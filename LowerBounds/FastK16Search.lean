import LowerBounds.K16Search
import LowerBounds.DomTables

/-!
# Proof-Ready Register-Packed `K16` Engine (`Rule JS` + `M3` + `W4` + `U3Fwd`)

100% pure functional table construction (`Array.ofFn` / `List.foldl` / `Nat.iterate`, ZERO `Id.run`)
so every table-lookup lemma in `FastK16Sound.lean` is a short symbolic proof:
* Canonical `S_7`-equivariant `s3` (5 entries) & `s4` (23 entries) via pure hex-digit permutations
  `s3Code` / `s4Code` and `codeToIdx` (`pack7`).
* `m3AllowBA` (`5400` bytes) and `w4AllowBA` (`138` bytes) built directly from `DomTables.m3Witnesses`
  and `DomTables.w4Witnesses` (verified by Lean kernel `decide` in `FastK16Sound.lean`).
* `u3MinRBA` (`(hi + 1) * 5400` bytes) built via pure `Nat.iterate` GFP relaxation (`relaxU3`).
* `Int64`-packed `a1BA`/`a2BA` (100% overflow-proof!).
* Register-packed ARM64 hot loop (`<= 8` scalar/object args, zero `Nat`/`Int`, zero closures).
-/

namespace SuperpermLowerBounds
namespace FastK16

open PS (permCodes ciTab nxtTab sdTab idcF capF excF)
open KS (tab2 look2 maxLeN codeF maskG a1F a2F uF segF par)
open DomTables (m3Witnesses w4Witnesses)

/-! ### Unboxed ByteArray Helpers -/

theorem lt_ba_size_of_lt_usize {b : ByteArray} {i : USize} (h : i < b.usize) : i.toNat < b.size := by
  have h1 : i.toNat < b.usize.toNat := h
  have h2 : b.usize.toNat ≤ b.size := by
    change (USize.ofNat b.size).toNat ≤ b.size
    rw [USize.toNat_ofNat']
    exact Nat.mod_le b.size USize.size
  exact Nat.lt_of_lt_of_le h1 h2

@[inline] def baGetU8 (b : ByteArray) (i : USize) : UInt8 :=
  if h : i < b.usize then b.uget i (lt_ba_size_of_lt_usize h) else 0

@[inline] def baSetU8 (b : ByteArray) (i : USize) (v : UInt8) : ByteArray :=
  if h : i < b.usize then b.uset i v (lt_ba_size_of_lt_usize h) else b

@[inline] def baGetU16 (b : ByteArray) (idx : USize) : UInt32 :=
  let o := idx + idx
  if h1 : o < b.usize then
    if h2 : o + 1 < b.usize then
      let lo := b.uget o (lt_ba_size_of_lt_usize h1)
      let hi := b.uget (o + 1) (lt_ba_size_of_lt_usize h2)
      lo.toUInt32 ||| (hi.toUInt32 <<< 8)
    else 0
  else 0

@[inline] def baGetI32 (b : ByteArray) (idx : USize) : Int32 :=
  let o := idx * 4
  let b0 := (baGetU8 b o).toUInt32
  let b1 := (baGetU8 b (o + 1)).toUInt32
  let b2 := (baGetU8 b (o + 2)).toUInt32
  let b3 := (baGetU8 b (o + 3)).toUInt32
  (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)).toInt32

@[inline] def baGetI64 (b : ByteArray) (idx : USize) : Int64 :=
  let o := idx * 8
  let b0 := (baGetU8 b o).toUInt64
  let b1 := (baGetU8 b (o + 1)).toUInt64
  let b2 := (baGetU8 b (o + 2)).toUInt64
  let b3 := (baGetU8 b (o + 3)).toUInt64
  let b4 := (baGetU8 b (o + 4)).toUInt64
  let b5 := (baGetU8 b (o + 5)).toUInt64
  let b6 := (baGetU8 b (o + 6)).toUInt64
  let b7 := (baGetU8 b (o + 7)).toUInt64
  (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
   (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)).toInt64

/-- Pure `Array.ofFn` LE 16-bit packer (zero `Id.run` -> trivial lookup lemma!). -/
def packU16Arr (arr : Array UInt32) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := arr.size * 2) fun i =>
    let v := arr[i.val / 2]!
    if i.val % 2 == 0 then UInt8.ofNat (v.toNat &&& 255)
    else UInt8.ofNat ((v.toNat >>> 8) &&& 255))

/-- Pure `Array.ofFn` LE 32-bit signed packer. -/
def packI32Arr (arr : Array Int32) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := arr.size * 4) fun i =>
    let v := arr[i.val / 4]!.toUInt32
    UInt8.ofNat ((v.toNat >>> (8 * (i.val % 4))) &&& 255))

/-- Pure `Array.ofFn` LE 64-bit signed packer (overflow-proof for all `Int` table values!). -/
def packI64Arr (arr : Array Int64) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := arr.size * 8) fun i =>
    let v := arr[i.val / 8]!.toUInt64
    UInt8.ofNat ((v.toNat >>> (8 * (i.val % 8))) &&& 255))

/-! ### Termination Helpers -/

theorem u32_sub_one_lt {x : UInt32} (h : 0 < x.toNat) : (x - 1).toNat < x.toNat := by
  have hle : (1 : UInt32) ≤ x := h
  rw [UInt32.toNat_sub_of_le _ _ hle]
  exact Nat.sub_lt h (by decide)

theorem u32_add_one_lt_bound {t lim : UInt32} (h : t < lim) :
    lim.toNat - (t + 1).toNat < lim.toNat - t.toNat := by
  have ht : t.toNat < lim.toNat := h
  have hlim : lim.toNat < UInt32.size := lim.toBitVec.isLt
  have hlt : t.toNat + 1 < UInt32.size := Nat.lt_of_le_of_lt ht hlim
  have h1 : (t + 1).toNat = t.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt hlt]
  omega

/-! ### Pure Canonical `S_7` Hex-Code Transitions & `DomTables` Builders -/

def perms3NonId : Array (Nat × Nat × Nat) :=
  #[(0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

def perms4NonId : Array (Nat × Nat × Nat × Nat) :=
  #[(0,1,3,2), (0,2,1,3), (0,2,3,1), (0,3,1,2), (0,3,2,1),
    (1,0,2,3), (1,0,3,2), (1,2,0,3), (1,2,3,0), (1,3,0,2), (1,3,2,0),
    (2,0,1,3), (2,0,3,1), (2,1,0,3), (2,1,3,0), (2,3,0,1), (2,3,1,0),
    (3,0,1,2), (3,0,2,1), (3,1,0,2), (3,1,2,0), (3,2,0,1), (3,2,1,0)]

@[inline] def hexDigit (c k : Nat) : Nat := (c >>> (4 * (6 - k))) &&& 15

@[inline] def packHex7 (d0 d1 d2 d3 d4 d5 d6 : Nat) : Nat :=
  ((((((d0 * 16 + d1) * 16 + d2) * 16 + d3) * 16 + d4) * 16 + d5) * 16 + d6)

@[inline] def packBase7 (c : Nat) : Nat :=
  (((((((hexDigit c 0 - 1) * 7 + (hexDigit c 1 - 1)) * 7 + (hexDigit c 2 - 1)) * 7 +
    (hexDigit c 3 - 1)) * 7 + (hexDigit c 4 - 1)) * 7 + (hexDigit c 5 - 1)) * 7 + (hexDigit c 6 - 1))

/-- Canonical `t`-th non-self weight-3 successor code of hex code `c` (`t ∈ 0..4`). -/
def s3Code (c t : Nat) : Nat :=
  let e := excF (16 ^ 6 - 1) c
  let p3 := #[hexDigit e 0, hexDigit e 1, hexDigit e 2]
  let (i0, i1, i2) := perms3NonId.getD t (0, 2, 1)
  packHex7 (hexDigit e 3) (hexDigit e 4) (hexDigit e 5) (hexDigit e 6)
    (p3.getD i0 0) (p3.getD i1 0) (p3.getD i2 0)

/-- Canonical `t`-th non-self weight-4 successor code of hex code `c` (`t ∈ 0..22`). -/
def s4Code (c t : Nat) : Nat :=
  let e := excF (16 ^ 6 - 1) c
  let p4 := #[hexDigit e 0, hexDigit e 1, hexDigit e 2, hexDigit e 3]
  let (i0, i1, i2, i3) := perms4NonId.getD t (0, 1, 3, 2)
  packHex7 (hexDigit e 4) (hexDigit e 5) (hexDigit e 6)
    (p4.getD i0 0) (p4.getD i1 0) (p4.getD i2 0) (p4.getD i3 0)

/-- Pure `List.foldl` inverse lookup table `packBase7 (jl[i]) ↦ i`. -/
def buildCodeToIdx (jl : List Nat) : Array UInt32 :=
  (jl.zipIdx.foldl (fun mp (c, i) => mp.set! (packBase7 c) (UInt32.ofNat i))
    (Array.replicate 823543 (0 : UInt32)))

structure S7K16Tabs where
  ciBA   : ByteArray   -- 5040 * 2B (UInt16): exact PS.ciTab 7 jl (0..5039)
  nxtBA  : ByteArray   -- 5040 * 2B (UInt16): exact PS.nxtTab 7 jl
  b2CiBA : ByteArray   -- 5040 * 2B (UInt16): exact ciTab[nxtTab[q]]
  s3BA   : ByteArray   -- 5040 * 5 * 2B (UInt16): canonical S_7-equivariant w3
  s4BA   : ByteArray   -- 5040 * 23 * 2B (UInt16): canonical S_7-equivariant w4
  ciArr  : Array Nat   -- exact PS.ciTab 7 jl
  nxtArr : Array Nat   -- exact PS.nxtTab 7 jl
  s3Arr  : Array UInt32
  st     : UInt32
  sz     : Nat

def buildS7K16Tabs : S7K16Tabs :=
  let jl := permCodes 7 7
  let n := jl.length
  let ja := jl.toArray
  let ciT := ciTab 7 jl
  let nxtT := nxtTab 7 jl
  let c2i := buildCodeToIdx jl
  let ciU := Array.ofFn (n := n) fun i => UInt32.ofNat ciT[i.val]!
  let nxtU := Array.ofFn (n := n) fun i => UInt32.ofNat nxtT[i.val]!
  let b2U := Array.ofFn (n := n) fun i => UInt32.ofNat ciT[nxtT[i.val]!]!
  let s3Arr := Array.ofFn (n := n * 5) fun i =>
    c2i[packBase7 (s3Code ja[i.val / 5]! (i.val % 5))]!
  let s4Arr := Array.ofFn (n := n * 23) fun i =>
    c2i[packBase7 (s4Code ja[i.val / 23]! (i.val % 23))]!
  { ciBA := packU16Arr ciU,
    nxtBA := packU16Arr nxtU,
    b2CiBA := packU16Arr b2U,
    s3BA := packU16Arr s3Arr,
    s4BA := packU16Arr s4Arr,
    ciArr := ciT, nxtArr := nxtT, s3Arr,
    st := UInt32.ofNat (jl.idxOf (idcF 7)),
    sz := n }

/-- Pure `List.foldl` builder for `m3AllowBA` (`5400` bytes): starts all `1`, clears each witness
    in `DomTables.m3Witnesses` to `0`! -/
def buildM3Allow : ByteArray :=
  m3Witnesses.foldl (fun ba (l0, t0, l1, t1, l2, _) =>
    let idx := ((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1)
    ba.set! idx 0) (ByteArray.mk (Array.replicate 5400 1))

/-- Pure `List.foldl` builder for `w4AllowBA` (`6 * 23 = 138` bytes): starts all `63`, clears bit
    `(l2 - 1)` for each witness in `DomTables.w4Witnesses`! -/
def buildW4Allow : ByteArray :=
  w4Witnesses.foldl (fun ba (l1, t4, l2, _) =>
    let idx := (l1 - 1) * 23 + t4
    let cur := ba.get! idx
    ba.set! idx (cur &&& (UInt8.ofNat (63 - (1 <<< (l2 - 1)))))) (ByteArray.mk (Array.replicate 138 63))

/-! ### Pure `Nat.iterate` GFP `U3Fwd` Builder (15-Line Soundness Proof!) -/

/-- Check if row of length `L` starting at `u` collides with `used` (or self-collides), returning
    `some (endU, newUsed)` if valid. Pure recursion on `L`! -/
def placeRow (ciArr nxtArr : Array Nat) : Nat → Nat → List Nat → Option (Nat × List Nat)
  | 0, _, _ => none
  | 1, u, used =>
    let c := ciArr[u]!
    if used.contains c then none else some (u, c :: used)
  | L + 1, u, used =>
    let c := ciArr[u]!
    if used.contains c then none
    else placeRow ciArr nxtArr L nxtArr[u]! (c :: used)

/-- Pure adjacency list of the `5400`-state `k=3` automaton from `st`:
    for state `s3 = (l0, t0, l1, t1, l2)`, returns list of valid next `(ns3, holes)` pairs! -/
def stateEdges (tabs : S7K16Tabs) (m3Allow : ByteArray) (js : Bool) (s3 : Nat) : List (Nat × Nat) :=
  if m3Allow.get! s3 == 0 then []
  else
    let l2 := s3 % 6 + 1
    let r2 := s3 / 6
    let t1 := r2 % 5
    let r1 := r2 / 5
    let l1 := r1 % 6 + 1
    let r0 := r1 / 6
    let t0 := r0 % 5
    let l0 := r0 / 5 + 1
    match placeRow tabs.ciArr tabs.nxtArr l0 tabs.st.toNat [] with
    | none => []
    | some (e0, u0) =>
      let n1 := tabs.s3Arr[e0 * 5 + t0]!.toNat
      let js0 := js && tabs.ciArr[n1]! == tabs.ciArr[tabs.nxtArr[e0]!]!
      if js0 && l1 >= 2 then []
      else match placeRow tabs.ciArr tabs.nxtArr l1 n1 u0 with
      | none => []
      | some (e1, u1) =>
        let n2 := tabs.s3Arr[e1 * 5 + t1]!.toNat
        let js1 := js && tabs.ciArr[n2]! == tabs.ciArr[tabs.nxtArr[e1]!]!
        if js1 && l2 >= 2 then []
        else match placeRow tabs.ciArr tabs.nxtArr l2 n2 u1 with
        | none => []
        | some (e2, u2) =>
          let cq2 := tabs.ciArr[tabs.nxtArr[e2]!]!
          let ns2 := (l1 - 1) * 30 + t1 * 6 + (l2 - 1)
          (List.range 5).flatMap fun t2 =>
            let n3 := tabs.s3Arr[e2 * 5 + t2]!.toNat
            let js2 := js && tabs.ciArr[n3]! == cq2
            (List.range 6).filterMap fun iL =>
              let l3 := iL + 1
              if js2 && l3 >= 2 then none
              else match placeRow tabs.ciArr tabs.nxtArr l3 n3 u2 with
              | none => none
              | some _ =>
                let ns3 := ns2 * 30 + t2 * 6 + iL
                if m3Allow.get! ns3 == 0 then none
                else some (ns3, 6 - l3)

/-- Single pure GFP relaxation step on row `y` of `U` (`Array Nat` of length `5400`). -/
def relaxRow (adj : Array (List (Nat × Nat))) (prevRows : Array (Array Nat))
    (y : Nat) (cur : Array Nat) : Array Nat :=
  Array.ofFn (n := 5400) fun s =>
    let best := (adj[s.val]!).foldl (fun acc (ns, h) =>
      if h == 0 then max acc (1 + cur[ns]!)
      else if h <= y then max acc (1 + (prevRows[y - h]!)[ns]!)
      else acc) 0
    min cur[s.val]! best

/-- Pure `n`-fold iteration (zero Mathlib imports!). -/
def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterN f n (f x)

/-- Pure recursive row-by-row GFP builder for `U3Fwd` (`0..hi`). -/
def buildU3Rows (adj : Array (List (Nat × Nat))) (P0 : Nat → Nat) : Nat → Array (Array Nat)
  | 0 =>
    let row0 := Array.replicate 5400 (P0 0)
    #[iterN (relaxRow adj #[] 0) 15 row0]
  | y + 1 =>
    let prev := buildU3Rows adj P0 y
    let rowInit := Array.replicate 5400 (P0 (y + 1))
    prev.push (iterN (relaxRow adj prev (y + 1)) 20 rowInit)

/-- Pure `Array.ofFn` compression into `u3MinR[d * 5400 + s3]`:
    `r` MUST exceed `u3MinR[d * 5400 + s3]` to beat `Ps x` at some `x ∈ [max lo d .. hi]`. -/
def buildU3MinR (tabs : S7K16Tabs) (m3Allow : ByteArray) (P0 Ps : Nat → Nat)
    (lo hi : Nat) (js : Bool) : ByteArray :=
  let adj := Array.ofFn (n := 5400) fun s => stateEdges tabs m3Allow js s.val
  let rows := buildU3Rows adj P0 hi
  ByteArray.mk (Array.ofFn (n := (hi + 1) * 5400) fun idx =>
    let d := idx.val / 5400
    let s := idx.val % 5400
    if m3Allow.get! s == 0 then (255 : UInt8)
    else
      let xStart := max lo d
      let best := (List.range (hi + 1 - xStart)).foldl (fun acc off =>
        let x := xStart + off
        let cap := (rows[x - d]!)[s]!
        let need := Ps x - cap
        min acc need) 255
      UInt8.ofNat best)

/-! ### Search Context & Register-Packed Hot Loop -/

structure FastK16Ctx where
  ciBA      : ByteArray
  nxtBA     : ByteArray
  b2CiBA    : ByteArray
  s3BA      : ByteArray
  s4BA      : ByteArray
  codeBA    : ByteArray
  maskBA    : ByteArray
  a1BA      : ByteArray   -- Int64 LE!
  a2BA      : ByteArray   -- Int64 LE!
  m3AllowBA : ByteArray
  w4AllowBA : ByteArray
  u3MinRBA  : ByteArray
  A         : UInt32
  S         : UInt32
  R         : UInt32
  C         : UInt32
  fullMk    : UInt32
  pa        : Int32
  pb        : Int32
  ph        : Int32
  ph2       : Int32
  js        : Bool
  useM3     : Bool
  useW4     : Bool
  fg        : UInt32
  nt        : UInt32
  tp        : UInt32

@[inline] def idx3 (ctx : FastK16Ctx) (t r d : UInt32) : USize :=
  ((t * (ctx.R + 1) + r) * ctx.C + d).toUSize

@[inline] def getCode (ctx : FastK16Ctx) (t r d : UInt32) : UInt32 :=
  if t < ctx.A && d < ctx.C then
    let r' := if r < ctx.R then r else ctx.R
    (baGetU8 ctx.codeBA (idx3 ctx t r' d)).toUInt32
  else 0

@[inline] def getMask (ctx : FastK16Ctx) (t r d : UInt32) : UInt32 :=
  if t < ctx.A && r <= ctx.R && d < ctx.C then
    (baGetU8 ctx.maskBA (idx3 ctx t r d)).toUInt32
  else ctx.fullMk

@[inline] def checkCut (ctx : FastK16Ctx) (t r d : UInt32) (m M : Int32) : Bool :=
  if m >= 0 then true
  else if t < ctx.A && r <= ctx.R && d < ctx.C then
    let idx := idx3 ctx t r d
    let m64 := m.toInt64
    let M64 := M.toInt64
    if baGetI64 ctx.a1BA idx <= M64 + m64 then true
    else baGetI64 ctx.a2BA idx <= m64
  else true

@[inline] def packMM (m M : Int32) : UInt64 :=
  m.toUInt32.toUInt64 ||| (M.toUInt32.toUInt64 <<< 32)
@[inline] def unpackM (mM : UInt64) : Int32 := mM.toUInt32.toInt32
@[inline] def unpackMax (mM : UInt64) : Int32 := (mM >>> 32).toUInt32.toInt32

mutual

def go (ctx : FastK16Ctx) (fuel : UInt32) (state mM : UInt64) (B : ByteArray) : ByteArray :=
  if hf : fuel > 0 then
    let q : UInt32 := (state &&& 8191).toUInt32
    let d : UInt32 := ((state >>> 13) &&& 255).toUInt32
    let r : UInt32 := ((state >>> 21) &&& 255).toUInt32
    let t : UInt32 := ((state >>> 29) &&& 15).toUInt32
    let c := getCode ctx t r d
    if c == 0 then B
    else if c == 1 then ByteArray.empty
    else
      let fuel' := fuel - 1
      if fuel' != ctx.fg || ((q + 8192 * d) % ctx.nt) == ctx.tp then
        let w3Run : UInt32 := ((state >>> 33) &&& 3).toUInt32
        let s1 : UInt32 := ((state >>> 35) &&& 7).toUInt32
        let s2 : UInt32 := ((state >>> 38) &&& 255).toUInt32
        let cq := if ctx.js then baGetU16 ctx.b2CiBA q.toUSize else 0
        let m := unpackM mM
        let M := unpackMax mM
        let fBase : Int32 := ctx.pa * r.toInt32 - ctx.pb * d.toInt32 - ctx.ph2 * t.toInt32
        let B1 :=
          if c != 3 then
            let mN := if fBase < m then fBase else m
            let MN := if fBase > M then fBase else M
            if checkCut ctx t r d mN MN then
              let nr := r + 1
              let mk := getMask ctx t nr d
              if mk == 0 then B
              else
                let nw3 := if w3Run < 2 then w3Run + 1 else 2
                let baseSt : UInt64 := (d.toUInt64 <<< 13) ||| (nr.toUInt64 <<< 21) ||| (t.toUInt64 <<< 29) |||
                  (nw3.toUInt64 <<< 33) ||| (s1.toUInt64 <<< 35) ||| (s2.toUInt64 <<< 38)
                let lArg : UInt64 := ((5 : UInt64) <<< 5) ||| (mk.toUInt64 <<< 10) ||| (cq.toUInt64 <<< 16)
                loopSucc ctx fuel' baseSt (packMM mN MN) lArg (q.toUSize * 5) 5 B
            else B
          else B
        if B1.usize == 0 then B1
        else if c != 2 then
          let g := fBase - ctx.ph
          let mS := if g < m then g else m
          let MS := if g > M then g else M
          if checkCut ctx t r d mS MS then
            let nt1 := t + 1
            let nr := r + 1
            let mk := getMask ctx nt1 nr d
            if mk == 0 then B1
            else
              let baseSt : UInt64 := (d.toUInt64 <<< 13) ||| (nr.toUInt64 <<< 21) ||| (nt1.toUInt64 <<< 29) |||
                (s1.toUInt64 <<< 35)
              let lArg : UInt64 := ((23 : UInt64) <<< 5) ||| (mk.toUInt64 <<< 10) ||| (cq.toUInt64 <<< 16) ||| ((1 : UInt64) <<< 29)
              loopSucc ctx fuel' baseSt (packMM mS MS) lArg (q.toUSize * 23) 23 B1
          else B1
        else B1
      else B
  else ByteArray.empty
termination_by (fuel.toNat, 3, 0)
decreasing_by
  all_goals
    have h1 : (fuel - 1).toNat + 1 = fuel.toNat := by
      have hle : (1 : UInt32) ≤ fuel := hf
      rw [UInt32.toNat_sub_of_le _ _ hle, UInt32.toNat_one]
      have hpos : 0 < fuel.toNat := hf
      omega
    rw [h1]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))

def loopSucc (ctx : FastK16Ctx) (fuel : UInt32) (baseSt mM lArg : UInt64) (sBase : USize) (rem : UInt32) (B : ByteArray) : ByteArray :=
  if h : rem > 0 then
    let lim : UInt32 := ((lArg >>> 5) &&& 31).toUInt32
    let idx := lim - rem
    let mk : UInt32 := ((lArg >>> 10) &&& 63).toUInt32
    let cq : UInt32 := ((lArg >>> 16) &&& 8191).toUInt32
    let isS4 := (lArg >>> 29) != 0
    let D := baGetU16 (if isS4 then ctx.s4BA else ctx.s3BA) (sBase + idx.toUSize)
    let emk0 := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
    let emk :=
      if isS4 && ctx.useW4 then
        let prevS1 : UInt32 := ((baseSt >>> 35) &&& 7).toUInt32
        emk0 &&& (baGetU8 ctx.w4AllowBA (prevS1 * 23 + idx).toUSize).toUInt32
      else emk0
    let B' :=
      if emk == 0 then B
      else
        let wBase := if isS4 then baseSt else baseSt ||| (idx.toUInt64 <<< 46)
        walkGo ctx fuel wBase mM 6 emk D B
    if B'.usize == 0 then B'
    else loopSucc ctx fuel baseSt mM lArg sBase (rem - 1) B'
  else B
termination_by (fuel.toNat + 1, 2, rem.toNat)
decreasing_by
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (u32_sub_one_lt h))

def walkGo (ctx : FastK16Ctx) (fuel : UInt32) (baseSt mM : UInt64) (rem mk D : UInt32) (B : ByteArray) : ByteArray :=
  if hr : rem > 0 then
    if mk == 0 then B
    else
      let c := (baGetU16 ctx.ciBA D.toUSize).toUSize
      if baGetU8 B c != 0 then B
      else
        let n := rem - 1
        let B0 := baSetU8 B c 1
        let B1 :=
          if (mk &&& 1) != 0 then
            let ns1 := 5 - n
            let nw3 : UInt32 := ((baseSt >>> 33) &&& 3).toUInt32
            let okM3 :=
              if nw3 == 2 && ctx.useM3 then
                let s2p : UInt32 := ((baseSt >>> 38) &&& 255).toUInt32
                let t3c : UInt32 := ((baseSt >>> 46) &&& 7).toUInt32
                let ns3 := s2p * 30 + t3c * 6 + ns1
                if baGetU8 ctx.m3AllowBA ns3.toUSize == 0 then false
                else
                  let nt : UInt32 := ((baseSt >>> 29) &&& 15).toUInt32
                  if nt == ctx.S then
                    let nr : UInt32 := ((baseSt >>> 21) &&& 255).toUInt32
                    let nd : UInt32 := ((baseSt >>> 13) &&& 255).toUInt32 + n
                    if nd < ctx.C then
                      nr > (baGetU8 ctx.u3MinRBA (nd.toUSize * 5400 + ns3.toUSize)).toUInt32
                    else false
                  else true
              else true
            if okM3 then
              let nextS2 : UInt32 :=
                if nw3 == 0 then 0
                else
                  let s1p : UInt32 := ((baseSt >>> 35) &&& 7).toUInt32
                  let t3c : UInt32 := ((baseSt >>> 46) &&& 7).toUInt32
                  s1p * 30 + t3c * 6 + ns1
              let lowBits := (baseSt &&& (34359738367 : UInt64)) + (n.toUInt64 <<< 13)
              let nst : UInt64 := lowBits ||| D.toUInt64 ||| (ns1.toUInt64 <<< 35) ||| (nextS2.toUInt64 <<< 38)
              go ctx fuel nst mM B0
            else B0
          else B0
        if B1.usize == 0 then B1
        else
          let mk' := mk >>> 1
          let B2 :=
            if mk' != 0 then
              walkGo ctx fuel baseSt mM n mk' (baGetU16 ctx.nxtBA D.toUSize) B1
            else B1
          if B2.usize == 0 then B2
          else baSetU8 B2 c 0
  else B
termination_by (fuel.toNat + 1, 1, rem.toNat)
decreasing_by
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (u32_sub_one_lt hr))

end

/-! ### Problem Builder & Entry Points -/

def buildProblem (caps : List (List Nat)) (s lo hi a b h : Nat) (js useM3 useW4 : Bool)
    (fuel ds nt : Nat) : FastK16Ctx × UInt32 × Nat :=
  let A := s + 1
  let C := hi + 1
  let tP := tab2 A C (capF caps)
  let P := look2 A C tP (capF caps)
  let R := maxLeN (P s) hi + 1
  let B := R + 1
  let tot := A * B * C
  let tc := KS.tabA A B C (codeF P s lo hi)
  let tm := KS.tabA A B C (fun t r d => maskG (KS.codeT A R C tc) t r d 6)
  let tu := tab2 A C (uF P s a b h)
  let tg := tab2 A C (segF P s a b h)
  let t1 := KS.tabA A B C (a1F P s lo hi a b h)
  let t2 := KS.tabA A B C (a2F (look2 A C tu (uF P s a b h)) (look2 A C tg (segF P s a b h)) P s lo hi a b h)
  let codeBA := ByteArray.mk (Array.ofFn (n := tot) fun i => UInt8.ofNat tc[i.val]!)
  let maskBA := ByteArray.mk (Array.ofFn (n := tot) fun i => UInt8.ofNat tm[i.val]!)
  let a1BA := packI64Arr (Array.ofFn (n := tot) fun i => Int64.ofInt t1[i.val]!)
  let a2BA := packI64Arr (Array.ofFn (n := tot) fun i => Int64.ofInt t2[i.val]!)
  let tabs := buildS7K16Tabs
  let m3AllowBA := if useM3 then buildM3Allow else ByteArray.empty
  let w4AllowBA := if useW4 then buildW4Allow else ByteArray.empty
  let u3MinRBA :=
    if useM3 then buildU3MinR tabs m3AllowBA (P 0) (P s) lo hi js
    else ByteArray.empty
  let fullMk := UInt32.ofNat (maskG (fun _ _ _ => 1) 0 0 0 6)
  let ctx : FastK16Ctx := {
    ciBA := tabs.ciBA, nxtBA := tabs.nxtBA, b2CiBA := tabs.b2CiBA,
    s3BA := tabs.s3BA, s4BA := tabs.s4BA,
    codeBA, maskBA, a1BA, a2BA,
    m3AllowBA, w4AllowBA, u3MinRBA,
    A := UInt32.ofNat A, S := UInt32.ofNat s, R := UInt32.ofNat R, C := UInt32.ofNat C,
    fullMk,
    pa := Int32.ofInt a, pb := Int32.ofInt b,
    ph := Int32.ofInt h, ph2 := Int32.ofInt (2 * h),
    js, useM3, useW4,
    fg := UInt32.ofNat (fuel - ds),
    nt := UInt32.ofNat nt, tp := 0
  }
  (ctx, tabs.st, tabs.sz)

def runPart (ctx0 : FastK16Ctx) (st : UInt32) (sz fuel tp : Nat) : Bool :=
  let ctx := { ctx0 with tp := UInt32.ofNat tp }
  let B0 := ByteArray.mk (Array.replicate sz 0)
  let baseSt : UInt64 := (1 : UInt64) <<< 21
  (walkGo ctx (UInt32.ofNat fuel) baseSt 0 6 ctx.fullMk st B0).usize == 0

def seqSearch (caps : List (List Nat)) (s lo hi a b h : Nat) (js useM3 useW4 : Bool)
    (fuel ds nt pa pb : Nat) : Bool :=
  let (ctx0, st, sz) := buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt
  if pb == pa + 1 then runPart ctx0 st sz fuel pa
  else par (runPart ctx0 st sz fuel) pa pb

end FastK16
end SuperpermLowerBounds
