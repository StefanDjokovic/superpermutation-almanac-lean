import LowerBounds.J16Search
import LowerBounds.FastK16Search

/-!
# Proof-Ready Fast Joint Engine (`FastJ16`: O(1) Tabulated `PREV` + `ORD` + `VS` + `Rule JS`)

100% pure functional table construction (`Array.ofFn` only, ZERO `Id.run`, overflow-proof `Int64`
for `cn1Base`/`a2pBase`/`best`/`g`/`rb`/`f`):
* Uses exact `PS.ciTab 7 jl`, `PS.nxtTab 7 jl`, `PS.sdTab 7 3 jl` (6 entries), `PS.sdTab 7 4 jl`
  (24 entries) via `Array.ofFn` -> 1-line table-lookup lemmas in `FastJ16Sound.lean`!
* O(1) tabulated `cn1Base[om]` and `a2pBase[tl, om]` (`Int64`, zero overflow even when `nx = negInf`!).
* Optional `Rule JS` (`js : Bool`) on every piece continuation (`ci[D] == ci[nxt[q]] → mk &&& 1`).
-/

namespace SuperpermLowerBounds
namespace FastJ16

open PS (permCodes ciTab nxtTab sdTab idcF capF)
open KS (tabA tab2 look2 maxLe maxLeN par)
open J15 (negInf bestF bestStep kdF loF hiF digs gprod)
open J16 (Rules vloF vhiF prevOn ordOn potF segF cn1F a2pF fG)
open FastK16 (baGetU8 baSetU8 baGetU16 baGetI64 packU16Arr packI64Arr u32_sub_one_lt)

structure FastJ16Ctx where
  ciBA      : ByteArray  -- 5040 * 2B (UInt16, exact PS.ciTab 7 jl)
  nxtBA     : ByteArray  -- 5040 * 2B (UInt16, exact PS.nxtTab 7 jl)
  b2CiBA    : ByteArray  -- 5040 * 2B (UInt16, ciTab[nxtTab[q]])
  s3BA      : ByteArray  -- 5040 * 6 * 2B (UInt16, exact PS.sdTab 7 3 jl)
  s4BA      : ByteArray  -- 5040 * 24 * 2B (UInt16, exact PS.sdTab 7 4 jl)
  kdBA      : ByteArray  -- np bytes
  loBA      : ByteArray  -- np bytes
  hiBA      : ByteArray  -- np bytes
  vloBA     : ByteArray  -- np * 8B (Int64)
  vhiBA     : ByteArray  -- np * 8B (Int64)
  bestBA    : ByteArray  -- (np + 1) * C * 8B (Int64)
  gBA       : ByteArray  -- np * S * C * 8B (Int64)
  rbBA      : ByteArray  -- S * C * 8B (Int64)
  fBA       : ByteArray  -- (np * C) * RR * C * 8B (Int64)
  cn1BaseBA : ByteArray  -- C * 8B (Int64): cn1F (B rp) pa pb 0 om
  a2pBaseBA : ByteArray  -- S * C * 8B (Int64): a2pF seg (B rp) pa pb tl 0 om
  gatePi    : ByteArray  -- ng bytes
  gateR     : ByteArray  -- ng bytes
  gateMod   : ByteArray  -- ng * 2B (UInt16)
  gateDig   : ByteArray  -- ng * 2B (UInt16)
  ng        : UInt32
  np        : UInt32
  S         : UInt32
  C         : UInt32
  RR        : UInt32
  bm        : UInt32
  rp        : UInt32
  oi        : UInt32
  pa        : Int64
  pb        : Int64
  ph        : Int64
  ph2       : Int64
  clip      : Bool
  js        : Bool

@[inline] def getKd (ctx : FastJ16Ctx) (i : UInt32) : UInt32 := (baGetU8 ctx.kdBA i.toUSize).toUInt32
@[inline] def getLo (ctx : FastJ16Ctx) (i : UInt32) : UInt32 := (baGetU8 ctx.loBA i.toUSize).toUInt32
@[inline] def getHi (ctx : FastJ16Ctx) (i : UInt32) : UInt32 := (baGetU8 ctx.hiBA i.toUSize).toUInt32
@[inline] def getVlo (ctx : FastJ16Ctx) (i : UInt32) : Int64 := baGetI64 ctx.vloBA i.toUSize
@[inline] def getVhi (ctx : FastJ16Ctx) (i : UInt32) : Int64 := baGetI64 ctx.vhiBA i.toUSize

@[inline] def getBest (ctx : FastJ16Ctx) (i y : UInt32) : Int64 :=
  if i <= ctx.np && y < ctx.C then baGetI64 ctx.bestBA (i * ctx.C + y).toUSize else 0

@[inline] def getG (ctx : FastJ16Ctx) (i u y : UInt32) : Int64 :=
  if i < ctx.np && u < ctx.S && y < ctx.C then baGetI64 ctx.gBA ((i * ctx.S + u) * ctx.C + y).toUSize else 0

@[inline] def getRB (ctx : FastJ16Ctx) (u y : UInt32) : Int64 :=
  if u < ctx.S && y < ctx.C then baGetI64 ctx.rbBA (u * ctx.C + y).toUSize else 0

@[inline] def ringOkFast (ctx : FastJ16Ctx) (i b r d : UInt32) (x : Int64) : Bool :=
  if i < ctx.np && b < ctx.C && r < ctx.RR && d < ctx.C then
    let F := baGetI64 ctx.fBA (((i * ctx.C + b) * ctx.RR + r) * ctx.C + d).toUSize
    x <= F && (!ctx.clip || 0 <= F)
  else true

@[inline] def u32ToI64 (x : UInt32) : Int64 := x.toUInt64.toInt64

@[inline] def vOfFast (t r d : UInt32) : Int64 :=
  u32ToI64 r - u32ToI64 d - (5 : Int64) * u32ToI64 t

@[inline] def s3Contains (ctx : FastJ16Ctx) (q z : UInt32) : Bool :=
  let base := q.toUSize * 6
  baGetU16 ctx.s3BA base == z ||
  baGetU16 ctx.s3BA (base + 1) == z ||
  baGetU16 ctx.s3BA (base + 2) == z ||
  baGetU16 ctx.s3BA (base + 3) == z ||
  baGetU16 ctx.s3BA (base + 4) == z ||
  baGetU16 ctx.s3BA (base + 5) == z

def gateLoop (ctx : FastJ16Ctx) (i r key rem : UInt32) : Bool :=
  if h : rem > 0 then
    let idx := rem - 1
    let gi := (baGetU8 ctx.gatePi idx.toUSize).toUInt32
    let gr := (baGetU8 ctx.gateR idx.toUSize).toUInt32
    let ok :=
      if gi == i && gr == r then
        let m := baGetU16 ctx.gateMod idx.toUSize
        let dg := baGetU16 ctx.gateDig idx.toUSize
        (key % m) == dg
      else true
    if ok then gateLoop ctx i r key idx else false
  else true
termination_by rem.toNat
decreasing_by exact u32_sub_one_lt h

def earlyLoop (ctx : FastJ16Ctx) (i r key rem : UInt32) : Bool :=
  if h : rem > 0 then
    let idx := rem - 1
    let gi := (baGetU8 ctx.gatePi idx.toUSize).toUInt32
    let gr := (baGetU8 ctx.gateR idx.toUSize).toUInt32
    let ok :=
      if gi == i && r < gr then
        let m := baGetU16 ctx.gateMod idx.toUSize
        let dg := baGetU16 ctx.gateDig idx.toUSize
        (key % m) == dg
      else true
    if ok then earlyLoop ctx i r key idx else false
  else true
termination_by rem.toNat
decreasing_by exact u32_sub_one_lt h

@[inline] def checkGate (ctx : FastJ16Ctx) (i r q d : UInt32) : Bool :=
  if ctx.ng == 0 then true else gateLoop ctx i r (q + 8192 * d) ctx.ng

@[inline] def checkEarly (ctx : FastJ16Ctx) (i r q d : UInt32) : Bool :=
  if ctx.ng == 0 then true else earlyLoop ctx i r (q + 8192 * d) ctx.ng

@[inline] def compOkFast (ctx : FastJ16Ctx) (i : UInt32) (a : Int64) (y : UInt32) (v : Int64) (eOk : Bool) : Bool :=
  if i + 1 == ctx.np then a <= v
  else (a - v) <= getBest ctx i y && eOk

@[inline] def k3OkFast (ctx : FastJ16Ctx) (i c t r d : UInt32) (a : Int64) (b y : UInt32) (v : Int64) : Bool :=
  if c == 0 then ringOkFast ctx i b r d a
  else (1 : Int64) <= v && (a - v) <= getG ctx i (c - 1 - t) y

@[inline] def k4OkFast (ctx : FastJ16Ctx) (i c t : UInt32) (a : Int64) (y : UInt32) (v : Int64) : Bool :=
  t + 1 < c && (6 : Int64) <= v && 6 <= y &&
  (a - v + 5) <= getG ctx i (c - 2 - t) (y - 6)

@[inline] def liveFast (ctx : FastJ16Ctx) (i t r d : UInt32) (a : Int64) (b : UInt32) (m : Int64) : Bool :=
  let c := getKd ctx i
  let wt := d + 6 * t
  let y := b - wt
  let v := vOfFast t r d
  k3OkFast ctx i c t r d a b y v ||
  k4OkFast ctx i c t a y v ||
  ((if c == 0 then 2 <= r else m < v) && compOkFast ctx i a y v true)

@[inline] def computeMask (ctx : FastJ16Ctx) (i t r d : UInt32) (a : Int64) (b : UInt32) (m : Int64) : UInt32 :=
  let wt := d + 6 * t
  let b0 : UInt32 := if wt + 5 <= b && liveFast ctx i t r (d + 5) a b m then 1 else 0
  let b1 : UInt32 := if wt + 4 <= b && liveFast ctx i t r (d + 4) a b m then 2 else 0
  let b2 : UInt32 := if wt + 3 <= b && liveFast ctx i t r (d + 3) a b m then 4 else 0
  let b3 : UInt32 := if wt + 2 <= b && liveFast ctx i t r (d + 2) a b m then 8 else 0
  let b4 : UInt32 := if wt + 1 <= b && liveFast ctx i t r (d + 1) a b m then 16 else 0
  let b5 : UInt32 := if wt     <= b && liveFast ctx i t r  d      a b m then 32 else 0
  b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5

@[inline] def prevOkFast (ctx : FastJ16Ctx) (kind : UInt32) (f pm pM : Int64)
    (tl : UInt32) (need : Int64) (om : UInt32) : Bool :=
  if kind == 0 then
    let mn := if pm < f then pm else f
    let mx := if pM > f then pM else f
    if 0 <= mn then true
    else
      let cn1 := ctx.pa * need + baGetI64 ctx.cn1BaseBA om.toUSize
      if cn1 <= mx + mn - f then true
      else
        let a2p := ctx.pa * need + baGetI64 ctx.a2pBaseBA (tl * ctx.C + om).toUSize
        a2p <= mn
  else
    let fp := f - ctx.ph
    let mn := if pm < fp then pm else fp
    let mx := if pM > fp then pM else fp
    if 0 <= mn then true
    else
      let need' := need + 5
      let om' := om - 6
      let cn1 := ctx.pa * need' + baGetI64 ctx.cn1BaseBA om'.toUSize - ctx.ph2
      if cn1 <= mx + mn - f then true
      else
        let a2p := ctx.pa * need' + baGetI64 ctx.a2pBaseBA ((tl - 1) * ctx.C + om').toUSize
        a2p <= mn

@[inline] def xrFast (ctx : FastJ16Ctx) (kind i c t r d : UInt32) (a : Int64) (b : UInt32) (pm pM : Int64) : Bool :=
  let v := vOfFast t r d
  let wt := d + 6 * t
  let y := b - wt
  let okPrev :=
    if i == ctx.rp && c != 0 then
      let f := ctx.pa * u32ToI64 r - ctx.pb * u32ToI64 d - ctx.ph2 * u32ToI64 t
      prevOkFast ctx kind f pm pM (c - 1 - t) (a - v) y
    else true
  if !okPrev then false
  else if i == ctx.oi && i + 1 < ctx.np then
    if kind == 0 then
      a <= 2 * (v + getRB ctx (c - 1 - t) y) + getBest ctx (i + 1) b
    else
      a <= 2 * (v - 5 + getRB ctx (c - 2 - t) (y - 6)) + getBest ctx (i + 1) b
  else true

@[inline] def xcFast (ctx : FastJ16Ctx) (i c t r d : UInt32) (a : Int64) (b : UInt32) (pm pM : Int64) : Bool :=
  let okRing :=
    if c == 0 then
      let vr := u32ToI64 r - u32ToI64 d
      getVlo ctx i <= vr && vr <= getVhi ctx i
    else true
  if !okRing then false
  else
    let okPrev :=
      if i == ctx.rp && c != 0 then
        let f := ctx.pa * u32ToI64 r - ctx.pb * u32ToI64 d - ctx.ph2 * u32ToI64 t
        let mn := if pm < f then pm else f
        let mx := if pM > f then pM else f
        0 <= mn + mx - f
      else true
    if !okPrev then false
    else if i == ctx.oi && i + 1 < ctx.np then
      let v := vOfFast t r d
      let y := b - (d + 6 * t)
      a <= 2 * v + getBest ctx (i + 1) y
    else true

@[inline] def packI32Pair (x y : Int64) : UInt64 :=
  x.toInt32.toUInt32.toUInt64 ||| (y.toInt32.toUInt32.toUInt64 <<< 32)
@[inline] def fstI64 (p : UInt64) : Int64 := p.toUInt32.toInt32.toInt64
@[inline] def sndI64 (p : UInt64) : Int64 := (p >>> 32).toUInt32.toInt32.toInt64

@[inline] def packSt (i t r d b du z q : UInt32) : UInt64 :=
  i.toUInt64 ||| (t.toUInt64 <<< 4) ||| (r.toUInt64 <<< 8) ||| (d.toUInt64 <<< 16) |||
  (b.toUInt64 <<< 24) ||| (du.toUInt64 <<< 32) ||| (z.toUInt64 <<< 36) ||| (q.toUInt64 <<< 49)

@[specialize] def walkJFast (ctx : FastJ16Ctx) (visit : UInt32 → UInt32 → UInt32 → ByteArray → ByteArray)
    (pm : UInt8) (rem mk du D : UInt32) (M : ByteArray) : ByteArray :=
  if h : rem > 0 then
    if mk == 0 then M
    else
      let c := (baGetU16 ctx.ciBA D.toUSize).toUSize
      let o := baGetU8 M c
      if o == pm then M
      else if o != 0 && ctx.bm <= du then M
      else
        let du' := if o != 0 then du + 1 else du
        let n := rem - 1
        let M0 := baSetU8 M c pm
        let M1 := if (mk &&& 1) != 0 then visit n D du' M0 else M0
        if M1.usize == 0 then M1
        else
          let mk' := mk >>> 1
          let M2 := if mk' != 0 then walkJFast ctx visit pm n mk' du' (baGetU16 ctx.nxtBA D.toUSize) M1 else M1
          if M2.usize == 0 then M2
          else baSetU8 M2 c o
  else M
termination_by rem.toNat
decreasing_by exact u32_sub_one_lt h

@[specialize] def loopU32 (lim idx : UInt32) (step : UInt32 → ByteArray → ByteArray) (M : ByteArray) : ByteArray :=
  if h : idx < lim then
    let M' := step idx M
    if M'.usize == 0 then M'
    else loopU32 lim (idx + 1) step M'
  else M
termination_by lim.toNat - idx.toNat
decreasing_by exact FastK16.u32_add_one_lt_bound h

def go (ctx : FastJ16Ctx) (fuel : UInt32) (st am pMM : UInt64) (M : ByteArray) : ByteArray :=
  if hf : fuel > 0 then
    let i : UInt32 := (st &&& 15).toUInt32
    let t : UInt32 := ((st >>> 4) &&& 15).toUInt32
    let r : UInt32 := ((st >>> 8) &&& 255).toUInt32
    let d : UInt32 := ((st >>> 16) &&& 255).toUInt32
    let b : UInt32 := ((st >>> 24) &&& 255).toUInt32
    let du : UInt32 := ((st >>> 32) &&& 15).toUInt32
    let z : UInt32 := ((st >>> 36) &&& 8191).toUInt32
    let q : UInt32 := ((st >>> 49) &&& 8191).toUInt32
    if checkGate ctx i r q d then
      let fuel' := fuel - 1
      let a := fstI64 am
      let m := sndI64 am
      let pm := fstI64 pMM
      let pM := sndI64 pMM
      let c := getKd ctx i
      let wt := d + 6 * t
      let y := b - wt
      let v := vOfFast t r d
      let M1 :=
        if compOkFast ctx i a y v (checkEarly ctx i r q d) &&
            (if c == 0 then 2 <= r && getLo ctx i <= d && d <= getHi ctx i && s3Contains ctx q z
             else m < v) &&
            xcFast ctx i c t r d a b pm pM then
          if i + 1 == ctx.np then ByteArray.empty
          else
            let ni := i + 1
            let na := a - v
            let mk := computeMask ctx ni 0 1 0 na y (-6)
            if mk == 0 then M
            else
              let pmMark := UInt8.ofNat (ni.toNat + 1)
              let nam := packI32Pair na (-6)
              loopU32 5040 0 (fun D M' =>
                walkJFast ctx (fun n e du' M'' =>
                  go ctx fuel' (packSt ni 0 1 n y du' D e) nam 0 M'')
                  pmMark 6 mk du D M') M
        else M
      if M1.usize == 0 then M1
      else
        let m' := if m > v then m else v
        let nam' := packI32Pair a m'
        let pmMark := UInt8.ofNat (i.toNat + 1)
        let cq := if ctx.js then baGetU16 ctx.b2CiBA q.toUSize else 9999
        let fBase := ctx.pa * u32ToI64 r - ctx.pb * u32ToI64 d - ctx.ph2 * u32ToI64 t
        let M2 :=
          if k3OkFast ctx i c t r d a b y v && xrFast ctx 0 i c t r d a b pm pM then
            let nr := r + 1
            let mk := computeMask ctx i t nr d a b m'
            if mk == 0 then M1
            else
              let npm := if pm < fBase then pm else fBase
              let npM := if pM > fBase then pM else fBase
              let npMM := packI32Pair npm npM
              let s3Base := q.toUSize * 6
              loopU32 6 0 (fun idx M' =>
                let D := baGetU16 ctx.s3BA (s3Base + idx.toUSize)
                let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
                if emk == 0 then M'
                else walkJFast ctx (fun n e du' M'' =>
                  go ctx fuel' (packSt i t nr (d + n) b du' z e) nam' npMM M'')
                  pmMark 6 emk du D M') M1
          else M1
        if M2.usize == 0 then M2
        else if k4OkFast ctx i c t a y v && xrFast ctx 1 i c t r d a b pm pM then
          let nt1 := t + 1
          let nr := r + 1
          let mk := computeMask ctx i nt1 nr d a b m'
          if mk == 0 then M2
          else
            let fp := fBase - ctx.ph
            let npm := if pm < fp then pm else fp
            let npM := if pM > fp then pM else fp
            let npMM := packI32Pair npm npM
            let s4Base := q.toUSize * 24
            loopU32 24 0 (fun idx M' =>
              let D := baGetU16 ctx.s4BA (s4Base + idx.toUSize)
              let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
              if emk == 0 then M'
              else walkJFast ctx (fun n e du' M'' =>
                go ctx fuel' (packSt i nt1 nr (d + n) b du' z e) nam' npMM M'')
                pmMark 6 emk du D M') M2
        else M2
    else M
  else ByteArray.empty
termination_by fuel.toNat
decreasing_by all_goals exact u32_sub_one_lt hf

structure BuiltJoint where
  ctx0 : FastJ16Ctx
  st   : UInt32
  sz   : Nat
  V    : Int64
  W    : UInt32
  fuel : UInt32
  gs   : List (Nat × Nat × Nat)

def buildJoint (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (js : Bool) : BuiltJoint :=
  let np := specs.length
  let S := maxLeN (kdF specs) np + 1
  let C := W + 1
  let tP := tab2 S C (capF caps)
  let P := look2 S C tP (capF caps)
  let tR := tab2 1 C (fun _ x => PRl.getD x 0)
  let PR := fun x => look2 1 C tR (fun _ x => PRl.getD x 0) 0 x
  let RR := maxLeN PR W + 1
  let kdA := (specs.map fun p => p.1).toArray
  let loA := (specs.map fun p => p.2.1).toArray
  let hiA := (specs.map fun p => p.2.2).toArray
  let tB := tab2 (np + 1) C (fun i y => bestF P PR 6 (specs.drop (i + 1)) y)
  let B := look2 (np + 1) C tB (fun i y => bestF P PR 6 (specs.drop (i + 1)) y)
  let tG := tabA np S C (fun i u y => bestStep P PR 6 (u + 1, 0, 0) (B i) y)
  let tRB := tab2 S C (fun u y => bestF P PR 6 [(u + 1, 0, 0)] y)
  let tS := tab2 S C (segF P 6 R.pa R.pb R.ph)
  let SG := look2 S C tS (segF P 6 R.pa R.pb R.ph)
  let tF := tabA (np * C) RR C (fun ib r d =>
    if kdA[ib / C]! == 0 then
      fG P PR (B (ib / C)) loA[ib / C]! hiA[ib / C]! (vloF R (ib / C)) (ib % C) r d
    else 0)
  let cn1BaseArr := Array.ofFn (n := C) fun om =>
    Int64.ofInt (cn1F (B R.rp) R.pa R.pb 0 om.val)
  let a2pBaseArr := Array.ofFn (n := S * C) fun idx =>
    Int64.ofInt (a2pF SG (B R.rp) R.pa R.pb (idx.val / C) 0 (idx.val % C))
  -- Exact PS tables directly via Array.ofFn (zero compression proof needed!)
  let jl := permCodes 7 7
  let n := jl.length
  let ciT := ciTab 7 jl
  let nxtT := nxtTab 7 jl
  let s3T := sdTab 7 3 jl
  let s4T := sdTab 7 4 jl
  let ciBA := packU16Arr (Array.ofFn (n := n) fun i => UInt32.ofNat ciT[i.val]!)
  let nxtBA := packU16Arr (Array.ofFn (n := n) fun i => UInt32.ofNat nxtT[i.val]!)
  let b2CiBA := packU16Arr (Array.ofFn (n := n) fun i => UInt32.ofNat ciT[nxtT[i.val]!]!)
  let s3BA := packU16Arr (Array.ofFn (n := n * 6) fun i => UInt32.ofNat ((s3T[i.val / 6]!).getD (i.val % 6) 0))
  let s4BA := packU16Arr (Array.ofFn (n := n * 24) fun i => UInt32.ofNat ((s4T[i.val / 24]!).getD (i.val % 24) 0))
  let kdBA := ByteArray.mk (Array.ofFn (n := np) fun i => UInt8.ofNat kdA[i.val]!)
  let loBA := ByteArray.mk (Array.ofFn (n := np) fun i => UInt8.ofNat loA[i.val]!)
  let hiBA := ByteArray.mk (Array.ofFn (n := np) fun i => UInt8.ofNat hiA[i.val]!)
  let vloBA := packI64Arr (Array.ofFn (n := np) fun i => Int64.ofInt (vloF R i.val))
  let vhiBA := packI64Arr (Array.ofFn (n := np) fun i => Int64.ofInt (vhiF R i.val))
  let bestBA := packI64Arr (Array.ofFn (n := (np + 1) * C) fun i => Int64.ofInt tB[i.val]!)
  let gBA := packI64Arr (Array.ofFn (n := np * S * C) fun i => Int64.ofInt tG[i.val]!)
  let rbBA := packI64Arr (Array.ofFn (n := S * C) fun i => Int64.ofInt tRB[i.val]!)
  let fBA := packI64Arr (Array.ofFn (n := (np * C) * RR * C) fun i => Int64.ofInt tF[i.val]!)
  let ctx0 : FastJ16Ctx := {
    ciBA, nxtBA, b2CiBA, s3BA, s4BA,
    kdBA, loBA, hiBA, vloBA, vhiBA, bestBA, gBA, rbBA, fBA,
    cn1BaseBA := packI64Arr cn1BaseArr,
    a2pBaseBA := packI64Arr a2pBaseArr,
    gatePi := ByteArray.empty, gateR := ByteArray.empty,
    gateMod := ByteArray.empty, gateDig := ByteArray.empty,
    ng := UInt32.ofNat gs.length,
    np := UInt32.ofNat np, S := UInt32.ofNat S, C := UInt32.ofNat C, RR := UInt32.ofNat RR,
    bm := UInt32.ofNat bm, rp := UInt32.ofNat R.rp, oi := UInt32.ofNat R.oi,
    pa := Int64.ofInt R.pa, pb := Int64.ofInt R.pb,
    ph := Int64.ofInt R.ph, ph2 := Int64.ofInt (2 * R.ph),
    clip := R.clip, js
  }
  { ctx0, st := UInt32.ofNat (jl.idxOf (idcF 7)), sz := n, V := Int64.ofInt V, W := UInt32.ofNat W,
    fuel := UInt32.ofNat fuel, gs }

def runJointPart (bj : BuiltJoint) (tp : Nat) : Bool :=
  let ds := digs bj.gs tp
  let ng := ds.length
  let piArr := Array.ofFn (n := ng) fun i => UInt8.ofNat (ds[i.val]!.1)
  let rArr  := Array.ofFn (n := ng) fun i => UInt8.ofNat (ds[i.val]!.2.1)
  let mArr  := Array.ofFn (n := ng) fun i => UInt32.ofNat (ds[i.val]!.2.2.1)
  let dArr  := Array.ofFn (n := ng) fun i => UInt32.ofNat (ds[i.val]!.2.2.2)
  let ctx := { bj.ctx0 with
    gatePi := ByteArray.mk piArr, gateR := ByteArray.mk rArr,
    gateMod := packU16Arr mArr, gateDig := packU16Arr dArr,
    ng := UInt32.ofNat ng }
  let mk := computeMask ctx 0 0 1 0 bj.V bj.W (-6)
  if mk == 0 then false
  else
    let M0 := ByteArray.mk (Array.replicate bj.sz 0)
    let am0 := packI32Pair bj.V (-6)
    (walkJFast ctx (fun n e du M' =>
      go ctx bj.fuel (packSt 0 0 1 n bj.W du bj.st e) am0 0 M')
      (UInt8.ofNat 1) 6 mk 0 bj.st M0).usize == 0

def jSearch (caps : List (List Nat)) (PRl : List Nat) (specs : List (Nat × Nat × Nat))
    (R : Rules) (V W bm fuel : Nat) (gs : List (Nat × Nat × Nat)) (js : Bool) (pa pb : Nat) : Bool :=
  let bj := buildJoint caps PRl specs R V W bm fuel gs js
  if pb == pa + 1 then runJointPart bj pa
  else par (runJointPart bj) pa pb

end FastJ16
end SuperpermLowerBounds
