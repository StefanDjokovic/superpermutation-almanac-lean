import LowerBounds.SSearch

/-!
# Pure-Kernel Definitions and Checkers for Level-2 `TropicCEGAR` (`k = 13`)

This file imports ONLY `LowerBounds.SSearch` (zero Mathlib imports) so that generated
certificate-checking shards load instantaneously and evaluate purely in the Lean kernel
via `decide +kernel` (zero `native_decide`, zero `sorry`, zero macros).

All soundness proofs live in `LowerBounds.TropicL2Sound`.
-/

namespace SuperpermLowerBounds
namespace TropicL2

open S

noncomputable section

/-! ### 1. Chunked range checks and pure-`Nat` potential ordering -/

/-- Check `p i = true` for all `lo ≤ i < lo + n`. -/
def checkRangeAux (lo : Nat) (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p (lo + n) && checkRangeAux lo p n

/-- Chunked range check (block size 64) to keep kernel recursion depth shallow. -/
def checkRangeChunked (lo len : Nat) (p : Nat → Bool) : Bool :=
  let full := len / 64
  let rem := len % 64
  checkRangeAux 0 (fun b => checkRangeAux (lo + b * 64) p 64) full &&
    checkRangeAux (lo + full * 64) p rem

/-- Pure-GMP-`Nat` potential ordering (`none` = unreachable = `-∞`). -/
def oLeN : Option Nat → Option Nat → Bool
  | none, _ => true
  | some _, none => false
  | some x, some y => Nat.ble x y

/-- Pure-GMP-`Nat` shifted step inequality `src + pos - neg ≤ dst`. -/
def oStepLeN (src : Option Nat) (pos neg : Nat) (dst : Option Nat) : Bool :=
  match src, dst with
  | none, _ => true
  | some _, none => false
  | some x, some y => Nat.ble (x + pos) (y + neg)

/-! ### 2. `w3Code`, `pieceAdvance`, `walkWordFast`, and `S_{13}` composition -/

/-- The 5 non-identity weight-3 seam successors of exit code `y`. -/
def w3Code (k y t : Nat) : Nat :=
  let base := (y % S.pw (k - 3)) * 4096
  let a := y / S.pw (k - 1)
  let b := (y / S.pw (k - 2)) % 16
  let c := (y / S.pw (k - 3)) % 16
  match t with
  | 0 => base + (a * 256 + c * 16 + b)
  | 1 => base + (b * 256 + a * 16 + c)
  | 2 => base + (b * 256 + c * 16 + a)
  | 3 => base + (c * 256 + a * 16 + b)
  | _ => base + (c * 256 + b * 16 + a)

/-- Advance `r` door-steps inside a single piece of length `≤ k - 1` via `rotl (k - 1)`. -/
def pieceAdvance (k r c : Nat) : Nat :=
  S.rotl (k - 1) (c / 16) r * 16 + c % 16

/-- Fast `O(|w|)` word walk computing the entry code of piece `w.length`. -/
def walkWordFast (k : Nat) : List (Nat × Nat) → Nat → Nat
  | [], cur => cur
  | (d, t) :: rest, cur =>
    let endP := pieceAdvance k (k - 2 - d) cur
    walkWordFast k rest (w3Code k (S.exc k endP) t)

/-- Pure-kernel `O(i2)` two-point collision witness verifier. -/
def checkWitness (k : Nat) (w : List (Nat × Nat)) (wit : Nat × Nat × Nat × Nat) : Bool :=
  let (i1, j1, i2, j2) := wit
  if !(Nat.ble (i1 + 1) i2 && Nat.ble i2 w.length) then false
  else
    let ok1 := Nat.ble (j1 + 1) (k - 1 - (w.getD i1 (0, 0)).1)
    let ok2 :=
      if Nat.ble (i2 + 1) w.length then Nat.ble (j2 + 1) (k - 1 - (w.getD i2 (0, 0)).1)
      else Nat.beq j2 0
    if !(ok1 && ok2) then false
    else
      let e1 := walkWordFast k (w.take i1) (S.idc k)
      let c1 := pieceAdvance k j1 e1
      let e2 := walkWordFast k ((w.drop i1).take (i2 - i1)) e1
      let c2 := pieceAdvance k j2 e2
      Nat.beq (S.canon k c1) (S.canon k c2)

/-- Extract the 1-based `b`-th nibble (`1 ≤ b ≤ 13`, MSB first) of a 13-nibble code `g`. -/
def getNib13 (g b : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x1000000000000) 16)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x100000000000) 16)
          (Nat.mod (Nat.div g 0x10000000000) 16)
          (Nat.ble 3 b))
        (Nat.ble 2 b))
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x1000000000) 16)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x100000000) 16)
          (Nat.mod (Nat.div g 0x10000000) 16)
          (Nat.ble 6 b))
        (Nat.ble 5 b))
      (Nat.ble 4 b))
    (@Bool.rec (fun _ => Nat)
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x1000000) 16)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x100000) 16)
          (Nat.mod (Nat.div g 0x10000) 16)
          (Nat.ble 9 b))
        (Nat.ble 8 b))
      (@Bool.rec (fun _ => Nat)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x1000) 16)
          (Nat.mod (Nat.div g 0x100) 16)
          (Nat.ble 11 b))
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x10) 16)
          (Nat.mod g 16)
          (Nat.ble 13 b))
        (Nat.ble 12 b))
      (Nat.ble 10 b))
    (Nat.ble 7 b)

/-- `S_{13}` composition `g ∘ h` on 1-based 13-nibble permutation codes (`S.idc 13 = 0x123456789abcd`). -/
def compose13 (g h : Nat) : Nat :=
  let n0 := getNib13 g (Nat.mod (Nat.div h 0x1000000000000) 16)
  let n1 := getNib13 g (Nat.mod (Nat.div h 0x100000000000) 16)
  let n2 := getNib13 g (Nat.mod (Nat.div h 0x10000000000) 16)
  let n3 := getNib13 g (Nat.mod (Nat.div h 0x1000000000) 16)
  let n4 := getNib13 g (Nat.mod (Nat.div h 0x100000000) 16)
  let n5 := getNib13 g (Nat.mod (Nat.div h 0x10000000) 16)
  let n6 := getNib13 g (Nat.mod (Nat.div h 0x1000000) 16)
  let n7 := getNib13 g (Nat.mod (Nat.div h 0x100000) 16)
  let n8 := getNib13 g (Nat.mod (Nat.div h 0x10000) 16)
  let n9 := getNib13 g (Nat.mod (Nat.div h 0x1000) 16)
  let n10 := getNib13 g (Nat.mod (Nat.div h 0x100) 16)
  let n11 := getNib13 g (Nat.mod (Nat.div h 0x10) 16)
  let n12 := getNib13 g (Nat.mod h 16)
  Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul n0 16) n1) 16) n2) 16) n3) 16) n4) 16) n5) 16) n6) 16) n7) 16) n8) 16) n9) 16) n10) 16) n11) 16) n12

/-! ### 3. Level-1 & Level-2 macro-expansion and `IsWindow` flag transitions -/

/-- Expand a single L1 macro-symbol `(m, d, t)` into `m` copies of `(0, 4)` followed by `(d, t)`. -/
def expandSym (m d t : Nat) : List (Nat × Nat) :=
  List.replicate m (0, 4) ++ [(d, t)]

/-- Special repeated L1 symbol `symA = (9, 2, 4)` for `k = 13`. -/
def symA13 : Nat × Nat × Nat := (9, 2, 4)

/-- Expand `r` copies of `symA13` into raw `(d, t)` pairs. -/
def expandSymARep (r : Nat) : List (Nat × Nat) :=
  (List.replicate r symA13).flatMap fun (m, d, t) => expandSym m d t

/-- Expand an L2 macro-symbol `(r, (m, d, t))` into raw `(d, t)` pairs (`r` copies of `symA13` + `(m, d, t)`). -/
def expandL2Sym (r m d t : Nat) : List (Nat × Nat) :=
  expandSymARep r ++ expandSym m d t

/-- `IsWindow` flag transition for a single deficit `d`. -/
def stepF (f d : Nat) : Option Nat :=
  if d == 0 then
    if f == 1 then none else some 0
  else if d == 1 then
    if f == 2 then some 2 else some 1
  else
    some 2

/-- `IsWindow` flag transition for an L1 macro-symbol `(m, d)`. -/
def nextF (f m d : Nat) : Option Nat :=
  if f == 1 && (m ≥ 1 || d == 0) then none
  else
    let fm := if m ≥ 1 then 0 else f
    if d == 0 then some 0
    else if d == 1 then some (if fm == 2 then 2 else 1)
    else some 2

/-- `IsWindow` flag transition for an L2 macro-symbol `(r, (m, d))` (`r` copies of `(9, 2)` + `(m, d)`). -/
def nextFL2 (f r m d : Nat) : Option Nat :=
  if r == 0 then nextF f m d
  else if f == 1 then none
  else nextF 2 m d

/-! ### 4. Level-2 `TropicCEGAR` Certificate Structure & Pure-Kernel Checkers -/

/-- Complete exact-integer Level-2 `TropicCEGAR` certificate for `k = 13`. -/
structure L2Cert where
  -- Theorem C & Level-2 parameters (for k = 13)
  D_track : Nat
  R_max : Nat
  cn : Nat
  bn : Nat
  q : Nat
  A : Nat
  bias : Nat
  -- L1 alphabet
  alpha1 : Nat
  idA : Nat
  sym1Info : Nat → Nat × Nat × Nat
  sym1Id : Nat → Nat → Nat → Option Nat
  sym1InvWit : Nat → Nat → Nat → Nat × Nat × Nat × Nat
  -- Precomputed S_13 elements
  pow04 : Nat → Nat        -- m ∈ 0..10
  powA : Nat → Nat         -- r ∈ 0..R_max
  l1Elem : Nat → Nat       -- s1 < alpha1
  -- forb1_2 (alpha1 × alpha1): 0 = allowed; w + 1 = forbidden with packed witness (i1:4|j1:4|i2:4|j2:4)
  forb1Pack : Nat → Nat → Nat
  -- L2 single validity for r ∈ 0..R_max, s1 < alpha1 (s1 ≠ idA)
  l2Valid : Nat → Nat → Bool
  l2InvWit : Nat → Nat → Nat × Nat × Nat × Nat
  -- Tracked L2 symbols: 0 .. nLong-1 (long) + nLong .. nLong+nPair-1 (pair)
  nLong : Nat              -- 10
  nPair : Nat              -- 2
  trInfo : Nat → Nat × Nat
  trId : Nat → Nat → Option Nat
  d1Long : Nat → Nat
  -- Precomputed constants for the 10 long symbols (checked in baseCheck)
  longPos : Nat → Nat      -- 2 * q * (10 * r + m + 1)
  longNeg : Nat → Nat      -- A * (2 * r + d)
  longD1Psi : Nat → Nat    -- stPsi (d1Long li)
  -- Len-2 CEGAR forbidden pairs among tracked symbols
  forb2 : Nat → Nat → Bool
  forb2Fid : Nat → Nat → Nat
  -- BPE DAG for all CEGAR words
  nBpe : Nat
  bpeLeft : Nat → Nat
  bpeRight : Nat → Nat
  bpeElem : Nat → Nat
  nCegar : Nat
  cegarFirst : Nat → Nat
  cegarMid : Nat → List Nat
  cegarLast : Nat → Nat
  cegarWit : Nat → Nat     -- packed (i1:7 | j1:4 | i2:7 | j2:4)
  deadLeafU : Nat → Nat    -- 0 if len-2 word; alive trie state u > 0 if len-3+ direct dead leaf
  deadLeafLi : Nat → Nat
  -- Alive AC trie states (0 = root placeholder with goPack 0 = d1Long[0..9]; 1..nAlive-1 = alive nodes)
  nAlive : Nat
  stPack : Nat → Nat       -- par(20b) | sym(4b) | fail(20b) | psi(20b)
  goPack : Nat → Nat       -- 10 × 20b: 0 = dead via fail; 1..nAlive-1 = alive v; 600000+fid = direct dead leaf
  -- Small non-trie potentials (shifted by bias)
  rootPsi : Nat → Option Nat
  pairPsi : Nat → Nat → Option Nat
  rootS1Psi : Nat → Nat → Option Nat
  maxTrPsi : Nat → Nat     -- li < nLong ↦ max stPsi u over all u with stSym u = li
  -- Base collision witnesses
  witZeroRun : Nat × Nat × Nat × Nat
  witAfterD0 : Nat → Nat × Nat × Nat × Nat
  witSymARun : Nat × Nat × Nat × Nat

/-- Sentinel threshold in `goPack` encoding direct dead trie leaves (`600000 + fid`). -/
def deadLeafBase : Nat := 600000

/-- Unpack trie state fields from `stPack u`. -/
def getStPar (cert : L2Cert) (u : Nat) : Nat := Nat.mod (cert.stPack u) 0x100000
def getStSym (cert : L2Cert) (u : Nat) : Nat := Nat.mod (Nat.div (cert.stPack u) 0x100000) 16
def getStFail (cert : L2Cert) (u : Nat) : Nat := Nat.mod (Nat.div (cert.stPack u) 0x1000000) 0x100000
def getStPsi (cert : L2Cert) (u : Nat) : Nat := Nat.div (cert.stPack u) 0x100000000000

/-- Extract lane `li ∈ 0..9` (20 bits) from a packed 200-bit `goPack` word using balanced `@Bool.rec`. -/
def getLane20 (g li : Nat) : Nat :=
  @Bool.rec (fun _ => Nat)
    (@Bool.rec (fun _ => Nat)
      (@Bool.rec (fun _ => Nat)
        (Nat.mod g 0x100000)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x100000) 0x100000)
          (Nat.mod (Nat.div g 0x10000000000) 0x100000)
          (Nat.ble 2 li))
        (Nat.ble 1 li))
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x1000000000000000) 0x100000)
        (Nat.mod (Nat.div g 0x100000000000000000000) 0x100000)
        (Nat.ble 4 li))
      (Nat.ble 3 li))
    (@Bool.rec (fun _ => Nat)
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x10000000000000000000000000) 0x100000)
        (@Bool.rec (fun _ => Nat)
          (Nat.mod (Nat.div g 0x1000000000000000000000000000000) 0x100000)
          (Nat.mod (Nat.div g 0x100000000000000000000000000000000000) 0x100000)
          (Nat.ble 7 li))
        (Nat.ble 6 li))
      (@Bool.rec (fun _ => Nat)
        (Nat.mod (Nat.div g 0x10000000000000000000000000000000000000000) 0x100000)
        (Nat.mod (Nat.div g 0x1000000000000000000000000000000000000000000000) 0x100000)
        (Nat.ble 9 li))
      (Nat.ble 8 li))
    (Nat.ble 5 li)

def getGo (cert : L2Cert) (u li : Nat) : Nat :=
  getLane20 (cert.goPack u) li

def isForb1 (cert : L2Cert) (a b : Nat) : Bool :=
  !Nat.beq (cert.forb1Pack a b) 0

/-! ### 5. Base, Alphabet, `S_{13}` Power, `forb1_2`, and `l2Valid` Checkers -/

/-- Base collision checks + `pow04`/`powA` + `idA` + `d1Long` + `longPos/Neg/D1Psi` + `forb2` consistency. -/
def baseCheckL2 (cert : L2Cert) : Bool :=
  -- Base structural collisions
  checkWitness 13 (List.replicate 11 (0, 4)) cert.witZeroRun &&
  checkRangeAux 0 (fun t => checkWitness 13 [(0, t), (0, 4)] (cert.witAfterD0 t)) 4 &&
  checkWitness 13 (expandSymARep (cert.R_max + 1)) cert.witSymARun &&
  -- idA is symA13 = (9, 2, 4)
  Nat.ble (cert.idA + 1) cert.alpha1 &&
  (cert.sym1Info cert.idA == symA13) &&
  (cert.sym1Id 9 2 4 == some cert.idA) &&
  -- pow04[0..10]
  checkRangeAux 0 (fun m =>
    Nat.beq (cert.pow04 m) (walkWordFast 13 (List.replicate m (0, 4)) (S.idc 13))) 11 &&
  -- powA[0..R_max]
  checkRangeAux 0 (fun r =>
    Nat.beq (cert.powA r) (walkWordFast 13 (expandSymARep r) (S.idc 13))) (cert.R_max + 1) &&
  -- nLong == 10, root psi[1] >= bias, d1Long and goPack 0
  Nat.beq cert.nLong 10 &&
  oLeN (some cert.bias) (cert.rootPsi 1) &&
  checkRangeAux 0 (fun li =>
    let u := cert.d1Long li
    let r := (cert.trInfo li).1
    let s1 := (cert.trInfo li).2
    let m := (cert.sym1Info s1).1
    let d := (cert.sym1Info s1).2.1
    Nat.ble 1 u && Nat.ble (u + 1) cert.nAlive &&
    Nat.beq (getStPar cert u) 0 &&
    Nat.beq (getStSym cert u) li &&
    Nat.beq (getStFail cert u) 0 &&
    Nat.beq (getGo cert 0 li) u &&
    Nat.beq (cert.longPos li) (2 * cert.q * (10 * r + m + 1)) &&
    Nat.beq (cert.longNeg li) (cert.A * (2 * r + d)) &&
    Nat.beq (cert.longD1Psi li) (getStPsi cert u) &&
    -- All long symbols have can_A = true (not forb1 with idA)
    !isForb1 cert s1 cert.idA) cert.nLong &&
  -- All tracked symbols (long + pair) are valid L2 symbols with m ≥ 1, d = 2, and consistent trId
  checkRangeAux 0 (fun ti =>
    let r := (cert.trInfo ti).1
    let s1 := (cert.trInfo ti).2
    let m := (cert.sym1Info s1).1
    let d := (cert.sym1Info s1).2.1
    Nat.ble r cert.R_max && Nat.ble (s1 + 1) cert.alpha1 &&
    !Nat.beq s1 cert.idA &&
    cert.l2Valid r s1 &&
    (cert.trId r s1 == some ti) &&
    Nat.ble 1 m && Nat.beq d 2) (cert.nLong + cert.nPair) &&
  -- No (long, long) pair is forbidden by forb1 or forb2
  checkRangeAux 0 (fun li1 =>
    let s1_1 := (cert.trInfo li1).2
    checkRangeAux 0 (fun li2 =>
      let r2 := (cert.trInfo li2).1
      let s1_2 := (cert.trInfo li2).2
      let fst2 := if r2 == 0 then s1_2 else cert.idA
      !isForb1 cert s1_1 fst2 && !cert.forb2 li1 li2) cert.nLong) cert.nLong &&
  -- All forb2 pairs are backed by len-2 CEGAR words
  checkRangeAux 0 (fun ti1 =>
    checkRangeAux 0 (fun ti2 =>
      if cert.forb2 ti1 ti2 then
        let fid := cert.forb2Fid ti1 ti2
        Nat.ble (fid + 1) cert.nCegar &&
        Nat.beq (cert.cegarFirst fid) ti1 &&
        (cert.cegarMid fid == []) &&
        Nat.beq (cert.cegarLast fid) ti2
      else true) (cert.nLong + cert.nPair)) (cert.nLong + cert.nPair)

/-- Check L1 alphabet completeness for `(m, d, t)` (`m ≤ 10, d ≤ D_track, t < 5`). -/
def alpha1TripleCheck (cert : L2Cert) (m d t : Nat) : Bool :=
  if d == 0 && t == 4 then true
  else match cert.sym1Id m d t with
    | some s1 => Nat.ble (s1 + 1) cert.alpha1 && (cert.sym1Info s1 == (m, d, t))
    | none => checkWitness 13 (expandSym m d t) (cert.sym1InvWit m d t)

/-- Check `l1Elem s1` and `sym1Info s1` bounds for `s1 < alpha1`. -/
def l1ElemCheck (cert : L2Cert) (s1 : Nat) : Bool :=
  let m := (cert.sym1Info s1).1
  let d := (cert.sym1Info s1).2.1
  let t := (cert.sym1Info s1).2.2
  Nat.ble m 10 && Nat.ble d cert.D_track && Nat.ble (t + 1) 5 &&
  !(d == 0 && t == 4) &&
  Nat.beq (cert.l1Elem s1) (walkWordFast 13 (expandSym m d t) (S.idc 13))

/-- Check `forb1Pack a b`: if nonzero, unpacks to a valid two-point `S_{13}` collision witness for `[a, b]`. -/
def forb1PairCheck (cert : L2Cert) (a b : Nat) : Bool :=
  let pk := cert.forb1Pack a b
  if Nat.beq pk 0 then true
  else
    let w := pk - 1
    let i1 := Nat.mod w 16
    let j1 := Nat.mod (Nat.div w 16) 16
    let i2 := Nat.mod (Nat.div w 256) 16
    let j2 := Nat.mod (Nat.div w 4096) 16
    let m1 := (cert.sym1Info a).1
    let d1 := (cert.sym1Info a).2.1
    let m2 := (cert.sym1Info b).1
    let d2 := (cert.sym1Info b).2.1
    let ok1 := Nat.ble i1 m1 && Nat.ble (j1 + 1) (12 - (if Nat.beq i1 m1 then d1 else 0))
    let ok2 := Nat.ble i2 (m2 + 1) &&
      (if Nat.beq i2 (m2 + 1) then Nat.beq j2 0
       else Nat.ble (j2 + 1) (12 - (if Nat.beq i2 m2 then d2 else 0)))
    if !(ok1 && ok2) then false
    else
      let c1 := pieceAdvance 13 j1 (cert.pow04 i1)
      let h2 := if Nat.beq i2 (m2 + 1) then cert.l1Elem b else cert.pow04 i2
      let c2 := pieceAdvance 13 j2 (compose13 (cert.l1Elem a) h2)
      Nat.beq (S.canon 13 c1) (S.canon 13 c2)

/-- Check all `forb1` pairs for a single first symbol `a < alpha1`. -/
def forb1RowCheck (cert : L2Cert) (a : Nat) : Bool :=
  checkRangeChunked 0 cert.alpha1 (fun b => forb1PairCheck cert a b)

/-- Check `l2Valid r s1` and `trId r s1` consistency for `r ≤ R_max, s1 < alpha1, s1 ≠ idA`. -/
def l2SingleCheck (cert : L2Cert) (r s1 : Nat) : Bool :=
  if Nat.beq s1 cert.idA then true
  else
    let m := (cert.sym1Info s1).1
    let d := (cert.sym1Info s1).2.1
    let t := (cert.sym1Info s1).2.2
    if cert.l2Valid r s1 then
      match cert.trId r s1 with
      | none => true
      | some ti => Nat.ble (ti + 1) (cert.nLong + cert.nPair) && (cert.trInfo ti == (r, s1))
    else
      Nat.ble 1 r && checkWitness 13 (expandL2Sym r m d t) (cert.l2InvWit r s1)

/-! ### 6. BPE DAG, CEGAR Collision Witnesses, and Direct Dead Leaf Suffix Checks -/

/-- Deficit of the `i`-th piece inside `expandL2Sym r m d t` (`i < 10 * r + m + 1`). -/
def l2PieceDef (r m d i : Nat) : Nat :=
  if Nat.ble (i + 1) (10 * r) then
    if Nat.beq (Nat.mod i 10) 9 then 2 else 0
  else if Nat.beq i (10 * r + m) then d
  else 0

/-- O(1) prefix code `walkWordFast 13 ((expandL2Sym r m d t).take i) (S.idc 13)` via `powA`, `pow04`, `l1Elem`. -/
def walkL2Prefix13 (cert : L2Cert) (r s1 m i : Nat) : Nat :=
  if Nat.ble (i + 1) (10 * r) then
    let qA := Nat.div i 10
    let rem := Nat.mod i 10
    if Nat.beq qA 0 then cert.pow04 rem else compose13 (cert.powA qA) (cert.pow04 rem)
  else if Nat.ble i (10 * r + m) then
    let rem := i - 10 * r
    if Nat.beq r 0 then cert.pow04 rem else compose13 (cert.powA r) (cert.pow04 rem)
  else
    if Nat.beq r 0 then cert.l1Elem s1 else compose13 (cert.powA r) (cert.l1Elem s1)

/-- Check `bpeElem t` for `t < nBpe` (`t < nLong + nPair` = base tracked L2 sym; `t ≥` = merge of two `< t`). -/
def bpeElemCheck (cert : L2Cert) (t : Nat) : Bool :=
  let nTr := cert.nLong + cert.nPair
  if Nat.ble (t + 1) nTr then
    let r := (cert.trInfo t).1
    let s1 := (cert.trInfo t).2
    let exp := if Nat.beq r 0 then cert.l1Elem s1 else compose13 (cert.powA r) (cert.l1Elem s1)
    Nat.beq (cert.bpeElem t) exp
  else
    let l := cert.bpeLeft t
    let r := cert.bpeRight t
    Nat.ble (l + 1) t && Nat.ble (r + 1) t &&
    Nat.beq (cert.bpeElem t) (compose13 (cert.bpeElem l) (cert.bpeElem r))

/-- Check collision witness for CEGAR word `fid < nCegar` using BPE `S_{13}` composition. -/
def cegarWitCheck (cert : L2Cert) (fid : Nat) : Bool :=
  let nTr := cert.nLong + cert.nPair
  let s0 := cert.cegarFirst fid
  let mid := cert.cegarMid fid
  let sL := cert.cegarLast fid
  if !(Nat.ble (s0 + 1) nTr && Nat.ble (sL + 1) nTr && mid.all (fun t => Nat.ble (t + 1) cert.nBpe)) then
    false
  else
    let w := cert.cegarWit fid
    let i1 := Nat.mod w 128
    let j1 := Nat.mod (Nat.div w 128) 16
    let i2 := Nat.mod (Nat.div w 2048) 128
    let j2 := Nat.mod (Nat.div w 262144) 16
    let r0 := (cert.trInfo s0).1
    let s1_0 := (cert.trInfo s0).2
    let m0 := (cert.sym1Info s1_0).1
    let d0 := (cert.sym1Info s1_0).2.1
    let rL := (cert.trInfo sL).1
    let s1_L := (cert.trInfo sL).2
    let mL := (cert.sym1Info s1_L).1
    let dL := (cert.sym1Info s1_L).2.1
    let len0 := 10 * r0 + m0 + 1
    let lenL := 10 * rL + mL + 1
    let ok1 := Nat.ble (i1 + 1) len0 && Nat.ble (j1 + 1) (12 - l2PieceDef r0 m0 d0 i1)
    let ok2 := Nat.ble i2 lenL &&
      (if Nat.beq i2 lenL then Nat.beq j2 0
       else Nat.ble (j2 + 1) (12 - l2PieceDef rL mL dL i2))
    if !(ok1 && ok2) then false
    else
      let e1 := walkL2Prefix13 cert r0 s1_0 m0 i1
      let c1 := pieceAdvance 13 j1 e1
      let gMid := mid.foldl (fun acc tok => compose13 acc (cert.bpeElem tok)) (cert.bpeElem s0)
      let e2 := compose13 gMid (walkL2Prefix13 cert rL s1_L mL i2)
      let c2 := pieceAdvance 13 j2 e2
      Nat.beq (S.canon 13 c1) (S.canon 13 c2)

/-- Match a single BPE token `tok` backwards along `stPar`/`stSym` starting at trie state `u`. -/
def matchBPETokRev (cert : L2Cert) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, u, tok =>
    let nTr := cert.nLong + cert.nPair
    if Nat.ble (tok + 1) nTr then
      if Nat.beq u 0 then none
      else
        let st := cert.stPack u
        let par := Nat.mod st 0x100000
        let sym := Nat.mod (Nat.div st 0x100000) 16
        if Nat.beq sym tok then some par else none
    else
      match matchBPETokRev cert fuel u (cert.bpeRight tok) with
      | none => none
      | some u1 => matchBPETokRev cert fuel u1 (cert.bpeLeft tok)

/-- Match a reversed list of BPE tokens backwards along `stPar`/`stSym`. -/
def matchBPEListRev (cert : L2Cert) (fuel : Nat) : Nat → List Nat → Option Nat
  | u, [] => some u
  | u, tok :: rest =>
    match matchBPETokRev cert fuel u tok with
    | none => none
    | some u1 => matchBPEListRev cert fuel u1 rest

/-- Check that direct dead leaf `(deadLeafU fid, deadLeafLi fid)` ends with `cegarWord fid`. -/
def cegarLeafCheck (cert : L2Cert) (fid : Nat) : Bool :=
  let u := cert.deadLeafU fid
  if Nat.beq u 0 then true
  else
    let li := cert.deadLeafLi fid
    if !(Nat.ble (u + 1) cert.nAlive && Nat.ble (li + 1) cert.nLong &&
         Nat.beq (cert.cegarLast fid) li) then false
    else
      match matchBPEListRev cert 64 u (cert.cegarMid fid).reverse with
      | none => false
      | some u1 =>
        if Nat.beq u1 0 then false
        else Nat.beq (getStSym cert u1) (cert.cegarFirst fid)

/-! ### 7. Small Non-Trie State Checkers (`reset`, `endBound`, and all L2 transitions) -/

/-- Pure-`Nat` reset transition check from `(srcPsi, f, d0, canA)` to `(root, 2)`. -/
def resetCheckL2 (cert : L2Cert) (srcPsi : Option Nat) (f : Nat) (d0 canA : Bool) : Bool :=
  let neg0 := cert.A * (cert.D_track + 1)
  if Nat.beq f 1 || d0 then
    oStepLeN srcPsi (2 * cert.q) neg0 (cert.rootPsi 2)
  else if !canA then
    oStepLeN srcPsi (2 * cert.q * 11) neg0 (cert.rootPsi 2)
  else
    oStepLeN srcPsi (2 * cert.q * 11) neg0 (cert.rootPsi 2) &&
    oStepLeN srcPsi (2 * cert.q * (10 * cert.R_max + 11))
      (cert.A * (2 * cert.R_max + cert.D_track + 1)) (cert.rootPsi 2)

/-- Pure-`Nat` end-of-window bound check (`eA`, `eB`, `eC`) for `(srcPsi, f, d0, canA)`. -/
def endBoundCheckL2 (cert : L2Cert) (srcPsi : Option Nat) (f : Nat) (d0 canA : Bool) : Bool :=
  match srcPsi with
  | none => true
  | some pu =>
    let c1 := 2 * cert.q * 9
    let rhsBase := cert.bias + cert.bn
    let okA := Nat.ble (pu + 2 * cert.q + c1) (rhsBase + (if Nat.beq f 2 then cert.A else 2 * cert.A))
    let okB :=
      if Nat.beq f 1 || d0 then true
      else Nat.ble (pu + 2 * cert.q * 11 + c1) (rhsBase + 2 * cert.A)
    let okC :=
      if Nat.beq f 1 || d0 || !canA then true
      else
        let rM := cert.R_max
        Nat.ble (pu + 2 * cert.q * 10 + 2 * cert.q + c1) (rhsBase + 3 * cert.A) &&
        Nat.ble (pu + 2 * cert.q * 10 + 2 * cert.q * 11 + c1) (rhsBase + 4 * cert.A) &&
        Nat.ble (pu + 2 * cert.q * 10 * rM + 2 * cert.q + c1) (rhsBase + (2 * rM + 1) * cert.A) &&
        Nat.ble (pu + 2 * cert.q * 10 * rM + 2 * cert.q * 11 + c1) (rhsBase + (2 * rM + 2) * cert.A)
    okA && okB && okC

/-- Check all L2 transitions `(r, s1)` from a single `(srcPsi, f, lastS1, lastTr, skipLong)`. -/
def edgesFromSrcF (cert : L2Cert) (srcPsi : Option Nat) (f : Nat)
    (lastS1 lastTr : Option Nat) (skipLong : Bool) : Bool :=
  match srcPsi with
  | none => true
  | some pu =>
    checkRangeAux 0 (fun r =>
      checkRangeChunked 0 cert.alpha1 (fun s1 =>
        if Nat.beq s1 cert.idA || !cert.l2Valid r s1 then true
        else
          let fstS1 := if Nat.beq r 0 then s1 else cert.idA
          let forbBy1 := match lastS1 with
            | none => false
            | some lc => isForb1 cert lc fstS1
          if forbBy1 then true
          else
            let m := (cert.sym1Info s1).1
            let d := (cert.sym1Info s1).2.1
            match nextFL2 f r m d with
            | none => true
            | some nf =>
              let pos := 2 * cert.q * (10 * r + m + 1)
              let neg := cert.A * (2 * r + d)
              match cert.trId r s1 with
              | none =>
                oStepLeN (some pu) pos neg (cert.rootS1Psi s1 nf)
              | some ti =>
                let forbBy2 := match lastTr with
                  | none => false
                  | some lt => cert.forb2 lt ti
                if forbBy2 then true
                else if Nat.ble (ti + 1) cert.nLong then
                  if skipLong then true
                  else
                    let dstPsi := if Nat.beq nf 2 then some (cert.longD1Psi ti) else none
                    oStepLeN (some pu) pos neg dstPsi
                else
                  let pi := ti - cert.nLong
                  oStepLeN (some pu) pos neg (cert.pairPsi pi nf)
      )) (cert.R_max + 1)

/-- Check `root` state (`reset`, `endBound`, and all L2 edges for `f ∈ 0..2`). -/
def checkRoot (cert : L2Cert) : Bool :=
  checkRangeAux 0 (fun f =>
    resetCheckL2 cert (cert.rootPsi f) f false true &&
    endBoundCheckL2 cert (cert.rootPsi f) f false true &&
    edgesFromSrcF cert (cert.rootPsi f) f none none false) 3

/-- Check `pair pi` state (`pi < nPair`). -/
def checkPair (cert : L2Cert) (pi : Nat) : Bool :=
  let ti := cert.nLong + pi
  let s1 := (cert.trInfo ti).2
  let canA := !isForb1 cert s1 cert.idA
  checkRangeAux 0 (fun f =>
    resetCheckL2 cert (cert.pairPsi pi f) f false canA &&
    endBoundCheckL2 cert (cert.pairPsi pi f) f false canA &&
    edgesFromSrcF cert (cert.pairPsi pi f) f (some s1) (some ti) false) 3

/-- Check `rootS1 s1` state (`s1 < alpha1, s1 ≠ idA`). -/
def checkRootS1 (cert : L2Cert) (s1 : Nat) : Bool :=
  if Nat.beq s1 cert.idA then true
  else
    let d := (cert.sym1Info s1).2.1
    let d0 := Nat.beq d 0
    let canA := !isForb1 cert s1 cert.idA
    checkRangeAux 0 (fun f =>
      resetCheckL2 cert (cert.rootS1Psi s1 f) f d0 canA &&
      endBoundCheckL2 cert (cert.rootS1Psi s1 f) f d0 canA &&
      edgesFromSrcF cert (cert.rootS1Psi s1 f) f (some s1) none false) 3

/-- Check `maxTrPsi li` (`li < nLong`): reset, endBound, and all non-long L2 edges at `f = 2`! -/
def checkMaxTr (cert : L2Cert) (li : Nat) : Bool :=
  let s1 := (cert.trInfo li).2
  let pu := some (cert.maxTrPsi li)
  resetCheckL2 cert pu 2 false true &&
  endBoundCheckL2 cert pu 2 false true &&
  edgesFromSrcF cert pu 2 (some s1) (some li) true

/-! ### 8. O(1) Per-State Alive AC Trie Checker (`573,188` states!) -/

/-- Check one outgoing long-symbol edge `(u, li)` with `v = getGo u li`, `fv = getGo fail u li`. -/
def trieEdgeCheckOne (cert : L2Cert) (u psi li v fv pos neg d1Psi : Nat) : Bool :=
  if Nat.beq v 0 then
    Nat.beq fv 0 || Nat.ble deadLeafBase fv
  else if Nat.ble deadLeafBase v then
    let fid := v - deadLeafBase
    Nat.ble (fid + 1) cert.nCegar &&
    Nat.beq (cert.deadLeafU fid) u &&
    Nat.beq (cert.deadLeafLi fid) li
  else
    Nat.ble (v + 1) cert.nAlive &&
    if Nat.beq v fv then
      Nat.ble (Nat.add psi pos) (Nat.add d1Psi neg) ||
      Nat.ble (Nat.add psi pos) (Nat.add (getStPsi cert v) neg)
    else
      let stv := cert.stPack v
      Nat.beq (Nat.mod stv 0x100000) u &&
      Nat.beq (Nat.mod (Nat.div stv 0x100000) 16) li &&
      (Nat.ble (Nat.add psi pos) (Nat.add d1Psi neg) ||
       Nat.ble (Nat.add psi pos) (Nat.add (Nat.div stv 0x100000000000) neg))

/-- Check a single alive AC trie state `u ∈ 1..nAlive-1` in O(1) (unrolled over `li = 0..9`). -/
def trieStateCheck (cert : L2Cert) (u : Nat) : Bool :=
  let st := cert.stPack u
  let par := Nat.mod st 0x100000
  let sym := Nat.mod (Nat.div st 0x100000) 16
  let fail := Nat.mod (Nat.div st 0x1000000) 0x100000
  let psi := Nat.div st 0x100000000000
  if !(Nat.ble (par + 1) u && Nat.ble (sym + 1) 10 && Nat.ble (fail + 1) u &&
       Nat.ble psi (cert.maxTrPsi sym)) then false
  else
    let okFail :=
      if Nat.beq par 0 then Nat.beq fail 0
      else
        let failPar := Nat.mod (Nat.div (cert.stPack par) 0x1000000) 0x100000
        Nat.ble 1 fail && Nat.beq fail (getGo cert failPar sym)
    if !okFail then false
    else
      let goU := cert.goPack u
      let goF := cert.goPack fail
      trieEdgeCheckOne cert u psi 0 (Nat.mod goU 0x100000) (Nat.mod goF 0x100000) (cert.longPos 0) (cert.longNeg 0) (cert.longD1Psi 0) &&
      trieEdgeCheckOne cert u psi 1 (Nat.mod (Nat.div goU 0x100000) 0x100000) (Nat.mod (Nat.div goF 0x100000) 0x100000) (cert.longPos 1) (cert.longNeg 1) (cert.longD1Psi 1) &&
      trieEdgeCheckOne cert u psi 2 (Nat.mod (Nat.div goU 0x10000000000) 0x100000) (Nat.mod (Nat.div goF 0x10000000000) 0x100000) (cert.longPos 2) (cert.longNeg 2) (cert.longD1Psi 2) &&
      trieEdgeCheckOne cert u psi 3 (Nat.mod (Nat.div goU 0x1000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x1000000000000000) 0x100000) (cert.longPos 3) (cert.longNeg 3) (cert.longD1Psi 3) &&
      trieEdgeCheckOne cert u psi 4 (Nat.mod (Nat.div goU 0x100000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x100000000000000000000) 0x100000) (cert.longPos 4) (cert.longNeg 4) (cert.longD1Psi 4) &&
      trieEdgeCheckOne cert u psi 5 (Nat.mod (Nat.div goU 0x10000000000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x10000000000000000000000000) 0x100000) (cert.longPos 5) (cert.longNeg 5) (cert.longD1Psi 5) &&
      trieEdgeCheckOne cert u psi 6 (Nat.mod (Nat.div goU 0x1000000000000000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x1000000000000000000000000000000) 0x100000) (cert.longPos 6) (cert.longNeg 6) (cert.longD1Psi 6) &&
      trieEdgeCheckOne cert u psi 7 (Nat.mod (Nat.div goU 0x100000000000000000000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x100000000000000000000000000000000000) 0x100000) (cert.longPos 7) (cert.longNeg 7) (cert.longD1Psi 7) &&
      trieEdgeCheckOne cert u psi 8 (Nat.mod (Nat.div goU 0x10000000000000000000000000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x10000000000000000000000000000000000000000) 0x100000) (cert.longPos 8) (cert.longNeg 8) (cert.longD1Psi 8) &&
      trieEdgeCheckOne cert u psi 9 (Nat.mod (Nat.div goU 0x1000000000000000000000000000000000000000000000) 0x100000) (Nat.mod (Nat.div goF 0x1000000000000000000000000000000000000000000000) 0x100000) (cert.longPos 9) (cert.longNeg 9) (cert.longD1Psi 9)

end

end TropicL2
end SuperpermLowerBounds
