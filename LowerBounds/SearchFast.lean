import LowerBounds.SSearch

/-!
# Zero-allocation LIFO flat `Array Nat` + `UInt64` window search (`SearchFast`)

A 100%-total, linearly-threaded `UInt64` + flat open-addressed `Array Nat` (`262144` slots)
implementation of Halfar's window search `S.search` (`SSearch.lean`).

* Every `k`-hex-digit code (`5 ≤ k ≤ 15`) satisfies `c < 16^k ≤ 2^60 < 2^63`, so `UInt64`
  arithmetic never overflows and `Array Nat` stores unboxed 63-bit tagged scalars.
* Returning `#[]` (`tab.size == 0`) to signal `found = true` eliminates `Bool × Array` boxing.
* Strict LIFO backtracking restores `tab` identically via `tab.set! slot 0`.
* `LowerBounds.SearchFastEq` proves in the Lean kernel:
  `5 ≤ k → k ≤ 15 → searchFast k A q2 C1 C2 bn fuel = false → search k A q2 C1 C2 bn fuel = false`.
-/

namespace SuperpermLowerBounds
namespace S

@[inline] def excU (sh1 : UInt64) (c : UInt64) : UInt64 :=
  ((c &&& 0xF) <<< sh1) ||| (c >>> 4)

@[inline] def doorU (sh1 sh2 mask2 : UInt64) (x : UInt64) : UInt64 :=
  ((x &&& mask2) <<< 8) ||| (((x >>> sh2) &&& 0xF) <<< 4) ||| (x >>> sh1)

/-- `Nat.log2 z.toNat / 4` computed purely in `UInt64` (zero allocations). -/
@[inline] def nibbleLog2 (z : UInt64) : Nat :=
  let r0 : Nat := if z >= 0x100000000 then 8 else 0
  let z1 : UInt64 := if z >= 0x100000000 then z >>> 32 else z
  let r1 : Nat := if z1 >= 0x10000 then r0 + 4 else r0
  let z2 : UInt64 := if z1 >= 0x10000 then z1 >>> 16 else z1
  let r2 : Nat := if z2 >= 0x100 then r1 + 2 else r1
  let z3 : UInt64 := if z2 >= 0x100 then z2 >>> 8 else z2
  if z3 >= 0x10 then r2 + 1 else r2

@[inline] def posU (kMask c : UInt64) : Nat :=
  let x := c ^^^ kMask
  let y := (((x &&& 0x7777777777777777) + 0x7777777777777777) ||| x) &&& 0x8888888888888888
  let z := y ^^^ 0x8888888888888888
  nibbleLog2 z

@[inline] def rotlU (k : Nat) (c : UInt64) (i : Nat) : UInt64 :=
  if i == 0 || i >= k then c
  else
    let sh : UInt64 := (4 * i).toUInt64
    let rsh : UInt64 := (4 * (k - i)).toUInt64
    let rmask : UInt64 := ((1 : UInt64) <<< rsh) - 1
    ((c &&& rmask) <<< sh) ||| (c >>> rsh)

@[inline] def canonU (k : Nat) (kMask : UInt64) (c : UInt64) : UInt64 :=
  rotlU k c ((k - 1) - posU kMask c)

def HT_SIZE : Nat := 262144
def HT_MASK : Nat := 262143
def HT_COLL : Nat := 262144
def HT_FULL : Nat := 262145

@[inline] def hashU (x : UInt64) : Nat :=
  let x := x ^^^ (x >>> 33)
  let x := x * 0xff51afd7ed558ccd
  let x := x ^^^ (x >>> 33)
  x.toNat &&& HT_MASK

/-- Linear probe starting at `i` for up to `steps` slots.
  Returns `< HT_SIZE` (free slot `j` with `tab.getD j 0 = 0`),
  `HT_COLL` (collision: `tab.getD j 0 = ck`), or `HT_FULL` (probe limit exceeded). -/
def probeHT (tab : Array Nat) (ck : Nat) : Nat → Nat → Nat
  | 0, _ => HT_FULL
  | steps + 1, i =>
    let v := tab.getD i 0
    if v == 0 then i
    else if v == ck then HT_COLL
    else probeHT tab ck steps ((i + 1) &&& HT_MASK)

mutual
def walkFast (k : Nat) (kMask sh1 sh2 sh3 mask2 mask3 : UInt64)
    (A q2 C1 C2 bn fuel P N f : Nat) : Nat → UInt64 → Array Nat → Array Nat
  | 0, _, tab => tab
  | n + 1, D, tab =>
    let ckU := canonU k kMask D
    let ck := ckU.toNat
    if ck == 0 then #[]
    else
      let slot := probeHT tab ck 512 (hashU ckU)
      if slot == HT_COLL then tab
      else if slot >= HT_SIZE then #[]
      else
        let tab := tab.set! slot ck
        let ex := excU sh1 D
        let tab :=
          if n == 0 then
            if f == 1 then tab
            else goFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel ex P (N + q2) 0 tab
          else
            let nP := P + A * n
            let nN := N + q2
            if nN + C2 <= nP then tab
            else if f == 0 then
              if N <= P then tab
              else goFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel ex nP nN (if 2 <= n then 2 else 1) tab
            else
              goFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel ex nP nN (if 2 <= n then 2 else f) tab
        if tab.size == 0 then tab
        else
          let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f n (doorU sh1 sh2 mask2 ex) tab
          if tab.size == 0 then tab
          else tab.set! slot 0

def goFast (k : Nat) (kMask sh1 sh2 sh3 mask2 mask3 : UInt64)
    (A q2 C1 C2 bn : Nat) : Nat → UInt64 → Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, _, _, _ => #[]
  | fuel + 1, y, P, N, f, tab =>
    if f == 2 && !(N + C1 <= P + bn) then #[]
    else
      let base := (y &&& mask3) <<< 12
      let a := y >>> sh1
      let b := (y >>> sh2) &&& 0xF
      let c := (y >>> sh3) &&& 0xF
      let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (a <<< 8) ||| (b <<< 4) ||| c) tab
      if tab.size == 0 then tab else
      let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (a <<< 8) ||| (c <<< 4) ||| b) tab
      if tab.size == 0 then tab else
      let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (b <<< 8) ||| (a <<< 4) ||| c) tab
      if tab.size == 0 then tab else
      let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (b <<< 8) ||| (c <<< 4) ||| a) tab
      if tab.size == 0 then tab else
      let tab := walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (c <<< 8) ||| (a <<< 4) ||| b) tab
      if tab.size == 0 then tab else
      walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (c <<< 8) ||| (b <<< 4) ||| a) tab
end

def idcU : Nat → UInt64
  | 0 => 0
  | n + 1 => (idcU n <<< 4) ||| (n + 1).toUInt64

def searchFast (k A q2 C1 C2 bn fuel : Nat) : Bool :=
  let kMask : UInt64 := k.toUInt64 * 0x1111111111111111
  let sh1 : UInt64 := (4 * (k - 1)).toUInt64
  let sh2 : UInt64 := (4 * (k - 2)).toUInt64
  let sh3 : UInt64 := (4 * (k - 3)).toUInt64
  let mask2 : UInt64 := ((1 : UInt64) <<< sh2) - 1
  let mask3 : UInt64 := ((1 : UInt64) <<< sh3) - 1
  let tab0 : Array Nat := Array.replicate HT_SIZE 0
  (walkFast k kMask sh1 sh2 sh3 mask2 mask3 A q2 C1 C2 bn fuel 0 0 1 (k - 1) (idcU k) tab0).size == 0

end S
end SuperpermLowerBounds
