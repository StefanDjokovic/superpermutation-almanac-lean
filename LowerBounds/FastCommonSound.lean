import LowerBounds.FastK16Search
import LowerBounds.K16Word

/-!
# Common Soundness Lemmas for `FastK16Search` and `FastJ16Search`

* Unboxed `ByteArray` accessors (`baGetU8`, `baSetU8`, `baGetU16`, `baGetI64`) and pure
  `Array.ofFn` packers (`packU16Arr`, `packI64Arr`), with ZERO extra axioms.
* Exact `Int32` / `Int64` overflow-free arithmetic helpers.
* Exact symbolic properties of `PS.permCodes 7 7`, `packBase7`, `buildCodeToIdx`,
  canonical `S_7`-equivariant transitions `w3Step` / `w4Step` (`s3Code` / `s4Code`), and
  `FastK16.buildS7K16Tabs`.
-/

namespace SuperpermLowerBounds
namespace FastSound

open S (PermW WLink DoorEq code)
open PS (permCodes ciTab nxtTab encB mem_perm tab_get arr_get idcF excF)
open FastK16

/-! ### `USize` and `ByteArray` Lemmas -/

theorem lt_usize_size_of_lt_u32 {n : ℕ} (h : n < 2 ^ 32) : n < USize.size := by
  have h1 : 2 ^ 32 ≤ USize.size := by
    cases System.Platform.numBits_eq with
    | inl h32 => simp [USize.size, h32]
    | inr h64 => simp [USize.size, h64]
  omega

theorem usize_ofNat_toNat {n : ℕ} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 h)]

theorem ba_usize_toNat {b : ByteArray} (h : b.size < 2 ^ 32) : b.usize.toNat = b.size :=
  usize_ofNat_toNat h

theorem ba_usize_eq_zero_iff {b : ByteArray} (h : b.size < 2 ^ 32) :
    (b.usize == 0) = true ↔ b.size = 0 := by
  simp only [beq_iff_eq]
  constructor
  · intro hz
    have h1 : b.usize.toNat = (0 : USize).toNat := congrArg USize.toNat hz
    rw [ba_usize_toNat h, USize.toNat_zero] at h1
    exact h1
  · intro hz
    apply USize.toNat_inj.mp
    rw [ba_usize_toNat h, USize.toNat_zero, hz]

theorem ba_uget_eq_get! {b : ByteArray} {i : USize} (hi : i.toNat < b.size) :
    b.uget i hi = b.get! i.toNat := by
  change b.data[i.toNat]'hi = b.get! i.toNat
  simp [ByteArray.get!, getElem!_pos, hi]

theorem baGetU8_eq_get! {b : ByteArray} {i : USize} (hb : b.size < 2 ^ 32) (hi : i.toNat < b.size) :
    baGetU8 b i = b.get! i.toNat := by
  have hlt : i < b.usize := by
    change i.toNat < b.usize.toNat
    rw [ba_usize_toNat hb]
    exact hi
  unfold baGetU8
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  exact ba_uget_eq_get! (lt_ba_size_of_lt_usize hlt)

theorem baSetU8_eq_set! {b : ByteArray} {i : USize} {v : UInt8} (hb : b.size < 2 ^ 32)
    (hi : i.toNat < b.size) : baSetU8 b i v = b.set! i.toNat v := by
  have hlt : i < b.usize := by
    change i.toNat < b.usize.toNat
    rw [ba_usize_toNat hb]
    exact hi
  unfold baSetU8
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  change ByteArray.mk (b.data.set i.toNat v _) = ByteArray.mk (b.data.setIfInBounds i.toNat v)
  congr 1
  simp [Array.setIfInBounds, hi]

theorem baSetU8_size (b : ByteArray) (i : USize) (v : UInt8) :
    (baSetU8 b i v).size = b.size := by
  unfold baSetU8
  split_ifs with h
  · change (b.data.set i.toNat v (lt_ba_size_of_lt_usize h)).size = b.data.size
    exact Array.size_set (lt_ba_size_of_lt_usize h)
  · rfl

theorem baGetU8_ofFn {n : ℕ} (f : Fin n → UInt8) {i : ℕ} (hn : n < 2 ^ 32) (hi : i < n) :
    baGetU8 (ByteArray.mk (Array.ofFn f)) (USize.ofNat i) = f ⟨i, hi⟩ := by
  have hsz : (ByteArray.mk (Array.ofFn f)).size = n := by simp [ByteArray.size]
  have hi' : (USize.ofNat i).toNat < (ByteArray.mk (Array.ofFn f)).size := by
    rw [usize_ofNat_toNat (by omega), hsz]; exact hi
  rw [baGetU8_eq_get! (by omega) hi', usize_ofNat_toNat (by omega)]
  simp [ByteArray.get!, getElem!_pos, hi]

private theorem testBit_255 {m : ℕ} (hm : m < 8) : Nat.testBit 255 m = true := by
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide

private theorem testBit_of_lt_pow {a n j : ℕ} (ha : a < 2 ^ n) (hj : n ≤ j) :
    Nat.testBit a j = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hlt : a < 2 ^ j := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hj)
  rw [Nat.div_eq_of_lt hlt]
  rfl

private theorem testBit_byte_u32 (x : UInt32) (k j : ℕ) (hk : k < 4) (hj : j < 32) :
    ((UInt8.ofNat ((x.toNat >>> (8 * k)) &&& 255)).toUInt32 <<< UInt32.ofNat (8 * k)).toBitVec.getLsbD j =
      (decide (8 * k ≤ j ∧ j < 8 * k + 8) && Nat.testBit x.toNat j) := by
  have hsh : ((UInt32.ofNat (8 * k)).toBitVec % 32).toNat = 8 * k := by
    simp [UInt32.toBitVec_ofNat]; omega
  rw [UInt32.toBitVec_shiftLeft]
  change ((UInt8.ofNat (x.toNat >>> (8 * k) &&& 255)).toUInt32.toBitVec <<<
      ((UInt32.ofNat (8 * k)).toBitVec % 32).toNat).getLsbD j = _
  rw [hsh, BitVec.getLsbD_shiftLeft]
  simp only [hj, decide_true, Bool.true_and]
  by_cases hge : 8 * k ≤ j
  · have hnlt : ¬ j < 8 * k := by omega
    simp only [hnlt, decide_false, Bool.not_false, Bool.true_and]
    rw [UInt8.toBitVec_toUInt32, BitVec.getLsbD_setWidth]
    have hb8 : (UInt8.ofNat (x.toNat >>> (8 * k) &&& 255)).toBitVec.getLsbD (j - 8 * k) =
        (decide (j - 8 * k < 8) && Nat.testBit (x.toNat >>> (8 * k) &&& 255) (j - 8 * k)) := by
      change (BitVec.ofNat 8 (x.toNat >>> (8 * k) &&& 255)).getLsbD (j - 8 * k) = _
      exact BitVec.getLsbD_ofNat 8 _ _
    rw [hb8]
    by_cases hlt : j - 8 * k < 8
    · have h255 := testBit_255 hlt
      have hj_lt : j < 8 * k + 8 := by omega
      have hsub : 8 * k + (j - 8 * k) = j := by omega
      simp [show j - 8 * k < 32 by omega, hlt, hge, hj_lt, Nat.testBit_and,
        Nat.testBit_shiftRight, h255, hsub]
    · simp [hlt, show ¬ (8 * k ≤ j ∧ j < 8 * k + 8) by omega]
  · simp [show j < 8 * k by omega, hge]

theorem u16_recombine {x : UInt32} (hx : x.toNat < 65536) :
    (UInt8.ofNat (x.toNat &&& 255)).toUInt32 |||
      ((UInt8.ofNat ((x.toNat >>> 8) &&& 255)).toUInt32 <<< 8) = x := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [UInt32.toBitVec_or, BitVec.getLsbD_or]
  have h0 : (UInt8.ofNat (x.toNat &&& 255)).toUInt32.toBitVec.getLsbD j =
      (decide (j < 8) && Nat.testBit x.toNat j) := by
    have := testBit_byte_u32 x 0 j (by omega) hj
    simpa using this
  have h1 : ((UInt8.ofNat ((x.toNat >>> 8) &&& 255)).toUInt32 <<< 8).toBitVec.getLsbD j =
      (decide (8 ≤ j ∧ j < 16) && Nat.testBit x.toNat j) := by
    have := testBit_byte_u32 x 1 j (by omega) hj
    simpa using this
  rw [h0, h1]
  have hxb : x.toBitVec.getLsbD j = Nat.testBit x.toNat j := rfl
  rw [hxb]
  by_cases hj16 : j < 16
  · by_cases hj8 : j < 8
    · simp [hj8, show ¬ (8 ≤ j ∧ j < 16) by omega]
    · simp [hj8, show 8 ≤ j ∧ j < 16 by omega]
  · have hfalse : Nat.testBit x.toNat j = false := testBit_of_lt_pow (n := 16) hx (by omega)
    simp [show ¬ j < 8 by omega, show ¬ (8 ≤ j ∧ j < 16) by omega, hfalse]

theorem baGetU16_packU16Arr {arr : Array UInt32} {i : ℕ}
    (hsz : arr.size * 2 < 2 ^ 32) (hi : i < arr.size) (hv : arr[i]!.toNat < 65536) :
    baGetU16 (packU16Arr arr) (USize.ofNat i) = arr[i]! := by
  have hbsize : (packU16Arr arr).size = arr.size * 2 := by
    simp [packU16Arr, ByteArray.size]
  have ho : (USize.ofNat i + USize.ofNat i).toNat = 2 * i := by
    rw [USize.toNat_add, usize_ofNat_toNat (by omega), Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega))]
    omega
  have ho1 : (USize.ofNat i + USize.ofNat i + 1).toNat = 2 * i + 1 := by
    rw [USize.toNat_add, ho, USize.toNat_one, Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega))]
  have hlt1 : USize.ofNat i + USize.ofNat i < (packU16Arr arr).usize := by
    change (USize.ofNat i + USize.ofNat i).toNat < (packU16Arr arr).usize.toNat
    rw [ho, ba_usize_toNat (by omega), hbsize]; omega
  have hlt2 : USize.ofNat i + USize.ofNat i + 1 < (packU16Arr arr).usize := by
    change (USize.ofNat i + USize.ofNat i + 1).toNat < (packU16Arr arr).usize.toNat
    rw [ho1, ba_usize_toNat (by omega), hbsize]; omega
  unfold baGetU16
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true hlt1), dite_eq_left_of_eq_true (eq_true hlt2),
    ba_uget_eq_get!, ba_uget_eq_get!, ho, ho1]
  have hlo : (packU16Arr arr).get! (2 * i) = UInt8.ofNat (arr[i]!.toNat &&& 255) := by
    simp [packU16Arr, ByteArray.get!, getElem!_pos, show 2 * i < arr.size * 2 by omega,
      show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
  have hhi : (packU16Arr arr).get! (2 * i + 1) = UInt8.ofNat ((arr[i]!.toNat >>> 8) &&& 255) := by
    simp [packU16Arr, ByteArray.get!, getElem!_pos, show 2 * i + 1 < arr.size * 2 by omega,
      show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
  rw [hlo, hhi]
  exact u16_recombine hv

private theorem testBit_byte_u64 (x : UInt64) (k j : ℕ) (hk : k < 8) (hj : j < 64) :
    ((UInt8.ofNat ((x.toNat >>> (8 * k)) &&& 255)).toUInt64 <<< UInt64.ofNat (8 * k)).toBitVec.getLsbD j =
      (decide (8 * k ≤ j ∧ j < 8 * k + 8) && Nat.testBit x.toNat j) := by
  have hsh : ((UInt64.ofNat (8 * k)).toBitVec % 64).toNat = 8 * k := by
    simp [UInt64.toBitVec_ofNat]; omega
  rw [UInt64.toBitVec_shiftLeft]
  change ((UInt8.ofNat (x.toNat >>> (8 * k) &&& 255)).toUInt64.toBitVec <<<
      ((UInt64.ofNat (8 * k)).toBitVec % 64).toNat).getLsbD j = _
  rw [hsh, BitVec.getLsbD_shiftLeft]
  simp only [hj, decide_true, Bool.true_and]
  by_cases hge : 8 * k ≤ j
  · have hnlt : ¬ j < 8 * k := by omega
    simp only [hnlt, decide_false, Bool.not_false, Bool.true_and]
    rw [UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
    have hb8 : (UInt8.ofNat (x.toNat >>> (8 * k) &&& 255)).toBitVec.getLsbD (j - 8 * k) =
        (decide (j - 8 * k < 8) && Nat.testBit (x.toNat >>> (8 * k) &&& 255) (j - 8 * k)) := by
      change (BitVec.ofNat 8 (x.toNat >>> (8 * k) &&& 255)).getLsbD (j - 8 * k) = _
      exact BitVec.getLsbD_ofNat 8 _ _
    rw [hb8]
    by_cases hlt : j - 8 * k < 8
    · have h255 := testBit_255 hlt
      have hj_lt : j < 8 * k + 8 := by omega
      have hsub : 8 * k + (j - 8 * k) = j := by omega
      simp [show j - 8 * k < 64 by omega, hlt, hge, hj_lt, Nat.testBit_and,
        Nat.testBit_shiftRight, h255, hsub]
    · simp [hlt, show ¬ (8 * k ≤ j ∧ j < 8 * k + 8) by omega]
  · simp [show j < 8 * k by omega, hge]

theorem u64_recombine (x : UInt64) :
    ((UInt8.ofNat ((x.toNat >>> 0) &&& 255)).toUInt64 |||
     ((UInt8.ofNat ((x.toNat >>> 8) &&& 255)).toUInt64 <<< 8) |||
     ((UInt8.ofNat ((x.toNat >>> 16) &&& 255)).toUInt64 <<< 16) |||
     ((UInt8.ofNat ((x.toNat >>> 24) &&& 255)).toUInt64 <<< 24) |||
     ((UInt8.ofNat ((x.toNat >>> 32) &&& 255)).toUInt64 <<< 32) |||
     ((UInt8.ofNat ((x.toNat >>> 40) &&& 255)).toUInt64 <<< 40) |||
     ((UInt8.ofNat ((x.toNat >>> 48) &&& 255)).toUInt64 <<< 48) |||
     ((UInt8.ofNat ((x.toNat >>> 56) &&& 255)).toUInt64 <<< 56)) = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  have h0 : (UInt8.ofNat ((x.toNat >>> 0) &&& 255)).toUInt64.toBitVec.getLsbD j =
      (decide (0 ≤ j ∧ j < 8) && Nat.testBit x.toNat j) := by
    have := testBit_byte_u64 x 0 j (by omega) hj; simpa using this
  have h1 : ((UInt8.ofNat ((x.toNat >>> 8) &&& 255)).toUInt64 <<< 8).toBitVec.getLsbD j =
      (decide (8 ≤ j ∧ j < 16) && Nat.testBit x.toNat j) := testBit_byte_u64 x 1 j (by omega) hj
  have h2 : ((UInt8.ofNat ((x.toNat >>> 16) &&& 255)).toUInt64 <<< 16).toBitVec.getLsbD j =
      (decide (16 ≤ j ∧ j < 24) && Nat.testBit x.toNat j) := testBit_byte_u64 x 2 j (by omega) hj
  have h3 : ((UInt8.ofNat ((x.toNat >>> 24) &&& 255)).toUInt64 <<< 24).toBitVec.getLsbD j =
      (decide (24 ≤ j ∧ j < 32) && Nat.testBit x.toNat j) := testBit_byte_u64 x 3 j (by omega) hj
  have h4 : ((UInt8.ofNat ((x.toNat >>> 32) &&& 255)).toUInt64 <<< 32).toBitVec.getLsbD j =
      (decide (32 ≤ j ∧ j < 40) && Nat.testBit x.toNat j) := testBit_byte_u64 x 4 j (by omega) hj
  have h5 : ((UInt8.ofNat ((x.toNat >>> 40) &&& 255)).toUInt64 <<< 40).toBitVec.getLsbD j =
      (decide (40 ≤ j ∧ j < 48) && Nat.testBit x.toNat j) := testBit_byte_u64 x 5 j (by omega) hj
  have h6 : ((UInt8.ofNat ((x.toNat >>> 48) &&& 255)).toUInt64 <<< 48).toBitVec.getLsbD j =
      (decide (48 ≤ j ∧ j < 56) && Nat.testBit x.toNat j) := testBit_byte_u64 x 6 j (by omega) hj
  have h7 : ((UInt8.ofNat ((x.toNat >>> 56) &&& 255)).toUInt64 <<< 56).toBitVec.getLsbD j =
      (decide (56 ≤ j ∧ j < 64) && Nat.testBit x.toNat j) := testBit_byte_u64 x 7 j (by omega) hj
  have hxb : x.toBitVec.getLsbD j = Nat.testBit x.toNat j := rfl
  rw [h0, h1, h2, h3, h4, h5, h6, h7, hxb]
  have hcover : (decide (0 ≤ j ∧ j < 8) || decide (8 ≤ j ∧ j < 16) || decide (16 ≤ j ∧ j < 24) ||
      decide (24 ≤ j ∧ j < 32) || decide (32 ≤ j ∧ j < 40) || decide (40 ≤ j ∧ j < 48) ||
      decide (48 ≤ j ∧ j < 56) || decide (56 ≤ j ∧ j < 64)) = true := by
    by_cases c0 : j < 8
    · simp [c0]
    · by_cases c1 : j < 16
      · simp [show 8 ≤ j by omega, c1]
      · by_cases c2 : j < 24
        · simp [show 16 ≤ j by omega, c2]
        · by_cases c3 : j < 32
          · simp [show 24 ≤ j by omega, c3]
          · by_cases c4 : j < 40
            · simp [show 32 ≤ j by omega, c4]
            · by_cases c5 : j < 48
              · simp [show 40 ≤ j by omega, c5]
              · by_cases c6 : j < 56
                · simp [show 48 ≤ j by omega, c6]
                · simp [show 56 ≤ j by omega, hj]
  cases hb : Nat.testBit x.toNat j
  · simp
  · simpa using hcover

theorem baGetI64_packI64Arr {arr : Array Int64} {i : ℕ}
    (hsz : arr.size * 8 < 2 ^ 32) (hi : i < arr.size) :
    baGetI64 (packI64Arr arr) (USize.ofNat i) = arr[i]! := by
  have hbsize : (packI64Arr arr).size = arr.size * 8 := by
    simp [packI64Arr, ByteArray.size]
  have h8 : (8 : USize).toNat = 8 := by
    change (USize.ofNat 8).toNat = 8
    exact usize_ofNat_toNat (by omega)
  have hbyte : ∀ k : ℕ, k < 8 →
      baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + USize.ofNat k) =
        UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> (8 * k)) &&& 255) := by
    intro k hk
    have hidx : (USize.ofNat i * 8 + USize.ofNat k).toNat = 8 * i + k := by
      have hm : (USize.ofNat i * 8).toNat = 8 * i := by
        rw [USize.toNat_mul, usize_ofNat_toNat (by omega), h8,
          Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega))]
        omega
      rw [USize.toNat_add, hm, usize_ofNat_toNat (by omega),
        Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega))]
    rw [baGetU8_eq_get! (by omega) (by rw [hidx, hbsize]; omega), hidx]
    have hlt : 8 * i + k < arr.size * 8 := by omega
    have hdiv : (8 * i + k) / 8 = i := by omega
    have hmod : (8 * i + k) % 8 = k := by omega
    simp [packI64Arr, ByteArray.get!, getElem!_pos, hlt, hdiv, hmod]
  have hadd0 : USize.ofNat i * 8 + USize.ofNat 0 = USize.ofNat i * 8 := by
    apply USize.toNat_inj.mp
    rw [USize.toNat_add, usize_ofNat_toNat (by omega), Nat.add_zero,
      Nat.mod_eq_of_lt (USize.toNat_lt_size _)]
  have h0 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 0) &&& 255) := by
    rw [← hadd0]; exact hbyte 0 (by omega)
  have h1 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 1) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 8) &&& 255) := hbyte 1 (by omega)
  have h2 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 2) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 16) &&& 255) := hbyte 2 (by omega)
  have h3 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 3) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 24) &&& 255) := hbyte 3 (by omega)
  have h4 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 4) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 32) &&& 255) := hbyte 4 (by omega)
  have h5 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 5) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 40) &&& 255) := hbyte 5 (by omega)
  have h6 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 6) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 48) &&& 255) := hbyte 6 (by omega)
  have h7 : baGetU8 (packI64Arr arr) (USize.ofNat i * 8 + 7) =
      UInt8.ofNat ((arr[i]!.toUInt64.toNat >>> 56) &&& 255) := hbyte 7 (by omega)
  unfold baGetI64
  dsimp only
  rw [h0, h1, h2, h3, h4, h5, h6, h7, u64_recombine]
  exact Int64.toInt64_toUInt64 (arr[i]!)

/-! ### `Int32` / `Int64` Arithmetic Without Overflow -/

theorem int_bmod_eq_self {x : ℤ} {m : ℕ} (hlo : -((m : ℤ) / 2) ≤ x) (hhi : x < ((m : ℤ) + 1) / 2)
    (hm : 0 < m) : x.bmod m = x := by
  unfold Int.bmod
  dsimp only
  by_cases hpos : 0 ≤ x
  · have hmod : x % (m : ℤ) = x := Int.emod_eq_of_lt hpos (by omega)
    rw [hmod, ite_eq_left (by omega)]
  · have hmod : x % (m : ℤ) = x + (m : ℤ) := by
      have h1 : (x + (m : ℤ)) % (m : ℤ) = x + (m : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
      rw [Int.add_emod_right] at h1
      exact h1
    rw [hmod, ite_eq_right (by omega)]
    omega

theorem int32_toInt_ofInt {x : ℤ} (hlo : -2 ^ 30 ≤ x) (hhi : x ≤ 2 ^ 30) :
    (Int32.ofInt x).toInt = x := by
  rw [Int32.toInt_ofInt]
  exact int_bmod_eq_self (by change -((2 ^ 32 : ℤ) / 2) ≤ x; omega)
    (by change x < ((2 ^ 32 : ℤ) + 1) / 2; omega) (by decide)

theorem int64_toInt_ofInt {x : ℤ} (hlo : -2 ^ 62 ≤ x) (hhi : x ≤ 2 ^ 62) :
    (Int64.ofInt x).toInt = x := by
  rw [Int64.toInt_ofInt]
  exact int_bmod_eq_self (by change -((2 ^ 64 : ℤ) / 2) ≤ x; omega)
    (by change x < ((2 ^ 64 : ℤ) + 1) / 2; omega) (by decide)

theorem int64_le_iff_toInt {x y : Int64} : (x ≤ y) ↔ x.toInt ≤ y.toInt :=
  Int64.le_iff_toInt_le

theorem int32_le_iff_toInt {x y : Int32} : (x ≤ y) ↔ x.toInt ≤ y.toInt :=
  Int32.le_iff_toInt_le

theorem int32_lt_iff_toInt {x y : Int32} : (x < y) ↔ x.toInt < y.toInt :=
  Int32.lt_iff_toInt_lt

theorem int32_toInt64_toInt (x : Int32) : x.toInt64.toInt = x.toInt :=
  Int32.toInt_toInt64 x

theorem int32_ofInt_add {x y : ℤ} (hx1 : -2 ^ 29 ≤ x) (hx2 : x ≤ 2 ^ 29)
    (hy1 : -2 ^ 29 ≤ y) (hy2 : y ≤ 2 ^ 29) :
    Int32.ofInt x + Int32.ofInt y = Int32.ofInt (x + y) := by
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_add, int32_toInt_ofInt (by omega) (by omega),
    int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]
  exact int_bmod_eq_self (by change -((2 ^ 32 : ℤ) / 2) ≤ x + y; omega)
    (by change x + y < ((2 ^ 32 : ℤ) + 1) / 2; omega) (by decide)

theorem int32_ofInt_sub {x y : ℤ} (hx1 : -2 ^ 29 ≤ x) (hx2 : x ≤ 2 ^ 29)
    (hy1 : -2 ^ 29 ≤ y) (hy2 : y ≤ 2 ^ 29) :
    Int32.ofInt x - Int32.ofInt y = Int32.ofInt (x - y) := by
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_sub, int32_toInt_ofInt (by omega) (by omega),
    int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]
  exact int_bmod_eq_self (by change -((2 ^ 32 : ℤ) / 2) ≤ x - y; omega)
    (by change x - y < ((2 ^ 32 : ℤ) + 1) / 2; omega) (by decide)

theorem int32_ofInt_mul {x y : ℤ} (hxy1 : -2 ^ 30 ≤ x * y) (hxy2 : x * y ≤ 2 ^ 30)
    (hx1 : -2 ^ 30 ≤ x) (hx2 : x ≤ 2 ^ 30) (hy1 : -2 ^ 30 ≤ y) (hy2 : y ≤ 2 ^ 30) :
    Int32.ofInt x * Int32.ofInt y = Int32.ofInt (x * y) := by
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_mul, int32_toInt_ofInt hx1 hx2, int32_toInt_ofInt hy1 hy2,
    int32_toInt_ofInt hxy1 hxy2]
  exact int_bmod_eq_self (by change -((2 ^ 32 : ℤ) / 2) ≤ x * y; omega)
    (by change x * y < ((2 ^ 32 : ℤ) + 1) / 2; omega) (by decide)

theorem int64_ofInt_add {x y : ℤ} (hx1 : -2 ^ 61 ≤ x) (hx2 : x ≤ 2 ^ 61)
    (hy1 : -2 ^ 61 ≤ y) (hy2 : y ≤ 2 ^ 61) :
    Int64.ofInt x + Int64.ofInt y = Int64.ofInt (x + y) := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_add, int64_toInt_ofInt (by omega) (by omega),
    int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
  exact int_bmod_eq_self (by change -((2 ^ 64 : ℤ) / 2) ≤ x + y; omega)
    (by change x + y < ((2 ^ 64 : ℤ) + 1) / 2; omega) (by decide)

theorem int64_ofInt_sub {x y : ℤ} (hx1 : -2 ^ 61 ≤ x) (hx2 : x ≤ 2 ^ 61)
    (hy1 : -2 ^ 61 ≤ y) (hy2 : y ≤ 2 ^ 61) :
    Int64.ofInt x - Int64.ofInt y = Int64.ofInt (x - y) := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_sub, int64_toInt_ofInt (by omega) (by omega),
    int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
  exact int_bmod_eq_self (by change -((2 ^ 64 : ℤ) / 2) ≤ x - y; omega)
    (by change x - y < ((2 ^ 64 : ℤ) + 1) / 2; omega) (by decide)

theorem int64_ofInt_mul {x y : ℤ} (hxy1 : -2 ^ 62 ≤ x * y) (hxy2 : x * y ≤ 2 ^ 62)
    (hx1 : -2 ^ 62 ≤ x) (hx2 : x ≤ 2 ^ 62) (hy1 : -2 ^ 62 ≤ y) (hy2 : y ≤ 2 ^ 62) :
    Int64.ofInt x * Int64.ofInt y = Int64.ofInt (x * y) := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_mul, int64_toInt_ofInt hx1 hx2, int64_toInt_ofInt hy1 hy2,
    int64_toInt_ofInt hxy1 hxy2]
  exact int_bmod_eq_self (by change -((2 ^ 64 : ℤ) / 2) ≤ x * y; omega)
    (by change x * y < ((2 ^ 64 : ℤ) + 1) / 2; omega) (by decide)

theorem u32_toInt32_ofNat {n : ℕ} (h : n < 2 ^ 30) :
    (UInt32.ofNat n).toInt32 = Int32.ofInt (n : ℤ) := by
  apply Int32.toBitVec_inj.mp
  rw [UInt32.toBitVec_toInt32, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  simp [UInt32.toNat_ofNat']

theorem u32_toInt64_ofNat {n : ℕ} (h : n < 2 ^ 30) :
    (UInt32.ofNat n).toUInt64.toInt64 = Int64.ofInt (n : ℤ) := by
  apply Int64.toBitVec_inj.mp
  rw [UInt64.toBitVec_toInt64, Int64.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  simp [UInt32.toNat_ofNat']; omega

/-! ### Properties of `PS.permCodes 7 7`, `packBase7`, and `buildCodeToIdx` -/

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → l₁.Subset l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    have ha : a ∈ l₂ := hsub List.mem_cons_self
    have hnd_t := (List.nodup_cons.mp hnd).2
    have hnot : a ∉ t := (List.nodup_cons.mp hnd).1
    have hsub' : t.Subset (l₂.erase a) := by
      intro x hx
      have hne : x ≠ a := fun h => hnot (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub (List.mem_cons_of_mem _ hx))
    have ih := nodup_length_le_of_subset t (l₂.erase a) hnd_t hsub'
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

private theorem list_sum_map_le {α : Type} (l : List α) (f g : α → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private theorem length_filter_add_not {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter fun x => !p x).length = l.length
  | [] => rfl
  | a :: t => by
    have ih := length_filter_add_not p t
    cases hp : p a <;> simp [List.filter, hp] <;> omega

theorem occF_code_iff (w : List ℕ) (a : ℕ) (hw : ∀ x ∈ w, x < 16) :
    PS.occF w.length (code w) a = true ↔ a ∈ w := by
  constructor
  · exact PS.occF_code w a hw
  · induction w using List.reverseRecOn with
    | nil => simp
    | append_singleton p b ih =>
      intro ha
      have hb : b < 16 := hw b (by simp)
      rw [List.length_append, List.length_singleton, PS.code_concat]
      simp only [PS.occF, S.mul_add_mod' hb, S.mul_add_div' hb, Bool.or_eq_true, beq_iff_eq]
      rcases List.mem_append.mp ha with h | h
      · exact Or.inr (ih (fun x hx => hw x (by simp [hx])) h)
      · exact Or.inl (List.mem_singleton.mp h).symm

theorem mem_permCodes_spec (k : ℕ) (hk15 : k ≤ 15) :
    ∀ n c, c ∈ permCodes k n →
      ∃ w : List ℕ, w.Nodup ∧ w.length = n ∧ (∀ a ∈ w, 1 ≤ a ∧ a ≤ k) ∧ code w = c
  | 0, c, hc => by
    simp only [permCodes, List.mem_singleton] at hc
    exact ⟨[], List.nodup_nil, rfl, by simp, by rw [hc]; exact S.code_nil⟩
  | n + 1, c, hc => by
    simp only [permCodes, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hc
    obtain ⟨c0, hc0, a, ⟨ha, hocc⟩, rfl⟩ := hc
    obtain ⟨p, hnd, hlen, hr, rfl⟩ := mem_permCodes_spec k hk15 n c0 hc0
    have hnot : a + 1 ∉ p := by
      intro hm
      have h1 := (occF_code_iff p (a + 1) (fun x hx => by have := hr x hx; omega)).mpr hm
      rw [hlen] at h1
      simp [h1] at hocc
    refine ⟨p ++ [a + 1], ?_, by simp [hlen], ?_, PS.code_concat p (a + 1)⟩
    · exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun x hx y hy => by
        rw [List.mem_singleton.mp hy]; intro h; subst h; exact hnot hx⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hr x h
      · rw [List.mem_singleton.mp h]; omega

theorem permW_of_mem_permCodes7 {c : ℕ} (hc : c ∈ permCodes 7 7) :
    ∃ u : List ℕ, PermW 7 u ∧ code u = c := by
  obtain ⟨u, hnd, hlen, hr, rfl⟩ := mem_permCodes_spec 7 (by omega) 7 c hc
  refine ⟨u, ⟨hnd, hlen, fun a => ⟨hr a, ?_⟩⟩, rfl⟩
  intro ⟨h1, h7⟩
  by_contra hnot
  have hsub : u.Subset ((List.range' 1 7).erase a) := by
    intro x hx
    have hxr := hr x hx
    have hne : x ≠ a := fun h => hnot (h ▸ hx)
    exact (List.mem_erase_of_ne hne).mpr (by rw [List.mem_range'_1]; omega)
  have hcard := nodup_length_le_of_subset u ((List.range' 1 7).erase a) hnd hsub
  have ha_mem : a ∈ List.range' 1 7 := by rw [List.mem_range'_1]; omega
  rw [List.length_erase_of_mem ha_mem, List.length_range', hlen] at hcard
  omega

theorem permCodes_nodup (k : ℕ) (hk15 : k ≤ 15) : ∀ n, (permCodes k n).Nodup
  | 0 => List.nodup_singleton 0
  | n + 1 => by
    unfold permCodes
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro c _
      refine List.Nodup.map ?_ (List.Nodup.filter _ List.nodup_range)
      intro a b hab
      dsimp only at hab
      omega
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      intro x hx1 hx2
      simp only [List.mem_map, List.mem_filter, List.mem_range] at hx1 hx2
      obtain ⟨a1, ⟨ha1, _⟩, rfl⟩ := hx1
      obtain ⟨a2, ⟨ha2, _⟩, heq⟩ := hx2
      have hc : (permCodes k n)[i] = (permCodes k n)[j] := by omega
      have hnd := permCodes_nodup k hk15 n
      have := (hnd.getElem_inj_iff (i := i) (j := j) (hi := hi) (hj := hj)).mp hc
      omega

theorem permCodes_length_le_descFact (k : ℕ) (hk15 : k ≤ 15) :
    ∀ n, n ≤ k → (permCodes k n).length ≤ (List.range n).foldl (fun acc i => acc * (k - i)) 1
  | 0, _ => by simp [permCodes]
  | n + 1, hn => by
    have ih := permCodes_length_le_descFact k hk15 n (by omega)
    have hfold : (List.range (n + 1)).foldl (fun acc i => acc * (k - i)) 1 =
        (List.range n).foldl (fun acc i => acc * (k - i)) 1 * (k - n) := by
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hfold]
    unfold permCodes
    rw [List.length_flatMap]
    have hle : ∀ c ∈ permCodes k n,
        (((List.range k).filter fun a => !PS.occF n c (a + 1)).map fun a => c * 16 + (a + 1)).length ≤ k - n := by
      intro c hc
      rw [List.length_map]
      obtain ⟨w, hnd, hlen, hr, rfl⟩ := mem_permCodes_spec k hk15 n c hc
      have htot := length_filter_add_not (fun a => !PS.occF n (code w) (a + 1)) (List.range k)
      rw [List.length_range] at htot
      have hge : n ≤ ((List.range k).filter fun a => !!PS.occF n (code w) (a + 1)).length := by
        have hsub : (w.map (· - 1)).Subset ((List.range k).filter fun a => !!PS.occF n (code w) (a + 1)) := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          have hyr := hr y hy
          refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
          have hocc := (occF_code_iff w y (fun z hz => by have := hr z hz; omega)).mpr hy
          rw [hlen] at hocc
          rw [show y - 1 + 1 = y by omega, hocc]
          rfl
        have hnd' : (w.map (· - 1)).Nodup := by
          refine hnd.map_on ?_
          intro a ha b hb hab
          have := hr a ha; have := hr b hb; omega
        have hc := nodup_length_le_of_subset _ _ hnd' hsub
        rwa [List.length_map, hlen] at hc
      omega
    calc ((permCodes k n).map fun c =>
            (((List.range k).filter fun a => !PS.occF n c (a + 1)).map fun a => c * 16 + (a + 1)).length).sum
        ≤ ((permCodes k n).map fun _ => k - n).sum := list_sum_map_le _ _ _ hle
      _ = (permCodes k n).length * (k - n) := by simp
      _ ≤ _ := Nat.mul_le_mul_right (k - n) ih

theorem permCodes7_length_le : (permCodes 7 7).length ≤ 5040 := by
  have h := permCodes_length_le_descFact 7 (by omega) 7 (by omega)
  exact h.trans (by decide)

theorem permCodes7_length_lt_8192 : (permCodes 7 7).length < 8192 := by
  have := permCodes7_length_le; omega

/-! ### `hexDigit`, `packHex7`, `packBase7`, and `buildCodeToIdx` -/

theorem code_list7 (d0 d1 d2 d3 d4 d5 d6 : ℕ) :
    code [d0, d1, d2, d3, d4, d5, d6] = packHex7 d0 d1 d2 d3 d4 d5 d6 := by
  simp [S.code, packHex7]

private theorem and_15_eq_mod_16 (x : ℕ) : x &&& 15 = x % 16 :=
  Nat.and_two_pow_sub_one_eq_mod x 4

theorem hexDigit_packHex7 {d0 d1 d2 d3 d4 d5 d6 : ℕ}
    (h0 : d0 < 16) (h1 : d1 < 16) (h2 : d2 < 16) (h3 : d3 < 16)
    (h4 : d4 < 16) (h5 : d5 < 16) (h6 : d6 < 16) :
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 0 = d0 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 1 = d1 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 2 = d2 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 3 = d3 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 4 = d4 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 5 = d5 ∧
    hexDigit (packHex7 d0 d1 d2 d3 d4 d5 d6) 6 = d6 := by
  simp only [hexDigit, packHex7, and_15_eq_mod_16, Nat.shiftRight_eq_div_pow]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem list7_exists {u : List ℕ} (h : u.length = 7) :
    ∃ d0 d1 d2 d3 d4 d5 d6, u = [d0, d1, d2, d3, d4, d5, d6] := by
  match u, h with
  | [d0, d1, d2, d3, d4, d5, d6], _ => exact ⟨d0, d1, d2, d3, d4, d5, d6, rfl⟩

theorem packBase7_lt_of_permW {u : List ℕ} (hu : PermW 7 u) :
    packBase7 (code u) < 823543 := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, rfl⟩ := list7_exists hu.2.1
  have hlt : ∀ a ∈ [d0, d1, d2, d3, d4, d5, d6], 1 ≤ a ∧ a ≤ 7 := fun a ha => (hu.2.2 a).mp ha
  have h0 := hlt d0 (by simp); have h1 := hlt d1 (by simp); have h2 := hlt d2 (by simp)
  have h3 := hlt d3 (by simp); have h4 := hlt d4 (by simp); have h5 := hlt d5 (by simp)
  have h6 := hlt d6 (by simp)
  rw [code_list7]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ :=
    hexDigit_packHex7 (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold packBase7
  rw [e0, e1, e2, e3, e4, e5, e6]
  omega

theorem packBase7_inj_of_permW {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v)
    (heq : packBase7 (code u) = packBase7 (code v)) : u = v := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, rfl⟩ := list7_exists hu.2.1
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, rfl⟩ := list7_exists hv.2.1
  have ha : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6], 1 ≤ a ∧ a ≤ 7 := fun a h => (hu.2.2 a).mp h
  have hb : ∀ b ∈ [b0, b1, b2, b3, b4, b5, b6], 1 ≤ b ∧ b ≤ 7 := fun b h => (hv.2.2 b).mp h
  have ha0 := ha a0 (by simp); have ha1 := ha a1 (by simp); have ha2 := ha a2 (by simp)
  have ha3 := ha a3 (by simp); have ha4 := ha a4 (by simp); have ha5 := ha a5 (by simp)
  have ha6 := ha a6 (by simp)
  have hb0 := hb b0 (by simp); have hb1 := hb b1 (by simp); have hb2 := hb b2 (by simp)
  have hb3 := hb b3 (by simp); have hb4 := hb b4 (by simp); have hb5 := hb b5 (by simp)
  have hb6 := hb b6 (by simp)
  rw [code_list7, code_list7] at heq
  obtain ⟨ea0, ea1, ea2, ea3, ea4, ea5, ea6⟩ :=
    hexDigit_packHex7 (d0 := a0) (d1 := a1) (d2 := a2) (d3 := a3) (d4 := a4) (d5 := a5) (d6 := a6)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨eb0, eb1, eb2, eb3, eb4, eb5, eb6⟩ :=
    hexDigit_packHex7 (d0 := b0) (d1 := b1) (d2 := b2) (d3 := b3) (d4 := b4) (d5 := b5) (d6 := b6)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold packBase7 at heq
  rw [ea0, ea1, ea2, ea3, ea4, ea5, ea6, eb0, eb1, eb2, eb3, eb4, eb5, eb6] at heq
  have : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 := by omega
  rcases this with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

theorem packBase7_inj_on_permCodes7 {c1 c2 : ℕ} (h1 : c1 ∈ permCodes 7 7) (h2 : c2 ∈ permCodes 7 7)
    (heq : packBase7 c1 = packBase7 c2) : c1 = c2 := by
  obtain ⟨u, hu, rfl⟩ := permW_of_mem_permCodes7 h1
  obtain ⟨v, hv, rfl⟩ := permW_of_mem_permCodes7 h2
  rw [packBase7_inj_of_permW hu hv heq]

private theorem map_fst_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | a :: t, k => by simp [List.zipIdx_cons, map_fst_zipIdx t (k + 1)]

private theorem foldl_set_get_other (l : List (ℕ × ℕ)) (mp : Array UInt32) (k : ℕ)
    (hk : k < mp.size) (hnot : ∀ p ∈ l, packBase7 p.1 ≠ k) :
    (l.foldl (fun a (c, i) => a.set! (packBase7 c) (UInt32.ofNat i)) mp)[k]! = mp[k]! := by
  induction l generalizing mp with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by rw [Array.size_set!]; exact hk) (fun q hq => hnot q (List.mem_cons_of_mem _ hq))]
    have hne : packBase7 p.1 ≠ k := hnot p List.mem_cons_self
    show (mp.setIfInBounds (packBase7 p.1) (UInt32.ofNat p.2))[k]! = mp[k]!
    by_cases hp : packBase7 p.1 < mp.size
    · simp only [Array.setIfInBounds, hp, dite_true]
      have hk' : k < (mp.set (packBase7 p.1) (UInt32.ofNat p.2) hp).size := by
        rw [Array.size_set]; exact hk
      rw [getElem!_pos (mp.set (packBase7 p.1) (UInt32.ofNat p.2) hp) k hk',
        Array.getElem_set_ne (h := hne), getElem!_pos mp k hk]
    · simp [Array.setIfInBounds, hp]

private theorem foldl_set_get_mem (l : List (ℕ × ℕ)) (mp : Array UInt32)
    (hsz : mp.size = 823543)
    (hnd : (l.map fun p => packBase7 p.1).Nodup)
    (hlt : ∀ p ∈ l, packBase7 p.1 < 823543) :
    ∀ p ∈ l, (l.foldl (fun a (c, i) => a.set! (packBase7 c) (UInt32.ofNat i)) mp)[packBase7 p.1]!
      = UInt32.ofNat p.2 := by
  induction l generalizing mp with
  | nil => simp
  | cons hd tl ih =>
    intro p hp
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | htl
    · rw [foldl_set_get_other tl _ (packBase7 p.1) (by rw [Array.size_set!, hsz]; exact hlt p List.mem_cons_self)]
      · have h1 : packBase7 p.1 < mp.size := by rw [hsz]; exact hlt p List.mem_cons_self
        show (mp.setIfInBounds (packBase7 p.1) (UInt32.ofNat p.2))[packBase7 p.1]! = UInt32.ofNat p.2
        simp only [Array.setIfInBounds, h1, dite_true]
        have h1' : packBase7 p.1 < (mp.set (packBase7 p.1) (UInt32.ofNat p.2) h1).size := by
          rw [Array.size_set]; exact h1
        rw [getElem!_pos (mp.set (packBase7 p.1) (UInt32.ofNat p.2) h1) (packBase7 p.1) h1',
          Array.getElem_set_self]
      · intro q hq heq
        exact hnd.1 (List.mem_map.mpr ⟨q, hq, heq⟩)
    · exact ih _ (by rw [Array.size_set!, hsz]) hnd.2 (fun q hq => hlt q (List.mem_cons_of_mem _ hq)) p htl

theorem buildCodeToIdx_get {u : List ℕ} (hu : PermW 7 u) :
    (buildCodeToIdx (permCodes 7 7))[packBase7 (code u)]! = UInt32.ofNat (encB 7 u) := by
  have hmem : code u ∈ permCodes 7 7 := mem_perm (by omega) hu
  have hi : (permCodes 7 7).idxOf (code u) < (permCodes 7 7).length := List.idxOf_lt_length_of_mem hmem
  have hzip_mem : (code u, (permCodes 7 7).idxOf (code u)) ∈ (permCodes 7 7).zipIdx := by
    rw [List.mem_iff_getElem]
    refine ⟨(permCodes 7 7).idxOf (code u), by simp [hi], ?_⟩
    simp [List.getElem_zipIdx, List.getElem_idxOf hi]
  have hnd_jl : (permCodes 7 7).Nodup := permCodes_nodup 7 (by omega) 7
  have hnd_map : ((permCodes 7 7).zipIdx.map fun p => packBase7 p.1).Nodup := by
    have hmap : ((permCodes 7 7).zipIdx.map fun p => packBase7 p.1) = (permCodes 7 7).map packBase7 := by
      change ((permCodes 7 7).zipIdx.map (packBase7 ∘ Prod.fst)) = (permCodes 7 7).map packBase7
      rw [← List.map_map, map_fst_zipIdx]
    rw [hmap]
    exact hnd_jl.map_on (fun a ha b hb hab => packBase7_inj_on_permCodes7 ha hb hab)
  have hlt : ∀ p ∈ (permCodes 7 7).zipIdx, packBase7 p.1 < 823543 := by
    intro p hp
    have hp1 : p.1 ∈ permCodes 7 7 := by
      have hm : p.1 ∈ (permCodes 7 7).zipIdx.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rwa [map_fst_zipIdx] at hm
    obtain ⟨v, hv, hcv⟩ := permW_of_mem_permCodes7 hp1
    rw [← hcv]
    exact packBase7_lt_of_permW hv
  exact foldl_set_get_mem (permCodes 7 7).zipIdx (Array.replicate 823543 (0 : UInt32))
    (Array.size_replicate) hnd_map hlt (code u, (permCodes 7 7).idxOf (code u)) hzip_mem

/-! ### Canonical `S_7`-Equivariant `w3Step` and `w4Step` -/

def w3Step (u : List ℕ) (t : ℕ) : List ℕ :=
  let e := u.rotate 6
  let (i0, i1, i2) := perms3NonId.getD t (0, 2, 1)
  [e[3]!, e[4]!, e[5]!, e[6]!, e[i0]!, e[i1]!, e[i2]!]

def w4Step (u : List ℕ) (t : ℕ) : List ℕ :=
  let e := u.rotate 6
  let (i0, i1, i2, i3) := perms4NonId.getD t (0, 1, 3, 2)
  [e[4]!, e[5]!, e[6]!, e[i0]!, e[i1]!, e[i2]!, e[i3]!]

theorem excF_code7 {u : List ℕ} (hu : PermW 7 u) :
    excF (16 ^ 6 - 1) (code u) = code (u.rotate 6) := by
  change S.excF (16 ^ (7 - 1) - 1) (code u) = code (u.rotate (7 - 1))
  rw [S.excF_eq]
  exact S.exc_code 7 u hu.2.1 (hu.lt16 (by omega)) (by omega)

private theorem perms3_lt (t : ℕ) :
    (perms3NonId.getD t (0, 2, 1)).1 < 3 ∧
    (perms3NonId.getD t (0, 2, 1)).2.1 < 3 ∧
    (perms3NonId.getD t (0, 2, 1)).2.2 < 3 := by
  by_cases ht : t < 5
  · revert ht; revert t; decide
  · have : perms3NonId.getD t (0, 2, 1) = (0, 2, 1) := by
      simp [Array.getD, perms3NonId, Nat.not_lt.mp ht]
    rw [this]; decide

private theorem perms4_lt (t : ℕ) :
    (perms4NonId.getD t (0, 1, 3, 2)).1 < 4 ∧
    (perms4NonId.getD t (0, 1, 3, 2)).2.1 < 4 ∧
    (perms4NonId.getD t (0, 1, 3, 2)).2.2.1 < 4 ∧
    (perms4NonId.getD t (0, 1, 3, 2)).2.2.2 < 4 := by
  by_cases ht : t < 23
  · revert ht; revert t; decide
  · have : perms4NonId.getD t (0, 1, 3, 2) = (0, 1, 3, 2) := by
      simp [Array.getD, perms4NonId, Nat.not_lt.mp ht]
    rw [this]; decide

theorem s3Code_code {u : List ℕ} (hu : PermW 7 u) (t : ℕ) :
    s3Code (code u) t = code (w3Step u t) := by
  unfold s3Code w3Step
  rw [excF_code7 hu]
  have hrot : PermW 7 (u.rotate 6) := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  have hlt : ∀ a ∈ [e0, e1, e2, e3, e4, e5, e6], a < 16 := fun a ha => by
    rw [he] at hrot; exact hrot.lt16 (by omega) a ha
  rw [he, code_list7]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6⟩ :=
    hexDigit_packHex7 (hlt e0 (by simp)) (hlt e1 (by simp)) (hlt e2 (by simp))
      (hlt e3 (by simp)) (hlt e4 (by simp)) (hlt e5 (by simp)) (hlt e6 (by simp))
  obtain ⟨hi0, hi1, hi2⟩ := perms3_lt t
  generalize perms3NonId.getD t (0, 2, 1) = p at hi0 hi1 hi2 ⊢
  rcases p with ⟨i0, i1, i2⟩
  dsimp only at hi0 hi1 hi2 ⊢
  rw [d0, d1, d2, d3, d4, d5, d6]
  have hget : ∀ k, k < 3 → (#[e0, e1, e2]).getD k 0 = [e0, e1, e2, e3, e4, e5, e6][k]! := by
    intro k hk; match k with | 0 | 1 | 2 => rfl
  rw [hget i0 hi0, hget i1 hi1, hget i2 hi2, code_list7]
  rfl

theorem s4Code_code {u : List ℕ} (hu : PermW 7 u) (t : ℕ) :
    s4Code (code u) t = code (w4Step u t) := by
  unfold s4Code w4Step
  rw [excF_code7 hu]
  have hrot : PermW 7 (u.rotate 6) := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  have hlt : ∀ a ∈ [e0, e1, e2, e3, e4, e5, e6], a < 16 := fun a ha => by
    rw [he] at hrot; exact hrot.lt16 (by omega) a ha
  rw [he, code_list7]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6⟩ :=
    hexDigit_packHex7 (hlt e0 (by simp)) (hlt e1 (by simp)) (hlt e2 (by simp))
      (hlt e3 (by simp)) (hlt e4 (by simp)) (hlt e5 (by simp)) (hlt e6 (by simp))
  obtain ⟨hi0, hi1, hi2, hi3⟩ := perms4_lt t
  generalize perms4NonId.getD t (0, 1, 3, 2) = p at hi0 hi1 hi2 hi3 ⊢
  rcases p with ⟨i0, i1, i2, i3⟩
  dsimp only at hi0 hi1 hi2 hi3 ⊢
  rw [d0, d1, d2, d3, d4, d5, d6]
  have hget : ∀ k, k < 4 → (#[e0, e1, e2, e3]).getD k 0 = [e0, e1, e2, e3, e4, e5, e6][k]! := by
    intro k hk; match k with | 0 | 1 | 2 | 3 => rfl
  rw [hget i0 hi0, hget i1 hi1, hget i2 hi2, hget i3 hi3, code_list7]
  rfl

theorem w3Step_map (f : ℕ → ℕ) {u : List ℕ} (hu : u.length = 7) (t : ℕ) :
    w3Step (u.map f) t = (w3Step u t).map f := by
  unfold w3Step
  rw [← List.map_rotate]
  have hlen : (u.rotate 6).length = 7 := by rw [List.length_rotate, hu]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hlen
  rw [he]
  obtain ⟨hi0, hi1, hi2⟩ := perms3_lt t
  generalize perms3NonId.getD t (0, 2, 1) = p at hi0 hi1 hi2 ⊢
  rcases p with ⟨i0, i1, i2⟩
  dsimp only at hi0 hi1 hi2 ⊢
  have hget : ∀ k, k < 3 →
      ([e0, e1, e2, e3, e4, e5, e6].map f)[k]! = f ([e0, e1, e2, e3, e4, e5, e6][k]!) := by
    intro k hk; match k with | 0 | 1 | 2 => rfl
  simp only [List.map_cons, List.map_nil] at hget ⊢
  rw [hget i0 hi0, hget i1 hi1, hget i2 hi2]
  rfl

theorem w4Step_map (f : ℕ → ℕ) {u : List ℕ} (hu : u.length = 7) (t : ℕ) :
    w4Step (u.map f) t = (w4Step u t).map f := by
  unfold w4Step
  rw [← List.map_rotate]
  have hlen : (u.rotate 6).length = 7 := by rw [List.length_rotate, hu]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hlen
  rw [he]
  obtain ⟨hi0, hi1, hi2, hi3⟩ := perms4_lt t
  generalize perms4NonId.getD t (0, 1, 3, 2) = p at hi0 hi1 hi2 hi3 ⊢
  rcases p with ⟨i0, i1, i2, i3⟩
  dsimp only at hi0 hi1 hi2 hi3 ⊢
  have hget : ∀ k, k < 4 →
      ([e0, e1, e2, e3, e4, e5, e6].map f)[k]! = f ([e0, e1, e2, e3, e4, e5, e6][k]!) := by
    intro k hk; match k with | 0 | 1 | 2 | 3 => rfl
  simp only [List.map_cons, List.map_nil] at hget ⊢
  rw [hget i0 hi0, hget i1 hi1, hget i2 hi2, hget i3 hi3]
  rfl

theorem permW_w3Step {u : List ℕ} (hu : PermW 7 u) (t : ℕ) : PermW 7 (w3Step u t) := by
  have hrot := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  unfold w3Step
  rw [he] at hrot ⊢
  have h1 : ∀ i0 i1 i2, [i0, i1, i2].Perm [0, 1, 2] →
      PermW 7 [e3, e4, e5, e6, [e0, e1, e2, e3, e4, e5, e6][i0]!,
        [e0, e1, e2, e3, e4, e5, e6][i1]!, [e0, e1, e2, e3, e4, e5, e6][i2]!] := by
    intro i0 i1 i2 hp
    have hmap : ([i0, i1, i2].map fun j => [e0, e1, e2, e3, e4, e5, e6][j]!).Perm
        ([0, 1, 2].map fun j => [e0, e1, e2, e3, e4, e5, e6][j]!) := hp.map _
    have hbase : [e0, e1, e2, e3, e4, e5, e6].Perm [e3, e4, e5, e6, e0, e1, e2] :=
      List.perm_append_comm (l₁ := [e0, e1, e2]) (l₂ := [e3, e4, e5, e6])
    exact K16.permW_of_perm hrot (hbase.trans (List.Perm.append_left [e3, e4, e5, e6] hmap.symm))
  have hperm3 : [(perms3NonId.getD t (0, 2, 1)).1, (perms3NonId.getD t (0, 2, 1)).2.1,
      (perms3NonId.getD t (0, 2, 1)).2.2].Perm [0, 1, 2] := by
    by_cases ht : t < 5
    · revert ht; revert t; decide
    · have : perms3NonId.getD t (0, 2, 1) = (0, 2, 1) := by
        simp [Array.getD, perms3NonId, Nat.not_lt.mp ht]
      rw [this]; decide
  exact h1 _ _ _ hperm3

theorem permW_w4Step {u : List ℕ} (hu : PermW 7 u) (t : ℕ) : PermW 7 (w4Step u t) := by
  have hrot := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  unfold w4Step
  rw [he] at hrot ⊢
  have h1 : ∀ i0 i1 i2 i3, [i0, i1, i2, i3].Perm [0, 1, 2, 3] →
      PermW 7 [e4, e5, e6, [e0, e1, e2, e3, e4, e5, e6][i0]!,
        [e0, e1, e2, e3, e4, e5, e6][i1]!, [e0, e1, e2, e3, e4, e5, e6][i2]!,
        [e0, e1, e2, e3, e4, e5, e6][i3]!] := by
    intro i0 i1 i2 i3 hp
    have hmap : ([i0, i1, i2, i3].map fun j => [e0, e1, e2, e3, e4, e5, e6][j]!).Perm
        ([0, 1, 2, 3].map fun j => [e0, e1, e2, e3, e4, e5, e6][j]!) := hp.map _
    have hbase : [e0, e1, e2, e3, e4, e5, e6].Perm [e4, e5, e6, e0, e1, e2, e3] :=
      List.perm_append_comm (l₁ := [e0, e1, e2, e3]) (l₂ := [e4, e5, e6])
    exact K16.permW_of_perm hrot (hbase.trans (List.Perm.append_left [e4, e5, e6] hmap.symm))
  have hperm4 : [(perms4NonId.getD t (0, 1, 3, 2)).1, (perms4NonId.getD t (0, 1, 3, 2)).2.1,
      (perms4NonId.getD t (0, 1, 3, 2)).2.2.1, (perms4NonId.getD t (0, 1, 3, 2)).2.2.2].Perm [0, 1, 2, 3] := by
    by_cases ht : t < 23
    · revert ht; revert t; decide
    · have : perms4NonId.getD t (0, 1, 3, 2) = (0, 1, 3, 2) := by
        simp [Array.getD, perms4NonId, Nat.not_lt.mp ht]
      rw [this]; decide
  exact h1 _ _ _ _ hperm4

theorem w3Step_complete {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v)
    (hl : WLink 7 3 u v) (hrot_ne : ¬ u ~r v) :
    ∃ t < 5, v = w3Step u t := by
  have hrot := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, rfl⟩ := list7_exists hv.2.1
  unfold WLink at hl
  rw [he] at hl hrot
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero] at hl
  injection hl with hv0 hl1
  injection hl1 with hv1 hl2
  injection hl2 with hv2 hl3
  injection hl3 with hv3 _
  subst hv0; subst hv1; subst hv2; subst hv3
  have hperm : [e0, e1, e2, e3, e4, e5, e6].Perm [e3, e4, e5, e6, v4, v5, v6] :=
    (List.perm_ext_iff_of_nodup hrot.1 hv.1).mpr (fun a => (hrot.2.2 a).trans (hv.2.2 a).symm)
  have hbase : [e0, e1, e2, e3, e4, e5, e6].Perm [e3, e4, e5, e6, e0, e1, e2] :=
    List.perm_append_comm (l₁ := [e0, e1, e2]) (l₂ := [e3, e4, e5, e6])
  have hp3 : [e0, e1, e2].Perm [v4, v5, v6] :=
    (List.perm_append_left_iff [e3, e4, e5, e6]).mp (hbase.symm.trans hperm)
  have hne_id : [v4, v5, v6] ≠ [e0, e1, e2] := by
    intro h
    apply hrot_ne
    have h2 : (u.rotate 6).rotate 3 = [e3, e4, e5, e6, v4, v5, v6] := by
      rw [he]; injection h with h4 h5; injection h5 with h5 h6; injection h6 with h6 _
      subst h4; subst h5; subst h6; rfl
    exact ⟨6 + 3, by rw [← List.rotate_rotate, h2]⟩
  have hndv : [v4, v5, v6].Nodup := by
    have h := hv.1
    change ([e3, e4, e5, e6] ++ [v4, v5, v6]).Nodup at h
    exact (List.nodup_append.mp h).2.1
  have hmem : ∀ x ∈ [v4, v5, v6], x ∈ [e0, e1, e2] := fun x hx => hp3.symm.subset hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hndv
  have hv4 := hmem v4 (Or.inl rfl)
  have hv5 := hmem v5 (Or.inr (Or.inl rfl))
  have hv6 := hmem v6 (Or.inr (Or.inr rfl))
  have hcases : [v4, v5, v6] = [e0, e2, e1] ∨ [v4, v5, v6] = [e1, e0, e2] ∨
      [v4, v5, v6] = [e1, e2, e0] ∨ [v4, v5, v6] = [e2, e0, e1] ∨ [v4, v5, v6] = [e2, e1, e0] := by
    rcases hv4 with rfl | rfl | rfl <;> rcases hv5 with rfl | rfl | rfl <;> rcases hv6 with rfl | rfl | rfl <;> simp_all
  rcases hcases with h | h | h | h | h
  · refine ⟨0, by omega, ?_⟩
    unfold w3Step; rw [he]; simp [perms3NonId]
    injection h with h1 h2; injection h2 with h2 h3; injection h3 with h3 _; simp [h1, h2, h3]
  · refine ⟨1, by omega, ?_⟩
    unfold w3Step; rw [he]; simp [perms3NonId]
    injection h with h1 h2; injection h2 with h2 h3; injection h3 with h3 _; simp [h1, h2, h3]
  · refine ⟨2, by omega, ?_⟩
    unfold w3Step; rw [he]; simp [perms3NonId]
    injection h with h1 h2; injection h2 with h2 h3; injection h3 with h3 _; simp [h1, h2, h3]
  · refine ⟨3, by omega, ?_⟩
    unfold w3Step; rw [he]; simp [perms3NonId]
    injection h with h1 h2; injection h2 with h2 h3; injection h3 with h3 _; simp [h1, h2, h3]
  · refine ⟨4, by omega, ?_⟩
    unfold w3Step; rw [he]; simp [perms3NonId]
    injection h with h1 h2; injection h2 with h2 h3; injection h3 with h3 _; simp [h1, h2, h3]

private theorem find_perms4 :
    ∀ a b c d : Fin 4,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (a.val, b.val, c.val, d.val) ≠ (0, 1, 2, 3) →
      ∃ t : Fin 23, perms4NonId.getD t.val (0, 1, 3, 2) = (a.val, b.val, c.val, d.val) := by
  decide

theorem w4Step_complete {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v)
    (hl : WLink 7 4 u v) (hrot_ne : ¬ u ~r v) :
    ∃ t < 23, v = w4Step u t := by
  have hrot := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, rfl⟩ := list7_exists hv.2.1
  unfold WLink at hl
  rw [he] at hl hrot
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero] at hl
  injection hl with hv0 hl1
  injection hl1 with hv1 hl2
  injection hl2 with hv2 _
  subst hv0; subst hv1; subst hv2
  have hperm : [e0, e1, e2, e3, e4, e5, e6].Perm [e4, e5, e6, v3, v4, v5, v6] :=
    (List.perm_ext_iff_of_nodup hrot.1 hv.1).mpr (fun a => (hrot.2.2 a).trans (hv.2.2 a).symm)
  have hbase : [e0, e1, e2, e3, e4, e5, e6].Perm [e4, e5, e6, e0, e1, e2, e3] :=
    List.perm_append_comm (l₁ := [e0, e1, e2, e3]) (l₂ := [e4, e5, e6])
  have hp4 : [e0, e1, e2, e3].Perm [v3, v4, v5, v6] :=
    (List.perm_append_left_iff [e4, e5, e6]).mp (hbase.symm.trans hperm)
  have hne_id : [v3, v4, v5, v6] ≠ [e0, e1, e2, e3] := by
    intro h
    apply hrot_ne
    have h2 : (u.rotate 6).rotate 4 = [e4, e5, e6, v3, v4, v5, v6] := by
      rw [he]; injection h with h3 h4; injection h4 with h4 h5; injection h5 with h5 h6; injection h6 with h6 _
      subst h3; subst h4; subst h5; subst h6; rfl
    exact ⟨6 + 4, by rw [← List.rotate_rotate, h2]⟩
  have hndv : [v3, v4, v5, v6].Nodup := by
    have h := hv.1
    change ([e4, e5, e6] ++ [v3, v4, v5, v6]).Nodup at h
    exact (List.nodup_append.mp h).2.1
  let idx (x : ℕ) : ℕ := [e0, e1, e2, e3].idxOf x
  have hidx_get : ∀ x ∈ [v3, v4, v5, v6], [e0, e1, e2, e3, e4, e5, e6][idx x]! = x ∧ idx x < 4 := by
    intro x hx
    have hmem : x ∈ [e0, e1, e2, e3] := hp4.symm.subset hx
    have hlt : idx x < 4 := List.idxOf_lt_length_of_mem hmem
    refine ⟨?_, hlt⟩
    have hget := List.getElem_idxOf hlt
    have hget2 : [e0, e1, e2, e3, e4, e5, e6][idx x]! = [e0, e1, e2, e3][idx x]'hlt := by
      match h : idx x, hlt with
      | 0, _ | 1, _ | 2, _ | 3, _ => rfl
    rw [hget2, hget]
  have h0 := hidx_get v3 (by simp)
  have h1 := hidx_get v4 (by simp)
  have h2 := hidx_get v5 (by simp)
  have h3 := hidx_get v6 (by simp)
  have hinj : ∀ a b, a ∈ [v3, v4, v5, v6] → b ∈ [v3, v4, v5, v6] → idx a = idx b → a = b := by
    intro a b ha hb heq
    have := (hidx_get a ha).1
    have := (hidx_get b hb).1
    rw [heq] at *
    omega
  have hne01 : idx v3 ≠ idx v4 := fun h => by
    have := hinj v3 v4 (by simp) (by simp) h; simp [this] at hndv
  have hne02 : idx v3 ≠ idx v5 := fun h => by
    have := hinj v3 v5 (by simp) (by simp) h; simp [this] at hndv
  have hne03 : idx v3 ≠ idx v6 := fun h => by
    have := hinj v3 v6 (by simp) (by simp) h; simp [this] at hndv
  have hne12 : idx v4 ≠ idx v5 := fun h => by
    have := hinj v4 v5 (by simp) (by simp) h; simp [this] at hndv
  have hne13 : idx v4 ≠ idx v6 := fun h => by
    have := hinj v4 v6 (by simp) (by simp) h; simp [this] at hndv
  have hne23 : idx v5 ≠ idx v6 := fun h => by
    have := hinj v5 v6 (by simp) (by simp) h; simp [this] at hndv
  have hnotid : (idx v3, idx v4, idx v5, idx v6) ≠ (0, 1, 2, 3) := by
    intro h
    injection h with k0 k1; injection k1 with k1 k2; injection k2 with k2 k3
    apply hne_id
    have e0' := h0.1; have e1' := h1.1; have e2' := h2.1; have e3' := h3.1
    rw [k0] at e0'; rw [k1] at e1'; rw [k2] at e2'; rw [k3] at e3'
    change e0 = v3 at e0'; change e1 = v4 at e1'; change e2 = v5 at e2'; change e3 = v6 at e3'
    rw [e0', e1', e2', e3']
  obtain ⟨t, hpt⟩ := find_perms4 ⟨idx v3, h0.2⟩ ⟨idx v4, h1.2⟩ ⟨idx v5, h2.2⟩ ⟨idx v6, h3.2⟩
    (fun h => hne01 (congrArg Fin.val h)) (fun h => hne02 (congrArg Fin.val h))
    (fun h => hne03 (congrArg Fin.val h)) (fun h => hne12 (congrArg Fin.val h))
    (fun h => hne13 (congrArg Fin.val h)) (fun h => hne23 (congrArg Fin.val h)) hnotid
  refine ⟨t.val, t.isLt, ?_⟩
  unfold w4Step
  rw [he, hpt]
  simp only [h0.1, h1.1, h2.1, h3.1]
  rfl

/-! ### `buildS7K16Tabs` Exactness Lemmas -/

theorem ciTab_lt {i : ℕ} (hi : i < (permCodes 7 7).length) :
    (ciTab 7 (permCodes 7 7))[i]! < (permCodes 7 7).length := by
  set jl := permCodes 7 7
  have hc : jl[i] ∈ jl := List.getElem_mem hi
  obtain ⟨u, hu, hu_eq⟩ := permW_of_mem_permCodes7 hc
  have hidx : jl.idxOf (code u) = i := by
    rw [hu_eq, (permCodes_nodup 7 (by omega) 7).idxOf_getElem i hi]
  rw [← hidx]
  unfold ciTab
  rw [tab_get jl _ (mem_perm (by omega) hu)]
  obtain ⟨r, hr⟩ := S.canonF_rot 7 (by omega) 7 u hu.2.1 (hu.lt16 (by omega))
  rw [PS.canonF_eq, hr]
  exact List.idxOf_lt_length_of_mem (mem_perm (by omega) (hu.rotate r))

theorem nxtTab_lt {i : ℕ} (hi : i < (permCodes 7 7).length) :
    (nxtTab 7 (permCodes 7 7))[i]! < (permCodes 7 7).length := by
  set jl := permCodes 7 7
  have hc : jl[i] ∈ jl := List.getElem_mem hi
  obtain ⟨u, hu, hu_eq⟩ := permW_of_mem_permCodes7 hc
  have hidx : jl.idxOf (code u) = i := by
    rw [hu_eq, (permCodes_nodup 7 (by omega) 7).idxOf_getElem i hi]
  rw [← hidx]
  have hnext := (PS.encB_enc 7 (by omega) (by omega)).nxt_eq u (K16.tau2 7 u) hu rfl
  change (nxtTab 7 jl)[encB 7 u]! < jl.length
  rw [hnext]
  exact List.idxOf_lt_length_of_mem (mem_perm (by omega) (K16.permW_tau2 (by omega) hu))

theorem encB_lt {u : List ℕ} (hu : PermW 7 u) : encB 7 u < (permCodes 7 7).length :=
  List.idxOf_lt_length_of_mem (mem_perm (by omega) hu)

theorem tabs_sz_le : buildS7K16Tabs.sz ≤ 5040 := permCodes7_length_le

theorem tabs_ciBA_get {u : List ℕ} (hu : PermW 7 u) :
    (baGetU16 buildS7K16Tabs.ciBA (USize.ofNat (encB 7 u))).toNat =
      (ciTab 7 (permCodes 7 7))[encB 7 u]! := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hci_lt : (ciTab 7 (permCodes 7 7))[encB 7 u]! < 65536 := by
    have := ciTab_lt hi; omega
  unfold buildS7K16Tabs
  dsimp only
  rw [baGetU16_packU16Arr (by simp; omega) (by simp; exact hi) (by
    rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hci_lt)]
  rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem tabs_nxtBA_get {u : List ℕ} (hu : PermW 7 u) :
    (baGetU16 buildS7K16Tabs.nxtBA (USize.ofNat (encB 7 u))).toNat =
      (nxtTab 7 (permCodes 7 7))[encB 7 u]! := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hlt : (nxtTab 7 (permCodes 7 7))[encB 7 u]! < 65536 := by
    have := nxtTab_lt hi; omega
  unfold buildS7K16Tabs
  dsimp only
  rw [baGetU16_packU16Arr (by simp; omega) (by simp; exact hi) (by
    rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hlt)]
  rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem tabs_b2CiBA_get {u : List ℕ} (hu : PermW 7 u) :
    (baGetU16 buildS7K16Tabs.b2CiBA (USize.ofNat (encB 7 u))).toNat =
      (ciTab 7 (permCodes 7 7))[(nxtTab 7 (permCodes 7 7))[encB 7 u]!]! := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hlt : (ciTab 7 (permCodes 7 7))[(nxtTab 7 (permCodes 7 7))[encB 7 u]!]! < 65536 := by
    have := ciTab_lt (nxtTab_lt hi); omega
  unfold buildS7K16Tabs
  dsimp only
  rw [baGetU16_packU16Arr (by simp; omega) (by simp; exact hi) (by
    rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hlt)]
  rw [getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]; dsimp only
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem tabs_s3Arr_get {u : List ℕ} (hu : PermW 7 u) {t : ℕ} (ht : t < 5) :
    (buildS7K16Tabs.s3Arr[encB 7 u * 5 + t]!).toNat = encB 7 (w3Step u t) := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hidx : encB 7 u * 5 + t < (permCodes 7 7).length * 5 := by omega
  have hdiv : (encB 7 u * 5 + t) / 5 = encB 7 u := by omega
  have hmod : (encB 7 u * 5 + t) % 5 = t := by omega
  have harr : (permCodes 7 7).toArray[encB 7 u]! = code u := arr_get _ (mem_perm (by omega) hu)
  have hw := encB_lt (permW_w3Step hu t)
  unfold buildS7K16Tabs
  dsimp only
  rw [getElem!_pos _ _ (by simp; exact hidx), Array.getElem_ofFn]
  dsimp only
  rw [hdiv, hmod, harr, s3Code_code hu t, buildCodeToIdx_get (permW_w3Step hu t),
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem tabs_s3BA_get {u : List ℕ} (hu : PermW 7 u) {t : ℕ} (ht : t < 5) :
    (baGetU16 buildS7K16Tabs.s3BA (USize.ofNat (encB 7 u * 5 + t))).toNat = encB 7 (w3Step u t) := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hidx : encB 7 u * 5 + t < (permCodes 7 7).length * 5 := by omega
  have hdiv : (encB 7 u * 5 + t) / 5 = encB 7 u := by omega
  have hmod : (encB 7 u * 5 + t) % 5 = t := by omega
  have harr : (permCodes 7 7).toArray[encB 7 u]! = code u := arr_get _ (mem_perm (by omega) hu)
  have hw := encB_lt (permW_w3Step hu t)
  unfold buildS7K16Tabs
  dsimp only
  rw [baGetU16_packU16Arr (by simp; omega) (by simp; exact hidx) (by
    rw [getElem!_pos _ _ (by simp; exact hidx), Array.getElem_ofFn]; dsimp only
    rw [hdiv, hmod, harr, s3Code_code hu t, buildCodeToIdx_get (permW_w3Step hu t),
      UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega)]
  rw [getElem!_pos _ _ (by simp; exact hidx), Array.getElem_ofFn]; dsimp only
  rw [hdiv, hmod, harr, s3Code_code hu t, buildCodeToIdx_get (permW_w3Step hu t),
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem tabs_s4BA_get {u : List ℕ} (hu : PermW 7 u) {t : ℕ} (ht : t < 23) :
    (baGetU16 buildS7K16Tabs.s4BA (USize.ofNat (encB 7 u * 23 + t))).toNat = encB 7 (w4Step u t) := by
  have hi := encB_lt hu
  have hle := permCodes7_length_le
  have hidx : encB 7 u * 23 + t < (permCodes 7 7).length * 23 := by omega
  have hdiv : (encB 7 u * 23 + t) / 23 = encB 7 u := by omega
  have hmod : (encB 7 u * 23 + t) % 23 = t := by omega
  have harr : (permCodes 7 7).toArray[encB 7 u]! = code u := arr_get _ (mem_perm (by omega) hu)
  have hw := encB_lt (permW_w4Step hu t)
  unfold buildS7K16Tabs
  dsimp only
  rw [baGetU16_packU16Arr (by simp; omega) (by simp; exact hidx) (by
    rw [getElem!_pos _ _ (by simp; exact hidx), Array.getElem_ofFn]; dsimp only
    rw [hdiv, hmod, harr, s4Code_code hu t, buildCodeToIdx_get (permW_w4Step hu t),
      UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega)]
  rw [getElem!_pos _ _ (by simp; exact hidx), Array.getElem_ofFn]; dsimp only
  rw [hdiv, hmod, harr, s4Code_code hu t, buildCodeToIdx_get (permW_w4Step hu t),
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

end FastSound
end SuperpermLowerBounds
