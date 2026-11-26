import LowerBounds.SearchFast

/-!
# Soundness of `SearchFast` with respect to Halfar's `S.search`

Proves in the Lean kernel (zero `sorry`, no custom axioms, no Mathlib dependency):
`5 ≤ k → k ≤ 15 → searchFast k A q2 C1 C2 bn fuel = false → search k A q2 C1 C2 bn fuel = false`.
-/

namespace SuperpermLowerBounds
namespace S

/-! ### 1. `UInt64` arithmetic equals `SSearch` `Nat` arithmetic for `5 ≤ k ≤ 15` -/

private theorem pow2_4n (n : Nat) : 2 ^ (4 * n) = 16 ^ n := by
  rw [Nat.pow_mul]

private theorem log2_div4_of_bounds {m r : Nat} (hlo : 16 ^ r ≤ m) (hhi : m < 16 ^ (r + 1)) :
    Nat.log2 m / 4 = r := by
  have h1 : 2 ^ (4 * r) ≤ m := by rw [pow2_4n]; exact hlo
  have h2 : m < 2 ^ (4 * r + 4) := by
    have : 2 ^ (4 * r + 4) = 16 ^ (r + 1) := by
      rw [Nat.pow_add, pow2_4n, Nat.pow_succ]; rfl
    omega
  have hge : 4 * r ≤ Nat.log2 m := (Nat.le_log2 (by omega)).mpr h1
  have hlt : Nat.log2 m < 4 * r + 4 := (Nat.log2_lt (by omega)).mpr h2
  omega

private theorem ui64_shift_right_toNat (z : UInt64) (s : UInt64) (hs : s.toNat < 64) :
    (z >>> s).toNat = z.toNat / 2 ^ s.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]

theorem nibbleLog2_eq (z : UInt64) : nibbleLog2 z = Nat.log2 z.toNat / 4 := by
  unfold nibbleLog2
  have hz : z.toNat < 2 ^ 64 := z.toFin.isLt
  have hdiv := ui64_shift_right_toNat
  by_cases h0 : z ≥ 0x100000000
  · simp only [h0, ↓reduceIte]
    have h0n : 2 ^ 32 ≤ z.toNat := h0
    have hz1 : (z >>> 32).toNat = z.toNat / 2 ^ 32 := hdiv z 32 (by decide)
    by_cases h1 : z >>> 32 ≥ 0x10000
    · simp only [h1, ↓reduceIte]
      have h1n : 2 ^ 16 ≤ (z >>> 32).toNat := h1
      have hz2 : ((z >>> 32) >>> 16).toNat = (z >>> 32).toNat / 2 ^ 16 := hdiv _ 16 (by decide)
      by_cases h2 : (z >>> 32) >>> 16 ≥ 0x100
      · simp only [h2, ↓reduceIte]
        have h2n : 2 ^ 8 ≤ ((z >>> 32) >>> 16).toNat := h2
        have hz3 : (((z >>> 32) >>> 16) >>> 8).toNat = ((z >>> 32) >>> 16).toNat / 2 ^ 8 := hdiv _ 8 (by decide)
        by_cases h3 : ((z >>> 32) >>> 16) >>> 8 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ (((z >>> 32) >>> 16) >>> 8).toNat := h3
          exact (log2_div4_of_bounds (r := 15) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : (((z >>> 32) >>> 16) >>> 8).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 14) (by omega) (by omega)).symm
      · simp only [h2, ↓reduceIte]; have h2n : ((z >>> 32) >>> 16).toNat < 2 ^ 8 := Nat.lt_of_not_ge h2
        by_cases h3 : (z >>> 32) >>> 16 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ ((z >>> 32) >>> 16).toNat := h3
          exact (log2_div4_of_bounds (r := 13) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : ((z >>> 32) >>> 16).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 12) (by omega) (by omega)).symm
    · simp only [h1, ↓reduceIte]; have h1n : (z >>> 32).toNat < 2 ^ 16 := Nat.lt_of_not_ge h1
      by_cases h2 : z >>> 32 ≥ 0x100
      · simp only [h2, ↓reduceIte]; have h2n : 2 ^ 8 ≤ (z >>> 32).toNat := h2
        have hz3 : ((z >>> 32) >>> 8).toNat = (z >>> 32).toNat / 2 ^ 8 := hdiv _ 8 (by decide)
        by_cases h3 : (z >>> 32) >>> 8 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ ((z >>> 32) >>> 8).toNat := h3
          exact (log2_div4_of_bounds (r := 11) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : ((z >>> 32) >>> 8).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 10) (by omega) (by omega)).symm
      · simp only [h2, ↓reduceIte]; have h2n : (z >>> 32).toNat < 2 ^ 8 := Nat.lt_of_not_ge h2
        by_cases h3 : z >>> 32 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ (z >>> 32).toNat := h3
          exact (log2_div4_of_bounds (r := 9) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : (z >>> 32).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 8) (by omega) (by omega)).symm
  · simp only [h0, ↓reduceIte]; have h0n : z.toNat < 2 ^ 32 := Nat.lt_of_not_ge h0
    by_cases h1 : z ≥ 0x10000
    · simp only [h1, ↓reduceIte]; have h1n : 2 ^ 16 ≤ z.toNat := h1
      have hz2 : (z >>> 16).toNat = z.toNat / 2 ^ 16 := hdiv z 16 (by decide)
      by_cases h2 : z >>> 16 ≥ 0x100
      · simp only [h2, ↓reduceIte]; have h2n : 2 ^ 8 ≤ (z >>> 16).toNat := h2
        have hz3 : ((z >>> 16) >>> 8).toNat = (z >>> 16).toNat / 2 ^ 8 := hdiv _ 8 (by decide)
        by_cases h3 : (z >>> 16) >>> 8 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ ((z >>> 16) >>> 8).toNat := h3
          exact (log2_div4_of_bounds (r := 7) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : ((z >>> 16) >>> 8).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 6) (by omega) (by omega)).symm
      · simp only [h2, ↓reduceIte]; have h2n : (z >>> 16).toNat < 2 ^ 8 := Nat.lt_of_not_ge h2
        by_cases h3 : z >>> 16 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ (z >>> 16).toNat := h3
          exact (log2_div4_of_bounds (r := 5) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : (z >>> 16).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 4) (by omega) (by omega)).symm
    · simp only [h1, ↓reduceIte]; have h1n : z.toNat < 2 ^ 16 := Nat.lt_of_not_ge h1
      by_cases h2 : z ≥ 0x100
      · simp only [h2, ↓reduceIte]; have h2n : 2 ^ 8 ≤ z.toNat := h2
        have hz3 : (z >>> 8).toNat = z.toNat / 2 ^ 8 := hdiv z 8 (by decide)
        by_cases h3 : z >>> 8 ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ (z >>> 8).toNat := h3
          exact (log2_div4_of_bounds (r := 3) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : (z >>> 8).toNat < 16 := Nat.lt_of_not_ge h3
          exact (log2_div4_of_bounds (r := 2) (by omega) (by omega)).symm
      · simp only [h2, ↓reduceIte]; have h2n : z.toNat < 2 ^ 8 := Nat.lt_of_not_ge h2
        by_cases h3 : z ≥ 0x10
        · simp only [h3, ↓reduceIte]; have h3n : 16 ≤ z.toNat := h3
          exact (log2_div4_of_bounds (r := 1) (by omega) (by omega)).symm
        · simp only [h3, ↓reduceIte]; have h3n : z.toNat < 16 := Nat.lt_of_not_ge h3
          by_cases hz0 : z.toNat = 0
          · rw [hz0]; decide
          · exact (log2_div4_of_bounds (r := 0) (by omega) (by omega)).symm

theorem posU_eq {k : Nat} (hk : k ≤ 15) (c : UInt64) :
    posU (k.toUInt64 * 0x1111111111111111) c = pos k c.toNat := by
  unfold posU pos
  rw [nibbleLog2_eq]
  have h11 : (0x1111111111111111 : UInt64).toNat = 0x1111111111111111 := by decide
  have h77 : (0x7777777777777777 : UInt64).toNat = 0x7777777777777777 := by decide
  have h88 : (0x8888888888888888 : UInt64).toNat = 0x8888888888888888 := by decide
  have hkm : (k.toUInt64 * 0x1111111111111111).toNat = k * 0x1111111111111111 := by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', h11, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have hx : (c ^^^ (k.toUInt64 * 0x1111111111111111)).toNat =
      Nat.xor c.toNat (Nat.mul k 0x1111111111111111) := by
    rw [UInt64.toNat_xor, hkm]; rfl
  have h7 : ((c ^^^ (k.toUInt64 * 0x1111111111111111)) &&& 0x7777777777777777).toNat =
      Nat.land (Nat.xor c.toNat (Nat.mul k 0x1111111111111111)) 0x7777777777777777 := by
    rw [UInt64.toNat_and, hx, h77]; rfl
  have hadd : (((c ^^^ (k.toUInt64 * 0x1111111111111111)) &&& 0x7777777777777777) + 0x7777777777777777).toNat =
      Nat.add (Nat.land (Nat.xor c.toNat (Nat.mul k 0x1111111111111111)) 0x7777777777777777) 0x7777777777777777 := by
    rw [UInt64.toNat_add, h7, h77]
    have hle : Nat.land (Nat.xor c.toNat (Nat.mul k 0x1111111111111111)) 0x7777777777777777 ≤ 0x7777777777777777 :=
      Nat.and_le_right
    exact Nat.mod_eq_of_lt (by omega)
  have hz : ((((((c ^^^ (k.toUInt64 * 0x1111111111111111)) &&& 0x7777777777777777) + 0x7777777777777777) |||
      (c ^^^ (k.toUInt64 * 0x1111111111111111))) &&& 0x8888888888888888) ^^^ 0x8888888888888888).toNat =
      Nat.xor (Nat.land (Nat.lor (Nat.add (Nat.land (Nat.xor c.toNat (Nat.mul k 0x1111111111111111)) 0x7777777777777777)
        0x7777777777777777) (Nat.xor c.toNat (Nat.mul k 0x1111111111111111))) 0x8888888888888888) 0x8888888888888888 := by
    rw [UInt64.toNat_xor, UInt64.toNat_and, UInt64.toNat_or, hadd, hx, h88]; rfl
  rw [hz]; rfl

private theorem lor_shift_eq_add {a b s : Nat} (hb : b < 2 ^ s) :
    (a * 2 ^ s) ||| b = a * 2 ^ s + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.shiftLeft_eq]
  by_cases hi : i < s
  · have hng : ¬(i ≥ s) := by omega
    simp only [hng, decide_false, Bool.false_and, Bool.false_or]
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have hs : 2 ^ s = 2 ^ i * 2 ^ (s - i) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have h2 : (a * 2 ^ s + b) / 2 ^ i = a * 2 ^ (s - i) + b / 2 ^ i := by
      rw [hs, ← Nat.mul_assoc, Nat.mul_comm a (2 ^ i), Nat.mul_assoc, Nat.mul_add_div (Nat.pow_pos (by omega)), Nat.mul_comm]
    rw [h2]
    have hsi : s - i = (s - i - 1) + 1 := by omega
    rw [hsi, Nat.pow_succ, ← Nat.mul_assoc]
    simp [Nat.mul_comm _ 2]
  · have hge : i ≥ s := by omega
    have hbi : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hge))
    rw [hbi, Bool.or_false, decide_eq_true hge, Bool.true_and]
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have hs : 2 ^ i = 2 ^ s * 2 ^ (i - s) := by rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    rw [hs, ← Nat.div_div_eq_div_mul, Nat.mul_comm a (2 ^ s), Nat.mul_add_div (Nat.pow_pos (by omega)),
      Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem ui64_mask_toNat (s : Nat) (hs : s < 64) :
    (((1 : UInt64) <<< s.toUInt64) - 1).toNat = 2 ^ s - 1 := by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hsh : ((1 : UInt64) <<< s.toUInt64).toNat = 2 ^ s := by
    rw [UInt64.toNat_shiftLeft, h1, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 64), Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)
  rw [UInt64.toNat_sub_of_le]
  · rw [hsh, h1]
  · show (1 : UInt64).toNat ≤ ((1 : UInt64) <<< s.toUInt64).toNat
    rw [hsh, h1]; exact Nat.one_le_pow s 2 (by decide)

theorem excU_eq {k : Nat} (hk1 : 1 ≤ k) (hk15 : k ≤ 15) {c : UInt64} (hc : c.toNat < 16 ^ k) :
    (excU (4 * (k - 1)).toUInt64 c).toNat = exc k c.toNat ∧
    (excU (4 * (k - 1)).toUInt64 c).toNat < 16 ^ k := by
  have hs : 4 * (k - 1) < 64 := by omega
  have h16 : 16 ^ k = 16 * 16 ^ (k - 1) := by
    calc 16 ^ k = 16 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk1]
    _ = 16 ^ (k - 1) * 16 := Nat.pow_succ _ _
    _ = 16 * 16 ^ (k - 1) := Nat.mul_comm _ _
  have hp1 : 2 ^ (4 * (k - 1)) = 16 ^ (k - 1) := pow2_4n (k - 1)
  have hlo : (c &&& 0xF).toNat = c.toNat % 16 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod c.toNat 4
  have hhi : (c >>> 4).toNat = c.toNat / 16 := by
    rw [ui64_shift_right_toNat c 4 (by decide)]; rfl
  have h64 : 16 ^ k ≤ 2 ^ 60 := by
    rw [← pow2_4n]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsh : ((c &&& 0xF) <<< (4 * (k - 1)).toUInt64).toNat = (c.toNat % 16) * 16 ^ (k - 1) := by
    rw [UInt64.toNat_shiftLeft, hlo, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega : 4 * (k - 1) < 2 ^ 64), Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq, hp1]
    have hlt : c.toNat % 16 * 16 ^ (k - 1) < 16 ^ k := by
      rw [h16]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide)) (Nat.pow_pos (by decide))
    exact Nat.mod_eq_of_lt (by omega)
  have hdivlt : c.toNat / 16 < 16 ^ (k - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm, ← h16]; exact hc
  have heq : (excU (4 * (k - 1)).toUInt64 c).toNat = (c.toNat % 16) * 16 ^ (k - 1) + c.toNat / 16 := by
    unfold excU
    rw [UInt64.toNat_or, hsh, hhi, ← hp1]
    exact lor_shift_eq_add (by rw [hp1]; exact hdivlt)
  refine ⟨by rw [heq]; rfl, ?_⟩
  rw [heq, h16]
  have : c.toNat % 16 ≤ 15 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have : (c.toNat % 16) * 16 ^ (k - 1) ≤ 15 * 16 ^ (k - 1) := Nat.mul_le_mul_right _ this
  omega

theorem doorU_eq {k : Nat} (hk2 : 2 ≤ k) (hk15 : k ≤ 15) {x : UInt64} (hx : x.toNat < 16 ^ k) :
    (doorU (4 * (k - 1)).toUInt64 (4 * (k - 2)).toUInt64
      (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1) x).toNat = doorc k x.toNat ∧
    (doorU (4 * (k - 1)).toUInt64 (4 * (k - 2)).toUInt64
      (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1) x).toNat < 16 ^ k := by
  have hs1 : 4 * (k - 1) < 64 := by omega
  have hs2 : 4 * (k - 2) < 64 := by omega
  have hp1 : 2 ^ (4 * (k - 1)) = 16 ^ (k - 1) := pow2_4n (k - 1)
  have hp2 : 2 ^ (4 * (k - 2)) = 16 ^ (k - 2) := pow2_4n (k - 2)
  have h16k : 16 ^ k = 16 ^ (k - 2) * 256 := by
    calc 16 ^ k = 16 ^ ((k - 2) + 2) := by rw [Nat.sub_add_cancel hk2]
    _ = 16 ^ (k - 2) * 256 := Nat.pow_add _ _ _
  have h16k1 : 16 ^ k = 16 ^ (k - 1) * 16 := by
    calc 16 ^ k = 16 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
    _ = 16 ^ (k - 1) * 16 := Nat.pow_succ _ _
  have h64 : 16 ^ k ≤ 2 ^ 60 := by
    rw [← pow2_4n]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hm2 : (x &&& (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)).toNat = x.toNat % 16 ^ (k - 2) := by
    rw [UInt64.toNat_and, ui64_mask_toNat (4 * (k - 2)) hs2, Nat.and_two_pow_sub_one_eq_mod, hp2]
  have ha : ((x &&& (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)) <<< 8).toNat =
      (x.toNat % 16 ^ (k - 2)) * 256 := by
    rw [UInt64.toNat_shiftLeft, hm2]
    have h8 : (8 : UInt64).toNat % 64 = 8 := by decide
    rw [h8, Nat.shiftLeft_eq]
    have hlt : x.toNat % 16 ^ (k - 2) * 256 < 16 ^ k := by
      rw [h16k]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.pow_pos (by decide))) (by decide)
    exact Nat.mod_eq_of_lt (by omega)
  have hb0 : ((x >>> (4 * (k - 2)).toUInt64) &&& 0xF).toNat = (x.toNat / 16 ^ (k - 2)) % 16 := by
    rw [UInt64.toNat_and, ui64_shift_right_toNat x _ (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hs2)]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), hp2]
    exact Nat.and_two_pow_sub_one_eq_mod _ 4
  have hb : (((x >>> (4 * (k - 2)).toUInt64) &&& 0xF) <<< 4).toNat = ((x.toNat / 16 ^ (k - 2)) % 16) * 16 := by
    rw [UInt64.toNat_shiftLeft, hb0]
    have h4 : (4 : UInt64).toNat % 64 = 4 := by decide
    rw [h4, Nat.shiftLeft_eq]
    have hlt : (x.toNat / 16 ^ (k - 2)) % 16 < 16 := Nat.mod_lt _ (by decide)
    exact Nat.mod_eq_of_lt (by omega)
  have hc : (x >>> (4 * (k - 1)).toUInt64).toNat = x.toNat / 16 ^ (k - 1) := by
    rw [ui64_shift_right_toNat x _ (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hs1)]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), hp1]
  have hclt : x.toNat / 16 ^ (k - 1) < 16 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← h16k1]; exact hx
  have hbc : ((((x >>> (4 * (k - 2)).toUInt64) &&& 0xF) <<< 4) ||| (x >>> (4 * (k - 1)).toUInt64)).toNat =
      ((x.toNat / 16 ^ (k - 2)) % 16) * 16 + x.toNat / 16 ^ (k - 1) := by
    rw [UInt64.toNat_or, hb, hc]; exact lor_shift_eq_add (s := 4) hclt
  have hbclt : ((x.toNat / 16 ^ (k - 2)) % 16) * 16 + x.toNat / 16 ^ (k - 1) < 256 := by
    have : (x.toNat / 16 ^ (k - 2)) % 16 ≤ 15 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    omega
  have heq : (doorU (4 * (k - 1)).toUInt64 (4 * (k - 2)).toUInt64
      (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1) x).toNat =
      (x.toNat % 16 ^ (k - 2)) * 256 + ((x.toNat / 16 ^ (k - 2)) % 16) * 16 + x.toNat / 16 ^ (k - 1) := by
    unfold doorU
    rw [UInt64.or_assoc, UInt64.toNat_or, ha, hbc, lor_shift_eq_add (s := 8) hbclt, Nat.add_assoc]
  refine ⟨?_, ?_⟩
  · rw [heq]; unfold doorc pw
    change _ = (x.toNat % 16 ^ (k - 2)) * 256 + ((x.toNat / 16 ^ (k - 2)) % 16) * 16 + x.toNat / 16 ^ (k - 1)
    rfl
  · rw [heq, h16k]
    have : x.toNat % 16 ^ (k - 2) + 1 ≤ 16 ^ (k - 2) := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have : (x.toNat % 16 ^ (k - 2)) * 256 + 256 ≤ 16 ^ (k - 2) * 256 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right 256 this
    omega

theorem rotlU_eq {k i : Nat} (hk15 : k ≤ 15) (hi : i ≤ k) {c : UInt64} (hc : c.toNat < 16 ^ k) :
    (rotlU k c i).toNat = rotl k c.toNat i := by
  unfold rotlU rotl pw
  change (if (i == 0 || decide (i ≥ k)) = true then c else _).toNat =
    (c.toNat % 16 ^ (k - i)) * 16 ^ i + c.toNat / 16 ^ (k - i)
  by_cases hz : i = 0
  · subst hz
    simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, Nat.add_zero]
  · by_cases hge : i ≥ k
    · have hik : i = k := by omega
      subst hik
      simp only [ge_iff_le, Nat.le_refl, decide_true, Bool.or_true, ↓reduceIte, Nat.sub_self,
        Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Nat.div_one, Nat.zero_add]
    · have hlt : i < k := by omega
      simp only [beq_iff_eq, hz, ge_iff_le, Nat.not_le.mpr hlt, decide_false, Bool.or_false,
        ↓reduceIte]
      have hs1 : 4 * i < 64 := by omega
      have hs2 : 4 * (k - i) < 64 := by omega
      have hp1 : 2 ^ (4 * i) = 16 ^ i := pow2_4n i
      have hp2 : 2 ^ (4 * (k - i)) = 16 ^ (k - i) := pow2_4n (k - i)
      have h16k : 16 ^ k = 16 ^ (k - i) * 16 ^ i := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hi]
      have h64 : 16 ^ k ≤ 2 ^ 60 := by
        rw [← pow2_4n]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have hm : (c &&& (((1 : UInt64) <<< (4 * (k - i)).toUInt64) - 1)).toNat = c.toNat % 16 ^ (k - i) := by
        rw [UInt64.toNat_and, ui64_mask_toNat (4 * (k - i)) hs2, Nat.and_two_pow_sub_one_eq_mod, hp2]
      have hl : ((c &&& (((1 : UInt64) <<< (4 * (k - i)).toUInt64) - 1)) <<< (4 * i).toUInt64).toNat =
          (c.toNat % 16 ^ (k - i)) * 16 ^ i := by
        rw [UInt64.toNat_shiftLeft, hm, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega : 4 * i < 2 ^ 64), Nat.mod_eq_of_lt hs1, Nat.shiftLeft_eq, hp1]
        have hlt2 : c.toNat % 16 ^ (k - i) * 16 ^ i < 16 ^ k := by
          rw [h16k]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))
        exact Nat.mod_eq_of_lt (by omega)
      have hr : (c >>> (4 * (k - i)).toUInt64).toNat = c.toNat / 16 ^ (k - i) := by
        rw [ui64_shift_right_toNat c _ (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hs2)]
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), hp2]
      have hrlt : c.toNat / 16 ^ (k - i) < 16 ^ i := by
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← h16k]; exact hc
      rw [UInt64.toNat_or, hl, hr, ← hp1]
      exact lor_shift_eq_add (by rw [hp1]; exact hrlt)

theorem canonU_eq {k : Nat} (hk15 : k ≤ 15) {c : UInt64} (hc : c.toNat < 16 ^ k) :
    (canonU k (k.toUInt64 * 0x1111111111111111) c).toNat = canon k c.toNat := by
  unfold canonU canon
  rw [posU_eq hk15 c]
  exact rotlU_eq hk15 (by omega) hc

theorem idcU_eq : ∀ {n : Nat}, n ≤ 15 → (idcU n).toNat = idc n ∧ (idcU n).toNat < 16 ^ n
  | 0, _ => ⟨rfl, by decide⟩
  | n + 1, hn => by
    obtain ⟨heq, hlt⟩ := idcU_eq (n := n) (by omega)
    have h64 : 16 ^ (n + 1) ≤ 2 ^ 60 := by
      rw [← pow2_4n]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hsh : (idcU n <<< 4).toNat = idc n * 16 := by
      rw [UInt64.toNat_shiftLeft, heq]
      have h4 : (4 : UInt64).toNat % 64 = 4 := by decide
      rw [h4, Nat.shiftLeft_eq]
      have : idc n * 16 < 16 ^ (n + 1) := by
        rw [Nat.pow_succ]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by decide)
      exact Nat.mod_eq_of_lt (by omega)
    have hn1 : ((n + 1).toUInt64).toNat = n + 1 := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hr : (idcU (n + 1)).toNat = idc n * 16 + (n + 1) := by
      unfold idcU; rw [UInt64.toNat_or, hsh, hn1]; exact lor_shift_eq_add (s := 4) (by omega)
    refine ⟨by rw [hr, idc_succ], ?_⟩
    rw [hr, Nat.pow_succ]
    have : idc n + 1 ≤ 16 ^ n := by omega
    have : idc n * 16 + 16 ≤ 16 ^ n * 16 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right 16 this
    omega

private theorem child_code_eq {k : Nat} (hk3 : 3 ≤ k) (hk15 : k ≤ 15) {y : UInt64}
    (hy : y.toNat < 16 ^ k) {u v w : UInt64} (hu : u.toNat < 16) (hv : v.toNat < 16) (hw : w.toNat < 16) :
    let base := (y &&& (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1)) <<< 12
    (base ||| (u <<< 8) ||| (v <<< 4) ||| w).toNat =
      (y.toNat % 16 ^ (k - 3)) * 4096 + (u.toNat * 256 + v.toNat * 16 + w.toNat) ∧
    (base ||| (u <<< 8) ||| (v <<< 4) ||| w).toNat < 16 ^ k := by
  intro base
  have hs3 : 4 * (k - 3) < 64 := by omega
  have hp3 : 2 ^ (4 * (k - 3)) = 16 ^ (k - 3) := pow2_4n (k - 3)
  have h16k : 16 ^ k = 16 ^ (k - 3) * 4096 := by
    calc 16 ^ k = 16 ^ ((k - 3) + 3) := by rw [Nat.sub_add_cancel hk3]
    _ = 16 ^ (k - 3) * 4096 := Nat.pow_add _ _ _
  have h64 : 16 ^ k ≤ 2 ^ 60 := by
    rw [← pow2_4n]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hm3 : (y &&& (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1)).toNat = y.toNat % 16 ^ (k - 3) := by
    rw [UInt64.toNat_and, ui64_mask_toNat (4 * (k - 3)) hs3, Nat.and_two_pow_sub_one_eq_mod, hp3]
  have hbase : base.toNat = (y.toNat % 16 ^ (k - 3)) * 4096 := by
    show ((y &&& (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1)) <<< 12).toNat = _
    rw [UInt64.toNat_shiftLeft, hm3]
    have h12 : (12 : UInt64).toNat % 64 = 12 := by decide
    rw [h12, Nat.shiftLeft_eq]
    have hlt : y.toNat % 16 ^ (k - 3) * 4096 < 16 ^ k := by
      rw [h16k]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.pow_pos (by decide))) (by decide)
    exact Nat.mod_eq_of_lt (by omega)
  have hu8 : (u <<< 8).toNat = u.toNat * 256 := by
    rw [UInt64.toNat_shiftLeft]
    have h8 : (8 : UInt64).toNat % 64 = 8 := by decide
    rw [h8, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hv4 : (v <<< 4).toNat = v.toNat * 16 := by
    rw [UInt64.toNat_shiftLeft]
    have h4 : (4 : UInt64).toNat % 64 = 4 := by decide
    rw [h4, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hvw : ((v <<< 4) ||| w).toNat = v.toNat * 16 + w.toNat := by
    rw [UInt64.toNat_or, hv4]; exact lor_shift_eq_add (s := 4) hw
  have huvw : ((u <<< 8) ||| ((v <<< 4) ||| w)).toNat = u.toNat * 256 + (v.toNat * 16 + w.toNat) := by
    rw [UInt64.toNat_or, hu8, hvw]; exact lor_shift_eq_add (s := 8) (by omega)
  have heq : (base ||| (u <<< 8) ||| (v <<< 4) ||| w).toNat =
      (y.toNat % 16 ^ (k - 3)) * 4096 + (u.toNat * 256 + v.toNat * 16 + w.toNat) := by
    rw [UInt64.or_assoc, UInt64.or_assoc, UInt64.toNat_or, hbase, huvw, lor_shift_eq_add (s := 12) (by omega), Nat.add_assoc]
  refine ⟨heq, ?_⟩
  rw [heq, h16k]
  have : y.toNat % 16 ^ (k - 3) + 1 ≤ 16 ^ (k - 3) := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have : (y.toNat % 16 ^ (k - 3)) * 4096 + 4096 ≤ 16 ^ (k - 3) * 4096 := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right 4096 this
  omega

/-! ### 2. Flat LIFO hash-table invariant -/

def HTSub (tab : Array Nat) (T : Tr) : Prop :=
  tab.size = HT_SIZE ∧ ∀ i, tab.getD i 0 ≠ 0 → Tr.mem T (tab.getD i 0) = true

private theorem htsub_empty : HTSub (Array.replicate HT_SIZE 0) Tr.leaf := by
  refine ⟨Array.size_replicate, fun i h => ?_⟩
  have : (Array.replicate HT_SIZE 0).getD i 0 = 0 := by simp [Array.getD]
  exact absurd this h

private theorem tr_mem_ins_self (t : Tr) (x : Nat) : Tr.mem (Tr.ins t x) x = true := by
  induction t with
  | leaf =>
    rw [Tr.ins_leaf, Tr.mem_node]
    have h : Nat.ble x x = true := Nat.ble_eq.mpr (Nat.le_refl x)
    simp [h]
  | node l key r ihl ihr =>
    rw [Tr.ins_node]
    by_cases h : Nat.ble key x = true
    · simp only [h, Bool.cond_true, Tr.mem_node]
      by_cases h2 : Nat.ble x key = true
      · simp [h2]
      · simp [h2, ihr]
    · simp only [Bool.not_eq_true] at h
      simp only [h, Bool.cond_false, Tr.mem_node]
      exact ihl

private theorem tr_mem_ins_of_mem (t : Tr) (x y : Nat) (hmem : Tr.mem t y = true) :
    Tr.mem (Tr.ins t x) y = true := by
  induction t with
  | leaf => rw [Tr.mem_leaf] at hmem; cases hmem
  | node l key r ihl ihr =>
    rw [Tr.mem_node] at hmem; rw [Tr.ins_node]
    by_cases hx : Nat.ble key x = true
    · simp only [hx, Bool.cond_true, Tr.mem_node]
      by_cases hy : Nat.ble key y = true
      · simp only [hy, Bool.cond_true] at hmem ⊢
        by_cases hy2 : Nat.ble y key = true
        · simp [hy2]
        · simp only [hy2, Bool.cond_false] at hmem ⊢; exact ihr hmem
      · simp only [Bool.not_eq_true] at hy; simp only [hy, Bool.cond_false] at hmem ⊢; exact hmem
    · simp only [Bool.not_eq_true] at hx; simp only [hx, Bool.cond_false, Tr.mem_node]
      by_cases hy : Nat.ble key y = true
      · simp only [hy, Bool.cond_true] at hmem ⊢; exact hmem
      · simp only [Bool.not_eq_true] at hy; simp only [hy, Bool.cond_false] at hmem ⊢; exact ihl hmem

private theorem land_ht_mask_lt (n : Nat) : (n &&& HT_MASK) < HT_SIZE := by
  have h : n &&& HT_MASK ≤ HT_MASK := Nat.and_le_right
  unfold HT_MASK HT_SIZE at *; omega

private theorem probeHT_coll (tab : Array Nat) (ck : Nat) :
    ∀ steps i, i < HT_SIZE → probeHT tab ck steps i = HT_COLL → ∃ j, tab.getD j 0 = ck
  | 0, _, _, h => by unfold probeHT at h; simp [HT_FULL, HT_COLL] at h
  | steps + 1, i, hi, h => by
    unfold probeHT at h
    by_cases hv0 : tab.getD i 0 = 0
    · simp only [hv0, beq_self_eq_true, ↓reduceIte] at h
      unfold HT_SIZE at hi; unfold HT_COLL at h; omega
    · simp only [beq_iff_eq, hv0, ↓reduceIte] at h
      by_cases hvc : tab.getD i 0 = ck
      · exact ⟨i, hvc⟩
      · simp only [hvc, ↓reduceIte] at h
        exact probeHT_coll tab ck steps ((i + 1) &&& HT_MASK) (land_ht_mask_lt _) h

private theorem probeHT_free (tab : Array Nat) (ck : Nat) :
    ∀ steps i, i < HT_SIZE → probeHT tab ck steps i < HT_SIZE →
      tab.getD (probeHT tab ck steps i) 0 = 0
  | 0, _, _, h => by unfold probeHT at h; unfold HT_FULL HT_SIZE at h; omega
  | steps + 1, i, hi, h => by
    unfold probeHT at h ⊢
    by_cases hv0 : tab.getD i 0 = 0
    · simp only [hv0, beq_self_eq_true, ↓reduceIte] at h ⊢
    · simp only [beq_iff_eq, hv0, ↓reduceIte] at h ⊢
      by_cases hvc : tab.getD i 0 = ck
      · simp only [hvc, ↓reduceIte] at h; exact absurd h (by decide)
      · simp only [hvc, ↓reduceIte] at h ⊢
        exact probeHT_free tab ck steps ((i + 1) &&& HT_MASK) (land_ht_mask_lt _) h

private theorem array_setBang_eq (tab : Array Nat) (slot v : Nat) (hslot : slot < tab.size) :
    tab.set! slot v = tab.set slot v hslot := by
  simp [Array.set!, Array.setIfInBounds, hslot]

private theorem getD_set_eq (tab : Array Nat) (slot v : Nat) (hslot : slot < tab.size) (i : Nat) :
    (tab.set! slot v).getD i 0 = if i = slot then v else tab.getD i 0 := by
  rw [array_setBang_eq tab slot v hslot]
  simp only [Array.getD, Array.size_set]
  by_cases hi : i < tab.size
  · simp only [hi, ↓reduceDIte]
    by_cases heq : i = slot
    · subst heq; simp
    · simp [heq, Array.getElem_set_ne hslot hi (Ne.symm heq)]
  · have hne : i ≠ slot := by omega
    simp [hi, hne]

private theorem htsub_set {tab : Array Nat} {T : Tr} (hsub : HTSub tab T) {slot ck : Nat}
    (hslot : slot < HT_SIZE) : HTSub (tab.set! slot ck) (Tr.ins T ck) := by
  have hsz : slot < tab.size := by rw [hsub.1]; exact hslot
  refine ⟨by rw [array_setBang_eq tab slot ck hsz, Array.size_set, hsub.1], fun i hne => ?_⟩
  rw [getD_set_eq tab slot ck hsz i] at hne ⊢
  by_cases heq : i = slot
  · simp only [heq, ↓reduceIte] at hne ⊢; exact tr_mem_ins_self T ck
  · simp only [heq, ↓reduceIte] at hne ⊢; exact tr_mem_ins_of_mem T ck _ (hsub.2 i hne)

private theorem set_restore {tab : Array Nat} {slot ck : Nat} (hsz : slot < tab.size)
    (h0 : tab.getD slot 0 = 0) : (tab.set! slot ck).set! slot 0 = tab := by
  rw [array_setBang_eq tab slot ck hsz]
  have hsz1 : slot < (tab.set slot ck hsz).size := by rw [Array.size_set]; exact hsz
  rw [array_setBang_eq _ slot 0 hsz1]
  apply Array.ext
  · simp
  · intro i hi1 hi2
    by_cases heq : i = slot
    · subst heq
      rw [Array.getElem_set_self]
      have : tab.getD i 0 = tab[i] := by simp [Array.getD, hi2]
      omega
    · have hi' : i < (tab.set slot ck hsz).size := by rw [Array.size_set]; exact hi2
      rw [Array.getElem_set_ne hsz1 hi' (Ne.symm heq), Array.getElem_set_ne hsz hi2 (Ne.symm heq)]

/-! ### 3. Key-irrelevance of `goK` and unified step lemma for `walkFast` -/

private theorem goK_key_irrel (k A q2 C1 C2 bn : Nat) :
    ∀ fuel st key1 key2,
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel st key1 =
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel st key2
  | 0, _, _, _ => rfl
  | fuel + 1, st, key1, key2 => by
    rw [goK_succ, goK_succ]
    cases viol C1 bn st
    · simp only [Bool.cond_false]
      suffices h : ∀ (l : List St) (j : Nat),
          anyIdx (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c (i :: key1)) l j =
          anyIdx (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c (i :: key2)) l j from h _ 0
      intro l
      induction l with
      | nil => intro j; rfl
      | cons c t ih =>
        intro j
        rw [anyIdx_cons, anyIdx_cons, goK_key_irrel k A q2 C1 C2 bn fuel c (j :: key1) (j :: key2), ih]
    · simp

private theorem anyIdx_const_false_iff (P : St → Bool) (l : List St) :
    ∀ j, anyIdx (fun c _ => P c) l j = false ↔ ∀ c ∈ l, P c = false := by
  induction l with
  | nil => intro j; simp [anyIdx_nil]
  | cons c t ih =>
    intro j
    rw [anyIdx_cons, Bool.or_eq_false_iff, ih (j + 1)]; simp

private theorem anyIdx_goK_false_iff (k A q2 C1 C2 bn fuel : Nat) (l : List St) (key : List Nat) (j : Nat) :
    anyIdx (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c (i :: key)) l j = false ↔
    ∀ c ∈ l, goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [] = false := by
  have h : anyIdx (fun c i => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c (i :: key)) l j =
      anyIdx (fun c _ => goK k A q2 C1 C2 bn (fun _ _ => true) fuel c []) l j := by
    induction l generalizing j with
    | nil => rfl
    | cons c t ih =>
      rw [anyIdx_cons, anyIdx_cons, goK_key_irrel k A q2 C1 C2 bn fuel c (j :: key) [], ih]
  rw [h, anyIdx_const_false_iff]

/-- Unified induction on `n` for `walkFast`, given soundness of `goFast` at `fuel`. -/
private theorem walkFast_step_of_go {k : Nat} (hk5 : 5 ≤ k) (hk15 : k ≤ 15)
    (A q2 C1 C2 bn fuel : Nat)
    (hgo : ∀ (y : UInt64) (P N f : Nat) (tab : Array Nat) (T : Tr),
      y.toNat < 16 ^ k → HTSub tab T →
      (goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel y P N f tab).size ≠ 0 →
      goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel y P N f tab = tab ∧
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel ⟨y.toNat, T, P, N, f⟩ [] = false) :
    ∀ (n : Nat) (D : UInt64) (P N f : Nat) (tab : Array Nat) (T : Tr) (acc : List St),
      D.toNat < 16 ^ k → HTSub tab T →
      (∀ c ∈ acc, goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [] = false) →
      (walkFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel P N f n D tab).size ≠ 0 →
      walkFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel P N f n D tab = tab ∧
      ∀ c ∈ walk k A q2 C2 P N f n D.toNat T acc,
        goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [] = false := by
  intro n
  induction n with
  | zero =>
    intro D P N f tab T acc _ _ hacc _
    rw [walkFast, walk_zero]
    exact ⟨rfl, hacc⟩
  | succ n ihn =>
    intro D P N f tab T acc hD hsub hacc hne
    rw [walkFast] at hne ⊢
    dsimp only [] at hne ⊢
    generalize hckU : canonU k (k.toUInt64 * 0x1111111111111111) D = ckU at hne ⊢
    have hck_eq : ckU.toNat = canon k D.toNat := hckU ▸ canonU_eq hk15 hD
    by_cases hck0 : ckU.toNat = 0
    · simp only [hck0, beq_self_eq_true, ↓reduceIte, Array.size_empty, ne_eq, not_true_eq_false] at hne
    · simp only [beq_iff_eq, hck0, ↓reduceIte] at hne ⊢
      have hhash : hashU ckU < HT_SIZE := land_ht_mask_lt _
      generalize hslot : probeHT tab ckU.toNat 512 (hashU ckU) = slot at hne ⊢
      by_cases hcoll : slot = HT_COLL
      · simp only [hcoll, ↓reduceIte] at hne ⊢
        obtain ⟨j, hj⟩ := probeHT_coll tab ckU.toNat 512 (hashU ckU) hhash (hslot.trans hcoll)
        have hmem : Tr.mem T ckU.toNat = true := hj ▸ hsub.2 j (hj.symm ▸ hck0)
        refine ⟨trivial, ?_⟩
        rw [walk_succ, ← hck_eq, hmem]; simpa using hacc
      · simp only [hcoll, ↓reduceIte] at hne ⊢
        by_cases hfull : slot ≥ HT_SIZE
        · simp only [hfull, ↓reduceIte, Array.size_empty, ne_eq, not_true_eq_false] at hne
        · simp only [hfull, ↓reduceIte] at hne ⊢
          have hslot_lt : slot < HT_SIZE := Nat.lt_of_not_ge hfull
          have hslot_free : tab.getD slot 0 = 0 := hslot ▸ probeHT_free tab ckU.toNat 512 (hashU ckU) hhash (hslot.symm ▸ hslot_lt)
          have hsz : slot < tab.size := by rw [hsub.1]; exact hslot_lt
          let tab1 := tab.set! slot ckU.toNat
          have hsub1 : HTSub tab1 (Tr.ins T ckU.toNat) := htsub_set hsub hslot_lt
          obtain ⟨hex_eq, hex_lt⟩ := excU_eq (by omega) hk15 hD
          obtain ⟨hdoor_eq, hdoor_lt⟩ := doorU_eq (by omega) hk15 hex_lt
          generalize htab2 : (if n = 0 then
              if f = 1 then tab1
              else goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
                (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
                (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
                (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel (excU (4 * (k - 1)).toUInt64 D) P (N + q2) 0 tab1
            else
              let nP := P + A * n
              let nN := N + q2
              if nN + C2 ≤ nP then tab1
              else if f = 0 then
                if N ≤ P then tab1
                else goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
                  (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
                  (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
                  (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel (excU (4 * (k - 1)).toUInt64 D) nP nN (if 2 ≤ n then 2 else 1) tab1
              else
                goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
                  (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
                  (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
                  (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel (excU (4 * (k - 1)).toUInt64 D) nP nN (if 2 ≤ n then 2 else f) tab1) = tab2 at hne ⊢
          by_cases hsz2 : tab2.size = 0
          · simp only [hsz2, ↓reduceIte, ne_eq, not_true_eq_false] at hne
          · simp only [hsz2, ↓reduceIte] at hne ⊢
            have hkid : tab2 = tab1 ∧
                ∀ c ∈ kid A q2 C2 P N f n (exc k D.toNat) (Tr.ins T ckU.toNat) acc,
                  goK k A q2 C1 C2 bn (fun _ _ => true) fuel c [] = false := by
              rw [kid_eq]
              by_cases hn0 : n = 0
              · subst hn0
                simp only [↓reduceIte] at htab2
                have hb0 : Nat.beq 0 0 = true := rfl
                by_cases hf1 : f = 1
                · subst hf1; simp only [↓reduceIte] at htab2
                  have hbf1 : Nat.beq 1 1 = true := rfl
                  refine ⟨htab2.symm, ?_⟩; simpa [hb0, hbf1] using hacc
                · simp only [hf1, ↓reduceIte] at htab2
                  have hbf1 : Nat.beq f 1 = false := by
                    cases f with | zero => rfl | succ m => cases m with | zero => exact absurd rfl hf1 | succ _ => rfl
                  obtain ⟨et, hg⟩ := hgo (excU (4 * (k - 1)).toUInt64 D) P (N + q2) 0 tab1 (Tr.ins T ckU.toNat) hex_lt hsub1 (htab2 ▸ hsz2)
                  refine ⟨htab2.symm.trans et, fun c hc => ?_⟩
                  simp only [hb0, Bool.cond_true, hbf1, Bool.cond_false] at hc
                  rcases List.mem_cons.mp hc with rfl | hmem
                  · rw [← hex_eq]; exact hg
                  · exact hacc c hmem
              · simp only [hn0, ↓reduceIte] at htab2
                have hb0 : Nat.beq n 0 = false := by cases n with | zero => exact absurd rfl hn0 | succ _ => rfl
                by_cases hle : N + q2 + C2 ≤ P + A * n
                · simp only [hle, ↓reduceIte] at htab2
                  have hble : Nat.ble (N + q2 + C2) (P + A * n) = true := Nat.ble_eq.mpr hle
                  refine ⟨htab2.symm, ?_⟩; simpa [hb0, hble] using hacc
                · have hble : Nat.ble (N + q2 + C2) (P + A * n) = false :=
                    Bool.eq_false_iff.mpr (fun h => hle (Nat.ble_eq.mp h))
                  simp only [hle, ↓reduceIte] at htab2
                  by_cases hf0 : f = 0
                  · subst hf0; simp only [↓reduceIte] at htab2
                    have hbf0 : Nat.beq 0 0 = true := rfl
                    by_cases hnp : N ≤ P
                    · simp only [hnp, ↓reduceIte] at htab2
                      have hbl2 : Nat.ble N P = true := Nat.ble_eq.mpr hnp
                      refine ⟨htab2.symm, ?_⟩; simpa [hb0, hble, hbf0, hbl2] using hacc
                    · have hbl2 : Nat.ble N P = false :=
                        Bool.eq_false_iff.mpr (fun h => hnp (Nat.ble_eq.mp h))
                      simp only [hnp, ↓reduceIte] at htab2
                      obtain ⟨et, hg⟩ := hgo (excU (4 * (k - 1)).toUInt64 D) (P + A * n) (N + q2) (if 2 ≤ n then 2 else 1) tab1 (Tr.ins T ckU.toNat) hex_lt hsub1 (htab2 ▸ hsz2)
                      refine ⟨htab2.symm.trans et, fun c hc => ?_⟩
                      simp only [hb0, Bool.cond_false, hble, hbf0, Bool.cond_true, hbl2] at hc
                      have h2eq : (bif Nat.ble 2 n then 2 else 1) = (if 2 ≤ n then 2 else 1) := by
                        by_cases h2 : 2 ≤ n <;> simp [h2, Nat.ble_eq]
                      rw [h2eq] at hc
                      rcases List.mem_cons.mp hc with rfl | hmem
                      · rw [← hex_eq]; exact hg
                      · exact hacc c hmem
                  · simp only [hf0, ↓reduceIte] at htab2
                    have hbf0 : Nat.beq f 0 = false := by cases f with | zero => exact absurd rfl hf0 | succ _ => rfl
                    obtain ⟨et, hg⟩ := hgo (excU (4 * (k - 1)).toUInt64 D) (P + A * n) (N + q2) (if 2 ≤ n then 2 else f) tab1 (Tr.ins T ckU.toNat) hex_lt hsub1 (htab2 ▸ hsz2)
                    refine ⟨htab2.symm.trans et, fun c hc => ?_⟩
                    simp only [hb0, Bool.cond_false, hble, hbf0] at hc
                    have h2eq : (bif Nat.ble 2 n then 2 else f) = (if 2 ≤ n then 2 else f) := by
                      by_cases h2 : 2 ≤ n <;> simp [h2, Nat.ble_eq]
                    rw [h2eq] at hc
                    rcases List.mem_cons.mp hc with rfl | hmem
                    · rw [← hex_eq]; exact hg
                    · exact hacc c hmem
            obtain ⟨htab2_eq, hkid_all⟩ := hkid
            rw [htab2_eq] at hne ⊢
            generalize htab3 : walkFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
              (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
              (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
              (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel P N f n
              (doorU (4 * (k - 1)).toUInt64 (4 * (k - 2)).toUInt64
                (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1) (excU (4 * (k - 1)).toUInt64 D)) tab1 = tab3 at hne ⊢
            by_cases hsz3 : tab3.size = 0
            · simp only [hsz3, ↓reduceIte, ne_eq, not_true_eq_false] at hne
            · simp only [hsz3, ↓reduceIte] at hne ⊢
              obtain ⟨et3, hwalk3⟩ := ihn _ P N f tab1 (Tr.ins T ckU.toNat) _ hdoor_lt hsub1 hkid_all (htab3 ▸ hsz3)
              refine ⟨by rw [← htab3, et3]; exact set_restore hsz hslot_free, ?_⟩
              rw [walk_succ, ← hck_eq]
              cases Tr.mem T ckU.toNat
              · simp only [Bool.cond_false]
                rw [hdoor_eq, hex_eq] at hwalk3
                exact hwalk3
              · simpa using hacc

/-! ### 4. Main induction on `fuel` -/

private theorem goFast_sound {k : Nat} (hk5 : 5 ≤ k) (hk15 : k ≤ 15) (A q2 C1 C2 bn : Nat) :
    ∀ fuel (y : UInt64) (P N f : Nat) (tab : Array Nat) (T : Tr),
      y.toNat < 16 ^ k → HTSub tab T →
      (goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel y P N f tab).size ≠ 0 →
      goFast k (k.toUInt64 * 0x1111111111111111) (4 * (k - 1)).toUInt64
        (4 * (k - 2)).toUInt64 (4 * (k - 3)).toUInt64
        (((1 : UInt64) <<< (4 * (k - 2)).toUInt64) - 1)
        (((1 : UInt64) <<< (4 * (k - 3)).toUInt64) - 1) A q2 C1 C2 bn fuel y P N f tab = tab ∧
      goK k A q2 C1 C2 bn (fun _ _ => true) fuel ⟨y.toNat, T, P, N, f⟩ [] = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro y P N f tab T _ _ hne
    rw [goFast] at hne; simp at hne
  | succ fuel ih =>
    have ih_walk := walkFast_step_of_go hk5 hk15 A q2 C1 C2 bn fuel ih
    intro y P N f tab T hy hsub hne
    rw [goFast] at hne ⊢
    dsimp only [] at hne ⊢
    by_cases hviol : f = 2 ∧ ¬(N + C1 ≤ P + bn)
    · have hv : (f == 2 && !decide (N + C1 ≤ P + bn)) = true := by simp [hviol.1, hviol.2]
      simp only [hv, ↓reduceIte, Array.size_empty, ne_eq, not_true_eq_false] at hne
    · have hv : (f == 2 && !decide (N + C1 ≤ P + bn)) = false := by
        by_cases hf2 : f = 2
        · have hle : N + C1 ≤ P + bn := Classical.byContradiction (fun h => hviol ⟨hf2, h⟩)
          simp [hf2, hle]
        · simp [hf2]
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at hne ⊢
      have h16k1 : 16 ^ k = 16 ^ (k - 1) * 16 := by
        calc 16 ^ k = 16 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 16 ^ (k - 1) * 16 := Nat.pow_succ _ _
      let sh1 : UInt64 := (4 * (k - 1)).toUInt64
      let sh2 : UInt64 := (4 * (k - 2)).toUInt64
      let sh3 : UInt64 := (4 * (k - 3)).toUInt64
      have hs1 : sh1.toNat = 4 * (k - 1) := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hs2 : sh2.toNat = 4 * (k - 2) := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have hs3 : sh3.toNat = 4 * (k - 3) := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have ha_eq : (y >>> sh1).toNat = y.toNat / 16 ^ (k - 1) := by
        rw [ui64_shift_right_toNat y sh1 (by omega), hs1, pow2_4n]
      have ha_lt : (y >>> sh1).toNat < 16 := by
        rw [ha_eq, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← h16k1]; exact hy
      have hb_eq : ((y >>> sh2) &&& 0xF).toNat = (y.toNat / 16 ^ (k - 2)) % 16 := by
        rw [UInt64.toNat_and, ui64_shift_right_toNat y sh2 (by omega), hs2, pow2_4n]
        exact Nat.and_two_pow_sub_one_eq_mod _ 4
      have hb_lt : ((y >>> sh2) &&& 0xF).toNat < 16 := by rw [hb_eq]; exact Nat.mod_lt _ (by decide)
      have hc_eq : ((y >>> sh3) &&& 0xF).toNat = (y.toNat / 16 ^ (k - 3)) % 16 := by
        rw [UInt64.toNat_and, ui64_shift_right_toNat y sh3 (by omega), hs3, pow2_4n]
        exact Nat.and_two_pow_sub_one_eq_mod _ 4
      have hc_lt : ((y >>> sh3) &&& 0xF).toNat < 16 := by rw [hc_eq]; exact Nat.mod_lt _ (by decide)
      let base := (y &&& (((1 : UInt64) <<< sh3) - 1)) <<< 12
      let a := y >>> sh1
      let b := (y >>> sh2) &&& 0xF
      let c := (y >>> sh3) &&& 0xF
      obtain ⟨hd0_eq, hd0_lt⟩ := child_code_eq (by omega) hk15 hy ha_lt hb_lt hc_lt
      obtain ⟨hd1_eq, hd1_lt⟩ := child_code_eq (by omega) hk15 hy ha_lt hc_lt hb_lt
      obtain ⟨hd2_eq, hd2_lt⟩ := child_code_eq (by omega) hk15 hy hb_lt ha_lt hc_lt
      obtain ⟨hd3_eq, hd3_lt⟩ := child_code_eq (by omega) hk15 hy hb_lt hc_lt ha_lt
      obtain ⟨hd4_eq, hd4_lt⟩ := child_code_eq (by omega) hk15 hy hc_lt ha_lt hb_lt
      obtain ⟨hd5_eq, hd5_lt⟩ := child_code_eq (by omega) hk15 hy hc_lt hb_lt ha_lt
      generalize ht0 : walkFast k (k.toUInt64 * 0x1111111111111111) sh1 sh2 sh3 (((1 : UInt64) <<< sh2) - 1) (((1 : UInt64) <<< sh3) - 1) A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (a <<< 8) ||| (b <<< 4) ||| c) tab = t0 at hne ⊢
      by_cases h0 : t0.size = 0
      · simp only [h0, beq_self_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at hne
      · simp only [beq_iff_eq, h0, ↓reduceIte] at hne ⊢
        generalize ht1 : walkFast k (k.toUInt64 * 0x1111111111111111) sh1 sh2 sh3 (((1 : UInt64) <<< sh2) - 1) (((1 : UInt64) <<< sh3) - 1) A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (a <<< 8) ||| (c <<< 4) ||| b) t0 = t1 at hne ⊢
        by_cases h1 : t1.size = 0
        · simp only [h1, ↓reduceIte, ne_eq, not_true_eq_false] at hne
        · simp only [h1, ↓reduceIte] at hne ⊢
          generalize ht2 : walkFast k (k.toUInt64 * 0x1111111111111111) sh1 sh2 sh3 (((1 : UInt64) <<< sh2) - 1) (((1 : UInt64) <<< sh3) - 1) A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (b <<< 8) ||| (a <<< 4) ||| c) t1 = t2 at hne ⊢
          by_cases h2 : t2.size = 0
          · simp only [h2, ↓reduceIte, ne_eq, not_true_eq_false] at hne
          · simp only [h2, ↓reduceIte] at hne ⊢
            generalize ht3 : walkFast k (k.toUInt64 * 0x1111111111111111) sh1 sh2 sh3 (((1 : UInt64) <<< sh2) - 1) (((1 : UInt64) <<< sh3) - 1) A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (b <<< 8) ||| (c <<< 4) ||| a) t2 = t3 at hne ⊢
            by_cases h3 : t3.size = 0
            · simp only [h3, ↓reduceIte, ne_eq, not_true_eq_false] at hne
            · simp only [h3, ↓reduceIte] at hne ⊢
              generalize ht4 : walkFast k (k.toUInt64 * 0x1111111111111111) sh1 sh2 sh3 (((1 : UInt64) <<< sh2) - 1) (((1 : UInt64) <<< sh3) - 1) A q2 C1 C2 bn fuel P N f (k - 1) (base ||| (c <<< 8) ||| (a <<< 4) ||| b) t3 = t4 at hne ⊢
              by_cases h4 : t4.size = 0
              · simp only [h4, ↓reduceIte, ne_eq, not_true_eq_false] at hne
              · simp only [h4, ↓reduceIte] at hne ⊢
                obtain ⟨et0, _⟩ := ih_walk (k - 1) _ P N f tab T [] hd0_lt hsub (by simp) (ht0 ▸ h0)
                have et0' : t0 = tab := ht0.symm.trans et0
                have hsub0 : HTSub t0 T := et0' ▸ hsub
                obtain ⟨et1, _⟩ := ih_walk (k - 1) _ P N f t0 T [] hd1_lt hsub0 (by simp) (ht1 ▸ h1)
                have et1' : t1 = t0 := ht1.symm.trans et1
                have hsub1 : HTSub t1 T := et1' ▸ hsub0
                obtain ⟨et2, _⟩ := ih_walk (k - 1) _ P N f t1 T [] hd2_lt hsub1 (by simp) (ht2 ▸ h2)
                have et2' : t2 = t1 := ht2.symm.trans et2
                have hsub2 : HTSub t2 T := et2' ▸ hsub1
                obtain ⟨et3, _⟩ := ih_walk (k - 1) _ P N f t2 T [] hd3_lt hsub2 (by simp) (ht3 ▸ h3)
                have et3' : t3 = t2 := ht3.symm.trans et3
                have hsub3 : HTSub t3 T := et3' ▸ hsub2
                obtain ⟨et4, _⟩ := ih_walk (k - 1) _ P N f t3 T [] hd4_lt hsub3 (by simp) (ht4 ▸ h4)
                have et4' : t4 = t3 := ht4.symm.trans et4
                have hsub4 : HTSub t4 T := et4' ▸ hsub3
                obtain ⟨et5, hw5⟩ := ih_walk (k - 1) _ P N f t4 T [] hd5_lt hsub4 (by simp) hne
                obtain ⟨_, hw4⟩ := ih_walk (k - 1) _ P N f t3 T _ hd4_lt hsub3 hw5 (ht4 ▸ h4)
                obtain ⟨_, hw3⟩ := ih_walk (k - 1) _ P N f t2 T _ hd3_lt hsub2 hw4 (ht3 ▸ h3)
                obtain ⟨_, hw2⟩ := ih_walk (k - 1) _ P N f t1 T _ hd2_lt hsub1 hw3 (ht2 ▸ h2)
                obtain ⟨_, hw1⟩ := ih_walk (k - 1) _ P N f t0 T _ hd1_lt hsub0 hw2 (ht1 ▸ h1)
                obtain ⟨_, hw0⟩ := ih_walk (k - 1) _ P N f tab T _ hd0_lt hsub hw1 (ht0 ▸ h0)
                refine ⟨by rw [et5, et4', et3', et2', et1', et0'], ?_⟩
                rw [goK_succ]
                have hviol_f : viol C1 bn ⟨y.toNat, T, P, N, f⟩ = false := by
                  rw [viol_eq]
                  by_cases hf2 : f = 2
                  · have hle : N + C1 ≤ P + bn := Classical.byContradiction (fun h => hviol ⟨hf2, h⟩)
                    simp [hf2, Nat.ble_eq.mpr hle]
                  · simp [hf2]
                rw [hviol_f]
                simp only [Bool.cond_false]
                rw [anyIdx_goK_false_iff]
                unfold children six pw
                have e0 : (base ||| (a <<< 8) ||| (b <<< 4) ||| c).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1))) 256)
                        (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16) 16))
                        (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16)) := by
                  rw [hd0_eq, ha_eq, hb_eq, hc_eq]; rfl
                have e1 : (base ||| (a <<< 8) ||| (c <<< 4) ||| b).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1))) 256)
                        (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16) 16))
                        (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16)) := by
                  rw [hd1_eq, ha_eq, hb_eq, hc_eq]; rfl
                have e2 : (base ||| (b <<< 8) ||| (a <<< 4) ||| c).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16) 256)
                        (Nat.mul (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1))) 16))
                        (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16)) := by
                  rw [hd2_eq, ha_eq, hb_eq, hc_eq]; rfl
                have e3 : (base ||| (b <<< 8) ||| (c <<< 4) ||| a).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16) 256)
                        (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16) 16))
                        (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1)))) := by
                  rw [hd3_eq, ha_eq, hb_eq, hc_eq]; rfl
                have e4 : (base ||| (c <<< 8) ||| (a <<< 4) ||| b).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16) 256)
                        (Nat.mul (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1))) 16))
                        (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16)) := by
                  rw [hd4_eq, ha_eq, hb_eq, hc_eq]; rfl
                have e5 : (base ||| (c <<< 8) ||| (b <<< 4) ||| a).toNat =
                    Nat.add (Nat.mul (Nat.mod y.toNat (Nat.pow 16 (Nat.sub k 3))) 4096)
                      (Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 3))) 16) 256)
                        (Nat.mul (Nat.mod (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 2))) 16) 16))
                        (Nat.div y.toNat (Nat.pow 16 (Nat.sub k 1)))) := by
                  rw [hd5_eq, ha_eq, hb_eq, hc_eq]; rfl
                rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5]
                exact hw0

/-- Main kernel-checked soundness theorem: if `searchFast` returns `false`, then `S.search` returns `false`. -/
theorem searchFast_sound {k A q2 C1 C2 bn fuel : Nat} (hk5 : 5 ≤ k) (hk15 : k ≤ 15)
    (h : searchFast k A q2 C1 C2 bn fuel = false) :
    search k A q2 C1 C2 bn fuel = false := by
  unfold searchFast at h
  simp only [beq_eq_false_iff_ne] at h
  obtain ⟨hid_eq, hid_lt⟩ := idcU_eq hk15
  have hwalk := walkFast_step_of_go hk5 hk15 A q2 C1 C2 bn fuel (goFast_sound hk5 hk15 A q2 C1 C2 bn fuel)
  obtain ⟨_, hall⟩ := hwalk (k - 1) (idcU k) 0 0 1 (Array.replicate HT_SIZE 0) Tr.leaf [] hid_lt htsub_empty (by simp) h
  unfold search rootChildren
  rw [anyIdx_goK_false_iff, ← hid_eq]
  exact hall

end S
end SuperpermLowerBounds
