import AsymptoticZero.SliceModel
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# Lemma 1: Universal Low-Slope Walk Family `W_{6m} = (F^{6m-3} S)^{4m}`

For every `m ≥ 1`, let `b = 6 * m`. We construct the periodic walk `W_{6m}` on `Fin b`:
* `W6mState m k r = FStep^[r] (P_b^[k] id_b)` (`k < 4 * m`, `r < b - 2`),
* `P_b = SStep ∘ FStep^[b - 3]` has order `4 * m` (2 disjoint cycles of lengths `4m` and `2m`),
* `Nat.gcd (6 * m - 1) (4 * m * (6 * m - 4)) = 1` (`tr(W_{6m}) = 1`),
* **100% loop-disjointness**: `W6mState m k1 r1 ~r W6mState m k2 r2 → k1 = k2 ∧ r1 = r2`,
* Packages `selW6m m hm : PureSelection (6 * m)` with `4 * m` `'S'`-rows,
  `4 * m * (6 * m - 3)` `'F'`-rows, and `(6 * m - 1)! - 4 * m * (6 * m - 2)` `'D'`-loops.
-/

namespace AsymptoticZero

/-! ### 1. List realization of `Equiv.Perm (Fin b)` and right-action of `FStep`, `SStep` -/

/-- Convert a permutation `σ : Equiv.Perm (Fin b)` to its list of values `[σ 0, σ 1, ..., σ (b - 1)]`. -/
def permList {b : Nat} (σ : Equiv.Perm (Fin b)) : List (Fin b) :=
  (List.finRange b).map σ

theorem permList_length {b : Nat} (σ : Equiv.Perm (Fin b)) : (permList σ).length = b := by
  simp [permList]

theorem permList_isPerm {b : Nat} (σ : Equiv.Perm (Fin b)) : IsPerm b (permList σ) :=
  ⟨(List.nodup_finRange b).map σ.injective, permList_length σ⟩

theorem permList_getElem {b : Nat} (σ : Equiv.Perm (Fin b)) {i : Nat} (hi : i < b) :
    (permList σ)[i]'(by rw [permList_length]; exact hi) = σ ⟨i, hi⟩ := by
  simp [permList]

theorem permList_map {b : Nat} (τ σ : Equiv.Perm (Fin b)) :
    (permList σ).map τ = permList (τ * σ) := by
  simp [permList, List.map_map, Equiv.Perm.mul_def, Function.comp_def]

/-- Position permutation for `FStep` on `Fin b` (`b ≥ 3`):
`i ↦ (i + 1) % (b - 1)` for `i < b - 1`, and `b - 1 ↦ b - 1`. -/
def fIdxFn (b : Nat) (hb : 3 ≤ b) (i : Fin b) : Fin b :=
  if h : i.1 < b - 1 then ⟨(i.1 + 1) % (b - 1), by
    have := Nat.mod_lt (i.1 + 1) (by omega : 0 < b - 1); omega⟩
  else ⟨b - 1, by omega⟩

def fIdxInvFn (b : Nat) (hb : 3 ≤ b) (i : Fin b) : Fin b :=
  if h : i.1 < b - 1 then ⟨(i.1 + (b - 2)) % (b - 1), by
    have := Nat.mod_lt (i.1 + (b - 2)) (by omega : 0 < b - 1); omega⟩
  else ⟨b - 1, by omega⟩

def fIdx (b : Nat) (hb : 3 ≤ b) : Equiv.Perm (Fin b) where
  toFun := fIdxFn b hb
  invFun := fIdxInvFn b hb
  left_inv := by
    intro i; apply Fin.ext; dsimp [fIdxFn, fIdxInvFn]
    by_cases h : i.1 < b - 1
    · have hmod : (i.1 + 1) % (b - 1) < b - 1 := Nat.mod_lt _ (by omega)
      simp only [h, hmod, ↓reduceDIte]
      have h1 : ((i.1 + 1) % (b - 1) + (b - 2)) % (b - 1) = (i.1 + 1 + (b - 2)) % (b - 1) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1]
      have h2 : i.1 + 1 + (b - 2) = i.1 + (b - 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h]
    · have hni : ¬(b - 1 < b - 1) := by omega
      simp only [h, hni, ↓reduceDIte]; omega
  right_inv := by
    intro i; apply Fin.ext; dsimp [fIdxFn, fIdxInvFn]
    by_cases h : i.1 < b - 1
    · have hmod : (i.1 + (b - 2)) % (b - 1) < b - 1 := Nat.mod_lt _ (by omega)
      simp only [h, hmod, ↓reduceDIte]
      have h1 : ((i.1 + (b - 2)) % (b - 1) + 1) % (b - 1) = (i.1 + (b - 2) + 1) % (b - 1) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1]
      have h2 : i.1 + (b - 2) + 1 = i.1 + (b - 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt h]
    · have hni : ¬(b - 1 < b - 1) := by omega
      simp only [h, hni, ↓reduceDIte]; omega

theorem fIdx_pow_apply (b : Nat) (hb : 3 ≤ b) (r : Nat) (i : Fin b) :
    ((fIdx b hb) ^ r) i =
      if h : i.1 < b - 1 then ⟨(i.1 + r) % (b - 1), by
        have := Nat.mod_lt (i.1 + r) (by omega : 0 < b - 1); omega⟩
      else ⟨b - 1, by omega⟩ := by
  induction r with
  | zero =>
    apply Fin.ext; simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
    by_cases h : i.1 < b - 1
    · simp only [h, ↓reduceDIte, Nat.add_zero, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceDIte]; omega
  | succ r ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    apply Fin.ext
    by_cases h : i.1 < b - 1
    · have hmod : (i.1 + r) % (b - 1) < b - 1 := Nat.mod_lt _ (by omega)
      simp only [h, ↓reduceDIte]
      change (fIdxFn b hb ⟨(i.1 + r) % (b - 1), _⟩).1 = _
      simp only [fIdxFn, hmod, ↓reduceDIte]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    · simp only [h, ↓reduceDIte]
      change (fIdxFn b hb ⟨b - 1, _⟩).1 = b - 1
      have hni : ¬(b - 1 < b - 1) := by omega
      simp only [fIdxFn, hni, ↓reduceDIte]

/-- Position permutation for `SStep` on `Fin b` (`b ≥ 4`):
`0 ↦ b - 1`, `1 ≤ i ≤ b - 3 ↦ i - 1`, `b - 2 ↦ b - 2`, `b - 1 ↦ b - 3`. -/
def sIdxVal (b i : Nat) : Nat :=
  if i = 0 then b - 1
  else if i ≤ b - 3 then i - 1
  else if i = b - 2 then b - 2
  else b - 3

def sIdxInvVal (b i : Nat) : Nat :=
  if i = b - 1 then 0
  else if i < b - 3 then i + 1
  else if i = b - 2 then b - 2
  else b - 1

theorem sIdxVal_lt (b : Nat) (hb : 4 ≤ b) (i : Nat) (hi : i < b) : sIdxVal b i < b := by
  dsimp [sIdxVal]; split_ifs <;> omega

theorem sIdxInvVal_lt (b : Nat) (hb : 4 ≤ b) (i : Nat) (hi : i < b) : sIdxInvVal b i < b := by
  dsimp [sIdxInvVal]; split_ifs <;> omega

def sIdx (b : Nat) (hb : 4 ≤ b) : Equiv.Perm (Fin b) where
  toFun := fun i => ⟨sIdxVal b i.1, sIdxVal_lt b hb i.1 i.2⟩
  invFun := fun i => ⟨sIdxInvVal b i.1, sIdxInvVal_lt b hb i.1 i.2⟩
  left_inv := by
    intro i; apply Fin.ext; have hi := i.2
    change sIdxInvVal b (sIdxVal b i.1) = i.1
    dsimp [sIdxVal, sIdxInvVal]
    by_cases h0 : i.1 = 0
    · simp [h0]
    · by_cases h1 : i.1 ≤ b - 3
      · simp only [h0, h1, ↓reduceIte]; split_ifs <;> omega
      · by_cases h2 : i.1 = b - 2
        · simp only [h0, h1, h2, ↓reduceIte]; split_ifs <;> omega
        · simp only [h0, h1, h2, ↓reduceIte]; split_ifs <;> omega
  right_inv := by
    intro i; apply Fin.ext; have hi := i.2
    change sIdxVal b (sIdxInvVal b i.1) = i.1
    dsimp [sIdxVal, sIdxInvVal]
    by_cases h1 : i.1 = b - 1
    · simp [h1]
    · by_cases h2 : i.1 < b - 3
      · simp only [h1, h2, ↓reduceIte]
        have ha : i.1 + 1 ≠ 0 := by omega
        have hb' : i.1 + 1 ≤ b - 3 := by omega
        simp only [ha, hb', ↓reduceIte]; omega
      · by_cases h3 : i.1 = b - 2
        · simp only [h1, h2, h3, ↓reduceIte]; split_ifs <;> omega
        · simp only [h1, h2, h3, ↓reduceIte]; split_ifs <;> omega

theorem FStep_permList {b : Nat} (hb : 3 ≤ b) (σ : Equiv.Perm (Fin b)) :
    FStep (permList σ) = permList (σ * fIdx b hb) := by
  have hF : FStep (permList σ) = ((permList σ).take (b - 1)).rotate 1 ++ (permList σ).drop (b - 1) := by
    simp [FStep, permList_length]
  rw [hF]
  have htake_len : ((permList σ).take (b - 1)).length = b - 1 := by
    rw [List.length_take, permList_length]; omega
  refine List.ext_getElem (by simp [permList_length]) fun i hi1 hi2 => ?_
  have hi : i < b := by rw [permList_length] at hi2; exact hi2
  rw [permList_getElem (σ * fIdx b hb) hi, Equiv.Perm.mul_apply]
  by_cases hlt : i < b - 1
  · rw [List.getElem_append_left (by rw [List.length_rotate, htake_len]; exact hlt),
      List.getElem_rotate]
    simp only [htake_len, List.getElem_take]
    rw [permList_getElem σ (by have := Nat.mod_lt (i + 1) (by omega : 0 < b - 1); omega)]
    congr 1; apply Fin.ext; simp [fIdx, fIdxFn, hlt]
  · have hi_eq : i = b - 1 := by omega
    rw [List.getElem_append_right (by rw [List.length_rotate, htake_len]; omega)]
    simp only [List.length_rotate, htake_len, List.getElem_drop]
    have hidx : b - 1 + (i - (b - 1)) = b - 1 := by omega
    simp only [hidx]
    rw [permList_getElem σ (by omega)]
    congr 1; apply Fin.ext; simp [fIdx, fIdxFn, hlt]

theorem SStep_permList {b : Nat} (hb : 4 ≤ b) (σ : Equiv.Perm (Fin b)) :
    SStep (permList σ) = permList (σ * sIdx b hb) := by
  have hS : SStep (permList σ) =
      (permList σ).drop (b - 1) ++ (permList σ).take (b - 3) ++ (((permList σ).drop (b - 3)).take 2).reverse := by
    simp [SStep, permList_length]
  rw [hS]
  have hd1 : ((permList σ).drop (b - 1)).length = 1 := by rw [List.length_drop, permList_length]; omega
  have ht3 : ((permList σ).take (b - 3)).length = b - 3 := by rw [List.length_take, permList_length]; omega
  have hrev : (((permList σ).drop (b - 3)).take 2).length = 2 := by
    rw [List.length_take, List.length_drop, permList_length]; omega
  refine List.ext_getElem (by simp [permList_length]; omega) fun i hi1 hi2 => ?_
  have hi : i < b := by rw [permList_length] at hi2; exact hi2
  rw [permList_getElem (σ * sIdx b hb) hi, Equiv.Perm.mul_apply]
  by_cases h0 : i = 0
  · subst h0
    rw [List.getElem_append_left (by simp [hd1, ht3]),
      List.getElem_append_left (by omega), List.getElem_drop]
    simp only [Nat.add_zero]
    rw [permList_getElem σ (by omega)]
    rfl
  · by_cases hmid : i ≤ b - 3
    · rw [List.getElem_append_left (by simp [hd1, ht3]; omega),
        List.getElem_append_right (by omega)]
      simp only [hd1, List.getElem_take]
      rw [permList_getElem σ (by omega)]
      congr 1; apply Fin.ext; simp [sIdx, sIdxVal, h0, hmid]
    · rw [List.getElem_append_right (by simp [hd1, ht3]; omega)]
      simp only [List.length_append, hd1, ht3, List.getElem_reverse, hrev, List.getElem_take,
        List.getElem_drop]
      rw [permList_getElem σ (by omega)]
      congr 1; apply Fin.ext
      change b - 3 + (2 - 1 - (i - (1 + (b - 3)))) = sIdxVal b i
      dsimp [sIdxVal]; split_ifs <;> omega

theorem FStep_iter_permList {b : Nat} (hb : 3 ≤ b) (r : Nat) (σ : Equiv.Perm (Fin b)) :
    FStep^[r] (permList σ) = permList (σ * (fIdx b hb) ^ r) := by
  induction r generalizing σ with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, FStep_permList hb, ih, pow_succ', mul_assoc]

/-! ### 2. Macro-step permutation `pIdx m` on `Fin (6 * m)`, cycle decomposition, and order `4m` -/

/-- Macro-step `P_b = SStep ∘ FStep^[b - 3]` as a position permutation `fIdx^(b-3) * sIdx`. -/
def pIdx (m : Nat) (hm : 1 ≤ m) : Equiv.Perm (Fin (6 * m)) :=
  (fIdx (6 * m) (by omega)) ^ (6 * m - 3) * sIdx (6 * m) (by omega)

theorem PStep_permList (m : Nat) (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (6 * m))) :
    SStep (FStep^[6 * m - 3] (permList σ)) = permList (σ * pIdx m hm) := by
  rw [FStep_iter_permList (by omega), SStep_permList (by omega), pIdx, mul_assoc]

/-- Exact formula for `pIdx m hm i`. -/
theorem pIdx_apply (m : Nat) (hm : 1 ≤ m) (i : Fin (6 * m)) :
    (pIdx m hm i).1 =
      if i.1 = 0 then 6 * m - 1
      else if i.1 = 1 then 6 * m - 3
      else if i.1 = 2 then 6 * m - 2
      else if i.1 ≤ 6 * m - 3 then i.1 - 3
      else if i.1 = 6 * m - 2 then 6 * m - 4
      else 6 * m - 5 := by
  rw [pIdx, Equiv.Perm.mul_apply, fIdx_pow_apply]
  set s : Fin (6 * m) := sIdx (6 * m) (by omega) i
  have hs_val : s.1 = sIdxVal (6 * m) i.1 := rfl
  by_cases h0 : i.1 = 0
  · have hs0 : s.1 = 6 * m - 1 := by rw [hs_val]; dsimp [sIdxVal]; simp [h0]
    have hni : ¬(s.1 < 6 * m - 1) := by omega
    simp only [hni, ↓reduceDIte, h0, ↓reduceIte]
  · have hlt : s.1 < 6 * m - 1 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
    simp only [hlt, ↓reduceDIte]
    by_cases h1 : i.1 = 1
    · have hs1 : s.1 = 0 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
      rw [hs1, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 6 * m - 3 < 6 * m - 1)]
      split_ifs <;> omega
    · by_cases h2 : i.1 = 2
      · have hs2 : s.1 = 1 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
        rw [hs2]
        have heq : 1 + (6 * m - 3) = 6 * m - 2 := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
        split_ifs <;> omega
      · by_cases hmid : i.1 ≤ 6 * m - 3
        · have hsm : s.1 = i.1 - 1 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
          rw [hsm]
          have heq : i.1 - 1 + (6 * m - 3) = (i.1 - 3) + (6 * m - 1) := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          split_ifs <;> omega
        · by_cases hm2 : i.1 = 6 * m - 2
          · have hsm2 : s.1 = 6 * m - 2 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
            rw [hsm2]
            have heq : 6 * m - 2 + (6 * m - 3) = (6 * m - 4) + (6 * m - 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            split_ifs <;> omega
          · have hm1 : i.1 = 6 * m - 1 := by omega
            have hsm1 : s.1 = 6 * m - 3 := by rw [hs_val]; dsimp [sIdxVal]; split_ifs <;> omega
            rw [hsm1]
            have heq : 6 * m - 3 + (6 * m - 3) = (6 * m - 5) + (6 * m - 1) := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            split_ifs <;> omega

/-- Value of the `4m`-cycle of `pIdx m hm`. -/
def cyc1Val (m t : Nat) : Nat :=
  let u := t % (4 * m)
  if u = 0 then 0
  else if u = 1 then 6 * m - 1
  else if u ≤ 2 * m then 6 * m - 3 * u + 1
  else 12 * m - 3 * u

theorem cyc1Val_lt (m : Nat) (hm : 1 ≤ m) (t : Nat) : cyc1Val m t < 6 * m := by
  dsimp [cyc1Val]
  have := Nat.mod_lt t (by omega : 0 < 4 * m)
  split_ifs <;> omega

/-- The `4m`-cycle of `pIdx m hm`. -/
def cyc1 (m : Nat) (hm : 1 ≤ m) (t : Nat) : Fin (6 * m) :=
  ⟨cyc1Val m t, cyc1Val_lt m hm t⟩

/-- Value of the `2m`-cycle of `pIdx m hm`. -/
def cyc2Val (m t : Nat) : Nat :=
  let u := t % (2 * m)
  if u = 0 then 2
  else if u = 1 then 6 * m - 2
  else 6 * m - 3 * u + 2

theorem cyc2Val_lt (m : Nat) (hm : 1 ≤ m) (t : Nat) : cyc2Val m t < 6 * m := by
  dsimp [cyc2Val]
  have := Nat.mod_lt t (by omega : 0 < 2 * m)
  split_ifs <;> omega

/-- The `2m`-cycle of `pIdx m hm`. -/
def cyc2 (m : Nat) (hm : 1 ≤ m) (t : Nat) : Fin (6 * m) :=
  ⟨cyc2Val m t, cyc2Val_lt m hm t⟩

theorem pIdx_cyc1 (m : Nat) (hm : 1 ≤ m) (t : Nat) :
    pIdx m hm (cyc1 m hm t) = cyc1 m hm (t + 1) := by
  apply Fin.ext
  rw [pIdx_apply]
  have hval1 : (cyc1 m hm t).1 = cyc1Val m t := rfl
  have hval2 : (cyc1 m hm (t + 1)).1 = cyc1Val m (t + 1) := rfl
  rw [hval1, hval2]
  generalize hu_eq : t % (4 * m) = u
  have hmod_lt : u < 4 * m := hu_eq ▸ Nat.mod_lt t (by omega)
  have hnext : (t + 1) % (4 * m) = if u + 1 = 4 * m then 0 else u + 1 := by
    by_cases h : u + 1 = 4 * m
    · simp only [h, ↓reduceIte]
      rw [Nat.add_mod, hu_eq, Nat.mod_eq_of_lt (by omega : 1 < 4 * m), h, Nat.mod_self]
    · simp only [h, ↓reduceIte]
      rw [Nat.add_mod, hu_eq, Nat.mod_eq_of_lt (by omega : 1 < 4 * m), Nat.mod_eq_of_lt (by omega)]
  have hc1_eq : cyc1Val m t =
      if u = 0 then 0 else if u = 1 then 6 * m - 1 else if u ≤ 2 * m then 6 * m - 3 * u + 1 else 12 * m - 3 * u := by
    dsimp [cyc1Val]; rw [hu_eq]
  have hc2_eq : ∀ v, (t + 1) % (4 * m) = v → cyc1Val m (t + 1) =
      if v = 0 then 0 else if v = 1 then 6 * m - 1 else if v ≤ 2 * m then 6 * m - 3 * v + 1 else 12 * m - 3 * v := by
    intro v hv; dsimp [cyc1Val]; rw [hv]
  by_cases hu0 : u = 0
  · have hc1 : cyc1Val m t = 0 := by rw [hc1_eq]; simp [hu0]
    have hc2 : cyc1Val m (t + 1) = 6 * m - 1 := by
      rw [hc2_eq (u + 1) (by rw [hnext]; simp [hu0, show 0 + 1 ≠ 4 * m by omega])]
      simp [hu0]
    rw [hc1, hc2]; simp
  · by_cases hu1 : u = 1
    · have hc1 : cyc1Val m t = 6 * m - 1 := by rw [hc1_eq]; simp [hu1]
      have hc2 : cyc1Val m (t + 1) = 6 * m - 5 := by
        rw [hc2_eq (u + 1) (by rw [hnext]; simp [hu1, show 1 + 1 ≠ 4 * m by omega])]
        simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, show u + 1 ≤ 2 * m by omega, ↓reduceIte]; omega
      rw [hc1, hc2]
      simp only [show 6 * m - 1 ≠ 0 by omega, show 6 * m - 1 ≠ 1 by omega,
        show 6 * m - 1 ≠ 2 by omega, show ¬(6 * m - 1 ≤ 6 * m - 3) by omega,
        show 6 * m - 1 ≠ 6 * m - 2 by omega, ↓reduceIte]
    · by_cases hu2 : u ≤ 2 * m
      · by_cases heq : u = 2 * m
        · have hc1 : cyc1Val m t = 1 := by rw [hc1_eq]; simp [hu0, hu1, hu2]; omega
          have hc2 : cyc1Val m (t + 1) = 6 * m - 3 := by
            rw [hc2_eq (u + 1) (by rw [hnext]; simp [show u + 1 ≠ 4 * m by omega])]
            simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, show ¬(u + 1 ≤ 2 * m) by omega, ↓reduceIte]; omega
          rw [hc1, hc2]; simp
        · have hc1 : cyc1Val m t = 6 * m - 3 * u + 1 := by rw [hc1_eq]; simp [hu0, hu1, hu2]
          have hc2 : cyc1Val m (t + 1) = 6 * m - 3 * (u + 1) + 1 := by
            rw [hc2_eq (u + 1) (by rw [hnext]; simp [show u + 1 ≠ 4 * m by omega])]
            simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, show u + 1 ≤ 2 * m by omega, ↓reduceIte]
          rw [hc1, hc2]
          simp only [show 6 * m - 3 * u + 1 ≠ 0 by omega, show 6 * m - 3 * u + 1 ≠ 1 by omega,
            show 6 * m - 3 * u + 1 ≠ 2 by omega, show 6 * m - 3 * u + 1 ≤ 6 * m - 3 by omega, ↓reduceIte]
          omega
      · by_cases hlast : u + 1 = 4 * m
        · have hc1 : cyc1Val m t = 3 := by rw [hc1_eq]; simp [hu0, hu1, hu2]; omega
          have hc2 : cyc1Val m (t + 1) = 0 := by rw [hc2_eq 0 (by rw [hnext]; simp [hlast])]; simp
          rw [hc1, hc2]
          simp only [show (3 : Nat) ≠ 0 by omega, show (3 : Nat) ≠ 1 by omega,
            show (3 : Nat) ≠ 2 by omega, show 3 ≤ 6 * m - 3 by omega, ↓reduceIte]
        · have hc1 : cyc1Val m t = 12 * m - 3 * u := by rw [hc1_eq]; simp [hu0, hu1, hu2]
          have hc2 : cyc1Val m (t + 1) = 12 * m - 3 * (u + 1) := by
            rw [hc2_eq (u + 1) (by rw [hnext]; simp [hlast])]
            simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, show ¬(u + 1 ≤ 2 * m) by omega, ↓reduceIte]
          rw [hc1, hc2]
          simp only [show 12 * m - 3 * u ≠ 0 by omega, show 12 * m - 3 * u ≠ 1 by omega,
            show 12 * m - 3 * u ≠ 2 by omega, show 12 * m - 3 * u ≤ 6 * m - 3 by omega, ↓reduceIte]
          omega

theorem pIdx_cyc2 (m : Nat) (hm : 1 ≤ m) (t : Nat) :
    pIdx m hm (cyc2 m hm t) = cyc2 m hm (t + 1) := by
  apply Fin.ext
  rw [pIdx_apply]
  have hval1 : (cyc2 m hm t).1 = cyc2Val m t := rfl
  have hval2 : (cyc2 m hm (t + 1)).1 = cyc2Val m (t + 1) := rfl
  rw [hval1, hval2]
  generalize hu_eq : t % (2 * m) = u
  have hmod_lt : u < 2 * m := hu_eq ▸ Nat.mod_lt t (by omega)
  have hnext : (t + 1) % (2 * m) = if u + 1 = 2 * m then 0 else u + 1 := by
    by_cases h : u + 1 = 2 * m
    · simp only [h, ↓reduceIte]
      rw [Nat.add_mod, hu_eq, Nat.mod_eq_of_lt (by omega : 1 < 2 * m), h, Nat.mod_self]
    · simp only [h, ↓reduceIte]
      rw [Nat.add_mod, hu_eq, Nat.mod_eq_of_lt (by omega : 1 < 2 * m), Nat.mod_eq_of_lt (by omega)]
  have hc1_eq : cyc2Val m t =
      if u = 0 then 2 else if u = 1 then 6 * m - 2 else 6 * m - 3 * u + 2 := by
    dsimp [cyc2Val]; rw [hu_eq]
  have hc2_eq : ∀ v, (t + 1) % (2 * m) = v → cyc2Val m (t + 1) =
      if v = 0 then 2 else if v = 1 then 6 * m - 2 else 6 * m - 3 * v + 2 := by
    intro v hv; dsimp [cyc2Val]; rw [hv]
  by_cases hu0 : u = 0
  · have hc1 : cyc2Val m t = 2 := by rw [hc1_eq]; simp [hu0]
    have hc2 : cyc2Val m (t + 1) = 6 * m - 2 := by
      rw [hc2_eq (u + 1) (by rw [hnext]; simp [hu0, show 0 + 1 ≠ 2 * m by omega])]
      simp [hu0]
    rw [hc1, hc2]; simp
  · by_cases hu1 : u = 1
    · have hc1 : cyc2Val m t = 6 * m - 2 := by rw [hc1_eq]; simp [hu1]
      by_cases hm1 : m = 1
      · subst hm1
        have hc2 : cyc2Val 1 (t + 1) = 2 := by rw [hc2_eq 0 (by rw [hnext]; simp [hu1])]; simp
        rw [hc1, hc2]; simp
      · have hc2 : cyc2Val m (t + 1) = 6 * m - 4 := by
          rw [hc2_eq (u + 1) (by rw [hnext]; simp [show u + 1 ≠ 2 * m by omega])]
          simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, ↓reduceIte]; omega
        rw [hc1, hc2]
        simp only [show 6 * m - 2 ≠ 0 by omega, show 6 * m - 2 ≠ 1 by omega,
          show 6 * m - 2 ≠ 2 by omega, show ¬(6 * m - 2 ≤ 6 * m - 3) by omega, ↓reduceIte]
    · by_cases hlast : u + 1 = 2 * m
      · have hc1 : cyc2Val m t = 5 := by rw [hc1_eq]; simp [hu0, hu1]; omega
        have hc2 : cyc2Val m (t + 1) = 2 := by rw [hc2_eq 0 (by rw [hnext]; simp [hlast])]; simp
        rw [hc1, hc2]
        simp only [show (5 : Nat) ≠ 0 by omega, show (5 : Nat) ≠ 1 by omega,
          show (5 : Nat) ≠ 2 by omega, show 5 ≤ 6 * m - 3 by omega, ↓reduceIte]
      · have hc1 : cyc2Val m t = 6 * m - 3 * u + 2 := by rw [hc1_eq]; simp [hu0, hu1]
        have hc2 : cyc2Val m (t + 1) = 6 * m - 3 * (u + 1) + 2 := by
          rw [hc2_eq (u + 1) (by rw [hnext]; simp [hlast])]
          simp only [show u + 1 ≠ 0 by omega, show u + 1 ≠ 1 by omega, ↓reduceIte]
        rw [hc1, hc2]
        simp only [show 6 * m - 3 * u + 2 ≠ 0 by omega, show 6 * m - 3 * u + 2 ≠ 1 by omega,
          show 6 * m - 3 * u + 2 ≠ 2 by omega, show 6 * m - 3 * u + 2 ≤ 6 * m - 3 by omega, ↓reduceIte]
        omega

theorem pIdx_pow_cyc1 (m : Nat) (hm : 1 ≤ m) (k t : Nat) :
    ((pIdx m hm) ^ k) (cyc1 m hm t) = cyc1 m hm (t + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pIdx_cyc1, Nat.add_assoc]

theorem pIdx_pow_cyc2 (m : Nat) (hm : 1 ≤ m) (k t : Nat) :
    ((pIdx m hm) ^ k) (cyc2 m hm t) = cyc2 m hm (t + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pIdx_cyc2, Nat.add_assoc]

/-- Every element of `Fin (6 * m)` lies on either `cyc1` or `cyc2`. -/
theorem mem_cyc1_or_cyc2 (m : Nat) (hm : 1 ≤ m) (x : Fin (6 * m)) :
    (∃ t < 4 * m, cyc1 m hm t = x) ∨ (∃ t < 2 * m, cyc2 m hm t = x) := by
  have hx := x.2
  by_cases h0 : x.1 = 0
  · left; exact ⟨0, by omega, by apply Fin.ext; simp [cyc1, cyc1Val, h0]⟩
  · by_cases hm1 : x.1 = 6 * m - 1
    · left; exact ⟨1, by omega, by apply Fin.ext; simp [cyc1, cyc1Val, hm1, Nat.mod_eq_of_lt (by omega : 1 < 4 * m)]⟩
    · by_cases h2 : x.1 = 2
      · right; exact ⟨0, by omega, by apply Fin.ext; simp [cyc2, cyc2Val, h2]⟩
      · by_cases hm2 : x.1 = 6 * m - 2
        · right; exact ⟨1, by omega, by apply Fin.ext; simp [cyc2, cyc2Val, hm2, Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]⟩
        · have hr : x.1 % 3 = 0 ∨ x.1 % 3 = 1 ∨ x.1 % 3 = 2 := by omega
          rcases hr with hr0 | hr1 | hr2
          · left
            refine ⟨4 * m - x.1 / 3, by omega, ?_⟩
            apply Fin.ext; dsimp [cyc1, cyc1Val]
            rw [Nat.mod_eq_of_lt (by omega)]
            split_ifs <;> omega
          · left
            refine ⟨2 * m - (x.1 - 1) / 3, by omega, ?_⟩
            apply Fin.ext; dsimp [cyc1, cyc1Val]
            rw [Nat.mod_eq_of_lt (by omega)]
            split_ifs <;> omega
          · right
            refine ⟨2 * m - (x.1 - 2) / 3, by omega, ?_⟩
            apply Fin.ext; dsimp [cyc2, cyc2Val]
            rw [Nat.mod_eq_of_lt (by omega)]
            split_ifs <;> omega

/-- Exact closure: `(pIdx m hm) ^ (4 * m) = 1`. -/
theorem pIdx_pow_4m (m : Nat) (hm : 1 ≤ m) : (pIdx m hm) ^ (4 * m) = 1 := by
  ext x
  simp only [Equiv.Perm.coe_one, id_eq]
  rcases mem_cyc1_or_cyc2 m hm x with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩
  · rw [pIdx_pow_cyc1]
    simp only [cyc1, cyc1Val, Nat.add_mod_right]
  · rw [pIdx_pow_cyc2]
    have h4 : 4 * m = 2 * (2 * m) := by ring
    simp only [cyc2, cyc2Val, h4, Nat.add_mul_mod_self_right]

/-! ### 3. Single-trail coprimality: `gcd(6m - 1, 4m(6m - 4)) = 1` -/

theorem W6m_tr_eq_one (m : Nat) (hm : 1 ≤ m) :
    Nat.gcd (6 * m - 1) (4 * m * (6 * m - 4)) = 1 := by
  have h2 : Nat.Coprime (6 * m - 1) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have h4 : Nat.Coprime (6 * m - 1) 4 := by
    have : (4 : Nat) = 2 * 2 := rfl
    rw [this]; exact h2.mul_right h2
  have hm_cop : Nat.Coprime (6 * m - 1) m := by
    refine Nat.coprime_of_dvd fun p hp hd1 hd2 => ?_
    have h6m : p ∣ 6 * m := dvd_mul_of_dvd_right hd2 6
    have hsub : p ∣ 6 * m - (6 * m - 1) := Nat.dvd_sub h6m hd1
    have h1 : 6 * m - (6 * m - 1) = 1 := by omega
    rw [h1] at hsub
    exact hp.not_dvd_one hsub
  have h6m4 : Nat.Coprime (6 * m - 1) (6 * m - 4) := by
    have h3 : Nat.Coprime (6 * m - 1) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    refine Nat.coprime_of_dvd fun p hp hd1 hd2 => ?_
    have hsub : p ∣ (6 * m - 1) - (6 * m - 4) := Nat.dvd_sub hd1 hd2
    have h1 : (6 * m - 1) - (6 * m - 4) = 3 := by omega
    rw [h1] at hsub
    have hne := Nat.dvd_gcd hd1 hsub
    rw [h3.gcd_eq_one] at hne
    exact hp.not_dvd_one hne
  exact ((h4.mul_right hm_cop).mul_right h6m4).gcd_eq_one

/-! ### 4. 100% Loop-disjointness of `W_{6m}` via the 3-element cyclic-orientation invariant -/

/-- Three distinct elements `[a, b, c]` are NEVER cyclically rotated to `[a, c, b]`. -/
theorem not_isRotated_triple {α : Type} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ([a, b, c] ~r [a, c, b]) := by
  rintro ⟨r, hr⟩
  have hmod : [a, b, c].rotate r = [a, b, c].rotate (r % 3) := (List.rotate_mod [a, b, c] r).symm
  rw [hmod] at hr
  have hlt : r % 3 < 3 := Nat.mod_lt r (by omega)
  interval_cases (r % 3) <;> simp at hr
  · exact hbc hr.1
  · exact hab hr.1.symm
  · exact hac hr.1.symm

/-- Filtering commutes with cyclic rotation! -/
theorem isRotated_filter {α : Type} (p : α → Bool) {l1 l2 : List α} (h : l1 ~r l2) :
    l1.filter p ~r l2.filter p := by
  obtain ⟨r, rfl⟩ := h
  cases l1 with
  | nil => simp
  | cons a as =>
    rw [← List.rotate_mod]
    have hle : r % (a :: as).length ≤ (a :: as).length :=
      Nat.le_of_lt (Nat.mod_lt r (by simp))
    rw [List.rotate_eq_drop_append_take hle, List.filter_append]
    have h1 : (a :: as) = (a :: as).take (r % (a :: as).length) ++ (a :: as).drop (r % (a :: as).length) :=
      (List.take_append_drop _ _).symm
    conv_lhs => rw [h1, List.filter_append]
    exact ⟨(((a :: as).take (r % (a :: as).length)).filter p).length, List.rotate_append_length_eq _ _⟩

/-- Filtering `permList (fIdx b hb ^ r)` to `{x, y, z}` (`x < y < z < b - 1`) is `~r [x, y, z]`. -/
theorem filter_fIdx_pow_triple {b : Nat} (hb : 3 ≤ b) (r : Nat) {x y z : Fin b}
    (hxy : x.1 < y.1) (hyz : y.1 < z.1) (hz : z.1 < b - 1) :
    let P : Fin b → Bool := fun a => a == x || a == y || a == z
    (permList ((fIdx b hb) ^ r)).filter P ~r [x, y, z] := by
  intro P
  have hsplit : permList ((fIdx b hb) ^ r) =
      (((List.finRange b).take (b - 1)).rotate r) ++ [⟨b - 1, by omega⟩] := by
    refine List.ext_getElem (by simp [permList_length]; omega) fun i hi1 hi2 => ?_
    have hi : i < b := by rw [permList_length] at hi1; exact hi1
    rw [permList_getElem _ hi, fIdx_pow_apply]
    by_cases hlt : i < b - 1
    · simp only [hlt, ↓reduceDIte]
      rw [List.getElem_append_left (by simp; omega), List.getElem_rotate]
      apply Fin.ext
      simp only [List.length_take, List.length_finRange, Nat.min_eq_left (by omega : b - 1 ≤ b),
        List.getElem_take, List.getElem_finRange, Fin.val_cast]
    · have hi_eq : i = b - 1 := by omega
      simp only [hlt, ↓reduceDIte]
      rw [List.getElem_append_right (by simp; omega)]
      simp [hi_eq]
  have hP_last : P ⟨b - 1, by omega⟩ = false := by
    dsimp [P]
    have h1 : (⟨b - 1, by omega⟩ : Fin b) ≠ x := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    have h2 : (⟨b - 1, by omega⟩ : Fin b) ≠ y := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    have h3 : (⟨b - 1, by omega⟩ : Fin b) ≠ z := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    simp [h1, h2, h3]
  rw [hsplit, List.filter_append]
  simp only [List.filter_cons, hP_last, List.filter_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte]
  have hrot_filt : (((List.finRange b).take (b - 1)).rotate r).filter P ~r
      ((List.finRange b).take (b - 1)).filter P :=
    (isRotated_filter P ⟨r, rfl⟩).symm
  have hfilt_eq : ((List.finRange b).take (b - 1)).filter P = [x, y, z] := by
    have hfilt_full : (List.finRange b).filter P = [x, y, z] := by
      have hnd : ((List.finRange b).filter P).Nodup := (List.nodup_finRange b).filter P
      have hpw : ((List.finRange b).filter P).Pairwise (· < ·) := by
        refine List.Pairwise.filter P ?_
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp [Fin.lt_def, hij]
      have hmem : ∀ a : Fin b, a ∈ (List.finRange b).filter P ↔ a = x ∨ a = y ∨ a = z := by
        intro a; simp [P, List.mem_filter, List.mem_finRange, or_assoc]
      have hperm : ((List.finRange b).filter P).Perm [x, y, z] := by
        refine (List.perm_ext_iff_of_nodup hnd ?_).mpr ?_
        · simp [Fin.ext_iff]; omega
        · intro a; rw [hmem]; simp
      have hpw2 : ([x, y, z] : List (Fin b)).Pairwise (· < ·) := by
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
        exact ⟨⟨hxy, Nat.lt_trans hxy hyz⟩, hyz, fun _ h => h.elim⟩
      exact List.Perm.eq_of_pairwise' hpw hpw2 hperm
    have h1 : List.finRange b = (List.finRange b).take (b - 1) ++ [⟨b - 1, by omega⟩] := by
      refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
      by_cases hlt : i < b - 1
      · rw [List.getElem_append_left (by simp; omega)]; simp
      · have hi_eq : i = b - 1 := by simp at hi1; omega
        rw [List.getElem_append_right (by simp; omega)]; simp [hi_eq]
    rw [h1, List.filter_append] at hfilt_full
    simp only [List.filter_cons, hP_last, List.filter_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte] at hfilt_full
    exact hfilt_full
  rwa [hfilt_eq] at hrot_filt

/-- Helper: filtering a duplicate-free list `l` to `{a, b, c}` when `a, b, c` appear at `i < j < k` gives `[a, b, c]`. -/
theorem filter_triple_of_indices {α : Type} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {i j k : Nat} (hij : i < j) (hjk : j < k) (hk : k < l.length) :
    let a := l[i]'(by omega)
    let b := l[j]'(by omega)
    let c := l[k]'hk
    l.filter (fun x => x == a || x == b || x == c) = [a, b, c] := by
  intro a b c
  let P : α → Bool := fun x => x == a || x == b || x == c
  have hab : a ≠ b := fun h => by
    have := (List.Nodup.getElem_inj_iff hnd).mp h; omega
  have hac : a ≠ c := fun h => by
    have := (List.Nodup.getElem_inj_iff hnd).mp h; omega
  have hbc : b ≠ c := fun h => by
    have := (List.Nodup.getElem_inj_iff hnd).mp h; omega
  -- Split `l` at `i`, `j`, `k` using `take`/`drop`
  have hsplit : l = l.take i ++ [a] ++ (l.drop (i + 1)).take (j - i - 1) ++ [b] ++
      (l.drop (j + 1)).take (k - j - 1) ++ [c] ++ l.drop (k + 1) := by
    have h1 : l = l.take i ++ a :: l.drop (i + 1) := by
      have := List.take_append_getElem (l := l) (i := i) (by omega)
      have h2 := List.take_append_drop (i + 1) l
      rw [← h2, List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp [a]
    have h2 : l.drop (i + 1) = (l.drop (i + 1)).take (j - i - 1) ++ b :: l.drop (j + 1) := by
      have hlen : j - i - 1 < (l.drop (i + 1)).length := by simp; omega
      have hget : (l.drop (i + 1))[j - i - 1]'hlen = b := by
        simp only [List.getElem_drop, b]; congr 1; omega
      have hsub := List.take_append_drop (j - i - 1 + 1) (l.drop (i + 1))
      rw [List.take_succ, List.getElem?_eq_getElem hlen, hget, List.drop_drop] at hsub
      have hidx : i + 1 + (j - i - 1 + 1) = j + 1 := by omega
      rw [hidx] at hsub
      simpa [List.append_assoc] using hsub.symm
    have h3 : l.drop (j + 1) = (l.drop (j + 1)).take (k - j - 1) ++ c :: l.drop (k + 1) := by
      have hlen : k - j - 1 < (l.drop (j + 1)).length := by simp; omega
      have hget : (l.drop (j + 1))[k - j - 1]'hlen = c := by
        simp only [List.getElem_drop, c]; congr 1; omega
      have hsub := List.take_append_drop (k - j - 1 + 1) (l.drop (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem hlen, hget, List.drop_drop] at hsub
      have hidx : j + 1 + (k - j - 1 + 1) = k + 1 := by omega
      rw [hidx] at hsub
      simpa [List.append_assoc] using hsub.symm
    conv_lhs => rw [h1, h2, h3]
    simp [List.append_assoc]
  have hfilt_nil : ∀ s : List α, a ∉ s → b ∉ s → c ∉ s → s.filter P = [] := by
    intro s ha hb hc
    rw [List.filter_eq_nil_iff]
    intro x hx
    have hxa : x ≠ a := fun h => ha (h ▸ hx)
    have hxb : x ≠ b := fun h => hb (h ▸ hx)
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    simp [P, hxa, hxb, hxc]
  have hnd' := hnd
  rw [hsplit] at hnd'
  let g0 := l.take i
  let g1 := (l.drop (i + 1)).take (j - i - 1)
  let g2 := (l.drop (j + 1)).take (k - j - 1)
  let g3 := l.drop (k + 1)
  have hperm_all : (g0 ++ [a] ++ g1 ++ [b] ++ g2 ++ [c] ++ g3).Perm ([a, b, c] ++ (g0 ++ g1 ++ g2 ++ g3)) := by
    have p1 : (g0 ++ a :: (g1 ++ b :: (g2 ++ c :: g3))).Perm (a :: (g0 ++ (g1 ++ b :: (g2 ++ c :: g3)))) :=
      List.perm_middle
    have p2 : ((g0 ++ g1) ++ b :: (g2 ++ c :: g3)).Perm (b :: ((g0 ++ g1) ++ (g2 ++ c :: g3))) :=
      List.perm_middle
    have p3 : ((g0 ++ g1 ++ g2) ++ c :: g3).Perm (c :: ((g0 ++ g1 ++ g2) ++ g3)) :=
      List.perm_middle
    have h1 : g0 ++ [a] ++ g1 ++ [b] ++ g2 ++ [c] ++ g3 = g0 ++ a :: (g1 ++ b :: (g2 ++ c :: g3)) := by
      simp [List.append_assoc]
    rw [h1]
    refine p1.trans (List.Perm.cons a ?_)
    have h2 : g0 ++ (g1 ++ b :: (g2 ++ c :: g3)) = (g0 ++ g1) ++ b :: (g2 ++ c :: g3) := by
      simp [List.append_assoc]
    rw [h2]
    refine p2.trans (List.Perm.cons b ?_)
    have h3 : (g0 ++ g1) ++ (g2 ++ c :: g3) = (g0 ++ g1 ++ g2) ++ c :: g3 := by
      simp [List.append_assoc]
    rw [h3]
    exact p3.trans (List.Perm.cons c (by simp [List.append_assoc]))
  have hnd_re : ([a, b, c] ++ (g0 ++ g1 ++ g2 ++ g3)).Nodup := hperm_all.nodup_iff.mp hnd'
  have hdisj := (List.nodup_append.mp hnd_re).2.2
  have hnot : ∀ x ∈ ([a, b, c] : List α), x ∉ g0 ∧ x ∉ g1 ∧ x ∉ g2 ∧ x ∉ g3 := by
    intro x hx
    have hnot_all : x ∉ g0 ++ g1 ++ g2 ++ g3 := fun hm => hdisj x hx x hm rfl
    simp only [List.mem_append, not_or] at hnot_all
    exact ⟨hnot_all.1.1.1, hnot_all.1.1.2, hnot_all.1.2, hnot_all.2⟩
  have hna := hnot a (by simp)
  have hnb := hnot b (by simp)
  have hnc := hnot c (by simp)
  conv_lhs => rw [hsplit]
  simp only [List.filter_append]
  rw [hfilt_nil g0 hna.1 hnb.1 hnc.1, hfilt_nil g1 hna.2.1 hnb.2.1 hnc.2.1,
    hfilt_nil g2 hna.2.2.1 hnb.2.2.1 hnc.2.2.1, hfilt_nil g3 hna.2.2.2 hnb.2.2.2 hnc.2.2.2]
  simp [P]

/-- **States of `W_{6m}`:** `W6mState m hm k r = permList (pIdx^k * fIdx^r)`. -/
def W6mState (m : Nat) (hm : 1 ≤ m) (k r : Nat) : List (Fin (6 * m)) :=
  permList ((pIdx m hm) ^ k * (fIdx (6 * m) (by omega)) ^ r)

theorem W6mState_isPerm (m : Nat) (hm : 1 ≤ m) (k r : Nat) :
    IsPerm (6 * m) (W6mState m hm k r) :=
  permList_isPerm _

/-- Helper: `permList (σ * fIdx^r)` equals `((permList σ).take (b - 1)).rotate r ++ [σ (b - 1)]`. -/
theorem permList_mul_fIdx_pow {b : Nat} (hb : 3 ≤ b) (σ : Equiv.Perm (Fin b)) (r : Nat) :
    permList (σ * (fIdx b hb) ^ r) =
      ((permList σ).take (b - 1)).rotate r ++ [σ ⟨b - 1, by omega⟩] := by
  refine List.ext_getElem (by simp [permList_length]; omega) fun i hi1 hi2 => ?_
  have hi : i < b := by rw [permList_length] at hi1; exact hi1
  rw [permList_getElem _ hi, Equiv.Perm.mul_apply, fIdx_pow_apply]
  by_cases hlt : i < b - 1
  · simp only [hlt, ↓reduceDIte]
    rw [List.getElem_append_left (by simp [permList_length]; omega), List.getElem_rotate]
    simp only [List.length_take, permList_length, Nat.min_eq_left (by omega : b - 1 ≤ b),
      List.getElem_take]
    rw [permList_getElem]
  · have hi_eq : i = b - 1 := by omega
    simp only [hlt, ↓reduceDIte]
    rw [List.getElem_append_right (by simp [permList_length]; omega)]
    simp [permList_length, hi_eq]

/-- **Lemma 1 (100% Loop-Disjointness of `W_{6m}`):**
For every `m ≥ 1`, all `4m * (6m - 2)` states `W6mState m hm k r` (`k < 4m`, `r < 6m - 2`)
lie in pairwise distinct cyclic loops! -/
theorem W6m_loop_disjoint (m : Nat) (hm : 1 ≤ m) {k1 k2 r1 r2 : Nat}
    (hk1 : k1 < 4 * m) (hk2 : k2 < 4 * m) (hr1 : r1 < 6 * m - 2) (hr2 : r2 < 6 * m - 2)
    (hrot : W6mState m hm k1 r1 ~r W6mState m hm k2 r2) :
    k1 = k2 ∧ r1 = r2 := by
  let b := 6 * m
  have hb_eq : b = 6 * m := rfl
  have hb : 6 ≤ b := by omega
  have hreduced : ∀ {k a c : Nat}, k ≤ 2 * m → a < b - 2 → c < b - 2 →
      permList ((fIdx b (by omega)) ^ a) ~r permList ((pIdx m hm) ^ k * (fIdx b (by omega)) ^ c) →
      k = 0 ∧ a = c := by
    intro k a c hk ha hc hrel
    by_cases hk0 : k = 0
    · subst hk0
      simp only [pow_zero, one_mul] at hrel
      refine ⟨rfl, ?_⟩
      have hcanon_eq : ∀ r < b - 2,
          (permList ((fIdx b (by omega)) ^ r)).rotate (b - 1) =
            ⟨b - 1, by omega⟩ :: ((List.finRange b).take (b - 1)).rotate r := by
        intro r _
        have hs := permList_mul_fIdx_pow (by omega : 3 ≤ b) (1 : Equiv.Perm (Fin b)) r
        simp only [one_mul, Equiv.Perm.coe_one, id_eq] at hs
        rw [hs]
        have hlen : (((permList (1 : Equiv.Perm (Fin b))).take (b - 1)).rotate r).length = b - 1 := by
          simp [permList_length]
        have hrot_app := List.rotate_append_length_eq
          (((permList (1 : Equiv.Perm (Fin b))).take (b - 1)).rotate r) [⟨b - 1, by omega⟩]
        rw [hlen] at hrot_app
        rw [hrot_app]
        simp [permList]
      let L1 := (permList ((fIdx b (by omega)) ^ a)).rotate (b - 1)
      let L2 := (permList ((fIdx b (by omega)) ^ c)).rotate (b - 1)
      have hrot1 : permList ((fIdx b (by omega)) ^ a) ~r L1 := ⟨b - 1, rfl⟩
      have hrot2 : permList ((fIdx b (by omega)) ^ c) ~r L2 := ⟨b - 1, rfl⟩
      have hL12 : L1 ~r L2 := hrot1.symm.trans (hrel.trans hrot2)
      obtain ⟨s, hs⟩ := hL12
      have hL1_eq : L1 = ⟨b - 1, by omega⟩ :: ((List.finRange b).take (b - 1)).rotate a := hcanon_eq a ha
      have hL2_eq : L2 = ⟨b - 1, by omega⟩ :: ((List.finRange b).take (b - 1)).rotate c := hcanon_eq c hc
      have hL1_nd : L1.Nodup := List.nodup_rotate.mpr (permList_isPerm _).1
      have hL1_len : L1.length = b := by rw [List.length_rotate, permList_length]
      have hL2_len : L2.length = b := by rw [List.length_rotate, permList_length]
      have h0L1 : L1[0]'(by omega) = ⟨b - 1, by omega⟩ := by simp [hL1_eq]
      have h0L2 : (L1.rotate s)[0]'(by rw [List.length_rotate]; omega) = ⟨b - 1, by omega⟩ := by
        simp [hs, hL2_eq]
      rw [List.getElem_rotate] at h0L2
      have hs0 : (0 + s) % L1.length = 0 :=
        (List.Nodup.getElem_inj_iff hL1_nd).mp (h0L2.trans h0L1.symm)
      have hrot_s : L1.rotate s = L1 := by
        rw [← List.rotate_mod]; simp only [Nat.zero_add] at hs0; rw [hs0, List.rotate_zero]
      have hEq : L1 = L2 := hrot_s.symm.trans hs
      have h1_eq : L1[1]'(by omega) = L2[1]'(by omega) := by simp [hEq]
      have get1 : ∀ (r : Nat) (hr : r < b - 2),
          ((⟨b - 1, by omega⟩ :: ((List.finRange b).take (b - 1)).rotate r) : List (Fin b))[1]'(by simp; omega) =
            ⟨r, by omega⟩ := by
        intro r hr
        apply Fin.ext
        simp only [List.getElem_cons_succ, List.getElem_rotate, List.length_take,
          List.length_finRange, Nat.min_eq_left (by omega : b - 1 ≤ b), List.getElem_take,
          List.getElem_finRange, Fin.val_cast, Nat.zero_add, Nat.mod_eq_of_lt (by omega : r < b - 1)]
      have h1a : L1[1]'(by omega) = ⟨a, by omega⟩ := by
        have := get1 a ha
        simp only [hL1_eq]
        exact this
      have h1c : L2[1]'(by omega) = ⟨c, by omega⟩ := by
        have := get1 c hc
        simp only [hL2_eq]
        exact this
      have hv := congrArg Fin.val (h1a.symm.trans (h1_eq.trans h1c))
      exact hv
    · by_cases hk1 : k = 1
      · subst hk1
        exfalso
        let x : Fin b := ⟨b - 6, by omega⟩
        let y : Fin b := ⟨b - 5, by omega⟩
        let z : Fin b := ⟨b - 4, by omega⟩
        let P : Fin b → Bool := fun v => v == x || v == y || v == z
        have hL_filt : (permList ((fIdx b (by omega)) ^ a)).filter P ~r [x, y, z] :=
          filter_fIdx_pow_triple (by omega) a (by dsimp [x, y]; omega)
            (by dsimp [y, z]; omega) (by dsimp [z]; omega)
        have hR_filt : (permList ((pIdx m hm) ^ 1 * (fIdx b (by omega)) ^ c)).filter P = [x, z, y] := by
          simp only [pow_one]
          let L := permList (pIdx m hm * (fIdx b (by omega)) ^ c)
          have hL_nd : L.Nodup := (permList_isPerm _).1
          have hL_len : L.length = b := permList_length _
          have hi : L[b - 3 - c]'(by omega) = x := by
            rw [permList_getElem _ (by omega), Equiv.Perm.mul_apply, fIdx_pow_apply]
            have hlt : b - 3 - c < b - 1 := by omega
            simp only [hlt, ↓reduceDIte]
            apply Fin.ext; rw [pIdx_apply]
            have hmod : (b - 3 - c + c) % (b - 1) = b - 3 := by
              have : b - 3 - c + c = b - 3 := by omega
              rw [this, Nat.mod_eq_of_lt (by omega)]
            change (if (b - 3 - c + c) % (b - 1) = 0 then _ else _) = b - 6
            have hb6 : b = 6 * m := rfl
            simp only [hmod]
            split_ifs <;> omega
          have hj : L[b - 2 - c]'(by omega) = z := by
            rw [permList_getElem _ (by omega), Equiv.Perm.mul_apply, fIdx_pow_apply]
            have hlt : b - 2 - c < b - 1 := by omega
            simp only [hlt, ↓reduceDIte]
            apply Fin.ext; rw [pIdx_apply]
            have hmod : (b - 2 - c + c) % (b - 1) = b - 2 := by
              have : b - 2 - c + c = b - 2 := by omega
              rw [this, Nat.mod_eq_of_lt (by omega)]
            change (if (b - 2 - c + c) % (b - 1) = 0 then _ else _) = b - 4
            have hb6 : b = 6 * m := rfl
            simp only [hmod]
            split_ifs <;> omega
          have hk' : L[b - 1]'(by omega) = y := by
            rw [permList_getElem _ (by omega), Equiv.Perm.mul_apply, fIdx_pow_apply]
            have hni : ¬(b - 1 < b - 1) := by omega
            simp only [hni, ↓reduceDIte]
            apply Fin.ext; rw [pIdx_apply]
            dsimp only [y, b]
            split_ifs <;> omega
          have hft := filter_triple_of_indices hL_nd (i := b - 3 - c) (j := b - 2 - c)
            (k := b - 1) (by omega) (by omega) (by omega)
          dsimp only at hft
          rw [hi, hj, hk'] at hft
          have hPeq : (fun v => v == x || v == z || v == y) = P := by
            funext v; dsimp [P]; cases (v == x) <;> cases (v == y) <;> cases (v == z) <;> rfl
          rwa [hPeq] at hft
        have hrot_filt : [x, y, z] ~r [x, z, y] :=
          hL_filt.symm.trans ((isRotated_filter P hrel).trans (by rw [hR_filt]))
        exact not_isRotated_triple (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega)
          (by intro h; have := congrArg Fin.val h; dsimp [x, z] at this; omega)
          (by intro h; have := congrArg Fin.val h; dsimp [y, z] at this; omega) hrot_filt
      · exfalso
        have hk2_ge : 2 ≤ k := by omega
        let σ := (pIdx m hm) ^ k
        let y : Fin b := σ ⟨0, by omega⟩
        let x : Fin b := σ ⟨1, by omega⟩
        let z : Fin b := σ ⟨2, by omega⟩
        have h0_eq : (⟨0, by omega⟩ : Fin (6 * m)) = cyc1 m hm 0 := by apply Fin.ext; simp [cyc1, cyc1Val]
        have h1_eq : (⟨1, by omega⟩ : Fin (6 * m)) = cyc1 m hm (2 * m) := by
          apply Fin.ext; dsimp [cyc1, cyc1Val]; rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega
        have h2_eq : (⟨2, by omega⟩ : Fin (6 * m)) = cyc2 m hm 0 := by apply Fin.ext; simp [cyc2, cyc2Val]
        have hy_val : y.1 = if k = 2 * m then 1 else 6 * m - 3 * k + 1 := by
          change (((pIdx m hm) ^ k) ⟨0, by omega⟩).1 = _
          rw [h0_eq, pIdx_pow_cyc1, Nat.zero_add]
          dsimp [cyc1, cyc1Val]; rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega
        have hx_val : x.1 = if k = 2 * m then 0 else 6 * m - 3 * k := by
          change (((pIdx m hm) ^ k) ⟨1, by omega⟩).1 = _
          rw [h1_eq, pIdx_pow_cyc1]
          dsimp [cyc1, cyc1Val]
          by_cases hkm : k = 2 * m
          · subst hkm; have h4 : 2 * m + 2 * m = 4 * m := by ring
            rw [h4, Nat.mod_self]; simp
          · rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega
        have hz_val : z.1 = if k = 2 * m then 2 else 6 * m - 3 * k + 2 := by
          change (((pIdx m hm) ^ k) ⟨2, by omega⟩).1 = _
          rw [h2_eq, pIdx_pow_cyc2, Nat.zero_add]
          dsimp [cyc2, cyc2Val]
          by_cases hkm : k = 2 * m
          · subst hkm; rw [Nat.mod_self]; simp
          · rw [Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega
        have hxy : x.1 < y.1 := by rw [hx_val, hy_val]; split_ifs <;> omega
        have hyz : y.1 < z.1 := by rw [hy_val, hz_val]; split_ifs <;> omega
        have hz_lt : z.1 < b - 1 := by rw [hz_val]; split_ifs <;> omega
        let P : Fin b → Bool := fun v => v == x || v == y || v == z
        have hL_filt : (permList ((fIdx b (by omega)) ^ a)).filter P ~r [x, y, z] :=
          filter_fIdx_pow_triple (by omega) a hxy hyz hz_lt
        have hP_last : P (σ ⟨6 * m - 1, by omega⟩) = false := by
          dsimp [P]
          have h1 : σ ⟨6 * m - 1, by omega⟩ ≠ x := fun h => by
            have := congrArg Fin.val (σ.injective h); dsimp at this; omega
          have h2 : σ ⟨6 * m - 1, by omega⟩ ≠ y := fun h => by
            have := congrArg Fin.val (σ.injective h); dsimp at this; omega
          have h3 : σ ⟨6 * m - 1, by omega⟩ ≠ z := fun h => by
            have := congrArg Fin.val (σ.injective h); dsimp at this; omega
          simp [h1, h2, h3]
        have hR_rot : (permList (σ * (fIdx b (by omega)) ^ c)).filter P ~r
            ((permList σ).take (b - 1)).filter P := by
          rw [permList_mul_fIdx_pow (by omega), List.filter_append]
          simp only [List.filter_cons, hP_last, List.filter_nil, List.append_nil,
            Bool.false_eq_true, ↓reduceIte]
          exact (isRotated_filter P ⟨c, rfl⟩).symm
        have htake_nd : ((permList σ).take (b - 1)).Nodup := (permList_isPerm σ).1.take
        have htake_len : ((permList σ).take (b - 1)).length = b - 1 := by
          rw [List.length_take, permList_length]; omega
        have hft := filter_triple_of_indices htake_nd (i := 0) (j := 1) (k := 2)
          (by omega) (by omega) (by omega)
        dsimp only at hft
        have g0 : ((permList σ).take (b - 1))[0]'(by omega) = y := by
          rw [List.getElem_take, permList_getElem]
        have g1 : ((permList σ).take (b - 1))[1]'(by omega) = x := by
          rw [List.getElem_take, permList_getElem]
        have g2 : ((permList σ).take (b - 1))[2]'(by omega) = z := by
          rw [List.getElem_take, permList_getElem]
        rw [g0, g1, g2] at hft
        have hPeq : (fun v => v == y || v == x || v == z) = P := by
          funext v; dsimp [P]; cases (v == x) <;> cases (v == y) <;> cases (v == z) <;> rfl
        have htake_filt : ((permList σ).take (b - 1)).filter P = [y, x, z] := by
          rwa [hPeq] at hft
        have hyxz_rot : [y, x, z] ~r [x, z, y] := ⟨1, by simp⟩
        have hcontra : [x, y, z] ~r [x, z, y] :=
          hL_filt.symm.trans ((isRotated_filter P hrel).trans (hR_rot.trans (by rw [htake_filt]; exact hyxz_rot)))
        exact not_isRotated_triple (by intro h; have := congrArg Fin.val h; omega)
          (by intro h; have := congrArg Fin.val h; omega)
          (by intro h; have := congrArg Fin.val h; omega) hcontra
  have hleft : ∀ {a1 a2 c1 c2 : Nat}, a1 < 4 * m → a2 < 4 * m → c1 < b - 2 → c2 < b - 2 →
      W6mState m hm a1 c1 ~r W6mState m hm a2 c2 →
      permList ((fIdx b (by omega)) ^ c1) ~r
        permList ((pIdx m hm) ^ ((a2 + 4 * m - a1) % (4 * m)) * (fIdx b (by omega)) ^ c2) := by
    intro a1 a2 c1 c2 ha1 ha2 _ _ h
    let invA1 : Equiv.Perm (Fin (6 * m)) := ((pIdx m hm) ^ a1)⁻¹
    have hmap := h.map invA1
    rw [W6mState, W6mState, permList_map, permList_map, ← mul_assoc] at hmap
    have hcan : invA1 * (pIdx m hm) ^ a1 = 1 := inv_mul_cancel _
    rw [hcan, one_mul] at hmap
    have hpow : invA1 * (pIdx m hm) ^ a2 =
        (pIdx m hm) ^ ((a2 + 4 * m - a1) % (4 * m)) := by
      have hinv : invA1 = (pIdx m hm) ^ (4 * m - a1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_add, show a1 + (4 * m - a1) = 4 * m by omega, pIdx_pow_4m]
      rw [hinv, ← pow_add]
      have heq : 4 * m - a1 + a2 = a2 + 4 * m - a1 := by omega
      rw [heq]
      have hdiv : a2 + 4 * m - a1 = 4 * m * ((a2 + 4 * m - a1) / (4 * m)) +
          (a2 + 4 * m - a1) % (4 * m) := (Nat.div_add_mod _ _).symm
      conv_lhs => rw [hdiv, pow_add, pow_mul, pIdx_pow_4m, one_pow, one_mul]
    rw [← mul_assoc, hpow] at hmap
    exact hmap
  have hmod_diff : ∀ {a1 a2 : Nat}, a1 < 4 * m → a2 < 4 * m →
      (a2 + 4 * m - a1) % (4 * m) = if a1 ≤ a2 then a2 - a1 else a2 + 4 * m - a1 := by
    intro a1 a2 ha1 ha2
    by_cases hle : a1 ≤ a2
    · simp only [hle, ↓reduceIte]
      have h1 : a2 + 4 * m - a1 = (a2 - a1) + 4 * m := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.mod_eq_of_lt (by omega)
  let d := (k2 + 4 * m - k1) % (4 * m)
  have hd_eq : d = if k1 ≤ k2 then k2 - k1 else k2 + 4 * m - k1 := hmod_diff hk1 hk2
  by_cases hd : d ≤ 2 * m
  · have h1 := hleft hk1 hk2 hr1 hr2 hrot
    obtain ⟨hd0, hr⟩ := hreduced hd hr1 hr2 h1
    refine ⟨?_, hr⟩
    have : d = 0 := hd0
    rw [hd_eq] at this
    split_ifs at this <;> omega
  · let d' := (k1 + 4 * m - k2) % (4 * m)
    have hd'_eq : d' = if k2 ≤ k1 then k1 - k2 else k1 + 4 * m - k2 := hmod_diff hk2 hk1
    have hd' : d' ≤ 2 * m := by
      rw [hd_eq] at hd; rw [hd'_eq]; split_ifs at hd ⊢ <;> omega
    have h1 := hleft hk2 hk1 hr2 hr1 hrot.symm
    obtain ⟨hd0, hr⟩ := hreduced hd' hr2 hr1 h1
    refine ⟨?_, hr.symm⟩
    have : d' = 0 := hd0
    rw [hd'_eq] at this
    split_ifs at this <;> omega

/-! ### 5. Packaging `W_{6m}` as a valid `PureSelection (6 * m)` -/

/-- Exact list of all `4m * (6m - 2)` states of `W_{6m}` with their row types (`'F'` for `r < 6m - 3`, `'S'` for `r = 6m - 3`). -/
def W6mRows (m : Nat) (hm : 1 ≤ m) : List (List (Fin (6 * m)) × RowType) :=
  (List.range (4 * m)).flatMap fun k =>
    (List.range (6 * m - 2)).map fun r =>
      (W6mState m hm k r, if r = 6 * m - 3 then .S else .F)

theorem W6mRows_length (m : Nat) (hm : 1 ≤ m) :
    (W6mRows m hm).length = 4 * m * (6 * m - 2) := by
  simp [W6mRows, List.length_flatMap, Function.comp_def]

theorem mem_W6mRows_iff (m : Nat) (hm : 1 ≤ m) (x : List (Fin (6 * m))) (rt : RowType) :
    (x, rt) ∈ W6mRows m hm ↔
      ∃ k < 4 * m, ∃ r < 6 * m - 2,
        x = W6mState m hm k r ∧ rt = (if r = 6 * m - 3 then .S else .F) := by
  simp only [W6mRows, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, r, hr, hx, hrt⟩
    exact ⟨k, hk, r, hr, hx.symm, hrt.symm⟩
  · rintro ⟨k, hk, r, hr, rfl, rfl⟩
    exact ⟨k, hk, r, hr, rfl, rfl⟩

/-- `FStep` advances `(k, r)` (`r < 6m - 3`) to `(k, r + 1)`. -/
theorem FStep_W6mState (m : Nat) (hm : 1 ≤ m) (k r : Nat) :
    FStep (W6mState m hm k r) = W6mState m hm k (r + 1) := by
  unfold W6mState
  rw [FStep_permList (by omega), mul_assoc, ← pow_succ]

/-- `SStep` advances `(k, 6m - 3)` to `((k + 1) % (4m), 0)`. -/
theorem SStep_W6mState (m : Nat) (hm : 1 ≤ m) (k : Nat) :
    SStep (W6mState m hm k (6 * m - 3)) = W6mState m hm ((k + 1) % (4 * m)) 0 := by
  unfold W6mState
  rw [SStep_permList (by omega), mul_assoc]
  have hp : (fIdx (6 * m) (by omega)) ^ (6 * m - 3) * sIdx (6 * m) (by omega) = pIdx m hm := rfl
  rw [hp, ← pow_succ, pow_zero, mul_one]
  congr 1
  have hdiv : k + 1 = 4 * m * ((k + 1) / (4 * m)) + (k + 1) % (4 * m) := (Nat.div_add_mod _ _).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, pIdx_pow_4m, one_pow, one_mul]

/-- The pure-`F/S` selection `selW6m m hm` on `Fin (6 * m)` generated by the single walk `W_{6m}`. -/
noncomputable def selW6m (m : Nat) (hm : 1 ≤ m) :
    @PureSelection (6 * m) ⟨by omega⟩ :=
  letI : NeZero (6 * m) := ⟨by omega⟩
  { row := fun L =>
      match (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | some p => p
      | none => (L, .D)
    row_perm := by
      intro L hL
      cases hfind : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | none => exact ⟨hL.1, List.IsRotated.refl L⟩
      | some p =>
        have hp_mem : p ∈ W6mRows m hm := List.mem_of_find?_eq_some hfind
        have hp_dec : decide (canonLoop p.1 = L) = true :=
          List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = L)) hfind
        have hp_eq : canonLoop p.1 = L := of_decide_eq_true hp_dec
        obtain ⟨k, _, r, _, hp1, _⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
        have hperm : IsPerm (6 * m) p.1 := hp1 ▸ W6mState_isPerm m hm k r
        exact ⟨hperm, hp_eq ▸ canonLoop_isRotated p.1⟩
    closed_F := by
      intro L hL hF
      cases hfind : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | none => simp [hfind] at hF
      | some p =>
        simp only [hfind] at hF ⊢
        have hp_mem : p ∈ W6mRows m hm := List.mem_of_find?_eq_some hfind
        obtain ⟨k, hk, r, hr, hp1, hp2⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
        have hr_ne : r ≠ 6 * m - 3 := by intro heq; rw [heq] at hp2; simp [hp2] at hF
        have hr1_lt : r + 1 < 6 * m - 2 := by omega
        have hx'_eq : FStep p.1 = W6mState m hm k (r + 1) := by rw [hp1, FStep_W6mState]
        let rt' : RowType := if r + 1 = 6 * m - 3 then .S else .F
        have hmem' : (W6mState m hm k (r + 1), rt') ∈ W6mRows m hm :=
          (mem_W6mRows_iff m hm _ _).mpr ⟨k, hk, r + 1, hr1_lt, rfl, rfl⟩
        have hfind' : (W6mRows m hm).find? (fun q => decide (canonLoop q.1 = canonLoop (FStep p.1))) =
            some (W6mState m hm k (r + 1), rt') := by
          cases hf2 : (W6mRows m hm).find? (fun q => decide (canonLoop q.1 = canonLoop (FStep p.1))) with
          | none =>
            have hfalse := List.find?_eq_none.mp hf2 _ hmem'
            simp [hx'_eq] at hfalse
          | some q =>
            have hq_mem : q ∈ W6mRows m hm := List.mem_of_find?_eq_some hf2
            have hq_dec : decide (canonLoop q.1 = canonLoop (FStep p.1)) = true :=
              List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = canonLoop (FStep p.1))) hf2
            have hq_eq : canonLoop q.1 = canonLoop (FStep p.1) := of_decide_eq_true hq_dec
            obtain ⟨k', hk', r', hr', hq1, hq2⟩ := (mem_W6mRows_iff m hm q.1 q.2).mp hq_mem
            rw [hq1, hx'_eq] at hq_eq
            have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k' r') (W6mState_isPerm m hm k (r + 1))).mp hq_eq
            obtain ⟨rfl, rfl⟩ := W6m_loop_disjoint m hm hk' hk hr' hr1_lt hrot
            congr 1; exact Prod.ext hq1 hq2
        rw [hfind']; refine ⟨hx'_eq.symm, ?_⟩
        dsimp [rt']; split_ifs <;> decide
    closed_S := by
      intro L hL hS
      cases hfind : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | none => simp [hfind] at hS
      | some p =>
        simp only [hfind] at hS ⊢
        have hp_mem : p ∈ W6mRows m hm := List.mem_of_find?_eq_some hfind
        obtain ⟨k, hk, r, hr, hp1, hp2⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
        have hr_eq : r = 6 * m - 3 := by by_contra hne; simp [hne] at hp2; rw [hp2] at hS; cases hS
        subst hr_eq
        let k' := (k + 1) % (4 * m)
        have hk' : k' < 4 * m := Nat.mod_lt _ (by omega)
        have hx'_eq : SStep p.1 = W6mState m hm k' 0 := by rw [hp1, SStep_W6mState]
        let rt' : RowType := if (0 : Nat) = 6 * m - 3 then .S else .F
        have hmem' : (W6mState m hm k' 0, rt') ∈ W6mRows m hm :=
          (mem_W6mRows_iff m hm _ _).mpr ⟨k', hk', 0, by omega, rfl, rfl⟩
        have hfind' : (W6mRows m hm).find? (fun q => decide (canonLoop q.1 = canonLoop (SStep p.1))) =
            some (W6mState m hm k' 0, rt') := by
          cases hf2 : (W6mRows m hm).find? (fun q => decide (canonLoop q.1 = canonLoop (SStep p.1))) with
          | none =>
            have hfalse := List.find?_eq_none.mp hf2 _ hmem'
            simp [hx'_eq] at hfalse
          | some q =>
            have hq_mem : q ∈ W6mRows m hm := List.mem_of_find?_eq_some hf2
            have hq_dec : decide (canonLoop q.1 = canonLoop (SStep p.1)) = true :=
              List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = canonLoop (SStep p.1))) hf2
            have hq_eq : canonLoop q.1 = canonLoop (SStep p.1) := of_decide_eq_true hq_dec
            obtain ⟨k2, hk2, r2, hr2, hq1, hq2⟩ := (mem_W6mRows_iff m hm q.1 q.2).mp hq_mem
            rw [hq1, hx'_eq] at hq_eq
            have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k2 r2) (W6mState_isPerm m hm k' 0)).mp hq_eq
            obtain ⟨rfl, rfl⟩ := W6m_loop_disjoint m hm hk2 hk' hr2 (by omega) hrot
            congr 1; exact Prod.ext hq1 hq2
        rw [hfind']; refine ⟨hx'_eq.symm, ?_⟩
        dsimp [rt']; split_ifs <;> decide }

/-- Exact lookup lemma for `selW6m`: on any loop of `W6mState m hm k r`, `selW6m` returns `(W6mState m hm k r, rt)`. -/
theorem selW6m_row_state (m : Nat) (hm : 1 ≤ m) {k r : Nat} (hk : k < 4 * m) (hr : r < 6 * m - 2) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    (selW6m m hm).row (canonLoop (W6mState m hm k r)) =
      (W6mState m hm k r, if r = 6 * m - 3 then .S else .F) := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  dsimp [selW6m]
  let rt : RowType := if r = 6 * m - 3 then .S else .F
  have hmem : (W6mState m hm k r, rt) ∈ W6mRows m hm :=
    (mem_W6mRows_iff m hm _ _).mpr ⟨k, hk, r, hr, rfl, rfl⟩
  cases hf : (W6mRows m hm).find? (fun q => decide (canonLoop q.1 = canonLoop (W6mState m hm k r))) with
  | none =>
    have := List.find?_eq_none.mp hf _ hmem; simp at this
  | some q =>
    have hq_mem : q ∈ W6mRows m hm := List.mem_of_find?_eq_some hf
    have hq_dec : decide (canonLoop q.1 = canonLoop (W6mState m hm k r)) = true :=
      List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = canonLoop (W6mState m hm k r))) hf
    have hq_eq : canonLoop q.1 = canonLoop (W6mState m hm k r) := of_decide_eq_true hq_dec
    obtain ⟨k', hk', r', hr', hq1, hq2⟩ := (mem_W6mRows_iff m hm q.1 q.2).mp hq_mem
    rw [hq1] at hq_eq
    have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k' r') (W6mState_isPerm m hm k r)).mp hq_eq
    obtain ⟨rfl, rfl⟩ := W6m_loop_disjoint m hm hk' hk hr' hr hrot
    exact Prod.ext hq1 hq2

/-- Exact counts of `'S'`-rows, non-`'D'`-rows, and `'D'`-loops in `selW6m m hm`. -/
theorem selW6m_counts (m : Nat) (hm : 1 ≤ m) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .S)).length = 4 * m ∧
    ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 != .D)).length =
      4 * m * (6 * m - 2) ∧
    ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .D)).length =
      Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2) := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  let nonDLoops : List (List (Fin (6 * m))) := (W6mRows m hm).map (fun p => canonLoop p.1)
  have hnonD_nd : nonDLoops.Nodup := by
    dsimp [nonDLoops, W6mRows]
    rw [List.map_flatMap]
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro k hk
      rw [List.mem_range] at hk
      rw [List.map_map]
      refine (List.nodup_map_iff_inj_on List.nodup_range).mpr ?_
      intro r1 hr1 r2 hr2 heq
      rw [List.mem_range] at hr1 hr2
      have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k r1) (W6mState_isPerm m hm k r2)).mp heq
      exact (W6m_loop_disjoint m hm hk hk hr1 hr2 hrot).2
    · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
      intro k1 k2 hk1 hk2 hne
      rw [List.mem_range] at hk1 hk2
      change List.Disjoint _ _
      rw [List.disjoint_iff_ne]
      intro L1 hL1 L2 hL2 heq
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hL1 hL2
      obtain ⟨r1, hr1, rfl⟩ := hL1
      obtain ⟨r2, hr2, rfl⟩ := hL2
      have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k1 r1) (W6mState_isPerm m hm k2 r2)).mp heq
      exact hne (W6m_loop_disjoint m hm hk1 hk2 hr1 hr2 hrot).1
  have hnonD_perm : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 != .D)).Perm nonDLoops := by
    refine (List.perm_ext_iff_of_nodup ((allCanonLoops_nodup (6 * m)).filter _) hnonD_nd).mpr ?_
    intro L
    simp only [List.mem_filter, mem_allCanonLoops_iff, bne_iff_ne, ne_eq, nonDLoops, List.mem_map]
    constructor
    · rintro ⟨hL, hneD⟩
      dsimp [selW6m] at hneD
      cases hf : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | none => simp [hf] at hneD
      | some p =>
        have hp_dec : decide (canonLoop p.1 = L) = true :=
          List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = L)) hf
        exact ⟨p, List.mem_of_find?_eq_some hf, of_decide_eq_true hp_dec⟩
    · rintro ⟨p, hp_mem, rfl⟩
      obtain ⟨k, hk, r, hr, hp1, _⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
      rw [hp1]
      refine ⟨canonLoop_isCanonLoop (W6mState_isPerm m hm k r), ?_⟩
      rw [selW6m_row_state m hm hk hr]
      dsimp; split_ifs <;> decide
  have hnonD_len : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 != .D)).length =
      4 * m * (6 * m - 2) := by
    rw [hnonD_perm.length_eq]; simp [nonDLoops, W6mRows_length]
  let sLoops : List (List (Fin (6 * m))) :=
    (List.range (4 * m)).map (fun k => canonLoop (W6mState m hm k (6 * m - 3)))
  have hs_nd : sLoops.Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr ?_
    intro k1 hk1 k2 hk2 heq
    rw [List.mem_range] at hk1 hk2
    have hrot := (canonLoop_eq_iff (W6mState_isPerm m hm k1 _) (W6mState_isPerm m hm k2 _)).mp heq
    exact (W6m_loop_disjoint m hm hk1 hk2 (by omega) (by omega) hrot).1
  have hs_perm : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .S)).Perm sLoops := by
    refine (List.perm_ext_iff_of_nodup ((allCanonLoops_nodup (6 * m)).filter _) hs_nd).mpr ?_
    intro L
    simp only [List.mem_filter, mem_allCanonLoops_iff, beq_iff_eq, sLoops, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨hL, hS⟩
      dsimp [selW6m] at hS
      cases hf : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
      | none => simp [hf] at hS
      | some p =>
        have hp_mem := List.mem_of_find?_eq_some hf
        have hp_dec : decide (canonLoop p.1 = L) = true :=
          List.find?_some (p := fun q : List (Fin (6 * m)) × RowType => decide (canonLoop q.1 = L)) hf
        have hp_eq := of_decide_eq_true hp_dec
        obtain ⟨k, hk, r, hr, hp1, hp2⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
        rw [hf] at hS
        have hr_eq : r = 6 * m - 3 := by by_contra hne; simp [hne] at hp2; rw [hp2] at hS; cases hS
        subst hr_eq
        exact ⟨k, hk, hp1 ▸ hp_eq⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨canonLoop_isCanonLoop (W6mState_isPerm m hm k _), ?_⟩
      rw [selW6m_row_state m hm hk (by omega)]
      simp
  have hs_len : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .S)).length =
      4 * m := by
    rw [hs_perm.length_eq]; simp [sLoops]
  -- 3. `'D'`-loops + non-`'D'`-loops = `(6 * m - 1)!`!
  have hsum : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .D)).length +
      ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 != .D)).length =
      (allCanonLoops (6 * m)).length := by
    have hpart : ∀ (l : List (List (Fin (6 * m)))) (p : List (Fin (6 * m)) → Bool),
        (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
      intro l p
      induction l with
      | nil => simp
      | cons a as ih =>
        cases hpa : p a <;> simp [hpa] <;> omega
    have heq : (fun L => ((selW6m m hm).row L).2 != .D) =
        (fun L => !(((selW6m m hm).row L).2 == .D)) := by
      funext L; cases ((selW6m m hm).row L).2 <;> rfl
    rw [heq]
    exact hpart (allCanonLoops (6 * m)) _
  rw [allCanonLoops_length] at hsum
  exact ⟨hs_len, hnonD_len, by omega⟩

end AsymptoticZero
