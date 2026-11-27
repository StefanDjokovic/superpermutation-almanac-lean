import AlmanacDefs
import AsymptoticZero.DLoopBags
import AsymptoticZero.StarsAndBars

/-!
# Main Assembly: `S(n) = n! + (n-1)! + (n-2)! + o((n-3)!)` (`Almanac.AsymptoticUpper 0`)

Combines:
- Lemma 1 (`WalkW6m.lean`): `selW6m` counts and `W_{6m}` walk disjointness,
- Lemma 2 (`BlockEmbed.lean`): `iterW6mLift`, `iterW6mLift_S_count_le`, `iterW6mLift_D_count`,
- Lemma 3 (`LayerSliceGraph.lean` + `StarsAndBars.lean`): `allLayerBags_theorem`,
- Lemma 4 (`DLoopBags.lean`): `dLoop_bags_theorem`,
- Eulerian bag assembly (`Eulerian.lean`): `word_of_bags`,
- Permutation coverage (`SliceModel.lean`): `isSuperpermutation_of_covers_all_slices`, `rowSlices_body_sum`, `F3_eq_mul_fact`.

Proves `Almanac.AsymptoticUpper 0` in 100% pure Lean 4.35.0 kernel (zero `sorry`, zero `native_decide`).
-/

namespace AsymptoticZero

/-- `Almanac.fact` is strictly positive. -/
private theorem fact_pos (n : Nat) : 0 < Almanac.fact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

/-- `Almanac.fact` is monotone. -/
private theorem fact_mono {a b : Nat} (h : a ≤ b) : Almanac.fact a ≤ Almanac.fact b := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    change Almanac.fact a ≤ (k + 1) * Almanac.fact k
    exact ih.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))

/-- Elementary `Nat` Bernoulli inequality: `a * (a + d) ^ r ≥ (a + r * d) * a ^ r`. -/
private theorem nat_bernoulli (a d r : Nat) :
    (a + r * d) * a ^ r ≤ a * (a + d) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc (a + (r + 1) * d) * a ^ (r + 1)
        = (a + (r + 1) * d) * (a ^ r * a) := by rw [pow_succ]
      _ ≤ ((a + r * d) * a ^ r) * (a + d) := by
          have h1 : (a + (r + 1) * d) * a ≤ (a + r * d) * (a + d) := by
            have : (a + r * d) * (a + d) = (a + (r + 1) * d) * a + r * (d * d) := by ring
            omega
          calc (a + (r + 1) * d) * (a ^ r * a)
              = a ^ r * ((a + (r + 1) * d) * a) := by ring
            _ ≤ a ^ r * ((a + r * d) * (a + d)) := Nat.mul_le_mul_left _ h1
            _ = ((a + r * d) * a ^ r) * (a + d) := by ring
      _ ≤ (a * (a + d) ^ r) * (a + d) := Nat.mul_le_mul_right _ ih
      _ = a * (a + d) ^ (r + 1) := by rw [pow_succ]; ring

/-- Pure `Nat` exponential decay: for `a < c` and any `M : Nat`, `∃ r ≥ 1, M * a ^ r ≤ c ^ r`. -/
private theorem exists_pow_ratio_le {a c : Nat} (hac : a < c) (M : Nat) :
    ∃ r : Nat, 1 ≤ r ∧ M * a ^ r ≤ c ^ r := by
  by_cases ha : a = 0
  · subst ha
    exact ⟨1, Nat.le_refl 1, by simp⟩
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    let d := c - a
    have hd_pos : 1 ≤ d := by omega
    have hc : a + d = c := Nat.add_sub_cancel' (Nat.le_of_lt hac)
    let r := M * a + 1
    refine ⟨r, by omega, ?_⟩
    have hbern := nat_bernoulli a d r
    rw [hc] at hbern
    have hge : M * a ≤ a + r * d := by
      have h1 : r ≤ r * d := Nat.le_mul_of_pos_right r hd_pos
      omega
    have hmul : a * (M * a ^ r) ≤ a * c ^ r :=
      calc a * (M * a ^ r) = (M * a) * a ^ r := by ring
        _ ≤ (a + r * d) * a ^ r := Nat.mul_le_mul_right _ hge
        _ ≤ a * c ^ r := hbern
    exact Nat.le_of_mul_le_mul_left hmul ha_pos

/-- Sum of `body.length` over a flattened list of bags equals sum of bag body sums. -/
private theorem sum_flatten_map {α : Type} (f : α → Nat) (ls : List (List α)) :
    (ls.flatten.map f).sum = (ls.map (fun l => (l.map f).sum)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

/-- Partition sum of a list by a Boolean predicate `p`. -/
private theorem sum_filter_add_filter_not {α : Type} (p : α → Bool) (f : α → Nat) (l : List α) :
    ((l.filter p).map f).sum + ((l.filter (fun x => !(p x))).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases p a with
    | true => simp; omega
    | false => simp; omega

/-- Core finite construction for any `(m, r, K)` with `1 ≤ m`, `1 ≤ r`, `r * (6 * m) + 1 ≤ K`:
produces a superpermutation `w : Almanac.Word (K + 2)` whose excess length over
`(K+2)! + (K+1)! + K!` is explicitly bounded in `Nat`! -/
theorem superperm_construction (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) :
    let b := 6 * m
    let F := Almanac.fact (b - 1)
    let Db := F - 4 * m * (b - 2)
    ∃ w : Almanac.Word (K + 2),
      Almanac.IsSuperpermutation (K + 2) w ∧
      ∃ extra1 extra2 extra3 : Nat,
        w.length = Almanac.fact (K + 2) + Almanac.fact (K + 1) + Almanac.fact K +
          (extra1 + extra2 + extra3) ∧
        extra1 * m ≤ Almanac.fact (K - 1) ∧
        F ^ r * extra2 = 2 * Db ^ r * Almanac.fact (K - 1) ∧
        (K - 2) * extra3 ≤ r * Almanac.fact (K - 1) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  set b := 6 * m
  set F := Almanac.fact (b - 1)
  set Lb := 4 * m * (b - 2)
  set Db := F - Lb
  -- Obtain Layer bags (Lemma 3) and D-loop bags (Lemma 4)
  obtain ⟨bagsL, hL_len, hL_ok, hL_cov, zTotal, hz_le, hL_body⟩ :=
    allLayerBags_theorem m hm r hr K hK
  obtain ⟨bagsD, hD_len, hD_ok, hD_cov, hD_body⟩ :=
    dLoop_bags_theorem m hm r hr K hK
  -- Assemble all bags into a single word `w : Word (K + 2)` via `word_of_bags`
  let bags := bagsL ++ bagsD
  have hbags_ok : ∀ B ∈ bags, B ≠ [] ∧ (∀ e ∈ B, EdgeOk (K - 1) e) ∧ Balanced B ∧ WeaklyConnected B := by
    intro B hB
    rw [List.mem_append] at hB
    rcases hB with h1 | h2
    · exact hL_ok B h1
    · exact hD_ok B h2
  obtain ⟨w, hw_len, hw_cov⟩ := word_of_bags bags hbags_ok
  -- Step 1: Prove `w` is a superpermutation on `K + 2` symbols!
  have hsp : Almanac.IsSuperpermutation (K + 2) w := by
    apply isSuperpermutation_of_covers_all_slices hK4 (iterW6mLift m hm r hr K hK) w
    intro L hL e he
    by_cases hD : ((iterW6mLift m hm r hr K hK).row L).2 = .D
    · rw [hD] at he
      obtain ⟨B, hB, heB⟩ := hD_cov L hL hD e he
      exact hw_cov B (List.mem_append_right _ hB) e heB
    · obtain ⟨B, hB, heB⟩ := hL_cov L hL hD e he
      exact hw_cov B (List.mem_append_left _ hB) e heB
  -- Step 2: Compute exact total body sum across all `(K - 1)!` canonical loops!
  let fRow : List (Fin K) → Nat := fun L =>
    ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
      ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum
  let QS := ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .S)).length
  have hpart_sum :
      (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 != .D)).map fRow).sum +
      (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).map fRow).sum =
      ((allCanonLoops K).map fRow).sum := by
    have hnot : (fun L : List (Fin K) => ((iterW6mLift m hm r hr K hK).row L).2 != .D) =
        (fun L => !(((iterW6mLift m hm r hr K hK).row L).2 == .D)) := by
      funext L; rfl
    rw [hnot, Nat.add_comm]
    exact sum_filter_add_filter_not (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D) fRow _
  have hall_row_sum : ((allCanonLoops K).map fRow).sum =
      Almanac.fact (K + 2) + Almanac.fact (K + 1) + Almanac.fact K + 2 * QS := by
    have hgen : ∀ (l : List (List (Fin K))),
        (∀ L ∈ l, IsCanonLoop K L) →
        (l.map fRow).sum = l.length * ((K + 2) * (K + 2) * K) +
          2 * (l.filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .S)).length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons L Ls ih =>
        intro hmem
        have hL := hmem L List.mem_cons_self
        have hperm := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
        have hbody := rowSlices_body_sum hK4 hperm.2 ((iterW6mLift m hm r hr K hK).row L).2
        have hih := ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        simp only [List.map_cons, List.sum_cons, List.length_cons, List.filter_cons]
        change fRow L + (Ls.map fRow).sum = _
        dsimp only [fRow]
        rw [hbody, hih]
        cases hc : ((iterW6mLift m hm r hr K hK).row L).2 with
        | D => simp; ring
        | F => simp; ring
        | S => simp; ring
    rw [hgen (allCanonLoops K) (fun L hL => (mem_allCanonLoops_iff L).mp hL),
      allCanonLoops_length, ← F3_eq_mul_fact K (by omega)]
  -- Step 3: Assemble exact `w.length` into `F3 + (extra1 + extra2 + extra3)`!
  let extra1 := 2 * QS + (K - 1) * zTotal
  let extra2 := 2 * (K - 1) * bagsD.length
  let extra3 := (K - 1) * bagsL.length
  have hlen_exact : w.length = Almanac.fact (K + 2) + Almanac.fact (K + 1) + Almanac.fact K +
      (extra1 + extra2 + extra3) := by
    rw [hw_len, sum_flatten_map]
    dsimp only [bags]
    rw [List.length_append, List.map_append, List.sum_append, hL_body, hD_body]
    have hsum_all :
        (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 != .D)).map fRow).sum +
        (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).map fRow).sum =
        Almanac.fact (K + 2) + Almanac.fact (K + 1) + Almanac.fact K + 2 * QS :=
      hpart_sum.trans hall_row_sum
    dsimp only [fRow] at hsum_all
    dsimp only [extra1, extra2, extra3]
    rw [Nat.mul_add]
    linarith
  -- Step 4: Prove the 3 `Nat` bounds on `extra1`, `extra2`, `extra3`!
  have hfact_km1 : (K - 1) * Almanac.fact (K - 2) = Almanac.fact (K - 1) := by
    have h1 : K - 1 = (K - 2) + 1 := by omega
    conv_rhs => rw [h1]; simp [Almanac.fact]
    rw [h1]
  have hextra1 : extra1 * m ≤ Almanac.fact (K - 1) := by
    have hQS_le : QS * Lb ≤ 4 * m * Almanac.fact (K - 1) :=
      iterW6mLift_S_count_le m hm r hr K hK
    have h2QS : (2 * QS) * Lb ≤ 8 * m * Almanac.fact (K - 1) := by
      calc (2 * QS) * Lb = 2 * (QS * Lb) := by ring
        _ ≤ 2 * (4 * m * Almanac.fact (K - 1)) := Nat.mul_le_mul_left 2 hQS_le
        _ = 8 * m * Almanac.fact (K - 1) := by ring
    have hz_km1 : ((K - 1) * zTotal) * Lb ≤ (b - 1) * Almanac.fact (K - 1) := by
      calc ((K - 1) * zTotal) * Lb = (K - 1) * (zTotal * Lb) := by ring
        _ ≤ (K - 1) * ((b - 1) * Almanac.fact (K - 2)) := Nat.mul_le_mul_left (K - 1) hz_le
        _ = (b - 1) * ((K - 1) * Almanac.fact (K - 2)) := by ring
        _ = (b - 1) * Almanac.fact (K - 1) := by rw [hfact_km1]
    have h16m_le_Lb : 16 * m * m ≤ Lb := by
      dsimp only [Lb, b]
      have h1 : 4 * m ≤ 6 * m - 2 := by omega
      calc 16 * m * m = (4 * m) * (4 * m) := by ring
        _ ≤ (4 * m) * (6 * m - 2) := Nat.mul_le_mul_left (4 * m) h1
    have h14_le_16 : 8 * m + (b - 1) ≤ 16 * m := by dsimp only [b]; omega
    have hmul16 : (16 * m) * (extra1 * m) ≤ (16 * m) * Almanac.fact (K - 1) := by
      calc (16 * m) * (extra1 * m) = extra1 * (16 * m * m) := by ring
        _ ≤ extra1 * Lb := Nat.mul_le_mul_left extra1 h16m_le_Lb
        _ = (2 * QS) * Lb + ((K - 1) * zTotal) * Lb := by dsimp only [extra1]; ring
        _ ≤ 8 * m * Almanac.fact (K - 1) + (b - 1) * Almanac.fact (K - 1) := Nat.add_le_add h2QS hz_km1
        _ = (8 * m + (b - 1)) * Almanac.fact (K - 1) := by ring
        _ ≤ (16 * m) * Almanac.fact (K - 1) := Nat.mul_le_mul_right _ h14_le_16
    exact Nat.le_of_mul_le_mul_left hmul16 (by omega)
  have hextra2 : F ^ r * extra2 = 2 * Db ^ r * Almanac.fact (K - 1) := by
    calc F ^ r * extra2 = 2 * (K - 1) * (F ^ r * bagsD.length) := by dsimp only [extra2]; ring
      _ = 2 * (K - 1) * (Db ^ r * Almanac.fact (K - 2)) := by rw [hD_len]
      _ = 2 * Db ^ r * ((K - 1) * Almanac.fact (K - 2)) := by ring
      _ = 2 * Db ^ r * Almanac.fact (K - 1) := by rw [hfact_km1]
  have hextra3 : (K - 2) * extra3 ≤ r * Almanac.fact (K - 1) := by
    have hfact_km2 : (K - 2) * Almanac.fact (K - 3) = Almanac.fact (K - 2) := by
      have h1 : K - 2 = (K - 3) + 1 := by omega
      conv_rhs => rw [h1]; simp [Almanac.fact]
      rw [h1]
    have hKb_le : Almanac.fact (K - b) ≤ Almanac.fact (K - 3) :=
      fact_mono (by dsimp only [b]; omega)
    calc (K - 2) * extra3 = (K - 2) * ((K - 1) * bagsL.length) := rfl
      _ ≤ (K - 2) * ((K - 1) * (r * Almanac.fact (K - b))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL_len)
      _ = r * ((K - 1) * ((K - 2) * Almanac.fact (K - b))) := by ring
      _ ≤ r * ((K - 1) * ((K - 2) * Almanac.fact (K - 3))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hKb_le))
      _ = r * ((K - 1) * Almanac.fact (K - 2)) := by rw [hfact_km2]
      _ = r * Almanac.fact (K - 1) := by rw [hfact_km1]
  exact ⟨w, hsp, extra1, extra2, extra3, hlen_exact, hextra1, hextra2, hextra3⟩

/-- **Main Theorem:** `Almanac.AsymptoticUpper 0`, i.e.
`S(n) ≤ n! + (n-1)! + (n-2)! + o((n-3)!)`! -/
theorem asymptotic_upper_zero : Almanac.AsymptoticUpper 0 := by
  intro ε hε
  -- Step 1: Choose `T : Nat` with `1 ≤ T` and `(3 : Rat) ≤ ε * (T : Rat)`!
  -- Since `0 < ε`, we have `1 ≤ ε.num` and `ε = ε.num / ε.den`, so `T := 3 * ε.den + 1` works!
  have hε_num_pos : (0 : Int) < ε.num := Rat.num_pos.mpr hε
  have hε_num_ge1 : (1 : Rat) ≤ (ε.num : Rat) := by
    have : (1 : Int) ≤ ε.num := by omega
    exact_mod_cast this
  have hε_den_pos : (0 : Rat) < (ε.den : Rat) := by exact_mod_cast ε.den_pos
  have hε_ge_inv : (1 : Rat) / (ε.den : Rat) ≤ ε := by
    conv_rhs => rw [← Rat.num_div_den ε]
    exact div_le_div_of_nonneg_right hε_num_ge1 (le_of_lt hε_den_pos)
  let T : Nat := 3 * ε.den + 1
  have hT_pos : 1 ≤ T := by omega
  have h3_le_εT : (3 : Rat) ≤ ε * (T : Rat) := by
    have hT_ge : (3 * ε.den : Rat) ≤ (T : Rat) := by
      dsimp only [T]; push_cast; linarith
    have h1 : (3 : Rat) = (1 / (ε.den : Rat)) * (3 * (ε.den : Rat)) := by
      field_simp [ne_of_gt hε_den_pos]
    calc (3 : Rat) = (1 / (ε.den : Rat)) * (3 * (ε.den : Rat)) := h1
      _ ≤ ε * (3 * (ε.den : Rat)) :=
            mul_le_mul_of_nonneg_right hε_ge_inv (by positivity)
      _ ≤ ε * (T : Rat) :=
            mul_le_mul_of_nonneg_left hT_ge (le_of_lt hε)
  -- Step 2: Set `m := T` (`1 ≤ m`) and choose `r ≥ 1` so `2 * T * Db ^ r ≤ F ^ r`!
  let m : Nat := T
  have hm : 1 ≤ m := hT_pos
  let b := 6 * m
  let F := Almanac.fact (b - 1)
  let Lb := 4 * m * (b - 2)
  let Db := F - Lb
  have hLb_pos : 0 < Lb := Nat.mul_pos (by omega) (by dsimp only [b]; omega)
  have hLb_le_F : Lb ≤ F := by
    let _ : NeZero b := ⟨by dsimp only [b]; omega⟩
    have h1 := (selW6m_counts m hm).2.1
    have h2 := List.length_filter_le (fun L => ((selW6m m hm).row L).2 != .D) (allCanonLoops b)
    rw [h1, allCanonLoops_length] at h2; exact h2
  have hDb_lt_F : Db < F := by dsimp only [Db]; omega
  obtain ⟨r, hr, hr_decay⟩ := exists_pow_ratio_le hDb_lt_F (2 * T)
  -- Step 3: Set `N := max (r * (6 * m) + 3) (T * r + 4)`!
  let N := max (r * (6 * m) + 3) (T * r + 4)
  refine ⟨N, ?_⟩
  intro n hn
  have hn_ge_rb3 : r * (6 * m) + 3 ≤ n := le_trans (le_max_left _ _) hn
  have hn_ge_Tr4 : T * r + 4 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 2 := ⟨n - 2, by omega⟩
  have hK : r * (6 * m) + 1 ≤ K := by omega
  have hK_Tr : T * r ≤ K - 2 := by omega
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  -- Step 4: Invoke `superperm_construction m hm r hr K hK`!
  obtain ⟨w, hsp, extra1, extra2, extra3, hw_len, hex1, hex2, hex3⟩ :=
    superperm_construction m hm r hr K hK
  -- Bound `T * extra1`, `T * extra2`, `T * extra3` each by `Almanac.fact (K - 1)`!
  have hT1 : T * extra1 ≤ Almanac.fact (K - 1) := by
    simpa [m, Nat.mul_comm] using hex1
  have hT2 : T * extra2 ≤ Almanac.fact (K - 1) := by
    have hFr_pos : 0 < F ^ r := pow_pos (fact_pos _) r
    have hmul : F ^ r * (T * extra2) ≤ F ^ r * Almanac.fact (K - 1) := by
      calc F ^ r * (T * extra2) = T * (F ^ r * extra2) := by ring
        _ = T * (2 * Db ^ r * Almanac.fact (K - 1)) := by rw [hex2]
        _ = (2 * T * Db ^ r) * Almanac.fact (K - 1) := by ring
        _ ≤ F ^ r * Almanac.fact (K - 1) := Nat.mul_le_mul_right _ hr_decay
    exact Nat.le_of_mul_le_mul_left hmul hFr_pos
  have hT3 : T * extra3 ≤ Almanac.fact (K - 1) := by
    have hmul : r * (T * extra3) ≤ r * Almanac.fact (K - 1) := by
      calc r * (T * extra3) = (T * r) * extra3 := by ring
        _ ≤ (K - 2) * extra3 := Nat.mul_le_mul_right _ hK_Tr
        _ ≤ r * Almanac.fact (K - 1) := hex3
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hT_tot : T * (extra1 + extra2 + extra3) ≤ 3 * Almanac.fact (K - 1) := by
    have hsum : T * (extra1 + extra2 + extra3) = T * extra1 + T * extra2 + T * extra3 := by ring
    omega
  -- Cast to `Rat` and cancel `(T : Rat) > 0`!
  have hextra_rat : ((extra1 + extra2 + extra3 : Nat) : Rat) ≤ ε * (Almanac.fact (K - 1) : Rat) := by
    have hT_pos_rat : (0 : Rat) < (T : Rat) := by exact_mod_cast (by omega : 0 < T)
    have hcast : (T : Rat) * ((extra1 + extra2 + extra3 : Nat) : Rat) ≤
        (3 : Rat) * (Almanac.fact (K - 1) : Rat) := by exact_mod_cast hT_tot
    have hmul_rat : (T : Rat) * ((extra1 + extra2 + extra3 : Nat) : Rat) ≤
        (T : Rat) * (ε * (Almanac.fact (K - 1) : Rat)) := by
      calc (T : Rat) * ((extra1 + extra2 + extra3 : Nat) : Rat)
          ≤ (3 : Rat) * (Almanac.fact (K - 1) : Rat) := hcast
        _ ≤ (ε * (T : Rat)) * (Almanac.fact (K - 1) : Rat) :=
              mul_le_mul_of_nonneg_right h3_le_εT (by positivity)
        _ = (T : Rat) * (ε * (Almanac.fact (K - 1) : Rat)) := by ring
    exact le_of_mul_le_mul_left hmul_rat hT_pos_rat
  refine ⟨w, hsp, ?_⟩
  unfold Almanac.asymptoticForm
  have hsub1 : K + 2 - 1 = K + 1 := by omega
  have hsub2 : K + 2 - 2 = K := by omega
  have hsub3 : K + 2 - 3 = K - 1 := by omega
  rw [hsub1, hsub2, hsub3, zero_add, hw_len]
  push_cast at hextra_rat ⊢
  linarith

end AsymptoticZero
