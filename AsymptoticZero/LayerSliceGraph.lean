import AsymptoticZero.DLoopBags

/-!
# AsymptoticZero.LayerSliceGraph (Lemma 3 — Part 1)

Defines the Layer-`j` (`0 ≤ j < r`) Stars-and-Bars bags for `iterW6mLift m hm r hr K hK`:
* `allLayerSigmas`: surviving linear permutations `σ` of `M_j = Fin K \ B_j` whose projections
  onto blocks `B_0, ..., B_{j-1}` are all `'D'` in `selW6m`, with exact count
  `((6m - 1)!)^j * |allLayerSigmas| = Db^j * (K - 6m)!`.
* `interleavings` & `zCyclesOf`: the `Nat.choose (K - 2) (6m - 2)` lifted `z`-connector cycles
  per `σ`, each of length `K - 1`.
* `LayerSlice`, `layerSlices`, `nextSlice`: the deterministic bijective transition map on
  Layer-`j` slices preserving `σ`, yielding `Balanced (layerBag j σ)` and exact body-sum
  partitioning across all Layer-`j` loops of `iterW6mLift`.
-/

namespace AsymptoticZero

/-! ### 1. Block membership predicates and surviving `M_j` linear permutations `allLayerSigmas` -/

/-- Decidable block membership predicate: `x ∈ B_j = [j * b, (j + 1) * b)`. -/
def inBlock (b j : Nat) {K : Nat} (x : Fin K) : Bool :=
  decide (j * b ≤ x.1 ∧ x.1 < (j + 1) * b)

/-- Complement predicate: `x ∈ M_j = Fin K \ B_j`. -/
def notInBlock (b j : Nat) {K : Nat} (x : Fin K) : Bool :=
  !(inBlock b j x)

theorem inBlock_iff_projBlockElem_isSome (b j : Nat) {K : Nat} (x : Fin K) :
    inBlock b j x = true ↔ (projBlockElem b j x).isSome = true := by
  unfold inBlock projBlockElem
  by_cases h : j * b ≤ x.1 ∧ x.1 < (j + 1) * b <;> simp [h]

theorem notInBlock_iff_projBlockElem_eq_none (b j : Nat) {K : Nat} (x : Fin K) :
    notInBlock b j x = true ↔ projBlockElem b j x = none := by
  unfold notInBlock inBlock projBlockElem
  by_cases h : j * b ≤ x.1 ∧ x.1 < (j + 1) * b <;> simp [h]

theorem inBlock_embBlock (b K j : Nat) (hjb : (j + 1) * b ≤ K) (a : Fin b) :
    inBlock b j (embBlock b K j hjb a) = true := by
  rw [inBlock_iff_projBlockElem_isSome, projBlockElem_embBlock]; rfl

theorem notInBlock_embBlock_ne {b K i j : Nat} (hij : i ≠ j) (hjb : (j + 1) * b ≤ K) (a : Fin b) :
    notInBlock b i (embBlock b K j hjb a) = true := by
  rw [notInBlock_iff_projBlockElem_eq_none]; exact projBlockElem_embBlock_ne hij hjb a

theorem filter_inBlock_eq_map_projBlock {b j K : Nat} (hjb : (j + 1) * b ≤ K) (l : List (Fin K)) :
    l.filter (inBlock b j) = (projBlock b j l).map (embBlock b K j hjb) := by
  unfold projBlock
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.filterMap_cons]
    cases hx : projBlockElem b j x with
    | none =>
      have hin : inBlock b j x = false := by
        have h := (notInBlock_iff_projBlockElem_eq_none b j x).mpr hx
        unfold notInBlock at h; simp at h; exact h
      simp [hin, ih]
    | some a =>
      have hin : inBlock b j x = true := by
        rw [inBlock_iff_projBlockElem_isSome, hx]; rfl
      have hxe : x = embBlock b K j hjb a := (projBlockElem_eq_some_iff b j hjb x a).mp hx
      rw [hin, ih, hxe]; rfl

/-- The list of all elements of `M_j = Fin K \ B_j` in ascending order. -/
def elemsMj (b j K : Nat) : List (Fin K) :=
  (List.finRange K).filter (notInBlock b j)

theorem elemsMj_nodup (b j K : Nat) : (elemsMj b j K).Nodup :=
  (List.nodup_finRange K).filter _

theorem elemsMj_length {b j K : Nat} (hjb : (j + 1) * b ≤ K) :
    (elemsMj b j K).length = K - b := by
  unfold elemsMj
  have hpart : ((List.finRange K).filter (inBlock b j)).length +
      ((List.finRange K).filter (notInBlock b j)).length = K := by
    have hsum : ∀ (l : List (Fin K)),
        (l.filter (inBlock b j)).length + (l.filter (notInBlock b j)).length = l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        have hb : notInBlock b j x = !inBlock b j x := rfl
        rw [List.filter_cons, List.filter_cons, hb]
        cases h : inBlock b j x <;> simp <;> omega
    simpa [List.length_finRange] using hsum (List.finRange K)
  have hin_len : ((List.finRange K).filter (inBlock b j)).length = b := by
    rw [filter_inBlock_eq_map_projBlock hjb, List.length_map]
    exact (projBlock_isPerm hjb ⟨List.nodup_finRange K, List.length_finRange⟩).2
  omega

/-- All `(K - b)!` linear permutations of `M_j = Fin K \ B_j`. -/
def allLinearPermsMj (b j K : Nat) : List (List (Fin K)) :=
  (elemsMj b j K).permutations

theorem allLinearPermsMj_nodup (b j K : Nat) : (allLinearPermsMj b j K).Nodup :=
  List.nodup_permutations _ (elemsMj_nodup b j K)

theorem allLinearPermsMj_length {b j K : Nat} (hjb : (j + 1) * b ≤ K) :
    (allLinearPermsMj b j K).length = Almanac.fact (K - b) := by
  unfold allLinearPermsMj
  rw [List.length_permutations, elemsMj_length hjb]
  have hfact : ∀ n : Nat, Nat.factorial n = Almanac.fact n := fun n => by
    induction n with
    | zero => rfl
    | succ k ih => simp [Nat.factorial, Almanac.fact, ih]
  exact hfact (K - b)

theorem mem_allLinearPermsMj_iff {b j K : Nat} (hjb : (j + 1) * b ≤ K) (σ : List (Fin K)) :
    σ ∈ allLinearPermsMj b j K ↔
      σ.Nodup ∧ σ.length = K - b ∧ ∀ x ∈ σ, notInBlock b j x = true := by
  unfold allLinearPermsMj
  rw [List.mem_permutations]
  constructor
  · intro hp
    refine ⟨hp.nodup_iff.mpr (elemsMj_nodup b j K),
      hp.length_eq.trans (elemsMj_length hjb), ?_⟩
    intro x hx
    have hm := hp.mem_iff.mp hx
    exact (List.mem_filter.mp hm).2
  · rintro ⟨hnd, hlen, hall⟩
    have hsub : ∀ x ∈ σ, x ∈ elemsMj b j K := fun x hx =>
      List.mem_filter.mpr ⟨List.mem_finRange x, hall x hx⟩
    have hfin : σ.toFinset = (elemsMj b j K).toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub x hx
      · rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup (elemsMj_nodup b j K),
          hlen, elemsMj_length hjb]
    exact (List.perm_ext_iff_of_nodup hnd (elemsMj_nodup b j K)).mpr fun x => by
      rw [← List.mem_toFinset, ← List.mem_toFinset, hfin]

theorem projBlock_isPerm_of_Mj {b i j K : Nat} (hij : i < j) (hjb : (j + 1) * b ≤ K)
    {σ : List (Fin K)} (hσ : σ ∈ allLinearPermsMj b j K) :
    IsPerm b (projBlock b i σ) := by
  have hσ_perm : σ.Perm (elemsMj b j K) := List.mem_permutations.mp hσ
  have hfull : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).Perm (List.finRange K) := by
    have hnd1 := elemsMj_nodup b j K
    have hnd2 : ((List.finRange b).map (embBlock b K j hjb)).Nodup := by
      refine (List.nodup_finRange b).map fun a1 a2 h => ?_
      have hv := congrArg Fin.val h; dsimp [embBlock] at hv
      apply Fin.ext; omega
    have hdisj : ∀ x ∈ elemsMj b j K, x ∉ (List.finRange b).map (embBlock b K j hjb) := by
      intro x hx hm
      have hnb := (List.mem_filter.mp hx).2
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
      have hib := inBlock_embBlock b K j hjb a
      unfold notInBlock at hnb; rw [hib] at hnb; simp at hnb
    have hnd_app : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).Nodup :=
      List.nodup_append.mpr ⟨hnd1, hnd2, fun a ha b' hb heq => hdisj a ha (heq ▸ hb)⟩
    have hlen_app : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).length = K := by
      rw [List.length_append, elemsMj_length hjb, List.length_map, List.length_finRange]
      have : b ≤ (j + 1) * b := by
        have := Nat.mul_le_mul_right b (show 1 ≤ j + 1 by omega); rwa [Nat.one_mul] at this
      omega
    exact (List.perm_ext_iff_of_nodup hnd_app (List.nodup_finRange K)).mpr fun x => by
      have hfin : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).toFinset =
          (List.finRange K).toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro y _; rw [List.mem_toFinset]; exact List.mem_finRange y
        · rw [List.toFinset_card_of_nodup hnd_app, List.toFinset_card_of_nodup (List.nodup_finRange K),
            hlen_app, List.length_finRange]
      rw [← List.mem_toFinset, ← List.mem_toFinset, hfin]
  have hp_big : IsPerm K (σ ++ (List.finRange b).map (embBlock b K j hjb)) := by
    have hp := (hσ_perm.append_right ((List.finRange b).map (embBlock b K j hjb))).trans hfull
    exact ⟨hp.nodup_iff.mpr (List.nodup_finRange K), hp.length_eq.trans List.length_finRange⟩
  have hib : (i + 1) * b ≤ K := by
    have := Nat.mul_le_mul_right b (show i + 1 ≤ j + 1 by omega); omega
  have hproj_eq : projBlock b i (σ ++ (List.finRange b).map (embBlock b K j hjb)) =
      projBlock b i σ := by
    unfold projBlock
    rw [List.filterMap_append]
    have hnil : ((List.finRange b).map (embBlock b K j hjb)).filterMap (projBlockElem b i) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro x hx
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
      exact projBlockElem_embBlock_ne (by omega) hjb a
    rw [hnil, List.append_nil]
  rw [← hproj_eq]
  exact projBlock_isPerm hib hp_big

/-- Surviving linear permutations `σ` of `M_j` for Layer `j < r`:
all preceding blocks `B_0, ..., B_{j-1}` are `'D'` in `selW6m`. -/
noncomputable def allLayerSigmas (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) : List (List (Fin K)) :=
  letI : NeZero (6 * m) := ⟨by omega⟩
  (allLinearPermsMj (6 * m) j K).filter (fun σ =>
    decide (∀ i : Fin j, ((selW6m m hm).row (blockLoop (6 * m) i.1 σ)).2 = .D))

theorem allLayerSigmas_nodup (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) :
    (allLayerSigmas m hm r hr K hK j).Nodup := by
  unfold allLayerSigmas
  exact (allLinearPermsMj_nodup (6 * m) j K).filter _

/-- Exact count of surviving Layer-`j` linear orders `σ`:
`((6m - 1)!)^j * |allLayerSigmas j| = D_b^j * (K - 6m)!`! -/
theorem allLayerSigmas_length (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r) :
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    (Almanac.fact (6 * m - 1)) ^ j * (allLayerSigmas m hm r hr K hK j).length =
      Db ^ j * Almanac.fact (K - 6 * m) := by
  set b := 6 * m
  let _ : NeZero b := ⟨by omega⟩
  have hjb : (j + 1) * b ≤ K := by
    have h1 : (j + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j + 1 ≤ r by omega)
    omega
  have hjK : j * b ≤ K := by
    have h1 : j * b ≤ (j + 1) * b := Nat.mul_le_mul_right b (by omega)
    omega
  have hact_mem : ∀ (τ : Fin j → Equiv.Perm (Fin b)) (σ : List (Fin K)),
      σ ∈ allLinearPermsMj b j K →
      σ.map (blockDiagPerm b j K hjK τ) ∈ allLinearPermsMj b j K := by
    intro τ σ hσ
    obtain ⟨hnd, hlen, hall⟩ := (mem_allLinearPermsMj_iff hjb σ).mp hσ
    rw [mem_allLinearPermsMj_iff hjb]
    refine ⟨hnd.map (blockDiagPerm b j K hjK τ).injective, by rw [List.length_map, hlen], ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hnb := hall x hx
    rw [notInBlock_iff_projBlockElem_eq_none] at hnb ⊢
    by_cases hlt : x.1 < j * b
    · -- `blockDiagPerm` maps `[0, j * b)` into `[0, j * b)`, hence outside `B_j = [j*b, (j+1)*b)`!
      have hval : (blockDiagPerm b j K hjK τ x).1 < j * b := by
        change (blockDiagAct b j K hjK τ x).1 < j * b
        unfold blockDiagAct
        rw [dif_pos hlt]
        dsimp only
        have hb_pos : 0 < b := by dsimp [b]; omega
        have hi : x.1 / b < j := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm b j]; exact hlt)
        have h1 : (x.1 / b + 1) * b ≤ j * b := Nat.mul_le_mul_right b (show x.1 / b + 1 ≤ j by omega)
        have h2 : (τ ⟨x.1 / b, hi⟩ ⟨x.1 % b, Nat.mod_lt _ hb_pos⟩).1 < b :=
          (τ ⟨x.1 / b, hi⟩ ⟨x.1 % b, Nat.mod_lt _ hb_pos⟩).2
        have h3 : (x.1 / b + 1) * b = x.1 / b * b + b := by ring
        omega
      unfold projBlockElem
      exact dif_neg (fun h => by omega)
    · -- Outside `[0, j * b)`, `blockDiagPerm` fixes `x`!
      have hfix : blockDiagPerm b j K hjK τ x = x := by
        change blockDiagAct b j K hjK τ x = x
        unfold blockDiagAct; exact dif_neg hlt
      rw [hfix]; exact hnb
  have huni := uniform_block_fibers (α := List (Fin K)) (b := b) j (allLinearPermsMj b j K)
    (allLinearPermsMj_nodup b j K)
    (fun σ i => blockLoop b i.1 σ)
    (fun σ hσ i => canonLoop_isCanonLoop (projBlock_isPerm_of_Mj i.2 hjb hσ))
    (fun τ σ => σ.map (blockDiagPerm b j K hjK τ))
    hact_mem
    (fun τ σ _ => by
      rw [List.map_map]
      have hcomp : (blockDiagPerm b j K hjK (fun i => (τ i)⁻¹)) ∘ (blockDiagPerm b j K hjK τ) = id := by
        funext x; exact (blockDiagPerm b j K hjK τ).left_inv x
      simp [hcomp])
    (fun τ σ hσ i => by
      have hpL : IsPerm b (projBlock b i.1 σ) := projBlock_isPerm_of_Mj i.2 hjb hσ
      have hp1 : IsPerm b (projBlock b i.1 (σ.map (blockDiagPerm b j K hjK τ))) :=
        projBlock_isPerm_of_Mj i.2 hjb (hact_mem τ σ hσ)
      have hpB : IsPerm b ((blockLoop b i.1 σ).map (τ i)) :=
        ⟨(canonLoop_isCanonLoop hpL).1.1.map (τ i).injective,
          by rw [List.length_map]; exact (canonLoop_isCanonLoop hpL).1.2⟩
      unfold blockLoop
      rw [projBlock_map_blockDiagPerm]
      exact (canonLoop_eq_iff (by rw [projBlock_map_blockDiagPerm] at hp1; exact hp1) hpB).mpr
        ((canonLoop_isRotated _).map _))
  let P : (Fin j → List (Fin b)) → Bool :=
    fun t => decide (∀ i : Fin j, ((selW6m m hm).row (t i)).2 = .D)
  have hcnt := uniform_block_count j (allLinearPermsMj b j K) (allLinearPermsMj_nodup b j K)
    (fun σ i => blockLoop b i.1 σ)
    (fun σ hσ i => canonLoop_isCanonLoop (projBlock_isPerm_of_Mj i.2 hjb hσ))
    huni P
  rw [allLinearPermsMj_length hjb, count_allD_tuples m hm j] at hcnt
  exact hcnt

/-! ### 2. Order-preserving interleavings and lifted `z`-connector cycles -/

/-- All order-preserving interleavings (shuffles) of two lists `l1` and `l2`. -/
def interleavings {α : Type} : List α → List α → List (List α)
  | [], l2 => [l2]
  | a :: as, [] => [a :: as]
  | a :: as, b :: bs =>
    (interleavings as (b :: bs)).map (a :: ·) ++
    (interleavings (a :: as) bs).map (b :: ·)

theorem interleavings_length {α : Type} (l1 l2 : List α) :
    (interleavings l1 l2).length = Nat.choose (l1.length + l2.length) l1.length := by
  induction l1 generalizing l2 with
  | nil => simp [interleavings]
  | cons a as ih1 =>
    induction l2 with
    | nil => simp [interleavings]
    | cons b bs ih2 =>
      simp only [interleavings, List.length_append, List.length_map]
      rw [ih1 (b :: bs), ih2]
      simp only [List.length_cons]
      have h1 : as.length + (bs.length + 1) = as.length + bs.length + 1 := by omega
      have h2 : as.length + 1 + bs.length = as.length + bs.length + 1 := by omega
      have h3 : as.length + 1 + (bs.length + 1) = (as.length + bs.length + 1) + 1 := by omega
      rw [h1, h2, h3]
      exact (Nat.choose_succ_succ (as.length + bs.length + 1) as.length).symm

theorem mem_interleavings_iff {α : Type} (P : α → Bool) :
    ∀ (l1 l2 : List α), (∀ x ∈ l1, P x = true) → (∀ y ∈ l2, P y = false) →
      ∀ w : List α, w ∈ interleavings l1 l2 ↔ w.filter P = l1 ∧ w.filter (fun x => !(P x)) = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ h2 w
    simp only [interleavings, List.mem_singleton]
    constructor
    · rintro rfl
      refine ⟨List.filter_eq_nil_iff.mpr fun x hx => by simp [h2 x hx],
              List.filter_eq_self.mpr fun x hx => by simp [h2 x hx]⟩
    · rintro ⟨hf1, hf2⟩
      have hnil : ∀ x ∈ w, P x = false := fun x hx => by
        cases hPx : P x with
        | false => rfl
        | true =>
          have : x ∈ w.filter P := List.mem_filter.mpr ⟨hx, hPx⟩
          rw [hf1] at this; cases this
      have hself : w.filter (fun x => !(P x)) = w :=
        List.filter_eq_self.mpr fun x hx => by simp [hnil x hx]
      rw [hself] at hf2; exact hf2
  | cons a as ih1 =>
    intro l2
    induction l2 with
    | nil =>
      intro h1 _ w
      simp only [interleavings, List.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨List.filter_eq_self.mpr fun x hx => h1 x hx,
                List.filter_eq_nil_iff.mpr fun x hx => by simp [h1 x hx]⟩
      · rintro ⟨hf1, hf2⟩
        have hall : ∀ x ∈ w, P x = true := fun x hx => by
          cases hPx : P x with
          | true => rfl
          | false =>
            have : x ∈ w.filter (fun x => !(P x)) := List.mem_filter.mpr ⟨hx, by simp [hPx]⟩
            rw [hf2] at this; cases this
        have hself : w.filter P = w := List.filter_eq_self.mpr hall
        rw [hself] at hf1; exact hf1
    | cons b bs ih2 =>
      intro h1 h2 w
      have ha : P a = true := h1 a List.mem_cons_self
      have hb : P b = false := h2 b List.mem_cons_self
      have has : ∀ x ∈ as, P x = true := fun x hx => h1 x (List.mem_cons_of_mem _ hx)
      have hbs : ∀ y ∈ bs, P y = false := fun y hy => h2 y (List.mem_cons_of_mem _ hy)
      simp only [interleavings, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩)
        · obtain ⟨hf1, hf2⟩ := (ih1 (b :: bs) has h2 w').mp hw'
          simp [List.filter_cons, ha, hf1, hf2]
        · obtain ⟨hf1, hf2⟩ := (ih2 h1 hbs w').mp hw'
          simp [List.filter_cons, hb, hf1, hf2]
      · rintro ⟨hf1, hf2⟩
        cases w with
        | nil => simp at hf1
        | cons x xs =>
          simp only [List.filter_cons] at hf1 hf2
          cases hPx : P x with
          | true =>
            simp only [hPx, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at hf1 hf2
            have ⟨rfl, htail⟩ := List.cons.inj hf1
            exact Or.inl ⟨xs, (ih1 (b :: bs) has h2 xs).mpr ⟨htail, hf2⟩, rfl⟩
          | false =>
            simp only [hPx, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hf1 hf2
            have ⟨rfl, htail⟩ := List.cons.inj hf2
            exact Or.inr ⟨xs, (ih2 h1 hbs xs).mpr ⟨hf1, htail⟩, rfl⟩

theorem interleavings_sub_length {α : Type} (l1 l2 : List α) {w : List α}
    (hw : w ∈ interleavings l1 l2) : w.length = l1.length + l2.length := by
  induction l1 generalizing l2 w with
  | nil =>
    simp only [interleavings, List.mem_singleton] at hw; subst hw; simp
  | cons a as ih1 =>
    induction l2 generalizing w with
    | nil =>
      simp only [interleavings, List.mem_singleton] at hw; subst hw; simp
    | cons b bs ih2 =>
      simp only [interleavings, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
      · have := ih1 (b :: bs) hw'; simp at this ⊢; omega
      · have := ih2 hw'; simp at this ⊢; omega

/-- The prefix `[emb_j(0), emb_j(1), ..., emb_j(b - 3)]` of length `b - 2` in block `j`. -/
def bPref (b K j : Nat) (hjb : (j + 1) * b ≤ K) : List (Fin K) :=
  (List.finRange (b - 2)).map (fun i => embBlock b K j hjb ⟨i.1, by omega⟩)

theorem bPref_length (b K j : Nat) (hjb : (j + 1) * b ≤ K) :
    (bPref b K j hjb).length = b - 2 := by
  simp [bPref]

theorem bPref_inBlock (b K j : Nat) (hjb : (j + 1) * b ≤ K) :
    ∀ x ∈ bPref b K j hjb, notInBlock b j x = false := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  unfold notInBlock; rw [inBlock_embBlock]; rfl

/-- The `Nat.choose (K - 2) (b - 2)` lifted `z`-connector cycles for Layer `j`, order `σ`. -/
def zCyclesOf (b K j : Nat) (hjb : (j + 1) * b ≤ K) (σ : List (Fin K)) :
    List (Almanac.Word (K + 2)) :=
  (interleavings σ (bPref b K j hjb)).map (fun w => symZ K :: w.map embK)

theorem zCyclesOf_length {b K j : Nat} (hb : 2 ≤ b) (hjb : (j + 1) * b ≤ K)
    {σ : List (Fin K)} (hσ : σ.length = K - b) :
    (zCyclesOf b K j hjb σ).length = Nat.choose (K - 2) (b - 2) := by
  have hbK : b ≤ K := by
    have := Nat.mul_le_mul_right b (show 1 ≤ j + 1 by omega); rw [Nat.one_mul] at this; omega
  unfold zCyclesOf
  rw [List.length_map, interleavings_length, hσ, bPref_length]
  have hsum : K - b + (b - 2) = K - 2 := by omega
  rw [hsum, ← Nat.choose_symm (by omega : K - b ≤ K - 2)]
  congr 1; omega

theorem zCyclesOf_elem_length {b K j : Nat} (hb : 2 ≤ b) (hjb : (j + 1) * b ≤ K)
    {σ : List (Fin K)} (hσ : σ.length = K - b) {ck : Almanac.Word (K + 2)}
    (hck : ck ∈ zCyclesOf b K j hjb σ) :
    ck.length = K - 1 := by
  have hbK : b ≤ K := by
    have := Nat.mul_le_mul_right b (show 1 ≤ j + 1 by omega); rw [Nat.one_mul] at this; omega
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hck
  rw [List.length_cons, List.length_map, interleavings_sub_length _ _ hw, hσ, bPref_length]
  omega

/-! ### 3. Layer-`j` slice descriptors, `sliceSigma`, `nextSlice`, and `Balanced` -/

/-- Tag identifying a slice within a non-`'D'` row `rowSlices q rt`. -/
inductive SliceTag where
  | ins (port : Nat)
  | repKm2
  | repKm1
  deriving DecidableEq, Repr

/-- Valid tags for row type `rt` at level `K`. -/
def tagsOfRowType (K : Nat) : RowType → List SliceTag
  | .D => []
  | .F => (List.range K).map SliceTag.ins
  | .S => (List.range K).map SliceTag.ins ++ [.repKm2, .repKm1]

theorem tagsOfRowType_nodup (K : Nat) (rt : RowType) : (tagsOfRowType K rt).Nodup := by
  cases rt with
  | D => exact List.nodup_nil
  | F => exact (List.nodup_range).map (fun _ _ h => SliceTag.ins.inj h)
  | S =>
    rw [tagsOfRowType, List.nodup_append]
    refine ⟨(List.nodup_range).map (fun _ _ h => SliceTag.ins.inj h), by decide, ?_⟩
    intro a ha b hb
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp

/-- Raw edge corresponding to `(q, rt, tag)`. -/
def edgeOfRowTag {K : Nat} (q : List (Fin K)) (rt : RowType) (tag : SliceTag) :
    RawEdge (K + 2) :=
  let v := match rt with | .F => K | _ => K - 2
  match tag with
  | .ins port => insSlice q v port
  | .repKm2 => repSlice q (K - 2)
  | .repKm1 => repSlice q (K - 1)

theorem map_edgeOfRowTag_eq_rowSlices {K : Nat} (hK : 4 ≤ K) (q : List (Fin K))
    {rt : RowType} (hrt : rt ≠ .D) :
    (tagsOfRowType K rt).map (edgeOfRowTag q rt) = rowSlices q rt := by
  cases rt with
  | D => exact absurd rfl hrt
  | F =>
    simp [tagsOfRowType, rowSlices, edgeOfRowTag]
  | S =>
    have hdrop : (List.range K).drop (K - 2) = [K - 2, K - 1] := by
      refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
      rw [List.getElem_drop, List.getElem_range]
      simp only [List.length_cons, List.length_nil] at hi2
      interval_cases i <;> simp <;> omega
    simp only [tagsOfRowType, rowSlices, List.map_append, List.map_map, List.map_cons,
      List.map_nil, hdrop]
    rfl

/-- The invariant `M_j`-order `σ` of a row `q` and tag `tag` in Layer `j`:
for `ins port`, `(q.rotate port).filter (notInBlock b j)`;
for `repKm2` / `repKm1`, `(q.rotate (K - 2)).filter (notInBlock b j)`. -/
def tagSigma (b j K : Nat) (q : List (Fin K)) : SliceTag → List (Fin K)
  | .ins port => (q.rotate port).filter (notInBlock b j)
  | .repKm2 => (q.rotate (K - 2)).filter (notInBlock b j)
  | .repKm1 => (q.rotate (K - 2)).filter (notInBlock b j)

/-- Exact invariance of `tagSigma` on `'F'`-port `0 → K - 1`. -/
theorem tagSigma_F_zero {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hlast : inBlock b j (q[K - 1]'(by omega)) = true) :
    tagSigma b j K q (.ins (K - 1)) = tagSigma b j K q (.ins 0) := by
  obtain ⟨a, last, mid, hq_eq, _, hmid_len, _, hlast_eq⟩ := split_first_last hK hq
  have hnb_last : notInBlock b j last = false := by
    unfold notInBlock; rw [hlast_eq, hlast]; rfl
  have hrot : q.rotate (K - 1) = [last] ++ (a :: mid) := by
    have hlen : (a :: mid).length = K - 1 := by simp [hmid_len]; omega
    have h1 := List.rotate_append_length_eq (a :: mid) [last]
    rw [hlen] at h1
    rw [hq_eq, h1]
  dsimp only [tagSigma]
  rw [List.rotate_zero, hrot, hq_eq, List.filter_append, List.filter_append]
  simp [List.filter_cons, hnb_last]

/-- Exact invariance of `tagSigma` on `'F'`-port `1 ≤ port < K → (FStep q, port - 1)`. -/
theorem tagSigma_F_pos {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hlast : inBlock b j (q[K - 1]'(by omega)) = true) {port : Nat} (hp1 : 1 ≤ port) (hpK : port < K) :
    tagSigma b j K (FStep q) (.ins (port - 1)) = tagSigma b j K q (.ins port) := by
  obtain ⟨a, last, mid, hq_eq, hF, hmid_len, _, hlast_eq⟩ := split_first_last hK hq
  have hnb_last : notInBlock b j last = false := by
    unfold notInBlock; rw [hlast_eq, hlast]; rfl
  set p := port - 1
  have hp_le : p ≤ mid.length := by omega
  have hrot_F : (FStep q).rotate p = mid.drop p ++ [a, last] ++ mid.take p := by
    rw [hF, List.rotate_eq_drop_append_take (by simp [hmid_len]; omega)]
    rw [List.drop_append_of_le_length hp_le, List.take_append_of_le_length hp_le]
  have hrot_q : q.rotate port = mid.drop p ++ [last, a] ++ mid.take p := by
    have hport : port = 1 + p := by omega
    rw [hport, ← List.rotate_rotate, hq_eq]
    have h1 : (a :: mid ++ [last]).rotate 1 = mid ++ [last, a] := by
      rw [List.cons_append, List.rotate_cons_succ, List.rotate_zero, List.append_assoc]
      rfl
    rw [h1, List.rotate_eq_drop_append_take (by simp [hmid_len]; omega)]
    rw [List.drop_append_of_le_length hp_le, List.take_append_of_le_length hp_le]
  dsimp only [tagSigma]
  rw [hrot_F, hrot_q]
  simp [List.filter_append, List.filter_cons, hnb_last]

/-- Exact invariance of `tagSigma` on `'S'`-port `port ≤ K - 3 → (SStep q, port + 1)`. -/
theorem tagSigma_S_lt {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hv : inBlock b j (q[K - 2]'(by omega)) = true) {port : Nat} (hp : port ≤ K - 3) :
    tagSigma b j K (SStep q) (.ins (port + 1)) = tagSigma b j K q (.ins port) := by
  obtain ⟨pre, u, v, w, hq_eq, hS, hpre_len, _, hv_eq, _⟩ := split_last3 hK hq
  have hnb_v : notInBlock b j v = false := by
    unfold notInBlock; rw [hv_eq, hv]; rfl
  have hp_le : port ≤ pre.length := by omega
  have hrot_S : (SStep q).rotate (port + 1) = pre.drop port ++ [v, u, w] ++ pre.take port := by
    have h1 : ([w] ++ pre ++ [v, u]).rotate 1 = pre ++ [v, u, w] := by
      simp [List.singleton_append, List.rotate_cons_succ, List.rotate_zero, List.append_assoc]
    rw [hS, Nat.add_comm, ← List.rotate_rotate, h1,
      List.rotate_eq_drop_append_take (by simp [hpre_len]; omega),
      List.drop_append_of_le_length hp_le, List.take_append_of_le_length hp_le]
  have hrot_q : q.rotate port = pre.drop port ++ [u, v, w] ++ pre.take port := by
    rw [hq_eq, List.rotate_eq_drop_append_take (by simp [hpre_len]; omega),
      List.drop_append_of_le_length hp_le, List.take_append_of_le_length hp_le]
  dsimp only [tagSigma]
  rw [hrot_S, hrot_q]
  simp [List.filter_append, List.filter_cons, hnb_v]

/-- Exact invariance of `tagSigma` across the `'S'`-detour `ins(K-2) → repKm2 → repKm1 → ins(K-1) → (SStep q, 0)`. -/
theorem tagSigma_S_detour {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hv : inBlock b j (q[K - 2]'(by omega)) = true) :
    tagSigma b j K q (.ins (K - 1)) = tagSigma b j K q (.ins (K - 2)) ∧
    tagSigma b j K (SStep q) (.ins 0) = tagSigma b j K q (.ins (K - 2)) := by
  obtain ⟨pre, u, v, w, hq_eq, hS, hpre_len, _, hv_eq, _⟩ := split_last3 hK hq
  have hnb_v : notInBlock b j v = false := by
    unfold notInBlock; rw [hv_eq, hv]; rfl
  have hrot_km2 : q.rotate (K - 2) = [v, w] ++ (pre ++ [u]) := by
    have h1 : q = (pre ++ [u]) ++ [v, w] := by rw [hq_eq]; simp [List.append_assoc]
    have hlen : (pre ++ [u]).length = K - 2 := by simp [hpre_len]; omega
    have h2 := List.rotate_append_length_eq (pre ++ [u]) [v, w]
    rw [hlen] at h2; rw [h1, h2]
  have hrot_km1 : q.rotate (K - 1) = [w] ++ (pre ++ [u, v]) := by
    have h1 : q = (pre ++ [u, v]) ++ [w] := by rw [hq_eq]; simp [List.append_assoc]
    have hlen : (pre ++ [u, v]).length = K - 1 := by simp [hpre_len]; omega
    have h2 := List.rotate_append_length_eq (pre ++ [u, v]) [w]
    rw [hlen] at h2; rw [h1, h2]
  dsimp only [tagSigma]
  rw [List.rotate_zero, hrot_km2, hrot_km1, hS]
  constructor <;> simp [List.filter_append, List.filter_cons, hnb_v]

/-- Deterministic transition `nextSlice` on Layer-`j` slice descriptors `(L, tag)`. -/
noncomputable def nextSlice (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    List (Fin K) × SliceTag → List (Fin K) × SliceTag := fun ⟨L, tag⟩ =>
  letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  let row := (iterW6mLift m hm r hr K hK).row L
  match row.2 with
  | .D => (L, tag)
  | .F =>
    match tag with
    | .ins port =>
      if port = 0 then (L, .ins (K - 1))
      else (canonLoop (FStep row.1), .ins (port - 1))
    | _ => (L, tag)
  | .S =>
    match tag with
    | .ins port =>
      if port ≤ K - 3 then (canonLoop (SStep row.1), .ins (port + 1))
      else if port = K - 2 then (L, .repKm2)
      else (canonLoop (SStep row.1), .ins 0)
    | .repKm2 => (L, .repKm1)
    | .repKm1 => (L, .ins (K - 1))

/-- All Layer-`j` slice descriptors `(L, tag)` belonging to `σ`. -/
noncomputable def layerSlices (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) (σ : List (Fin K)) :
    List (List (Fin K) × SliceTag) :=
  letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  ((allCanonLoops K).filter (fun L => activeLayer m hm r L == some j)).flatMap fun L =>
    let row := (iterW6mLift m hm r hr K hK).row L
    ((tagsOfRowType K row.2).filter (fun tag => tagSigma (6 * m) j K row.1 tag == σ)).map (fun tag => (L, tag))

theorem layerSlices_nodup (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) (σ : List (Fin K)) :
    (layerSlices m hm r hr K hK j σ).Nodup := by
  let _ : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  unfold layerSlices
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro L _
    exact ((tagsOfRowType_nodup K _).filter _).map (fun _ _ h => (Prod.mk.inj h).2)
  · have hnd := (allCanonLoops_nodup K).filter (fun L => activeLayer m hm r L == some j)
    refine hnd.imp_of_mem ?_
    intro L1 L2 _ _ hne x hx1 hx2
    obtain ⟨t1, _, rfl⟩ := List.mem_map.mp hx1
    obtain ⟨t2, _, heq⟩ := List.mem_map.mp hx2
    exact hne (Prod.mk.inj heq).1.symm

theorem mem_layerSlices_iff (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) (σ : List (Fin K))
    (s : List (Fin K) × SliceTag) :
    letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
    s ∈ layerSlices m hm r hr K hK j σ ↔
      IsCanonLoop K s.1 ∧ activeLayer m hm r s.1 = some j ∧
      s.2 ∈ tagsOfRowType K ((iterW6mLift m hm r hr K hK).row s.1).2 ∧
      tagSigma (6 * m) j K ((iterW6mLift m hm r hr K hK).row s.1).1 s.2 = σ := by
  let _ : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  rcases s with ⟨L, tag⟩
  unfold layerSlices
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq, mem_allCanonLoops_iff]
  constructor
  · rintro ⟨L', ⟨hL', hact⟩, t', ⟨ht', hsig⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨hL', hact, ht', hsig⟩
  · rintro ⟨hL, hact, ht, hsig⟩
    exact ⟨L, ⟨hL, hact⟩, tag, ⟨ht, hsig⟩, rfl⟩

/-- `FStep` is injective on length-`K` lists (`K ≥ 4`). -/
theorem FStep_inj {α : Type} {K : Nat} (hK : 4 ≤ K) {q1 q2 : List α}
    (hq1 : q1.length = K) (hq2 : q2.length = K) (h : FStep q1 = FStep q2) : q1 = q2 := by
  obtain ⟨a1, l1, m1, hq1_eq, hF1, hm1, _, _⟩ := split_first_last hK hq1
  obtain ⟨a2, l2, m2, hq2_eq, hF2, hm2, _, _⟩ := split_first_last hK hq2
  rw [hF1, hF2] at h
  have hm_eq : m1 = m2 := by
    have := congrArg (List.take (K - 2)) h
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
    exact this
  rw [hm_eq, List.append_cancel_left_eq] at h
  simp only [List.cons.injEq, and_true] at h
  rw [hq1_eq, hq2_eq, hm_eq, h.1, h.2]

/-- `SStep` is injective on length-`K` lists (`K ≥ 4`). -/
theorem SStep_inj {α : Type} {K : Nat} (hK : 4 ≤ K) {q1 q2 : List α}
    (hq1 : q1.length = K) (hq2 : q2.length = K) (h : SStep q1 = SStep q2) : q1 = q2 := by
  obtain ⟨p1, u1, v1, w1, hq1_eq, hS1, hp1, _, _, _⟩ := split_last3 hK hq1
  obtain ⟨p2, u2, v2, w2, hq2_eq, hS2, hp2, _, _, _⟩ := split_last3 hK hq2
  rw [hS1, hS2] at h
  have hw_eq : w1 = w2 := by
    have := congrArg List.head? h; simp at this; exact this
  have hrest : p1 ++ [v1, u1] = p2 ++ [v2, u2] := by
    simp only [List.singleton_append, List.cons_append, List.cons.injEq] at h; exact h.2
  have hp_eq : p1 = p2 := by
    have := congrArg (List.take (K - 3)) hrest
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
    exact this
  rw [hp_eq, List.append_cancel_left_eq] at hrest
  simp only [List.cons.injEq, and_true] at hrest
  rw [hq1_eq, hq2_eq, hp_eq, hw_eq, hrest.1, hrest.2]

/-- Helper: on a Layer-`j` loop `L` with `row = (q, .F)`, `q[K - 1] ∈ B_j` and
`activeLayer (canonLoop (FStep q)) = some j`. -/
theorem layer_F_step_info (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} {L : List (Fin K)}
    (hL : IsCanonLoop K L)
    (hact : activeLayer m hm r L = some j)
    (hF : ((iterW6mLift m hm r hr K hK).row L).2 = .F) :
    let q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    have hK4 : 4 ≤ K := by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega
    inBlock (6 * m) j (q[K - 1]'(by rw [hq.2]; omega)) = true ∧
    activeLayer m hm r (canonLoop (FStep q)) = some j := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  obtain ⟨hj_lt, hj_neD, hprev⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  have hbl_canon : IsCanonLoop (6 * m) (blockLoop (6 * m) j L) :=
    canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1)
  have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L) hbl_canon
  have hrt_F : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .F := by
    change (iterW6mRow m hm r K hK L).2 = .F at hF
    cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
    | D => exact absurd hc hj_neD
    | F => rfl
    | S => rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hF; cases hF
  have hlenB : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
    rw [hrowB.1.2]; omega
  have hq_eq : ((iterW6mLift m hm r hr K hK).row L).1 =
      pinAt L (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB)) (K - 1) := by
    change (iterW6mRow m hm r K hK L).1 = _
    rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hrt_F hlenB]
  set q := ((iterW6mLift m hm r hr K hK).row L).1
  have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
  have hq_last : q[K - 1]'(by rw [hq.2]; omega) =
      embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB) := by
    have := pinAt_getElem hL.1 (embBlock (6 * m) K j hjb
      (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB)) (by omega : K - 1 < K)
    simpa [hq_eq] using this
  have hin : inBlock (6 * m) j (q[K - 1]'(by rw [hq.2]; omega)) = true := by
    rw [hq_last]; exact inBlock_embBlock _ _ _ _ _
  refine ⟨hin, ?_⟩
  have hcl := (iterW6mLift m hm r hr K hK).closed_F L hL hF
  have hx'_perm : IsPerm K (FStep q) := FStep_isPerm hq
  -- All blocks `i < j` are unchanged (stay `'D'`), and `activeLayer (canonLoop (FStep q)) ≠ none`!
  have hother : ∀ i < j, blockLoop (6 * m) i (canonLoop (FStep q)) = blockLoop (6 * m) i L := by
    intro i hi
    have hib : (i + 1) * (6 * m) ≤ K := by
      have := Nat.mul_le_mul_right (6 * m) (show i + 1 ≤ r by omega); omega
    have hnone : projBlockElem (6 * m) i (q[K - 1]'(by rw [hq.2]; omega)) = none := by
      rw [hq_last]; exact projBlockElem_embBlock_ne (by omega) hjb _
    have hrot1 : projBlock (6 * m) i (FStep q) ~r projBlock (6 * m) i q :=
      projBlock_FStep_of_last_none hK4 hq.2 hnone
    have hrot2 : projBlock (6 * m) i q ~r projBlock (6 * m) i L :=
      projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2
    have hrot3 : projBlock (6 * m) i (canonLoop (FStep q)) ~r projBlock (6 * m) i (FStep q) :=
      projBlock_isRotated (canonLoop_isRotated _).symm
    exact (canonLoop_eq_iff (projBlock_isPerm hib (canonLoop_isCanonLoop hx'_perm).1)
      (projBlock_isPerm hib hL.1)).mpr (hrot3.trans (hrot1.trans hrot2))
  -- Also block `j` is non-`'D'` (either unchanged if `q[0] ∉ B_j`, or `FStep rowB` if `q[0] ∈ B_j`)!
  have hj_neD' : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop (FStep q)))).2 ≠ .D := by
    cases hq0 : projBlockElem (6 * m) j (q[0]'(by rw [hq.2]; omega)) with
    | none =>
      have hproj_x' := projBlock_FStep_of_head_none hK4 hq.2 hq0
      have hbl_eq : blockLoop (6 * m) j (canonLoop (FStep q)) = blockLoop (6 * m) j L := by
        have hr1 : projBlock (6 * m) j (canonLoop (FStep q)) ~r projBlock (6 * m) j (FStep q) :=
          projBlock_isRotated (canonLoop_isRotated _).symm
        rw [hproj_x'] at hr1
        exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
          (projBlock_isPerm hjb hL.1)).mpr
          (hr1.trans (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2))
      rw [hbl_eq]; exact hj_neD
    | some a' =>
      have hl_some : projBlockElem (6 * m) j (q[K - 1]'(by rw [hq.2]; omega)) =
          some (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB) := by
        rw [hq_last]; exact projBlockElem_embBlock _ _ _ _ _
      have hproj_q : projBlock (6 * m) j q = ((selW6m m hm).row (blockLoop (6 * m) j L)).1 := by
        have hpr_rot : projBlock (6 * m) j q ~r ((selW6m m hm).row (blockLoop (6 * m) j L)).1 :=
          (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2).trans
            ((canonLoop_isRotated _).trans hrowB.2.symm)
        have hpr_perm := projBlock_isPerm hjb hq
        have hlast_pr : (projBlock (6 * m) j q)[6 * m - 1]'(by rw [hpr_perm.2]; omega) =
            ((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB := by
          obtain ⟨a, last, mid, hsp, _, _, _, hlsp⟩ := split_first_last hK4 hq.2
          have hls : projBlockElem (6 * m) j last =
              some (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB) := hlsp ▸ hl_some
          have hdec : projBlock (6 * m) j q = (a :: mid).filterMap (projBlockElem (6 * m) j) ++
              [((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB] := by
            unfold projBlock; rw [hsp, List.filterMap_append]; simp [List.filterMap_cons, hls]
          have hlp : ((a :: mid).filterMap (projBlockElem (6 * m) j)).length = 6 * m - 1 := by
            have := hpr_perm.2; rw [hdec] at this; simp at this; omega
          have ht : ((a :: mid).filterMap (projBlockElem (6 * m) j) ++
              [((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB])[6 * m - 1]'(by simp [hlp]) =
              ((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB := by
            rw [List.getElem_append_right (by omega)]; simp [hlp]
          simpa [hdec] using ht
        exact (eq_pinAt_of_isRotated hrowB.1 hpr_perm hpr_rot (by omega) hlast_pr).trans
          (eq_pinAt_of_isRotated hrowB.1 hrowB.1 (List.IsRotated.refl _) (by omega) rfl).symm
      have hproj_x' : projBlock (6 * m) j (FStep q) = FStep ((selW6m m hm).row (blockLoop (6 * m) j L)).1 := by
        rw [← hproj_q]; exact projBlock_FStep_of_both_some hK4 hq.2 hq0 hl_some
      have hbl_eq : blockLoop (6 * m) j (canonLoop (FStep q)) =
          canonLoop (FStep ((selW6m m hm).row (blockLoop (6 * m) j L)).1) := by
        have hr1 : projBlock (6 * m) j (canonLoop (FStep q)) ~r projBlock (6 * m) j (FStep q) :=
          projBlock_isRotated (canonLoop_isRotated _).symm
        rw [hproj_x'] at hr1
        exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
          (FStep_isPerm hrowB.1)).mpr hr1
      rw [hbl_eq]
      exact ((selW6m m hm).closed_F (blockLoop (6 * m) j L) hbl_canon hrt_F).2
  rw [activeLayer_eq_some_iff]
  exact ⟨hj_lt, hj_neD', fun i hi => by rw [hother i hi]; exact hprev i hi⟩

/-- Helper: on a Layer-`j` loop `L` with `row = (q, .S)`, `q[K - 2] ∈ B_j` and
`activeLayer (canonLoop (SStep q)) = some j`. -/
theorem layer_S_step_info (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} {L : List (Fin K)}
    (hL : IsCanonLoop K L)
    (hact : activeLayer m hm r L = some j)
    (hS : ((iterW6mLift m hm r hr K hK).row L).2 = .S) :
    let q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    have hK4 : 4 ≤ K := by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega
    inBlock (6 * m) j (q[K - 2]'(by rw [hq.2]; omega)) = true ∧
    activeLayer m hm r (canonLoop (SStep q)) = some j := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  obtain ⟨hj_lt, hj_neD, hprev⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  have hbl_canon : IsCanonLoop (6 * m) (blockLoop (6 * m) j L) :=
    canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1)
  have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L) hbl_canon
  have hrt_S : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .S := by
    change (iterW6mRow m hm r K hK L).2 = .S at hS
    cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
    | D => exact absurd hc hj_neD
    | F => rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hS; cases hS
    | S => rfl
  have hlenB : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
    rw [hrowB.1.2]; omega
  have hq_eq : ((iterW6mLift m hm r hr K hK).row L).1 =
      pinAt L (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 2]'hlenB)) (K - 2) := by
    change (iterW6mRow m hm r K hK L).1 = _
    rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hrt_S hlenB]
  set q := ((iterW6mLift m hm r hr K hK).row L).1
  have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
  have hq_km2 : q[K - 2]'(by rw [hq.2]; omega) =
      embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 2]'hlenB) := by
    have := pinAt_getElem hL.1 (embBlock (6 * m) K j hjb
      (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 2]'hlenB)) (by omega : K - 2 < K)
    simpa [hq_eq] using this
  have hin : inBlock (6 * m) j (q[K - 2]'(by rw [hq.2]; omega)) = true := by
    rw [hq_km2]; exact inBlock_embBlock _ _ _ _ _
  refine ⟨hin, ?_⟩
  have hx'_perm : IsPerm K (SStep q) := SStep_isPerm (by omega) hq
  have hother : ∀ i < j, blockLoop (6 * m) i (canonLoop (SStep q)) = blockLoop (6 * m) i L := by
    intro i hi
    have hib : (i + 1) * (6 * m) ≤ K := by
      have := Nat.mul_le_mul_right (6 * m) (show i + 1 ≤ r by omega); omega
    have hnone : projBlockElem (6 * m) i (q[K - 2]'(by rw [hq.2]; omega)) = none := by
      rw [hq_km2]; exact projBlockElem_embBlock_ne (by omega) hjb _
    have hrot1 : projBlock (6 * m) i (SStep q) ~r projBlock (6 * m) i q :=
      projBlock_SStep_of_none hK4 hq.2 (Or.inr hnone)
    have hrot2 : projBlock (6 * m) i q ~r projBlock (6 * m) i L :=
      projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2
    have hrot3 : projBlock (6 * m) i (canonLoop (SStep q)) ~r projBlock (6 * m) i (SStep q) :=
      projBlock_isRotated (canonLoop_isRotated (SStep q)).symm
    exact (canonLoop_eq_iff (projBlock_isPerm hib (canonLoop_isCanonLoop hx'_perm).1)
      (projBlock_isPerm hib hL.1)).mpr (hrot3.trans (hrot1.trans hrot2))
  have hj_neD' : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop (SStep q)))).2 ≠ .D := by
    cases hq3 : projBlockElem (6 * m) j (q[K - 3]'(by rw [hq.2]; omega)) with
    | none =>
      have hrot1 := projBlock_SStep_of_none hK4 hq.2 (Or.inl hq3)
      have hbl_eq : blockLoop (6 * m) j (canonLoop (SStep q)) = blockLoop (6 * m) j L := by
        have hr1 : projBlock (6 * m) j (canonLoop (SStep q)) ~r projBlock (6 * m) j (SStep q) :=
          projBlock_isRotated (canonLoop_isRotated (SStep q)).symm
        exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
          (projBlock_isPerm hjb hL.1)).mpr
          (hr1.trans (hrot1.trans (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2)))
      rw [hbl_eq]; exact hj_neD
    | some u' =>
      have hproj_rot : projBlock (6 * m) j q ~r ((selW6m m hm).row (blockLoop (6 * m) j L)).1 :=
        (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2).trans
          ((canonLoop_isRotated _).trans hrowB.2.symm)
      have hkm2_s : projBlockElem (6 * m) j (q[K - 2]'(by rw [hq.2]; omega)) =
          some (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 2]'hlenB) := by
        rw [hq_km2]; exact projBlockElem_embBlock _ _ _ _ _
      obtain ⟨_, hproj_x'⟩ := projBlock_SStep_of_both_some (by omega) hK4 hjb hq
        hrowB.1 hproj_rot hkm2_s hq3
      have hbl_eq : blockLoop (6 * m) j (canonLoop (SStep q)) =
          canonLoop (SStep ((selW6m m hm).row (blockLoop (6 * m) j L)).1) := by
        have hr1 : projBlock (6 * m) j (canonLoop (SStep q)) ~r projBlock (6 * m) j (SStep q) :=
          projBlock_isRotated (canonLoop_isRotated (SStep q)).symm
        rw [hproj_x'] at hr1
        exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
          (SStep_isPerm (by omega) hrowB.1)).mpr hr1
      rw [hbl_eq]
      exact ((selW6m m hm).closed_S (blockLoop (6 * m) j L) hbl_canon hrt_S).2
  rw [activeLayer_eq_some_iff]
  exact ⟨hj_lt, hj_neD', fun i hi => by rw [hother i hi]; exact hprev i hi⟩

/-- `nextSlice` maps `layerSlices j σ` into `layerSlices j σ`, AND matches edge endpoints `e.v = e'.u`! -/
theorem nextSlice_closed_and_edge (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} {σ : List (Fin K)}
    {s : List (Fin K) × SliceTag} (hs : s ∈ layerSlices m hm r hr K hK j σ) :
    let s' := nextSlice m hm r hr K hK s
    s' ∈ layerSlices m hm r hr K hK j σ ∧
    (edgeOfRowTag ((iterW6mLift m hm r hr K hK).row s.1).1
        ((iterW6mLift m hm r hr K hK).row s.1).2 s.2).v =
    (edgeOfRowTag ((iterW6mLift m hm r hr K hK).row s'.1).1
        ((iterW6mLift m hm r hr K hK).row s'.1).2 s'.2).u := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  rcases s with ⟨L, tag⟩
  obtain ⟨hL, hact, htag, hsig⟩ := (mem_layerSlices_iff m hm r hr K hK j σ (L, tag)).mp hs
  set row := (iterW6mLift m hm r hr K hK).row L
  have hq : IsPerm K row.1 := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
  cases hrt : row.2 with
  | D => rw [hrt] at htag; simp [tagsOfRowType] at htag
  | F =>
    rw [hrt] at htag
    simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
    obtain ⟨port, hport, rfl⟩ := htag
    obtain ⟨hlast, hact'⟩ := layer_F_step_info m hm r hr K hK hL hact hrt
    by_cases hp0 : port = 0
    · subst hp0
      have hnext : nextSlice m hm r hr K hK (L, .ins 0) = (L, .ins (K - 1)) := by
        unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]; simp
      rw [hnext]
      refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, ?_⟩, ?_⟩
      · rw [hrt]; exact List.mem_map.mpr ⟨K - 1, List.mem_range.mpr (by omega), rfl⟩
      · rw [tagSigma_F_zero hK4 hq.2 hlast]; exact hsig
      · dsimp only [edgeOfRowTag]
        have hrt' : ((iterW6mLift m hm r hr K hK).row L).2 = .F := hrt
        rw [hrt']; exact insSlice_F_zero_v hK4 hq.2
    · have hnext : nextSlice m hm r hr K hK (L, .ins port) =
          (canonLoop (FStep row.1), .ins (port - 1)) := by
        unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]; simp [hp0]; rfl
      rw [hnext]
      have hcl := (iterW6mLift m hm r hr K hK).closed_F L hL hrt
      have hL' : IsCanonLoop K (canonLoop (FStep row.1)) := canonLoop_isCanonLoop (FStep_isPerm hq)
      have htag' : SliceTag.ins (port - 1) ∈
          tagsOfRowType K ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep row.1))).2 := by
        cases hc' : ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep row.1))).2 with
        | D => exact absurd hc' hcl.2
        | F => exact List.mem_map.mpr ⟨port - 1, List.mem_range.mpr (by omega), rfl⟩
        | S => exact List.mem_append_left _ (List.mem_map.mpr ⟨port - 1, List.mem_range.mpr (by omega), rfl⟩)
      refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL', hact', htag', ?_⟩, ?_⟩
      · rw [hcl.1, tagSigma_F_pos hK4 hq.2 hlast (by omega) hport]; exact hsig
      · dsimp only [edgeOfRowTag]
        rw [hcl.1, insSlice_F_pos_v hK4 hq.2 (by omega) hport]
        rw [insSlice_u hK4 ((FStep_perm _).length_eq.trans hq.2) (by omega),
            insSlice_u hK4 ((FStep_perm _).length_eq.trans hq.2) (by cases ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep row.1))).2 <;> dsimp only <;> omega)]
  | S =>
    rw [hrt] at htag
    obtain ⟨hkm2, hact'⟩ := layer_S_step_info m hm r hr K hK hL hact hrt
    have hcl := (iterW6mLift m hm r hr K hK).closed_S L hL hrt
    have hL' : IsCanonLoop K (canonLoop (SStep row.1)) :=
      canonLoop_isCanonLoop (SStep_isPerm (by omega) hq)
    cases tag with
    | repKm2 =>
      have hnext : nextSlice m hm r hr K hK (L, .repKm2) = (L, .repKm1) := by
        unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]
      rw [hnext]
      refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, hsig⟩, ?_⟩
      · rw [hrt]; simp [tagsOfRowType]
      · dsimp only [edgeOfRowTag]
        rw [repSlice_v hK4 hq.2 (K - 2), repSlice_u hK4 hq.2 (K - 1), show K - 2 + 1 = K - 1 by omega]
    | repKm1 =>
      have hnext : nextSlice m hm r hr K hK (L, .repKm1) = (L, .ins (K - 1)) := by
        unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]
      rw [hnext]
      refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, ?_⟩, ?_⟩
      · rw [hrt]; exact List.mem_append_left _ (List.mem_map.mpr ⟨K - 1, List.mem_range.mpr (by omega), rfl⟩)
      · rw [(tagSigma_S_detour hK4 hq.2 hkm2).1]; exact hsig
      · dsimp only [edgeOfRowTag]
        have hrt' : ((iterW6mLift m hm r hr K hK).row L).2 = .S := hrt
        rw [hrt']; dsimp only; exact repSlice_km1_v_eq_ins_km1_u hK4 hq.2 (by omega)
    | ins port =>
      simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag
      obtain ⟨p', hp', hpeq⟩ := htag
      have hport : port < K := by cases hpeq; exact hp'
      by_cases hlt : port ≤ K - 3
      · have hnext : nextSlice m hm r hr K hK (L, .ins port) =
            (canonLoop (SStep row.1), .ins (port + 1)) := by
          unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]; simp [hlt]; rfl
        rw [hnext]
        have htag' : SliceTag.ins (port + 1) ∈
            tagsOfRowType K ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 := by
          cases hc' : ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 with
          | D => exact absurd hc' hcl.2
          | F => exact List.mem_map.mpr ⟨port + 1, List.mem_range.mpr (by omega), rfl⟩
          | S => exact List.mem_append_left _ (List.mem_map.mpr ⟨port + 1, List.mem_range.mpr (by omega), rfl⟩)
        refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL', hact', htag', ?_⟩, ?_⟩
        · rw [hcl.1, tagSigma_S_lt hK4 hq.2 hkm2 hlt]; exact hsig
        · dsimp only [edgeOfRowTag]
          rw [hcl.1, insSlice_S_lt_v hK4 hq.2 hlt]
          rw [insSlice_u hK4 ((SStep_perm _ (by rw [hq.2]; omega)).length_eq.trans hq.2) (by omega),
              insSlice_u hK4 ((SStep_perm _ (by rw [hq.2]; omega)).length_eq.trans hq.2) (by cases ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 <;> dsimp only <;> omega)]
      · by_cases hkm : port = K - 2
        · subst hkm
          have hnext : nextSlice m hm r hr K hK (L, .ins (K - 2)) = (L, .repKm2) := by
            unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]; simp [hlt]
          rw [hnext]
          refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, hsig⟩, ?_⟩
          · rw [hrt]; simp [tagsOfRowType]
          · dsimp only [edgeOfRowTag]; exact insSlice_S_km2_v hK4 hq.2
        · have hkm1 : port = K - 1 := by omega
          subst hkm1
          have hnext : nextSlice m hm r hr K hK (L, .ins (K - 1)) =
              (canonLoop (SStep row.1), .ins 0) := by
            unfold nextSlice; dsimp only; change (match row.2 with | _ => _) = _; rw [hrt]; simp [hlt, hkm]; rfl
          rw [hnext]
          have htag' : SliceTag.ins 0 ∈
              tagsOfRowType K ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 := by
            cases hc' : ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 with
            | D => exact absurd hc' hcl.2
            | F => exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
            | S => exact List.mem_append_left _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)
          refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL', hact', htag', ?_⟩, ?_⟩
          · rw [hcl.1, (tagSigma_S_detour hK4 hq.2 hkm2).2, ← (tagSigma_S_detour hK4 hq.2 hkm2).1]
            exact hsig
          · dsimp only [edgeOfRowTag]
            rw [hcl.1, insSlice_S_km1_v hK4 hq.2]
            rw [insSlice_u hK4 ((SStep_perm _ (by rw [hq.2]; omega)).length_eq.trans hq.2) (by omega),
                insSlice_u hK4 ((SStep_perm _ (by rw [hq.2]; omega)).length_eq.trans hq.2) (by cases ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep row.1))).2 <;> dsimp only <;> omega)]

/-- Helper: in `W_{6m}`, no `'F'`-row and `'S'`-row can collide under `FStep x1 = SStep x2`! -/
theorem not_W6m_FStep_eq_SStep {m : Nat} (hm : 1 ≤ m) {L1 L2 : List (Fin (6 * m))}
    (hF1 : letI : NeZero (6 * m) := ⟨by omega⟩; ((selW6m m hm).row L1).2 = .F)
    (hS2 : letI : NeZero (6 * m) := ⟨by omega⟩; ((selW6m m hm).row L2).2 = .S) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    FStep ((selW6m m hm).row L1).1 ≠ SStep ((selW6m m hm).row L2).1 := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  dsimp only [selW6m] at hF1 hS2 ⊢
  intro heq
  cases hf1 : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L1)) with
  | none => simp [hf1] at hF1
  | some p1 =>
    cases hf2 : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L2)) with
    | none => simp [hf2] at hS2
    | some p2 =>
      rw [hf1] at hF1 heq; rw [hf2] at hS2 heq
      obtain ⟨k1, hk1, t1, ht1, hp1, ht1_eq⟩ := (mem_W6mRows_iff m hm p1.1 p1.2).mp (List.mem_of_find?_eq_some hf1)
      obtain ⟨k2, hk2, t2, ht2, hp2, ht2_eq⟩ := (mem_W6mRows_iff m hm p2.1 p2.2).mp (List.mem_of_find?_eq_some hf2)
      have ht1_lt : t1 < 6 * m - 3 := by
        by_contra hge
        have h1 : t1 = 6 * m - 3 := by omega
        rw [h1] at ht1_eq; simp at ht1_eq; rw [ht1_eq] at hF1; cases hF1
      have ht2_eq' : t2 = 6 * m - 3 := by
        by_contra hne
        simp [hne] at ht2_eq; rw [ht2_eq] at hS2; cases hS2
      subst ht2_eq'
      rw [hp1, hp2, FStep_W6mState, SStep_W6mState] at heq
      have hdisj := W6m_loop_disjoint m hm hk1 (Nat.mod_lt (k2 + 1) (by omega))
        (by omega : t1 + 1 < 6 * m - 2) (by omega : 0 < 6 * m - 2)
        (by rw [heq])
      omega

/-- `nextSlice` is injective on `layerSlices j σ`! -/
theorem nextSlice_inj (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} {σ : List (Fin K)}
    {s1 s2 : List (Fin K) × SliceTag}
    (hs1 : s1 ∈ layerSlices m hm r hr K hK j σ)
    (hs2 : s2 ∈ layerSlices m hm r hr K hK j σ)
    (heq : nextSlice m hm r hr K hK s1 = nextSlice m hm r hr K hK s2) :
    s1 = s2 := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  rcases s1 with ⟨L1, tag1⟩
  rcases s2 with ⟨L2, tag2⟩
  obtain ⟨hL1, hact1, htag1, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1
  obtain ⟨hL2, hact2, htag2, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs2
  obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L1 j).mp hact1
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  set row1 := (iterW6mLift m hm r hr K hK).row L1
  set row2 := (iterW6mLift m hm r hr K hK).row L2
  have hq1 := ((iterW6mLift m hm r hr K hK).row_perm L1 hL1).1
  have hq2 := ((iterW6mLift m hm r hr K hK).row_perm L2 hL2).1
  -- Key helper: `FStep q1` and `SStep q2` cannot be equal for Layer-`j` rows `row1 (.F)` and `row2 (.S)`!
  have hcross : ∀ (La Lb : List (Fin K)),
      IsCanonLoop K La → activeLayer m hm r La = some j →
      ((iterW6mLift m hm r hr K hK).row La).2 = .F →
      IsCanonLoop K Lb → activeLayer m hm r Lb = some j →
      ((iterW6mLift m hm r hr K hK).row Lb).2 = .S →
      FStep ((iterW6mLift m hm r hr K hK).row La).1 ≠ SStep ((iterW6mLift m hm r hr K hK).row Lb).1 := by
    intro La Lb hLa hactA hFA hLb hactB hSB hFS_eq
    set qa := ((iterW6mLift m hm r hr K hK).row La).1
    set qb := ((iterW6mLift m hm r hr K hK).row Lb).1
    have hqa := ((iterW6mLift m hm r hr K hK).row_perm La hLa).1
    have hqb := ((iterW6mLift m hm r hr K hK).row_perm Lb hLb).1
    have hlast_in := (layer_F_step_info m hm r hr K hK hLa hactA hFA).1
    have hkm2_in := (layer_S_step_info m hm r hr K hK hLb hactB hSB).1
    -- Read off `qa[0] = (FStep qa)[K - 2] = (SStep qb)[K - 2] = qb[K - 2] ∈ B_j`
    -- and `qb[K - 3] = (SStep qb)[K - 1] = (FStep qa)[K - 1] = qa[K - 1] ∈ B_j`!
    obtain ⟨aa, lasta, mida, hqa_sp, hFa_sp, hmida_len, haa_eq, hlasta_eq⟩ := split_first_last hK4 hqa.2
    obtain ⟨preb, ub, vb, wb, hqb_sp, hSb_sp, hpreb_len, hub_eq, hvb_eq, _⟩ := split_last3 hK4 hqb.2
    have hkm2_eq : aa = vb := by
      have h1 : (FStep qa)[K - 2]'(by rw [(FStep_perm _).length_eq, hqa.2]; omega) = aa := by
        have ht : (mida ++ [aa, lasta])[K - 2]'(by simp [hmida_len]) = aa := by
          rw [List.getElem_append_right (by omega)]; simp [hmida_len]
        have hF' : FStep qa = mida ++ [aa, lasta] := hFa_sp
        simpa [hF'] using ht
      have h2 : (SStep qb)[K - 2]'(by rw [(SStep_perm _ (by rw [hqb.2]; omega)).length_eq, hqb.2]; omega) = vb := by
        have ht : ([wb] ++ preb ++ [vb, ub])[K - 2]'(by simp [hpreb_len]; omega) = vb := by
          rw [List.getElem_append_right (by simp [hpreb_len]; omega)]
          simp [hpreb_len, show K - 2 - (K - 3 + 1) = 0 by omega]
        have hS' : SStep qb = [wb] ++ preb ++ [vb, ub] := hSb_sp
        simpa [hS'] using ht
      rw [← h1, ← h2]; simp [hFS_eq]
    have hkm1_eq : lasta = ub := by
      have h1 : (FStep qa)[K - 1]'(by rw [(FStep_perm _).length_eq, hqa.2]; omega) = lasta := by
        have ht : (mida ++ [aa, lasta])[K - 1]'(by simp [hmida_len]; omega) = lasta := by
          rw [List.getElem_append_right (by omega)]
          simp [hmida_len, show K - 1 - (K - 2) = 1 by omega]
        have hF' : FStep qa = mida ++ [aa, lasta] := hFa_sp
        simpa [hF'] using ht
      have h2 : (SStep qb)[K - 1]'(by rw [(SStep_perm _ (by rw [hqb.2]; omega)).length_eq, hqb.2]; omega) = ub := by
        have ht : ([wb] ++ preb ++ [vb, ub])[K - 1]'(by simp [hpreb_len]; omega) = ub := by
          rw [List.getElem_append_right (by simp [hpreb_len]; omega)]
          simp [hpreb_len, show K - 1 - (K - 3 + 1) = 1 by omega]
        have hS' : SStep qb = [wb] ++ preb ++ [vb, ub] := hSb_sp
        simpa [hS'] using ht
      rw [← h1, ← h2]; simp [hFS_eq]
    have hqa0_some : (projBlockElem (6 * m) j (qa[0]'(by rw [hqa.2]; omega))).isSome = true := by
      rw [← inBlock_iff_projBlockElem_isSome, ← haa_eq, hkm2_eq, hvb_eq]; exact hkm2_in
    have hqal_some : (projBlockElem (6 * m) j (qa[K - 1]'(by rw [hqa.2]; omega))).isSome = true := by
      rw [← inBlock_iff_projBlockElem_isSome]; exact hlast_in
    have hqb3_some : (projBlockElem (6 * m) j (qb[K - 3]'(by rw [hqb.2]; omega))).isSome = true := by
      rw [← inBlock_iff_projBlockElem_isSome, ← hub_eq, ← hkm1_eq, hlasta_eq]; exact hlast_in
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hqa0_some
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp hqal_some
    obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hqb3_some
    -- Project `FStep qa = SStep qb` to block `B_j`!
    have hproj_F : projBlock (6 * m) j (FStep qa) = FStep (projBlock (6 * m) j qa) :=
      projBlock_FStep_of_both_some hK4 hqa.2 ha' hl'
    -- Identify `projBlock b j qa = rowBa.1` and `projBlock b j (SStep qb) = SStep rowBb.1`!
    have hblA := canonLoop_isCanonLoop (projBlock_isPerm hjb hLa.1)
    have hblB := canonLoop_isCanonLoop (projBlock_isPerm hjb hLb.1)
    have hrowBa := (selW6m m hm).row_perm (blockLoop (6 * m) j La) hblA
    have hrowBb := (selW6m m hm).row_perm (blockLoop (6 * m) j Lb) hblB
    obtain ⟨_, hneDA, _⟩ := (activeLayer_eq_some_iff m hm r La j).mp hactA
    obtain ⟨_, hneDB, _⟩ := (activeLayer_eq_some_iff m hm r Lb j).mp hactB
    have hrtA : ((selW6m m hm).row (blockLoop (6 * m) j La)).2 = .F := by
      dsimp only [iterW6mLift] at hFA
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j La)).2 with
      | D => exact absurd hc hneDA
      | F => rfl
      | S => rw [iterW6mRow_eq_S hm hK hactA hj_lt hjb hc (by rw [hrowBa.1.2]; omega)] at hFA; cases hFA
    have hrtB : ((selW6m m hm).row (blockLoop (6 * m) j Lb)).2 = .S := by
      dsimp only [iterW6mLift] at hSB
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j Lb)).2 with
      | D => exact absurd hc hneDB
      | F => rw [iterW6mRow_eq_F hm hK hactB hj_lt hjb hc (by rw [hrowBb.1.2]; omega)] at hSB; cases hSB
      | S => rfl
    have hlenBa : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j La)).1.length := by rw [hrowBa.1.2]; omega
    have hlenBb : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j Lb)).1.length := by rw [hrowBb.1.2]; omega
    have hqa_last : qa[K - 1]'(by rw [hqa.2]; omega) =
        embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa) := by
      have h1 : qa = pinAt La (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa)) (K - 1) := by
        dsimp only [qa, iterW6mLift]; rw [iterW6mRow_eq_F hm hK hactA hj_lt hjb hrtA hlenBa]
      simpa [h1] using pinAt_getElem hLa.1 (embBlock (6 * m) K j hjb
        (((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa)) (by omega : K - 1 < K)
    have hqb_km2 : qb[K - 2]'(by rw [hqb.2]; omega) =
        embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j Lb)).1[6 * m - 2]'hlenBb) := by
      have h1 : qb = pinAt Lb (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j Lb)).1[6 * m - 2]'hlenBb)) (K - 2) := by
        dsimp only [qb, iterW6mLift]; rw [iterW6mRow_eq_S hm hK hactB hj_lt hjb hrtB hlenBb]
      simpa [h1] using pinAt_getElem hLb.1 (embBlock (6 * m) K j hjb
        (((selW6m m hm).row (blockLoop (6 * m) j Lb)).1[6 * m - 2]'hlenBb)) (by omega : K - 2 < K)
    have hproj_qa : projBlock (6 * m) j qa = ((selW6m m hm).row (blockLoop (6 * m) j La)).1 := by
      have hpr_rot : projBlock (6 * m) j qa ~r ((selW6m m hm).row (blockLoop (6 * m) j La)).1 :=
        (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm La hLa).2).trans
          ((canonLoop_isRotated _).trans hrowBa.2.symm)
      have hpr_perm := projBlock_isPerm hjb hqa
      have hls : projBlockElem (6 * m) j lasta =
          some (((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa) := by
        rw [hlasta_eq, hqa_last]; exact projBlockElem_embBlock _ _ _ _ _
      have hdec : projBlock (6 * m) j qa = (aa :: mida).filterMap (projBlockElem (6 * m) j) ++
          [((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa] := by
        have hqa_sp' : qa = aa :: mida ++ [lasta] := hqa_sp
        unfold projBlock; rw [hqa_sp', List.filterMap_append]; simp [List.filterMap_cons, hls]
      have hlp : ((aa :: mida).filterMap (projBlockElem (6 * m) j)).length = 6 * m - 1 := by
        have := hpr_perm.2; rw [hdec] at this; simp at this; omega
      have hlast_pr : (projBlock (6 * m) j qa)[6 * m - 1]'(by rw [hpr_perm.2]; omega) =
          ((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa := by
        have ht : ((aa :: mida).filterMap (projBlockElem (6 * m) j) ++
            [((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa])[6 * m - 1]'(by simp [hlp]) =
            ((selW6m m hm).row (blockLoop (6 * m) j La)).1[6 * m - 1]'hlenBa := by
          rw [List.getElem_append_right (by omega)]; simp [hlp]
        simpa [hdec] using ht
      exact (eq_pinAt_of_isRotated hrowBa.1 hpr_perm hpr_rot (by omega) hlast_pr).trans
        (eq_pinAt_of_isRotated hrowBa.1 hrowBa.1 (List.IsRotated.refl _) (by omega) rfl).symm
    have hproj_Sb : projBlock (6 * m) j (SStep qb) = SStep ((selW6m m hm).row (blockLoop (6 * m) j Lb)).1 := by
      have hpr_rot : projBlock (6 * m) j qb ~r ((selW6m m hm).row (blockLoop (6 * m) j Lb)).1 :=
        (projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm Lb hLb).2).trans
          ((canonLoop_isRotated _).trans hrowBb.2.symm)
      have hkm2_s : projBlockElem (6 * m) j (qb[K - 2]'(by rw [hqb.2]; omega)) =
          some (((selW6m m hm).row (blockLoop (6 * m) j Lb)).1[6 * m - 2]'hlenBb) := by
        rw [hqb_km2]; exact projBlockElem_embBlock _ _ _ _ _
      exact (projBlock_SStep_of_both_some (by omega) hK4 hjb hqb hrowBb.1 hpr_rot hkm2_s hu').2
    have hcoll : FStep ((selW6m m hm).row (blockLoop (6 * m) j La)).1 =
        SStep ((selW6m m hm).row (blockLoop (6 * m) j Lb)).1 := by
      rw [← hproj_qa, ← hproj_F, hFS_eq, hproj_Sb]
    exact not_W6m_FStep_eq_SStep hm hrtA hrtB hcoll
  -- Now case-split on `(row1.2, tag1)` vs `(row2.2, tag2)`!
  cases hrt1 : row1.2 <;> cases hrt2 : row2.2
  · rw [hrt1] at htag1; simp [tagsOfRowType] at htag1
  · rw [hrt1] at htag1; simp [tagsOfRowType] at htag1
  · rw [hrt1] at htag1; simp [tagsOfRowType] at htag1
  · rw [hrt2] at htag2; simp [tagsOfRowType] at htag2
  · -- F vs F
    rw [hrt1] at htag1; rw [hrt2] at htag2
    simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag1 htag2
    obtain ⟨p1, hp1, rfl⟩ := htag1
    obtain ⟨p2, hp2, rfl⟩ := htag2
    unfold nextSlice at heq; dsimp only at heq; rw [hrt1, hrt2] at heq
    by_cases h1 : p1 = 0 <;> by_cases h2 : p2 = 0
    · subst h1; subst h2; simp only [↓reduceIte] at heq
      obtain ⟨rfl, _⟩ := Prod.mk.inj heq; rfl
    · simp only [h1, h2, ↓reduceIte] at heq
      obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
    · simp only [h1, h2, ↓reduceIte] at heq
      obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
    · simp only [h1, h2, ↓reduceIte] at heq
      obtain ⟨hL_eq, ht⟩ := Prod.mk.inj heq
      have hp_eq : p1 = p2 := by have := SliceTag.ins.inj ht; omega
      have hcl1 := ((iterW6mLift m hm r hr K hK).closed_F L1 hL1 hrt1).1
      have hcl2 := ((iterW6mLift m hm r hr K hK).closed_F L2 hL2 hrt2).1
      have hF_eq : FStep row1.1 = FStep row2.1 := by
        rw [← hcl1, ← hcl2, hL_eq]
      have hq_eq : row1.1 = row2.1 := FStep_inj hK4 hq1.2 hq2.2 hF_eq
      have hL12 : L1 = L2 := by
        have hr1 := ((iterW6mLift m hm r hr K hK).row_perm L1 hL1).2
        have hr2 := ((iterW6mLift m hm r hr K hK).row_perm L2 hL2).2
        exact isCanonLoop_eq_of_isRotated hL1 hL2 (hr1.symm.trans (hq_eq ▸ hr2))
      rw [hL12, hp_eq]
  · -- F vs S
    rw [hrt1] at htag1; rw [hrt2] at htag2
    simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag1
    obtain ⟨p1, hp1, rfl⟩ := htag1
    unfold nextSlice at heq; dsimp only at heq; rw [hrt1, hrt2] at heq
    cases tag2 with
    | repKm2 =>
      by_cases h1 : p1 = 0 <;> simp only [h1, ↓reduceIte] at heq <;>
        exact absurd (Prod.mk.inj heq).2 (by simp)
    | repKm1 =>
      by_cases h1 : p1 = 0
      · simp only [h1, ↓reduceIte] at heq
        obtain ⟨rfl, _⟩ := Prod.mk.inj heq
        rw [hrt1] at hrt2; cases hrt2
      · simp only [h1, ↓reduceIte] at heq
        obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
    | ins p2 =>
      simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag2
      obtain ⟨p2', hp2', hpeq2⟩ := htag2; have hp2 : p2 < K := by cases hpeq2; exact hp2'
      by_cases h1 : p1 = 0
      · simp only [h1, ↓reduceIte] at heq
        by_cases h2a : p2 ≤ K - 3
        · simp only [h2a, ↓reduceIte] at heq
          obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h2a, ↓reduceIte] at heq
          by_cases h2b : p2 = K - 2
          · simp only [h2b, ↓reduceIte] at heq
            exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h2b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
      · simp only [h1, ↓reduceIte] at heq
        by_cases h2a : p2 ≤ K - 3
        · simp only [h2a, ↓reduceIte] at heq
          obtain ⟨hL_eq, _⟩ := Prod.mk.inj heq
          have hcl1 := ((iterW6mLift m hm r hr K hK).closed_F L1 hL1 hrt1).1
          have hcl2 := ((iterW6mLift m hm r hr K hK).closed_S L2 hL2 hrt2).1
          exact absurd (by rw [← hcl1, ← hcl2, hL_eq]) (hcross L1 L2 hL1 hact1 hrt1 hL2 hact2 hrt2)
        · simp only [h2a, ↓reduceIte] at heq
          by_cases h2b : p2 = K - 2
          · simp only [h2b, ↓reduceIte] at heq
            exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h2b, ↓reduceIte] at heq
            obtain ⟨hL_eq, _⟩ := Prod.mk.inj heq
            have hcl1 := ((iterW6mLift m hm r hr K hK).closed_F L1 hL1 hrt1).1
            have hcl2 := ((iterW6mLift m hm r hr K hK).closed_S L2 hL2 hrt2).1
            exact absurd (by rw [← hcl1, ← hcl2, hL_eq]) (hcross L1 L2 hL1 hact1 hrt1 hL2 hact2 hrt2)
  · rw [hrt2] at htag2; simp [tagsOfRowType] at htag2
  · -- S vs F (symmetric to F vs S!)
    rw [hrt2] at htag2; rw [hrt1] at htag1
    simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag2
    obtain ⟨p2, hp2, rfl⟩ := htag2
    unfold nextSlice at heq; dsimp only at heq; rw [hrt1, hrt2] at heq
    cases tag1 with
    | repKm2 =>
      by_cases h2 : p2 = 0 <;> simp only [h2, ↓reduceIte] at heq <;>
        exact absurd (Prod.mk.inj heq).2 (by simp)
    | repKm1 =>
      by_cases h2 : p2 = 0
      · simp only [h2, ↓reduceIte] at heq
        obtain ⟨rfl, _⟩ := Prod.mk.inj heq
        rw [hrt1] at hrt2; cases hrt2
      · simp only [h2, ↓reduceIte] at heq
        obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
    | ins p1 =>
      simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag1
      obtain ⟨p1', hp1', hpeq1⟩ := htag1; have hp1 : p1 < K := by cases hpeq1; exact hp1'
      by_cases h2 : p2 = 0
      · simp only [h2, ↓reduceIte] at heq
        by_cases h1a : p1 ≤ K - 3
        · simp only [h1a, ↓reduceIte] at heq
          obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h1a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2
          · simp only [h1b, ↓reduceIte] at heq
            exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
      · simp only [h2, ↓reduceIte] at heq
        by_cases h1a : p1 ≤ K - 3
        · simp only [h1a, ↓reduceIte] at heq
          obtain ⟨hL_eq, _⟩ := Prod.mk.inj heq
          have hcl1 := ((iterW6mLift m hm r hr K hK).closed_S L1 hL1 hrt1).1
          have hcl2 := ((iterW6mLift m hm r hr K hK).closed_F L2 hL2 hrt2).1
          exact absurd (by rw [← hcl1, ← hcl2, hL_eq]) (hcross L2 L1 hL2 hact2 hrt2 hL1 hact1 hrt1)
        · simp only [h1a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2
          · simp only [h1b, ↓reduceIte] at heq
            exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, ↓reduceIte] at heq
            obtain ⟨hL_eq, _⟩ := Prod.mk.inj heq
            have hcl1 := ((iterW6mLift m hm r hr K hK).closed_S L1 hL1 hrt1).1
            have hcl2 := ((iterW6mLift m hm r hr K hK).closed_F L2 hL2 hrt2).1
            exact absurd (by rw [← hcl1, ← hcl2, hL_eq]) (hcross L2 L1 hL2 hact2 hrt2 hL1 hact1 hrt1)
  · -- S vs S
    rw [hrt1] at htag1; rw [hrt2] at htag2
    unfold nextSlice at heq; dsimp only at heq; rw [hrt1, hrt2] at heq
    have hS_inj_L : canonLoop (SStep row1.1) = canonLoop (SStep row2.1) → L1 = L2 := by
      intro hL_eq
      have hcl1 := ((iterW6mLift m hm r hr K hK).closed_S L1 hL1 hrt1).1
      have hcl2 := ((iterW6mLift m hm r hr K hK).closed_S L2 hL2 hrt2).1
      have hS_eq : SStep row1.1 = SStep row2.1 := by rw [← hcl1, ← hcl2, hL_eq]
      have hq_eq := SStep_inj hK4 hq1.2 hq2.2 hS_eq
      have hr1 := ((iterW6mLift m hm r hr K hK).row_perm L1 hL1).2
      have hr2 := ((iterW6mLift m hm r hr K hK).row_perm L2 hL2).2
      exact isCanonLoop_eq_of_isRotated hL1 hL2 (hr1.symm.trans (hq_eq ▸ hr2))
    cases tag1 with
    | repKm2 =>
      cases tag2 with
      | repKm2 => obtain ⟨rfl, _⟩ := Prod.mk.inj heq; rfl
      | repKm1 => exact absurd (Prod.mk.inj heq).2 (by simp)
      | ins p2 =>
        by_cases h2a : p2 ≤ K - 3
        · simp only [h2a, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
        · simp only [h2a, ↓reduceIte] at heq
          by_cases h2b : p2 = K - 2
          · simp only [h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
    | repKm1 =>
      cases tag2 with
      | repKm2 => exact absurd (Prod.mk.inj heq).2 (by simp)
      | repKm1 => obtain ⟨rfl, _⟩ := Prod.mk.inj heq; rfl
      | ins p2 =>
        by_cases h2a : p2 ≤ K - 3
        · simp only [h2a, ↓reduceIte] at heq
          obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h2a, ↓reduceIte] at heq
          by_cases h2b : p2 = K - 2
          · simp only [h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h2b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
    | ins p1 =>
      simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag1
      obtain ⟨p1', hp1', hpeq1⟩ := htag1; have hp1 : p1 < K := by cases hpeq1; exact hp1'
      cases tag2 with
      | repKm2 =>
        by_cases h1a : p1 ≤ K - 3
        · simp only [h1a, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
        · simp only [h1a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2
          · simp only [h1b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
      | repKm1 =>
        by_cases h1a : p1 ≤ K - 3
        · simp only [h1a, ↓reduceIte] at heq
          obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h1a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2
          · simp only [h1b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
      | ins p2 =>
        simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag2
        obtain ⟨p2', hp2', hpeq2⟩ := htag2; have hp2 : p2 < K := by cases hpeq2; exact hp2'
        by_cases h1a : p1 ≤ K - 3 <;> by_cases h2a : p2 ≤ K - 3
        · simp only [h1a, h2a, ↓reduceIte] at heq
          obtain ⟨hL_eq, ht⟩ := Prod.mk.inj heq
          have hp_eq : p1 = p2 := by have := SliceTag.ins.inj ht; omega
          rw [hS_inj_L hL_eq, hp_eq]
        · simp only [h1a, h2a, ↓reduceIte] at heq
          by_cases h2b : p2 = K - 2
          · simp only [h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h2b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h1a, h2a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2
          · simp only [h1b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, ↓reduceIte] at heq
            obtain ⟨_, ht⟩ := Prod.mk.inj heq; have := SliceTag.ins.inj ht; omega
        · simp only [h1a, h2a, ↓reduceIte] at heq
          by_cases h1b : p1 = K - 2 <;> by_cases h2b : p2 = K - 2
          · subst h1b; subst h2b; simp only [↓reduceIte] at heq
            obtain ⟨rfl, _⟩ := Prod.mk.inj heq; rfl
          · simp only [h1b, h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, h2b, ↓reduceIte] at heq; exact absurd (Prod.mk.inj heq).2 (by simp)
          · simp only [h1b, h2b, ↓reduceIte] at heq
            obtain ⟨hL_eq, _⟩ := Prod.mk.inj heq
            have hp_eq : p1 = p2 := by omega
            rw [hS_inj_L hL_eq, hp_eq]

/-- Edge list of all slices in `layerSlices j σ`. -/
noncomputable def layerSliceEdges (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) (σ : List (Fin K)) :
    List (RawEdge (K + 2)) :=
  letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  (layerSlices m hm r hr K hK j σ).map fun s =>
    let row := (iterW6mLift m hm r hr K hK).row s.1
    edgeOfRowTag row.1 row.2 s.2

/-- The complete Layer-`j` Eulerian bag for `σ ∈ allLayerSigmas j`:
all `Nat.choose (K - 2) (6m - 2)` lifted `z`-connector cycles + all slices in `layerSlices j σ`. -/
noncomputable def layerBag (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r) (σ : List (Fin K)) :
    List (RawEdge (K + 2)) :=
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  (zCyclesOf (6 * m) K j hjb σ).flatMap connCycleEdges ++
    layerSliceEdges m hm r hr K hK j σ

/-- `layerSliceEdges j σ` is `Balanced`! (Direct 10-line proof from `nextSlice_inj`!) -/
theorem layerSliceEdges_balanced (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) (j : Nat) (σ : List (Fin K)) :
    Balanced (layerSliceEdges m hm r hr K hK j σ) := by
  let _ : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  set S := layerSlices m hm r hr K hK j σ
  set f := nextSlice m hm r hr K hK
  set E := layerSliceEdges m hm r hr K hK j σ
  have hS_nd : S.Nodup := layerSlices_nodup m hm r hr K hK j σ
  have hmap_nd : (S.map f).Nodup := by
    rw [List.nodup_map_iff_inj_on hS_nd]
    intro a ha b hb hab
    exact nextSlice_inj m hm r hr K hK ha hb hab
  have hsub : ∀ x ∈ S.map f, x ∈ S := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (nextSlice_closed_and_edge m hm r hr K hK ha).1
  have hfin : (S.map f).toFinset = S.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub x hx
    · rw [List.toFinset_card_of_nodup hmap_nd, List.toFinset_card_of_nodup hS_nd, List.length_map]
  have hperm : (S.map f).Perm S :=
    (List.perm_ext_iff_of_nodup hmap_nd hS_nd).mpr fun x => by
      rw [← List.mem_toFinset, ← List.mem_toFinset, hfin]
  let uOf : List (Fin K) × SliceTag → Almanac.Word (K + 2) := fun s =>
    let row := (iterW6mLift m hm r hr K hK).row s.1
    (edgeOfRowTag row.1 row.2 s.2).u
  let vOf : List (Fin K) × SliceTag → Almanac.Word (K + 2) := fun s =>
    let row := (iterW6mLift m hm r hr K hK).row s.1
    (edgeOfRowTag row.1 row.2 s.2).v
  have hvu : S.map vOf = (S.map f).map uOf := by
    rw [List.map_map]
    refine List.map_congr_left fun s hs => ?_
    exact (nextSlice_closed_and_edge m hm r hr K hK hs).2
  have huv_perm : (E.map RawEdge.v).Perm (E.map RawEdge.u) := by
    have h1 : E.map RawEdge.v = S.map vOf := by
      dsimp only [E, layerSliceEdges, vOf]; rw [List.map_map]; rfl
    have h2 : E.map RawEdge.u = S.map uOf := by
      dsimp only [E, layerSliceEdges, uOf]; rw [List.map_map]; rfl
    rw [h1, h2, hvu]
    exact hperm.map uOf
  intro x
  unfold outDeg inDeg
  have hcnt : ∀ (l : List (RawEdge (K + 2))) (g : RawEdge (K + 2) → Almanac.Word (K + 2)),
      (l.filter (fun e => decide (g e = x))).length = ((l.map g).filter (fun y => decide (y = x))).length := by
    intro l g; rw [List.filter_map, List.length_map]; rfl
  rw [hcnt E RawEdge.u, hcnt E RawEdge.v]
  exact (huv_perm.symm.filter _).length_eq

/-- `layerBag j σ` is `EdgeOk (K - 1)` and `Balanced`! -/
theorem layerBag_ok_and_balanced (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} (hσ : σ ∈ allLayerSigmas m hm r hr K hK j) :
    (∀ e ∈ layerBag m hm r hr K hK hj σ, EdgeOk (K - 1) e) ∧
    Balanced (layerBag m hm r hr K hK hj σ) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  obtain ⟨_, hσ_len, _⟩ := (mem_allLinearPermsMj_iff hjb σ).mp (List.mem_filter.mp hσ).1
  unfold layerBag
  constructor
  · intro e he
    rw [List.mem_append] at he
    rcases he with h1 | h2
    · obtain ⟨ck, hck, he_ck⟩ := List.mem_flatMap.mp h1
      exact connCycleEdges_ok (zCyclesOf_elem_length (by omega) hjb hσ_len hck) e he_ck
    · obtain ⟨⟨L, tag⟩, hs, rfl⟩ := List.mem_map.mp h2
      obtain ⟨hL, _, htag, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
      have hrow := (iterW6mLift m hm r hr K hK).row_perm L hL
      have hneD : ((iterW6mLift m hm r hr K hK).row L).2 ≠ .D := by
        intro hD; rw [hD] at htag; simp [tagsOfRowType] at htag
      have he_in : edgeOfRowTag ((iterW6mLift m hm r hr K hK).row L).1
          ((iterW6mLift m hm r hr K hK).row L).2 tag ∈
          rowSlices ((iterW6mLift m hm r hr K hK).row L).1
            ((iterW6mLift m hm r hr K hK).row L).2 := by
        rw [← map_edgeOfRowTag_eq_rowSlices hK4 _ hneD]
        exact List.mem_map.mpr ⟨tag, htag, rfl⟩
      exact rowSlices_ok hK4 hrow.1.2 _ _ he_in
  · apply balanced_append
    · have hbf : ∀ (l : List (Almanac.Word (K + 2))),
          (∀ ck ∈ l, 0 < ck.length) → Balanced (l.flatMap connCycleEdges) := by
        intro l hl
        induction l with
        | nil => exact balanced_nil
        | cons ck cks ih =>
          rw [List.flatMap_cons]
          exact balanced_append (connCycleEdges_balanced (hl ck List.mem_cons_self))
            (ih fun c hc => hl c (List.mem_cons_of_mem _ hc))
      exact hbf _ fun ck hck => by
        rw [zCyclesOf_elem_length (by omega) hjb hσ_len hck]; omega
    · exact layerSliceEdges_balanced m hm r hr K hK j σ

/-- Every slice of every Layer-`j` loop `L` has its `tagSigma` in `allLayerSigmas j`! -/
theorem tagSigma_mem_allLayerSigmas (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r) {L : List (Fin K)}
    (hL : @IsCanonLoop K ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩ L)
    (hact : activeLayer m hm r L = some j) (tag : SliceTag) :
    letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
    tagSigma (6 * m) j K ((iterW6mLift m hm r hr K hK).row L).1 tag ∈
      allLayerSigmas m hm r hr K hK j := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  obtain ⟨_, _, hprev⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
  set q := ((iterW6mLift m hm r hr K hK).row L).1
  have hq := (iterW6mLift m hm r hr K hK).row_perm L hL
  have hrot_any : ∀ p : Nat,
      (q.rotate p).filter (notInBlock (6 * m) j) ∈ allLayerSigmas m hm r hr K hK j := by
    intro p
    have hqp : IsPerm K (q.rotate p) := isPerm_rotate hq.1 p
    have hnd : ((q.rotate p).filter (notInBlock (6 * m) j)).Nodup := hqp.1.filter _
    have hperm_fr : (q.rotate p).Perm (List.finRange K) :=
      (List.perm_ext_iff_of_nodup hqp.1 (List.nodup_finRange K)).mpr fun x =>
        ⟨fun _ => List.mem_finRange x, fun _ => mem_of_isPerm hqp x⟩
    have hlen : ((q.rotate p).filter (notInBlock (6 * m) j)).length = K - 6 * m := by
      have := (hperm_fr.filter (notInBlock (6 * m) j)).length_eq
      exact this.trans (elemsMj_length hjb)
    have hmem_Mj : (q.rotate p).filter (notInBlock (6 * m) j) ∈ allLinearPermsMj (6 * m) j K :=
      (mem_allLinearPermsMj_iff hjb _).mpr ⟨hnd, hlen, fun x hx => (List.mem_filter.mp hx).2⟩
    refine List.mem_filter.mpr ⟨hmem_Mj, decide_eq_true fun i => ?_⟩
    have hib : (i.1 + 1) * (6 * m) ≤ K := by
      have := Nat.mul_le_mul_right (6 * m) (show i.1 + 1 ≤ r by omega); omega
    -- `projBlock (6 * m) i.1 ((q.rotate p).filter (notInBlock (6 * m) j)) = projBlock (6 * m) i.1 (q.rotate p)`!
    have hproj_eq : projBlock (6 * m) i.1 ((q.rotate p).filter (notInBlock (6 * m) j)) =
        projBlock (6 * m) i.1 (q.rotate p) := by
      unfold projBlock
      induction (q.rotate p) with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filter_cons, List.filterMap_cons]
        cases hnb : notInBlock (6 * m) j x with
        | true => simp [List.filterMap_cons, ih]
        | false =>
          have hin : inBlock (6 * m) j x = true := by unfold notInBlock at hnb; simp at hnb; exact hnb
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hin)
          have hxe := (projBlockElem_eq_some_iff (6 * m) j hjb x a).mp ha
          have hnone : projBlockElem (6 * m) i.1 x = none := by
            rw [hxe]; exact projBlockElem_embBlock_ne (by have := i.2; omega) hjb a
          simp [hnone, ih]
    have hbl_eq : blockLoop (6 * m) i.1 ((q.rotate p).filter (notInBlock (6 * m) j)) =
        blockLoop (6 * m) i.1 L := by
      unfold blockLoop
      rw [hproj_eq]
      have hr1 : projBlock (6 * m) i.1 (q.rotate p) ~r projBlock (6 * m) i.1 q :=
        projBlock_isRotated ⟨p, rfl⟩ |>.symm
      have hr2 : projBlock (6 * m) i.1 q ~r projBlock (6 * m) i.1 L :=
        projBlock_isRotated hq.2
      exact (canonLoop_eq_iff (projBlock_isPerm hib hqp) (projBlock_isPerm hib hL.1)).mpr
        (hr1.trans hr2)
    rw [hbl_eq]
    exact hprev i.1 i.2
  cases tag with
  | ins port => exact hrot_any port
  | repKm2 => exact hrot_any (K - 2)
  | repKm1 => exact hrot_any (K - 2)

/-- Exact sum of body lengths across all `σ ∈ allLayerSigmas j` of `layerBag j σ`! -/
theorem layerBags_body_sum (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r) :
    letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
    let sigmas := allLayerSigmas m hm r hr K hK j
    (sigmas.map (fun σ => ((layerBag m hm r hr K hK hj σ).map (fun e => e.body.length)).sum)).sum =
      (K - 1) * (sigmas.length * Nat.choose (K - 2) (6 * m - 2)) +
      (((allCanonLoops K).filter (fun L => activeLayer m hm r L == some j)).map
        (fun L => ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
          ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  set sigmas := allLayerSigmas m hm r hr K hK j
  have hsum_flat : ∀ {α : Type} (l : List α) (f : α → List Nat),
      (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := fun l f => by
    induction l with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]
  have hsum_add : ∀ {α : Type} (l : List α) (f g : α → Nat),
      (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := fun l f g => by
    induction l with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega
  -- Split each `layerBag j σ` into `zCycles` part + `layerSliceEdges` part!
  have hsplit : (sigmas.map (fun σ =>
        ((layerBag m hm r hr K hK hj σ).map (fun e => e.body.length)).sum)).sum =
      (sigmas.map (fun σ => (((zCyclesOf (6 * m) K j hjb σ).flatMap connCycleEdges).map
        (fun e => e.body.length)).sum)).sum +
      (sigmas.map (fun σ => ((layerSliceEdges m hm r hr K hK j σ).map
        (fun e => e.body.length)).sum)).sum := by
    rw [← hsum_add]
    congr 1; refine List.map_congr_left fun σ _ => ?_
    unfold layerBag; rw [List.map_append, List.sum_append]
  dsimp only
  rw [hsplit]
  congr 1
  · -- Part 1: every `σ ∈ sigmas` has `Nat.choose (K - 2) (6 * m - 2)` cycles, each of body sum `K - 1`!
    have hzc : ∀ σ ∈ sigmas,
        (((zCyclesOf (6 * m) K j hjb σ).flatMap connCycleEdges).map (fun e => e.body.length)).sum =
          (K - 1) * Nat.choose (K - 2) (6 * m - 2) := by
      intro σ hσ
      obtain ⟨_, hσ_len, _⟩ := (mem_allLinearPermsMj_iff hjb σ).mp (List.mem_filter.mp hσ).1
      rw [List.map_flatMap, hsum_flat]
      have heach : ∀ ck ∈ zCyclesOf (6 * m) K j hjb σ,
          ((connCycleEdges ck).map (fun e => e.body.length)).sum = K - 1 := fun ck hck =>
        connCycleEdges_body_sum (zCyclesOf_elem_length (by omega) hjb hσ_len hck)
      rw [List.map_congr_left heach, List.map_const', List.sum_replicate, smul_eq_mul,
        zCyclesOf_length (by omega) hjb hσ_len, Nat.mul_comm]
    rw [List.map_congr_left hzc, List.map_const', List.sum_replicate, smul_eq_mul]; ring
  · -- Part 2: `sigmas.flatMap (layerSlices j ·)` is a permutation of ALL `(L, tag)` in Layer `j`!
    set layerLoops := (allCanonLoops K).filter (fun L => activeLayer m hm r L == some j)
    let allLJs : List (List (Fin K) × SliceTag) := layerLoops.flatMap fun L =>
      (tagsOfRowType K ((iterW6mLift m hm r hr K hK).row L).2).map (fun tag => (L, tag))
    let bodyOf : List (Fin K) × SliceTag → Nat := fun s =>
      let row := (iterW6mLift m hm r hr K hK).row s.1
      (edgeOfRowTag row.1 row.2 s.2).body.length
    have hLHS : (sigmas.map (fun σ => ((layerSliceEdges m hm r hr K hK j σ).map
        (fun e => e.body.length)).sum)).sum =
        ((sigmas.flatMap (layerSlices m hm r hr K hK j)).map bodyOf).sum := by
      rw [List.map_flatMap, hsum_flat]
      congr 1; refine List.map_congr_left fun σ _ => ?_
      simp [layerSliceEdges, bodyOf, List.map_map, Function.comp_def]
    have hRHS : (layerLoops.map (fun L =>
        ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
          ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum =
        (allLJs.map bodyOf).sum := by
      dsimp only [allLJs]
      rw [List.map_flatMap, hsum_flat]
      congr 1; refine List.map_congr_left fun L hL => ?_
      obtain ⟨hL_mem, hact_b⟩ := List.mem_filter.mp hL
      have hL' := (mem_allCanonLoops_iff L).mp hL_mem
      have hact : activeLayer m hm r L = some j := by simpa using hact_b
      have hneD : ((iterW6mLift m hm r hr K hK).row L).2 ≠ .D := by
        obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
        have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L)
          (canonLoop_isCanonLoop (projBlock_isPerm hjb hL'.1))
        dsimp only [iterW6mLift]
        cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
        | D => exact absurd hc hj_neD
        | F => rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; simp
        | S => rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; simp
      rw [← map_edgeOfRowTag_eq_rowSlices hK4 _ hneD, List.map_map, List.map_map]
      rfl
    rw [hLHS, hRHS]
    -- Show `(sigmas.flatMap (layerSlices j ·)).Perm allLJs` (both `Nodup`, same elements)!
    have hnd1 : (sigmas.flatMap (layerSlices m hm r hr K hK j)).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun σ _ => layerSlices_nodup m hm r hr K hK j σ, ?_⟩
      refine (allLayerSigmas_nodup m hm r hr K hK j).imp_of_mem ?_
      intro σ1 σ2 _ _ hne s hs1 hs2
      have h1 := ((mem_layerSlices_iff m hm r hr K hK j σ1 s).mp hs1).2.2.2
      have h2 := ((mem_layerSlices_iff m hm r hr K hK j σ2 s).mp hs2).2.2.2
      exact hne (h1.symm.trans h2)
    have hnd2 : allLJs.Nodup := by
      dsimp only [allLJs]
      rw [List.nodup_flatMap]
      refine ⟨fun L _ => (tagsOfRowType_nodup K _).map (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
      refine ((allCanonLoops_nodup K).filter _).imp_of_mem ?_
      intro L1 L2 _ _ hne x hx1 hx2
      obtain ⟨t1, _, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨t2, _, heq⟩ := List.mem_map.mp hx2
      exact hne (Prod.mk.inj heq).1.symm
    have hperm : (sigmas.flatMap (layerSlices m hm r hr K hK j)).Perm allLJs := by
      refine (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun s => ?_
      rcases s with ⟨L, tag⟩
      simp only [List.mem_flatMap, mem_layerSlices_iff, allLJs, layerLoops, List.mem_filter,
        List.mem_map, beq_iff_eq, mem_allCanonLoops_iff]
      constructor
      · rintro ⟨σ, _, hL, hact, htag, _⟩
        exact ⟨L, ⟨hL, hact⟩, tag, htag, rfl⟩
      · rintro ⟨L', ⟨hL', hact'⟩, t', ht', heq⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨tagSigma (6 * m) j K ((iterW6mLift m hm r hr K hK).row L').1 t',
          tagSigma_mem_allLayerSigmas m hm r hr K hK hj hL' hact' t',
          hL', hact', ht', rfl⟩
    exact (hperm.map bodyOf).sum_eq

end AsymptoticZero
