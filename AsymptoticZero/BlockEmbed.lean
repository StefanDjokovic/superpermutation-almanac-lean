import AsymptoticZero.WalkW6m
import Mathlib.Tactic

/-!
# Lemma 2: Disjoint-Block Multi-Layer Selection `iterW6mLift` & Exact Symmetry Fiber Counting

Given `m ≥ 1` (`b = 6 * m`), `r ≥ 1`, and ANY `K ≥ r * b + 1`:
1. Defines block embedding `embBlock b K j`, block projection `projBlock b j`, and `blockLoop b j`.
2. Proves the exact slot-pinning characterization of Pantone-transported `r`-layer composition
   `iterW6mLift m hm r K hK : PureSelection K` directly on `Fin K`, with a 4-case closure proof.
3. Proves the universal **Block-Diagonal Symmetry Fiber Lemma** (`block_symmetry_count`),
   immediately giving exact multiplicative identities for:
   * the number of `'S'`-rows in `iterW6mLift`,
   * the number of `'D'`-loops in `iterW6mLift`,
   * the number of surviving cyclic orders `σ` and lifted `z`-cycles in each Layer `j < r` (for Lemma 3),
   * the number of `'D'`-connector cycles on `Fin K \ {r * b}` (for Lemma 4).
-/

namespace AsymptoticZero

/-! ### 1. Block projection, `filterMap` rotation invariance, and `pinAt` -/

/-- Projection of an element `x : Fin K` into block `j` of width `b` (`[j*b, (j+1)*b)`). -/
def projBlockElem (b j : Nat) {K : Nat} (x : Fin K) : Option (Fin b) :=
  if h : j * b ≤ x.1 ∧ x.1 < (j + 1) * b then
    some ⟨x.1 - j * b, by
      have h1 : (j + 1) * b = j * b + b := by ring
      omega⟩
  else none

/-- Embedding of `a : Fin b` into block `j` of `Fin K`. -/
def embBlock (b K j : Nat) (hjb : (j + 1) * b ≤ K) (a : Fin b) : Fin K :=
  ⟨j * b + a.1, by
    have ha := a.2
    have h1 : (j + 1) * b = j * b + b := by ring
    omega⟩

theorem projBlockElem_embBlock (b K j : Nat) (hjb : (j + 1) * b ≤ K) (a : Fin b) :
    projBlockElem b j (embBlock b K j hjb a) = some a := by
  unfold projBlockElem embBlock
  have ha := a.2
  have hcond : j * b ≤ j * b + a.1 ∧ j * b + a.1 < (j + 1) * b := by
    have : (j + 1) * b = j * b + b := by ring
    omega
  rw [dif_pos hcond]
  congr 1; apply Fin.ext; dsimp; omega

theorem projBlockElem_embBlock_ne {b K i j : Nat} (hij : i ≠ j) (hjb : (j + 1) * b ≤ K) (a : Fin b) :
    projBlockElem b i (embBlock b K j hjb a) = none := by
  unfold projBlockElem embBlock
  have ha := a.2
  have hcond : ¬(i * b ≤ j * b + a.1 ∧ j * b + a.1 < (i + 1) * b) := by
    intro ⟨h1, h2⟩
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · have : (i + 1) * b ≤ j * b := Nat.mul_le_mul_right b hlt
      omega
    · have : (j + 1) * b ≤ i * b := Nat.mul_le_mul_right b hgt
      have : (j + 1) * b = j * b + b := by ring
      omega
  simp only [hcond, ↓reduceDIte]

theorem projBlockElem_eq_some_iff (b j : Nat) {K : Nat} (hjb : (j + 1) * b ≤ K)
    (x : Fin K) (a : Fin b) :
    projBlockElem b j x = some a ↔ x = embBlock b K j hjb a := by
  constructor
  · intro h
    unfold projBlockElem at h
    by_cases hc : j * b ≤ x.1 ∧ x.1 < (j + 1) * b
    · rw [dif_pos hc] at h
      have h' := Option.some.inj h
      apply Fin.ext; dsimp [embBlock]
      have hv := congrArg Fin.val h'; dsimp at hv; omega
    · rw [dif_neg hc] at h; cases h
  · rintro rfl; exact projBlockElem_embBlock b K j hjb a

theorem projBlockElem_inj {b j K : Nat} {x y : Fin K} {a : Fin b}
    (hx : projBlockElem b j x = some a) (hy : projBlockElem b j y = some a) : x = y := by
  unfold projBlockElem at hx hy
  by_cases hcx : j * b ≤ x.1 ∧ x.1 < (j + 1) * b
  · by_cases hcy : j * b ≤ y.1 ∧ y.1 < (j + 1) * b
    · rw [dif_pos hcx] at hx
      rw [dif_pos hcy] at hy
      have hvx := congrArg Fin.val (Option.some.inj hx)
      have hvy := congrArg Fin.val (Option.some.inj hy)
      dsimp at hvx hvy; apply Fin.ext; omega
    · rw [dif_neg hcy] at hy; cases hy
  · rw [dif_neg hcx] at hx; cases hx

/-- Project a list on `Fin K` to block `j` of width `b`. -/
def projBlock (b j : Nat) {K : Nat} (p : List (Fin K)) : List (Fin b) :=
  p.filterMap (projBlockElem b j)

/-- `filterMap` commutes with cyclic rotation! -/
theorem isRotated_filterMap {α β : Type} (f : α → Option β) {l1 l2 : List α} (h : l1 ~r l2) :
    l1.filterMap f ~r l2.filterMap f := by
  obtain ⟨r, rfl⟩ := h
  cases l1 with
  | nil => simp
  | cons a as =>
    rw [← List.rotate_mod]
    have hle : r % (a :: as).length ≤ (a :: as).length := Nat.le_of_lt (Nat.mod_lt r (by simp))
    rw [List.rotate_eq_drop_append_take hle, List.filterMap_append]
    have h1 : (a :: as) = (a :: as).take (r % (a :: as).length) ++ (a :: as).drop (r % (a :: as).length) :=
      (List.take_append_drop _ _).symm
    conv_lhs => rw [h1, List.filterMap_append]
    exact ⟨(((a :: as).take (r % (a :: as).length)).filterMap f).length, List.rotate_append_length_eq _ _⟩

theorem projBlock_isRotated {b j K : Nat} {p q : List (Fin K)} (h : p ~r q) :
    projBlock b j p ~r projBlock b j q :=
  isRotated_filterMap (projBlockElem b j) h

theorem projBlock_nodup {b j K : Nat} {p : List (Fin K)} (hnd : p.Nodup) :
    (projBlock b j p).Nodup := by
  unfold projBlock
  induction p with
  | nil => simp
  | cons x xs ih =>
    have ⟨hxn, hxs⟩ := List.nodup_cons.mp hnd
    cases hx : projBlockElem b j x with
    | none => simp [List.filterMap_cons, hx, ih hxs]
    | some a =>
      simp only [List.filterMap_cons, hx, List.nodup_cons]
      refine ⟨?_, ih hxs⟩
      intro ha
      rw [List.mem_filterMap] at ha
      obtain ⟨y, hy_mem, hy_eq⟩ := ha
      have hxy := projBlockElem_inj hx hy_eq
      exact hxn (hxy ▸ hy_mem)

theorem projBlock_isPerm {b j K : Nat} (hjb : (j + 1) * b ≤ K) {p : List (Fin K)} (hp : IsPerm K p) :
    IsPerm b (projBlock b j p) := by
  have hnd : (projBlock b j p).Nodup := projBlock_nodup hp.1
  have hmem : ∀ a : Fin b, a ∈ projBlock b j p := by
    intro a
    unfold projBlock
    rw [List.mem_filterMap]
    exact ⟨embBlock b K j hjb a, mem_of_isPerm hp _, projBlockElem_embBlock b K j hjb a⟩
  have hlen : (projBlock b j p).length = b := by
    have hcard : (projBlock b j p).toFinset = Finset.univ := by
      ext a; simp [List.mem_toFinset, hmem a]
    have := congrArg Finset.card hcard
    rw [List.toFinset_card_of_nodup hnd, Finset.card_univ, Fintype.card_fin] at this
    exact this
  exact ⟨hnd, hlen⟩

/-- Canonical loop of the projection of `p` onto block `j`. -/
def blockLoop (b : Nat) [NeZero b] (j : Nat) {K : Nat} (p : List (Fin K)) : List (Fin b) :=
  canonLoop (projBlock b j p)

theorem blockLoop_eq_of_isRotated {b : Nat} [NeZero b] {j K : Nat} (hjb : (j + 1) * b ≤ K)
    {p q : List (Fin K)} (hp : IsPerm K p) (hq : IsPerm K q) (hrot : p ~r q) :
    blockLoop b j p = blockLoop b j q :=
  (canonLoop_eq_iff (projBlock_isPerm hjb hp) (projBlock_isPerm hjb hq)).mpr
    (projBlock_isRotated hrot)

/-- Rotate a length-`K` permutation `p` so that symbol `a` sits at index `slot` (`slot < K`). -/
def pinAt {K : Nat} (p : List (Fin K)) (a : Fin K) (slot : Nat) : List (Fin K) :=
  p.rotate ((p.idxOf a + K - slot) % K)

theorem pinAt_isRotated {K : Nat} (p : List (Fin K)) (a : Fin K) (slot : Nat) :
    pinAt p a slot ~r p := by
  have h : p ~r pinAt p a slot := ⟨(p.idxOf a + K - slot) % K, rfl⟩
  exact h.symm

theorem pinAt_isPerm {K : Nat} {p : List (Fin K)} (hp : IsPerm K p) (a : Fin K) (slot : Nat) :
    IsPerm K (pinAt p a slot) :=
  isPerm_rotate hp _

theorem pinAt_getElem {K : Nat} {p : List (Fin K)} (hp : IsPerm K p) (a : Fin K)
    {slot : Nat} (hslot : slot < K) :
    (pinAt p a slot)[slot]'(by rw [pinAt, List.length_rotate, hp.2]; exact hslot) = a := by
  unfold pinAt
  rw [List.getElem_rotate]
  have hidx : p.idxOf a < p.length := List.idxOf_lt_length_of_mem (mem_of_isPerm hp a)
  have hlen := hp.2
  have hmod : (slot + (p.idxOf a + K - slot) % K) % p.length = p.idxOf a := by
    rw [hlen]
    have h1 : (slot + (p.idxOf a + K - slot) % K) % K = (slot + (p.idxOf a + K - slot)) % K := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [h1]
    have h2 : slot + (p.idxOf a + K - slot) = p.idxOf a + K := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [hmod, List.getElem_idxOf]

/-- Uniqueness of rotation with a pinned symbol at `slot`: any `q ~r p` with `q[slot] = a` equals `pinAt p a slot`. -/
theorem eq_pinAt_of_isRotated {K : Nat} {p q : List (Fin K)} (hp : IsPerm K p) (hq : IsPerm K q)
    (hrot : q ~r p) {a : Fin K} {slot : Nat} (hslot : slot < K)
    (hget : q[slot]'(by rw [hq.2]; exact hslot) = a) :
    q = pinAt p a slot := by
  have hqp : q ~r pinAt p a slot := hrot.trans (pinAt_isRotated p a slot).symm
  obtain ⟨r, hr⟩ := hqp
  have hpin_get := pinAt_getElem hp a hslot
  have hq_rot : (q.rotate r)[slot]'(by rw [List.length_rotate, hq.2]; exact hslot) = a := by
    simpa [hr] using hpin_get
  rw [List.getElem_rotate] at hq_rot
  have hidx_eq : (slot + r) % q.length = slot :=
    (List.Nodup.getElem_inj_iff hq.1).mp (hq_rot.trans hget.symm)
  have hr0 : r % q.length = 0 := by
    have hlt : slot < q.length := by rw [hq.2]; exact hslot
    have hmod_r : r % q.length < q.length := Nat.mod_lt r (by omega)
    have h1 : (slot + r % q.length) % q.length = slot := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hidx_eq]
    by_cases hsum : slot + r % q.length < q.length
    · rw [Nat.mod_eq_of_lt hsum] at h1; omega
    · have h2 : slot + r % q.length = (slot + r % q.length - q.length) + q.length := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h1; omega
  have hrot_id : q.rotate r = q := by rw [← List.rotate_mod, hr0, List.rotate_zero]
  exact hrot_id.symm.trans hr

/-! ### 2. Action of `FStep` and `SStep` on `projBlock` -/

/-- Decompose a length-`K` list (`K ≥ 4`) as `a :: mid ++ [last]` where `a = q[0]`, `last = q[K - 1]`. -/
theorem split_first_last {α : Type} {q : List α} {K : Nat} (hK : 4 ≤ K) (hq : q.length = K) :
    ∃ (a last : α) (mid : List α),
      q = a :: mid ++ [last] ∧ FStep q = mid ++ [a, last] ∧ mid.length = K - 2 ∧
      a = q[0]'(by omega) ∧ last = q[K - 1]'(by omega) := by
  cases q with
  | nil => simp at hq; omega
  | cons a rest =>
    have hne : rest ≠ [] := by intro h; subst h; simp at hq; omega
    let mid := rest.dropLast
    let last := rest.getLast hne
    have hrest : rest = mid ++ [last] := (List.dropLast_append_getLast hne).symm
    have hq_eq : a :: rest = a :: mid ++ [last] := by rw [hrest, List.cons_append]
    have hmid_len : mid.length = K - 2 := by
      have := congrArg List.length hq_eq; simp [hq] at this; omega
    have hF : FStep (a :: rest) = mid ++ [a, last] := by
      unfold FStep
      rw [hq]
      have htake : (a :: rest).take (K - 1) = a :: mid := by
        rw [hq_eq, List.take_append_of_le_length (by simp [hmid_len]; omega),
          List.take_of_length_le (by simp [hmid_len]; omega)]
      have hdrop : (a :: rest).drop (K - 1) = [last] := by
        rw [hq_eq, List.drop_append_of_le_length (by simp [hmid_len]; omega),
          List.drop_eq_nil_of_le (by simp [hmid_len]; omega), List.nil_append]
      rw [htake, hdrop, List.rotate_cons_succ, List.rotate_zero]
      simp [List.append_assoc]
    refine ⟨a, last, mid, hq_eq, hF, hmid_len, rfl, ?_⟩
    have : (a :: mid ++ [last])[K - 1]'(by simp [hmid_len]; omega) = last := by
      rw [List.getElem_append_right (by simp [hmid_len]; omega)]
      simp [hmid_len, show K - 1 - (K - 2 + 1) = 0 by omega]
    simpa [hq_eq] using this.symm

/-- Decompose a length-`K` list (`K ≥ 4`) as `pre ++ [u, v, w]` where `u = q[K-3], v = q[K-2], w = q[K-1]`. -/
theorem split_last3 {α : Type} {q : List α} {K : Nat} (hK : 4 ≤ K) (hq : q.length = K) :
    ∃ (pre : List α) (u v w : α),
      q = pre ++ [u, v, w] ∧ SStep q = [w] ++ pre ++ [v, u] ∧ pre.length = K - 3 ∧
      u = q[K - 3]'(by omega) ∧ v = q[K - 2]'(by omega) ∧ w = q[K - 1]'(by omega) := by
  let pre := q.take (K - 3)
  let tail3 := q.drop (K - 3)
  have hpre_len : pre.length = K - 3 := by simp [pre, hq]
  have htail_len : tail3.length = 3 := by simp [tail3, hq]; omega
  rcases List.length_eq_three.mp htail_len with ⟨u, v, w, htail_eq⟩
  have hq_eq : q = pre ++ [u, v, w] := by
    have := (List.take_append_drop (K - 3) q).symm
    change q = pre ++ tail3 at this
    rwa [htail_eq] at this
  have hS : SStep q = [w] ++ pre ++ [v, u] := by
    unfold SStep; rw [hq]
    have hdrop1 : q.drop (K - 1) = [w] := by
      rw [hq_eq, List.drop_append]
      have hnil : pre.drop (K - 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil, List.nil_append, hpre_len, show K - 1 - (K - 3) = 2 by omega]; rfl
    have htake3 : q.take (K - 3) = pre := rfl
    have hdrop3 : (q.drop (K - 3)).take 2 = [u, v] := by
      change tail3.take 2 = [u, v]; rw [htail_eq]; rfl
    rw [hdrop1, htake3, hdrop3]; rfl
  refine ⟨pre, u, v, w, hq_eq, hS, hpre_len, ?_, ?_, ?_⟩
  · have : (pre ++ [u, v, w])[K - 3]'(by simp [hpre_len]) = u := by
      rw [List.getElem_append_right (by omega)]; simp [hpre_len]
    simpa [hq_eq] using this.symm
  · have : (pre ++ [u, v, w])[K - 2]'(by simp [hpre_len]; omega) = v := by
      rw [List.getElem_append_right (by omega)]
      simp [hpre_len, show K - 2 - (K - 3) = 1 by omega]
    simpa [hq_eq] using this.symm
  · have : (pre ++ [u, v, w])[K - 1]'(by simp [hpre_len]; omega) = w := by
      rw [List.getElem_append_right (by omega)]
      simp [hpre_len, show K - 1 - (K - 3) = 2 by omega]
    simpa [hq_eq] using this.symm

/-- If `q[K - 1] ∉ B_i`, then `FStep q` preserves the cyclic order of block `B_i`. -/
theorem projBlock_FStep_of_last_none {b i K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hlast : projBlockElem b i (q[K - 1]'(by omega)) = none) :
    projBlock b i (FStep q) ~r projBlock b i q := by
  obtain ⟨a, last, mid, hq_eq, hF, _, _, hlast_eq⟩ := split_first_last hK hq
  have hlast' : projBlockElem b i last = none := hlast_eq ▸ hlast
  unfold projBlock
  rw [hF, hq_eq]
  have hL : (mid ++ [a, last]).filterMap (projBlockElem b i) =
      mid.filterMap (projBlockElem b i) ++ [a].filterMap (projBlockElem b i) := by
    have : mid ++ [a, last] = mid ++ [a] ++ [last] := by simp
    rw [this, List.filterMap_append, List.filterMap_append]
    simp [List.filterMap_cons, hlast']
  have hR : (a :: mid ++ [last]).filterMap (projBlockElem b i) =
      [a].filterMap (projBlockElem b i) ++ mid.filterMap (projBlockElem b i) := by
    have : a :: mid ++ [last] = [a] ++ mid ++ [last] := by simp
    rw [this, List.filterMap_append, List.filterMap_append]
    simp [List.filterMap_cons, hlast']
  rw [hL, hR]
  exact ⟨(mid.filterMap (projBlockElem b i)).length, List.rotate_append_length_eq _ _⟩

/-- If `q[K - 1] ∈ B_j` and `q[0] ∉ B_j`, then `projBlock b j (FStep q) = projBlock b j q`. -/
theorem projBlock_FStep_of_head_none {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (ha : projBlockElem b j (q[0]'(by omega)) = none) :
    projBlock b j (FStep q) = projBlock b j q := by
  obtain ⟨a, last, mid, hq_eq, hF, _, ha_eq, _⟩ := split_first_last hK hq
  have ha' : projBlockElem b j a = none := ha_eq ▸ ha
  unfold projBlock
  rw [hF, hq_eq]
  have h1 : mid ++ [a, last] = mid ++ ([a] ++ [last]) := by simp
  have h2 : a :: mid ++ [last] = [a] ++ (mid ++ [last]) := by simp
  rw [h1, h2]
  simp [List.filterMap_append, List.filterMap_cons, ha']

/-- If `q[K - 1] ∈ B_j` and `q[0] ∈ B_j`, then `projBlock b j (FStep q) = FStep (projBlock b j q)`. -/
theorem projBlock_FStep_of_both_some {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    {a' l' : Fin b} (ha : projBlockElem b j (q[0]'(by omega)) = some a')
    (hl : projBlockElem b j (q[K - 1]'(by omega)) = some l') :
    projBlock b j (FStep q) = FStep (projBlock b j q) := by
  obtain ⟨a, last, mid, hq_eq, hF, _, ha_eq, hl_eq⟩ := split_first_last hK hq
  have ha' : projBlockElem b j a = some a' := ha_eq ▸ ha
  have hl' : projBlockElem b j last = some l' := hl_eq ▸ hl
  unfold projBlock
  rw [hF, hq_eq]
  let M := mid.filterMap (projBlockElem b j)
  have hL : (mid ++ [a, last]).filterMap (projBlockElem b j) = M ++ [a', l'] := by
    simp [M, List.filterMap_append, List.filterMap_cons, ha', hl']
  have hR : (a :: mid ++ [last]).filterMap (projBlockElem b j) = (a' :: M) ++ [l'] := by
    simp [M, List.filterMap_append, List.filterMap_cons, ha', hl']
  rw [hL, hR]
  unfold FStep
  have hlen : ((a' :: M) ++ [l']).length = M.length + 2 := by simp
  rw [hlen, show M.length + 2 - 1 = M.length + 1 by omega]
  rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
    List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append,
    List.rotate_cons_succ, List.rotate_zero]
  simp [List.append_assoc]

/-- If `q[K - 2] ∉ B_i` (or `q[K - 3] ∉ B_i`), then `SStep q` preserves the cyclic order of block `B_i`. -/
theorem projBlock_SStep_of_none {b i K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hnone : projBlockElem b i (q[K - 3]'(by omega)) = none ∨
             projBlockElem b i (q[K - 2]'(by omega)) = none) :
    projBlock b i (SStep q) ~r projBlock b i q := by
  obtain ⟨pre, u, v, w, hq_eq, hS, _, hu_eq, hv_eq, _⟩ := split_last3 hK hq
  have hnone' : projBlockElem b i u = none ∨ projBlockElem b i v = none := by
    rcases hnone with hu | hv
    · exact Or.inl (hu_eq ▸ hu)
    · exact Or.inr (hv_eq ▸ hv)
  unfold projBlock
  rw [hS, hq_eq]
  have huv : [v, u].filterMap (projBlockElem b i) = [u, v].filterMap (projBlockElem b i) := by
    rcases hnone' with hu | hv
    · simp [List.filterMap_cons, hu]
    · simp [List.filterMap_cons, hv]
  have h1 : pre ++ [u, v, w] = (pre ++ [u, v]) ++ [w] := by simp [List.append_assoc]
  have h2 : [w] ++ pre ++ [v, u] = [w] ++ (pre ++ [v, u]) := by simp [List.append_assoc]
  rw [h1, h2, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    List.filterMap_append, huv]
  exact ⟨([w].filterMap (projBlockElem b i)).length, List.rotate_append_length_eq _ _⟩

/-- If `q[K - 3], q[K - 2] ∈ B_j` and `projBlock b j q ~r xB` (`IsPerm b xB`, `b ≥ 4`) with
`projBlockElem b j q[K - 2] = some xB[b - 2]`, then `projBlockElem b j q[K - 3] = some xB[b - 3]`
AND `projBlock b j (SStep q) = SStep xB`! -/
theorem projBlock_SStep_of_both_some {b j K : Nat} (hb : 4 ≤ b) (hK : 4 ≤ K) (hjb : (j + 1) * b ≤ K)
    {q : List (Fin K)} (hq : IsPerm K q) {xB : List (Fin b)} (hxB : IsPerm b xB)
    (hrot : projBlock b j q ~r xB)
    (hv : projBlockElem b j (q[K - 2]'(by rw [hq.2]; omega)) = some (xB[b - 2]'(by rw [hxB.2]; omega)))
    {u' : Fin b} (hu : projBlockElem b j (q[K - 3]'(by rw [hq.2]; omega)) = some u') :
    u' = xB[b - 3]'(by rw [hxB.2]; omega) ∧ projBlock b j (SStep q) = SStep xB := by
  obtain ⟨pre, u, v, w, hq_eq, hS, _, hu_eq, hv_eq, hw_eq⟩ := split_last3 hK hq.2
  have hu' : projBlockElem b j u = some u' := hu_eq ▸ hu
  have hv' : projBlockElem b j v = some (xB[b - 2]'(by rw [hxB.2]; omega)) := hv_eq ▸ hv
  let P := pre.filterMap (projBlockElem b j)
  let v' : Fin b := xB[b - 2]'(by rw [hxB.2]; omega)
  have hpq_perm : IsPerm b (projBlock b j q) := projBlock_isPerm hjb hq
  obtain ⟨preB, uB, vB, wB, hxB_eq, hSB, hpreB_len, huB_eq, hvB_eq, hwB_eq⟩ := split_last3 hb hxB.2
  have hv'_eq : v' = vB := hvB_eq.symm
  cases hw : projBlockElem b j w with
  | some w' =>
    have hproj_q : projBlock b j q = P ++ [u', v', w'] := by
      unfold projBlock; rw [hq_eq]
      simp [P, List.filterMap_append, List.filterMap_cons, hu', hv', hw, v']
    have hP_len : P.length = b - 3 := by
      have := hpq_perm.2; rw [hproj_q] at this; simp at this; omega
    have hq_at : (projBlock b j q)[b - 2]'(by rw [hpq_perm.2]; omega) = v' := by
      have htmp : (P ++ [u', v', w'])[b - 2]'(by simp [hP_len]; omega) = v' := by
        rw [List.getElem_append_right (by omega)]
        simp [hP_len, show b - 2 - (b - 3) = 1 by omega]
      simpa [hproj_q] using htmp
    have hxB_at : xB[b - 2]'(by rw [hxB.2]; omega) = v' := rfl
    have heq_q : projBlock b j q = xB := by
      have h1 := eq_pinAt_of_isRotated hxB hpq_perm hrot (by omega : b - 2 < b) hq_at
      have h2 := eq_pinAt_of_isRotated hxB hxB (List.IsRotated.refl xB) (by omega : b - 2 < b) hxB_at
      exact h1.trans h2.symm
    rw [hproj_q, hxB_eq] at heq_q
    have hP_eq : P = preB := by
      have := congrArg (List.take (b - 3)) heq_q
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
      exact this
    have htail_eq : [u', v', w'] = [uB, vB, wB] := by
      rw [hP_eq, List.append_cancel_left_eq] at heq_q; exact heq_q
    simp only [List.cons.injEq, and_true] at htail_eq
    refine ⟨htail_eq.1.trans huB_eq, ?_⟩
    unfold projBlock; rw [hS, hSB]
    simp [P, List.filterMap_append, List.filterMap_cons, hu', hv', hw, hP_eq, htail_eq.1,
      htail_eq.2.1, htail_eq.2.2, v']
  | none =>
    have hproj_q : projBlock b j q = P ++ [u', v'] := by
      unfold projBlock; rw [hq_eq]
      simp [P, List.filterMap_append, List.filterMap_cons, hu', hv', hw, v']
    have hP_len : P.length = b - 2 := by
      have := hpq_perm.2; rw [hproj_q] at this; simp at this; omega
    have hxB_rot : xB.rotate (b - 1) = ([wB] ++ preB) ++ [uB, vB] := by
      have h1 : xB = (preB ++ [uB, vB]) ++ [wB] := by rw [hxB_eq]; simp [List.append_assoc]
      have hlen1 : (preB ++ [uB, vB]).length = b - 1 := by simp [hpreB_len]; omega
      have hrot_app := List.rotate_append_length_eq (preB ++ [uB, vB]) [wB]
      rw [hlen1] at hrot_app
      rw [h1, hrot_app]; simp [List.append_assoc]
    have hq_at : (projBlock b j q)[b - 1]'(by rw [hpq_perm.2]; omega) = v' := by
      have htmp : (P ++ [u', v'])[b - 1]'(by simp [hP_len]; omega) = v' := by
        rw [List.getElem_append_right (by omega)]
        simp [hP_len, show b - 1 - (b - 2) = 1 by omega]
      simpa [hproj_q] using htmp
    have hxB_rot_at : (xB.rotate (b - 1))[b - 1]'(by rw [List.length_rotate, hxB.2]; omega) = v' := by
      have htmp : (([wB] ++ preB) ++ [uB, vB])[b - 1]'(by simp [hpreB_len]; omega) = v' := by
        rw [List.getElem_append_right (by simp [hpreB_len]; omega)]
        simp [hpreB_len, show b - 1 - (1 + (b - 3)) = 1 by omega, show b - 1 - (b - 3 + 1) = 1 by omega, hv'_eq]
      simpa [hxB_rot] using htmp
    have heq_q : projBlock b j q = xB.rotate (b - 1) := by
      have h1 := eq_pinAt_of_isRotated hxB hpq_perm hrot (by omega : b - 1 < b) hq_at
      have hrot_xB : xB ~r xB.rotate (b - 1) := ⟨b - 1, rfl⟩
      have h2 := eq_pinAt_of_isRotated hxB (isPerm_rotate hxB (b - 1))
        hrot_xB.symm (by omega : b - 1 < b) hxB_rot_at
      exact h1.trans h2.symm
    rw [hproj_q, hxB_rot] at heq_q
    have hP_eq : P = [wB] ++ preB := by
      have := congrArg (List.take (b - 2)) heq_q
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.take_append_of_le_length (by simp [hpreB_len]; omega),
        List.take_of_length_le (by simp [hpreB_len]; omega)] at this
      exact this
    have htail_eq : [u', v'] = [uB, vB] := by
      rw [hP_eq, List.append_cancel_left_eq] at heq_q; exact heq_q
    simp only [List.cons.injEq, and_true] at htail_eq
    refine ⟨htail_eq.1.trans huB_eq, ?_⟩
    unfold projBlock; rw [hS, hSB]
    simp [P, List.filterMap_append, List.filterMap_cons, hu', hv', hw, hP_eq, htail_eq.1,
      htail_eq.2, v']

/-! ### 3. Direct multi-layer selection `iterW6mLift m hm r K hK` -/

/-- Find the first block `j < r` where `blockLoop (6 * m) j L` is non-`'D'` in `selW6m m hm`. -/
noncomputable def activeLayer (m : Nat) (hm : 1 ≤ m) (r : Nat) {K : Nat} (L : List (Fin K)) : Option Nat :=
  letI : NeZero (6 * m) := ⟨by omega⟩
  (List.range r).find? fun j => ((selW6m m hm).row (blockLoop (6 * m) j L)).2 != .D

/-- Every `'S'`-row of `selW6m` transitions under `SStep` to an `'F'`-row! -/
theorem selW6m_S_next_is_F (m : Nat) (hm : 1 ≤ m) {L : List (Fin (6 * m))}
    (hL : letI : NeZero (6 * m) := ⟨by omega⟩; IsCanonLoop (6 * m) L)
    (hS : letI : NeZero (6 * m) := ⟨by omega⟩; ((selW6m m hm).row L).2 = .S) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    ((selW6m m hm).row (canonLoop (SStep ((selW6m m hm).row L).1))).2 = .F := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  dsimp only [selW6m] at hS ⊢
  cases hf : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = L)) with
  | none => simp [hf] at hS
  | some p =>
    rw [hf] at hS
    have hp_mem := List.mem_of_find?_eq_some hf
    obtain ⟨k, hk, r, hr, hp1, hp2⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp hp_mem
    have hr_eq : r = 6 * m - 3 := by by_contra hne; simp [hne] at hp2; rw [hp2] at hS; cases hS
    subst hr_eq
    rw [hp1, SStep_W6mState]
    have hst := selW6m_row_state m hm (Nat.mod_lt (k + 1) (by omega)) (by omega : 0 < 6 * m - 2)
    dsimp [selW6m] at hst
    rw [hst]
    simp [show (0 : Nat) ≠ 6 * m - 3 by omega]

/-- Raw row assignment of the `r`-layer lifted `W_{6m}` selection on `Fin K` (`K ≥ r * 6m + 1`). -/
noncomputable def iterW6mRow (m : Nat) (hm : 1 ≤ m) (r K : Nat) (hK : r * (6 * m) + 1 ≤ K)
    (L : List (Fin K)) : List (Fin K) × RowType :=
  letI : NeZero (6 * m) := ⟨by omega⟩
  match activeLayer m hm r L with
  | none => (L, .D)
  | some j =>
    if hj : j < r then
      have hjb : (j + 1) * (6 * m) ≤ K := by
        have : (j + 1) * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right (6 * m) hj
        omega
      let rowB := (selW6m m hm).row (blockLoop (6 * m) j L)
      match rowB.2 with
      | .D => (L, .D)
      | .F =>
        if hlen : 6 * m - 1 < rowB.1.length then
          (pinAt L (embBlock (6 * m) K j hjb (rowB.1[6 * m - 1]'hlen)) (K - 1), .F)
        else (L, .D)
      | .S =>
        if hlen : 6 * m - 2 < rowB.1.length then
          (pinAt L (embBlock (6 * m) K j hjb (rowB.1[6 * m - 2]'hlen)) (K - 2), .S)
        else (L, .D)
    else (L, .D)

/-- Helper: characterizing `activeLayer m hm r L = some j`. -/
theorem activeLayer_eq_some_iff (m : Nat) (hm : 1 ≤ m) (r : Nat) {K : Nat} (L : List (Fin K)) (j : Nat) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    activeLayer m hm r L = some j ↔
      j < r ∧
      ((selW6m m hm).row (blockLoop (6 * m) j L)).2 ≠ .D ∧
      ∀ i < j, ((selW6m m hm).row (blockLoop (6 * m) i L)).2 = .D := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hrange_split : ∀ (j : Nat), j < r →
      List.range r = List.range j ++ j :: (List.range (r - j - 1)).map (· + (j + 1)) := by
    intro j hj
    refine List.ext_getElem (by simp; omega) fun t ht1 ht2 => ?_
    simp only [List.getElem_range]
    by_cases h1 : t < j
    · rw [List.getElem_append_left (by simp; omega)]; simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_range]
      by_cases h2 : t = j
      · subst h2; simp
      · obtain ⟨d, hd⟩ : ∃ d, t - j = d + 1 := ⟨t - j - 1, by omega⟩
        simp only [hd, List.getElem_cons_succ, List.getElem_map, List.getElem_range]; omega
  unfold activeLayer
  constructor
  · intro h
    have hj_mem : j ∈ List.range r := List.mem_of_find?_eq_some h
    have hj_lt : j < r := List.mem_range.mp hj_mem
    have hj_pred : (((selW6m m hm).row (blockLoop (6 * m) j L)).2 != .D) = true :=
      List.find?_some (p := fun j => ((selW6m m hm).row (blockLoop (6 * m) j L)).2 != .D) h
    have hj_neD : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 ≠ .D := by
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 <;> simp [hc] at hj_pred ⊢
    refine ⟨hj_lt, hj_neD, ?_⟩
    intro i hi
    rw [hrange_split j hj_lt, List.find?_append] at h
    cases hf : (List.range j).find? (fun k => ((selW6m m hm).row (blockLoop (6 * m) k L)).2 != .D) with
    | some k =>
      rw [hf] at h; simp only [Option.some_or, Option.some.injEq] at h
      have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      omega
    | none =>
      have hfalse := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) i L)).2 <;> simp [hc] at hfalse ⊢
  · rintro ⟨hj_lt, hj_neD, hprev⟩
    rw [hrange_split j hj_lt, List.find?_append]
    have hnone : (List.range j).find? (fun k => ((selW6m m hm).row (blockLoop (6 * m) k L)).2 != .D) = none := by
      rw [List.find?_eq_none]
      intro i hi
      rw [List.mem_range] at hi
      simp [hprev i hi]
    rw [hnone, Option.none_or, List.find?_cons]
    have htrue : (((selW6m m hm).row (blockLoop (6 * m) j L)).2 != .D) = true := by
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 <;> simp [hc] at hj_neD ⊢
    simp [htrue]

theorem activeLayer_eq_none_iff (m : Nat) (hm : 1 ≤ m) (r : Nat) {K : Nat} (L : List (Fin K)) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    activeLayer m hm r L = none ↔
      ∀ i < r, ((selW6m m hm).row (blockLoop (6 * m) i L)).2 = .D := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  unfold activeLayer
  rw [List.find?_eq_none]
  constructor
  · intro h i hi
    have h1 := h i (List.mem_range.mpr hi)
    cases hc : ((selW6m m hm).row (blockLoop (6 * m) i L)).2 <;> simp [hc] at h1 ⊢
  · intro h i hi
    rw [List.mem_range] at hi
    simp [h i hi]

theorem iterW6mRow_eq_none {m : Nat} (hm : 1 ≤ m) {r K : Nat} (hK : r * (6 * m) + 1 ≤ K)
    {L : List (Fin K)} (hact : activeLayer m hm r L = none) :
    iterW6mRow m hm r K hK L = (L, .D) := by
  unfold iterW6mRow; simp [hact]

theorem iterW6mRow_eq_F {m : Nat} (hm : 1 ≤ m) {r K : Nat} (hK : r * (6 * m) + 1 ≤ K)
    {L : List (Fin K)} {j : Nat} (hact : activeLayer m hm r L = some j)
    (hj : j < r) (hjb : (j + 1) * (6 * m) ≤ K)
    (hF : letI : NeZero (6 * m) := ⟨by omega⟩; ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .F)
    (hlen : letI : NeZero (6 * m) := ⟨by omega⟩; 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    iterW6mRow m hm r K hK L =
      (pinAt L (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlen)) (K - 1), .F) := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  unfold iterW6mRow
  simp only [hact, hj, ↓reduceDIte, hF, hlen]

theorem iterW6mRow_eq_S {m : Nat} (hm : 1 ≤ m) {r K : Nat} (hK : r * (6 * m) + 1 ≤ K)
    {L : List (Fin K)} {j : Nat} (hact : activeLayer m hm r L = some j)
    (hj : j < r) (hjb : (j + 1) * (6 * m) ≤ K)
    (hS : letI : NeZero (6 * m) := ⟨by omega⟩; ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .S)
    (hlen : letI : NeZero (6 * m) := ⟨by omega⟩; 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    iterW6mRow m hm r K hK L =
      (pinAt L (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 2]'hlen)) (K - 2), .S) := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  unfold iterW6mRow
  simp only [hact, hj, ↓reduceDIte, hS, hlen]

/-- **Lemma 2 (`iterW6mLift`):** For all `m ≥ 1`, `r ≥ 1`, and `K ≥ r * (6 * m) + 1`,
`iterW6mRow` defines a 100% valid `PureSelection K`! -/
noncomputable def iterW6mLift (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    @PureSelection K ⟨by have : 1 * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right _ hr; omega⟩ :=
  letI : NeZero K := ⟨by have : 1 * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right _ hr; omega⟩
  letI : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by have : 1 * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right _ hr; omega
  have hmul_le : ∀ {j : Nat}, j < r → (j + 1) * (6 * m) ≤ K := by
    intro j hj
    have h1 : (j + 1) * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right (6 * m) (Nat.succ_le_of_lt hj)
    omega
  { row := iterW6mRow m hm r K hK
    row_perm := by
      intro L hL
      cases hact : activeLayer m hm r L with
      | none =>
        rw [iterW6mRow_eq_none hm hK hact]
        exact ⟨hL.1, List.IsRotated.refl L⟩
      | some j =>
        obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
        have hjb := hmul_le hj_lt
        have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L)
          (canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1))
        cases hrt : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
        | D => exact absurd hrt hj_neD
        | F =>
          rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hrt (by rw [hrowB.1.2]; omega)]
          exact ⟨pinAt_isPerm hL.1 _ _, pinAt_isRotated L _ _⟩
        | S =>
          rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hrt (by rw [hrowB.1.2]; omega)]
          exact ⟨pinAt_isPerm hL.1 _ _, pinAt_isRotated L _ _⟩
    closed_F := by
      intro L hL hF
      cases hact : activeLayer m hm r L with
      | none => rw [iterW6mRow_eq_none hm hK hact] at hF; cases hF
      | some j =>
        obtain ⟨hj_lt, hj_neD, hprev⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
        have hjb := hmul_le hj_lt
        have hbl_canon : IsCanonLoop (6 * m) (blockLoop (6 * m) j L) :=
          canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1)
        have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L) hbl_canon
        set rowB := (selW6m m hm).row (blockLoop (6 * m) j L)
        have hrt_F : rowB.2 = .F := by
          cases hc : rowB.2 with
          | D => exact absurd hc hj_neD
          | F => rfl
          | S =>
            rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hF
            cases hF
        have hlenB : 6 * m - 1 < rowB.1.length := by rw [hrowB.1.2]; omega
        let q := pinAt L (embBlock (6 * m) K j hjb (rowB.1[6 * m - 1]'hlenB)) (K - 1)
        have hq_eq : (iterW6mRow m hm r K hK L).1 = q := by
          rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hrt_F hlenB]
        have hq_perm : IsPerm K q := pinAt_isPerm hL.1 _ _
        have hq_last : q[K - 1]'(by rw [hq_perm.2]; omega) = embBlock (6 * m) K j hjb (rowB.1[6 * m - 1]'hlenB) :=
          pinAt_getElem hL.1 _ (by omega)
        let x' := FStep q
        have hx'_perm : IsPerm K x' := FStep_isPerm hq_perm
        have hother : ∀ i < r, i ≠ j → blockLoop (6 * m) i (canonLoop x') = blockLoop (6 * m) i L := by
          intro i hi hij
          have hib := hmul_le hi
          have hnone : projBlockElem (6 * m) i (q[K - 1]'(by rw [hq_perm.2]; omega)) = none := by
            rw [hq_last]; exact projBlockElem_embBlock_ne hij hjb _
          have hrot1 : projBlock (6 * m) i x' ~r projBlock (6 * m) i q :=
            projBlock_FStep_of_last_none hK4 hq_perm.2 hnone
          have hrot2 : projBlock (6 * m) i q ~r projBlock (6 * m) i L :=
            projBlock_isRotated (pinAt_isRotated L _ _)
          have hrot3 : projBlock (6 * m) i (canonLoop x') ~r projBlock (6 * m) i x' :=
            projBlock_isRotated (canonLoop_isRotated x').symm
          exact (canonLoop_eq_iff (projBlock_isPerm hib (canonLoop_isCanonLoop hx'_perm).1)
            (projBlock_isPerm hib hL.1)).mpr (hrot3.trans (hrot1.trans hrot2))
        have hproj_q_eq : projBlock (6 * m) j q = rowB.1 := by
          have hproj_rot : projBlock (6 * m) j q ~r rowB.1 :=
            (projBlock_isRotated (pinAt_isRotated L _ _)).trans
              ((canonLoop_isRotated _).trans hrowB.2.symm)
          have hproj_perm : IsPerm (6 * m) (projBlock (6 * m) j q) := projBlock_isPerm hjb hq_perm
          have hlast_proj : (projBlock (6 * m) j q)[6 * m - 1]'(by rw [hproj_perm.2]; omega) =
              rowB.1[6 * m - 1]'hlenB := by
            obtain ⟨a, last, mid, hq_sp, _, _, _, hl_sp⟩ := split_first_last hK4 hq_perm.2
            have hl_some : projBlockElem (6 * m) j last = some (rowB.1[6 * m - 1]'hlenB) := by
              have : last = embBlock (6 * m) K j hjb (rowB.1[6 * m - 1]'hlenB) := hl_sp.trans hq_last
              rw [this]; exact projBlockElem_embBlock _ _ _ _ _
            have hdecomp : projBlock (6 * m) j q = (a :: mid).filterMap (projBlockElem (6 * m) j) ++
                [rowB.1[6 * m - 1]'hlenB] := by
              unfold projBlock; rw [hq_sp, List.filterMap_append]
              simp [List.filterMap_cons, hl_some]
            have hlen_pre : ((a :: mid).filterMap (projBlockElem (6 * m) j)).length = 6 * m - 1 := by
              have := hproj_perm.2; rw [hdecomp] at this; simp at this; omega
            have htmp : ((a :: mid).filterMap (projBlockElem (6 * m) j) ++ [rowB.1[6 * m - 1]'hlenB])[6 * m - 1]'(by simp [hlen_pre]) =
                rowB.1[6 * m - 1]'hlenB := by
              rw [List.getElem_append_right (by omega)]; simp [hlen_pre]
            simpa [hdecomp] using htmp
          have h1 := eq_pinAt_of_isRotated hrowB.1 hproj_perm hproj_rot (by omega : 6 * m - 1 < 6 * m) hlast_proj
          have h2 := eq_pinAt_of_isRotated hrowB.1 hrowB.1 (List.IsRotated.refl _) (by omega : 6 * m - 1 < 6 * m) rfl
          exact h1.trans h2.symm
        have hgoal_q : (iterW6mRow m hm r K hK (canonLoop x')).1 = x' ∧
            (iterW6mRow m hm r K hK (canonLoop x')).2 ≠ .D := by
          cases hq0 : projBlockElem (6 * m) j (q[0]'(by rw [hq_perm.2]; omega)) with
          | none =>
            have hproj_x' : projBlock (6 * m) j x' = projBlock (6 * m) j q :=
              projBlock_FStep_of_head_none hK4 hq_perm.2 hq0
            have hbl_x' : blockLoop (6 * m) j (canonLoop x') = blockLoop (6 * m) j L := by
              have hrot_c : projBlock (6 * m) j (canonLoop x') ~r projBlock (6 * m) j x' :=
                projBlock_isRotated (canonLoop_isRotated x').symm
              rw [hproj_x'] at hrot_c
              exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
                (projBlock_isPerm hjb hL.1)).mpr (hrot_c.trans (projBlock_isRotated (pinAt_isRotated L _ _)))
            have hact' : activeLayer m hm r (canonLoop x') = some j := by
              rw [activeLayer_eq_some_iff]
              exact ⟨hj_lt, by rw [hbl_x']; exact hj_neD, fun i hi => by rw [hother i (by omega) (by omega)]; exact hprev i hi⟩
            rw [iterW6mRow_eq_F hm hK hact' hj_lt hjb (by rw [hbl_x']; exact hrt_F) (by rw [hbl_x']; exact hlenB)]
            refine ⟨?_, by simp⟩
            have hx'_last : x'[K - 1]'(by rw [hx'_perm.2]; omega) =
                embBlock (6 * m) K j hjb (rowB.1[6 * m - 1]'hlenB) := by
              obtain ⟨a, last, mid, _, hF_sp, hmid_len, _, hl_sp⟩ := split_first_last hK4 hq_perm.2
              have hlast_f : (mid ++ [a, last])[K - 1]'(by simp [hmid_len]; omega) = last := by
                rw [List.getElem_append_right (by omega)]
                simp [hmid_len, show K - 1 - (K - 2) = 1 by omega]
              simpa [x', hF_sp, hl_sp, hq_last] using hlast_f
            have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hx'_perm).1 hx'_perm
              (canonLoop_isRotated x') (by omega : K - 1 < K) hx'_last
            have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop x'))).1[6 * m - 1]'(by rw [hbl_x']; exact hlenB) =
                rowB.1[6 * m - 1]'hlenB := by simp only [hbl_x', rowB]
            change pinAt (canonLoop x') (embBlock (6 * m) K j hjb _) (K - 1) = x'
            rw [harg]; exact hpin.symm
          | some a' =>
            have hl_some : projBlockElem (6 * m) j (q[K - 1]'(by rw [hq_perm.2]; omega)) =
                some (rowB.1[6 * m - 1]'hlenB) := by
              rw [hq_last]; exact projBlockElem_embBlock _ _ _ _ _
            have hproj_x' : projBlock (6 * m) j x' = FStep rowB.1 := by
              rw [← hproj_q_eq]; exact projBlock_FStep_of_both_some hK4 hq_perm.2 hq0 hl_some
            have ha'_eq : a' = rowB.1[0]'(by rw [hrowB.1.2]; omega) := by
              obtain ⟨a, last, mid, hq_sp, _, _, ha_sp, _⟩ := split_first_last hK4 hq_perm.2
              have ha_s : projBlockElem (6 * m) j a = some a' := ha_sp ▸ hq0
              have hhd : projBlock (6 * m) j q = a' :: (mid ++ [last]).filterMap (projBlockElem (6 * m) j) := by
                unfold projBlock; rw [hq_sp, List.cons_append, List.filterMap_cons, ha_s]
              rw [hproj_q_eq] at hhd
              have h0 := congrArg (fun l => l[0]?) hhd
              have h0_lt : 0 < rowB.1.length := by rw [hrowB.1.2]; omega
              rw [List.getElem?_eq_getElem h0_lt, List.getElem?_cons_zero] at h0
              exact (Option.some.inj h0).symm
            have hbl_x' : blockLoop (6 * m) j (canonLoop x') = canonLoop (FStep rowB.1) := by
              have hrot_c : projBlock (6 * m) j (canonLoop x') ~r projBlock (6 * m) j x' :=
                projBlock_isRotated (canonLoop_isRotated x').symm
              rw [hproj_x'] at hrot_c
              exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
                (FStep_isPerm hrowB.1)).mpr hrot_c
            have hclF := (selW6m m hm).closed_F (blockLoop (6 * m) j L) hbl_canon hrt_F
            have hact' : activeLayer m hm r (canonLoop x') = some j := by
              rw [activeLayer_eq_some_iff]
              exact ⟨hj_lt, by rw [hbl_x']; exact hclF.2, fun i hi => by rw [hother i (by omega) (by omega)]; exact hprev i hi⟩
            set rowB' := (selW6m m hm).row (canonLoop (FStep rowB.1))
            have hrowB'_1 : rowB'.1 = FStep rowB.1 := hclF.1
            have hlenB' : rowB'.1.length = 6 * m := by rw [hrowB'_1, (FStep_perm _).length_eq, hrowB.1.2]
            obtain ⟨a, last, mid, _, hF_sp, hmid_len, ha_sp, hl_sp⟩ := split_first_last hK4 hq_perm.2
            have ha_emb : a = embBlock (6 * m) K j hjb a' :=
              (projBlockElem_eq_some_iff (6 * m) j hjb a a').mp (ha_sp ▸ hq0)
            cases hrt' : rowB'.2 with
            | D => exact absurd hrt' hclF.2
            | F =>
              have hlt' : 6 * m - 1 < rowB'.1.length := by omega
              rw [iterW6mRow_eq_F hm hK hact' hj_lt hjb (by rw [hbl_x']; exact hrt') (by rw [hbl_x']; exact hlt')]
              refine ⟨?_, by simp⟩
              have hx'_last : x'[K - 1]'(by rw [hx'_perm.2]; omega) =
                  embBlock (6 * m) K j hjb (rowB'.1[6 * m - 1]'hlt') := by
                have h1 : (mid ++ [a, last])[K - 1]'(by simp [hmid_len]; omega) = last := by
                  rw [List.getElem_append_right (by omega)]
                  simp [hmid_len, show K - 1 - (K - 2) = 1 by omega]
                have h2 : rowB'.1[6 * m - 1]'hlt' = rowB.1[6 * m - 1]'hlenB := by
                  obtain ⟨aB, lastB, midB, hB_sp, hFB, hmidB_len, _, hlB_sp⟩ := split_first_last (by omega) hrowB.1.2
                  have h3 : (midB ++ [aB, lastB])[6 * m - 1]'(by simp [hmidB_len]; omega) = lastB := by
                    rw [List.getElem_append_right (by omega)]
                    simp [hmidB_len, show 6 * m - 1 - (6 * m - 2) = 1 by omega]
                  simpa [hrowB'_1, hFB, hlB_sp] using h3
                rw [h2]; simpa [x', hF_sp, hl_sp, hq_last] using h1
              have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hx'_perm).1 hx'_perm
                (canonLoop_isRotated x') (by omega : K - 1 < K) hx'_last
              have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop x'))).1[6 * m - 1]'(by rw [hbl_x']; exact hlt') =
                  rowB'.1[6 * m - 1]'hlt' := by simp only [hbl_x', rowB']
              change pinAt (canonLoop x') (embBlock (6 * m) K j hjb _) (K - 1) = x'
              rw [harg]; exact hpin.symm
            | S =>
              have hlt' : 6 * m - 2 < rowB'.1.length := by omega
              rw [iterW6mRow_eq_S hm hK hact' hj_lt hjb (by rw [hbl_x']; exact hrt') (by rw [hbl_x']; exact hlt')]
              refine ⟨?_, by simp⟩
              have hx'_km2 : x'[K - 2]'(by rw [hx'_perm.2]; omega) =
                  embBlock (6 * m) K j hjb (rowB'.1[6 * m - 2]'hlt') := by
                have h1 : (mid ++ [a, last])[K - 2]'(by simp [hmid_len]) = a := by
                  rw [List.getElem_append_right (by omega)]; simp [hmid_len]
                have h2 : rowB'.1[6 * m - 2]'hlt' = a' := by
                  rw [ha'_eq]
                  obtain ⟨aB, lastB, midB, _, hFB, hmidB_len, haB_sp, _⟩ := split_first_last (by omega) hrowB.1.2
                  have h3 : (midB ++ [aB, lastB])[6 * m - 2]'(by simp [hmidB_len]) = aB := by
                    rw [List.getElem_append_right (by omega)]; simp [hmidB_len]
                  simpa [hrowB'_1, hFB, haB_sp] using h3
                rw [h2, ← ha_emb]; simpa [x', hF_sp] using h1
              have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hx'_perm).1 hx'_perm
                (canonLoop_isRotated x') (by omega : K - 2 < K) hx'_km2
              have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop x'))).1[6 * m - 2]'(by rw [hbl_x']; exact hlt') =
                  rowB'.1[6 * m - 2]'hlt' := by simp only [hbl_x', rowB']
              change pinAt (canonLoop x') (embBlock (6 * m) K j hjb _) (K - 2) = x'
              rw [harg]; exact hpin.symm
        change (iterW6mRow m hm r K hK (canonLoop (FStep (iterW6mRow m hm r K hK L).1))).1 =
            FStep (iterW6mRow m hm r K hK L).1 ∧
          (iterW6mRow m hm r K hK (canonLoop (FStep (iterW6mRow m hm r K hK L).1))).2 ≠ .D
        rwa [hq_eq]
    closed_S := by
      intro L hL hS
      cases hact : activeLayer m hm r L with
      | none => rw [iterW6mRow_eq_none hm hK hact] at hS; cases hS
      | some j =>
        obtain ⟨hj_lt, hj_neD, hprev⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
        have hjb := hmul_le hj_lt
        have hbl_canon : IsCanonLoop (6 * m) (blockLoop (6 * m) j L) :=
          canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1)
        have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L) hbl_canon
        set rowB := (selW6m m hm).row (blockLoop (6 * m) j L)
        have hrt_S : rowB.2 = .S := by
          cases hc : rowB.2 with
          | D => exact absurd hc hj_neD
          | F =>
            rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hS
            cases hS
          | S => rfl
        have hlenB : 6 * m - 2 < rowB.1.length := by rw [hrowB.1.2]; omega
        let q := pinAt L (embBlock (6 * m) K j hjb (rowB.1[6 * m - 2]'hlenB)) (K - 2)
        have hq_eq : (iterW6mRow m hm r K hK L).1 = q := by
          rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hrt_S hlenB]
        have hq_perm : IsPerm K q := pinAt_isPerm hL.1 _ _
        have hq_km2 : q[K - 2]'(by rw [hq_perm.2]; omega) = embBlock (6 * m) K j hjb (rowB.1[6 * m - 2]'hlenB) :=
          pinAt_getElem hL.1 _ (by omega)
        let x' := SStep q
        have hx'_perm : IsPerm K x' := SStep_isPerm (by omega) hq_perm
        have hother : ∀ i < r, i ≠ j → blockLoop (6 * m) i (canonLoop x') = blockLoop (6 * m) i L := by
          intro i hi hij
          have hib := hmul_le hi
          have hnone : projBlockElem (6 * m) i (q[K - 2]'(by rw [hq_perm.2]; omega)) = none := by
            rw [hq_km2]; exact projBlockElem_embBlock_ne hij hjb _
          have hrot1 : projBlock (6 * m) i x' ~r projBlock (6 * m) i q :=
            projBlock_SStep_of_none hK4 hq_perm.2 (Or.inr hnone)
          have hrot2 : projBlock (6 * m) i q ~r projBlock (6 * m) i L :=
            projBlock_isRotated (pinAt_isRotated L _ _)
          have hrot3 : projBlock (6 * m) i (canonLoop x') ~r projBlock (6 * m) i x' :=
            projBlock_isRotated (canonLoop_isRotated x').symm
          exact (canonLoop_eq_iff (projBlock_isPerm hib (canonLoop_isCanonLoop hx'_perm).1)
            (projBlock_isPerm hib hL.1)).mpr (hrot3.trans (hrot1.trans hrot2))
        have hgoal_q : (iterW6mRow m hm r K hK (canonLoop x')).1 = x' ∧
            (iterW6mRow m hm r K hK (canonLoop x')).2 ≠ .D := by
          obtain ⟨pre, u, v, w, hq_sp, hS_sp, hpre_len, hu_sp, hv_sp, _⟩ := split_last3 hK4 hq_perm.2
          cases hqkm3 : projBlockElem (6 * m) j (q[K - 3]'(by rw [hq_perm.2]; omega)) with
          | none =>
            have hrot1 : projBlock (6 * m) j x' ~r projBlock (6 * m) j q :=
              projBlock_SStep_of_none hK4 hq_perm.2 (Or.inl hqkm3)
            have hbl_x' : blockLoop (6 * m) j (canonLoop x') = blockLoop (6 * m) j L := by
              have hrot_c : projBlock (6 * m) j (canonLoop x') ~r projBlock (6 * m) j x' :=
                projBlock_isRotated (canonLoop_isRotated x').symm
              exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
                (projBlock_isPerm hjb hL.1)).mpr (hrot_c.trans (hrot1.trans (projBlock_isRotated (pinAt_isRotated L _ _))))
            have hact' : activeLayer m hm r (canonLoop x') = some j := by
              rw [activeLayer_eq_some_iff]
              exact ⟨hj_lt, by rw [hbl_x']; exact hj_neD, fun i hi => by rw [hother i (by omega) (by omega)]; exact hprev i hi⟩
            rw [iterW6mRow_eq_S hm hK hact' hj_lt hjb (by rw [hbl_x']; exact hrt_S) (by rw [hbl_x']; exact hlenB)]
            refine ⟨?_, by simp⟩
            have hx'_km2 : x'[K - 2]'(by rw [hx'_perm.2]; omega) =
                embBlock (6 * m) K j hjb (rowB.1[6 * m - 2]'hlenB) := by
              have h1 : ([w] ++ pre ++ [v, u])[K - 2]'(by simp [hpre_len]; omega) = v := by
                rw [List.getElem_append_right (by simp [hpre_len]; omega)]
                simp [hpre_len, show K - 2 - (1 + (K - 3)) = 0 by omega, show K - 2 - (K - 3 + 1) = 0 by omega]
              simpa [x', hS_sp, hv_sp, hq_km2] using h1
            have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hx'_perm).1 hx'_perm
              (canonLoop_isRotated x') (by omega : K - 2 < K) hx'_km2
            have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop x'))).1[6 * m - 2]'(by rw [hbl_x']; exact hlenB) =
                rowB.1[6 * m - 2]'hlenB := by simp only [hbl_x', rowB]
            change pinAt (canonLoop x') (embBlock (6 * m) K j hjb _) (K - 2) = x'
            rw [harg]; exact hpin.symm
          | some u' =>
            have hproj_rot : projBlock (6 * m) j q ~r rowB.1 :=
              (projBlock_isRotated (pinAt_isRotated L _ _)).trans
                ((canonLoop_isRotated _).trans hrowB.2.symm)
            have hkm2_some : projBlockElem (6 * m) j (q[K - 2]'(by rw [hq_perm.2]; omega)) =
                some (rowB.1[6 * m - 2]'(by rw [hrowB.1.2]; omega)) := by
              rw [hq_km2]; exact projBlockElem_embBlock _ _ _ _ _
            obtain ⟨hu'_eq, hproj_x'⟩ := projBlock_SStep_of_both_some (by omega) hK4 hjb hq_perm
              hrowB.1 hproj_rot hkm2_some hqkm3
            have hbl_x' : blockLoop (6 * m) j (canonLoop x') = canonLoop (SStep rowB.1) := by
              have hrot_c : projBlock (6 * m) j (canonLoop x') ~r projBlock (6 * m) j x' :=
                projBlock_isRotated (canonLoop_isRotated x').symm
              rw [hproj_x'] at hrot_c
              exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hx'_perm).1)
                (SStep_isPerm (by omega) hrowB.1)).mpr hrot_c
            have hclS := (selW6m m hm).closed_S (blockLoop (6 * m) j L) hbl_canon hrt_S
            have hnext_F : ((selW6m m hm).row (canonLoop (SStep rowB.1))).2 = .F :=
              selW6m_S_next_is_F m hm hbl_canon hrt_S
            have hact' : activeLayer m hm r (canonLoop x') = some j := by
              rw [activeLayer_eq_some_iff]
              exact ⟨hj_lt, by rw [hbl_x']; exact hclS.2, fun i hi => by rw [hother i (by omega) (by omega)]; exact hprev i hi⟩
            set rowB' := (selW6m m hm).row (canonLoop (SStep rowB.1))
            have hrowB'_1 : rowB'.1 = SStep rowB.1 := hclS.1
            have hlenB' : 6 * m - 1 < rowB'.1.length := by
              rw [hrowB'_1, (SStep_perm _ (by rw [hrowB.1.2]; omega)).length_eq, hrowB.1.2]; omega
            rw [iterW6mRow_eq_F hm hK hact' hj_lt hjb (by rw [hbl_x']; exact hnext_F) (by rw [hbl_x']; exact hlenB')]
            refine ⟨?_, by simp⟩
            have hu_emb : u = embBlock (6 * m) K j hjb u' :=
              (projBlockElem_eq_some_iff (6 * m) j hjb u u').mp (hu_sp ▸ hqkm3)
            have hx'_last : x'[K - 1]'(by rw [hx'_perm.2]; omega) =
                embBlock (6 * m) K j hjb (rowB'.1[6 * m - 1]'hlenB') := by
              have h1 : ([w] ++ pre ++ [v, u])[K - 1]'(by simp [hpre_len]; omega) = u := by
                rw [List.getElem_append_right (by simp [hpre_len]; omega)]
                simp [hpre_len, show K - 1 - (1 + (K - 3)) = 1 by omega, show K - 1 - (K - 3 + 1) = 1 by omega]
              have h2 : rowB'.1[6 * m - 1]'hlenB' = u' := by
                rw [hu'_eq]
                obtain ⟨preB, uB, vB, wB, _, hSB, hpreB_len, huB_sp, _, _⟩ := split_last3 (by omega) hrowB.1.2
                have h3 : ([wB] ++ preB ++ [vB, uB])[6 * m - 1]'(by simp [hpreB_len]; omega) = uB := by
                  rw [List.getElem_append_right (by simp [hpreB_len]; omega)]
                  simp [hpreB_len, show 6 * m - 1 - (1 + (6 * m - 3)) = 1 by omega, show 6 * m - 1 - (6 * m - 3 + 1) = 1 by omega]
                simpa [hrowB'_1, hSB, huB_sp] using h3
              rw [h2, ← hu_emb]; simpa [x', hS_sp] using h1
            have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hx'_perm).1 hx'_perm
              (canonLoop_isRotated x') (by omega : K - 1 < K) hx'_last
            have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop x'))).1[6 * m - 1]'(by rw [hbl_x']; exact hlenB') =
                rowB'.1[6 * m - 1]'hlenB' := by simp only [hbl_x', rowB']
            change pinAt (canonLoop x') (embBlock (6 * m) K j hjb _) (K - 1) = x'
            rw [harg]; exact hpin.symm
        change (iterW6mRow m hm r K hK (canonLoop (SStep (iterW6mRow m hm r K hK L).1))).1 =
            SStep (iterW6mRow m hm r K hK L).1 ∧
          (iterW6mRow m hm r K hK (canonLoop (SStep (iterW6mRow m hm r K hK L).1))).2 ≠ .D
        rwa [hq_eq] }

/-! ### 4. Universal Block-Diagonal Symmetry Fiber Counting Theorem -/

/-- Build a permutation `σ : Equiv.Perm (Fin b)` mapping a permutation `p` to `q` (`p.map σ = q`). -/
theorem exists_perm_map_eq {b : Nat} {p q : List (Fin b)} (hp : IsPerm b p) (hq : IsPerm b q) :
    ∃ σ : Equiv.Perm (Fin b), p.map σ = q := by
  let toIdx (l : List (Fin b)) (hl : IsPerm b l) : Equiv.Perm (Fin b) :=
    { toFun := fun i => l[i.1]'(by rw [hl.2]; exact i.2)
      invFun := fun a => ⟨l.idxOf a, by
        have h1 := List.idxOf_lt_length_of_mem (mem_of_isPerm hl a)
        rw [hl.2] at h1; exact h1⟩
      left_inv := fun i => by
        apply Fin.ext; dsimp
        exact List.Nodup.idxOf_getElem hl.1 i.1 (by rw [hl.2]; exact i.2)
      right_inv := fun a => by
        dsimp; exact List.getElem_idxOf _ }
  let σ : Equiv.Perm (Fin b) := (toIdx q hq) * (toIdx p hp)⁻¹
  refine ⟨σ, ?_⟩
  refine List.ext_getElem (by rw [List.length_map, hp.2, hq.2]) fun i hi1 hi2 => ?_
  rw [List.getElem_map]
  have hi : i < b := by rw [hq.2] at hi2; exact hi2
  change toIdx q hq ((toIdx p hp)⁻¹ (p[i]'(by rw [hp.2]; exact hi))) = q[i]'hi2
  have hinv : (toIdx p hp)⁻¹ (p[i]'(by rw [hp.2]; exact hi)) = ⟨i, hi⟩ := by
    change (toIdx p hp).symm (toIdx p hp ⟨i, hi⟩) = ⟨i, hi⟩
    exact (toIdx p hp).symm_apply_apply ⟨i, hi⟩
  rw [hinv]; rfl

/-- Helper: raw action of block-diagonal permutation on `Fin K`. -/
def blockDiagAct (b r K : Nat) (hK : r * b ≤ K) (τ : Fin r → Equiv.Perm (Fin b)) (x : Fin K) : Fin K :=
  if h : x.1 < r * b then
    have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at h)
    have hj : x.1 / b < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    have ho : x.1 % b < b := Nat.mod_lt x.1 hb_pos
    ⟨x.1 / b * b + (τ ⟨x.1 / b, hj⟩ ⟨x.1 % b, ho⟩).1, by
      have h1 : (x.1 / b + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show x.1 / b + 1 ≤ r by omega)
      have h2 : (τ ⟨x.1 / b, hj⟩ ⟨x.1 % b, ho⟩).1 < b := (τ ⟨x.1 / b, hj⟩ ⟨x.1 % b, ho⟩).2
      have h3 : (x.1 / b + 1) * b = x.1 / b * b + b := by ring
      omega⟩
  else x

theorem blockDiagAct_inv (b r K : Nat) (hK : r * b ≤ K)
    (τ : Fin r → Equiv.Perm (Fin b)) (x : Fin K) :
    blockDiagAct b r K hK (fun j => (τ j)⁻¹) (blockDiagAct b r K hK τ x) = x := by
  apply Fin.ext; unfold blockDiagAct
  by_cases hx : x.1 < r * b
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at hx)
    have hj : x.1 / b < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have ho : x.1 % b < b := Nat.mod_lt x.1 hb_pos
    set y := τ ⟨x.1 / b, hj⟩ ⟨x.1 % b, ho⟩
    have hlt : x.1 / b * b + y.1 < r * b := by
      have h1 : (x.1 / b + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show x.1 / b + 1 ≤ r by omega)
      have h2 : y.1 < b := y.2
      have h3 : (x.1 / b + 1) * b = x.1 / b * b + b := by ring
      omega
    rw [dif_pos hx]
    dsimp only
    rw [dif_pos hlt]
    dsimp only
    have hdiv : (x.1 / b * b + y.1) / b = x.1 / b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb_pos, Nat.div_eq_of_lt y.2, Nat.zero_add]
    have hmod : (x.1 / b * b + y.1) % b = y.1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.2]
    have hfin_j : (⟨(x.1 / b * b + y.1) / b, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm b r]; exact hlt)⟩ : Fin r) = ⟨x.1 / b, hj⟩ :=
      Fin.ext hdiv
    have hfin_o : (⟨(x.1 / b * b + y.1) % b, Nat.mod_lt _ hb_pos⟩ : Fin b) = y :=
      Fin.ext hmod
    have happ : (τ ⟨(x.1 / b * b + y.1) / b, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm b r]; exact hlt)⟩)⁻¹
        ⟨(x.1 / b * b + y.1) % b, Nat.mod_lt _ hb_pos⟩ = ⟨x.1 % b, ho⟩ := by
      rw [hfin_j, hfin_o]; exact (τ ⟨x.1 / b, hj⟩).symm_apply_apply ⟨x.1 % b, ho⟩
    rw [happ, hdiv]
    have := Nat.div_add_mod x.1 b
    rw [Nat.mul_comm] at this; exact this
  · rw [dif_neg hx, dif_neg hx]

/-- Block-diagonal permutation on `Fin K` acting as `σ j` on block `j < r` (of width `b`) and `id` outside. -/
def blockDiagPerm (b r K : Nat) (hK : r * b ≤ K) (σ : Fin r → Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin K) where
  toFun := blockDiagAct b r K hK σ
  invFun := blockDiagAct b r K hK (fun j => (σ j)⁻¹)
  left_inv := blockDiagAct_inv b r K hK σ
  right_inv := fun x => by
    have := blockDiagAct_inv b r K hK (fun j => (σ j)⁻¹) x
    simpa [inv_inv] using this

theorem blockDiagAct_embBlock {b r K : Nat} (hK : r * b ≤ K)
    (τ : Fin r → Equiv.Perm (Fin b)) (j : Fin r)
    (hjb : (j.1 + 1) * b ≤ K) (a : Fin b) :
    blockDiagAct b r K hK τ (embBlock b K j.1 hjb a) = embBlock b K j.1 hjb (τ j a) := by
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact Nat.not_lt_zero _ a.2)
  apply Fin.ext; unfold blockDiagAct embBlock
  have hlt : j.1 * b + a.1 < r * b := by
    have h1 : (j.1 + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega)
    have h2 : (j.1 + 1) * b = j.1 * b + b := by ring
    have ha := a.2; omega
  simp only [hlt, ↓reduceDIte]
  have hdiv : (j.1 * b + a.1) / b = j.1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb_pos, Nat.div_eq_of_lt a.2, Nat.zero_add]
  have hmod : (j.1 * b + a.1) % b = a.1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.2]
  have hfj : (⟨(j.1 * b + a.1) / b, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm b r]; exact hlt)⟩ : Fin r) = j := Fin.ext hdiv
  have hfo : (⟨(j.1 * b + a.1) % b, Nat.mod_lt _ hb_pos⟩ : Fin b) = a := Fin.ext hmod
  have happ : τ ⟨(j.1 * b + a.1) / b, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm b r]; exact hlt)⟩
      ⟨(j.1 * b + a.1) % b, Nat.mod_lt _ hb_pos⟩ = τ j a := by rw [hfj, hfo]
  rw [happ, hdiv]

theorem projBlock_map_blockDiagPerm {b r K : Nat} (hK : r * b ≤ K)
    (σ : Fin r → Equiv.Perm (Fin b)) (j : Fin r) (p : List (Fin K)) :
    projBlock b j.1 (p.map (blockDiagPerm b r K hK σ)) = (projBlock b j.1 p).map (σ j) := by
  have hjb : (j.1 + 1) * b ≤ K := by
    have h1 : (j.1 + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega)
    omega
  unfold projBlock
  induction p with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.filterMap_cons]
    cases hx : projBlockElem b j.1 x with
    | some a =>
      have hx_eq : x = embBlock b K j.1 hjb a := (projBlockElem_eq_some_iff b j.1 hjb x a).mp hx
      have hmap_x : blockDiagPerm b r K hK σ x = embBlock b K j.1 hjb (σ j a) := by
        rw [hx_eq]; exact blockDiagAct_embBlock hK σ j hjb a
      rw [hmap_x, projBlockElem_embBlock, ih]; rfl
    | none =>
      have hmap_none : projBlockElem b j.1 (blockDiagPerm b r K hK σ x) = none := by
        by_contra hne
        cases hsome : projBlockElem b j.1 (blockDiagPerm b r K hK σ x) with
        | none => exact hne hsome
        | some a' =>
          have hy := (projBlockElem_eq_some_iff b j.1 hjb _ a').mp hsome
          have hinv_y : x = (blockDiagPerm b r K hK σ).symm (embBlock b K j.1 hjb a') := by
            rw [← hy, Equiv.symm_apply_apply]
          have hx_in : x = embBlock b K j.1 hjb ((σ j)⁻¹ a') := by
            rw [hinv_y]; exact blockDiagAct_embBlock hK (fun k => (σ k)⁻¹) j hjb a'
          rw [hx_in, projBlockElem_embBlock] at hx; cases hx
      rw [hmap_none, ih]

/-- **Universal Block-Diagonal Symmetry Theorem (on ANY list `Ω` closed under `blockDiagPerm`!):**
If `Ω : List α` is duplicate-free, `extract : α → Fin r → List (Fin b)` always returns `IsCanonLoop b`,
and for every `σ : Fin r → Equiv.Perm (Fin b)` there is a bijection `act σ : α → α` preserving `Ω`
and transforming `extract (act σ x) j = canonLoop ((extract x j).map (σ j))`,
then ALL `((b - 1)!)^r` fibers of `extract` in `Ω` have EQUAL cardinality! -/
theorem uniform_block_fibers {α : Type} [DecidableEq α] {b : Nat} [NeZero b] (r : Nat)
    (Ω : List α) (hΩ_nd : Ω.Nodup)
    (extract : α → Fin r → List (Fin b))
    (hextract_ok : ∀ x ∈ Ω, ∀ j : Fin r, IsCanonLoop b (extract x j))
    (act : (Fin r → Equiv.Perm (Fin b)) → α → α)
    (hact_mem : ∀ σ x, x ∈ Ω → act σ x ∈ Ω)
    (hact_inv : ∀ σ x, x ∈ Ω → act (fun j => (σ j)⁻¹) (act σ x) = x)
    (hact_ext : ∀ σ x, x ∈ Ω → ∀ j : Fin r, extract (act σ x) j = canonLoop ((extract x j).map (σ j))) :
    ∀ (t1 t2 : Fin r → List (Fin b)),
      (∀ j, IsCanonLoop b (t1 j)) → (∀ j, IsCanonLoop b (t2 j)) →
      (Ω.filter (fun x => decide (extract x = t1))).length =
      (Ω.filter (fun x => decide (extract x = t2))).length := by
  intro t1 t2 ht1 ht2
  -- Choose `σ j` mapping `t1 j` to `t2 j` for each `j : Fin r`!
  have hex : ∀ j : Fin r, ∃ σj : Equiv.Perm (Fin b), (t1 j).map σj = t2 j :=
    fun j => exists_perm_map_eq (ht1 j).1 (ht2 j).1
  choose σ hσ using hex
  let F1 := Ω.filter (fun x => decide (extract x = t1))
  let F2 := Ω.filter (fun x => decide (extract x = t2))
  have hnd1 : (F1.map (act σ)).Nodup := by
    refine (List.nodup_map_iff_inj_on (hΩ_nd.filter _)).mpr ?_
    intro x hx y hy heq
    have hxΩ : x ∈ Ω := (List.mem_filter.mp hx).1
    have hyΩ : y ∈ Ω := (List.mem_filter.mp hy).1
    have := congrArg (act (fun j => (σ j)⁻¹)) heq
    rwa [hact_inv σ x hxΩ, hact_inv σ y hyΩ] at this
  have hperm : (F1.map (act σ)).Perm F2 := by
    refine (List.perm_ext_iff_of_nodup hnd1 (hΩ_nd.filter _)).mpr ?_
    intro y
    simp only [F1, F2, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨x, ⟨hxΩ, hxt1⟩, rfl⟩
      refine ⟨hact_mem σ x hxΩ, ?_⟩
      funext j
      rw [hact_ext σ x hxΩ j, hxt1, hσ j, canonLoop_self (ht2 j)]
    · rintro ⟨hyΩ, hyt2⟩
      let x := act (fun j => (σ j)⁻¹) y
      have hxΩ : x ∈ Ω := hact_mem _ y hyΩ
      have hact_x : act σ x = y := by
        have := hact_inv (fun j => (σ j)⁻¹) y hyΩ
        simpa [inv_inv] using this
      refine ⟨x, ⟨hxΩ, ?_⟩, hact_x⟩
      funext j
      rw [hact_ext _ y hyΩ j, hyt2]
      have hmap_inv : (t2 j).map (⇑((σ j)⁻¹)) = t1 j := by
        rw [← hσ j, List.map_map]
        have : (⇑((σ j)⁻¹) ∘ ⇑(σ j)) = id := by funext a; exact (σ j).symm_apply_apply a
        simp [this]
      rw [hmap_inv, canonLoop_self (ht1 j)]
  rw [← hperm.length_eq, List.length_map]

/-- Enumerate all `((b - 1)!)^r` valid `r`-tuples of canonical loops on `Fin b`. -/
def allBlockTuples (b : Nat) [NeZero b] : (r : Nat) → List (Fin r → List (Fin b))
  | 0 => [Fin.elim0]
  | r + 1 =>
    (allCanonLoops b).flatMap fun L =>
      (allBlockTuples b r).map fun t => Fin.cons L t

theorem allBlockTuples_length (b : Nat) [NeZero b] (r : Nat) :
    (allBlockTuples b r).length = (Almanac.fact (b - 1)) ^ r := by
  induction r with
  | zero => simp [allBlockTuples]
  | succ r ih =>
    simp [allBlockTuples, List.length_flatMap, ih, allCanonLoops_length, pow_succ']

theorem allBlockTuples_nodup (b : Nat) [NeZero b] (r : Nat) :
    (allBlockTuples b r).Nodup := by
  induction r with
  | zero => simp [allBlockTuples]
  | succ r ih =>
    dsimp [allBlockTuples]
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro L _
      refine List.Nodup.map ?_ ih
      intro t1 t2 h
      funext j
      have := congrFun h j.succ
      simpa using this
    · refine List.Pairwise.imp_of_mem ?_ (allCanonLoops_nodup b)
      intro L1 L2 _ _ hne
      change List.Disjoint _ _
      rw [List.disjoint_iff_ne]
      intro f1 hf1 f2 hf2 heq
      rw [List.mem_map] at hf1 hf2
      obtain ⟨t1, _, rfl⟩ := hf1
      obtain ⟨t2, _, rfl⟩ := hf2
      have := congrFun heq 0
      simp at this
      exact hne this

theorem mem_allBlockTuples_iff (b : Nat) [NeZero b] :
    ∀ (r : Nat) (t : Fin r → List (Fin b)),
      t ∈ allBlockTuples b r ↔ ∀ j : Fin r, IsCanonLoop b (t j)
  | 0, t => by
    simp only [allBlockTuples, List.mem_singleton]
    constructor
    · intro _ j; exact Fin.elim0 j
    · intro _; funext j; exact Fin.elim0 j
  | r + 1, t => by
    simp only [allBlockTuples, List.mem_flatMap, List.mem_map, mem_allCanonLoops_iff,
      mem_allBlockTuples_iff b r]
    constructor
    · rintro ⟨L, hL, t', ht', rfl⟩ j
      refine Fin.cases hL (fun k => ht' k) j
    · intro h
      refine ⟨t 0, h 0, fun k => t k.succ, fun k => h k.succ, ?_⟩
      funext j
      refine Fin.cases rfl (fun k => rfl) j

/-- **Master Uniform Counting Identity:** Under uniform block fibers, for ANY predicate `P` on `r`-tuples,
`((b - 1)!)^r * |{x ∈ Ω | P (extract x)}| = |{t ∈ allBlockTuples b r | P t}| * |Ω|`! -/
theorem uniform_block_count {α : Type} [DecidableEq α] {b : Nat} [NeZero b] (r : Nat)
    (Ω : List α) (hΩ_nd : Ω.Nodup)
    (extract : α → Fin r → List (Fin b))
    (hextract_ok : ∀ x ∈ Ω, ∀ j : Fin r, IsCanonLoop b (extract x j))
    (huniform : ∀ t1 t2 : Fin r → List (Fin b),
      (∀ j, IsCanonLoop b (t1 j)) → (∀ j, IsCanonLoop b (t2 j)) →
      (Ω.filter (fun x => decide (extract x = t1))).length =
      (Ω.filter (fun x => decide (extract x = t2))).length)
    (P : (Fin r → List (Fin b)) → Bool) :
    (Almanac.fact (b - 1)) ^ r * (Ω.filter (fun x => P (extract x))).length =
      ((allBlockTuples b r).filter P).length * Ω.length := by
  -- Pick the canonical default tuple `t0` (`id_b` in every block) to represent the common fiber size `c`!
  let L0 : List (Fin b) := List.finRange b
  have hL0 : IsCanonLoop b L0 := by
    refine ⟨⟨List.nodup_finRange b, List.length_finRange⟩, ?_⟩
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp [L0]; exact NeZero.pos b)]
    simp [L0]
  let t0 : Fin r → List (Fin b) := fun _ => L0
  have ht0 : ∀ j, IsCanonLoop b (t0 j) := fun _ => hL0
  let c := (Ω.filter (fun x => decide (extract x = t0))).length
  -- General partition sum lemma: for ANY `T : List (Fin r → List (Fin b))` of valid distinct tuples,
  -- `|{x ∈ Ω | extract x ∈ T}| = T.length * c`!
  have hpart : ∀ (T : List (Fin r → List (Fin b))), T.Nodup →
      (∀ t ∈ T, ∀ j, IsCanonLoop b (t j)) →
      (Ω.filter (fun x => decide (extract x ∈ T))).length = T.length * c := by
    intro T
    induction T with
    | nil => intro _ _; simp
    | cons t ts ih =>
      intro hnd hval
      have ⟨ht_notin, hts_nd⟩ := List.nodup_cons.mp hnd
      have ht_ok : ∀ j, IsCanonLoop b (t j) := hval t List.mem_cons_self
      have hts_ok : ∀ s ∈ ts, ∀ j, IsCanonLoop b (s j) := fun s hs => hval s (List.mem_cons_of_mem _ hs)
      -- Split `Ω.filter (extract x ∈ t :: ts)` into `extract x = t` and `extract x ∈ ts`!
      have hdisj : ∀ (l : List α),
          (l.filter (fun x => decide (extract x ∈ t :: ts))).length =
          (l.filter (fun x => decide (extract x = t))).length +
          (l.filter (fun x => decide (extract x ∈ ts))).length := by
        intro l
        induction l with
        | nil => simp
        | cons a as iha =>
          rw [List.filter_cons, List.filter_cons, List.filter_cons]
          by_cases h1 : extract a = t
          · have h2 : extract a ∉ ts := h1 ▸ ht_notin
            have h3 : extract a ∈ t :: ts := List.mem_cons.mpr (Or.inl h1)
            simp only [decide_eq_true h1, decide_eq_false h2, decide_eq_true h3, ↓reduceIte,
              Bool.false_eq_true, List.length_cons, iha]
            omega
          · by_cases h2 : extract a ∈ ts
            · have h3 : extract a ∈ t :: ts := List.mem_cons.mpr (Or.inr h2)
              simp only [decide_eq_false h1, decide_eq_true h2, decide_eq_true h3, ↓reduceIte,
                Bool.false_eq_true, List.length_cons, iha]
              omega
            · have h3 : extract a ∉ t :: ts := by simp [List.mem_cons, h1, h2]
              simp only [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3,
                Bool.false_eq_true, ↓reduceIte, iha]
      rw [hdisj Ω, ih hts_nd hts_ok, huniform t t0 ht_ok ht0]
      simp [c]; ring
  -- Apply `hpart` to `allBlockTuples b r` and to `(allBlockTuples b r).filter P`!
  have hall_eq : Ω.filter (fun x => decide (extract x ∈ allBlockTuples b r)) = Ω := by
    rw [List.filter_eq_self]
    intro x hx
    simp [mem_allBlockTuples_iff, hextract_ok x hx]
  have hΩ_eq : Ω.length = (Almanac.fact (b - 1)) ^ r * c := by
    have := hpart (allBlockTuples b r) (allBlockTuples_nodup b r)
      (fun t ht => (mem_allBlockTuples_iff b r t).mp ht)
    rw [hall_eq, allBlockTuples_length] at this
    exact this
  have hP_eq : Ω.filter (fun x => P (extract x)) =
      Ω.filter (fun x => decide (extract x ∈ (allBlockTuples b r).filter P)) := by
    refine List.filter_congr fun x hx => ?_
    simp [List.mem_filter, mem_allBlockTuples_iff, hextract_ok x hx]
  have hfilt_eq : (Ω.filter (fun x => P (extract x))).length = ((allBlockTuples b r).filter P).length * c := by
    rw [hP_eq]
    exact hpart ((allBlockTuples b r).filter P) ((allBlockTuples_nodup b r).filter P)
      (fun t ht => (mem_allBlockTuples_iff b r t).mp (List.mem_filter.mp ht).1)
  rw [hfilt_eq, hΩ_eq]; ring

/-- Specialization of `uniform_block_count` to `Ω = allCanonLoops K` (`K ≥ r * b`)! -/
theorem allCanonLoops_block_count {b : Nat} [NeZero b] (r K : Nat) [NeZero K] (hK : r * b ≤ K)
    (P : (Fin r → List (Fin b)) → Bool) :
    (Almanac.fact (b - 1)) ^ r *
      ((allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop b j.1 L))).length =
    ((allBlockTuples b r).filter P).length * Almanac.fact (K - 1) := by
  have hact_perm : ∀ σ L, IsCanonLoop K L → IsPerm K (L.map (blockDiagPerm b r K hK σ)) := by
    intro σ L hL
    exact ⟨hL.1.1.map (blockDiagPerm b r K hK σ).injective, by rw [List.length_map, hL.1.2]⟩
  have hmul_j : ∀ j : Fin r, (j.1 + 1) * b ≤ K := fun j => by
    have h1 : (j.1 + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega)
    omega
  have huni := uniform_block_fibers (α := List (Fin K)) (b := b) r (allCanonLoops K)
    (allCanonLoops_nodup K)
    (fun L j => blockLoop b j.1 L)
    (fun L hL j => by
      have hL' := (mem_allCanonLoops_iff L).mp hL
      exact canonLoop_isCanonLoop (projBlock_isPerm (hmul_j j) hL'.1))
    (fun σ L => canonLoop (L.map (blockDiagPerm b r K hK σ)))
    (fun σ L hL => by
      rw [mem_allCanonLoops_iff] at hL ⊢
      exact canonLoop_isCanonLoop (hact_perm σ L hL))
    (fun σ L hL => by
      have hL' := (mem_allCanonLoops_iff L).mp hL
      have hp1 := hact_perm σ L hL'
      have hrot1 : (canonLoop (L.map (blockDiagPerm b r K hK σ))).map (blockDiagPerm b r K hK (fun j => (σ j)⁻¹)) ~r
          (L.map (blockDiagPerm b r K hK σ)).map (blockDiagPerm b r K hK (fun j => (σ j)⁻¹)) :=
        (canonLoop_isRotated _).symm.map _
      have hinv_map : (L.map (blockDiagPerm b r K hK σ)).map (blockDiagPerm b r K hK (fun j => (σ j)⁻¹)) = L := by
        rw [List.map_map]
        have hcomp : ((blockDiagPerm b r K hK (fun j => (σ j)⁻¹)) ∘ (blockDiagPerm b r K hK σ)) = id := by
          funext x; exact (blockDiagPerm b r K hK σ).left_inv x
        simp [hcomp]
      rw [hinv_map] at hrot1
      have hp2 : IsPerm K ((canonLoop (L.map (blockDiagPerm b r K hK σ))).map
          (blockDiagPerm b r K hK (fun j => (σ j)⁻¹))) :=
        hact_perm _ _ (canonLoop_isCanonLoop hp1)
      exact isCanonLoop_eq_of_isRotated (canonLoop_isCanonLoop hp2) hL'
        ((canonLoop_isRotated _).symm.trans hrot1))
    (fun σ L hL j => by
      have hL' := (mem_allCanonLoops_iff L).mp hL
      have hjb := hmul_j j
      have hp1 := hact_perm σ L hL'
      have hrot1 : projBlock b j.1 (canonLoop (L.map (blockDiagPerm b r K hK σ))) ~r
          projBlock b j.1 (L.map (blockDiagPerm b r K hK σ)) :=
        projBlock_isRotated (canonLoop_isRotated _).symm
      rw [projBlock_map_blockDiagPerm] at hrot1
      have hrot2 : (projBlock b j.1 L).map (σ j) ~r (blockLoop b j.1 L).map (σ j) :=
        (canonLoop_isRotated _).map _
      have hpL : IsPerm b (projBlock b j.1 L) := projBlock_isPerm hjb hL'.1
      have hpB : IsPerm b ((blockLoop b j.1 L).map (σ j)) :=
        ⟨(canonLoop_isCanonLoop hpL).1.1.map (σ j).injective,
          by rw [List.length_map]; exact (canonLoop_isCanonLoop hpL).1.2⟩
      exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hp1).1) hpB).mpr
        (hrot1.trans hrot2))
  have hcnt := uniform_block_count r (allCanonLoops K) (allCanonLoops_nodup K)
    (fun L j => blockLoop b j.1 L)
    (fun L hL j => by
      have hL' := (mem_allCanonLoops_iff L).mp hL
      exact canonLoop_isCanonLoop (projBlock_isPerm (hmul_j j) hL'.1))
    huni P
  rwa [allCanonLoops_length] at hcnt

/-! ### 5. Exact `'D'`-loop and `'S'`-row counts of `iterW6mLift` -/

/-- Exact number of `'D'`-tuples in `allBlockTuples (6 * m) r` is `D_b^r`. -/
theorem count_allD_tuples (m : Nat) (hm : 1 ≤ m) (r : Nat) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    ((allBlockTuples (6 * m) r).filter (fun t => decide (∀ j : Fin r, ((selW6m m hm).row (t j)).2 = .D))).length =
      Db ^ r := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hDb : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .D)).length =
      Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2) := (selW6m_counts m hm).2.2
  induction r with
  | zero => simp [allBlockTuples]
  | succ r ih =>
    dsimp [allBlockTuples]
    rw [List.filter_flatMap]
    have hstep : ∀ L ∈ allCanonLoops (6 * m),
        (((allBlockTuples (6 * m) r).map (fun t => Fin.cons L t)).filter
          (fun t => decide (∀ j : Fin (r + 1), ((selW6m m hm).row (t j)).2 = .D))).length =
        if ((selW6m m hm).row L).2 == .D then
          (Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) ^ r
        else 0 := by
      intro L _
      rw [List.filter_map, List.length_map]
      by_cases hD : ((selW6m m hm).row L).2 = .D
      · have hbeq : (((selW6m m hm).row L).2 == .D) = true := by simp [hD]
        simp only [hbeq, ↓reduceIte]
        have hcongr : (allBlockTuples (6 * m) r).filter
            ((fun t : Fin (r + 1) → List (Fin (6 * m)) => decide (∀ j, ((selW6m m hm).row (t j)).2 = .D)) ∘
              fun t => Fin.cons L t) =
            (allBlockTuples (6 * m) r).filter (fun t => decide (∀ j : Fin r, ((selW6m m hm).row (t j)).2 = .D)) := by
          refine List.filter_congr fun t _ => ?_
          simp only [Function.comp_def, decide_eq_decide, Fin.forall_fin_succ, Fin.cons_zero,
            Fin.cons_succ, hD, true_and]
        rw [hcongr, ih]
      · have hbeq : (((selW6m m hm).row L).2 == .D) = false := by
          cases hc : ((selW6m m hm).row L).2 <;> simp [hc] at hD ⊢
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro t _
        simp only [Function.comp_def, decide_eq_true_eq, not_forall]
        exact ⟨0, by simpa using hD⟩
    rw [List.length_flatMap, List.map_congr_left hstep]
    have hsum_ite : ∀ (l : List (List (Fin (6 * m)))) (f : List (Fin (6 * m)) → Bool) (c : Nat),
        (l.map (fun x => if f x then c else 0)).sum = (l.filter f).length * c := by
      intro l f c
      induction l with
      | nil => simp
      | cons a as iha =>
        cases hf : f a <;> simp [hf, iha, Nat.succ_mul] <;> ring
    rw [hsum_ite, hDb, pow_succ']

/-- Exact number of `'S'`-tuples (at active layer `j < r`) in `allBlockTuples (6 * m) r`. -/
theorem count_S_tuples_le (m : Nat) (hm : 1 ≤ m) (r : Nat) :
    letI : NeZero (6 * m) := ⟨by omega⟩
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    let F := Almanac.fact (6 * m - 1)
    let isSTuple : (Fin r → List (Fin (6 * m))) → Bool := fun t =>
      match (List.range r).find? (fun j =>
          if hj : j < r then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
      | none => false
      | some j => if hj : j < r then ((selW6m m hm).row (t ⟨j, hj⟩)).2 == .S else false
    ((allBlockTuples (6 * m) r).filter isSTuple).length * (4 * m * (6 * m - 2)) ≤
      (4 * m) * F ^ r := by
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hS : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .S)).length = 4 * m :=
    (selW6m_counts m hm).1
  have hDb : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 == .D)).length =
      Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2) := (selW6m_counts m hm).2.2
  have hLb_le : 4 * m * (6 * m - 2) ≤ Almanac.fact (6 * m - 1) := by
    have h1 := (selW6m_counts m hm).2.1
    have h2 : ((allCanonLoops (6 * m)).filter (fun L => ((selW6m m hm).row L).2 != .D)).length ≤
        (allCanonLoops (6 * m)).length := List.length_filter_le _ _
    rw [h1, allCanonLoops_length] at h2; exact h2
  -- Prove exact closed-form recursion by induction on `r`:
  -- `c(r) * L_b = 4m * (F^r - D_b^r)` (hence `≤ 4m * F^r`)!
  let c : Nat → Nat := fun k =>
    ((allBlockTuples (6 * m) k).filter (fun t =>
      match (List.range k).find? (fun j =>
          if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
      | none => false
      | some j => if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 == .S else false)).length
  have hrec : ∀ k, c (k + 1) =
      4 * m * (Almanac.fact (6 * m - 1)) ^ k +
      (Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) * c k := by
    intro k
    dsimp only [c, allBlockTuples]
    rw [List.filter_flatMap, List.length_flatMap]
    have hstep : ∀ L ∈ allCanonLoops (6 * m),
        (((allBlockTuples (6 * m) k).map (fun t : Fin k → List (Fin (6 * m)) => Fin.cons L t)).filter
          (fun t : Fin (k + 1) → List (Fin (6 * m)) =>
            match (List.range (k + 1)).find? (fun j =>
                if hj : j < k + 1 then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
            | none => false
            | some j => if hj : j < k + 1 then ((selW6m m hm).row (t ⟨j, hj⟩)).2 == .S else false)).length =
        if ((selW6m m hm).row L).2 == .S then (Almanac.fact (6 * m - 1)) ^ k
        else if ((selW6m m hm).row L).2 == .D then c k
        else 0 := by
      intro L _
      rw [List.filter_map, List.length_map]
      cases hrt : ((selW6m m hm).row L).2 with
      | S =>
        simp only [beq_self_eq_true, ↓reduceIte]
        have hall : ∀ t ∈ allBlockTuples (6 * m) k,
            ((fun t' : Fin (k + 1) → List (Fin (6 * m)) =>
              match (List.range (k + 1)).find? (fun j =>
                  if hj : j < k + 1 then ((selW6m m hm).row (t' ⟨j, hj⟩)).2 != .D else false) with
              | none => false
              | some j => if hj : j < k + 1 then ((selW6m m hm).row (t' ⟨j, hj⟩)).2 == .S else false) ∘
              fun t => Fin.cons L t) t = true := by
          intro t _
          have h0 : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := rfl
          have hSD : (RowType.S != RowType.D) = true := rfl
          simp only [Function.comp_def, List.range_succ_eq_map, List.find?_cons,
            show (0 : Nat) < k + 1 by omega, ↓reduceDIte, h0, Fin.cons_zero, hrt, hSD,
            beq_self_eq_true]
        rw [List.filter_eq_self.mpr hall, allBlockTuples_length]
      | F =>
        simp only [reduceCtorEq, beq_iff_eq, ↓reduceIte]
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro t _
        have h0 : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := rfl
        have hFD : (RowType.F != RowType.D) = true := rfl
        have hFS : (RowType.F == RowType.S) = false := rfl
        simp only [Function.comp_def, List.range_succ_eq_map, List.find?_cons,
          show (0 : Nat) < k + 1 by omega, ↓reduceDIte, h0, Fin.cons_zero, hrt, hFD, hFS,
          Bool.false_eq_true, not_false_eq_true]
      | D =>
        simp only [reduceCtorEq, beq_iff_eq, ↓reduceIte, beq_self_eq_true]
        have hcongr : (allBlockTuples (6 * m) k).filter
            ((fun t' : Fin (k + 1) → List (Fin (6 * m)) =>
              match (List.range (k + 1)).find? (fun j =>
                  if hj : j < k + 1 then ((selW6m m hm).row (t' ⟨j, hj⟩)).2 != .D else false) with
              | none => false
              | some j => if hj : j < k + 1 then ((selW6m m hm).row (t' ⟨j, hj⟩)).2 == .S else false) ∘
              fun t => Fin.cons L t) =
            (allBlockTuples (6 * m) k).filter (fun t =>
              match (List.range k).find? (fun j =>
                  if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
              | none => false
              | some j => if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 == .S else false) := by
          refine List.filter_congr fun t _ => ?_
          have h0 : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := rfl
          simp only [Function.comp_def, List.range_succ_eq_map, List.find?_cons,
            show (0 : Nat) < k + 1 by omega, ↓reduceDIte, h0, Fin.cons_zero, hrt, bne_self_eq_false,
            List.find?_map]
          have hpred : (fun j => if hj : j.succ < k + 1 then ((selW6m m hm).row (Fin.cons (α := fun _ => List (Fin (6 * m))) L t ⟨j.succ, hj⟩)).2 != .D else false) =
              (fun j => if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) := by
            funext j
            by_cases hj : j < k
            · have hjs : j.succ < k + 1 := by omega
              simp only [hj, hjs, ↓reduceDIte]; rfl
            · have hjs : ¬(j.succ < k + 1) := by omega
              simp only [hj, hjs, ↓reduceDIte]
          change (match Option.map Nat.succ ((List.range k).find?
              (fun j => if hj : j.succ < k + 1 then ((selW6m m hm).row (Fin.cons (α := fun _ => List (Fin (6 * m))) L t ⟨j.succ, hj⟩)).2 != .D else false)) with
            | none => false
            | some j => if hj : j < k + 1 then ((selW6m m hm).row (Fin.cons (α := fun _ => List (Fin (6 * m))) L t ⟨j, hj⟩)).2 == RowType.S else false) = _
          rw [hpred]
          cases (List.range k).find? (fun j => if hj : j < k then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
          | none => rfl
          | some j =>
            simp only [Option.map_some]
            by_cases hj : j < k
            · have hjs : j.succ < k + 1 := by omega
              simp only [hj, hjs, ↓reduceDIte]; rfl
            · have hjs : ¬(j.succ < k + 1) := by omega
              simp only [hj, hjs, ↓reduceDIte]
        rw [hcongr]
    rw [List.map_congr_left hstep]
    have hsum : ∀ (l : List (List (Fin (6 * m)))) (a b : Nat),
        (l.map (fun L => if ((selW6m m hm).row L).2 == .S then a
                         else if ((selW6m m hm).row L).2 == .D then b else 0)).sum =
        (l.filter (fun L => ((selW6m m hm).row L).2 == .S)).length * a +
        (l.filter (fun L => ((selW6m m hm).row L).2 == .D)).length * b := by
      intro l a b
      have hSD : (RowType.S == RowType.D) = false := rfl
      have hDS : (RowType.D == RowType.S) = false := rfl
      have hFS : (RowType.F == RowType.S) = false := rfl
      have hFD : (RowType.F == RowType.D) = false := rfl
      induction l with
      | nil => simp
      | cons x xs ihx =>
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        cases hc : ((selW6m m hm).row x).2 <;>
          simp only [hSD, hDS, hFS, hFD, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
            List.length_cons, ihx] <;> ring
    rw [hsum, hS, hDb]
  -- Now prove `c k * L_b + 4 * m * Db^k = 4 * m * F^k` by induction on `k`!
  have hexact : ∀ k, c k * (4 * m * (6 * m - 2)) +
      4 * m * (Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) ^ k =
      4 * m * (Almanac.fact (6 * m - 1)) ^ k := by
    intro k
    induction k with
    | zero => simp [c, allBlockTuples]
    | succ k ih =>
      rw [hrec k]
      set F := Almanac.fact (6 * m - 1)
      set L := 4 * m * (6 * m - 2)
      set D := F - L
      have hFD : D + L = F := Nat.sub_add_cancel hLb_le
      calc (4 * m * F ^ k + D * c k) * L + 4 * m * D ^ (k + 1)
          = 4 * m * F ^ k * L + D * (c k * L + 4 * m * D ^ k) := by rw [pow_succ']; ring
        _ = 4 * m * F ^ k * L + D * (4 * m * F ^ k) := by rw [ih]
        _ = 4 * m * F ^ k * (D + L) := by ring
        _ = 4 * m * F ^ (k + 1) := by rw [hFD, pow_succ]; ring
  have := hexact r
  dsimp [c] at this
  omega

/-- Exact `'S'`-row bound for `iterW6mLift m hm r K hK`:
`((allCanonLoops K).filter (row = .S)).length * (4m * (6m - 2)) ≤ 4m * (K - 1)!`! -/
theorem iterW6mLift_S_count_le (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    letI : NeZero K := ⟨by have := Nat.mul_le_mul_right (6 * m) hr; omega⟩
    ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .S)).length *
      (4 * m * (6 * m - 2)) ≤ 4 * m * Almanac.fact (K - 1) := by
  let _ : NeZero K := ⟨by have := Nat.mul_le_mul_right (6 * m) hr; omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  let P : (Fin r → List (Fin (6 * m))) → Bool := fun t =>
    match (List.range r).find? (fun j =>
        if hj : j < r then ((selW6m m hm).row (t ⟨j, hj⟩)).2 != .D else false) with
    | none => false
    | some j => if hj : j < r then ((selW6m m hm).row (t ⟨j, hj⟩)).2 == .S else false
  have hcongr : (allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .S) =
      (allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop (6 * m) j.1 L)) := by
    refine List.filter_congr fun L hL => ?_
    have hL' := (mem_allCanonLoops_iff L).mp hL
    have hfind_eq : (List.range r).find? (fun j =>
        if hj : j < r then ((selW6m m hm).row (blockLoop (6 * m) j L)).2 != .D else false) =
        activeLayer m hm r L := by
      unfold activeLayer
      refine List.find?_congr ?_
      intro j hj; rw [List.mem_range] at hj; simp [hj]
    dsimp only [iterW6mLift, iterW6mRow, P]
    rw [hfind_eq]
    cases hact : activeLayer m hm r L with
    | none => rfl
    | some j =>
      obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
      have hjb : (j + 1) * (6 * m) ≤ K := by
        have h1 : (j + 1) * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega)
        omega
      have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L)
        (canonLoop_isCanonLoop (projBlock_isPerm hjb hL'.1))
      have hlen1 : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by rw [hrowB.1.2]; omega
      have hlen2 : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by rw [hrowB.1.2]; omega
      simp only [hj_lt, ↓reduceDIte]
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
      | D => simp
      | F => simp [hlen1]
      | S => simp [hlen2]
  rw [hcongr]
  have hcnt := allCanonLoops_block_count (b := 6 * m) r K (by omega) P
  have hle := count_S_tuples_le m hm r
  have hFpos : 0 < (Almanac.fact (6 * m - 1)) ^ r := by
    refine pow_pos ?_ r
    have hfact_pos : ∀ n : Nat, 0 < Almanac.fact n := by
      intro n; induction n with
      | zero => exact Nat.zero_lt_one
      | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih
    exact hfact_pos _
  have hmul : (Almanac.fact (6 * m - 1)) ^ r *
      (((allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop (6 * m) j.1 L))).length *
        (4 * m * (6 * m - 2))) ≤
      (Almanac.fact (6 * m - 1)) ^ r * (4 * m * Almanac.fact (K - 1)) := by
    calc (Almanac.fact (6 * m - 1)) ^ r *
          (((allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop (6 * m) j.1 L))).length *
            (4 * m * (6 * m - 2)))
        = ((Almanac.fact (6 * m - 1)) ^ r *
            ((allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop (6 * m) j.1 L))).length) *
            (4 * m * (6 * m - 2)) := by ring
      _ = (((allBlockTuples (6 * m) r).filter P).length * (4 * m * (6 * m - 2))) *
            Almanac.fact (K - 1) := by rw [hcnt]; ring
      _ ≤ (4 * m * (Almanac.fact (6 * m - 1)) ^ r) * Almanac.fact (K - 1) :=
            Nat.mul_le_mul_right _ hle
      _ = (Almanac.fact (6 * m - 1)) ^ r * (4 * m * Almanac.fact (K - 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hFpos

/-- Exact `'D'`-loop count of `iterW6mLift m hm r hr K hK`:
`((6m - 1)!)^r * |D-loops| = D_b^r * (K - 1)!`! -/
theorem iterW6mLift_D_count (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    letI : NeZero K := ⟨by have := Nat.mul_le_mul_right (6 * m) hr; omega⟩
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    (Almanac.fact (6 * m - 1)) ^ r *
      ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).length =
    Db ^ r * Almanac.fact (K - 1) := by
  let _ : NeZero K := ⟨by have := Nat.mul_le_mul_right (6 * m) hr; omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  let P : (Fin r → List (Fin (6 * m))) → Bool :=
    fun t => decide (∀ j : Fin r, ((selW6m m hm).row (t j)).2 = .D)
  have hcongr : (allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D) =
      (allCanonLoops K).filter (fun L => P (fun j : Fin r => blockLoop (6 * m) j.1 L)) := by
    refine List.filter_congr fun L hL => ?_
    have hL' := (mem_allCanonLoops_iff L).mp hL
    dsimp only [iterW6mLift, P]
    cases hact : activeLayer m hm r L with
    | none =>
      rw [iterW6mRow_eq_none hm hK hact]
      have hall := (activeLayer_eq_none_iff m hm r L).mp hact
      simp [hall]
    | some j =>
      obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
      have hjb : (j + 1) * (6 * m) ≤ K := by
        have h1 : (j + 1) * (6 * m) ≤ r * (6 * m) := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega)
        omega
      have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L)
        (canonLoop_isCanonLoop (projBlock_isPerm hjb hL'.1))
      have hnotall : ¬(∀ i : Fin r, ((selW6m m hm).row (blockLoop (6 * m) i.1 L)).2 = .D) :=
        fun h => hj_neD (h ⟨j, hj_lt⟩)
      rw [decide_eq_false hnotall]
      cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
      | D => exact absurd hc hj_neD
      | F =>
        rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; rfl
      | S =>
        rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; rfl
  rw [hcongr, allCanonLoops_block_count (b := 6 * m) r K (by omega) P, count_allD_tuples m hm r]

end AsymptoticZero
