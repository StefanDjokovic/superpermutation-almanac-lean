import AsymptoticZero.LayerSliceGraph

/-!
# AsymptoticZero.StarsAndBars (Lemma 3 — Part 2)

Proves `WeaklyConnected (layerBag m hm r hr K hK hj σ)` for every layer `j < r` and every
surviving linear order `σ ∈ allLayerSigmas j`, using our 5 crisp sublemmas:
* **Sublemma A:** Every `ck ∈ zCyclesOf j σ` touches an `x_0`-slice of `layerSlices j σ`.
* **Sublemma B:** Every slice in `layerSlices j σ` reaches an `x_0`-slice along `nextSlice`.
* **Sublemma C:** One full `W_{6m}`-lap at `x_0` preserves the `B_j/M_j` mask and shifts the
  `B_j`-sequence rotation by `+2 mod (6m - 1)`; hence `3m` full laps shift by `+1 mod (6m - 1)`,
  reaching any desired rotation of `[0, ..., 6m - 2]`.
* **Sublemma D:** Any two `x_0`-slices with the same `uCyc = (q.take (K - 1)).rotate port` are
  connected by sliding `M_j`-symbols across index `0` via `FStep`.
* **Sublemma E:** Strong induction on `(6m - 1) - trailingTrues` connects every `x_0`-slice to
  the canonical anchor `(canonLoop q_*, .ins 0)` via unit `z`-cycle transfers.

Finally combines all layers `0 ≤ j < r` into `allLayerBags_theorem`.
-/

namespace AsymptoticZero

/-! ### 1. Basic helpers for reachability, `uCyc`, `mask`, and `W6m` rows in Layer `j` -/

/-- Starting vertex of a slice descriptor `(L, tag)`. -/
noncomputable def sliceStartV (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) (s : List (Fin K) × SliceTag) :
    Almanac.Word (K + 2) :=
  let row := (iterW6mLift m hm r hr K hK).row s.1
  (edgeOfRowTag row.1 row.2 s.2).u

/-- Iterating `nextSlice` stays in `layerSlices j σ` and traces an undirected path in `layerBag j σ`! -/
theorem reach_nextSlice_iter (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r) {σ : List (Fin K)}
    {s : List (Fin K) × SliceTag} (hs : s ∈ layerSlices m hm r hr K hK j σ) (t : Nat) :
    (nextSlice m hm r hr K hK)^[t] s ∈ layerSlices m hm r hr K hK j σ ∧
    Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
      (sliceStartV m hm r hr K hK s)
      (sliceStartV m hm r hr K hK ((nextSlice m hm r hr K hK)^[t] s)) := by
  induction t with
  | zero => exact ⟨hs, Relation.ReflTransGen.refl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hst, hreach⟩ := ih
    have hstep := nextSlice_closed_and_edge m hm r hr K hK hst
    refine ⟨hstep.1, hreach.trans (Relation.ReflTransGen.single ?_)⟩
    set st := (nextSlice m hm r hr K hK)^[t] s
    let row := (iterW6mLift m hm r hr K hK).row st.1
    refine ⟨edgeOfRowTag row.1 row.2 st.2, ?_, Or.inl ⟨rfl, hstep.2⟩⟩
    unfold layerBag
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨st, hst, rfl⟩

/-- The length-`(K - 1)` cyclic `Z`-anchored tuple `(q.take (K - 1)).rotate port`. -/
def uCyc {K : Nat} (q : List (Fin K)) (port : Nat) : List (Fin K) :=
  (q.take (K - 1)).rotate port

theorem uCyc_length {K : Nat} {q : List (Fin K)} (hq : q.length = K) (port : Nat) :
    (uCyc q port).length = K - 1 := by
  unfold uCyc; rw [List.length_rotate, List.length_take, hq]; omega

theorem uCyc_nodup {K : Nat} {q : List (Fin K)} (hnd : q.Nodup) (port : Nat) :
    (uCyc q port).Nodup :=
  (List.IsRotated.perm (⟨port, rfl⟩ : q.take (K - 1) ~r uCyc q port)).nodup_iff.mp hnd.take

theorem uCyc_F_zero {K : Nat} {q : List (Fin K)} (hq : q.length = K) :
    uCyc q (K - 1) = uCyc q 0 := by
  unfold uCyc
  have hlen : (q.take (K - 1)).length = K - 1 := by simp [hq]
  have hrot : (q.take (K - 1)).rotate (q.take (K - 1)).length = q.take (K - 1) := List.rotate_length _
  rw [hlen] at hrot
  rw [hrot, List.rotate_zero]

theorem uCyc_F_pos {K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    {port : Nat} (hp : 1 ≤ port) :
    uCyc (FStep q) (port - 1) = uCyc q port := by
  obtain ⟨a, last, mid, hq_eq, hF, hmid_len, _, _⟩ := split_first_last hK hq
  have htake_q : q.take (K - 1) = a :: mid := by
    rw [hq_eq, List.take_append_of_le_length (by simp [hmid_len]; omega),
      List.take_of_length_le (by simp [hmid_len]; omega)]
  have htake_F : (FStep q).take (K - 1) = mid ++ [a] := by
    have h1 : FStep q = (mid ++ [a]) ++ [last] := by rw [hF]; simp [List.append_assoc]
    rw [h1, List.take_append_of_le_length (by simp [hmid_len]; omega),
      List.take_of_length_le (by simp [hmid_len]; omega)]
  unfold uCyc
  rw [htake_F, htake_q]
  have hrot1 : (a :: mid).rotate 1 = mid ++ [a] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  rw [← hrot1, List.rotate_rotate, show 1 + (port - 1) = port by omega]

theorem uCyc_filter_notInBlock {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (hlast : inBlock b j (q[K - 1]'(by omega)) = true) {port : Nat} (hp : port < K) :
    (uCyc q port).filter (notInBlock b j) = tagSigma b j K q (.ins port) := by
  obtain ⟨a, last, mid, hq_eq, _, hmid_len, _, hlast_eq⟩ := split_first_last hK hq
  have hnb_last : notInBlock b j last = false := by
    unfold notInBlock; rw [hlast_eq, hlast]; rfl
  have htake : q.take (K - 1) = a :: mid := by
    rw [hq_eq, List.take_append_of_le_length (by simp [hmid_len]; omega),
      List.take_of_length_le (by simp [hmid_len]; omega)]
  have hlen_am : (a :: mid).length = K - 1 := by simp [hmid_len]; omega
  unfold uCyc; dsimp only [tagSigma]
  rw [htake, hq_eq]
  rw [List.rotate_eq_drop_append_take (by omega : port ≤ (a :: mid).length),
      List.rotate_eq_drop_append_take (by simp [hmid_len]; omega)]
  rw [List.drop_append_of_le_length (by omega : port ≤ (a :: mid).length),
      List.take_append_of_le_length (by omega : port ≤ (a :: mid).length)]
  simp [List.filter_append, List.filter_cons, hnb_last]

/-- Helper: given any permutation `q` with all blocks `i < j` as `'D'` and `projBlock b j q = W6mState m hm k t`
(`t < 6m - 3` and `q[K-1] = emb_j(xB[b-1])`), `canonLoop q` is a Layer-`j` `'F'`-loop with row `(q, .F)`! -/
theorem layerRow_of_W6m_F (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} (hσ : σ ∈ allLayerSigmas m hm r hr K hK j)
    {q : List (Fin K)} (hq : IsPerm K q)
    {k t : Nat} (hk : k < 4 * m) (ht : t < 6 * m - 3)
    (hjb : (j + 1) * (6 * m) ≤ K)
    (hproj : projBlock (6 * m) j q = W6mState m hm k t)
    (hlast : q[K - 1]'(by rw [hq.2]; have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega) =
      embBlock (6 * m) K j hjb ((W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega)))
    (hsig : ∃ port, (q.rotate port).filter (notInBlock (6 * m) j) = σ) :
    activeLayer m hm r (canonLoop q) = some j ∧
    (iterW6mLift m hm r hr K hK).row (canonLoop q) = (q, .F) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  have hbl_j : blockLoop (6 * m) j (canonLoop q) = canonLoop (W6mState m hm k t) := by
    unfold blockLoop
    have hr1 : projBlock (6 * m) j (canonLoop q) ~r projBlock (6 * m) j q :=
      projBlock_isRotated (canonLoop_isRotated q).symm
    rw [hproj] at hr1
    exact (canonLoop_eq_iff (projBlock_isPerm hjb (canonLoop_isCanonLoop hq).1)
      (W6mState_isPerm m hm k t)).mpr hr1
  have hrowB_eq : (selW6m m hm).row (blockLoop (6 * m) j (canonLoop q)) =
      (W6mState m hm k t, .F) := by
    rw [hbl_j, selW6m_row_state m hm hk (by omega : t < 6 * m - 2)]
    simp [show t ≠ 6 * m - 3 by omega]
  have hprev : ∀ i < j, ((selW6m m hm).row (blockLoop (6 * m) i (canonLoop q))).2 = .D := by
    intro i hi
    have hib : (i + 1) * (6 * m) ≤ K := by
      have := Nat.mul_le_mul_right (6 * m) (show i + 1 ≤ r by omega); omega
    obtain ⟨port, hport⟩ := hsig
    have hσ_D := of_decide_eq_true (List.mem_filter.mp hσ).2 ⟨i, hi⟩
    have hproj_i : projBlock (6 * m) i ((q.rotate port).filter (notInBlock (6 * m) j)) =
        projBlock (6 * m) i (q.rotate port) := by
      unfold projBlock
      induction (q.rotate port) with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filter_cons, List.filterMap_cons]
        cases hnb : notInBlock (6 * m) j x with
        | true => simp [List.filterMap_cons, ih]
        | false =>
          have hin : inBlock (6 * m) j x = true := by unfold notInBlock at hnb; simp at hnb; exact hnb
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hin)
          have hxe := (projBlockElem_eq_some_iff (6 * m) j hjb x a).mp ha
          have hnone : projBlockElem (6 * m) i x = none := by
            rw [hxe]; exact projBlockElem_embBlock_ne (by omega) hjb a
          simp [hnone, ih]
    have hbl_i : blockLoop (6 * m) i (canonLoop q) = blockLoop (6 * m) i σ := by
      rw [← hport]
      unfold blockLoop
      rw [hproj_i]
      have hr1 : projBlock (6 * m) i (canonLoop q) ~r projBlock (6 * m) i q :=
        projBlock_isRotated (canonLoop_isRotated q).symm
      have hr2 : projBlock (6 * m) i q ~r projBlock (6 * m) i (q.rotate port) :=
        projBlock_isRotated ⟨port, rfl⟩
      exact (canonLoop_eq_iff (projBlock_isPerm hib (canonLoop_isCanonLoop hq).1)
        (projBlock_isPerm hib (isPerm_rotate hq port))).mpr (hr1.trans hr2)
    rw [hbl_i]; exact hσ_D
  have hact : activeLayer m hm r (canonLoop q) = some j := by
    rw [activeLayer_eq_some_iff]
    refine ⟨hj, ?_, hprev⟩
    rw [hrowB_eq]; simp
  refine ⟨hact, ?_⟩
  change iterW6mRow m hm r K hK (canonLoop q) = (q, .F)
  have hF : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop q))).2 = .F := by rw [hrowB_eq]
  have hlen : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop q))).1.length := by
    rw [hrowB_eq, (W6mState_isPerm m hm k t).2]; omega
  rw [iterW6mRow_eq_F hm hK hact hj hjb hF hlen]
  congr 1
  have hpin := eq_pinAt_of_isRotated (canonLoop_isCanonLoop hq).1 hq
    (canonLoop_isRotated q) (by omega : K - 1 < K) hlast
  have harg : ((selW6m m hm).row (blockLoop (6 * m) j (canonLoop q))).1[6 * m - 1]'hlen =
      (W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega) := by
    simp only [hrowB_eq]
  rw [harg]; exact hpin.symm

/-- Helper: `IsPerm K (w ++ [emb_j(b - 2), emb_j(b - 1)])` for any `w ∈ interleavings σ (bPref b K j hjb)`! -/
theorem isPerm_of_interleaving_append {b j K : Nat} (hb : 4 ≤ b) (hjb : (j + 1) * b ≤ K)
    {σ : List (Fin K)} (hσ : σ ∈ allLinearPermsMj b j K)
    {w : List (Fin K)} (hw : w ∈ interleavings σ (bPref b K j hjb)) :
    IsPerm K (w ++ [embBlock b K j hjb ⟨b - 2, by omega⟩, embBlock b K j hjb ⟨b - 1, by omega⟩]) := by
  obtain ⟨hσ_nd, hσ_len, hσ_nb⟩ := (mem_allLinearPermsMj_iff hjb σ).mp hσ
  obtain ⟨hw_M, hw_B⟩ := (mem_interleavings_iff (notInBlock b j) σ (bPref b K j hjb)
    hσ_nb (bPref_inBlock b K j hjb) w).mp hw
  have hhb_full : ((List.finRange b).map (embBlock b K j hjb)) =
      bPref b K j hjb ++ [embBlock b K j hjb ⟨b - 2, by omega⟩, embBlock b K j hjb ⟨b - 1, by omega⟩] := by
    refine List.ext_getElem (by simp [bPref]; omega) fun i hi1 hi2 => ?_
    rw [List.getElem_map, List.getElem_finRange]
    by_cases h1 : i < b - 2
    · rw [List.getElem_append_left (by simp [bPref]; omega)]
      simp [bPref]
    · rw [List.getElem_append_right (by simp [bPref]; omega)]
      simp only [bPref_length]
      have hhi : i < b := by simp at hi1; exact hi1
      by_cases h2 : i = b - 2
      · subst h2; simp
      · have h3 : i = b - 1 := by omega
        subst h3; simp [show b - 1 - (b - 2) = 1 by omega]
  have hw_perm : w.Perm (σ ++ bPref b K j hjb) := by
    have hsplit : ∀ l : List (Fin K), l.Perm (l.filter (notInBlock b j) ++ l.filter (fun x => !(notInBlock b j x))) := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.filter_cons]
        cases notInBlock b j x with
        | true =>
          simp only [Bool.not_true, List.cons_append]
          exact ih.cons x
        | false =>
          simp only [Bool.not_false]
          exact (ih.cons x).trans List.perm_middle.symm
    have hsp := hsplit w
    rwa [hw_M, hw_B] at hsp
  have hfull_perm : (w ++ [embBlock b K j hjb ⟨b - 2, by omega⟩, embBlock b K j hjb ⟨b - 1, by omega⟩]).Perm
      (σ ++ (List.finRange b).map (embBlock b K j hjb)) := by
    rw [hhb_full, ← List.append_assoc]
    exact hw_perm.append_right _
  -- `σ ++ (List.finRange b).map emb_j` is a permutation of `List.finRange K`!
  have hσ_perm : σ.Perm (elemsMj b j K) := List.mem_permutations.mp hσ
  have hbase_nd : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).Nodup := by
    refine List.nodup_append.mpr ⟨elemsMj_nodup b j K, ?_, ?_⟩
    · refine (List.nodup_finRange b).map fun a1 a2 h => ?_
      have hv := congrArg Fin.val h; dsimp [embBlock] at hv; apply Fin.ext; omega
    · intro x hx y hy heq; subst heq
      have hnb := (List.mem_filter.mp hx).2
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
      unfold notInBlock at hnb; rw [inBlock_embBlock] at hnb; simp at hnb
  have hbase_len : (elemsMj b j K ++ (List.finRange b).map (embBlock b K j hjb)).length = K := by
    rw [List.length_append, elemsMj_length hjb, List.length_map, List.length_finRange]
    have : b ≤ (j + 1) * b := by
      have := Nat.mul_le_mul_right b (show 1 ≤ j + 1 by omega); rwa [Nat.one_mul] at this
    omega
  have hp_fin := hfull_perm.trans (hσ_perm.append_right _)
  exact ⟨hp_fin.nodup_iff.mpr hbase_nd, hp_fin.length_eq.trans hbase_len⟩

theorem projBlock_of_interleaving_append {b j K : Nat} (hb : 4 ≤ b) (hjb : (j + 1) * b ≤ K)
    {σ : List (Fin K)} (hσ : σ ∈ allLinearPermsMj b j K)
    {w : List (Fin K)} (hw : w ∈ interleavings σ (bPref b K j hjb)) :
    projBlock b j (w ++ [embBlock b K j hjb ⟨b - 2, by omega⟩, embBlock b K j hjb ⟨b - 1, by omega⟩]) =
      List.finRange b := by
  obtain ⟨_, _, hσ_nb⟩ := (mem_allLinearPermsMj_iff hjb σ).mp hσ
  obtain ⟨_, hw_B⟩ := (mem_interleavings_iff (notInBlock b j) σ (bPref b K j hjb)
    hσ_nb (bPref_inBlock b K j hjb) w).mp hw
  have hin_eq : (fun x : Fin K => !(notInBlock b j x)) = inBlock b j := by
    funext x; unfold notInBlock; simp
  rw [hin_eq, filter_inBlock_eq_map_projBlock hjb] at hw_B
  have hproj_w : projBlock b j w = (List.finRange (b - 2)).map (fun i => ⟨i.1, by omega⟩) := by
    have hinj : Function.Injective (embBlock b K j hjb) := fun a1 a2 h => by
      have hv := congrArg Fin.val h; dsimp [embBlock] at hv; apply Fin.ext; omega
    apply List.map_injective_iff.mpr hinj
    rw [hw_B, bPref, List.map_map]; rfl
  unfold projBlock at hproj_w ⊢
  rw [List.filterMap_append, hproj_w, List.filterMap_cons, List.filterMap_cons, List.filterMap_nil,
    projBlockElem_embBlock, projBlockElem_embBlock]
  refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
  rw [List.getElem_finRange]
  by_cases h1 : i < b - 2
  · rw [List.getElem_append_left (by simp; omega)]; simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_map, List.length_finRange]
    have hhi : i < b := by simp at hi2; exact hi2
    by_cases h2 : i = b - 2
    · subst h2; simp
    · have h3 : i = b - 1 := by omega
      subst h3; simp [show b - 1 - (b - 2) = 1 by omega]

/-- Note: `W6mState m hm 0 0 = List.finRange (6 * m)`! -/
theorem W6mState_zero_zero (m : Nat) (hm : 1 ≤ m) :
    W6mState m hm 0 0 = List.finRange (6 * m) := by
  unfold W6mState permList
  simp only [pow_zero, one_mul, Equiv.Perm.coe_one, id_eq]
  rw [List.map_id]

/-! ### 2. Sublemma A: Every `ck ∈ zCyclesOf j σ` hits an `x_0`-slice of `layerSlices j σ` -/

theorem zCycle_hits_x0 (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} (hσ : σ ∈ allLayerSigmas m hm r hr K hK j)
    (hjb : (j + 1) * (6 * m) ≤ K) {w : List (Fin K)}
    (hw : w ∈ interleavings σ (bPref (6 * m) K j hjb)) :
    let q := w ++ [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩,
                   embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩]
    (canonLoop q, SliceTag.ins 0) ∈ layerSlices m hm r hr K hK j σ ∧
    sliceStartV m hm r hr K hK (canonLoop q, SliceTag.ins 0) = symZ K :: w.map embK ∧
    ((iterW6mLift m hm r hr K hK).row (canonLoop q)) = (q, .F) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  have hσ_Mj := (List.mem_filter.mp hσ).1
  obtain ⟨_, hσ_len, hσ_nb⟩ := (mem_allLinearPermsMj_iff hjb σ).mp hσ_Mj
  set q := w ++ [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩,
                 embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩]
  have hq_perm : IsPerm K q := isPerm_of_interleaving_append (by omega) hjb hσ_Mj hw
  have hproj : projBlock (6 * m) j q = W6mState m hm 0 0 := by
    rw [W6mState_zero_zero m hm]
    exact projBlock_of_interleaving_append (by omega) hjb hσ_Mj hw
  have hw_len : w.length = K - 2 := by
    rw [interleavings_sub_length _ _ hw, hσ_len, bPref_length]
    have : 6 * m ≤ K := by omega
    omega
  have hq_last : q[K - 1]'(by rw [hq_perm.2]; omega) =
      embBlock (6 * m) K j hjb ((W6mState m hm 0 0)[6 * m - 1]'(by rw [(W6mState_isPerm m hm 0 0).2]; omega)) := by
    have h1 : q[K - 1]'(by rw [hq_perm.2]; omega) = embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩ := by
      dsimp only [q]
      rw [List.getElem_append_right (by omega)]
      simp [hw_len, show K - 1 - (K - 2) = 1 by omega]
    have h2 : (W6mState m hm 0 0)[6 * m - 1]'(by rw [(W6mState_isPerm m hm 0 0).2]; omega) =
        ⟨6 * m - 1, by omega⟩ := by
      simp only [W6mState_zero_zero, List.getElem_finRange, Fin.cast_mk]
    rw [h1, h2]
  have hq_sig : (q.rotate 0).filter (notInBlock (6 * m) j) = σ := by
    rw [List.rotate_zero]
    dsimp only [q]
    rw [List.filter_append]
    have h1 := ((mem_interleavings_iff (notInBlock (6 * m) j) σ (bPref (6 * m) K j hjb)
      hσ_nb (bPref_inBlock (6 * m) K j hjb) w).mp hw).1
    have hnb1 : notInBlock (6 * m) j (embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩) = false := by
      unfold notInBlock; rw [inBlock_embBlock]; rfl
    have hnb2 : notInBlock (6 * m) j (embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩) = false := by
      unfold notInBlock; rw [inBlock_embBlock]; rfl
    simp [h1, hnb1, hnb2]
  obtain ⟨hact, hrow⟩ := layerRow_of_W6m_F m hm r hr K hK hj hσ hq_perm
    (by omega : 0 < 4 * m) (by omega : 0 < 6 * m - 3) hjb hproj hq_last ⟨0, hq_sig⟩
  refine ⟨(mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨canonLoop_isCanonLoop hq_perm, hact, ?_, ?_⟩, ?_, hrow⟩
  · rw [hrow]; exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
  · rw [hrow]; exact hq_sig
  · unfold sliceStartV edgeOfRowTag
    rw [hrow]; dsimp only
    rw [insSlice_u hK4 hq_perm.2 (by omega) 0]
    unfold insBase
    simp only [List.take_zero, List.drop_zero, List.map_nil, List.nil_append, List.singleton_append]
    have htake : (symZ K :: q.map embK).take (K - 1) = symZ K :: (q.map embK).take (K - 2) := by
      cases hk1 : K - 1 with
      | zero => omega
      | succ d =>
        have : d = K - 2 := by omega
        subst this; rfl
    rw [htake, ← List.map_take]
    congr 2
    dsimp only [q]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-! ### 3. Sublemma B & C: `F`-block advancement, `'S'`-run `uCyc` law, and full-lap rotation -/

/-- Exact `B_j`-projection characterization of a Layer-`j` row `(q, rt)`:
it is rotated to some unique `W6mState m hm k t`, and if `rt = .F` then `projBlock b j q = W6mState m hm k t`! -/
theorem layerRow_W6mState_info (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} {L : List (Fin K)}
    (hL : IsCanonLoop K L) (hact : activeLayer m hm r L = some j) :
    let row := (iterW6mLift m hm r hr K hK).row L
    ∃ k < 4 * m, ∃ t < 6 * m - 2,
      projBlock (6 * m) j row.1 ~r W6mState m hm k t ∧
      (t < 6 * m - 3 → row.2 = .F ∧ projBlock (6 * m) j row.1 = W6mState m hm k t) ∧
      (t = 6 * m - 3 → row.2 = .S) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  have hbl := canonLoop_isCanonLoop (projBlock_isPerm hjb hL.1)
  have hrowB_perm := (selW6m m hm).row_perm (blockLoop (6 * m) j L) hbl
  have hfind : ∃ k < 4 * m, ∃ t < 6 * m - 2,
      (selW6m m hm).row (blockLoop (6 * m) j L) =
        (W6mState m hm k t, if t = 6 * m - 3 then .S else .F) := by
    dsimp only [selW6m] at hj_neD ⊢
    cases hf : (W6mRows m hm).find? (fun p => decide (canonLoop p.1 = blockLoop (6 * m) j L)) with
    | none => simp [hf] at hj_neD
    | some p =>
      obtain ⟨k, hk, t, ht, hp1, hp2⟩ := (mem_W6mRows_iff m hm p.1 p.2).mp (List.mem_of_find?_eq_some hf)
      exact ⟨k, hk, t, ht, Prod.ext hp1 hp2⟩
  obtain ⟨k, hk, t, ht, hrowB_eq⟩ := hfind
  have hq := (iterW6mLift m hm r hr K hK).row_perm L hL
  have hproj_rot : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 ~r W6mState m hm k t := by
    have h1 : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 ~r projBlock (6 * m) j L :=
      projBlock_isRotated hq.2
    have h2 : projBlock (6 * m) j L ~r blockLoop (6 * m) j L := canonLoop_isRotated _
    have h3 : blockLoop (6 * m) j L ~r W6mState m hm k t := by
      have := hrowB_perm.2.symm; rwa [hrowB_eq] at this
    exact h1.trans (h2.trans h3)
  refine ⟨k, hk, t, ht, hproj_rot, ?_, ?_⟩
  · intro ht_lt
    have hF : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .F := by
      rw [hrowB_eq]; simp [show t ≠ 6 * m - 3 by omega]
    have hlenB : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
      rw [hrowB_eq, (W6mState_isPerm m hm k t).2]; omega
    have hrow_eq : (iterW6mLift m hm r hr K hK).row L =
        (pinAt L (embBlock (6 * m) K j hjb (((selW6m m hm).row (blockLoop (6 * m) j L)).1[6 * m - 1]'hlenB)) (K - 1), .F) := by
      change iterW6mRow m hm r K hK L = _
      exact iterW6mRow_eq_F hm hK hact hj_lt hjb hF hlenB
    refine ⟨by rw [hrow_eq], ?_⟩
    set q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq_last : q[K - 1]'(by rw [hq.1.2]; omega) =
        embBlock (6 * m) K j hjb ((W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega)) := by
      have h1 : q = pinAt L (embBlock (6 * m) K j hjb ((W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega))) (K - 1) := by
        dsimp only [q]; rw [hrow_eq]; simp only [hrowB_eq]
      simpa [h1] using pinAt_getElem hL.1 (embBlock (6 * m) K j hjb ((W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega))) (by omega : K - 1 < K)
    obtain ⟨a, last, mid, hsp, _, _, _, hlsp⟩ := split_first_last hK4 hq.1.2
    have hls : projBlockElem (6 * m) j last =
        some ((W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega)) := by
      rw [hlsp, hq_last]; exact projBlockElem_embBlock _ _ _ _ _
    have hdec : projBlock (6 * m) j q = (a :: mid).filterMap (projBlockElem (6 * m) j) ++
        [(W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega)] := by
      have hsp' : q = a :: mid ++ [last] := hsp
      unfold projBlock; rw [hsp', List.filterMap_append]; simp [List.filterMap_cons, hls]
    have hpr_perm := projBlock_isPerm hjb hq.1
    have hlp : ((a :: mid).filterMap (projBlockElem (6 * m) j)).length = 6 * m - 1 := by
      have := hpr_perm.2; rw [hdec] at this; simp at this; omega
    have hlast_pr : (projBlock (6 * m) j q)[6 * m - 1]'(by rw [hpr_perm.2]; omega) =
        (W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega) := by
      have ht' : ((a :: mid).filterMap (projBlockElem (6 * m) j) ++
          [(W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega)])[6 * m - 1]'(by simp [hlp]) =
          (W6mState m hm k t)[6 * m - 1]'(by rw [(W6mState_isPerm m hm k t).2]; omega) := by
        rw [List.getElem_append_right (by omega)]; simp [hlp]
      simpa [hdec] using ht'
    exact (eq_pinAt_of_isRotated (W6mState_isPerm m hm k t) hpr_perm hproj_rot (by omega) hlast_pr).trans
      (eq_pinAt_of_isRotated (W6mState_isPerm m hm k t) (W6mState_isPerm m hm k t) (List.IsRotated.refl _) (by omega) rfl).symm
  · intro ht_eq
    have hS : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .S := by rw [hrowB_eq, ht_eq]; simp
    have hlenB : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
      rw [hrowB_eq, (W6mState_isPerm m hm k t).2]; omega
    change (iterW6mRow m hm r K hK L).2 = .S
    rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hS hlenB]

/-- Helper: count of leading non-`B_j` elements of a list `l`. -/
def leadingMj (b j : Nat) {K : Nat} (l : List (Fin K)) : Nat :=
  (l.takeWhile (notInBlock b j)).length

theorem leadingMj_FStep_of_none {b j K : Nat} (hK : 4 ≤ K) {q : List (Fin K)} (hq : q.length = K)
    (h0 : notInBlock b j (q[0]'(by omega)) = true)
    (hhas : ∃ x ∈ q.take (K - 1), inBlock b j x = true) :
    leadingMj b j ((FStep q).take (K - 1)) + 1 = leadingMj b j (q.take (K - 1)) := by
  obtain ⟨a, last, mid, hq_eq, hF, hmid_len, ha_eq, _⟩ := split_first_last hK hq
  have ha_nb : notInBlock b j a = true := ha_eq ▸ h0
  have htake_q : q.take (K - 1) = a :: mid := by
    rw [hq_eq, List.take_append_of_le_length (by simp [hmid_len]; omega),
      List.take_of_length_le (by simp [hmid_len]; omega)]
  have htake_F : (FStep q).take (K - 1) = mid ++ [a] := by
    have h1 : FStep q = (mid ++ [a]) ++ [last] := by rw [hF]; simp [List.append_assoc]
    rw [h1, List.take_append_of_le_length (by simp [hmid_len]; omega),
      List.take_of_length_le (by simp [hmid_len]; omega)]
  have hmid_has : ∃ x ∈ mid, notInBlock b j x = false := by
    obtain ⟨x, hx, hxin⟩ := hhas
    rw [htake_q, List.mem_cons] at hx
    rcases hx with rfl | hxm
    · unfold notInBlock at ha_nb; rw [hxin] at ha_nb; simp at ha_nb
    · exact ⟨x, hxm, by unfold notInBlock; rw [hxin]; rfl⟩
  have htw_app : (mid ++ [a]).takeWhile (notInBlock b j) = mid.takeWhile (notInBlock b j) := by
    have hgen : ∀ l : List (Fin K), (∃ x ∈ l, notInBlock b j x = false) →
        (l ++ [a]).takeWhile (notInBlock b j) = l.takeWhile (notInBlock b j) := by
      intro l
      induction l with
      | nil => intro h; obtain ⟨x, hx, _⟩ := h; cases hx
      | cons y ys ih =>
        intro h
        simp only [List.cons_append, List.takeWhile_cons]
        cases hy : notInBlock b j y with
        | false => rfl
        | true =>
          simp only [hy, ↓reduceIte, List.cons.injEq, true_and]
          apply ih
          obtain ⟨x, hx, hxf⟩ := h
          rcases List.mem_cons.mp hx with rfl | hx'
          · rw [hy] at hxf; cases hxf
          · exact ⟨x, hx', hxf⟩
    exact hgen mid hmid_has
  unfold leadingMj
  rw [htake_F, htake_q, htw_app, List.takeWhile_cons, ha_nb]
  simp

/-- **Sublemma B1 (`advance_F_step`):** From any `'F'`-slice `(L, .ins port)` at `(k, t)` (`t < 6m - 3`),
iterating `nextSlice` advances to `(k, t + 1)` while preserving `uCyc` identically!
Furthermore, when `t + 1 = 6m - 3`, the landing `'S'`-row `q'` ALSO has `projBlock b j q' = W6mState m hm k (6m - 3)`! -/
theorem advance_F_step (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {k t : Nat} (hk : k < 4 * m) (ht : t < 6 * m - 3) :
    ∀ (d : Nat) (L : List (Fin K)) (port : Nat),
      (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm k t →
      leadingMj (6 * m) j (((iterW6mLift m hm r hr K hK).row L).1.take (K - 1)) = d →
      ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
        port' < K - 1 ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm k (t + 1) ∧
        uCyc ((iterW6mLift m hm r hr K hK).row L').1 port' =
          uCyc ((iterW6mLift m hm r hr K hK).row L).1 port ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  intro d
  induction d with
  | zero =>
    intro L port hs hF hproj hd
    obtain ⟨hL, hact, htag, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
    have hport : port < K := by
      rw [hF] at htag; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
      obtain ⟨p, hp, hpe⟩ := htag; cases hpe; exact hp
    set q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    -- Ensure positive port (`p1 ≥ 1`) by stepping `0 → K - 1` if `port = 0`!
    have hpos_step : ∃ p1, 1 ≤ p1 ∧ p1 < K ∧
        (L, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ ∧
        uCyc q p1 = uCyc q port ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins p1)) := by
      by_cases hp0 : port = 0
      · subst hp0
        have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs 1
        have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins 0) = (L, .ins (K - 1)) := by
          simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]; simp
        rw [h1] at hr1
        exact ⟨K - 1, by omega, by omega, hr1.1, uCyc_F_zero hq.2, hr1.2⟩
      · exact ⟨port, by omega, hport, hs, rfl, Relation.ReflTransGen.refl⟩
    obtain ⟨p1, hp1_ge, hp1_lt, hs1, hu1, hreach1⟩ := hpos_step
    -- Since `leadingMj = 0`, `q[0] ∈ B_j`!
    have hq0_in : inBlock (6 * m) j (q[0]'(by rw [hq.2]; omega)) = true := by
      have htake_pos : 0 < (q.take (K - 1)).length := by simp [hq.2]; omega
      cases hqt : q.take (K - 1) with
      | nil => rw [hqt] at htake_pos; simp at htake_pos
      | cons a rest =>
        have ha_eq : a = q[0]'(by rw [hq.2]; omega) := by
          have := congrArg (fun l => l[0]?) hqt
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by rw [hq.2]; omega),
            List.getElem?_cons_zero] at this
          exact (Option.some.inj this).symm
        unfold leadingMj at hd; rw [hqt, List.takeWhile_cons] at hd
        cases hnb : notInBlock (6 * m) j a with
        | true => simp [hnb] at hd
        | false =>
          unfold notInBlock at hnb; simp at hnb; rw [← ha_eq]; exact hnb
    have hq_last_in : inBlock (6 * m) j (q[K - 1]'(by rw [hq.2]; omega)) = true :=
      (layer_F_step_info m hm r hr K hK hL hact hF).1
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hq0_in)
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hq_last_in)
    -- Step 1 time via `nextSlice`: `(L, .ins p1) ↦ (canonLoop (FStep q), .ins (p1 - 1))`!
    have hr2 := reach_nextSlice_iter m hm r hr K hK hj hs1 1
    have h2 : (nextSlice m hm r hr K hK)^[1] (L, .ins p1) = (canonLoop (FStep q), .ins (p1 - 1)) := by
      simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]
      simp [show p1 ≠ 0 by omega]; rfl
    rw [h2] at hr2
    have hcl := ((iterW6mLift m hm r hr K hK).closed_F L hL hF).1
    refine ⟨canonLoop (FStep q), p1 - 1, hr2.1, by omega, ?_, ?_, hreach1.trans hr2.2⟩
    · rw [hcl, projBlock_FStep_of_both_some hK4 hq.2 ha' hl', hproj, FStep_W6mState]
    · rw [hcl, uCyc_F_pos hK4 hq.2 hp1_ge, hu1]
  | succ d ih =>
    intro L port hs hF hproj hd
    obtain ⟨hL, hact, htag, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
    have hport : port < K := by
      rw [hF] at htag; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
      obtain ⟨p, hp, hpe⟩ := htag; cases hpe; exact hp
    set q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    have hpos_step : ∃ p1, 1 ≤ p1 ∧ p1 < K ∧
        (L, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ ∧
        uCyc q p1 = uCyc q port ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins p1)) := by
      by_cases hp0 : port = 0
      · subst hp0
        have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs 1
        have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins 0) = (L, .ins (K - 1)) := by
          simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]; simp
        rw [h1] at hr1
        exact ⟨K - 1, by omega, by omega, hr1.1, uCyc_F_zero hq.2, hr1.2⟩
      · exact ⟨port, by omega, hport, hs, rfl, Relation.ReflTransGen.refl⟩
    obtain ⟨p1, hp1_ge, hp1_lt, hs1, hu1, hreach1⟩ := hpos_step
    -- Since `leadingMj = d + 1 > 0`, `q[0] ∉ B_j`!
    have hq0_nb : notInBlock (6 * m) j (q[0]'(by rw [hq.2]; omega)) = true := by
      have htake_pos : 0 < (q.take (K - 1)).length := by simp [hq.2]; omega
      cases hqt : q.take (K - 1) with
      | nil => rw [hqt] at htake_pos; simp at htake_pos
      | cons a rest =>
        have ha_eq : a = q[0]'(by rw [hq.2]; omega) := by
          have := congrArg (fun l => l[0]?) hqt
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by rw [hq.2]; omega),
            List.getElem?_cons_zero] at this
          exact (Option.some.inj this).symm
        unfold leadingMj at hd; rw [hqt, List.takeWhile_cons] at hd
        cases hnb : notInBlock (6 * m) j a with
        | false => simp [hnb] at hd
        | true => rw [← ha_eq]; exact hnb
    have hq0_none : projBlockElem (6 * m) j (q[0]'(by rw [hq.2]; omega)) = none :=
      (notInBlock_iff_projBlockElem_eq_none _ _ _).mp hq0_nb
    have hhas : ∃ x ∈ q.take (K - 1), inBlock (6 * m) j x = true := by
      have hcnt : (q.filter (inBlock (6 * m) j)).length = 6 * m := by
        rw [filter_inBlock_eq_map_projBlock hjb, List.length_map, hproj, (W6mState_isPerm m hm k t).2]
      have hsplit : q = q.take (K - 1) ++ q.drop (K - 1) := (List.take_append_drop (K - 1) q).symm
      have hdl : (q.drop (K - 1)).length = 1 := by simp [hq.2]; omega
      have h1 : ((q.take (K - 1)).filter (inBlock (6 * m) j)).length +
          ((q.drop (K - 1)).filter (inBlock (6 * m) j)).length = 6 * m := by
        rw [← List.length_append, ← List.filter_append, ← hsplit]; exact hcnt
      have h2 : ((q.drop (K - 1)).filter (inBlock (6 * m) j)).length ≤ 1 :=
        (List.length_filter_le _ _).trans (by omega)
      have hpos : 0 < ((q.take (K - 1)).filter (inBlock (6 * m) j)).length := by omega
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hpos)
      exact ⟨x, (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩
    have hr2 := reach_nextSlice_iter m hm r hr K hK hj hs1 1
    have h2 : (nextSlice m hm r hr K hK)^[1] (L, .ins p1) = (canonLoop (FStep q), .ins (p1 - 1)) := by
      simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]
      simp [show p1 ≠ 0 by omega]; rfl
    rw [h2] at hr2
    have hcl := ((iterW6mLift m hm r hr K hK).closed_F L hL hF).1
    have hproj' : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).1 =
        W6mState m hm k t := by
      rw [hcl, projBlock_FStep_of_head_none hK4 hq.2 hq0_none, hproj]
    have hF' : ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).2 = .F := by
      have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hr2.1).2.1
      have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hr2.1).1
      obtain ⟨k', hk', t', ht', hrot', hF_of, _⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
      rw [hproj'] at hrot'
      have ⟨_, hteq⟩ := W6m_loop_disjoint m hm hk hk' (by omega) ht' hrot'
      exact (hF_of (by omega)).1
    have hd' : leadingMj (6 * m) j (((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).1.take (K - 1)) = d := by
      rw [hcl]
      change leadingMj (6 * m) j ((FStep q).take (K - 1)) = d
      have hstep := leadingMj_FStep_of_none hK4 hq.2 hq0_nb hhas
      have hdq : leadingMj (6 * m) j (q.take (K - 1)) = d + 1 := hd
      omega
    obtain ⟨L', port', hs', hplt', hproj_fin, hu_fin, hreach_fin⟩ :=
      ih (canonLoop (FStep q)) (p1 - 1) hr2.1 hF' hproj' hd'
    refine ⟨L', port', hs', hplt', hproj_fin, ?_, (hreach1.trans hr2.2).trans hreach_fin⟩
    rw [hu_fin, hcl, uCyc_F_pos hK4 hq.2 hp1_ge, hu1]

/-- Iterating `advance_F_step` from `(k, t)` (`t ≤ 6m - 3`) reaches the `'S'`-row `(k, 6m - 3)`
with `projBlock b j q' = W6mState m hm k (6m - 3)` and IDENTICAL `uCyc`! -/
theorem advance_F_to_S (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {k : Nat} (hk : k < 4 * m) :
    ∀ (rem : Nat), 1 ≤ rem → ∀ (t : Nat), t + rem = 6 * m - 3 →
      ∀ (L : List (Fin K)) (port : Nat),
      (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm k t →
      (t < 6 * m - 3 → ((iterW6mLift m hm r hr K hK).row L).2 = .F) →
      ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
        port' < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L').2 = .S ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm k (6 * m - 3) ∧
        uCyc ((iterW6mLift m hm r hr K hK).row L').1 port' =
          uCyc ((iterW6mLift m hm r hr K hK).row L).1 port ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  intro rem
  induction rem with
  | zero => intro h1; omega
  | succ rem' ih =>
    intro _ t ht L port hs hproj hF_of
    have ht_lt : t < 6 * m - 3 := by omega
    have hF := hF_of ht_lt
    obtain ⟨L1, port1, hs1, hplt1, hproj1, hu1, hreach1⟩ :=
      advance_F_step m hm r hr K hK hj hk ht_lt _ L port hs hF hproj rfl
    by_cases hdone : rem' = 0
    · subst hdone
      have ht1 : t + 1 = 6 * m - 3 := by omega
      rw [ht1] at hproj1
      obtain ⟨hL1, hact1, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1
      obtain ⟨k', hk', t', ht', hrot', _, hS_of⟩ := layerRow_W6mState_info m hm r hr K hK hL1 hact1
      rw [hproj1] at hrot'
      have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm hk hk' (by omega) ht' hrot'
      exact ⟨L1, port1, hs1, hplt1, hS_of ht'_eq.symm, hproj1, hu1, hreach1⟩
    · have hF1 : ((iterW6mLift m hm r hr K hK).row L1).2 = .F := by
        obtain ⟨hL1, hact1, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1
        obtain ⟨k', hk', t', ht', hrot', hF_of1, _⟩ := layerRow_W6mState_info m hm r hr K hK hL1 hact1
        rw [hproj1] at hrot'
        have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm hk hk' (by omega) ht' hrot'
        exact (hF_of1 (by omega)).1
      obtain ⟨L2, port2, hs2, hplt2, hS2, hproj2, hu2, hreach2⟩ :=
        ih (by omega) (t + 1) (by omega) L1 port1 hs1 hproj1 (fun _ => hF1)
      exact ⟨L2, port2, hs2, hplt2, hS2, hproj2, hu2.trans hu1, hreach1.trans hreach2⟩

/-- Helper: one `SStep` on an `'S'`-slice `(L, .ins port)` with `port < K - 1` advances via
`1` or `4` steps of `nextSlice` to `(canonLoop (SStep q), .ins ((port + 1) % (K - 1)))`! -/
theorem S_single_step_mod (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {L : List (Fin K)} {port : Nat}
    (hs : (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ)
    (hS : ((iterW6mLift m hm r hr K hK).row L).2 = .S) (hplt : port < K - 1) :
    let q := ((iterW6mLift m hm r hr K hK).row L).1
    (canonLoop (SStep q), SliceTag.ins ((port + 1) % (K - 1))) ∈ layerSlices m hm r hr K hK j σ ∧
    Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
      (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
      (sliceStartV m hm r hr K hK (canonLoop (SStep q), SliceTag.ins ((port + 1) % (K - 1)))) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  by_cases hlt : port ≤ K - 3
  · have hmod : (port + 1) % (K - 1) = port + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs 1
    have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins port) =
        (canonLoop (SStep ((iterW6mLift m hm r hr K hK).row L).1), .ins (port + 1)) := by
      simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hS]; simp [hlt]
    rwa [h1] at hr1
  · have hkm2 : port = K - 2 := by omega
    subst hkm2
    have hmod : (K - 2 + 1) % (K - 1) = 0 := by
      rw [show K - 2 + 1 = K - 1 by omega, Nat.mod_self]
    rw [hmod]
    have hr4 := reach_nextSlice_iter m hm r hr K hK hj hs 4
    have hstep1 : nextSlice m hm r hr K hK (L, .ins (K - 2)) = (L, .repKm2) := by
      unfold nextSlice; dsimp only; rw [hS]; simp [hlt]
    have hstep2 : nextSlice m hm r hr K hK (L, .repKm2) = (L, .repKm1) := by
      unfold nextSlice; dsimp only; rw [hS]
    have hstep3 : nextSlice m hm r hr K hK (L, .repKm1) = (L, .ins (K - 1)) := by
      unfold nextSlice; dsimp only; rw [hS]
    have hstep4 : nextSlice m hm r hr K hK (L, .ins (K - 1)) =
        (canonLoop (SStep ((iterW6mLift m hm r hr K hK).row L).1), .ins 0) := by
      unfold nextSlice; dsimp only; rw [hS]
      simp [show ¬(K - 1 ≤ K - 3) by omega, show K - 1 ≠ K - 2 by omega]
    have h4 : (nextSlice m hm r hr K hK)^[4] (L, .ins (K - 2)) =
        (canonLoop (SStep ((iterW6mLift m hm r hr K hK).row L).1), .ins 0) := by
      change nextSlice m hm r hr K hK (nextSlice m hm r hr K hK (nextSlice m hm r hr K hK (nextSlice m hm r hr K hK (L, .ins (K - 2))))) = _
      rw [hstep1, hstep2, hstep3, hstep4]
    rwa [h4] at hr4

/-- **Sublemma B2a (`advance_S_to_F_any`):** From ANY `'S'`-slice `(L, .ins port)` (`port < K - 1`)
at block `k < 4m`, iterating `S_single_step_mod` reaches an `'F'`-slice at `((k + 1) % (4 * m), 0)`! -/
theorem advance_S_to_F_any (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {k : Nat} (hk : k < 4 * m) :
    ∀ (d : Nat) (L : List (Fin K)) (port : Nat),
      (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .S →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 ~r W6mState m hm k (6 * m - 3) →
      port < K - 1 →
      ((((iterW6mLift m hm r hr K hK).row L).1.take (K - 2)).reverse.takeWhile (notInBlock (6 * m) j)).length = d →
      ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
        port' < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 =
          W6mState m hm ((k + 1) % (4 * m)) 0 ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  intro d
  induction d with
  | zero =>
    intro L port hs hS hrot hplt hd
    obtain ⟨hL, hact, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
    set q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    -- `d = 0` means `q[K - 3] ∈ B_j`!
    obtain ⟨pre, u, v, w, hq_sp, hS_sp, hpre_len, hu_eq, hv_eq, _⟩ := split_last3 hK4 hq.2
    have htake : q.take (K - 2) = pre ++ [u] := by
      have h1 : q = (pre ++ [u]) ++ [v, w] := by rw [hq_sp]; simp [List.append_assoc]
      rw [h1, List.take_append_of_le_length (by simp [hpre_len]; omega),
        List.take_of_length_le (by simp [hpre_len]; omega)]
    have hu_in : inBlock (6 * m) j u = true := by
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.takeWhile_cons] at hd
      cases hnb : notInBlock (6 * m) j u with
      | true => simp [hnb] at hd
      | false => unfold notInBlock at hnb; simp at hnb; exact hnb
    have hq3_some : (projBlockElem (6 * m) j (q[K - 3]'(by rw [hq.2]; omega))).isSome = true := by
      rw [← inBlock_iff_projBlockElem_isSome, ← hu_eq]; exact hu_in
    obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hq3_some
    have hkm2_in := (layer_S_step_info m hm r hr K hK hL hact hS).1
    have hq_km2 : projBlockElem (6 * m) j (q[K - 2]'(by rw [hq.2]; omega)) =
        some ((W6mState m hm k (6 * m - 3))[6 * m - 2]'(by rw [(W6mState_isPerm m hm k _).2]; omega)) := by
      obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
      have hbl_eq : blockLoop (6 * m) j L = canonLoop (W6mState m hm k (6 * m - 3)) := by
        have hr1 : projBlock (6 * m) j L ~r projBlock (6 * m) j q :=
          projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2.symm
        exact (canonLoop_eq_iff (projBlock_isPerm hjb hL.1) (W6mState_isPerm m hm k _)).mpr
          (hr1.trans hrot)
      have hrowB_eq : (selW6m m hm).row (blockLoop (6 * m) j L) = (W6mState m hm k (6 * m - 3), .S) := by
        rw [hbl_eq, selW6m_row_state m hm hk (by omega)]; simp
      have hS_B : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .S := by rw [hrowB_eq]
      have hlenB : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
        rw [hrowB_eq, (W6mState_isPerm m hm k _).2]; omega
      have hq_pin : q = pinAt L (embBlock (6 * m) K j hjb
          ((W6mState m hm k (6 * m - 3))[6 * m - 2]'(by rw [(W6mState_isPerm m hm k _).2]; omega))) (K - 2) := by
        have h1 : (iterW6mLift m hm r hr K hK).row L = _ := iterW6mRow_eq_S hm hK hact hj_lt hjb hS_B hlenB
        dsimp only [q]; rw [h1]; simp only [hrowB_eq]
      have hget : q[K - 2]'(by rw [hq.2]; omega) = embBlock (6 * m) K j hjb
          ((W6mState m hm k (6 * m - 3))[6 * m - 2]'(by rw [(W6mState_isPerm m hm k _).2]; omega)) := by
        simpa [hq_pin] using pinAt_getElem hL.1 (embBlock (6 * m) K j hjb
          ((W6mState m hm k (6 * m - 3))[6 * m - 2]'(by rw [(W6mState_isPerm m hm k _).2]; omega))) (by omega : K - 2 < K)
      rw [hget]; exact projBlockElem_embBlock _ _ _ _ _
    have hproj_S := (projBlock_SStep_of_both_some (by omega) hK4 hjb hq
      (W6mState_isPerm m hm k (6 * m - 3)) hrot hq_km2 hu').2
    rw [SStep_W6mState] at hproj_S
    have hstep := S_single_step_mod m hm r hr K hK hj hs hS hplt
    have hcl := ((iterW6mLift m hm r hr K hK).closed_S L hL hS).1
    have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).2.1
    have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).1
    obtain ⟨k', hk', t', ht', hrot', hF_of, _⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
    rw [hcl, hproj_S] at hrot'
    have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm (Nat.mod_lt (k + 1) (by omega)) hk' (by omega) ht' hrot'
    exact ⟨canonLoop (SStep q), (port + 1) % (K - 1), hstep.1, Nat.mod_lt _ (by omega),
      (hF_of (by omega)).1, by rw [hcl, hproj_S], hstep.2⟩
  | succ d ih =>
    intro L port hs hS hrot hplt hd
    obtain ⟨hL, hact, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
    set q := ((iterW6mLift m hm r hr K hK).row L).1
    have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
    obtain ⟨pre, u, v, w, hq_sp, hS_sp, hpre_len, hu_eq, hv_eq, _⟩ := split_last3 hK4 hq.2
    have htake : q.take (K - 2) = pre ++ [u] := by
      have h1 : q = (pre ++ [u]) ++ [v, w] := by rw [hq_sp]; simp [List.append_assoc]
      rw [h1, List.take_append_of_le_length (by simp [hpre_len]; omega),
        List.take_of_length_le (by simp [hpre_len]; omega)]
    have htake_S : (SStep q).take (K - 2) = [w] ++ pre := by
      rw [hS_sp, List.take_append_of_le_length (by simp [hpre_len]; omega),
        List.take_of_length_le (by simp [hpre_len]; omega)]
    have hu_nb : notInBlock (6 * m) j u = true := by
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.takeWhile_cons] at hd
      cases hnb : notInBlock (6 * m) j u with
      | false => simp [hnb] at hd
      | true => rfl
    have hpre_tw : (pre.reverse.takeWhile (notInBlock (6 * m) j)).length = d := by
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.takeWhile_cons, hu_nb] at hd
      simp at hd; exact hd
    -- `pre` contains at least one element of `B_j` (since `q` has `6m ≥ 6` elements of `B_j`, and `[u, v, w]` has `≤ 2`)!
    have hpre_has : ∃ x ∈ pre.reverse, notInBlock (6 * m) j x = false := by
      have hcnt : (q.filter (inBlock (6 * m) j)).length = 6 * m := by
        rw [filter_inBlock_eq_map_projBlock hjb, List.length_map, hrot.perm.length_eq,
          (W6mState_isPerm m hm k _).2]
      rw [hq_sp, List.filter_append, List.length_append] at hcnt
      have h3 : ([u, v, w].filter (inBlock (6 * m) j)).length ≤ 3 :=
        (List.length_filter_le _ _).trans (by simp)
      have hpos : 0 < (pre.filter (inBlock (6 * m) j)).length := by omega
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hpos)
      exact ⟨x, List.mem_reverse.mpr (List.mem_filter.mp hx).1, by
        unfold notInBlock; rw [(List.mem_filter.mp hx).2]; rfl⟩
    have htw_S : ((pre.reverse ++ [w]).takeWhile (notInBlock (6 * m) j)) =
        pre.reverse.takeWhile (notInBlock (6 * m) j) := by
      have hgen : ∀ pr : List (Fin K), (∃ x ∈ pr, notInBlock (6 * m) j x = false) →
          (pr ++ [w]).takeWhile (notInBlock (6 * m) j) = pr.takeWhile (notInBlock (6 * m) j) := by
        intro pr
        induction pr with
        | nil => intro h; obtain ⟨x, hx, _⟩ := h; cases hx
        | cons y ys ihy =>
          intro h
          simp only [List.cons_append, List.takeWhile_cons]
          cases hy : notInBlock (6 * m) j y with
          | false => rfl
          | true =>
            simp only [hy, ↓reduceIte, List.cons.injEq, true_and]
            apply ihy
            obtain ⟨x, hx, hxf⟩ := h
            rcases List.mem_cons.mp hx with rfl | hx'
            · rw [hy] at hxf; cases hxf
            · exact ⟨x, hx', hxf⟩
      exact hgen pre.reverse hpre_has
    have hstep := S_single_step_mod m hm r hr K hK hj hs hS hplt
    have hcl := ((iterW6mLift m hm r hr K hK).closed_S L hL hS).1
    have hq3_none : projBlockElem (6 * m) j (q[K - 3]'(by rw [hq.2]; omega)) = none :=
      (notInBlock_iff_projBlockElem_eq_none _ _ _).mp (hu_eq ▸ hu_nb)
    have hrot' : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep q))).1 ~r
        W6mState m hm k (6 * m - 3) := by
      rw [hcl]; exact (projBlock_SStep_of_none hK4 hq.2 (Or.inl hq3_none)).trans hrot
    have hS' : ((iterW6mLift m hm r hr K hK).row (canonLoop (SStep q))).2 = .S := by
      have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).2.1
      have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).1
      obtain ⟨k', hk', t', ht', hrot2, _, hS_of⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
      have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm hk hk' (by omega) ht' (hrot'.symm.trans hrot2)
      exact hS_of ht'_eq.symm
    have hd' : ((((iterW6mLift m hm r hr K hK).row (canonLoop (SStep q))).1.take (K - 2)).reverse.takeWhile
        (notInBlock (6 * m) j)).length = d := by
      rw [hcl, htake_S, List.reverse_append, List.reverse_singleton, htw_S, hpre_tw]
    obtain ⟨L', port', hs', hplt', hF', hproj', hreach'⟩ :=
      ih (canonLoop (SStep q)) ((port + 1) % (K - 1)) hstep.1 hS' hrot' (Nat.mod_lt _ (by omega)) hd'
    exact ⟨L', port', hs', hplt', hF', hproj', hstep.2.trans hreach'⟩

/-- **Sublemma B2b (`S_run_uCyc`):** From an `'S'`-slice `(L, .ins port)` with `port < K - 1`
and `projBlock b j q = W6mState m hm k (6m - 3)` (the exact entry state from `advance_F_to_S`!),
advancing through the `'S'`-run lands at an `'F'`-slice `(L', .ins port')` at `W6mState m hm ((k+1)%4m) 0`
whose `uCyc` equals `(uCyc q port).map fS`, where `fS` maps `b_in ↦ v`, `v ↦ w`, and fixes all other elements! -/
theorem S_run_uCyc (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {k : Nat} (hk : k < 4 * m)
    {L : List (Fin K)} {port : Nat}
    (hs : (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ)
    (hS : ((iterW6mLift m hm r hr K hK).row L).2 = .S)
    (hproj : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm k (6 * m - 3))
    (hplt : port < K - 1) :
    have hjb : (j + 1) * (6 * m) ≤ K := by
      have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
    let xB := W6mState m hm k (6 * m - 3)
    let bIn := embBlock (6 * m) K j hjb (xB[6 * m - 3]'(by rw [(W6mState_isPerm m hm k _).2]; omega))
    let vB  := embBlock (6 * m) K j hjb (xB[6 * m - 2]'(by rw [(W6mState_isPerm m hm k _).2]; omega))
    let wB  := embBlock (6 * m) K j hjb (xB[6 * m - 1]'(by rw [(W6mState_isPerm m hm k _).2]; omega))
    let fS : Fin K → Fin K := fun x => if x = bIn then vB else if x = vB then wB else x
    ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
      port' < K - 1 ∧
      ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm ((k + 1) % (4 * m)) 0 ∧
      uCyc ((iterW6mLift m hm r hr K hK).row L').1 port' =
        (uCyc ((iterW6mLift m hm r hr K hK).row L).1 port).map fS ∧
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
        (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  obtain ⟨hL, hact, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
  set q0 := ((iterW6mLift m hm r hr K hK).row L).1
  have hq0 : IsPerm K q0 := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
  set xB := W6mState m hm k (6 * m - 3)
  have hxB : IsPerm (6 * m) xB := W6mState_isPerm m hm k (6 * m - 3)
  set bIn := embBlock (6 * m) K j hjb (xB[6 * m - 3]'(by rw [hxB.2]; omega))
  set vB  := embBlock (6 * m) K j hjb (xB[6 * m - 2]'(by rw [hxB.2]; omega))
  set wB  := embBlock (6 * m) K j hjb (xB[6 * m - 1]'(by rw [hxB.2]; omega))
  set fS : Fin K → Fin K := fun x => if x = bIn then vB else if x = vB then wB else x
  -- Decompose `q0 = pre ++ [bIn] ++ M_run ++ [vB, wB]`!
  -- First, `q0[K - 2] = vB` (from `iterW6mRow_eq_S`), and since `projBlock b j q0 = xB`, `q0[K - 1]` MUST be `wB`!
  have hq0_km2 : q0[K - 2]'(by rw [hq0.2]; omega) = vB := by
    obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
    have hbl_eq : blockLoop (6 * m) j L = canonLoop xB := by
      have hr1 : projBlock (6 * m) j L ~r projBlock (6 * m) j q0 :=
        projBlock_isRotated ((iterW6mLift m hm r hr K hK).row_perm L hL).2.symm
      rw [hproj] at hr1
      exact (canonLoop_eq_iff (projBlock_isPerm hjb hL.1) hxB).mpr hr1
    have hrowB_eq : (selW6m m hm).row (blockLoop (6 * m) j L) = (xB, .S) := by
      rw [hbl_eq, selW6m_row_state m hm hk (by omega)]; simp; rfl
    have hS_B : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .S := by rw [hrowB_eq]
    have hlenB : 6 * m - 2 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
      rw [hrowB_eq, hxB.2]; omega
    have hq_pin : q0 = pinAt L vB (K - 2) := by
      have h1 : (iterW6mLift m hm r hr K hK).row L = _ := iterW6mRow_eq_S hm hK hact hj_lt hjb hS_B hlenB
      dsimp only [q0]; rw [h1]; simp only [hrowB_eq, vB]
    simpa [hq_pin] using pinAt_getElem hL.1 vB (by omega : K - 2 < K)
  have hq0_km1 : q0[K - 1]'(by rw [hq0.2]; omega) = wB := by
    -- `wB` is in `q0`, and in `projBlock b j q0 = xB`, `wB` comes strictly AFTER `vB = q0[K - 2]`!
    have hw_mem : wB ∈ q0 := mem_of_isPerm hq0 wB
    have htake : q0 = q0.take (K - 2) ++ [q0[K - 2]'(by rw [hq0.2]; omega), q0[K - 1]'(by rw [hq0.2]; omega)] := by
      obtain ⟨pre, u, v, w, hsp, _, hpl, _, hv, hw⟩ := split_last3 hK4 hq0.2
      rw [← hv, ← hw]
      have h1 : q0 = (pre ++ [u]) ++ [v, w] := by rw [hsp]; simp [List.append_assoc]
      have h2 : q0.take (K - 2) = pre ++ [u] := by
        rw [h1, List.take_append_of_le_length (by simp [hpl]; omega),
          List.take_of_length_le (by simp [hpl]; omega)]
      rw [h2]; exact h1
    by_contra hne
    have hw_in_take : wB ∈ q0.take (K - 2) := by
      have hm := hw_mem
      rw [htake, List.mem_append, List.mem_cons, List.mem_singleton] at hm
      rcases hm with h1 | h2 | h3
      · exact h1
      · rw [hq0_km2] at h2
        have hvb_ne : vB ≠ wB := by
          intro he
          have hv1 := congrArg Fin.val he; dsimp [vB, wB, embBlock] at hv1
          have hfin : xB[6 * m - 2]'(by rw [hxB.2]; omega) = xB[6 * m - 1]'(by rw [hxB.2]; omega) :=
            Fin.ext (by omega)
          have := (List.Nodup.getElem_inj_iff hxB.1).mp hfin; omega
        exact absurd h2.symm hvb_ne
      · exact absurd h3.symm hne
    -- Then `xB[6*m - 1]` appears BEFORE `xB[6*m - 2]` in `projBlock b j q0 = xB`, impossible!
    have hproj_split : xB =
        projBlock (6 * m) j (q0.take (K - 2)) ++
        ([xB[6 * m - 2]'(by rw [hxB.2]; omega)] ++
        [q0[K - 1]'(by rw [hq0.2]; omega)].filterMap (projBlockElem (6 * m) j)) := by
      conv_lhs => rw [← hproj]; unfold projBlock; rw [htake, List.filterMap_append, List.filterMap_cons, hq0_km2,
        projBlockElem_embBlock]
      simp [projBlock]
    have hmem_pre : xB[6 * m - 1]'(by rw [hxB.2]; omega) ∈ projBlock (6 * m) j (q0.take (K - 2)) := by
      unfold projBlock; rw [List.mem_filterMap]
      exact ⟨wB, hw_in_take, projBlockElem_embBlock _ _ _ _ _⟩
    have hlen_pre : (projBlock (6 * m) j (q0.take (K - 2))).length ≤ 6 * m - 1 := by
      have hlen_eq := congrArg List.length hproj_split
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen_eq
      rw [hxB.2] at hlen_eq; omega
    obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem_pre
    have hget_xB : xB[idx]'(by rw [hxB.2]; omega) = xB[6 * m - 1]'(by rw [hxB.2]; omega) := by
      have h1 : xB[idx]? = (projBlock (6 * m) j (q0.take (K - 2)))[idx]? := by
        conv_lhs => rw [hproj_split]
        rw [List.getElem?_append_left hidx]
      rw [List.getElem?_eq_getElem (by rw [hxB.2]; omega), List.getElem?_eq_getElem hidx, hget] at h1
      exact Option.some.inj h1
    have := (List.Nodup.getElem_inj_iff hxB.1).mp hget_xB
    omega
  -- Now split `q0.take (K - 2)` at `bIn`!
  have hbIn_in_take : bIn ∈ q0.take (K - 2) := by
    have hm := mem_of_isPerm hq0 bIn
    have htake : q0 = q0.take (K - 2) ++ [vB, wB] := by
      obtain ⟨pre, u, v, w, hsp, _, hpl, _, hv, hw⟩ := split_last3 hK4 hq0.2
      rw [← hq0_km2, ← hq0_km1, ← hv, ← hw]
      have h1 : q0 = (pre ++ [u]) ++ [v, w] := by rw [hsp]; simp [List.append_assoc]
      have h2 : q0.take (K - 2) = pre ++ [u] := by
        rw [h1, List.take_append_of_le_length (by simp [hpl]; omega),
          List.take_of_length_le (by simp [hpl]; omega)]
      rw [h2]; exact h1
    rw [htake, List.mem_append, List.mem_cons, List.mem_singleton] at hm
    rcases hm with h1 | h2 | h3
    · exact h1
    · have hv1 := congrArg Fin.val h2; dsimp [bIn, vB, embBlock] at hv1
      have := (List.Nodup.getElem_inj_iff hxB.1).mp (Fin.ext (by omega : (xB[6 * m - 3]'(by rw [hxB.2]; omega)).1 = (xB[6 * m - 2]'(by rw [hxB.2]; omega)).1)); omega
    · have hv1 := congrArg Fin.val h3; dsimp [bIn, wB, embBlock] at hv1
      have := (List.Nodup.getElem_inj_iff hxB.1).mp (Fin.ext (by omega : (xB[6 * m - 3]'(by rw [hxB.2]; omega)).1 = (xB[6 * m - 1]'(by rw [hxB.2]; omega)).1)); omega
  let idxB := (q0.take (K - 2)).idxOf bIn
  have hidxB_lt : idxB < K - 2 := by
    have := List.idxOf_lt_length_of_mem hbIn_in_take; simp [hq0.2] at this; omega
  let pre := (q0.take (K - 2)).take idxB
  let M_run := (q0.take (K - 2)).drop (idxB + 1)
  have hq0_decomp : q0 = pre ++ [bIn] ++ M_run ++ [vB, wB] := by
    have htake : q0 = q0.take (K - 2) ++ [vB, wB] := by
      obtain ⟨p, u, v, w, hsp, _, hpl, _, hv, hw⟩ := split_last3 hK4 hq0.2
      rw [← hq0_km2, ← hq0_km1, ← hv, ← hw]
      have h1 : q0 = (p ++ [u]) ++ [v, w] := by rw [hsp]; simp [List.append_assoc]
      have h2 : q0.take (K - 2) = p ++ [u] := by
        rw [h1, List.take_append_of_le_length (by simp [hpl]; omega),
          List.take_of_length_le (by simp [hpl]; omega)]
      rw [h2]; exact h1
    have hsplit_tk : q0.take (K - 2) = pre ++ [bIn] ++ M_run := by
      have h1 := (List.take_append_drop idxB (q0.take (K - 2))).symm
      have hdrop : (q0.take (K - 2)).drop idxB = bIn :: M_run := by
        rw [List.drop_eq_getElem_cons (by simp [hq0.2]; omega)]
        congr 1; exact List.getElem_idxOf _
      rw [hdrop] at h1; simpa [pre, List.append_assoc] using h1
    rw [htake, hsplit_tk]
  -- Every element of `M_run` is NOT in `B_j` (since `projBlock b j q0 = xB` has `bIn, vB, wB` as its last 3 elements!)
  have hM_none : ∀ x ∈ M_run, projBlockElem (6 * m) j x = none := by
    intro x hx
    by_contra hne
    cases hpx : projBlockElem (6 * m) j x with
    | none => exact hne hpx
    | some a =>
      have hproj_d : xB =
          projBlock (6 * m) j pre ++
          ([xB[6 * m - 3]'(by rw [hxB.2]; omega)] ++
          projBlock (6 * m) j M_run ++ [xB[6 * m - 2]'(by rw [hxB.2]; omega), xB[6 * m - 1]'(by rw [hxB.2]; omega)]) := by
        conv_lhs => rw [← hproj]; unfold projBlock; rw [hq0_decomp]
        simp [List.filterMap_append, List.filterMap_cons, bIn, vB, wB, projBlockElem_embBlock, List.append_assoc]
        rfl
      have ha_mem : a ∈ projBlock (6 * m) j M_run := List.mem_filterMap.mpr ⟨x, hx, hpx⟩
      have hlen_M : 0 < (projBlock (6 * m) j M_run).length := List.length_pos_of_mem ha_mem
      have hidx_bIn : (projBlock (6 * m) j pre).length < 6 * m - 3 := by
        have hlen_eq := congrArg List.length hproj_d
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen_eq
        rw [hxB.2] at hlen_eq; omega
      have hget_bIn : xB[(projBlock (6 * m) j pre).length]'(by rw [hxB.2]; omega) =
          xB[6 * m - 3]'(by rw [hxB.2]; omega) := by
        have h1 : xB[(projBlock (6 * m) j pre).length]? = some (xB[6 * m - 3]'(by rw [hxB.2]; omega)) := by
          conv_lhs => rw [hproj_d]
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          simp
        rw [List.getElem?_eq_getElem (by rw [hxB.2]; omega)] at h1
        exact Option.some.inj h1
      have := (List.Nodup.getElem_inj_iff hxB.1).mp hget_bIn
      omega
  -- Now run `t + 1` steps of `SStep` (`t = M_run.length`)!
  let t := M_run.length
  let midSeq := [bIn] ++ M_run ++ [wB]
  have hmid_len : midSeq.length = t + 2 := by simp [midSeq, t]
  have hmid_getD : ∀ i (hi : i < midSeq.length), midSeq.getD i bIn = midSeq[i]'hi := by
    intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hpre_t : pre.length + t + 3 = K := by
    have := congrArg List.length hq0_decomp; rw [hq0.2] at this; simp [t] at this; omega
  -- Explicit formula for `q_s = SStep^[s] q0` (`0 ≤ s ≤ t + 1`), completely non-dependent via `getD`!
  let qAt (s : Nat) : List (Fin K) :=
    (M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t + 1 - s) ++
      [vB, midSeq.getD (t + 1 - s) bIn]
  have hqAt_zero : qAt 0 = q0 := by
    dsimp only [qAt]
    have h1 : (M_run ++ [wB]).drop (t + 1) = [] := List.drop_eq_nil_of_le (by simp [t])
    have h2 : ([bIn] ++ M_run).take (t + 1) = [bIn] ++ M_run := List.take_of_length_le (by simp [t])
    have h3 : midSeq.getD (t + 1) bIn = wB := by
      rw [hmid_getD (t + 1) (by rw [hmid_len]; omega)]
      dsimp only [midSeq]; rw [List.getElem_append_right (by simp [t])]; simp [t]
    rw [Nat.sub_zero, h1, h2, h3, List.nil_append, hq0_decomp]; simp [List.append_assoc]
  have hqAt_step : ∀ s ≤ t, SStep (qAt s) = qAt (s + 1) := by
    intro s hs_le
    dsimp only [qAt]
    have hlen_B : ((M_run ++ [wB]).drop (t + 1 - s)).length = s := by simp [t]; omega
    have hlen_A : (([bIn] ++ M_run).take (t + 1 - s)).length = t + 1 - s := by simp [t]
    have hpos_rem : 1 ≤ t + 1 - s := by omega
    -- Split `([bIn] ++ M_run).take (t + 1 - s)` as `take (t - s) ++ [midSeq.getD (t - s) bIn]`!
    have hA_split : ([bIn] ++ M_run).take (t + 1 - s) =
        ([bIn] ++ M_run).take (t - s) ++ [midSeq.getD (t - s) bIn] := by
      have hts : t + 1 - s = (t - s) + 1 := by omega
      rw [hts, List.take_succ_eq_append_getElem (by simp [t]), hmid_getD (t - s) (by rw [hmid_len]; omega)]
      congr 2
      dsimp only [midSeq]
      exact (List.getElem_append_left (by simp [t])).symm
    -- Split `(M_run ++ [wB]).drop (t - s)` as `[midSeq.getD (t + 1 - s) bIn] ++ drop (t + 1 - s)`!
    have hB_split : (M_run ++ [wB]).drop (t - s) =
        [midSeq.getD (t + 1 - s) bIn] ++ (M_run ++ [wB]).drop (t + 1 - s) := by
      have h1 := List.drop_eq_getElem_cons (l := M_run ++ [wB]) (i := t - s) (by simp [t])
      rw [show t - s + 1 = t + 1 - s by omega] at h1
      rw [h1, List.singleton_append, hmid_getD (t + 1 - s) (by rw [hmid_len]; omega)]
      congr 1
      dsimp only [midSeq]
      have hms : [bIn] ++ M_run ++ [wB] = bIn :: (M_run ++ [wB]) := by simp
      have hts : t + 1 - s = (t - s) + 1 := by omega
      simp only [hms, hts, List.getElem_cons_succ]
    have hq_sp : (M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t + 1 - s) ++
        [vB, midSeq.getD (t + 1 - s) bIn] =
        ((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)) ++
          [midSeq.getD (t - s) bIn, vB, midSeq.getD (t + 1 - s) bIn] := by
      rw [hA_split]; simp [List.append_assoc]
    have hpre3_len : ((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)).length = K - 3 := by
      simp [hlen_B, t]; omega
    rw [hq_sp]
    unfold SStep
    have hlen_full : (((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)) ++
        [midSeq.getD (t - s) bIn, vB, midSeq.getD (t + 1 - s) bIn]).length = K := by
      simp [hpre3_len]; omega
    rw [hlen_full]
    have htake3 : (((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)) ++
        [midSeq.getD (t - s) bIn, vB, midSeq.getD (t + 1 - s) bIn]).take (K - 3) =
        (M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s) := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hdrop1 : (((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)) ++
        [midSeq.getD (t - s) bIn, vB, midSeq.getD (t + 1 - s) bIn]).drop (K - 1) =
        [midSeq.getD (t + 1 - s) bIn] := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hpre3_len,
        show K - 1 - (K - 3) = 2 by omega]; rfl
    have hdrop3 : ((((M_run ++ [wB]).drop (t + 1 - s) ++ pre ++ ([bIn] ++ M_run).take (t - s)) ++
        [midSeq.getD (t - s) bIn, vB, midSeq.getD (t + 1 - s) bIn]).drop (K - 3)).take 2 =
        [midSeq.getD (t - s) bIn, vB] := by
      rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]; rfl
    rw [htake3, hdrop1, hdrop3]
    have hts' : t + 1 - (s + 1) = t - s := by omega
    simp only [hts', hB_split, List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc]
    rfl
  -- Prove by induction on `s ≤ t + 1` that `(canonLoop (qAt s), .ins ((port + s) % (K - 1)))` is in `layerSlices`,
  -- has `row.1 = qAt s`, and is reached from `(L, .ins port)`!
  have hind : ∀ s ≤ t + 1,
      (canonLoop (qAt s), SliceTag.ins ((port + s) % (K - 1))) ∈ layerSlices m hm r hr K hK j σ ∧
      ((iterW6mLift m hm r hr K hK).row (canonLoop (qAt s))).1 = qAt s ∧
      (s ≤ t → ((iterW6mLift m hm r hr K hK).row (canonLoop (qAt s))).2 = .S) ∧
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
        (sliceStartV m hm r hr K hK (canonLoop (qAt s), SliceTag.ins ((port + s) % (K - 1)))) := by
    intro s
    induction s with
    | zero =>
      intro _
      have hL_eq : canonLoop (qAt 0) = L := by
        rw [hqAt_zero]
        exact isCanonLoop_eq_of_isRotated (canonLoop_isCanonLoop hq0) hL
          ((canonLoop_isRotated q0).symm.trans ((iterW6mLift m hm r hr K hK).row_perm L hL).2)
      rw [hL_eq, Nat.add_zero, Nat.mod_eq_of_lt hplt]
      exact ⟨hs, hqAt_zero.symm, fun _ => hS, Relation.ReflTransGen.refl⟩
    | succ s ih =>
      intro hs1_le
      obtain ⟨hmem_s, hrow1_s, hS_s_of, hreach_s⟩ := ih (by omega)
      have hS_s := hS_s_of (by omega)
      have hstep := S_single_step_mod m hm r hr K hK hj hmem_s hS_s (Nat.mod_lt _ (by omega))
      have hmod_step : ((port + s) % (K - 1) + 1) % (K - 1) = (port + (s + 1)) % (K - 1) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
      have hS_eq : SStep ((iterW6mLift m hm r hr K hK).row (canonLoop (qAt s))).1 = qAt (s + 1) := by
        rw [hrow1_s]; exact hqAt_step s (by omega)
      dsimp only at hstep
      rw [hS_eq, hmod_step] at hstep
      have hL_s := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hmem_s).1
      have hcl := ((iterW6mLift m hm r hr K hK).closed_S (canonLoop (qAt s)) hL_s hS_s).1
      rw [hS_eq] at hcl
      refine ⟨hstep.1, hcl, ?_, hreach_s.trans hstep.2⟩
      intro hs1_t
      -- When `s + 1 ≤ t`, `qAt (s + 1)` still has `projBlock b j (qAt (s + 1)) ~r xB`, hence row type is `.S`!
      have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).2.1
      have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hstep.1).1
      obtain ⟨k', hk', t', ht', hrot', _, hS_of⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
      rw [hcl] at hrot'
      have hproj_rot_s1 : projBlock (6 * m) j (qAt (s + 1)) ~r xB := by
        dsimp only [qAt]
        have hM_proj_nil : ∀ l : List (Fin K), (∀ x ∈ l, projBlockElem (6 * m) j x = none) →
            l.filterMap (projBlockElem (6 * m) j) = [] := fun l hl =>
          List.filterMap_eq_nil_iff.mpr hl
        have htake_eq : (([bIn] ++ M_run).take (t + 1 - (s + 1))).filterMap (projBlockElem (6 * m) j) =
            [xB[6 * m - 3]'(by rw [hxB.2]; omega)] := by
          have hpos : 0 < t + 1 - (s + 1) := by omega
          cases hd' : t + 1 - (s + 1) with
          | zero => omega
          | succ d' =>
            simp only [List.singleton_append, List.take_succ_cons, List.filterMap_cons,
              bIn, projBlockElem_embBlock]
            rw [hM_proj_nil _ (fun x hx => hM_none x (List.mem_of_mem_take hx))]
        have hdrop_eq : (((M_run ++ [wB]).drop (t + 1 - (s + 1))).filterMap (projBlockElem (6 * m) j)) =
            [xB[6 * m - 1]'(by rw [hxB.2]; omega)] := by
          have hle : t + 1 - (s + 1) ≤ M_run.length := by dsimp [t]; omega
          rw [List.drop_append_of_le_length hle, List.filterMap_append,
            hM_proj_nil _ (fun x hx => hM_none x (List.mem_of_mem_drop hx)), List.nil_append]
          simp [wB, projBlockElem_embBlock]
        have hmid_none : projBlockElem (6 * m) j (midSeq.getD (t + 1 - (s + 1)) bIn) = none := by
          rw [hmid_getD (t + 1 - (s + 1)) (by rw [hmid_len]; omega)]
          apply hM_none
          dsimp only [midSeq]
          have h1 : t + 1 - (s + 1) < ([bIn] ++ M_run).length := by simp [t]
          rw [List.getElem_append_left h1]
          have hpos : 1 ≤ t + 1 - (s + 1) := by omega
          rw [List.getElem_append_right (by simp; omega)]
          exact List.getElem_mem _
        have hproj_q0 : projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega),
            xB[6 * m - 2]'(by rw [hxB.2]; omega), xB[6 * m - 1]'(by rw [hxB.2]; omega)] = xB := by
          conv_rhs => rw [← hproj]
          unfold projBlock; rw [hq0_decomp]
          simp [List.filterMap_append, List.filterMap_cons, bIn, vB, wB, projBlockElem_embBlock,
            hM_proj_nil M_run hM_none, List.append_assoc]
        have hproj_qs : projBlock (6 * m) j (qAt (s + 1)) =
            [xB[6 * m - 1]'(by rw [hxB.2]; omega)] ++
            (projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega), xB[6 * m - 2]'(by rw [hxB.2]; omega)]) := by
          unfold projBlock; dsimp only [qAt]
          rw [List.filterMap_append, List.filterMap_append, List.filterMap_append,
            hdrop_eq, htake_eq, List.filterMap_cons, List.filterMap_cons, List.filterMap_nil,
            hmid_none]
          simp [projBlock, vB, projBlockElem_embBlock, List.append_assoc]
        have hrot_1 := List.rotate_append_length_eq
          (projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega), xB[6 * m - 2]'(by rw [hxB.2]; omega)])
          [xB[6 * m - 1]'(by rw [hxB.2]; omega)]
        have hrot_2 : (projBlock (6 * m) j (qAt (s + 1))) ~r
            (projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega), xB[6 * m - 2]'(by rw [hxB.2]; omega),
              xB[6 * m - 1]'(by rw [hxB.2]; omega)]) := by
          rw [hproj_qs]
          have hcat : (projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega), xB[6 * m - 2]'(by rw [hxB.2]; omega)]) ++
              [xB[6 * m - 1]'(by rw [hxB.2]; omega)] =
              projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega), xB[6 * m - 2]'(by rw [hxB.2]; omega),
                xB[6 * m - 1]'(by rw [hxB.2]; omega)] := by simp [List.append_assoc]
          rw [← hcat]
          exact List.IsRotated.symm ⟨_, hrot_1⟩
        have hcast : ∀ a b : List (Fin (6 * m)), a = b →
            projBlock (6 * m) j (qAt (s + 1)) ~r a → projBlock (6 * m) j (qAt (s + 1)) ~r b := by
          intro a b hab hr; subst hab; exact hr
        exact hcast _ _ hproj_q0 hrot_2
      have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm hk hk' (by omega) ht' (hproj_rot_s1.symm.trans hrot')
      exact hS_of ht'_eq.symm
  -- Apply `hind` at `s = t + 1`!
  obtain ⟨hmem_fin, hrow1_fin, _, hreach_fin⟩ := hind (t + 1) (Nat.le_refl _)
  have hqAt_fin : qAt (t + 1) = M_run ++ [wB] ++ pre ++ [vB, bIn] := by
    dsimp only [qAt]
    rw [Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil]
    have h0 : midSeq.getD 0 bIn = bIn := by simp [midSeq]
    rw [h0]
  -- Compute `projBlock (6 * m) j (qAt (t + 1)) = SStep xB = W6mState m hm ((k + 1) % (4 * m)) 0`!
  have hproj_fin : projBlock (6 * m) j (qAt (t + 1)) = W6mState m hm ((k + 1) % (4 * m)) 0 := by
    have hM_proj_nil : M_run.filterMap (projBlockElem (6 * m) j) = [] :=
      List.filterMap_eq_nil_iff.mpr hM_none
    have hproj_q0 : projBlock (6 * m) j pre ++ [xB[6 * m - 3]'(by rw [hxB.2]; omega),
        xB[6 * m - 2]'(by rw [hxB.2]; omega), xB[6 * m - 1]'(by rw [hxB.2]; omega)] = xB := by
      conv_rhs => rw [← hproj]
      unfold projBlock; rw [hq0_decomp]
      simp [List.filterMap_append, List.filterMap_cons, bIn, vB, wB, projBlockElem_embBlock,
        hM_proj_nil, List.append_assoc]
    have hpreB_len : (projBlock (6 * m) j pre).length = 6 * m - 3 := by
      have hlen_eq := congrArg List.length hproj_q0
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen_eq
      rw [hxB.2] at hlen_eq; omega
    have hSStep_xB : SStep xB = [xB[6 * m - 1]'(by rw [hxB.2]; omega)] ++ projBlock (6 * m) j pre ++
        [xB[6 * m - 2]'(by rw [hxB.2]; omega), xB[6 * m - 3]'(by rw [hxB.2]; omega)] := by
      obtain ⟨preB, uB, vB', wB', hxB_sp, hSB, hpreB_l, _, _, _⟩ := split_last3 (by omega) hxB.2
      rw [← hproj_q0] at hxB_sp
      have hpe : projBlock (6 * m) j pre = preB := by
        have := congrArg (List.take (6 * m - 3)) hxB_sp
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
          List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
        exact this
      rw [hpe, List.append_cancel_left_eq] at hxB_sp
      simp only [List.cons.injEq, and_true] at hxB_sp
      rw [hSB, hpe, hxB_sp.1, hxB_sp.2.1, hxB_sp.2.2]
    have hSS_eq : SStep xB = W6mState m hm ((k + 1) % (4 * m)) 0 := SStep_W6mState m hm k
    rw [← hSS_eq, hSStep_xB]
    unfold projBlock; rw [hqAt_fin]
    simp [List.filterMap_append, List.filterMap_cons, bIn, vB, wB, projBlockElem_embBlock,
      hM_proj_nil, projBlock, List.append_assoc]
  have hF_fin : ((iterW6mLift m hm r hr K hK).row (canonLoop (qAt (t + 1)))).2 = .F := by
    have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hmem_fin).2.1
    have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hmem_fin).1
    obtain ⟨k', hk', t', ht', hrot', hF_of, _⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
    rw [hrow1_fin, hproj_fin] at hrot'
    have ⟨_, ht'_eq⟩ := W6m_loop_disjoint m hm (Nat.mod_lt (k + 1) (by omega)) hk' (by omega) ht' hrot'
    exact (hF_of (by omega)).1
  -- Finally, the 10-line algebraic `uCyc` identity!
  have huCyc_fin : uCyc (qAt (t + 1)) ((port + (t + 1)) % (K - 1)) = (uCyc q0 port).map fS := by
    have htake0 : q0.take (K - 1) = pre ++ [bIn] ++ M_run ++ [vB] := by
      have h1 : q0 = (pre ++ [bIn] ++ M_run ++ [vB]) ++ [wB] := by rw [hq0_decomp]; simp [List.append_assoc]
      have hlen1 : (pre ++ [bIn] ++ M_run ++ [vB]).length = K - 1 := by simp [t]; omega
      rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have htake1 : (qAt (t + 1)).take (K - 1) = M_run ++ [wB] ++ pre ++ [vB] := by
      have h1 : qAt (t + 1) = (M_run ++ [wB] ++ pre ++ [vB]) ++ [bIn] := by rw [hqAt_fin]; simp [List.append_assoc]
      have hlen1 : (M_run ++ [wB] ++ pre ++ [vB]).length = K - 1 := by simp [t]; omega
      rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    -- Check `fS` on `pre`, `M_run`, `bIn`, `vB`!
    have hnd0 : q0.Nodup := hq0.1
    rw [hq0_decomp] at hnd0
    have hpre_id : pre.map fS = pre := by
      have hc : pre.map fS = pre.map id := by
        refine List.map_congr_left fun x hx => ?_
        have hxb : x ≠ bIn := fun h => by
          subst h; rw [List.append_assoc, List.append_assoc, List.nodup_append] at hnd0
          exact hnd0.2.2 bIn hx bIn (by simp) rfl
        have hxv : x ≠ vB := fun h => by
          subst h; rw [List.append_assoc, List.append_assoc, List.nodup_append] at hnd0
          exact hnd0.2.2 vB hx vB (by simp) rfl
        dsimp only [fS, id_eq]; simp [hxb, hxv]
      rw [hc, List.map_id]
    have hM_id : M_run.map fS = M_run := by
      have hc : M_run.map fS = M_run.map id := by
        refine List.map_congr_left fun x hx => ?_
        have hxb : x ≠ bIn := fun h => by
          subst h; have h1 := hM_none bIn hx; dsimp only [bIn] at h1; rw [projBlockElem_embBlock] at h1; cases h1
        have hxv : x ≠ vB := fun h => by
          subst h; have h1 := hM_none vB hx; dsimp only [vB] at h1; rw [projBlockElem_embBlock] at h1; cases h1
        dsimp only [fS, id_eq]; simp [hxb, hxv]
      rw [hc, List.map_id]
    have hbv_ne : vB ≠ bIn := by
      intro h; have hv := congrArg Fin.val h; dsimp [bIn, vB, embBlock] at hv
      have := (List.Nodup.getElem_inj_iff hxB.1).mp (Fin.ext (by omega : (xB[6 * m - 2]'(by rw [hxB.2]; omega)).1 = (xB[6 * m - 3]'(by rw [hxB.2]; omega)).1)); omega
    have hmap0 : (q0.take (K - 1)).map fS = (pre ++ [vB]) ++ (M_run ++ [wB]) := by
      rw [htake0]
      simp [List.map_append, hpre_id, hM_id, fS, hbv_ne, List.append_assoc]
    have hrot_1 : ((q0.take (K - 1)).map fS).rotate (pre.length + 1) = (qAt (t + 1)).take (K - 1) := by
      rw [hmap0, htake1]
      have hlen_pv : (pre ++ [vB]).length = pre.length + 1 := by simp
      have hr := List.rotate_append_length_eq (pre ++ [vB]) (M_run ++ [wB])
      rw [hlen_pv] at hr; rw [hr]; simp [List.append_assoc]
    have hlen_t1 : ((qAt (t + 1)).take (K - 1)).length = K - 1 := by rw [htake1]; simp [t]; omega
    have hrot_mod : ((qAt (t + 1)).take (K - 1)).rotate ((port + (t + 1)) % (K - 1)) =
        ((qAt (t + 1)).take (K - 1)).rotate (port + (t + 1)) := by
      simpa [hlen_t1] using List.rotate_mod ((qAt (t + 1)).take (K - 1)) (port + (t + 1))
    unfold uCyc
    rw [hrot_mod, ← hrot_1, List.rotate_rotate]
    have hlen_r0 : (((q0.take (K - 1)).map fS).rotate port).length = K - 1 := by
      rw [List.length_rotate, List.length_map, List.length_take, hq0.2]; omega
    have hsum_rot : pre.length + 1 + (port + (t + 1)) = port + (((q0.take (K - 1)).map fS).rotate port).length := by
      rw [hlen_r0]; omega
    rw [hsum_rot, ← List.rotate_rotate, List.rotate_length, ← List.map_rotate]
  refine ⟨canonLoop (qAt (t + 1)), (port + (t + 1)) % (K - 1), hmem_fin, Nat.mod_lt _ (by omega),
    hF_fin, by rw [hrow1_fin, hproj_fin], by rw [hrow1_fin, huCyc_fin], hreach_fin⟩

/-- **Sublemma B (`reach_x0_from_any`):** Every slice `s ∈ layerSlices j σ` is connected in `layerBag j σ`
to some `x_0`-slice `(L', .ins port')` (`projBlock b j q' = W6mState m hm 0 0`, `port' < K - 1`)! -/
theorem reach_x0_from_any (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {s : List (Fin K) × SliceTag}
    (hs : s ∈ layerSlices m hm r hr K hK j σ) :
    ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
      port' < K - 1 ∧
      ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm 0 0 ∧
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK s)
        (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  -- Helper 1: from ANY `k < 4m`, an `'F'`-slice at `(k, 0)` reaches an `'F'`-slice at `((k + 1) % 4m, 0)`!
  have hblock_step : ∀ (k : Nat) (hk : k < 4 * m) (L : List (Fin K)) (port : Nat),
      (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm k 0 →
      ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
        port' < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 =
          W6mState m hm ((k + 1) % (4 * m)) 0 ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
    intro k hk L port hs0 hF0 hproj0
    obtain ⟨Ls, ps, hss, hps, hSs, hprojs, _, hrs⟩ :=
      advance_F_to_S m hm r hr K hK hj hk (6 * m - 3) (by omega) 0 (by omega) L port hs0 hproj0 (fun _ => hF0)
    obtain ⟨Lf, pf, hsf, hpf, hFf, hprojf, _, hrf⟩ :=
      S_run_uCyc m hm r hr K hK hj hk hss hSs hprojs hps
    exact ⟨Lf, pf, hsf, hpf, hFf, hprojf, hrs.trans hrf⟩
  -- Helper 2: iterating `hblock_step` `rem` times from `(k, 0)` reaches `((k + rem) % 4m, 0)`!
  have hblock_iter : ∀ (rem : Nat) (k : Nat) (hk : k < 4 * m) (L : List (Fin K)) (port : Nat),
      (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm k 0 →
      ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
        port' < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 =
          W6mState m hm ((k + rem) % (4 * m)) 0 ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk L port hs0 hF0 hproj0
      rw [Nat.add_zero, Nat.mod_eq_of_lt hk]
      obtain ⟨hL0, _, htag0, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs0
      have hport : port < K := by
        rw [hF0] at htag0; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag0
        obtain ⟨p, hp, hpe⟩ := htag0; cases hpe; exact hp
      by_cases hlt : port < K - 1
      · exact ⟨L, port, hs0, hlt, hF0, hproj0, Relation.ReflTransGen.refl⟩
      · have hp_eq : port = K - 1 := by omega
        subst hp_eq
        -- `(L, .ins 0) → (L, .ins (K - 1))`!
        have hs_zero : (L, SliceTag.ins 0) ∈ layerSlices m hm r hr K hK j σ := by
          obtain ⟨hL, hact, _, hsig⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs0
          have hlast := (layer_F_step_info m hm r hr K hK hL hact hF0).1
          have hq := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
          refine (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, ?_⟩
          · rw [hF0]; exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
          · rw [← tagSigma_F_zero hK4 hq.2 hlast]; exact hsig
        have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs_zero 1
        have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins 0) = (L, .ins (K - 1)) := by
          simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF0]; simp
        rw [h1] at hr1
        exact ⟨L, 0, hs_zero, by omega, hF0, hproj0, undirReach_symm hr1.2⟩
    | succ rem' ih =>
      intro k hk L port hs0 hF0 hproj0
      obtain ⟨L1, p1, hs1, _, hF1, hproj1, hr1⟩ := hblock_step k hk L port hs0 hF0 hproj0
      obtain ⟨L2, p2, hs2, hp2, hF2, hproj2, hr2⟩ :=
        ih ((k + 1) % (4 * m)) (Nat.mod_lt _ (by omega)) L1 p1 hs1 hF1 hproj1
      have hmod : ((k + 1) % (4 * m) + rem') % (4 * m) = (k + (rem' + 1)) % (4 * m) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show k + 1 + rem' = k + (rem' + 1) by omega]
      rw [hmod] at hproj2
      exact ⟨L2, p2, hs2, hp2, hF2, hproj2, hr1.trans hr2⟩
  -- Step 1: Reach SOME `(k, 0)` `'F'`-slice from `s = (L, tag)`!
  rcases s with ⟨L, tag⟩
  obtain ⟨hL, hact, htag, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
  obtain ⟨k, hk, t, ht, hrot, hF_of, hS_of⟩ := layerRow_W6mState_info m hm r hr K hK hL hact
  have hreach_k0 : ∃ k0 < 4 * m, ∃ L0 p0, (L0, SliceTag.ins p0) ∈ layerSlices m hm r hr K hK j σ ∧
      ((iterW6mLift m hm r hr K hK).row L0).2 = .F ∧
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L0).1 = W6mState m hm k0 0 ∧
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK (L, tag))
        (sliceStartV m hm r hr K hK (L0, SliceTag.ins p0)) := by
    by_cases hlt : t < 6 * m - 3
    · obtain ⟨hF, hproj⟩ := hF_of hlt
      rw [hF] at htag; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
      obtain ⟨port, _, rfl⟩ := htag
      obtain ⟨Ls, ps, hss, hps, hSs, hprojs, _, hrs⟩ :=
        advance_F_to_S m hm r hr K hK hj hk (6 * m - 3 - t) (by omega) t (by omega) L port hs hproj (fun _ => hF)
      obtain ⟨Lf, pf, hsf, _, hFf, hprojf, _, hrf⟩ :=
        S_run_uCyc m hm r hr K hK hj hk hss hSs hprojs hps
      exact ⟨(k + 1) % (4 * m), Nat.mod_lt _ (by omega), Lf, pf, hsf, hFf, hprojf, hrs.trans hrf⟩
    · have ht_eq : t = 6 * m - 3 := by omega
      subst ht_eq
      have hS := hS_of rfl
      -- First reach `(L, .ins p)` with `p < K - 1` (for `repKm2`/`repKm1`/`ins (K-1)`, step back to `ins (K-2)`!)
      have hto_lt : ∃ p < K - 1, (L, SliceTag.ins p) ∈ layerSlices m hm r hr K hK j σ ∧
          Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
            (sliceStartV m hm r hr K hK (L, tag))
            (sliceStartV m hm r hr K hK (L, SliceTag.ins p)) := by
        have hkm2_mem : (L, SliceTag.ins (K - 2)) ∈ layerSlices m hm r hr K hK j σ →
            Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
              (sliceStartV m hm r hr K hK (L, SliceTag.ins (K - 2)))
              (sliceStartV m hm r hr K hK (L, .repKm2)) ∧
            Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
              (sliceStartV m hm r hr K hK (L, SliceTag.ins (K - 2)))
              (sliceStartV m hm r hr K hK (L, .repKm1)) ∧
            Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
              (sliceStartV m hm r hr K hK (L, SliceTag.ins (K - 2)))
              (sliceStartV m hm r hr K hK (L, SliceTag.ins (K - 1))) := by
          intro hkm2
          have h1 := reach_nextSlice_iter m hm r hr K hK hj hkm2 1
          have h2 := reach_nextSlice_iter m hm r hr K hK hj hkm2 2
          have h3 := reach_nextSlice_iter m hm r hr K hK hj hkm2 3
          have hs1 : nextSlice m hm r hr K hK (L, .ins (K - 2)) = (L, .repKm2) := by
            unfold nextSlice; dsimp only; rw [hS]; simp [show ¬(K - 2 ≤ K - 3) by omega]
          have hs2 : nextSlice m hm r hr K hK (L, .repKm2) = (L, .repKm1) := by
            unfold nextSlice; dsimp only; rw [hS]
          have hs3 : nextSlice m hm r hr K hK (L, .repKm1) = (L, .ins (K - 1)) := by
            unfold nextSlice; dsimp only; rw [hS]
          simp only [Function.iterate_one, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
            hs1, hs2, hs3] at h1 h2 h3
          exact ⟨h1.2, h2.2, h3.2⟩
        have hkm2_in_slices : ∀ (ht' : tag = .repKm2 ∨ tag = .repKm1 ∨ tag = .ins (K - 1)),
            (L, SliceTag.ins (K - 2)) ∈ layerSlices m hm r hr K hK j σ := by
          intro ht'
          obtain ⟨_, _, _, hsig⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
          refine (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, ?_⟩
          · rw [hS]; exact List.mem_append_left _ (List.mem_map.mpr ⟨K - 2, List.mem_range.mpr (by omega), rfl⟩)
          · rcases ht' with rfl | rfl | rfl
            · exact hsig
            · exact hsig
            · have hkm2_in := (layer_S_step_info m hm r hr K hK hL hact hS).1
              have hq := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
              rw [← (tagSigma_S_detour hK4 hq.2 hkm2_in).1]; exact hsig
        cases tag with
        | repKm2 =>
          have hm2 := hkm2_in_slices (Or.inl rfl)
          exact ⟨K - 2, by omega, hm2, undirReach_symm (hkm2_mem hm2).1⟩
        | repKm1 =>
          have hm2 := hkm2_in_slices (Or.inr (Or.inl rfl))
          exact ⟨K - 2, by omega, hm2, undirReach_symm (hkm2_mem hm2).2.1⟩
        | ins p =>
          rw [hS] at htag
          simp only [tagsOfRowType, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
            List.not_mem_nil, or_false, reduceCtorEq, or_self] at htag
          obtain ⟨p', hp', hpe⟩ := htag; have hp : p < K := by cases hpe; exact hp'
          by_cases hltp : p < K - 1
          · exact ⟨p, hltp, hs, Relation.ReflTransGen.refl⟩
          · have hpeq : p = K - 1 := by omega
            subst hpeq
            have hm2 := hkm2_in_slices (Or.inr (Or.inr rfl))
            exact ⟨K - 2, by omega, hm2, undirReach_symm (hkm2_mem hm2).2.2⟩
      obtain ⟨p, hplt, hsp, hrp⟩ := hto_lt
      obtain ⟨Lf, pf, hsf, _, hFf, hprojf, hrf⟩ :=
        advance_S_to_F_any m hm r hr K hK hj hk _ L p hsp hS hrot hplt rfl
      exact ⟨(k + 1) % (4 * m), Nat.mod_lt _ (by omega), Lf, pf, hsf, hFf, hprojf, hrp.trans hrf⟩
  obtain ⟨k0, hk0, L0, p0, hs0, hF0, hproj0, hr0⟩ := hreach_k0
  obtain ⟨Lf, pf, hsf, hpf, hFf, hprojf, hrf⟩ :=
    hblock_iter (4 * m - k0) k0 hk0 L0 p0 hs0 hF0 hproj0
  have hmod0 : (k0 + (4 * m - k0)) % (4 * m) = 0 := by
    rw [show k0 + (4 * m - k0) = 4 * m by omega, Nat.mod_self]
  rw [hmod0] at hprojf
  exact ⟨Lf, pf, hsf, hpf, hFf, hprojf, hr0.trans hrf⟩

/-- **Sublemma C (`reach_any_bSeq_rot`):** At `x_0 = W6mState m hm 0 0`, from any slice `(L, .ins port)`
with `B_j`-mask `M = (uCyc q port).map (inBlock (6 * m) j)` and `projBlock (6 * m) j (uCyc q port) =
((List.finRange (6 * m)).take (6 * m - 1)).rotate d`, for ANY target rotation `d_target : Nat`,
there exists an `x_0`-slice `(L', .ins port')` connected to `(L, .ins port)` in `layerBag j σ`
with the **EXACT SAME** `B_j`-mask `M` and `projBlock (6 * m) j (uCyc q' port') =
((List.finRange (6 * m)).take (6 * m - 1)).rotate d_target`! -/
theorem reach_any_bSeq_rot (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {L : List (Fin K)} {port : Nat}
    (hs : (L, SliceTag.ins port) ∈ layerSlices m hm r hr K hK j σ)
    (hF : ((iterW6mLift m hm r hr K hK).row L).2 = .F)
    (hproj : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm 0 0)
    (d_target : Nat) :
    ∃ L' port', (L', SliceTag.ins port') ∈ layerSlices m hm r hr K hK j σ ∧
      port' < K - 1 ∧
      ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm 0 0 ∧
      (uCyc ((iterW6mLift m hm r hr K hK).row L').1 port').map (inBlock (6 * m) j) =
        (uCyc ((iterW6mLift m hm r hr K hK).row L).1 port).map (inBlock (6 * m) j) ∧
      projBlock (6 * m) j (uCyc ((iterW6mLift m hm r hr K hK).row L').1 port') =
        ((W6mState m hm 0 0).take (6 * m - 1)).rotate d_target ∧
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK (L, SliceTag.ins port))
        (sliceStartV m hm r hr K hK (L', SliceTag.ins port')) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  -- Helper: `(W6mState m hm k t).take (6 * m - 1) = ((W6mState m hm k 0).take (6 * m - 1)).rotate t`!
  have htake_W6m : ∀ (k t : Nat),
      (W6mState m hm k t).take (6 * m - 1) = ((W6mState m hm k 0).take (6 * m - 1)).rotate t := by
    intro k t
    induction t with
    | zero => simp
    | succ t iht =>
      rw [← FStep_W6mState]
      obtain ⟨a, last, mid, hsp, hF_sp, hmid_len, _, _⟩ := split_first_last (by omega) (W6mState_isPerm m hm k t).2
      have htk1 : (W6mState m hm k t).take (6 * m - 1) = a :: mid := by
        rw [hsp, List.take_append_of_le_length (by simp [hmid_len]; omega),
          List.take_of_length_le (by simp [hmid_len]; omega)]
      have htk2 : (FStep (W6mState m hm k t)).take (6 * m - 1) = mid ++ [a] := by
        have h1 : FStep (W6mState m hm k t) = (mid ++ [a]) ++ [last] := by rw [hF_sp]; simp [List.append_assoc]
        rw [h1, List.take_append_of_le_length (by simp [hmid_len]; omega),
          List.take_of_length_le (by simp [hmid_len]; omega)]
      rw [htk2, show mid ++ [a] = (a :: mid).rotate 1 by rw [List.rotate_cons_succ, List.rotate_zero],
        ← htk1, iht, List.rotate_rotate]
  -- Helper: one full block `(k, 0) → ((k+1)%4m, 0)` preserves `mask` and shifts rotation offset `d` by `+3`!
  have hblock_shift : ∀ (k : Nat) (hk : k < 4 * m) (L0 : List (Fin K)) (p0 d : Nat),
      (L0, SliceTag.ins p0) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L0).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L0).1 = W6mState m hm k 0 →
      projBlock (6 * m) j (uCyc ((iterW6mLift m hm r hr K hK).row L0).1 p0) =
        ((W6mState m hm k 0).take (6 * m - 1)).rotate d →
      ∃ L1 p1, (L1, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ ∧
        p1 < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L1).2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L1).1 =
          W6mState m hm ((k + 1) % (4 * m)) 0 ∧
        (uCyc ((iterW6mLift m hm r hr K hK).row L1).1 p1).map (inBlock (6 * m) j) =
          (uCyc ((iterW6mLift m hm r hr K hK).row L0).1 p0).map (inBlock (6 * m) j) ∧
        projBlock (6 * m) j (uCyc ((iterW6mLift m hm r hr K hK).row L1).1 p1) =
          ((W6mState m hm ((k + 1) % (4 * m)) 0).take (6 * m - 1)).rotate (d + 3) ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L0, SliceTag.ins p0))
          (sliceStartV m hm r hr K hK (L1, SliceTag.ins p1)) := by
    intro k hk L0 p0 d hs0 hF0 hproj0 hb0
    obtain ⟨Ls, ps, hss, hps, hSs, hprojs, hus, hrs⟩ :=
      advance_F_to_S m hm r hr K hK hj hk (6 * m - 3) (by omega) 0 (by omega) L0 p0 hs0 hproj0 (fun _ => hF0)
    obtain ⟨Lf, pf, hsf, hpf, hFf, hprojf, huf, hrf⟩ :=
      S_run_uCyc m hm r hr K hK hj hk hss hSs hprojs hps
    set xB := W6mState m hm k (6 * m - 3)
    have hxB := W6mState_isPerm m hm k (6 * m - 3)
    set bIn := embBlock (6 * m) K j hjb (xB[6 * m - 3]'(by rw [hxB.2]; omega))
    set vB  := embBlock (6 * m) K j hjb (xB[6 * m - 2]'(by rw [hxB.2]; omega))
    set wB  := embBlock (6 * m) K j hjb (xB[6 * m - 1]'(by rw [hxB.2]; omega))
    set fS : Fin K → Fin K := fun x => if x = bIn then vB else if x = vB then wB else x
    set fB : Fin (6 * m) → Fin (6 * m) := fun a =>
      if a = xB[6 * m - 3]'(by rw [hxB.2]; omega) then xB[6 * m - 2]'(by rw [hxB.2]; omega)
      else if a = xB[6 * m - 2]'(by rw [hxB.2]; omega) then xB[6 * m - 1]'(by rw [hxB.2]; omega)
      else a
    -- Check `inBlock (6 * m) j (fS x) = inBlock (6 * m) j x`!
    have hfS_in : ∀ x : Fin K, inBlock (6 * m) j (fS x) = inBlock (6 * m) j x := by
      intro x; dsimp only [fS]
      by_cases h1 : x = bIn
      · subst h1; simp [vB, bIn, inBlock_embBlock]
      · by_cases h2 : x = vB
        · subst h2; simp [h1, wB, vB, inBlock_embBlock]
        · simp [h1, h2]
    -- Check `projBlock (6 * m) j (l.map fS) = (projBlock (6 * m) j l).map fB`!
    have hfS_proj : ∀ l : List (Fin K), projBlock (6 * m) j (l.map fS) = (projBlock (6 * m) j l).map fB := by
      intro l; unfold projBlock
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, List.filterMap_cons]
        cases hx : projBlockElem (6 * m) j x with
        | none =>
          have h1 : x ≠ bIn := fun h => by subst h; dsimp [bIn] at hx; rw [projBlockElem_embBlock] at hx; cases hx
          have h2 : x ≠ vB := fun h => by subst h; dsimp [vB] at hx; rw [projBlockElem_embBlock] at hx; cases hx
          have hfx : fS x = x := by dsimp only [fS]; simp [h1, h2]
          rw [hfx, hx]; exact ih
        | some a =>
          have hxe : x = embBlock (6 * m) K j hjb a := (projBlockElem_eq_some_iff (6 * m) j hjb x a).mp hx
          have hfx : fS x = embBlock (6 * m) K j hjb (fB a) := by
            rw [hxe]; dsimp only [fS, fB, bIn, vB, wB]
            have hinj : Function.Injective (embBlock (6 * m) K j hjb) := fun a1 a2 h => by
              have hv := congrArg Fin.val h; dsimp [embBlock] at hv; apply Fin.ext; omega
            by_cases h1 : a = xB[6 * m - 3]'(by rw [hxB.2]; omega)
            · simp [h1]
            · have h1' : embBlock (6 * m) K j hjb a ≠ embBlock (6 * m) K j hjb (xB[6 * m - 3]'(by rw [hxB.2]; omega)) :=
                fun h => h1 (hinj h)
              by_cases h2 : a = xB[6 * m - 2]'(by rw [hxB.2]; omega)
              · rw [if_neg h1', if_pos (congrArg _ h2), if_neg h1, if_pos h2]
              · have h2' : embBlock (6 * m) K j hjb a ≠ embBlock (6 * m) K j hjb (xB[6 * m - 2]'(by rw [hxB.2]; omega)) :=
                  fun h => h2 (hinj h)
                rw [if_neg h1', if_neg h2', if_neg h1, if_neg h2]
          rw [hfx, projBlockElem_embBlock, ih]; rfl
    -- Check `(xB.take (6 * m - 1)).map fB = ((SStep xB).take (6 * m - 1)).rotate 1`!
    have hmap_xB : (xB.take (6 * m - 1)).map fB = ((SStep xB).take (6 * m - 1)).rotate 1 := by
      have hxB' : IsPerm (6 * m) xB := hxB
      obtain ⟨preB, uB, vB', wB', hxB_sp, hSB, hpreB_l, huB, hvB, hwB⟩ := split_last3 (by omega) hxB'.2
      have htk1 : xB.take (6 * m - 1) = preB ++ [uB, vB'] := by
        have h1 : xB = (preB ++ [uB, vB']) ++ [wB'] := by rw [hxB_sp]; simp [List.append_assoc]
        rw [h1, List.take_append_of_le_length (by simp [hpreB_l]; omega),
          List.take_of_length_le (by simp [hpreB_l]; omega)]
      have htk2 : (SStep xB).take (6 * m - 1) = [wB'] ++ preB ++ [vB'] := by
        have h1 : SStep xB = ([wB'] ++ preB ++ [vB']) ++ [uB] := by rw [hSB]; simp [List.append_assoc]
        rw [h1, List.take_append_of_le_length (by simp [hpreB_l]; omega),
          List.take_of_length_le (by simp [hpreB_l]; omega)]
      have hpre_id : preB.map fB = preB := by
        calc preB.map fB = preB.map id := List.map_congr_left fun a ha => ?_
          _ = preB := List.map_id _
        have hnd := hxB'.1; rw [hxB_sp, List.nodup_append] at hnd
        have h1 : a ≠ uB := fun h => hnd.2.2 a ha a (by simp [h]) rfl
        have h2 : a ≠ vB' := fun h => hnd.2.2 a ha a (by simp [h]) rfl
        dsimp only [fB, id_eq]; rw [← huB, ← hvB]; simp [h1, h2]
      have hvu_ne : vB' ≠ uB := by
        have hnd := hxB'.1; rw [hxB_sp, List.nodup_append] at hnd
        have h1 := (List.nodup_cons.mp hnd.2.1).1
        intro h; exact h1 (by simp [h])
      rw [htk1, htk2, List.map_append, hpre_id]
      have hrot1 : ([wB'] ++ preB ++ [vB']).rotate 1 = preB ++ [vB', wB'] := by
        simp [List.rotate_cons_succ, List.rotate_zero, List.append_assoc]
      rw [hrot1]; congr 1
      dsimp only [fB]; rw [← huB, ← hvB, ← hwB]; simp [hvu_ne]
    refine ⟨Lf, pf, hsf, hpf, hFf, hprojf, ?_, ?_, hrs.trans hrf⟩
    · rw [huf, hus, List.map_map]
      refine List.map_congr_left fun x _ => hfS_in x
    · rw [huf, hfS_proj, hus, hb0]
      have hlen_t : ((W6mState m hm k 0).take (6 * m - 1)).length = 6 * m - 1 := by
        simp [(W6mState_isPerm m hm k 0).2]
      have h1 : ((W6mState m hm k 0).take (6 * m - 1)).rotate d =
          (xB.take (6 * m - 1)).rotate (d + 2) := by
        have hrot_len : (((W6mState m hm k 0).take (6 * m - 1)).rotate d).rotate (6 * m - 1) =
            ((W6mState m hm k 0).take (6 * m - 1)).rotate d := by
          have hl : (((W6mState m hm k 0).take (6 * m - 1)).rotate d).length = 6 * m - 1 := by
            rw [List.length_rotate, hlen_t]
          simpa [hl] using List.rotate_length (((W6mState m hm k 0).take (6 * m - 1)).rotate d)
        calc ((W6mState m hm k 0).take (6 * m - 1)).rotate d
            = (((W6mState m hm k 0).take (6 * m - 1)).rotate d).rotate (6 * m - 1) := hrot_len.symm
          _ = ((W6mState m hm k 0).take (6 * m - 1)).rotate (d + (6 * m - 1)) := by rw [List.rotate_rotate]
          _ = ((W6mState m hm k 0).take (6 * m - 1)).rotate ((6 * m - 3) + (d + 2)) := by
                congr 1; omega
          _ = (((W6mState m hm k 0).take (6 * m - 1)).rotate (6 * m - 3)).rotate (d + 2) := by
                rw [List.rotate_rotate]
          _ = (xB.take (6 * m - 1)).rotate (d + 2) := by rw [← htake_W6m k (6 * m - 3)]
      have hSS_eq : SStep xB = W6mState m hm ((k + 1) % (4 * m)) 0 := SStep_W6mState m hm k
      rw [h1, List.map_rotate, hmap_xB, List.rotate_rotate, hSS_eq,
        show 1 + (d + 2) = d + 3 by omega]
  -- Iterating `hblock_shift` `N` times shifts `(0, 0) → (N % 4m, 0)` and `d ↦ d + 3 * N`!
  have hblock_shift_iter : ∀ (N : Nat) (L0 : List (Fin K)) (p0 d : Nat),
      (L0, SliceTag.ins p0) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L0).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L0).1 = W6mState m hm 0 0 →
      projBlock (6 * m) j (uCyc ((iterW6mLift m hm r hr K hK).row L0).1 p0) =
        ((W6mState m hm 0 0).take (6 * m - 1)).rotate d →
      ∃ L1 p1, (L1, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ ∧
        p1 < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L1).2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L1).1 =
          W6mState m hm (N % (4 * m)) 0 ∧
        (uCyc ((iterW6mLift m hm r hr K hK).row L1).1 p1).map (inBlock (6 * m) j) =
          (uCyc ((iterW6mLift m hm r hr K hK).row L0).1 p0).map (inBlock (6 * m) j) ∧
        projBlock (6 * m) j (uCyc ((iterW6mLift m hm r hr K hK).row L1).1 p1) =
          ((W6mState m hm (N % (4 * m)) 0).take (6 * m - 1)).rotate (d + 3 * N) ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L0, SliceTag.ins p0))
          (sliceStartV m hm r hr K hK (L1, SliceTag.ins p1)) := by
    intro N
    induction N with
    | zero =>
      intro L0 p0 d hs0 hF0 hproj0 hb0
      -- Ensure `p1 < K - 1` by stepping back `0 → K - 1` if needed (keeps `uCyc` equal!)
      obtain ⟨hL0, hact0, htag0, hsig0⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs0
      have hp0_lt : p0 < K := by
        rw [hF0] at htag0; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag0
        obtain ⟨p, hp, hpe⟩ := htag0; cases hpe; exact hp
      by_cases hlt : p0 < K - 1
      · exact ⟨L0, p0, hs0, hlt, hF0, by simpa using hproj0, rfl, by simpa using hb0, Relation.ReflTransGen.refl⟩
      · have hp_eq : p0 = K - 1 := by omega
        subst hp_eq
        have hq0 := ((iterW6mLift m hm r hr K hK).row_perm L0 hL0).1
        have hlast := (layer_F_step_info m hm r hr K hK hL0 hact0 hF0).1
        have hs_zero : (L0, SliceTag.ins 0) ∈ layerSlices m hm r hr K hK j σ := by
          refine (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL0, hact0, ?_, ?_⟩
          · rw [hF0]; exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
          · rw [← tagSigma_F_zero hK4 hq0.2 hlast]; exact hsig0
        have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs_zero 1
        have h1 : (nextSlice m hm r hr K hK)^[1] (L0, .ins 0) = (L0, .ins (K - 1)) := by
          simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF0]; simp
        rw [h1] at hr1
        have hu0 : uCyc ((iterW6mLift m hm r hr K hK).row L0).1 0 =
            uCyc ((iterW6mLift m hm r hr K hK).row L0).1 (K - 1) := (uCyc_F_zero hq0.2).symm
        exact ⟨L0, 0, hs_zero, by omega, hF0, by simpa using hproj0, by rw [hu0],
          by simpa [hu0] using hb0, undirReach_symm hr1.2⟩
    | succ N ih =>
      intro L0 p0 d hs0 hF0 hproj0 hb0
      obtain ⟨L1, p1, hs1, _, hF1, hproj1, hmask1, hb1, hr1⟩ := ih L0 p0 d hs0 hF0 hproj0 hb0
      obtain ⟨L2, p2, hs2, hp2, hF2, hproj2, hmask2, hb2, hr2⟩ :=
        hblock_shift (N % (4 * m)) (Nat.mod_lt _ (by omega)) L1 p1 (d + 3 * N) hs1 hF1 hproj1 hb1
      have hmod : (N % (4 * m) + 1) % (4 * m) = (N + 1) % (4 * m) := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [hmod] at hproj2 hb2
      rw [show d + 3 * N + 3 = d + 3 * (N + 1) by ring] at hb2
      exact ⟨L2, p2, hs2, hp2, hF2, hproj2, hmask2.trans hmask1, hb2, hr1.trans hr2⟩
  -- Find the initial rotation offset `d0` of `projBlock b j (uCyc q port)` relative to `(W6mState 0 0).take (b - 1)`!
  obtain ⟨hL, hact, _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
  set q := ((iterW6mLift m hm r hr K hK).row L).1
  have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
  have hq_last_in : inBlock (6 * m) j (q[K - 1]'(by rw [hq.2]; omega)) = true :=
    (layer_F_step_info m hm r hr K hK hL hact hF).1
  have hproj_take : projBlock (6 * m) j (q.take (K - 1)) = (W6mState m hm 0 0).take (6 * m - 1) := by
    obtain ⟨a, last, mid, hsp, _, hmid_len, _, hlast_eq⟩ := split_first_last hK4 hq.2
    have htk : q.take (K - 1) = a :: mid := by
      rw [hsp, List.take_append_of_le_length (by simp [hmid_len]; omega),
        List.take_of_length_le (by simp [hmid_len]; omega)]
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hq_last_in)
    have hdec : projBlock (6 * m) j q = projBlock (6 * m) j (q.take (K - 1)) ++ [l'] := by
      unfold projBlock; rw [htk, hsp, List.filterMap_append]
      simp [List.filterMap_cons, hlast_eq ▸ hl']
    have hlen1 : (projBlock (6 * m) j (q.take (K - 1))).length = 6 * m - 1 := by
      have hlen_eq := congrArg List.length hdec
      rw [hproj, (W6mState_isPerm m hm 0 0).2] at hlen_eq
      simp at hlen_eq; omega
    have h1 := congrArg (List.take (6 * m - 1)) hdec
    rw [hproj, List.take_append_of_le_length (le_of_eq hlen1.symm), List.take_of_length_le (le_of_eq hlen1)] at h1
    exact h1.symm
  have hrot_u : projBlock (6 * m) j (uCyc q port) ~r (W6mState m hm 0 0).take (6 * m - 1) := by
    rw [← hproj_take]; exact (projBlock_isRotated ⟨port, rfl⟩).symm
  obtain ⟨d0, hd0⟩ := hrot_u.symm
  -- Choose `steps := ((d_target + (6 * m - 1) - d0 % (6 * m - 1)) % (6 * m - 1)) * (3 * m)` full laps!
  -- Each full lap is `4 * m` blocks, shifting by `12 * m ≡ 2 mod (6 * m - 1)`, so `3 * m` full laps shift by `36 * m^2 = 3 * m * 12 * m ≡ 6 * m ≡ 1 mod (6 * m - 1)`!
  let delta := (d_target + (6 * m - 1) - d0 % (6 * m - 1)) % (6 * m - 1)
  let N := delta * (3 * m) * (4 * m)
  obtain ⟨L', p', hs', hp', hF', hproj', hmask', hb', hr'⟩ :=
    hblock_shift_iter N L port d0 hs hF hproj hd0.symm
  have hN_mod : N % (4 * m) = 0 := by
    dsimp only [N]; rw [Nat.mul_mod_left]
  rw [hN_mod] at hproj' hb'
  have hrot_eq : ((W6mState m hm 0 0).take (6 * m - 1)).rotate (d0 + 3 * N) =
      ((W6mState m hm 0 0).take (6 * m - 1)).rotate d_target := by
    have hlen_w : ((W6mState m hm 0 0).take (6 * m - 1)).length = 6 * m - 1 := by
      simp [(W6mState_isPerm m hm 0 0).2]
    rw [← List.rotate_mod, ← List.rotate_mod _ d_target, hlen_w]
    congr 1
    have h3N : 3 * N = (delta * (6 * m) + delta) * (6 * m - 1) + delta := by
      dsimp only [N]
      have h1 : 6 * m = (6 * m - 1) + 1 := by omega
      have h2 : delta * (6 * m) = delta * (6 * m - 1) + delta := by
        calc delta * (6 * m) = delta * ((6 * m - 1) + 1) := by congr 1
          _ = delta * (6 * m - 1) + delta := by ring
      calc 3 * (delta * (3 * m) * (4 * m)) = (delta * (6 * m)) * (6 * m) := by ring
        _ = (delta * (6 * m)) * ((6 * m - 1) + 1) := by congr 1
        _ = delta * (6 * m) * (6 * m - 1) + delta * (6 * m) := by ring
        _ = delta * (6 * m) * (6 * m - 1) + (delta * (6 * m - 1) + delta) := by rw [h2]
        _ = (delta * (6 * m) + delta) * (6 * m - 1) + delta := by ring
    have hmod_3N : (3 * N) % (6 * m - 1) = delta % (6 * m - 1) := by
      rw [h3N, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    have hdelta_lt : delta < 6 * m - 1 := Nat.mod_lt _ (by omega)
    rw [Nat.add_mod, hmod_3N, Nat.mod_eq_of_lt hdelta_lt]
    dsimp only [delta]
    have hd0_lt : d0 % (6 * m - 1) < 6 * m - 1 := Nat.mod_lt _ (by omega)
    have hsum : d0 % (6 * m - 1) + (d_target + (6 * m - 1) - d0 % (6 * m - 1)) =
        d_target + (6 * m - 1) := by omega
    calc (d0 % (6 * m - 1) + (d_target + (6 * m - 1) - d0 % (6 * m - 1)) % (6 * m - 1)) % (6 * m - 1)
        = (d0 % (6 * m - 1) + (d_target + (6 * m - 1) - d0 % (6 * m - 1))) % (6 * m - 1) := by
            conv_lhs => rw [Nat.add_mod]
            rw [Nat.mod_mod, Nat.mod_mod]
            conv_rhs => rw [Nat.add_mod]
            rw [Nat.mod_mod]
      _ = (d_target + (6 * m - 1)) % (6 * m - 1) := by rw [hsum]
      _ = d_target % (6 * m - 1) := Nat.add_mod_right _ _
  rw [hrot_eq] at hb'
  exact ⟨L', p', hs', hp', hF', hproj', hmask', hb', hr'⟩

/-! ### 4. Sublemma D: Any two `x_0`-slices with the same `uCyc` are connected! -/

theorem same_uCyc_connected (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} {L1 L2 : List (Fin K)} {p1 p2 : Nat}
    (hs1 : (L1, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ)
    (hs2 : (L2, SliceTag.ins p2) ∈ layerSlices m hm r hr K hK j σ)
    (hF1 : ((iterW6mLift m hm r hr K hK).row L1).2 = .F)
    (hF2 : ((iterW6mLift m hm r hr K hK).row L2).2 = .F)
    (hproj1 : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L1).1 = W6mState m hm 0 0)
    (hproj2 : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L2).1 = W6mState m hm 0 0)
    (hu_eq : uCyc ((iterW6mLift m hm r hr K hK).row L1).1 p1 =
             uCyc ((iterW6mLift m hm r hr K hK).row L2).1 p2) :
    Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
      (sliceStartV m hm r hr K hK (L1, SliceTag.ins p1))
      (sliceStartV m hm r hr K hK (L2, SliceTag.ins p2)) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  -- Helper: slide any `x_0`-slice `(L, .ins p)` to the unique `x_0`-slice with the same `uCyc`, `q[0] = emb_j 0`, and `port < K - 1`!
  have hslide : ∀ (d : Nat) (L : List (Fin K)) (p : Nat),
      (L, SliceTag.ins p) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm 0 0 →
      leadingMj (6 * m) j (((iterW6mLift m hm r hr K hK).row L).1.take (K - 1)) = d →
      ∃ L' p', (L', SliceTag.ins p') ∈ layerSlices m hm r hr K hK j σ ∧
        p' < K - 1 ∧
        ((iterW6mLift m hm r hr K hK).row L').2 = .F ∧
        projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L').1 = W6mState m hm 0 0 ∧
        uCyc ((iterW6mLift m hm r hr K hK).row L').1 p' =
          uCyc ((iterW6mLift m hm r hr K hK).row L).1 p ∧
        (((iterW6mLift m hm r hr K hK).row L').1)[0]? =
          some (embBlock (6 * m) K j hjb ⟨0, by omega⟩) ∧
        Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (L, SliceTag.ins p))
          (sliceStartV m hm r hr K hK (L', SliceTag.ins p')) := by
    intro d
    induction d with
    | zero =>
      intro L p hs hF hproj hd
      obtain ⟨hL, hact, htag, hsig⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
      set q := ((iterW6mLift m hm r hr K hK).row L).1
      have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
      -- `d = 0` means `q[0] ∈ B_j`, and since `projBlock b j q = [0, 1, ..., b - 1]`, `q[0] = emb_j 0`!
      have hq0_eq : q[0]? = some (embBlock (6 * m) K j hjb ⟨0, by omega⟩) := by
        rw [List.getElem?_eq_getElem (by rw [hq.2]; omega)]; congr 1
        have htake_pos : 0 < (q.take (K - 1)).length := by simp [hq.2]; omega
        cases hqt : q.take (K - 1) with
        | nil => rw [hqt] at htake_pos; simp at htake_pos
        | cons a rest =>
          have ha_eq : a = q[0]'(by rw [hq.2]; omega) := by
            have := congrArg (fun l => l[0]?) hqt
            rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by rw [hq.2]; omega),
              List.getElem?_cons_zero] at this
            exact (Option.some.inj this).symm
          unfold leadingMj at hd; rw [hqt, List.takeWhile_cons] at hd
          have ha_in : inBlock (6 * m) j a = true := by
            cases hnb : notInBlock (6 * m) j a with
            | true => simp [hnb] at hd
            | false => unfold notInBlock at hnb; simp at hnb; exact hnb
          obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp ha_in)
          have hq_cons : q = a :: (rest ++ q.drop (K - 1)) := by
            have := (List.take_append_drop (K - 1) q).symm; rwa [hqt, List.cons_append] at this
          have hpr_hd : (projBlock (6 * m) j q)[0]? = some a' := by
            unfold projBlock; rw [hq_cons, List.filterMap_cons, ha']; rfl
          rw [hproj, W6mState_zero_zero, List.getElem?_eq_getElem (by simp; omega), List.getElem_finRange] at hpr_hd
          have ha'_0 : a' = ⟨0, by omega⟩ := (Option.some.inj hpr_hd).symm
          rw [← ha_eq, (projBlockElem_eq_some_iff (6 * m) j hjb a a').mp ha', ha'_0]
      have hp_lt : p < K := by
        rw [hF] at htag; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
        obtain ⟨p', hp', hpe⟩ := htag; cases hpe; exact hp'
      by_cases hlt : p < K - 1
      · exact ⟨L, p, hs, hlt, hF, hproj, rfl, hq0_eq, Relation.ReflTransGen.refl⟩
      · have hp_eq : p = K - 1 := by omega
        subst hp_eq
        have hlast := (layer_F_step_info m hm r hr K hK hL hact hF).1
        have hs_zero : (L, SliceTag.ins 0) ∈ layerSlices m hm r hr K hK j σ := by
          refine (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL, hact, ?_, ?_⟩
          · rw [hF]; exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
          · rw [← tagSigma_F_zero hK4 hq.2 hlast]; exact hsig
        have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs_zero 1
        have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins 0) = (L, .ins (K - 1)) := by
          simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]; simp
        rw [h1] at hr1
        exact ⟨L, 0, hs_zero, by omega, hF, hproj, (uCyc_F_zero hq.2).symm, hq0_eq, undirReach_symm hr1.2⟩
    | succ d ih =>
      intro L p hs hF hproj hd
      obtain ⟨hL, hact, htag, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs
      set q := ((iterW6mLift m hm r hr K hK).row L).1
      have hq : IsPerm K q := ((iterW6mLift m hm r hr K hK).row_perm L hL).1
      have hp_lt : p < K := by
        rw [hF] at htag; simp only [tagsOfRowType, List.mem_map, List.mem_range] at htag
        obtain ⟨p', hp', hpe⟩ := htag; cases hpe; exact hp'
      have hpos : ∃ p1, 1 ≤ p1 ∧ p1 < K ∧ (L, SliceTag.ins p1) ∈ layerSlices m hm r hr K hK j σ ∧
          uCyc q p1 = uCyc q p ∧
          Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
            (sliceStartV m hm r hr K hK (L, SliceTag.ins p))
            (sliceStartV m hm r hr K hK (L, SliceTag.ins p1)) := by
        by_cases hp0 : p = 0
        · subst hp0
          have hr1 := reach_nextSlice_iter m hm r hr K hK hj hs 1
          have h1 : (nextSlice m hm r hr K hK)^[1] (L, .ins 0) = (L, .ins (K - 1)) := by
            simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]; simp
          rw [h1] at hr1
          exact ⟨K - 1, by omega, by omega, hr1.1, uCyc_F_zero hq.2, hr1.2⟩
        · exact ⟨p, by omega, hp_lt, hs, rfl, Relation.ReflTransGen.refl⟩
      obtain ⟨p1, hp1_ge, hp1_lt, hs1, hu1, hr1⟩ := hpos
      have hq0_nb : notInBlock (6 * m) j (q[0]'(by rw [hq.2]; omega)) = true := by
        have htake_pos : 0 < (q.take (K - 1)).length := by simp [hq.2]; omega
        cases hqt : q.take (K - 1) with
        | nil => rw [hqt] at htake_pos; simp at htake_pos
        | cons a rest =>
          have ha_eq : a = q[0]'(by rw [hq.2]; omega) := by
            have := congrArg (fun l => l[0]?) hqt
            rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by rw [hq.2]; omega),
              List.getElem?_cons_zero] at this
            exact (Option.some.inj this).symm
          unfold leadingMj at hd; rw [hqt, List.takeWhile_cons] at hd
          cases hnb : notInBlock (6 * m) j a with
          | false => simp [hnb] at hd
          | true => rw [← ha_eq]; exact hnb
      have hq0_none := (notInBlock_iff_projBlockElem_eq_none (6 * m) j _).mp hq0_nb
      have hhas : ∃ x ∈ q.take (K - 1), inBlock (6 * m) j x = true := by
        have hcnt : (q.filter (inBlock (6 * m) j)).length = 6 * m := by
          rw [filter_inBlock_eq_map_projBlock hjb, List.length_map, hproj, (W6mState_isPerm m hm 0 0).2]
        have hsplit : q = q.take (K - 1) ++ q.drop (K - 1) := (List.take_append_drop (K - 1) q).symm
        have hdl : (q.drop (K - 1)).length = 1 := by simp [hq.2]; omega
        have h1 : ((q.take (K - 1)).filter (inBlock (6 * m) j)).length +
            ((q.drop (K - 1)).filter (inBlock (6 * m) j)).length = 6 * m := by
          rw [← List.length_append, ← List.filter_append, ← hsplit]; exact hcnt
        have h2 : ((q.drop (K - 1)).filter (inBlock (6 * m) j)).length ≤ 1 :=
          (List.length_filter_le _ _).trans (by omega)
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (by omega : 0 < ((q.take (K - 1)).filter (inBlock (6 * m) j)).length))
        exact ⟨x, (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩
      have hr2 := reach_nextSlice_iter m hm r hr K hK hj hs1 1
      have h2 : (nextSlice m hm r hr K hK)^[1] (L, .ins p1) = (canonLoop (FStep q), .ins (p1 - 1)) := by
        simp only [Function.iterate_one]; unfold nextSlice; dsimp only; rw [hF]
        simp [show p1 ≠ 0 by omega]; rfl
      rw [h2] at hr2
      have hcl := ((iterW6mLift m hm r hr K hK).closed_F L hL hF).1
      have hproj' : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).1 =
          W6mState m hm 0 0 := by
        rw [hcl, projBlock_FStep_of_head_none hK4 hq.2 hq0_none, hproj]
      have hF' : ((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).2 = .F := by
        have hact' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hr2.1).2.1
        have hL' := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hr2.1).1
        obtain ⟨k', hk', t', ht', hrot', hF_of, _⟩ := layerRow_W6mState_info m hm r hr K hK hL' hact'
        rw [hproj'] at hrot'
        have ⟨_, hteq⟩ := W6m_loop_disjoint m hm (by omega) hk' (by omega) ht' hrot'
        exact (hF_of (by omega)).1
      have hd' : leadingMj (6 * m) j (((iterW6mLift m hm r hr K hK).row (canonLoop (FStep q))).1.take (K - 1)) = d := by
        rw [hcl]
        change leadingMj (6 * m) j ((FStep q).take (K - 1)) = d
        have hstep := leadingMj_FStep_of_none hK4 hq.2 hq0_nb hhas
        have hdq : leadingMj (6 * m) j (q.take (K - 1)) = d + 1 := hd
        omega
      obtain ⟨L', p', hs', hplt', hF_fin, hproj_fin, hu_fin, h0_fin, hr_fin⟩ :=
        ih (canonLoop (FStep q)) (p1 - 1) hr2.1 hF' hproj' hd'
      exact ⟨L', p', hs', hplt', hF_fin, hproj_fin, by rw [hu_fin, hcl, uCyc_F_pos hK4 hq.2 hp1_ge, hu1],
        h0_fin, (hr1.trans hr2.2).trans hr_fin⟩
  -- Slide BOTH `(L1, .ins p1)` and `(L2, .ins p2)` to their unique canonical representatives!
  obtain ⟨L1', p1', hs1', hp1', hF1', hproj1', hu1', h01', hr1'⟩ := hslide _ L1 p1 hs1 hF1 hproj1 rfl
  obtain ⟨L2', p2', hs2', hp2', hF2', hproj2', hu2', h02', hr2'⟩ := hslide _ L2 p2 hs2 hF2 hproj2 rfl
  have hu_same : uCyc ((iterW6mLift m hm r hr K hK).row L1').1 p1' =
      uCyc ((iterW6mLift m hm r hr K hK).row L2').1 p2' := by rw [hu1', hu2', hu_eq]
  -- Show `(L1', p1') = (L2', p2')`!
  obtain ⟨hL1', hact1', _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1'
  obtain ⟨hL2', hact2', _, _⟩ := (mem_layerSlices_iff m hm r hr K hK j σ _).mp hs2'
  set q1 := ((iterW6mLift m hm r hr K hK).row L1').1
  set q2 := ((iterW6mLift m hm r hr K hK).row L2').1
  have hq1 : IsPerm K q1 := ((iterW6mLift m hm r hr K hK).row_perm L1' hL1').1
  have hq2 : IsPerm K q2 := ((iterW6mLift m hm r hr K hK).row_perm L2' hL2').1
  -- Both `q1.take (K - 1)` and `q2.take (K - 1)` are rotations of `uCyc` starting at `emb_j 0` -> EQUAL!
  have htake_eq : q1.take (K - 1) = q2.take (K - 1) := by
    have hrot12 : q1.take (K - 1) ~r q2.take (K - 1) :=
      List.IsRotated.trans (⟨p1', rfl⟩ : q1.take (K - 1) ~r uCyc q1 p1')
        (hu_same ▸ List.IsRotated.symm (⟨p2', rfl⟩ : q2.take (K - 1) ~r uCyc q2 p2'))
    obtain ⟨rot, hrot⟩ := hrot12
    have hlen1 : (q1.take (K - 1)).length = K - 1 := by simp [hq1.2]
    have h01_val : q1[0]'(by rw [hq1.2]; omega) = embBlock (6 * m) K j hjb ⟨0, by omega⟩ := by
      have h1 := h01'; rw [List.getElem?_eq_getElem (by rw [hq1.2]; omega)] at h1
      exact Option.some.inj h1
    have h02_val : q2[0]'(by rw [hq2.2]; omega) = embBlock (6 * m) K j hjb ⟨0, by omega⟩ := by
      have h2 := h02'; rw [List.getElem?_eq_getElem (by rw [hq2.2]; omega)] at h2
      exact Option.some.inj h2
    have h0_eq : ((q1.take (K - 1)).rotate rot)[0]'(by rw [List.length_rotate, hlen1]; omega) =
        (q1.take (K - 1))[0]'(by rw [hlen1]; omega) := by
      have ha : (q2.take (K - 1))[0]'(by simp [hq2.2]; omega) = embBlock (6 * m) K j hjb ⟨0, by omega⟩ := by
        rw [List.getElem_take]; exact h02_val
      have hb : (q1.take (K - 1))[0]'(by rw [hlen1]; omega) = embBlock (6 * m) K j hjb ⟨0, by omega⟩ := by
        rw [List.getElem_take]; exact h01_val
      simpa [hrot, hb] using ha
    rw [List.getElem_rotate, Nat.zero_add] at h0_eq
    have hrmod : rot % (q1.take (K - 1)).length = 0 :=
      (List.Nodup.getElem_inj_iff hq1.1.take).mp h0_eq
    calc q1.take (K - 1) = (q1.take (K - 1)).rotate 0 := (List.rotate_zero _).symm
      _ = (q1.take (K - 1)).rotate (rot % (q1.take (K - 1)).length) := by rw [hrmod]
      _ = (q1.take (K - 1)).rotate rot := List.rotate_mod _ _
      _ = q2.take (K - 1) := hrot
  -- Both `q1[K - 1]` and `q2[K - 1]` equal `emb_j(b - 1)`!
  have hlast_eq : q1[K - 1]'(by rw [hq1.2]; omega) = q2[K - 1]'(by rw [hq2.2]; omega) := by
    have hget_last : ∀ (L : List (Fin K)) (hL : IsCanonLoop K L)
        (hact : activeLayer m hm r L = some j)
        (hF : ((iterW6mLift m hm r hr K hK).row L).2 = .F)
        (hproj : projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm 0 0),
        ((iterW6mLift m hm r hr K hK).row L).1[K - 1]'(by rw [((iterW6mLift m hm r hr K hK).row_perm L hL).1.2]; omega) =
          embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩ := by
      intro L hL hact hF hproj
      let _ : NeZero (6 * m) := ⟨by omega⟩
      obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
      have hbl_eq : blockLoop (6 * m) j L = canonLoop (W6mState m hm 0 0) := by
        have hr1 := projBlock_isRotated (b := 6 * m) (j := j) ((iterW6mLift m hm r hr K hK).row_perm L hL).2.symm
        rw [hproj] at hr1
        exact (canonLoop_eq_iff (projBlock_isPerm hjb hL.1) (W6mState_isPerm m hm 0 0)).mpr hr1
      have hrowB_eq : (selW6m m hm).row (blockLoop (6 * m) j L) = (W6mState m hm 0 0, .F) := by
        rw [hbl_eq, selW6m_row_state m hm (by omega) (by omega)]; simp [show (0 : Nat) ≠ 6 * m - 3 by omega]
      have hF_B : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 = .F := by rw [hrowB_eq]
      have hlenB : 6 * m - 1 < ((selW6m m hm).row (blockLoop (6 * m) j L)).1.length := by
        rw [hrowB_eq, (W6mState_isPerm m hm 0 0).2]; omega
      have hpin : ((iterW6mLift m hm r hr K hK).row L).1 =
          pinAt L (embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩) (K - 1) := by
        have h1 : (iterW6mLift m hm r hr K hK).row L = _ := iterW6mRow_eq_F hm hK hact hj_lt hjb hF_B hlenB
        rw [h1]; simp only [hrowB_eq, W6mState_zero_zero, List.getElem_finRange, Fin.cast_mk]
      simpa [hpin] using pinAt_getElem hL.1 (embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩) (by omega : K - 1 < K)
    rw [hget_last L1' hL1' hact1' hF1' hproj1', hget_last L2' hL2' hact2' hF2' hproj2']
  have hq_eq : q1 = q2 := by
    refine List.ext_getElem (hq1.2.trans hq2.2.symm) fun i hi1 hi2 => ?_
    by_cases hlt : i < K - 1
    · have h1 := congrArg (fun l => l[i]?) htake_eq
      rw [List.getElem?_take_of_lt hlt, List.getElem?_take_of_lt hlt,
        List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at h1
      exact Option.some.inj h1
    · have hi_eq : i = K - 1 := by rw [hq1.2] at hi1; omega
      subst hi_eq; exact hlast_eq
  have hL_eq : L1' = L2' := by
    have hr1 : q1 ~r L1' := ((iterW6mLift m hm r hr K hK).row_perm L1' hL1').2
    have hr2 : q2 ~r L2' := ((iterW6mLift m hm r hr K hK).row_perm L2' hL2').2
    rw [hq_eq] at hr1
    exact isCanonLoop_eq_of_isRotated hL1' hL2' (hr1.symm.trans hr2)
  have hp_eq : p1' = p2' := by
    unfold uCyc at hu_same
    have hrot_same : (q2.take (K - 1)).rotate p1' = (q2.take (K - 1)).rotate p2' := by
      simpa [htake_eq] using hu_same
    have hlen2 : (q2.take (K - 1)).length = K - 1 := by simp [hq2.2]
    have h0 : ((q2.take (K - 1)).rotate p1')[0]'(by rw [List.length_rotate, hlen2]; omega) =
        ((q2.take (K - 1)).rotate p2')[0]'(by rw [List.length_rotate, hlen2]; omega) := by
      simp only [hrot_same]
    rw [List.getElem_rotate, List.getElem_rotate, Nat.zero_add, Nat.zero_add] at h0
    have hmod_eq := (List.Nodup.getElem_inj_iff hq2.1.take).mp h0
    rw [hlen2, Nat.mod_eq_of_lt hp1', Nat.mod_eq_of_lt hp2'] at hmod_eq
    exact hmod_eq
  rw [hL_eq, hp_eq] at hr1'
  exact hr1'.trans (undirReach_symm hr2')

/-! ### 5. Sublemma E: Strong induction on `trailingTrues` + `layerBag_weaklyConnected` -/

/-- Number of trailing `true`s in a Boolean mask list. -/
def trailingTrues (mask : List Bool) : Nat :=
  (mask.reverse.takeWhile (· == true)).length

theorem trailingTrues_le_count (mask : List Bool) :
    trailingTrues mask ≤ mask.count true := by
  unfold trailingTrues
  have hsub : ∀ l : List Bool, (l.takeWhile (· == true)).length ≤ l.count true := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      cases a with
      | false => simp
      | true =>
        simp only [List.takeWhile_cons, beq_self_eq_true, ↓reduceIte, List.length_cons, List.count_cons_self]
        omega
  exact (hsub mask.reverse).trans (by rw [List.count_reverse])

/-- **Main Connectivity Theorem (`layerBag_weaklyConnected`):**
Every Layer-`j` bag `layerBag m hm r hr K hK hj σ` (`j < r`, `σ ∈ allLayerSigmas j`) is
non-empty and `WeaklyConnected`! -/
theorem layerBag_nonempty_and_weaklyConnected (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) {j : Nat} (hj : j < r)
    {σ : List (Fin K)} (hσ : σ ∈ allLayerSigmas m hm r hr K hK j) :
    layerBag m hm r hr K hK hj σ ≠ [] ∧
    WeaklyConnected (layerBag m hm r hr K hK hj σ) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  have hK4 : 4 ≤ K := by omega
  have hjb : (j + 1) * (6 * m) ≤ K := by
    have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
  have hσ_Mj := (List.mem_filter.mp hσ).1
  obtain ⟨hσ_nd, hσ_len, hσ_nb⟩ := (mem_allLinearPermsMj_iff hjb σ).mp hσ_Mj
  -- Canonical anchor: `w_* = σ ++ bPref`, `q_* = w_* ++ [emb_j(b - 2), emb_j(b - 1)]`, `anchorV = symZ K :: w_*.map embK`!
  set wStar := σ ++ bPref (6 * m) K j hjb
  have hwStar_mem : wStar ∈ interleavings σ (bPref (6 * m) K j hjb) := by
    rw [mem_interleavings_iff (notInBlock (6 * m) j) σ (bPref (6 * m) K j hjb) hσ_nb (bPref_inBlock _ _ _ _)]
    have h1 : wStar.filter (notInBlock (6 * m) j) = σ := by
      dsimp only [wStar]; rw [List.filter_append,
        List.filter_eq_self.mpr hσ_nb,
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [bPref_inBlock (6 * m) K j hjb x hx]),
        List.append_nil]
    have h2 : wStar.filter (fun x => !(notInBlock (6 * m) j x)) = bPref (6 * m) K j hjb := by
      dsimp only [wStar]; rw [List.filter_append,
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [hσ_nb x hx]),
        List.nil_append,
        List.filter_eq_self.mpr (fun x hx => by simp [bPref_inBlock (6 * m) K j hjb x hx])]
    exact ⟨h1, h2⟩
  set qStar := wStar ++ [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩,
                         embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩]
  have hstar_hit := zCycle_hits_x0 m hm r hr K hK hj hσ hjb hwStar_mem
  set anchorV := sliceStartV m hm r hr K hK (canonLoop qStar, SliceTag.ins 0)
  have hB_ne : layerBag m hm r hr K hK hj σ ≠ [] := by
    intro hnil
    have hmem : edgeOfRowTag ((iterW6mLift m hm r hr K hK).row (canonLoop qStar)).1
        ((iterW6mLift m hm r hr K hK).row (canonLoop qStar)).2 (.ins 0) ∈
        layerBag m hm r hr K hK hj σ := by
      unfold layerBag; apply List.mem_append_right
      exact List.mem_map.mpr ⟨(canonLoop qStar, .ins 0), hstar_hit.1, rfl⟩
    rw [hnil] at hmem; cases hmem
  refine ⟨hB_ne, ?_⟩
  -- Core induction (Sublemma E): every `x_0`-slice reaches `anchorV` by induction on `(6*m - 1) - trailingTrues`!
  have hreach_x0 : ∀ (gap : Nat) (L : List (Fin K)) (p : Nat),
      (L, SliceTag.ins p) ∈ layerSlices m hm r hr K hK j σ →
      ((iterW6mLift m hm r hr K hK).row L).2 = .F →
      projBlock (6 * m) j ((iterW6mLift m hm r hr K hK).row L).1 = W6mState m hm 0 0 →
      (6 * m - 1) - trailingTrues ((uCyc ((iterW6mLift m hm r hr K hK).row L).1 p).map (inBlock (6 * m) j)) = gap →
      Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
        (sliceStartV m hm r hr K hK (L, SliceTag.ins p)) anchorV := by
    intro gap
    induction gap with
    | zero =>
      intro L p hs hF hproj hgap
      -- Use Sublemma C to reach `d_target = 0` (so `projBlock b j u = [0, 1, ..., b - 2]`) with the SAME mask!
      obtain ⟨L1, p1, hs1, hp1, hF1, hproj1, hmask1, hb1, hr1⟩ :=
        reach_any_bSeq_rot m hm r hr K hK hj hs hF hproj 0
      rw [← hmask1] at hgap
      rw [List.rotate_zero] at hb1
      set q1 := ((iterW6mLift m hm r hr K hK).row L1).1
      set u1 := uCyc q1 p1
      have hL1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).1
      have hact1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).2.1
      have hsig1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).2.2.2
      have hq1 := ((iterW6mLift m hm r hr K hK).row_perm L1 hL1).1
      have hlast1 := (layer_F_step_info m hm r hr K hK hL1 hact1 hF1).1
      -- Since `trailingTrues (u1.map (inBlock b j)) ≥ 6*m - 1` and `count true = 6*m - 1`,
      -- ALL `6*m - 1` `true`s sit at the end of `u1` -> `u1 = uCyc qStar 0`!
      have hcnt1 : (u1.map (inBlock (6 * m) j)).count true = 6 * m - 1 := by
        have h1 : (u1.map (inBlock (6 * m) j)).count true = (u1.filter (inBlock (6 * m) j)).length := by
          clear hgap hmask1 hb1 hr1 hsig1 hlast1
          induction u1 with
          | nil => rfl
          | cons x xs ih =>
            simp only [List.map_cons, List.count_cons, List.filter_cons]
            cases inBlock (6 * m) j x <;> simp [ih]
        rw [h1, filter_inBlock_eq_map_projBlock hjb, List.length_map, hb1, List.length_take,
          (W6mState_isPerm m hm 0 0).2]; omega
      have htr_eq : trailingTrues (u1.map (inBlock (6 * m) j)) = 6 * m - 1 := by
        have hle := trailingTrues_le_count (u1.map (inBlock (6 * m) j))
        rw [hcnt1] at hle; omega
      have hu1_len : u1.length = K - 1 := uCyc_length hq1.2 p1
      -- Split `u1 = u1.take (K - 6*m) ++ u1.drop (K - 6*m)`:
      -- Every element of `u1.drop (K - 6*m)` has `inBlock = true`, and every element of `u1.take (K - 6*m)` has `inBlock = false`!
      have hdrop_true : ∀ x ∈ u1.drop (K - 6 * m), inBlock (6 * m) j x = true := by
        intro x hx
        have hmem_rev : inBlock (6 * m) j x ∈ ((u1.map (inBlock (6 * m) j)).reverse.take (6 * m - 1)) := by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          rw [List.length_drop, hu1_len] at hi
          rw [List.getElem_drop]
          have hrev_idx : (K - 1) - 1 - (K - 6 * m + i) < 6 * m - 1 := by omega
          have hmem_t : ((u1.map (inBlock (6 * m) j)).reverse.take (6 * m - 1))[(K - 1) - 1 - (K - 6 * m + i)]'(by simp [hu1_len]; omega) ∈
              (u1.map (inBlock (6 * m) j)).reverse.take (6 * m - 1) := List.getElem_mem _
          rw [List.getElem_take, List.getElem_reverse, List.getElem_map] at hmem_t
          have hidx_eq : (u1.map (inBlock (6 * m) j)).length - 1 - ((K - 1) - 1 - (K - 6 * m + i)) = K - 6 * m + i := by
            rw [List.length_map, hu1_len]; omega
          have hidx_eq2 : u1.length - 1 - ((K - 1) - 1 - (K - 6 * m + i)) = K - 6 * m + i := by
            rw [hu1_len]; omega
          simpa [hidx_eq2] using hmem_t
        have htw_eq : (u1.map (inBlock (6 * m) j)).reverse.take (6 * m - 1) =
            (u1.map (inBlock (6 * m) j)).reverse.takeWhile (· == true) := by
          have hpf : (u1.map (inBlock (6 * m) j)).reverse.takeWhile (· == true) <+:
              (u1.map (inBlock (6 * m) j)).reverse := List.takeWhile_prefix _
          obtain ⟨rest, hrest⟩ := hpf
          have hlen_tw : ((u1.map (inBlock (6 * m) j)).reverse.takeWhile (· == true)).length = 6 * m - 1 := htr_eq
          conv_lhs => rw [← hrest, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        rw [htw_eq] at hmem_rev
        have hmem_tw : ∀ (l : List Bool) (b : Bool), b ∈ l.takeWhile (· == true) → b = true := by
          intro l b hb
          induction l with
          | nil => simp at hb
          | cons a as ihl =>
            cases a with
            | false => simp at hb
            | true =>
              simp only [List.takeWhile_cons, beq_self_eq_true, ↓reduceIte, List.mem_cons] at hb
              rcases hb with rfl | hb'
              · rfl
              · exact ihl hb'
        exact hmem_tw _ _ hmem_rev
      have htake_false : ∀ x ∈ u1.take (K - 6 * m), inBlock (6 * m) j x = false := by
        intro x hx
        by_contra hne
        have hxt : inBlock (6 * m) j x = true := by cases h : inBlock (6 * m) j x <;> simp_all
        have h1 : (u1.take (K - 6 * m)).filter (inBlock (6 * m) j) ≠ [] :=
          List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx, hxt⟩)
        have hpos : 0 < ((u1.take (K - 6 * m)).filter (inBlock (6 * m) j)).length :=
          List.length_pos_of_ne_nil h1
        have hdrop_len : ((u1.drop (K - 6 * m)).filter (inBlock (6 * m) j)).length = 6 * m - 1 := by
          rw [List.filter_eq_self.mpr hdrop_true, List.length_drop, hu1_len]; omega
        have htot : (u1.filter (inBlock (6 * m) j)).length = 6 * m - 1 := by
          rw [filter_inBlock_eq_map_projBlock hjb, List.length_map, hb1, List.length_take,
            (W6mState_isPerm m hm 0 0).2]; omega
        have hsp : u1 = u1.take (K - 6 * m) ++ u1.drop (K - 6 * m) := (List.take_append_drop _ _).symm
        have hsum : ((u1.take (K - 6 * m)).filter (inBlock (6 * m) j)).length +
            ((u1.drop (K - 6 * m)).filter (inBlock (6 * m) j)).length = 6 * m - 1 := by
          rw [← List.length_append, ← List.filter_append, ← hsp]; exact htot
        omega
      have hu1_take_eq : u1.take (K - 6 * m) = σ := by
        have hfilt : u1.filter (notInBlock (6 * m) j) = σ := by
          rw [uCyc_filter_notInBlock hK4 hq1.2 hlast1 (by omega)]; exact hsig1
        rw [← hfilt]
        conv_rhs => rw [← List.take_append_drop (K - 6 * m) u1]
        rw [List.filter_append,
          List.filter_eq_self.mpr (fun x hx => by unfold notInBlock; rw [htake_false x hx]; rfl),
          List.filter_eq_nil_iff.mpr (fun x hx => by unfold notInBlock; rw [hdrop_true x hx]; simp),
          List.append_nil]
      have hu1_drop_eq : u1.drop (K - 6 * m) =
          bPref (6 * m) K j hjb ++ [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩] := by
        have hfilt : u1.filter (inBlock (6 * m) j) = u1.drop (K - 6 * m) := by
          conv_lhs => rw [← List.take_append_drop (K - 6 * m) u1]
          rw [List.filter_append,
            List.filter_eq_nil_iff.mpr (fun x hx => by simp [htake_false x hx]),
            List.nil_append, List.filter_eq_self.mpr hdrop_true]
        rw [← hfilt, filter_inBlock_eq_map_projBlock hjb, hb1, W6mState_zero_zero]
        refine List.ext_getElem (by simp [bPref]; omega) fun i hi1 hi2 => ?_
        rw [List.getElem_map, List.getElem_take, List.getElem_finRange]
        by_cases h1 : i < 6 * m - 2
        · rw [List.getElem_append_left (by simp [bPref]; omega)]; simp [bPref]
        · rw [List.getElem_append_right (by simp [bPref]; omega)]
          have hi_eq : i = 6 * m - 2 := by simp at hi1; omega
          subst hi_eq; simp [bPref_length]
      have hu1_eq_star : u1 = uCyc qStar 0 := by
        have htk_star : qStar.take (K - 1) = σ ++ bPref (6 * m) K j hjb ++
            [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩] := by
          have h1 : qStar = (σ ++ bPref (6 * m) K j hjb ++
              [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩]) ++
              [embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩] := by
            simp [qStar, wStar, List.append_assoc]
          have hlen1 : (σ ++ bPref (6 * m) K j hjb ++
              [embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩]).length = K - 1 := by
            simp [hσ_len, bPref_length]; omega
          rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        rw [← List.take_append_drop (K - 6 * m) u1, hu1_take_eq, hu1_drop_eq]
        unfold uCyc; rw [List.rotate_zero, htk_star, List.append_assoc]
      have hsame := same_uCyc_connected m hm r hr K hK hj hs1 hstar_hit.1 hF1
        (by rw [hstar_hit.2.2]) hproj1
        (by rw [hstar_hit.2.2, W6mState_zero_zero]; exact projBlock_of_interleaving_append (by omega) hjb hσ_Mj hwStar_mem)
        (by rw [hstar_hit.2.2]; exact hu1_eq_star)
      exact hr1.trans hsame
    | succ gap' ih =>
      intro L p hs hF hproj hgap
      -- Use Sublemma C to reach `d_target = 6 * m - 2` (so `projBlock b j u = [b - 2, 0, 1, ..., b - 3]`) with the SAME mask!
      obtain ⟨L1, p1, hs1, hp1, hF1, hproj1, hmask1, hb1, hr1⟩ :=
        reach_any_bSeq_rot m hm r hr K hK hj hs hF hproj (6 * m - 2)
      rw [← hmask1] at hgap
      set q1 := ((iterW6mLift m hm r hr K hK).row L1).1
      set u1 := uCyc q1 p1
      have hL1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).1
      have hact1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).2.1
      have hsig1 := ((mem_layerSlices_iff m hm r hr K hK j σ _).mp hs1).2.2.2
      have hq1 := ((iterW6mLift m hm r hr K hK).row_perm L1 hL1).1
      have hlast1 := (layer_F_step_info m hm r hr K hK hL1 hact1 hF1).1
      have hu1_len : u1.length = K - 1 := uCyc_length hq1.2 p1
      have hu1_nd : u1.Nodup := uCyc_nodup hq1.1 p1
      set bm2 := embBlock (6 * m) K j hjb ⟨6 * m - 2, by omega⟩
      set bm1 := embBlock (6 * m) K j hjb ⟨6 * m - 1, by omega⟩
      -- Identify `hb1 : projBlock b j u1 = ⟨6*m - 2⟩ :: (0 .. 6*m - 3)`!
      have hb1_cons : projBlock (6 * m) j u1 =
          ⟨6 * m - 2, by omega⟩ :: (List.finRange (6 * m - 2)).map (fun i => ⟨i.1, by omega⟩) := by
        rw [hb1, W6mState_zero_zero]
        have htk : (List.finRange (6 * m)).take (6 * m - 1) =
            (List.finRange (6 * m - 2)).map (fun i => ⟨i.1, by omega⟩) ++ [⟨6 * m - 2, by omega⟩] := by
          refine List.ext_getElem (by simp; omega) fun i hi1 hi2 => ?_
          rw [List.getElem_take, List.getElem_finRange]
          by_cases h1 : i < 6 * m - 2
          · rw [List.getElem_append_left (by simp; omega)]; simp
          · rw [List.getElem_append_right (by simp; omega)]
            have hi_eq : i = 6 * m - 2 := by simp at hi1; omega
            subst hi_eq; simp
        rw [htk]
        have hrot := List.rotate_append_length_eq
          ((List.finRange (6 * m - 2)).map (fun i : Fin (6 * m - 2) => (⟨i.1, by omega⟩ : Fin (6 * m))))
          [(⟨6 * m - 2, by omega⟩ : Fin (6 * m))]
        simp only [List.length_map, List.length_finRange] at hrot
        rw [hrot]; rfl
      -- Split `u1 = preM ++ [bm2] ++ rest` at `k = u1.idxOf bm2`!
      have hbm2_mem : bm2 ∈ u1 := by
        have hmem_f : bm2 ∈ u1.filter (inBlock (6 * m) j) := by
          rw [filter_inBlock_eq_map_projBlock hjb, hb1_cons]; simp [bm2]
        exact (List.mem_filter.mp hmem_f).1
      let k := u1.idxOf bm2
      have hk_lt : k < K - 1 := by have := List.idxOf_lt_length_of_mem hbm2_mem; omega
      let preM := u1.take k
      let rest := u1.drop (k + 1)
      have hu1_split : u1 = preM ++ [bm2] ++ rest := by
        have h1 := (List.take_append_drop k u1).symm
        have hdrop : u1.drop k = bm2 :: rest := by
          rw [List.drop_eq_getElem_cons (by omega)]; congr 1; exact List.getElem_idxOf _
        rw [hdrop] at h1; simpa [preM, List.append_assoc] using h1
      have hpreM_len : preM.length = k := by simp [preM, hu1_len]; omega
      have hrest_len : rest.length = K - 2 - k := by simp [rest, hu1_len]; omega
      -- Every element of `preM` is NOT in `B_j` (otherwise `projBlock b j u1` wouldn't start with `6*m - 2`!)
      have hpreM_nb : ∀ x ∈ preM, notInBlock (6 * m) j x = true := by
        intro x hx
        by_contra hne
        have hxin : inBlock (6 * m) j x = true := by unfold notInBlock at hne; cases h : inBlock (6 * m) j x <;> simp_all
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((inBlock_iff_projBlockElem_isSome _ _ _).mp hxin)
        have hpre_ne : projBlock (6 * m) j preM ≠ [] :=
          List.ne_nil_of_mem (List.mem_filterMap.mpr ⟨x, hx, ha⟩)
        have hproj_sp : projBlock (6 * m) j u1 =
            projBlock (6 * m) j preM ++ [⟨6 * m - 2, by omega⟩] ++ projBlock (6 * m) j rest := by
          unfold projBlock; rw [hu1_split]
          simp [List.filterMap_append, List.filterMap_cons, bm2, projBlockElem_embBlock, List.append_assoc]
        rw [hb1_cons] at hproj_sp
        cases hpm : projBlock (6 * m) j preM with
        | nil => exact hpre_ne hpm
        | cons a0 as =>
          rw [hpm, List.cons_append, List.cons_append] at hproj_sp
          have ha0 : a0 = ⟨6 * m - 2, by omega⟩ := (List.cons.inj hproj_sp).1.symm
          have hmem_a0 : a0 ∈ projBlock (6 * m) j preM := by rw [hpm]; simp
          obtain ⟨y, hy_pre, hy_proj⟩ := List.mem_filterMap.mp hmem_a0
          have hy_eq : y = bm2 := (projBlockElem_eq_some_iff (6 * m) j hjb y a0).mp hy_proj |>.trans (by rw [ha0])
          -- `bm2 ∈ preM` contradicts `u1.Nodup`!
          rw [hu1_split, List.append_assoc, List.nodup_append] at hu1_nd
          exact hu1_nd.2.2 bm2 (hy_eq ▸ hy_pre) bm2 (by simp) rfl
      have hpreM_inF : ∀ x ∈ preM, inBlock (6 * m) j x = false := fun x hx => by
        have h := hpreM_nb x hx; unfold notInBlock at h; simp at h; exact h
      -- `projBlock b j rest = (List.finRange (6*m - 2)).map ...`, hence `rest.filter (inBlock b j) = bPref`!
      have hrest_proj : projBlock (6 * m) j rest = (List.finRange (6 * m - 2)).map (fun i => ⟨i.1, by omega⟩) := by
        have hproj_sp : projBlock (6 * m) j u1 =
            projBlock (6 * m) j preM ++ [⟨6 * m - 2, by omega⟩] ++ projBlock (6 * m) j rest := by
          unfold projBlock; rw [hu1_split]
          simp [List.filterMap_append, List.filterMap_cons, bm2, projBlockElem_embBlock, List.append_assoc]
        have hpm_nil : projBlock (6 * m) j preM = [] :=
          List.filterMap_eq_nil_iff.mpr fun x hx => (notInBlock_iff_projBlockElem_eq_none _ _ _).mp (hpreM_nb x hx)
        rw [hb1_cons, hpm_nil, List.nil_append, List.singleton_append] at hproj_sp
        exact (List.cons.inj hproj_sp).2.symm
      -- Build `w := preM ++ rest ∈ interleavings σ (bPref (6 * m) K j hjb)`!
      set w := preM ++ rest
      have hw_mem : w ∈ interleavings σ (bPref (6 * m) K j hjb) := by
        rw [mem_interleavings_iff (notInBlock (6 * m) j) σ (bPref (6 * m) K j hjb) hσ_nb (bPref_inBlock _ _ _ _)]
        have hnb_bm2 : notInBlock (6 * m) j bm2 = false := by unfold notInBlock; rw [inBlock_embBlock]; rfl
        have h1 : w.filter (notInBlock (6 * m) j) = σ := by
          have hfilt : u1.filter (notInBlock (6 * m) j) = σ := by
            rw [uCyc_filter_notInBlock hK4 hq1.2 hlast1 (by omega)]; exact hsig1
          rw [← hfilt, hu1_split]
          simp [w, List.filter_append, List.filter_cons, hnb_bm2]
        have h2 : w.filter (fun x => !(notInBlock (6 * m) j x)) = bPref (6 * m) K j hjb := by
          have hin_eq : (fun x : Fin K => !(notInBlock (6 * m) j x)) = inBlock (6 * m) j := by
            funext x; unfold notInBlock; simp
          rw [hin_eq]
          dsimp only [w]
          rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun x hx => by simp [hpreM_inF x hx]),
            List.nil_append, filter_inBlock_eq_map_projBlock hjb, hrest_proj, bPref, List.map_map]
          rfl
        exact ⟨h1, h2⟩
      -- Construct `qA = w ++ [bm2, bm1]` (Cut A: `portA = 0`) and `qB = rest ++ preM ++ [bm2, bm1]` (Cut B: `portB = K - 2 - k`)!
      set ck := symZ K :: w.map embK
      have hck_mem : ck ∈ zCyclesOf (6 * m) K j hjb σ := List.mem_map.mpr ⟨w, hw_mem, rfl⟩
      have hck_len : ck.length = K - 1 := zCyclesOf_elem_length (by omega) hjb hσ_len hck_mem
      set qA := w ++ [bm2, bm1]
      have hA_hit := zCycle_hits_x0 m hm r hr K hK hj hσ hjb hw_mem
      set qB := rest ++ preM ++ [bm2, bm1]
      have hqB_perm : IsPerm K qB := by
        have hqA_perm : IsPerm K qA := isPerm_of_interleaving_append (by omega) hjb hσ_Mj hw_mem
        have hp : qB.Perm qA := by
          dsimp only [qB, qA, w]
          exact (List.perm_append_comm (l₁ := rest) (l₂ := preM)).append_right [bm2, bm1]
        exact ⟨hp.nodup_iff.mpr hqA_perm.1, hp.length_eq.trans hqA_perm.2⟩
      have hqB_proj : projBlock (6 * m) j qB = W6mState m hm 0 0 := by
        have hpm_nil : projBlock (6 * m) j preM = [] :=
          List.filterMap_eq_nil_iff.mpr fun x hx => (notInBlock_iff_projBlockElem_eq_none _ _ _).mp (hpreM_nb x hx)
        have hqA_proj := projBlock_of_interleaving_append (by omega) hjb hσ_Mj hw_mem
        rw [W6mState_zero_zero, ← hqA_proj]
        unfold projBlock at hpm_nil ⊢
        dsimp only [qB, qA, w]
        simp [List.filterMap_append, hpm_nil]; rfl
      have hqB_last : qB[K - 1]'(by rw [hqB_perm.2]; omega) =
          embBlock (6 * m) K j hjb ((W6mState m hm 0 0)[6 * m - 1]'(by rw [(W6mState_isPerm m hm 0 0).2]; omega)) := by
        have hlen_rp : (rest ++ preM).length = K - 2 := by simp [hrest_len, hpreM_len]; omega
        have h1 : qB[K - 1]'(by rw [hqB_perm.2]; omega) = bm1 := by
          dsimp only [qB]; rw [List.getElem_append_right (by omega)]
          simp [hlen_rp, show K - 1 - (K - 2) = 1 by omega]
        have h2 : (W6mState m hm 0 0)[6 * m - 1]'(by rw [(W6mState_isPerm m hm 0 0).2]; omega) = ⟨6 * m - 1, by omega⟩ := by
          simp only [W6mState_zero_zero, List.getElem_finRange, Fin.cast_mk]
        rw [h1, h2]
      have huCyc_qB : uCyc qB (K - 2 - k) = u1 := by
        have htkB : qB.take (K - 1) = rest ++ (preM ++ [bm2]) := by
          have h1 : qB = (rest ++ (preM ++ [bm2])) ++ [bm1] := by dsimp only [qB]; simp [List.append_assoc]
          have hlen1 : (rest ++ (preM ++ [bm2])).length = K - 1 := by simp [hrest_len, hpreM_len]; omega
          rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        unfold uCyc; rw [htkB]
        have hrot := List.rotate_append_length_eq rest (preM ++ [bm2])
        rw [hrest_len] at hrot; rw [hrot, hu1_split]
      have hqB_sig : (qB.rotate (K - 2 - k)).filter (notInBlock (6 * m) j) = σ := by
        have hlastB : inBlock (6 * m) j (qB[K - 1]'(by rw [hqB_perm.2]; omega)) = true := by
          rw [hqB_last]; exact inBlock_embBlock _ _ _ _ _
        have h1 := uCyc_filter_notInBlock hK4 hqB_perm.2 hlastB (by omega : K - 2 - k < K)
        dsimp only [tagSigma] at h1
        rw [← h1, huCyc_qB, uCyc_filter_notInBlock hK4 hq1.2 hlast1 (by omega)]; exact hsig1
      obtain ⟨hactB, hrowB⟩ := layerRow_of_W6m_F m hm r hr K hK hj hσ hqB_perm
        (by omega) (by omega) hjb hqB_proj hqB_last ⟨K - 2 - k, hqB_sig⟩
      have hsB : (canonLoop qB, SliceTag.ins (K - 2 - k)) ∈ layerSlices m hm r hr K hK j σ := by
        refine (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨canonLoop_isCanonLoop hqB_perm, hactB, ?_, ?_⟩
        · rw [hrowB]; exact List.mem_map.mpr ⟨K - 2 - k, List.mem_range.mpr (by omega), rfl⟩
        · rw [hrowB]; exact hqB_sig
      -- Step 1: `(L1, p1)` connects to `(canonLoop qB, K - 2 - k)` by Sublemma D!
      have hr_1B := same_uCyc_connected m hm r hr K hK hj hs1 hsB hF1 (by rw [hrowB]) hproj1
        (by rw [hrowB]; exact hqB_proj) (by rw [hrowB, huCyc_qB])
      -- Step 2: `(canonLoop qB, K - 2 - k)` has start vertex `ck.rotate (k + 1)`, connected via `connCycleEdges ck` to `ck = startV (canonLoop qA, 0)`!
      have hstartB : sliceStartV m hm r hr K hK (canonLoop qB, SliceTag.ins (K - 2 - k)) = ck.rotate (k + 1) := by
        unfold sliceStartV edgeOfRowTag; rw [hrowB]; dsimp only
        rw [insSlice_u hK4 hqB_perm.2 (by omega) (K - 2 - k)]
        unfold insBase
        have htk1 : qB.take (K - 2 - k) = rest := by
          have h1 : qB = rest ++ (preM ++ [bm2, bm1]) := by dsimp only [qB]; simp [List.append_assoc]
          rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        have hdp1 : qB.drop (K - 2 - k) = preM ++ [bm2, bm1] := by
          have h1 : qB = rest ++ (preM ++ [bm2, bm1]) := by dsimp only [qB]; simp [List.append_assoc]
          rw [h1, List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]
        rw [htk1, hdp1]
        have htake_full : (rest.map embK ++ [symZ K] ++ (preM ++ [bm2, bm1]).map embK).take (K - 1) =
            rest.map embK ++ [symZ K] ++ preM.map embK := by
          have h1 : rest.map embK ++ [symZ K] ++ (preM ++ [bm2, bm1]).map embK =
              (rest.map embK ++ [symZ K] ++ preM.map embK) ++ [embK bm2, embK bm1] := by
            simp [List.map_append, List.append_assoc]
          have hlen1 : (rest.map embK ++ [symZ K] ++ preM.map embK).length = K - 1 := by
            simp [hrest_len, hpreM_len]; omega
          rw [h1, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        rw [htake_full]
        have hck_sp : ck = (symZ K :: preM.map embK) ++ rest.map embK := by
          dsimp only [ck, w]; simp [List.map_append, List.cons_append]
        have hlen_sp : (symZ K :: preM.map embK).length = k + 1 := by simp [hpreM_len]
        have hrot := List.rotate_append_length_eq (symZ K :: preM.map embK) (rest.map embK)
        rw [hlen_sp] at hrot
        rw [hck_sp, hrot]; simp [List.append_assoc]
      have hr_BA : Relation.ReflTransGen (UndirAdj (layerBag m hm r hr K hK hj σ))
          (sliceStartV m hm r hr K hK (canonLoop qB, SliceTag.ins (K - 2 - k)))
          (sliceStartV m hm r hr K hK (canonLoop qA, SliceTag.ins 0)) := by
        rw [hstartB, hA_hit.2.1]
        have hck_pos : 0 < ck.length := by rw [hck_len]; omega
        have hcirc := connCycleEdges_isCircuit hck_pos
        have hsub : ∀ e ∈ connCycleEdges ck, e ∈ layerBag m hm r hr K hK hj σ := fun e he =>
          List.mem_append_left _ (List.mem_flatMap.mpr ⟨ck, hck_mem, he⟩)
        have hhit := connCycleEdges_mem_rot ((k + 1) % (K - 1)) (by rw [hck_len]; exact Nat.mod_lt _ (by omega))
        have hmod_r : ck.rotate ((k + 1) % (K - 1)) = ck.rotate (k + 1) := by rw [← hck_len, List.rotate_mod]
        rw [hmod_r] at hhit
        obtain ⟨ec, hec_mem, hec_u⟩ := hhit
        have hreach_ec := circuit_edges_undirReach hsub hcirc ec hec_mem
        rwa [hec_u] at hreach_ec
      -- Step 3: Show `trailingTrues (uCyc qA 0) = trailingTrues u1 + 1` -> apply `ih`!
      have hrest_has_false : ∃ x ∈ rest, inBlock (6 * m) j x = false := by
        by_contra hall
        push_neg at hall
        have hrest_true : ∀ x ∈ rest, inBlock (6 * m) j x = true := fun x hx => by
          cases h : inBlock (6 * m) j x with
          | true => rfl
          | false => exact absurd h (hall x hx)
        -- Then `rest` has length `6*m - 2` (all `true`), so `[bm2] ++ rest` is `6*m - 1` trailing `true`s of `u1`!
        have hlen_r : rest.length = 6 * m - 2 := by
          have h1 := List.filter_eq_self.mpr hrest_true
          have h2 : (rest.filter (inBlock (6 * m) j)).length = 6 * m - 2 := by
            rw [filter_inBlock_eq_map_projBlock hjb, hrest_proj]; simp
          rw [h1] at h2; exact h2
        have hrev_u1 : (u1.map (inBlock (6 * m) j)).reverse =
            List.replicate (6 * m - 1) true ++ (preM.map (inBlock (6 * m) j)).reverse := by
          have hrm : rest.map (inBlock (6 * m) j) = List.replicate (6 * m - 2) true := by
            refine List.ext_getElem (by simp [hlen_r]) fun i hi1 hi2 => ?_
            rw [List.getElem_map, List.getElem_replicate]; exact hrest_true _ (List.getElem_mem _)
          rw [hu1_split, List.map_append, List.map_append, hrm, List.map_singleton,
            inBlock_embBlock, List.reverse_append, List.reverse_append, List.reverse_replicate,
            List.reverse_singleton]
          rw [← List.append_assoc]
          congr 1
          rw [← List.replicate_succ', show 6 * m - 2 + 1 = 6 * m - 1 by omega]
        have htw_ge : 6 * m - 1 ≤ trailingTrues (u1.map (inBlock (6 * m) j)) := by
          unfold trailingTrues; rw [hrev_u1]
          have hrep : ∀ (n : Nat) (l : List Bool), n ≤ ((List.replicate n true ++ l).takeWhile (· == true)).length := by
            intro n l; induction n with
            | zero => simp
            | succ n ihn => simp [List.replicate_succ, ihn]
          exact hrep (6 * m - 1) _
        omega
      have htw_app_false : ∀ (l1 l2 : List Bool), (∃ b ∈ l1, b = false) →
          (l1 ++ l2).takeWhile (· == true) = l1.takeWhile (· == true) := by
        intro l1 l2 hhas
        induction l1 with
        | nil => obtain ⟨b, hb, _⟩ := hhas; cases hb
        | cons a as iha =>
          cases a with
          | false => simp
          | true =>
            simp only [List.cons_append, List.takeWhile_cons, beq_self_eq_true, ↓reduceIte,
              List.cons.injEq, true_and]
            apply iha
            obtain ⟨b, hb, hbf⟩ := hhas
            rcases List.mem_cons.mp hb with rfl | hb'
            · cases hbf
            · exact ⟨b, hb', hbf⟩
      have htr_u1 : trailingTrues (u1.map (inBlock (6 * m) j)) =
          ((rest.map (inBlock (6 * m) j)).reverse.takeWhile (· == true)).length := by
        unfold trailingTrues
        rw [hu1_split, List.map_append, List.map_append, List.reverse_append, List.reverse_append]
        have hhas_rev : ∃ b ∈ (rest.map (inBlock (6 * m) j)).reverse, b = false := by
          obtain ⟨x, hx, hxf⟩ := hrest_has_false
          exact ⟨false, List.mem_reverse.mpr (List.mem_map.mpr ⟨x, hx, hxf⟩), rfl⟩
        rw [htw_app_false _ _ hhas_rev]
      have huA_eq : uCyc qA 0 = preM ++ rest ++ [bm2] := by
        have h1 : qA = (preM ++ rest ++ [bm2]) ++ [bm1] := by dsimp only [qA, w]; simp [List.append_assoc]
        have hlen1 : (preM ++ rest ++ [bm2]).length = K - 1 := by simp [hpreM_len, hrest_len]; omega
        unfold uCyc; rw [List.rotate_zero, h1, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
      have htr_uA : trailingTrues ((uCyc qA 0).map (inBlock (6 * m) j)) =
          trailingTrues (u1.map (inBlock (6 * m) j)) + 1 := by
        conv_lhs => unfold trailingTrues
        rw [huA_eq, List.map_append, List.map_append, List.map_singleton, inBlock_embBlock,
          List.reverse_append, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.takeWhile_cons]
        simp only [beq_self_eq_true, ↓reduceIte, List.length_cons]
        have hhas_rev : ∃ b ∈ (rest.map (inBlock (6 * m) j)).reverse, b = false := by
          obtain ⟨x, hx, hxf⟩ := hrest_has_false
          exact ⟨false, List.mem_reverse.mpr (List.mem_map.mpr ⟨x, hx, hxf⟩), rfl⟩
        rw [htw_app_false _ _ hhas_rev, htr_u1]
      have hgapA : (6 * m - 1) - trailingTrues ((uCyc ((iterW6mLift m hm r hr K hK).row (canonLoop qA)).1 0).map (inBlock (6 * m) j)) = gap' := by
        rw [hA_hit.2.2, htr_uA]; omega
      have hr_Astar := ih (canonLoop qA) 0 hA_hit.1 (by rw [hA_hit.2.2])
        (by rw [hA_hit.2.2, W6mState_zero_zero]; exact projBlock_of_interleaving_append (by omega) hjb hσ_Mj hw_mem)
        hgapA
      exact hr1.trans (hr_1B.trans (hr_BA.trans hr_Astar))
  -- Combine Sublemmas A, B, E via `weaklyConnected_of_circuits_touching_hub`!
  apply weaklyConnected_of_circuits_touching_hub (hub := anchorV)
  intro e he
  unfold layerBag at he
  rw [List.mem_append] at he
  rcases he with hzc | hsl
  · -- Edge `e` is in `connCycleEdges ck` for some `ck ∈ zCyclesOf` -> reaches `ck = startV (canonLoop q, 0)` (Sublemma A) -> reaches `anchorV` (Sublemma E)!
    obtain ⟨ck, hck_mem, he_ck⟩ := List.mem_flatMap.mp hzc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hck_mem
    have hck_len : (symZ K :: w.map embK).length = K - 1 :=
      zCyclesOf_elem_length (by omega) hjb hσ_len hck_mem
    have hcirc := connCycleEdges_isCircuit (by rw [hck_len]; omega)
    have hsub : ∀ x ∈ connCycleEdges (symZ K :: w.map embK), x ∈ layerBag m hm r hr K hK hj σ :=
      fun x hx => List.mem_append_left _ (List.mem_flatMap.mpr ⟨symZ K :: w.map embK, hck_mem, hx⟩)
    have hr_ck := circuit_edges_undirReach hsub hcirc e he_ck
    have hhit := zCycle_hits_x0 m hm r hr K hK hj hσ hjb hw
    rw [← hhit.2.1] at hr_ck
    have hr_x0 := hreach_x0 _ _ 0 hhit.1 (by rw [hhit.2.2])
      (by rw [hhit.2.2, W6mState_zero_zero]; exact projBlock_of_interleaving_append (by omega) hjb hσ_Mj hw) rfl
    exact hr_ck.trans hr_x0
  · -- Edge `e` is a slice edge `s ∈ layerSlices j σ` -> reaches some `x_0`-slice (Sublemma B) -> reaches `anchorV` (Sublemma E)!
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsl
    obtain ⟨L', p', hs', _, hF', hproj', hrB⟩ := reach_x0_from_any m hm r hr K hK hj hs
    have hrE := hreach_x0 _ L' p' hs' hF' hproj' rfl
    exact hrB.trans hrE

/-! ### 6. Main Lemma 3 Theorem (`allLayerBags_theorem`): All `r` Layers Combined! -/

/-- **Main Lemma 3 Theorem (`allLayerBags_theorem`):**
Combines all layers `0 ≤ j < r` into a single list of valid Eulerian bags covering every
non-`'D'` loop of `iterW6mLift m hm r hr K hK`, with exact bag count and `z`-cycle cost bounds! -/
theorem allLayerBags_theorem (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) [NeZero K] (hK : r * (6 * m) + 1 ≤ K) :
    let b := 6 * m
    let F := Almanac.fact (b - 1)
    let Db := F - 4 * m * (b - 2)
    ∃ bags : List (List (RawEdge (K + 2))),
      bags.length ≤ r * Almanac.fact (K - b) ∧
      (∀ B ∈ bags, B ≠ [] ∧ (∀ e ∈ B, EdgeOk (K - 1) e) ∧ Balanced B ∧ WeaklyConnected B) ∧
      (∀ L ∈ allCanonLoops K, ((iterW6mLift m hm r hr K hK).row L).2 ≠ .D →
        ∀ e ∈ rowSlices ((iterW6mLift m hm r hr K hK).row L).1
          ((iterW6mLift m hm r hr K hK).row L).2, ∃ B ∈ bags, e ∈ B) ∧
      ∃ zTotal : Nat,
        zTotal * (4 * m * (b - 2)) ≤ (b - 1) * Almanac.fact (K - 2) ∧
        (bags.map (fun B => (B.map (fun e => e.body.length)).sum)).sum =
          (K - 1) * zTotal +
          (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 != .D)).map
            (fun L => ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
              ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  set b := 6 * m
  set F := Almanac.fact (b - 1)
  set Lb := 4 * m * (b - 2)
  set Db := F - Lb
  -- Build the list of all bags across layers `j ∈ List.finRange r`!
  let layerBagsOf (j : Fin r) : List (List (RawEdge (K + 2))) :=
    (allLayerSigmas m hm r hr K hK j.1).map (layerBag m hm r hr K hK j.2)
  let bags := (List.finRange r).flatMap layerBagsOf
  have hsum_flat : ∀ {α : Type} (l : List α) (f : α → List Nat),
      (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := fun l f => by
    induction l with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]
  have hfact_pos : ∀ n : Nat, 0 < Almanac.fact n := fun n => by
    induction n with
    | zero => exact Nat.zero_lt_one
    | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih
  refine ⟨bags, ?_, ?_, ?_, ?_⟩
  · -- 1. Bag count bound: each layer `j` has `|allLayerSigmas j| ≤ (K - b)!`, so total `≤ r * (K - b)!`!
    dsimp only [bags]
    rw [List.length_flatMap]
    have hle_each : ∀ j ∈ List.finRange r, (layerBagsOf j).length ≤ Almanac.fact (K - b) := by
      intro j _
      dsimp only [layerBagsOf]; rw [List.length_map]
      have hjb : (j.1 + 1) * b ≤ K := by
        have := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega); omega
      exact (List.length_filter_le _ _).trans (by rw [allLinearPermsMj_length hjb])
    have hsum_le : ∀ (l : List (Fin r)) (c : Nat), (∀ x ∈ l, (layerBagsOf x).length ≤ c) →
        (l.map (fun x => (layerBagsOf x).length)).sum ≤ l.length * c := by
      intro l c hl
      induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        have h1 := hl x List.mem_cons_self
        have h2 := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        omega
    simpa [List.length_finRange] using hsum_le (List.finRange r) (Almanac.fact (K - b)) hle_each
  · -- 2. Every bag is non-empty, `EdgeOk (K - 1)`, `Balanced`, and `WeaklyConnected`!
    intro B hB
    obtain ⟨j, _, hBj⟩ := List.mem_flatMap.mp hB
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hBj
    have ⟨hok, hbal⟩ := layerBag_ok_and_balanced m hm r hr K hK j.2 hσ
    have ⟨hne, hwc⟩ := layerBag_nonempty_and_weaklyConnected m hm r hr K hK j.2 hσ
    exact ⟨hne, hok, hbal, hwc⟩
  · -- 3. Coverage of every slice of every non-`'D'` loop `L`!
    intro L hL hneD e he
    have hL' := (mem_allCanonLoops_iff L).mp hL
    cases hact : activeLayer m hm r L with
    | none =>
      exfalso; apply hneD; change (iterW6mRow m hm r K hK L).2 = .D
      rw [iterW6mRow_eq_none hm hK hact]
    | some j =>
      obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
      rw [← map_edgeOfRowTag_eq_rowSlices hK4 _ hneD] at he
      obtain ⟨tag, htag, rfl⟩ := List.mem_map.mp he
      let σ := tagSigma b j K ((iterW6mLift m hm r hr K hK).row L).1 tag
      have hσ : σ ∈ allLayerSigmas m hm r hr K hK j :=
        tagSigma_mem_allLayerSigmas m hm r hr K hK hj_lt hL' hact tag
      refine ⟨layerBag m hm r hr K hK hj_lt σ, ?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨⟨j, hj_lt⟩, List.mem_finRange _, List.mem_map.mpr ⟨σ, hσ, rfl⟩⟩
      · unfold layerBag
        apply List.mem_append_right
        refine List.mem_map.mpr ⟨(L, tag), ?_, rfl⟩
        exact (mem_layerSlices_iff m hm r hr K hK j σ _).mpr ⟨hL', hact, htag, rfl⟩
  · -- 4. Total `z`-cycle count `zTotal` and exact body-sum identity!
    let zTotal := ((List.finRange r).map fun j : Fin r =>
      (allLayerSigmas m hm r hr K hK j.1).length * Nat.choose (K - 2) (b - 2)).sum
    refine ⟨zTotal, ?_, ?_⟩
    · -- Bound `zTotal * Lb ≤ (b - 1) * (K - 2)!`!
      -- Step 4a: First show `∀ j < r, F^j * (|allLayerSigmas j| * C(K-2, b-2)) * (b - 2)! = Db^j * (K - 2)!`!
      have hfact_eq : ∀ n : Nat, Nat.factorial n = Almanac.fact n := fun n => by
        induction n with
        | zero => rfl
        | succ k ih => simp [Nat.factorial, Almanac.fact, ih]
      have hchoose_mul : Almanac.fact (K - b) * Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2) =
          Almanac.fact (K - 2) := by
        rw [← hfact_eq, ← hfact_eq, ← hfact_eq]
        have h1 := Nat.choose_mul_factorial_mul_factorial (show b - 2 ≤ K - 2 by omega)
        have hsub : K - 2 - (b - 2) = K - b := by omega
        rw [hsub] at h1
        calc (K - b).factorial * (K - 2).choose (b - 2) * (b - 2).factorial
            = (K - 2).choose (b - 2) * (b - 2).factorial * (K - b).factorial := by ring
          _ = (K - 2).factorial := h1
      have hlayer_id : ∀ j : Fin r,
          F ^ r * ((allLayerSigmas m hm r hr K hK j.1).length * Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2)) =
          F ^ (r - 1 - j.1) * Db ^ j.1 * F * Almanac.fact (K - 2) := by
        intro j
        have hlen := allLayerSigmas_length m hm r hr K hK j.2
        have hexp : r = (r - 1 - j.1) + 1 + j.1 := by omega
        calc F ^ r * ((allLayerSigmas m hm r hr K hK j.1).length * Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2))
            = F ^ (r - 1 - j.1) * F * (F ^ j.1 * (allLayerSigmas m hm r hr K hK j.1).length) *
                Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2) := by
                  have hFr : F ^ r = F ^ (r - 1 - j.1) * F * F ^ j.1 := by
                    calc F ^ r = F ^ ((r - 1 - j.1) + 1 + j.1) := by congr 1
                      _ = F ^ (r - 1 - j.1) * F ^ 1 * F ^ j.1 := by rw [pow_add, pow_add]
                      _ = F ^ (r - 1 - j.1) * F * F ^ j.1 := by rw [pow_one]
                  rw [hFr]; ring
          _ = F ^ (r - 1 - j.1) * F * (Db ^ j.1 * Almanac.fact (K - b)) *
                Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2) := by rw [hlen]
          _ = F ^ (r - 1 - j.1) * Db ^ j.1 * F *
                (Almanac.fact (K - b) * Nat.choose (K - 2) (b - 2) * Almanac.fact (b - 2)) := by ring
          _ = F ^ (r - 1 - j.1) * Db ^ j.1 * F * Almanac.fact (K - 2) := by rw [hchoose_mul]
      -- Step 4b: Geometric telescoping sum: `(∑_{j < r} F^(r-1-j) * Db^j) * Lb + Db^r = F^r`!
      have hLb_le : Lb ≤ F := by
        have h1 := (selW6m_counts m hm).2.1
        have h2 := List.length_filter_le (fun L => ((selW6m m hm).row L).2 != .D) (allCanonLoops b)
        rw [h1, allCanonLoops_length] at h2; exact h2
      have hgeom : ∀ n : Nat,
          ((List.range n).map (fun j => F ^ (n - 1 - j) * Db ^ j)).sum * Lb + Db ^ n = F ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
          simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
          have hshift : (List.range n).map (fun j => F ^ (n - j) * Db ^ j) =
              ((List.range n).map (fun j => F ^ (n - 1 - j) * Db ^ j)).map (fun x => F * x) := by
            rw [List.map_map]
            refine List.map_congr_left fun j hj => ?_
            have hlt := List.mem_range.mp hj
            have he : n - j = (n - 1 - j) + 1 := by omega
            dsimp only [Function.comp_def]
            rw [he, pow_succ']; ring
          have hmul_sum : ∀ l : List Nat, (l.map (fun x => F * x)).sum = F * l.sum := fun l => by
            induction l with
            | nil => simp
            | cons a as iha => simp [iha, Nat.mul_add]
          rw [hshift, hmul_sum]
          have hFD : Db + Lb = F := Nat.sub_add_cancel hLb_le
          calc (F * ((List.range n).map (fun j => F ^ (n - 1 - j) * Db ^ j)).sum + Db ^ n) * Lb + Db ^ (n + 1)
              = F * (((List.range n).map (fun j => F ^ (n - 1 - j) * Db ^ j)).sum * Lb) +
                  Db ^ n * (Db + Lb) := by rw [pow_succ]; ring
            _ = F * (((List.range n).map (fun j => F ^ (n - 1 - j) * Db ^ j)).sum * Lb + Db ^ n) := by
                  rw [hFD]; ring
            _ = F * F ^ n := by rw [ihn]
            _ = F ^ (n + 1) := by rw [pow_succ']
      -- Step 4c: Multiply `zTotal * Lb ≤ (b - 1) * (K - 2)!` by `F^r * (b - 2)! > 0`!
      have hpos_mult : 0 < F ^ r * Almanac.fact (b - 2) :=
        Nat.mul_pos (pow_pos (hfact_pos _) r) (hfact_pos _)
      have hF_eq_bm1 : F = (b - 1) * Almanac.fact (b - 2) := by
        dsimp only [F]
        have h1 : b - 1 = (b - 2) + 1 := by omega
        rw [h1]; simp [Almanac.fact]
      have hsum_z : F ^ r * (zTotal * Almanac.fact (b - 2)) =
          ((List.range r).map (fun j => F ^ (r - 1 - j) * Db ^ j)).sum * F * Almanac.fact (K - 2) := by
        have hmul_l : ∀ (l : List Nat) (c : Nat), (l.map (· * c)).sum = l.sum * c := fun l c => by
          induction l with | nil => simp | cons a as ih => simp [ih, Nat.add_mul]
        have hl_mul : ∀ (l : List Nat) (c : Nat), (l.map (c * ·)).sum = c * l.sum := fun l c => by
          induction l with | nil => simp | cons a as ih => simp [ih, Nat.mul_add]
        have hfin_eq : (List.finRange r).map (fun j : Fin r => F ^ (r - 1 - j.1) * Db ^ j.1) =
            (List.range r).map (fun j => F ^ (r - 1 - j) * Db ^ j) := by
          refine List.ext_getElem (by simp) fun i hi1 hi2 => by simp
        dsimp only [zTotal]
        rw [← hmul_l, ← hl_mul, List.map_map, List.map_map]
        have hcongr : (List.finRange r).map (((fun x => F ^ r * x) ∘ (fun x => x * Almanac.fact (b - 2))) ∘
            fun j : Fin r => (allLayerSigmas m hm r hr K hK j.1).length * Nat.choose (K - 2) (b - 2)) =
            ((List.finRange r).map (fun j : Fin r => F ^ (r - 1 - j.1) * Db ^ j.1)).map
              (fun x => x * (F * Almanac.fact (K - 2))) := by
          rw [List.map_map]
          refine List.map_congr_left fun j _ => ?_
          dsimp only [Function.comp_def]
          rw [hlayer_id j]; ring
        rw [hcongr, hmul_l, hfin_eq]
        ring
      have hmul_ineq : F ^ r * Almanac.fact (b - 2) * (zTotal * Lb) ≤
          F ^ r * Almanac.fact (b - 2) * ((b - 1) * Almanac.fact (K - 2)) := by
        calc F ^ r * Almanac.fact (b - 2) * (zTotal * Lb)
            = F ^ r * (zTotal * Almanac.fact (b - 2)) * Lb := by ring
          _ = (((List.range r).map (fun j => F ^ (r - 1 - j) * Db ^ j)).sum * Lb) * F * Almanac.fact (K - 2) := by
                rw [hsum_z]; ring
          _ ≤ F ^ r * F * Almanac.fact (K - 2) := by
                have hle : ((List.range r).map (fun j => F ^ (r - 1 - j) * Db ^ j)).sum * Lb ≤ F ^ r := by
                  have := hgeom r; omega
                exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
          _ = F ^ r * ((b - 1) * Almanac.fact (b - 2)) * Almanac.fact (K - 2) := by
                rw [← hF_eq_bm1]
          _ = F ^ r * Almanac.fact (b - 2) * ((b - 1) * Almanac.fact (K - 2)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul_ineq hpos_mult
    · -- Exact body-sum identity across all layers `0 ≤ j < r`!
      have hsum_add : ∀ {α : Type} (l : List α) (f g : α → Nat),
          (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := fun l f g => by
        induction l with
        | nil => rfl
        | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega
      have hLHS : (bags.map (fun B => (B.map (fun e => e.body.length)).sum)).sum =
          ((List.finRange r).map fun j : Fin r =>
            (K - 1) * ((allLayerSigmas m hm r hr K hK j.1).length * Nat.choose (K - 2) (b - 2)) +
            (((allCanonLoops K).filter (fun L => activeLayer m hm r L == some j.1)).map
              (fun L => ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
                ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum).sum := by
        dsimp only [bags]
        rw [List.map_flatMap, hsum_flat]
        congr 1; refine List.map_congr_left fun j _ => ?_
        dsimp only [layerBagsOf]
        rw [List.map_map]
        exact layerBags_body_sum m hm r hr K hK j.2
      rw [hLHS, hsum_add]
      congr 1
      · dsimp only [zTotal]
        have hl_mul : ∀ (l : List Nat) (c : Nat), (l.map (c * ·)).sum = c * l.sum := fun l c => by
          induction l with | nil => simp | cons a as ih => simp [ih, Nat.mul_add]
        rw [← hl_mul, List.map_map]; rfl
      · -- Partition of non-`'D'` loops by `activeLayer L = some j` (`j ∈ List.finRange r`)!
        let fBody : List (Fin K) → Nat := fun L =>
          ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
            ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum
        have hLHS2 : ((List.finRange r).map fun j : Fin r =>
            (((allCanonLoops K).filter (fun L => activeLayer m hm r L == some j.1)).map fBody).sum).sum =
            (((List.finRange r).flatMap fun j : Fin r =>
              (allCanonLoops K).filter (fun L => activeLayer m hm r L == some j.1)).map fBody).sum := by
          rw [List.map_flatMap, hsum_flat]
        rw [hLHS2]
        have hnd1 : ((List.finRange r).flatMap fun j : Fin r =>
            (allCanonLoops K).filter (fun L => activeLayer m hm r L == some j.1)).Nodup := by
          rw [List.nodup_flatMap]
          refine ⟨fun j _ => (allCanonLoops_nodup K).filter _, ?_⟩
          refine (List.nodup_finRange r).imp_of_mem ?_
          intro j1 j2 _ _ hne L hL1 hL2
          have h1 : activeLayer m hm r L = some j1.1 := by simpa using (List.mem_filter.mp hL1).2
          have h2 : activeLayer m hm r L = some j2.1 := by simpa using (List.mem_filter.mp hL2).2
          exact hne (Fin.ext (Option.some.inj (h1.symm.trans h2)))
        have hnd2 : ((allCanonLoops K).filter
            (fun L => ((iterW6mLift m hm r hr K hK).row L).2 != .D)).Nodup :=
          (allCanonLoops_nodup K).filter _
        have hperm : ((List.finRange r).flatMap fun j : Fin r =>
            (allCanonLoops K).filter (fun L => activeLayer m hm r L == some j.1)).Perm
            ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 != .D)) := by
          refine (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun L => ?_
          simp only [List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq,
            bne_iff_ne]
          constructor
          · rintro ⟨j, hL_mem, hact⟩
            have hL' := (mem_allCanonLoops_iff L).mp hL_mem
            obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j.1).mp hact
            have hjb : (j.1 + 1) * b ≤ K := by
              have := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega); omega
            have hrowB := (selW6m m hm).row_perm (blockLoop b j.1 L)
              (canonLoop_isCanonLoop (projBlock_isPerm hjb hL'.1))
            refine ⟨hL_mem, ?_⟩
            change (iterW6mRow m hm r K hK L).2 ≠ .D
            cases hc : ((selW6m m hm).row (blockLoop b j.1 L)).2 with
            | D => exact absurd hc hj_neD
            | F => rw [iterW6mRow_eq_F hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; simp
            | S => rw [iterW6mRow_eq_S hm hK hact hj_lt hjb hc (by rw [hrowB.1.2]; omega)]; simp
          · rintro ⟨hL_mem, hneD⟩
            cases hact : activeLayer m hm r L with
            | none =>
              exfalso; apply hneD; change (iterW6mRow m hm r K hK L).2 = .D
              rw [iterW6mRow_eq_none hm hK hact]
            | some j =>
              obtain ⟨hj_lt, _, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp hact
              exact ⟨⟨j, hj_lt⟩, hL_mem, rfl⟩
        exact (hperm.map fBody).sum_eq

end AsymptoticZero
