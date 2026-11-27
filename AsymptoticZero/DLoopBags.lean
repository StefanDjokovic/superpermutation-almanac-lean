import AsymptoticZero.BlockEmbed

/-!
# AsymptoticZero.DLoopBags (Lemma 4)

Canonical closure of all remaining `'D'`-loops of `iterW6mLift m hm r hr K hK`:
* Let `w0 : Fin K := ⟨r * (6 * m), _⟩` (the first symbol outside blocks `B_0, ..., B_{r-1}`).
* Each canonical `'D'`-connector cycle `c ∈ allDCycles` (a length-`(K - 1)` `Nodup` list
  on `Fin K \ {w0}` starting at `0` whose projection onto every block `B_0, ..., B_{r-1}` is `'D'`)
  defines a single Eulerian bag `dBag c` consisting of `connCycleEdges (c.map embK)` plus the
  `K - 1` `'D'`-loop circuits `rowSlices (insertAt c w0 (pos + 1)) .D` (`pos < K - 1`).
* By `uniform_block_fibers` + `uniform_block_count` (from `BlockEmbed.lean`):
  `((6 * m - 1)!)^r * |allDCycles| = Db^r * (K - 2)!`.
* Every `'D'`-loop of `iterW6mLift` appears in `dBag c` for a unique `c ∈ allDCycles` and `pos < K - 1`.
-/

namespace AsymptoticZero

/-! ### 1. List helpers: `insertAt`, `erase`, `allCanonLoopsWithout` -/

/-- Insert `x` at position `pos` in `c`. -/
def insertAt {α : Type} (c : List α) (x : α) (pos : Nat) : List α :=
  c.take pos ++ [x] ++ c.drop pos

theorem insertAt_length {α : Type} (c : List α) (x : α) (pos : Nat) :
    (insertAt c x pos).length = c.length + 1 := by
  unfold insertAt
  simp only [List.length_append, List.length_singleton, List.length_take, List.length_drop]
  omega

theorem mem_insertAt {α : Type} {c : List α} {x y : α} {pos : Nat} :
    y ∈ insertAt c x pos ↔ y = x ∨ y ∈ c := by
  unfold insertAt
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ((h | rfl) | h)
    · exact Or.inr (List.mem_of_mem_take h)
    · exact Or.inl rfl
    · exact Or.inr (List.mem_of_mem_drop h)
  · rintro (rfl | h)
    · exact Or.inl (Or.inr rfl)
    · have := List.take_append_drop pos c
      rw [← this, List.mem_append] at h
      rcases h with h1 | h2
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h2

theorem insertAt_nodup {α : Type} {c : List α} {x : α} (hc : c.Nodup) (hx : x ∉ c) (pos : Nat) :
    (insertAt c x pos).Nodup := by
  have htd : (c.take pos ++ c.drop pos).Nodup := by rw [List.take_append_drop]; exact hc
  rw [List.nodup_append] at htd
  unfold insertAt
  rw [List.append_assoc, List.nodup_append]
  refine ⟨htd.1, ?_, ?_⟩
  · rw [List.singleton_append, List.nodup_cons]
    exact ⟨fun hm => hx (List.mem_of_mem_drop hm), htd.2.1⟩
  · intro a ha b hb
    rw [List.singleton_append, List.mem_cons] at hb
    rcases hb with rfl | hb'
    · intro h; subst h; exact hx (List.mem_of_mem_take ha)
    · exact htd.2.2 a ha b hb'

theorem insertAt_getElem_zero {α : Type} {c : List α} {x : α} {pos : Nat} (hpos : 1 ≤ pos)
    (hc : 0 < c.length) :
    (insertAt c x pos)[0]'(by rw [insertAt_length]; omega) = c[0]'hc := by
  have heq : insertAt c x pos = c.take pos ++ ([x] ++ c.drop pos) := by
    simp [insertAt, List.append_assoc]
  have h1 : (c.take pos ++ ([x] ++ c.drop pos))[0]'(by simp) = c[0]'hc := by
    rw [List.getElem_append_left (by simp; omega)]; simp
  simpa [heq] using h1

theorem insertAt_erase {α : Type} [DecidableEq α] {c : List α} {x : α} (hx : x ∉ c) (pos : Nat) :
    (insertAt c x pos).erase x = c := by
  unfold insertAt
  rw [List.append_assoc, List.erase_append_right _ (fun h => hx (List.mem_of_mem_take h))]
  rw [List.singleton_append, List.erase_cons_head, List.take_append_drop]

theorem insertAt_idxOf {α : Type} [DecidableEq α] {L : List α} {x : α}
    (hnd : L.Nodup) (hx : x ∈ L) :
    insertAt (L.erase x) x (L.idxOf x) = L := by
  have hidx_lt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
  have hsplit : L = L.take (L.idxOf x) ++ x :: L.drop (L.idxOf x + 1) := by
    have h1 := (List.take_append_drop (L.idxOf x) L).symm
    have hdrop : L.drop (L.idxOf x) = x :: L.drop (L.idxOf x + 1) := by
      rw [List.drop_eq_getElem_cons hidx_lt, List.getElem_idxOf]
    rwa [hdrop] at h1
  have hx_not_take : x ∉ L.take (L.idxOf x) := by
    intro hm
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hm
    rw [List.length_take] at hi
    rw [List.getElem_take] at heq
    have hlt : i < L.idxOf x := by omega
    have hinj : i = L.idxOf x := (List.Nodup.getElem_inj_iff hnd).mp (heq.trans (List.getElem_idxOf hidx_lt).symm)
    omega
  have herase : L.erase x = L.take (L.idxOf x) ++ L.drop (L.idxOf x + 1) := by
    conv_lhs => rw [hsplit]
    rw [List.erase_append_right _ hx_not_take, List.erase_cons_head]
  have hlen_take : (L.take (L.idxOf x)).length = L.idxOf x := by
    rw [List.length_take]; omega
  unfold insertAt
  rw [herase, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [List.append_assoc, List.singleton_append]
  exact hsplit.symm

theorem insertAt_rotate_take {α : Type} {c : List α} {x : α} {pos : Nat} (hpos : pos < c.length) :
    ((insertAt c x (pos + 1)).rotate ((pos + 2) % (c.length + 1))).take c.length =
      c.rotate (pos + 1) := by
  have h1 : insertAt c x (pos + 1) = (c.take (pos + 1) ++ [x]) ++ c.drop (pos + 1) := rfl
  have hlenA : (c.take (pos + 1) ++ [x]).length = pos + 2 := by simp; omega
  have hlenL : (insertAt c x (pos + 1)).length = c.length + 1 := insertAt_length c x (pos + 1)
  have hrot : (insertAt c x (pos + 1)).rotate ((pos + 2) % (c.length + 1)) =
      c.drop (pos + 1) ++ c.take (pos + 1) ++ [x] := by
    rw [← hlenL, List.rotate_mod]
    have happ := List.rotate_append_length_eq (c.take (pos + 1) ++ [x]) (c.drop (pos + 1))
    rw [hlenA] at happ
    rw [h1, happ, List.append_assoc]
  rw [hrot]
  have hlenR : (c.drop (pos + 1) ++ c.take (pos + 1)).length = c.length := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.rotate_eq_drop_append_take (by omega)]

/-- Canonical length-`(K - 1)` loops on `Fin K \ {w0}` starting at `0` (for `w0 ≠ 0`). -/
def allCanonLoopsWithout (K : Nat) [NeZero K] (w0 : Fin K) : List (List (Fin K)) :=
  (((List.finRange K).erase 0).erase w0).permutations.map (0 :: ·)

theorem allCanonLoopsWithout_nodup (K : Nat) [NeZero K] (w0 : Fin K) :
    (allCanonLoopsWithout K w0).Nodup := by
  unfold allCanonLoopsWithout
  refine List.Nodup.map (fun _ _ h => (List.cons.inj h).2) ?_
  exact List.nodup_permutations _ (((List.nodup_finRange K).erase 0).erase w0)

theorem allCanonLoopsWithout_length (K : Nat) [NeZero K] (hK : 2 ≤ K) {w0 : Fin K} (hw0 : w0 ≠ 0) :
    (allCanonLoopsWithout K w0).length = Almanac.fact (K - 2) := by
  unfold allCanonLoopsWithout
  rw [List.length_map, List.length_permutations]
  have hlen1 : ((List.finRange K).erase 0).length = K - 1 := by
    rw [List.length_erase_of_mem (List.mem_finRange 0), List.length_finRange]
  have hw0_mem : w0 ∈ (List.finRange K).erase 0 := by
    rw [List.mem_erase_of_ne hw0]
    exact List.mem_finRange w0
  have hlen2 : (((List.finRange K).erase 0).erase w0).length = K - 2 := by
    rw [List.length_erase_of_mem hw0_mem, hlen1]; omega
  rw [hlen2]
  have hfact : ∀ n : Nat, Nat.factorial n = Almanac.fact n := fun n => by
    induction n with
    | zero => rfl
    | succ k ih => simp [Nat.factorial, Almanac.fact, ih]
  exact hfact (K - 2)

theorem mem_allCanonLoopsWithout_iff {K : Nat} [NeZero K] {w0 : Fin K} (hw0 : w0 ≠ 0)
    (c : List (Fin K)) :
    c ∈ allCanonLoopsWithout K w0 ↔
      c.Nodup ∧ c.length = K - 1 ∧ w0 ∉ c ∧ c[0]? = some 0 := by
  unfold allCanonLoopsWithout
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_permutations] at ht
    have hnd_base : (((List.finRange K).erase 0).erase w0).Nodup :=
      ((List.nodup_finRange K).erase 0).erase w0
    have h0_notin : (0 : Fin K) ∉ t := by
      rw [ht.mem_iff]
      intro h
      have h1 := List.mem_of_mem_erase h
      exact (List.nodup_finRange K).not_mem_erase h1
    have hw_notin : w0 ∉ t := by
      rw [ht.mem_iff]
      exact ((List.nodup_finRange K).erase 0).not_mem_erase
    have hlen1 : ((List.finRange K).erase 0).length = K - 1 := by
      rw [List.length_erase_of_mem (List.mem_finRange 0), List.length_finRange]
    have hw_mem : w0 ∈ (List.finRange K).erase 0 := by
      rw [List.mem_erase_of_ne hw0]; exact List.mem_finRange w0
    have hlen2 : (((List.finRange K).erase 0).erase w0).length = K - 2 := by
      rw [List.length_erase_of_mem hw_mem, hlen1]; omega
    have hK2 : 2 ≤ K := by
      by_contra hlt
      have hK1 : K = 1 := by have := NeZero.ne K; omega
      have h0 : w0.1 = 0 := by omega
      exact hw0 (Fin.ext h0)
    refine ⟨List.nodup_cons.mpr ⟨h0_notin, ht.nodup_iff.mpr hnd_base⟩, ?_, ?_, rfl⟩
    · rw [List.length_cons, ht.length_eq, hlen2]; omega
    · simp [List.mem_cons, hw0, hw_notin]
  · rintro ⟨hnd, hlen, hw_notin, h0⟩
    cases c with
    | nil => simp at h0
    | cons a rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      refine ⟨rest, ?_, rfl⟩
      rw [List.mem_permutations]
      have hnd_r := (List.nodup_cons.mp hnd).2
      have h0_notin := (List.nodup_cons.mp hnd).1
      have hw_notin_r : w0 ∉ rest := fun h => hw_notin (List.mem_cons_of_mem _ h)
      have hnd_base : (((List.finRange K).erase 0).erase w0).Nodup :=
        ((List.nodup_finRange K).erase 0).erase w0
      have hsub : ∀ x ∈ rest, x ∈ ((List.finRange K).erase 0).erase w0 := by
        intro x hx
        have hxw : x ≠ w0 := fun h => hw_notin_r (h ▸ hx)
        have hx0 : x ≠ 0 := fun h => h0_notin (h ▸ hx)
        rw [List.mem_erase_of_ne hxw, List.mem_erase_of_ne hx0]
        exact List.mem_finRange x
      have hlen1 : ((List.finRange K).erase 0).length = K - 1 := by
        rw [List.length_erase_of_mem (List.mem_finRange 0), List.length_finRange]
      have hw_mem : w0 ∈ (List.finRange K).erase 0 := by
        rw [List.mem_erase_of_ne hw0]; exact List.mem_finRange w0
      have hlen2 : (((List.finRange K).erase 0).erase w0).length = K - 2 := by
        rw [List.length_erase_of_mem hw_mem, hlen1]; omega
      have hK2 : 2 ≤ K := by
        by_contra hlt
        have hK1 : K = 1 := by have := NeZero.ne K; omega
        have h0' : w0.1 = 0 := by omega
        exact hw0 (Fin.ext h0')
      have hlen_r : rest.length = (((List.finRange K).erase 0).erase w0).length := by
        rw [hlen2]; simp only [List.length_cons] at hlen; omega
      have hfin_eq : rest.toFinset = (((List.finRange K).erase 0).erase w0).toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx; rw [List.mem_toFinset] at hx ⊢; exact hsub x hx
        · rw [List.toFinset_card_of_nodup hnd_r, List.toFinset_card_of_nodup hnd_base, hlen_r]
      exact (List.perm_ext_iff_of_nodup hnd_r hnd_base).mpr fun x => by
        rw [← List.mem_toFinset, ← List.mem_toFinset, hfin_eq]

theorem projBlock_isPerm_of_without {b j K : Nat} (hjb : (j + 1) * b ≤ K)
    {w0 : Fin K} (hw0 : projBlockElem b j w0 = none)
    {c : List (Fin K)} (hnd : c.Nodup) (hlen : c.length = K - 1) (hw_notin : w0 ∉ c) :
    IsPerm b (projBlock b j c) := by
  have hins_perm : IsPerm K (insertAt c w0 0) :=
    ⟨insertAt_nodup hnd hw_notin 0, by rw [insertAt_length, hlen]; have := w0.2; omega⟩
  have hproj_eq : projBlock b j (insertAt c w0 0) = projBlock b j c := by
    unfold projBlock insertAt
    simp [List.filterMap_cons, hw0]
  rw [← hproj_eq]
  exact projBlock_isPerm hjb hins_perm

/-! ### 2. All `'D'`-connector cycles and exact count `((6m-1)!)^r * C_D = D_b^r * (K - 2)!` -/

/-- Canonical `'D'`-connector cycles on `Fin K \ {⟨r * 6m, _⟩}`. -/
noncomputable def allDCycles (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) : List (List (Fin K)) :=
  letI : NeZero K := ⟨by have := Nat.mul_le_mul_right (6 * m) hr; omega⟩
  letI : NeZero (6 * m) := ⟨by omega⟩
  let w0 : Fin K := ⟨r * (6 * m), by omega⟩
  (allCanonLoopsWithout K w0).filter (fun c =>
    decide (∀ j : Fin r, ((selW6m m hm).row (blockLoop (6 * m) j.1 c)).2 = .D))

theorem allDCycles_nodup (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    (allDCycles m hm r hr K hK).Nodup := by
  let _ : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
  unfold allDCycles
  exact (allCanonLoopsWithout_nodup K _).filter _

/-- Exact count of `'D'`-connector cycles:
`((6m - 1)!)^r * |allDCycles| = D_b^r * (K - 2)!`! -/
theorem allDCycles_length (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    (Almanac.fact (6 * m - 1)) ^ r * (allDCycles m hm r hr K hK).length =
      Db ^ r * Almanac.fact (K - 2) := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  set b := 6 * m
  let w0 : Fin K := ⟨r * b, by omega⟩
  have hw0_ne : w0 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    have hb_pos : 0 < b := by dsimp [b]; omega
    dsimp [w0] at hv; omega
  have hK2 : 2 ≤ K := by omega
  have hmul_j : ∀ j : Fin r, (j.1 + 1) * b ≤ K := fun j => by
    have h1 : (j.1 + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega)
    omega
  have hw0_none : ∀ j : Fin r, projBlockElem b j.1 w0 = none := fun j => by
    unfold projBlockElem
    have hnot : ¬(j.1 * b ≤ w0.1 ∧ w0.1 < (j.1 + 1) * b) := by
      have h1 : (j.1 + 1) * b ≤ r * b := Nat.mul_le_mul_right b (show j.1 + 1 ≤ r by omega)
      dsimp [w0]; omega
    exact dif_neg hnot
  have hfix_w0 : ∀ σ : Fin r → Equiv.Perm (Fin b),
      blockDiagPerm b r K (by omega) σ w0 = w0 := fun σ => by
    change blockDiagAct b r K (by omega) σ w0 = w0
    unfold blockDiagAct
    have hnot : ¬(w0.1 < r * b) := by dsimp [w0]; omega
    exact dif_neg hnot
  have hmem_zero_of_without : ∀ {c : List (Fin K)}, c.Nodup → c.length = K - 1 → w0 ∉ c →
      ∀ x : Fin K, x ≠ w0 → x ∈ c := by
    intro c hnd hlen hw_notin x hxw
    have hins : IsPerm K (insertAt c w0 0) :=
      ⟨insertAt_nodup hnd hw_notin 0, by rw [insertAt_length, hlen]; omega⟩
    have hm := mem_of_isPerm hins x
    rw [mem_insertAt] at hm
    rcases hm with rfl | h
    · exact absurd rfl hxw
    · exact h
  have hact_mem : ∀ (σ : Fin r → Equiv.Perm (Fin b)) (c : List (Fin K)),
      c ∈ allCanonLoopsWithout K w0 →
      canonLoop (c.map (blockDiagPerm b r K (by omega) σ)) ∈ allCanonLoopsWithout K w0 := by
    intro σ c hc
    obtain ⟨hnd, hlen, hw_notin, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc
    rw [mem_allCanonLoopsWithout_iff hw0_ne]
    let e := blockDiagPerm b r K (by omega) σ
    have hnd_m : (c.map e).Nodup := hnd.map e.injective
    have hlen_m : (c.map e).length = K - 1 := by rw [List.length_map, hlen]
    have hw_notin_m : w0 ∉ c.map e := by
      rw [List.mem_map]; rintro ⟨x, hx, hxe⟩
      have : x = w0 := e.injective (hxe.trans (hfix_w0 σ).symm)
      exact hw_notin (this ▸ hx)
    have h0_mem : (0 : Fin K) ∈ c.map e := hmem_zero_of_without hnd_m hlen_m hw_notin_m 0 hw0_ne.symm
    refine ⟨(canonLoop_isRotated _).symm.perm.nodup_iff.mpr hnd_m,
      by rw [(canonLoop_isRotated _).symm.perm.length_eq, hlen_m],
      fun h => hw_notin_m ((canonLoop_isRotated _).symm.perm.mem_iff.mp h), ?_⟩
    unfold canonLoop
    have hidx : (c.map e).idxOf 0 < (c.map e).length := List.idxOf_lt_length_of_mem h0_mem
    have hpos : 0 < (c.map e).length := Nat.lt_of_le_of_lt (Nat.zero_le _) hidx
    rw [List.getElem?_eq_getElem (by rw [List.length_rotate]; exact hpos)]
    congr 1
    rw [List.getElem_rotate, Nat.zero_add]
    have hmod : (c.map e).idxOf 0 % (c.map e).length = (c.map e).idxOf 0 := Nat.mod_eq_of_lt hidx
    change (c.map e)[(c.map e).idxOf 0 % (c.map e).length]'(Nat.mod_lt _ hpos) = 0
    simp only [hmod, List.getElem_idxOf]
  have huni := uniform_block_fibers (α := List (Fin K)) (b := b) r (allCanonLoopsWithout K w0)
    (allCanonLoopsWithout_nodup K w0)
    (fun c j => blockLoop b j.1 c)
    (fun c hc j => by
      obtain ⟨hnd, hlen, hw_notin, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc
      exact canonLoop_isCanonLoop (projBlock_isPerm_of_without (hmul_j j) (hw0_none j) hnd hlen hw_notin))
    (fun σ c => canonLoop (c.map (blockDiagPerm b r K (by omega) σ)))
    hact_mem
    (fun σ c hc => by
      obtain ⟨hnd, hlen, hw_notin, h0⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc
      have hc' := hact_mem σ c hc
      have hc'' := hact_mem (fun j => (σ j)⁻¹) _ hc'
      obtain ⟨hnd'', hlen'', hw_notin'', h0''⟩ := (mem_allCanonLoopsWithout_iff hw0_ne _).mp hc''
      have hrot1 : (canonLoop (c.map (blockDiagPerm b r K (by omega) σ))).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹)) ~r
          (c.map (blockDiagPerm b r K (by omega) σ)).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹)) :=
        (canonLoop_isRotated _).symm.map _
      have hinv_map : (c.map (blockDiagPerm b r K (by omega) σ)).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹)) = c := by
        rw [List.map_map]
        have hcomp : ((blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹)) ∘
            (blockDiagPerm b r K (by omega) σ)) = id := by
          funext x; exact (blockDiagPerm b r K (by omega) σ).left_inv x
        simp [hcomp]
      rw [hinv_map] at hrot1
      have hrot_fin : canonLoop ((canonLoop (c.map (blockDiagPerm b r K (by omega) σ))).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹))) ~r c :=
        (canonLoop_isRotated _).symm.trans hrot1
      -- Two `Nodup` lists with the same head `0` that are rotations of each other are equal!
      obtain ⟨rot, hrot_eq⟩ := hrot_fin.symm
      have hlen_pos : 0 < c.length := by omega
      have h0_eq : (c.rotate rot)[0]'(by rw [List.length_rotate]; exact hlen_pos) = c[0]'hlen_pos := by
        have ha : (canonLoop ((canonLoop (c.map (blockDiagPerm b r K (by omega) σ))).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹))))[0]'(by rw [hlen'']; omega) = 0 := by
          rw [List.getElem?_eq_getElem (by rw [hlen'']; omega)] at h0''
          exact Option.some.inj h0''
        have hb : c[0]'hlen_pos = 0 := by
          rw [List.getElem?_eq_getElem hlen_pos] at h0
          exact Option.some.inj h0
        simpa [hrot_eq, hb] using ha
      rw [List.getElem_rotate, Nat.zero_add] at h0_eq
      have hrmod : rot % c.length = 0 := (List.Nodup.getElem_inj_iff hnd).mp h0_eq
      calc canonLoop ((canonLoop (c.map (blockDiagPerm b r K (by omega) σ))).map
            (blockDiagPerm b r K (by omega) (fun j => (σ j)⁻¹)))
          = c.rotate rot := hrot_eq.symm
        _ = c.rotate (rot % c.length) := (List.rotate_mod c rot).symm
        _ = c := by rw [hrmod, List.rotate_zero])
    (fun σ c hc j => by
      obtain ⟨hnd, hlen, hw_notin, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc
      obtain ⟨hnd', hlen', hw_notin', _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne _).mp (hact_mem σ c hc)
      have hjb := hmul_j j
      have hpL : IsPerm b (projBlock b j.1 c) :=
        projBlock_isPerm_of_without hjb (hw0_none j) hnd hlen hw_notin
      have hp1 : IsPerm b (projBlock b j.1 (canonLoop (c.map (blockDiagPerm b r K (by omega) σ)))) :=
        projBlock_isPerm_of_without hjb (hw0_none j) hnd' hlen' hw_notin'
      have hpB : IsPerm b ((blockLoop b j.1 c).map (σ j)) :=
        ⟨(canonLoop_isCanonLoop hpL).1.1.map (σ j).injective,
          by rw [List.length_map]; exact (canonLoop_isCanonLoop hpL).1.2⟩
      have hrot1 : projBlock b j.1 (canonLoop (c.map (blockDiagPerm b r K (by omega) σ))) ~r
          projBlock b j.1 (c.map (blockDiagPerm b r K (by omega) σ)) :=
        projBlock_isRotated (canonLoop_isRotated _).symm
      rw [projBlock_map_blockDiagPerm] at hrot1
      have hrot2 : (projBlock b j.1 c).map (σ j) ~r (blockLoop b j.1 c).map (σ j) :=
        (canonLoop_isRotated _).map _
      exact (canonLoop_eq_iff hp1 hpB).mpr (hrot1.trans hrot2))
  let P : (Fin r → List (Fin b)) → Bool :=
    fun t => decide (∀ j : Fin r, ((selW6m m hm).row (t j)).2 = .D)
  have hcnt := uniform_block_count r (allCanonLoopsWithout K w0) (allCanonLoopsWithout_nodup K w0)
    (fun c j => blockLoop b j.1 c)
    (fun c hc j => by
      obtain ⟨hnd, hlen, hw_notin, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc
      exact canonLoop_isCanonLoop (projBlock_isPerm_of_without (hmul_j j) (hw0_none j) hnd hlen hw_notin))
    huni P
  rw [allCanonLoopsWithout_length K hK2 hw0_ne, count_allD_tuples m hm r] at hcnt
  exact hcnt

/-! ### 3. `'D'`-loop bags `dBag c` and full Lemma 4 -/

/-- The Eulerian bag for a `'D'`-connector cycle `c ∈ allDCycles`:
1 connector cycle `connCycleEdges (c.map embK)` + `K - 1` `'D'`-loop circuits. -/
def dBag {K : Nat} (w0 : Fin K) (c : List (Fin K)) : List (RawEdge (K + 2)) :=
  connCycleEdges (c.map embK) ++
    (List.range (K - 1)).flatMap (fun pos => rowSlices (insertAt c w0 (pos + 1)) .D)

/-- Helper: symmetry of `Relation.ReflTransGen (UndirAdj E)`. -/
theorem undirReach_symm {n : Nat} {E : List (RawEdge n)} {x y : Almanac.Word n}
    (h : Relation.ReflTransGen (UndirAdj E) x y) :
    Relation.ReflTransGen (UndirAdj E) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (Relation.ReflTransGen.single ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩).trans ih
    · exact (Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩).trans ih

/-- Helper: weakly connected when every edge's start vertex reaches a common hub vertex `hub`. -/
theorem weaklyConnected_of_circuits_touching_hub {n : Nat}
    {E : List (RawEdge n)} {hub : Almanac.Word n}
    (hreach : ∀ e ∈ E, Relation.ReflTransGen (UndirAdj E) e.u hub) :
    WeaklyConnected E := by
  intro e1 he1 e2 he2
  exact (hreach e1 he1).trans (undirReach_symm (hreach e2 he2))

/-- Helper: every edge of a circuit `C ⊆ E` reaches its base vertex `v0`. -/
theorem circuit_edges_undirReach {n : Nat}
    {E C : List (RawEdge n)} {v0 : Almanac.Word n} (hsub : ∀ e ∈ C, e ∈ E)
    (hcirc : IsCircuitAt C v0) :
    ∀ e ∈ C, Relation.ReflTransGen (UndirAdj E) e.u v0 := by
  have hwalk : ∀ (l : List (RawEdge n)), IsChainE l → (∀ e ∈ l, e ∈ E) →
      ∀ (a b : Nat) (ha : a < l.length) (hb : b < l.length),
      Relation.ReflTransGen (UndirAdj E) (l[a]'ha).u (l[b]'hb).u := by
    intro l hch hl
    have hstep : ∀ (i : Nat) (hi : i + 1 < l.length),
        Relation.ReflTransGen (UndirAdj E) (l[i]'(by omega)).u (l[i + 1]'hi).u := by
      intro i hi
      have hvu : (l[i]'(by omega)).v = (l[i + 1]'hi).u := by
        induction l generalizing i with
        | nil => simp at hi
        | cons x xs ih =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
            cases i with
            | zero => exact hch.1
            | succ i' =>
              exact ih hch.2 (fun e he => hl e (List.mem_cons_of_mem _ he)) i' (by simp at hi ⊢; omega)
      rw [← hvu]
      exact Relation.ReflTransGen.single ⟨l[i]'(by omega), hl _ (List.getElem_mem _), Or.inl ⟨rfl, rfl⟩⟩
    have hfwd : ∀ (a b : Nat) (hab : a ≤ b) (hb : b < l.length),
        Relation.ReflTransGen (UndirAdj E) (l[a]'(by omega)).u (l[b]'hb).u := by
      intro a b hab
      induction b with
      | zero =>
        intro hb
        have : a = 0 := by omega
        subst this; exact Relation.ReflTransGen.refl
      | succ b' ih =>
        intro hb
        by_cases hle : a ≤ b'
        · exact (ih hle (by omega)).trans (hstep b' hb)
        · have : a = b' + 1 := by omega
          subst this; exact Relation.ReflTransGen.refl
    intro a b ha hb
    by_cases hle : a ≤ b
    · exact hfwd a b hle hb
    · exact undirReach_symm (hfwd b a (by omega) ha)
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have h0 : 0 < C.length := List.length_pos_of_ne_nil hcirc.1
  have hr := hwalk C hcirc.2.1 hsub i 0 hi h0
  have hhd : (C[0]'h0).u = v0 := by rw [← List.head_eq_getElem]; exact hcirc.2.2.1
  rwa [hhd] at hr

theorem dBag_valid {K : Nat} (hK : 4 ≤ K) {w0 : Fin K} {c : List (Fin K)}
    (hc_len : c.length = K - 1) :
    dBag w0 c ≠ [] ∧
    (∀ e ∈ dBag w0 c, EdgeOk (K - 1) e) ∧
    Balanced (dBag w0 c) ∧
    WeaklyConnected (dBag w0 c) := by
  have hc_emb : (c.map embK).length = K - 1 := by rw [List.length_map, hc_len]
  have hc_emb_pos : 0 < (c.map embK).length := by omega
  have hconn_circ : IsCircuitAt (connCycleEdges (c.map embK)) (c.map embK) :=
    connCycleEdges_isCircuit hc_emb_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dBag
    intro h
    have h1 := (List.append_eq_nil_iff.mp h).1
    exact hconn_circ.1 h1
  · intro e he
    unfold dBag at he
    rw [List.mem_append, List.mem_flatMap] at he
    rcases he with h1 | ⟨pos, _, h2⟩
    · exact connCycleEdges_ok hc_emb e h1
    · exact rowSlices_ok hK (by rw [insertAt_length, hc_len]; omega) .D e h2
  · unfold dBag
    apply balanced_append (connCycleEdges_balanced hc_emb_pos)
    have hbal_flat : ∀ (l : List Nat),
        Balanced (l.flatMap (fun pos => rowSlices (insertAt c w0 (pos + 1)) .D)) := by
      intro l
      induction l with
      | nil => exact balanced_nil
      | cons a as ih =>
        rw [List.flatMap_cons]
        exact balanced_append (rowSlices_D_balanced hK (by rw [insertAt_length, hc_len]; omega)) ih
    exact hbal_flat _
  · apply weaklyConnected_of_circuits_touching_hub (hub := c.map embK)
    intro e he
    unfold dBag at he
    rw [List.mem_append, List.mem_flatMap] at he
    rcases he with h1 | ⟨pos, hpos_mem, h2⟩
    · exact circuit_edges_undirReach (fun x hx => List.mem_append_left _ hx) hconn_circ e h1
    · have hpos_lt : pos < K - 1 := List.mem_range.mp hpos_mem
      let L := insertAt c w0 (pos + 1)
      have hL_len : L.length = K := by rw [insertAt_length, hc_len]; omega
      have hD_circ := rowSlices_D_isCircuit hK hL_len
      have hsub_D : ∀ x ∈ rowSlices L .D, x ∈ dBag w0 c := fun x hx =>
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨pos, hpos_mem, hx⟩)
      have hsub_conn : ∀ x ∈ connCycleEdges (c.map embK), x ∈ dBag w0 c := fun x hx =>
        List.mem_append_left _ hx
      have hr1 := circuit_edges_undirReach hsub_D hD_circ e h2
      let idx := (pos + 2) % K
      have hidx_lt : idx < K := Nat.mod_lt _ (by omega)
      have hrep_mem : repSlice L idx ∈ rowSlices L .D := by
        unfold rowSlices; exact List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx_lt, rfl⟩
      have hr2 := circuit_edges_undirReach hsub_D hD_circ (repSlice L idx) hrep_mem
      have hrep_u : (repSlice L idx).u = (c.map embK).rotate (pos + 1) := by
        rw [repSlice_u hK hL_len idx]
        have hrot := insertAt_rotate_take (c := c) (x := w0) (by omega : pos < c.length)
        rw [hc_len, show K - 1 + 1 = K by omega] at hrot
        change ((L.rotate idx).take (K - 1)).map embK = (c.map embK).rotate (pos + 1)
        rw [hrot, List.map_rotate]
      have hconn_hit := connCycleEdges_mem_rot ((pos + 1) % (K - 1))
        (by rw [hc_emb]; exact Nat.mod_lt _ (by omega))
      have hrot_mod : (c.map embK).rotate ((pos + 1) % (K - 1)) = (c.map embK).rotate (pos + 1) := by
        rw [← hc_emb, List.rotate_mod]
      rw [hrot_mod] at hconn_hit
      obtain ⟨ec, hec_mem, hec_u⟩ := hconn_hit
      have hr3 := circuit_edges_undirReach hsub_conn hconn_circ ec hec_mem
      rw [hec_u] at hr3
      exact hr1.trans ((undirReach_symm hr2).trans (hrep_u ▸ hr3))

theorem dBag_body_sum {K : Nat} (hK : 4 ≤ K) {w0 : Fin K} {c : List (Fin K)}
    (hc_len : c.length = K - 1) :
    ((dBag w0 c).map (fun e => e.body.length)).sum =
      (K - 1) + ((List.range (K - 1)).map (fun pos =>
        ((rowSlices (insertAt c w0 (pos + 1)) .D).map (fun e => e.body.length)).sum)).sum := by
  unfold dBag
  rw [List.map_append, List.sum_append, connCycleEdges_body_sum (by rw [List.length_map, hc_len])]
  congr 1
  rw [List.map_flatMap]
  have hsum_flat : ∀ {α : Type} (l : List α) (f : α → List Nat),
      (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := fun l f => by
    induction l with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, List.sum_append, ih]
  exact hsum_flat _ _

/-- **Main Lemma 4 Theorem (`dLoop_bags_theorem`):**
All `'D'`-loops of `iterW6mLift m hm r hr K hK` are partitioned into `|allDCycles|` valid Eulerian bags
whose total count satisfies `((6m-1)!)^r * |bags| = Db^r * (K - 2)!` and whose total body sum equals
`(K - 1) * |bags| + ∑_{L ∈ D-loops} bodySum(rowSlices L .D)`. -/
theorem dLoop_bags_theorem (m : Nat) (hm : 1 ≤ m) (r : Nat) (hr : 1 ≤ r)
    (K : Nat) (hK : r * (6 * m) + 1 ≤ K) :
    letI : NeZero K := ⟨by have h1 := Nat.mul_le_mul_right (6 * m) hr; rw [Nat.one_mul] at h1; omega⟩
    let Db := Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)
    ∃ bags : List (List (RawEdge (K + 2))),
      (Almanac.fact (6 * m - 1)) ^ r * bags.length = Db ^ r * Almanac.fact (K - 2) ∧
      (∀ B ∈ bags, B ≠ [] ∧ (∀ e ∈ B, EdgeOk (K - 1) e) ∧ Balanced B ∧ WeaklyConnected B) ∧
      (∀ L ∈ allCanonLoops K, ((iterW6mLift m hm r hr K hK).row L).2 = .D →
        ∀ e ∈ rowSlices ((iterW6mLift m hm r hr K hK).row L).1 .D, ∃ B ∈ bags, e ∈ B) ∧
      (bags.map (fun B => (B.map (fun e => e.body.length)).sum)).sum =
        (K - 1) * bags.length +
        (((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).map
          (fun L => ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
            ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum := by
  have h6le : 6 * m ≤ r * (6 * m) := by
    have h1 := Nat.mul_le_mul_right (6 * m) hr; rwa [Nat.one_mul] at h1
  let _ : NeZero K := ⟨by omega⟩
  let _ : NeZero (6 * m) := ⟨by omega⟩
  have hK4 : 4 ≤ K := by omega
  let w0 : Fin K := ⟨r * (6 * m), by omega⟩
  have hw0_ne : w0 ≠ 0 := by
    intro h; have hv := congrArg Fin.val h; dsimp [w0] at hv; omega
  let cycles := allDCycles m hm r hr K hK
  refine ⟨cycles.map (dBag w0), ?_, ?_, ?_, ?_⟩
  · rw [List.length_map]; exact allDCycles_length m hm r hr K hK
  · intro B hB
    rw [List.mem_map] at hB
    obtain ⟨c, hc, rfl⟩ := hB
    have hc_mem : c ∈ allCanonLoopsWithout K w0 := (List.mem_filter.mp hc).1
    obtain ⟨_, hc_len, _, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp hc_mem
    exact dBag_valid hK4 hc_len
  · intro L hL hD e he
    have hL' := (mem_allCanonLoops_iff L).mp hL
    have hact : activeLayer m hm r L = none := by
      cases ha : activeLayer m hm r L with
      | none => rfl
      | some j =>
        obtain ⟨hj_lt, hj_neD, _⟩ := (activeLayer_eq_some_iff m hm r L j).mp ha
        have hjb : (j + 1) * (6 * m) ≤ K := by
          have := Nat.mul_le_mul_right (6 * m) (show j + 1 ≤ r by omega); omega
        have hrowB := (selW6m m hm).row_perm (blockLoop (6 * m) j L)
          (canonLoop_isCanonLoop (projBlock_isPerm hjb hL'.1))
        dsimp only [iterW6mLift] at hD
        cases hc : ((selW6m m hm).row (blockLoop (6 * m) j L)).2 with
        | D => exact absurd hc hj_neD
        | F => rw [iterW6mRow_eq_F hm hK ha hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hD; cases hD
        | S => rw [iterW6mRow_eq_S hm hK ha hj_lt hjb hc (by rw [hrowB.1.2]; omega)] at hD; cases hD
    have hrow_eq : ((iterW6mLift m hm r hr K hK).row L).1 = L := by
      dsimp only [iterW6mLift]; rw [iterW6mRow_eq_none hm hK hact]
    rw [hrow_eq] at he
    have hw_mem : w0 ∈ L := mem_of_isPerm hL'.1 w0
    let c := L.erase w0
    have hc_nd : c.Nodup := hL'.1.1.erase w0
    have hc_len : c.length = K - 1 := by rw [List.length_erase_of_mem hw_mem, hL'.1.2]
    have hw_notin : w0 ∉ c := hL'.1.1.not_mem_erase
    have hidx_pos : 1 ≤ L.idxOf w0 := by
      by_contra hlt
      have h0 : L.idxOf w0 = 0 := by omega
      have hget : L[0]'(by rw [hL'.1.2]; omega) = w0 := by
        have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hw_mem)
        simpa [h0] using this
      have hL0 : L[0]'(by rw [hL'.1.2]; omega) = 0 := by
        have hhd := hL'.2
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hL'.1.2]; omega)] at hhd
        exact Option.some.inj hhd
      exact hw0_ne (hget.symm.trans hL0)
    have hidx_lt : L.idxOf w0 < K := by
      have := List.idxOf_lt_length_of_mem hw_mem; rwa [hL'.1.2] at this
    have hc_0 : c[0]? = some 0 := by
      have hL_hd := hL'.2
      cases hL_eq : L with
      | nil => simp [hL_eq] at hL_hd
      | cons a rest =>
        have ha : a = 0 := by simp [hL_eq] at hL_hd; exact hL_hd
        subst ha
        have hne : (0 : Fin K) ≠ w0 := hw0_ne.symm
        show ((L.erase w0))[0]? = some 0
        rw [hL_eq, List.erase_cons_tail (by simp [hne])]; rfl
    have hc_in_wo : c ∈ allCanonLoopsWithout K w0 :=
      (mem_allCanonLoopsWithout_iff hw0_ne c).mpr ⟨hc_nd, hc_len, hw_notin, hc_0⟩
    have hc_in_D : c ∈ cycles := by
      refine List.mem_filter.mpr ⟨hc_in_wo, decide_eq_true fun j => ?_⟩
      have hproj_c : projBlock (6 * m) j.1 c = projBlock (6 * m) j.1 L := by
        have hL_ins : insertAt c w0 (L.idxOf w0) = L := insertAt_idxOf hL'.1.1 hw_mem
        have hw_none : projBlockElem (6 * m) j.1 w0 = none := by
          unfold projBlockElem
          have h1 : (j.1 + 1) * (6 * m) ≤ r * (6 * m) :=
            Nat.mul_le_mul_right (6 * m) (show j.1 + 1 ≤ r by omega)
          exact dif_neg (by dsimp [w0]; omega)
        rw [← hL_ins]
        unfold projBlock insertAt
        rw [List.filterMap_append, List.filterMap_append, List.filterMap_cons, hw_none,
          List.filterMap_nil, List.append_nil, ← List.filterMap_append, List.take_append_drop]
      have hbl_eq : blockLoop (6 * m) j.1 c = blockLoop (6 * m) j.1 L := by
        unfold blockLoop; rw [hproj_c]
      rw [hbl_eq]
      exact (activeLayer_eq_none_iff m hm r L).mp hact j.1 j.2
    refine ⟨dBag w0 c, List.mem_map.mpr ⟨c, hc_in_D, rfl⟩, ?_⟩
    unfold dBag
    apply List.mem_append_right
    rw [List.mem_flatMap]
    refine ⟨L.idxOf w0 - 1, List.mem_range.mpr (by omega), ?_⟩
    have hpos : L.idxOf w0 - 1 + 1 = L.idxOf w0 := by omega
    rw [hpos, insertAt_idxOf hL'.1.1 hw_mem]
    exact he
  · -- Exact body-sum identity: every `(c, pos)` contributes `(K + 2) * (K + 2) * K`!
    have hD_body : ∀ L ∈ (allCanonLoops K).filter
        (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D),
        ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
          ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum =
        (K + 2) * (K + 2) * K := by
      intro L hL
      obtain ⟨hL_mem, hL_D⟩ := List.mem_filter.mp hL
      have hL' := (mem_allCanonLoops_iff L).mp hL_mem
      have hD_eq : ((iterW6mLift m hm r hr K hK).row L).2 = .D := by
        simpa using hL_D
      have hrow_perm := (iterW6mLift m hm r hr K hK).row_perm L hL'
      rw [hD_eq, rowSlices_body_sum hK4 hrow_perm.1.2]; simp
    have hRHS_sum : (((allCanonLoops K).filter
        (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).map
          (fun L => ((rowSlices ((iterW6mLift m hm r hr K hK).row L).1
            ((iterW6mLift m hm r hr K hK).row L).2).map (fun e => e.body.length)).sum)).sum =
        ((allCanonLoops K).filter
          (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).length *
          ((K + 2) * (K + 2) * K) := by
      rw [List.map_congr_left hD_body, List.map_const', List.sum_replicate, smul_eq_mul]
    have hLHS_each : ∀ B ∈ cycles.map (dBag w0),
        (B.map (fun e => e.body.length)).sum =
          (K - 1) + (K - 1) * ((K + 2) * (K + 2) * K) := by
      intro B hB
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hB
      obtain ⟨_, hc_len, _, _⟩ := (mem_allCanonLoopsWithout_iff hw0_ne c).mp (List.mem_filter.mp hc).1
      rw [dBag_body_sum hK4 hc_len]
      congr 1
      have hpos_body : ∀ pos ∈ List.range (K - 1),
          ((rowSlices (insertAt c w0 (pos + 1)) .D).map (fun e => e.body.length)).sum =
            (K + 2) * (K + 2) * K := by
        intro pos _
        have hlen_ins : (insertAt c w0 (pos + 1)).length = K := by
          rw [insertAt_length, hc_len]; omega
        simpa using rowSlices_body_sum hK4 hlen_ins .D
      rw [List.map_congr_left hpos_body, List.map_const', List.sum_replicate, List.length_range,
        smul_eq_mul]
    rw [hRHS_sum, List.map_congr_left hLHS_each, List.map_const', List.sum_replicate, smul_eq_mul,
      List.length_map]
    -- Compare `(K - 1) * cycles.length` with `|D-loops|`: both equal `Db^r * (K - 1)! / ((6m-1)!)^r`!
    have hcnt_eq : (K - 1) * cycles.length =
        ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).length := by
      have hFpos : 0 < (Almanac.fact (6 * m - 1)) ^ r := by
        refine pow_pos ?_ r
        have hfp : ∀ n, 0 < Almanac.fact n := fun n => by
          induction n with
          | zero => exact Nat.zero_lt_one
          | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih
        exact hfp _
      have h1 := allDCycles_length m hm r hr K hK
      have h2 := iterW6mLift_D_count m hm r hr K hK
      have hfact_step : (K - 1) * Almanac.fact (K - 2) = Almanac.fact (K - 1) := by
        have hK1 : K - 1 = (K - 2) + 1 := by omega
        rw [hK1]; simp [Almanac.fact]
      have hmul : (Almanac.fact (6 * m - 1)) ^ r * ((K - 1) * cycles.length) =
          (Almanac.fact (6 * m - 1)) ^ r *
            ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).length := by
        calc (Almanac.fact (6 * m - 1)) ^ r * ((K - 1) * cycles.length)
            = (K - 1) * ((Almanac.fact (6 * m - 1)) ^ r * cycles.length) := by ring
          _ = (K - 1) * ((Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) ^ r *
                Almanac.fact (K - 2)) := by rw [h1]
          _ = (Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) ^ r *
                ((K - 1) * Almanac.fact (K - 2)) := by ring
          _ = (Almanac.fact (6 * m - 1) - 4 * m * (6 * m - 2)) ^ r *
                Almanac.fact (K - 1) := by rw [hfact_step]
          _ = (Almanac.fact (6 * m - 1)) ^ r *
                ((allCanonLoops K).filter (fun L => ((iterW6mLift m hm r hr K hK).row L).2 == .D)).length := h2.symm
      exact Nat.eq_of_mul_eq_mul_left hFpos hmul
    rw [← hcnt_eq]; ring

end AsymptoticZero
