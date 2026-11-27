import LowerBounds.DomSound
import LowerBounds.K16Sound

/-!
# Soundness of the Pure `Nat.iterate` GFP `U3Fwd` Table (`FastK16.buildU3MinR`)

Proves that `FastK16.buildU3Rows` computes a sound upper bound on the length of any pure-`w3`
suffix `rest` following 3 `w3`-linked rows `(R0, R1, R2)` in state `s3`, under `NoM3` and
(if `js`) `NoJS`, and therefore `FastK16.buildU3MinR` computes a sound strict lower bound on
the prefix row count `nr` whenever `t == s`.
-/

namespace SuperpermLowerBounds
namespace FastSound

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT encB ciTab nxtTab relabSeq)
open K16 (NoJS tau2 permW_tau2)
open FastK16 (S7K16Tabs buildS7K16Tabs buildM3Allow placeRow stateEdges relaxRow iterN
  buildU3Rows buildU3MinR perms3NonId)

/-! ### `placeRow` Soundness -/

theorem tabs_ciArr_eq : buildS7K16Tabs.ciArr = ciTab 7 (PS.permCodes 7 7) := rfl
theorem tabs_nxtArr_eq : buildS7K16Tabs.nxtArr = nxtTab 7 (PS.permCodes 7 7) := rfl

/-- Check that `placeRow` succeeds on any valid row `R` whose classes are disjoint from `used`. -/
theorem placeRow_sound (ciArr nxtArr : Array ℕ)
    (hci : ∀ w, PermW 7 w → ciArr[encB 7 w]! = (ciTab 7 (PS.permCodes 7 7))[encB 7 w]!)
    (hnxt : ∀ a b, PermW 7 a → DoorEq 7 a b → nxtArr[encB 7 a]! = encB 7 b) :
    ∀ (R : List (List ℕ)) (u : List ℕ) (used : List ℕ) (hne : R ≠ []),
      R.head hne = u →
      (∀ w ∈ R, PermW 7 w) →
      List.IsChain (DoorEq 7) R →
      List.Pairwise (fun a b => ¬ a ~r b) R →
      (∀ w ∈ R, ciArr[encB 7 w]! ∉ used) →
      ∃ outUsed,
        placeRow ciArr nxtArr R.length (encB 7 u) used =
          some (encB 7 (R.getLast hne), outUsed) ∧
        (∀ c, c ∈ outUsed ↔ c ∈ used ∨ ∃ w ∈ R, c = ciArr[encB 7 w]!)
  | [], _, _, h, _, _, _, _, _ => absurd rfl h
  | [v], u, used, _, hh, _, _, _, hnew => by
    simp only [List.head_cons] at hh
    subst hh
    have hnot : used.contains (ciArr[encB 7 v]!) = false := by
      cases hc : used.contains (ciArr[encB 7 v]!)
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) (hnew v List.mem_cons_self)
    refine ⟨ciArr[encB 7 v]! :: used, ?_, ?_⟩
    · simp only [List.length_singleton, placeRow, hnot, Bool.false_eq_true, ite_false,
        List.getLast_singleton]
    · intro c
      rw [List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inr ⟨v, List.mem_cons_self, rfl⟩
        · exact Or.inl h
      · rintro (h | ⟨w, hw, rfl⟩)
        · exact Or.inr h
        · rw [List.mem_singleton.mp hw]; exact Or.inl rfl
  | v :: v' :: R', u, used, _, hh, hperm, hch, hpw, hnew => by
    simp only [List.head_cons] at hh
    subst hh
    have hv := hperm v List.mem_cons_self
    have hnot : used.contains (ciArr[encB 7 v]!) = false := by
      cases hc : used.contains (ciArr[encB 7 v]!)
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) (hnew v List.mem_cons_self)
    obtain ⟨hd, htl⟩ := List.isChain_cons_cons.mp hch
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.mp hpw
    have hnxt_v : nxtArr[encB 7 v]! = encB 7 v' := hnxt v v' hv hd
    have hnew' : ∀ w ∈ v' :: R', ciArr[encB 7 w]! ∉ ciArr[encB 7 v]! :: used := by
      intro w hw hm
      rcases List.mem_cons.mp hm with heq | hin
      · have hw' := hperm w (List.mem_cons_of_mem _ hw)
        rw [hci w hw', hci v hv] at heq
        have hrot := (PS.encB_enc 7 (by omega) (by omega)).ci_inj w v hw' hv heq
        exact hp1 w hw hrot.symm
      · exact hnew w (List.mem_cons_of_mem _ hw) hin
    obtain ⟨outUsed, hrec, hmem⟩ := placeRow_sound ciArr nxtArr hci hnxt (v' :: R') v'
      (ciArr[encB 7 v]! :: used) (List.cons_ne_nil _ _) rfl
      (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) htl hp2 hnew'
    refine ⟨outUsed, ?_, ?_⟩
    · simp only [List.length_cons, placeRow, hnot, Bool.false_eq_true, ite_false, hnxt_v]
      rw [List.getLast_cons (List.cons_ne_nil v' R')]
      exact hrec
    · intro c
      rw [hmem, List.mem_cons]
      constructor
      · rintro ((rfl | hu) | ⟨w, hw, rfl⟩)
        · exact Or.inr ⟨v, List.mem_cons_self, rfl⟩
        · exact Or.inl hu
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
      · rintro (hu | ⟨w, hw, rfl⟩)
        · exact Or.inl (Or.inr hu)
        · rcases List.mem_cons.mp hw with rfl | hw'
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨w, hw', rfl⟩

/-! ### `stateEdges` Completeness on Any Valid 4-Row `w3` Window -/

private theorem perms3_inj :
    ∀ a b : Fin 5, perms3NonId.getD a.val (0, 2, 1) = perms3NonId.getD b.val (0, 2, 1) → a = b := by
  decide

private theorem perms3_lt_fin :
    ∀ k : Fin 5, (perms3NonId.getD k.val (0, 2, 1)).1 < 3 ∧
      (perms3NonId.getD k.val (0, 2, 1)).2.1 < 3 ∧
      (perms3NonId.getD k.val (0, 2, 1)).2.2 < 3 := by
  decide

theorem stateEdges_mem {R0 R1 R2 R3 : TRow} {s3 ns3 : ℕ} {js : Bool}
    (hseq : IsSeq 7 [R0, R1, R2, R3])
    (hnoM3 : NoM3 [R0, R1, R2, R3])
    (hnoJS : js = true → NoJS 7 [R0, R1, R2, R3])
    (hm1 : matchesM3Idx R0 R1 R2 s3)
    (hm2 : matchesM3Idx R1 R2 R3 ns3) :
    (ns3, 6 - R3.2.length) ∈ stateEdges buildS7K16Tabs buildM3Allow js s3 := by
  have h0ne := hseq.pieces_ne R0 List.mem_cons_self
  have h1ne := hseq.pieces_ne R1 (by simp)
  have h2ne := hseq.pieces_ne R2 (by simp)
  have h3ne := hseq.pieces_ne R3 (by simp)
  have h0sz := hseq.size_le R0 List.mem_cons_self
  have h1sz := hseq.size_le R1 (by simp)
  have h2sz := hseq.size_le R2 (by simp)
  have h3sz := hseq.size_le R3 (by simp)
  have h0pos : 1 ≤ R0.2.length := List.length_pos_iff.mpr h0ne
  have h1pos : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
  have h2pos : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
  have h3pos : 1 ≤ R3.2.length := List.length_pos_iff.mpr h3ne
  obtain ⟨hR1k, hR2k, t0, t1, _, _, _, ht0, ht1, hh1, hh2, hs3_eq⟩ := hm1
  obtain ⟨_, hR3k, t1', t2, _, _, _, ht1', ht2, hh2', hh3, hns3_eq⟩ := hm2
  have ht1_eq : t1' = t1 := by
    have hstep_eq : w3Step (R1.2.getLast h1ne) t1' = w3Step (R1.2.getLast h1ne) t1 := by
      rw [← hh2', hh2]
    have hu := hseq.words R1 (by simp) _ (List.getLast_mem h1ne)
    have hrot := hu.rotate 6
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
    unfold w3Step at hstep_eq
    rw [he] at hstep_eq hrot
    have hnd := hrot.1
    have hi1 := perms3_lt_fin ⟨t1', ht1'⟩
    have hi2 := perms3_lt_fin ⟨t1, ht1⟩
    have hp_eq : perms3NonId.getD t1' (0, 2, 1) = perms3NonId.getD t1 (0, 2, 1) := by
      generalize perms3NonId.getD t1' (0, 2, 1) = p1 at hstep_eq hi1 ⊢
      generalize perms3NonId.getD t1 (0, 2, 1) = p2 at hstep_eq hi2 ⊢
      rcases p1 with ⟨a0, a1, a2⟩; rcases p2 with ⟨b0, b1, b2⟩
      dsimp only at hstep_eq hi1 hi2 ⊢
      injection hstep_eq with _ hstep_eq; injection hstep_eq with _ hstep_eq
      injection hstep_eq with _ hstep_eq; injection hstep_eq with _ hstep_eq
      injection hstep_eq with ha0 hstep_eq; injection hstep_eq with ha1 hstep_eq
      injection hstep_eq with ha2 _
      have hge : ∀ i j : ℕ, i < 3 → j < 3 →
          [e0, e1, e2, e3, e4, e5, e6][i]! = [e0, e1, e2, e3, e4, e5, e6][j]! → i = j := by
        intro i j hi hj hget
        have h1 : i < [e0, e1, e2, e3, e4, e5, e6].length := by simp; omega
        have h2 : j < [e0, e1, e2, e3, e4, e5, e6].length := by simp; omega
        rw [getElem!_pos _ i h1, getElem!_pos _ j h2] at hget
        exact (hnd.getElem_inj_iff (hi := h1) (hj := h2)).mp hget
      rw [hge a0 b0 hi1.1 hi2.1 ha0, hge a1 b1 hi1.2.1 hi2.2.1 ha1, hge a2 b2 hi1.2.2 hi2.2.2 ha2]
    exact congrArg Fin.val (perms3_inj ⟨t1', ht1'⟩ ⟨t1, ht1⟩ hp_eq)
  rw [ht1_eq] at hns3_eq
  have hm3_s3 : buildM3Allow.get! s3 ≠ 0 :=
    hnoM3 [] R0 R1 R2 [R3] s3 rfl ⟨hR1k, hR2k, t0, t1, h0ne, h1ne, h2ne, ht0, ht1, hh1, hh2, hs3_eq⟩
  have hm3_ns3 : buildM3Allow.get! ns3 ≠ 0 :=
    hnoM3 [R0] R1 R2 R3 [] ns3 rfl ⟨hR2k, hR3k, t1, t2, h1ne, h2ne, h3ne, ht1, ht2, hh2, hh3, hns3_eq⟩
  set v0 := R0.2.head h0ne
  have hv0 : PermW 7 v0 := hseq.words R0 List.mem_cons_self v0 (List.head_mem h0ne)
  have hL1 := hseq.relabel hv0
  set Q0 := R0.2.map (List.map (S.relab v0))
  set Q1 := R1.2.map (List.map (S.relab v0))
  set Q2 := R2.2.map (List.map (S.relab v0))
  set Q3 := R3.2.map (List.map (S.relab v0))
  have hQ0ne : Q0 ≠ [] := by simpa [Q0] using h0ne
  have hQ1ne : Q1 ≠ [] := by simpa [Q1] using h1ne
  have hQ2ne : Q2 ≠ [] := by simpa [Q2] using h2ne
  have hQ3ne : Q3 ≠ [] := by simpa [Q3] using h3ne
  have hQ0len : Q0.length = R0.2.length := List.length_map _
  have hQ1len : Q1.length = R1.2.length := List.length_map _
  have hQ2len : Q2.length = R2.2.length := List.length_map _
  have hQ3len : Q3.length = R3.2.length := List.length_map _
  have hQ0hd : Q0.head hQ0ne = id7 := by
    simp only [Q0, List.head_map]
    exact (S.map_relab_self hv0.1).trans (by rw [hv0.2.1]; rfl)
  have hQ1hd : Q1.head hQ1ne = w3Step (Q0.getLast hQ0ne) t0 := by
    simp only [Q0, Q1, List.head_map, List.getLast_map]
    rw [hh1, w3Step_map _ (hseq.words R0 List.mem_cons_self _ (List.getLast_mem h0ne)).2.1]
  have hQ2hd : Q2.head hQ2ne = w3Step (Q1.getLast hQ1ne) t1 := by
    simp only [Q1, Q2, List.head_map, List.getLast_map]
    rw [hh2, w3Step_map _ (hseq.words R1 (by simp) _ (List.getLast_mem h1ne)).2.1]
  have hQ3hd : Q3.head hQ3ne = w3Step (Q2.getLast hQ2ne) t2 := by
    simp only [Q2, Q3, List.head_map, List.getLast_map]
    rw [hh3, w3Step_map _ (hseq.words R2 (by simp) _ (List.getLast_mem h2ne)).2.1]
  have hcl := hL1.classes
  simp only [relabSeq, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.pairwise_append] at hcl
  obtain ⟨hP0, ⟨hP1, ⟨hP2, hP3, hP23⟩, hP123⟩, hP0123⟩ := hcl
  have hW0 : ∀ w ∈ Q0, PermW 7 w := hL1.words _ List.mem_cons_self
  have hW1 : ∀ w ∈ Q1, PermW 7 w := hL1.words _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hW2 : ∀ w ∈ Q2, PermW 7 w := hL1.words _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hW3 : ∀ w ∈ Q3, PermW 7 w := hL1.words _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hD0 := S.door_chain (by omega) _ hW0 (hL1.doors _ List.mem_cons_self) hP0
  have hD1 := S.door_chain (by omega) _ hW1 (hL1.doors _ (List.mem_cons_of_mem _ List.mem_cons_self)) hP1
  have hD2 := S.door_chain (by omega) _ hW2 (hL1.doors _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) hP2
  have hD3 := S.door_chain (by omega) _ hW3 (hL1.doors _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hP3
  have hst : buildS7K16Tabs.st.toNat = encB 7 id7 := by
    have hlt := encB_lt id7_permW
    have hle := permCodes7_length_le
    have hsteq : (PS.permCodes 7 7).idxOf (PS.idcF 7) = encB 7 id7 :=
      (PS.encB_enc 7 (by omega) (by omega)).st_eq
    change (UInt32.ofNat ((PS.permCodes 7 7).idxOf (PS.idcF 7))).toNat = encB 7 id7
    rw [hsteq, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hci_eq : ∀ w, PermW 7 w → buildS7K16Tabs.ciArr[encB 7 w]! = (ciTab 7 (PS.permCodes 7 7))[encB 7 w]! :=
    fun _ _ => congrArg (fun a => a[_]!) tabs_ciArr_eq
  have hnxt_eq : ∀ a b, PermW 7 a → DoorEq 7 a b → buildS7K16Tabs.nxtArr[encB 7 a]! = encB 7 b :=
    fun a b ha hab => by rw [tabs_nxtArr_eq]; exact (PS.encB_enc 7 (by omega) (by omega)).nxt_eq a b ha hab
  obtain ⟨u0, hpr0, hu0⟩ := placeRow_sound buildS7K16Tabs.ciArr buildS7K16Tabs.nxtArr hci_eq hnxt_eq
    Q0 id7 [] hQ0ne hQ0hd hW0 hD0 hP0 (by simp)
  have hnot1 : ∀ w ∈ Q1, buildS7K16Tabs.ciArr[encB 7 w]! ∉ u0 := by
    intro w hw hm
    rcases (hu0 _).mp hm with hnil | ⟨a, ha, heq⟩
    · simp at hnil
    · rw [hci_eq w (hW1 w hw), hci_eq a (hW0 a ha)] at heq
      exact hP0123 a ha w (List.mem_append_left _ hw)
        ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW0 a ha) (hW1 w hw) heq.symm)
  obtain ⟨u1, hpr1, hu1⟩ := placeRow_sound buildS7K16Tabs.ciArr buildS7K16Tabs.nxtArr hci_eq hnxt_eq
    Q1 (w3Step (Q0.getLast hQ0ne) t0) u0 hQ1ne hQ1hd hW1 hD1 hP1 hnot1
  have hnot2 : ∀ w ∈ Q2, buildS7K16Tabs.ciArr[encB 7 w]! ∉ u1 := by
    intro w hw hm
    rcases (hu1 _).mp hm with hin0 | ⟨a, ha, heq⟩
    · rcases (hu0 _).mp hin0 with hnil | ⟨a, ha, heq⟩
      · simp at hnil
      · rw [hci_eq w (hW2 w hw), hci_eq a (hW0 a ha)] at heq
        exact hP0123 a ha w (List.mem_append_right _ (List.mem_append_left _ hw))
          ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW0 a ha) (hW2 w hw) heq.symm)
    · rw [hci_eq w (hW2 w hw), hci_eq a (hW1 a ha)] at heq
      exact hP123 a ha w (List.mem_append_left _ hw)
        ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW1 a ha) (hW2 w hw) heq.symm)
  obtain ⟨u2, hpr2, hu2⟩ := placeRow_sound buildS7K16Tabs.ciArr buildS7K16Tabs.nxtArr hci_eq hnxt_eq
    Q2 (w3Step (Q1.getLast hQ1ne) t1) u1 hQ2ne hQ2hd hW2 hD2 hP2 hnot2
  have hnot3 : ∀ w ∈ Q3, buildS7K16Tabs.ciArr[encB 7 w]! ∉ u2 := by
    intro w hw hm
    rcases (hu2 _).mp hm with hin1 | ⟨a, ha, heq⟩
    · rcases (hu1 _).mp hin1 with hin0 | ⟨a, ha, heq⟩
      · rcases (hu0 _).mp hin0 with hnil | ⟨a, ha, heq⟩
        · simp at hnil
        · rw [hci_eq w (hW3 w hw), hci_eq a (hW0 a ha)] at heq
          exact hP0123 a ha w (List.mem_append_right _ (List.mem_append_right _ hw))
            ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW0 a ha) (hW3 w hw) heq.symm)
      · rw [hci_eq w (hW3 w hw), hci_eq a (hW1 a ha)] at heq
        exact hP123 a ha w (List.mem_append_right _ hw)
          ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW1 a ha) (hW3 w hw) heq.symm)
    · rw [hci_eq w (hW3 w hw), hci_eq a (hW2 a ha)] at heq
      exact hP23 a ha w hw
        ((PS.encB_enc 7 (by omega) (by omega)).ci_inj a w (hW2 a ha) (hW3 w hw) heq.symm)
  obtain ⟨u3, hpr3, _⟩ := placeRow_sound buildS7K16Tabs.ciArr buildS7K16Tabs.nxtArr hci_eq hnxt_eq
    Q3 (w3Step (Q2.getLast hQ2ne) t2) u2 hQ3ne hQ3hd hW3 hD3 hP3 hnot3
  have hjs_ok : ∀ (U : List TRow) (A B : TRow) (W : List TRow),
      [R0, R1, R2, R3] = U ++ A :: B :: W →
      ∀ (hA : A.2 ≠ []) (hB : B.2 ≠ []),
      let eA := (A.2.getLast hA).map (S.relab v0)
      let fB := (B.2.head hB).map (S.relab v0)
      (js && buildS7K16Tabs.ciArr[encB 7 fB]! == buildS7K16Tabs.ciArr[buildS7K16Tabs.nxtArr[encB 7 eA]!]! &&
        decide (B.2.length ≥ 2)) = false := by
    intro U A B W hsplit hA hB
    cases hjs : js
    · rfl
    · simp only [Bool.true_and, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      by_cases hlen : B.2.length ≥ 2
      · left
        intro hci_eq
        have hno := hnoJS hjs
        have hA_mem : A ∈ [R0, R1, R2, R3] := by rw [hsplit]; simp
        have hB_mem : B ∈ [R0, R1, R2, R3] := by rw [hsplit]; simp
        have heA_p : PermW 7 ((A.2.getLast hA).map (S.relab v0)) :=
          hv0.map_relab (hseq.words A hA_mem _ (List.getLast_mem hA))
        have hfB_p : PermW 7 ((B.2.head hB).map (S.relab v0)) :=
          hv0.map_relab (hseq.words B hB_mem _ (List.head_mem hB))
        have hnxt := (PS.encB_enc 7 (by omega) (by omega)).nxt_eq _ (tau2 7 _) heA_p rfl
        rw [tabs_ciArr_eq, tabs_nxtArr_eq, hnxt] at hci_eq
        have hrot := (PS.encB_enc 7 (by omega) (by omega)).ci_inj _ _ hfB_p (permW_tau2 (by omega) heA_p) hci_eq
        rw [K16.tau2_map (by omega) _ (hseq.words A hA_mem _ (List.getLast_mem hA)).2.1] at hrot
        have hrot0 : B.2.head hB ~r tau2 7 (A.2.getLast hA) := by
          by_contra hnr
          exact S.not_isRotated_map_relab hv0 (hseq.words B hB_mem _ (List.head_mem hB))
            (permW_tau2 (by omega) (hseq.words A hA_mem _ (List.getLast_mem hA))) hnr hrot
        obtain ⟨b0, b1, bs, hb⟩ : ∃ b0 b1 bs, B.2 = b0 :: b1 :: bs := by
          match hb : B.2, hlen with
          | b0 :: b1 :: bs, _ => exact ⟨b0, b1, bs, rfl⟩
        have hhd_eq : B.2.head hB = b0 := by simp [hb]
        rw [hhd_eq] at hrot0
        exact hno U A B W hsplit ⟨hA, b0, b1, bs, hb, hrot0⟩
      · right; exact hlen
  have hQ0l : (R0.2.getLast h0ne).map (S.relab v0) = Q0.getLast hQ0ne := (List.getLast_map _).symm
  have hQ1h : (R1.2.head h1ne).map (S.relab v0) = w3Step (Q0.getLast hQ0ne) t0 :=
    (List.head_map _).symm.trans hQ1hd
  have hQ1l : (R1.2.getLast h1ne).map (S.relab v0) = Q1.getLast hQ1ne := (List.getLast_map _).symm
  have hQ2h : (R2.2.head h2ne).map (S.relab v0) = w3Step (Q1.getLast hQ1ne) t1 :=
    (List.head_map _).symm.trans hQ2hd
  have hQ2l : (R2.2.getLast h2ne).map (S.relab v0) = Q2.getLast hQ2ne := (List.getLast_map _).symm
  have hQ3h : (R3.2.head h3ne).map (S.relab v0) = w3Step (Q2.getLast hQ2ne) t2 :=
    (List.head_map _).symm.trans hQ3hd
  have hjs0 := hjs_ok [] R0 R1 [R2, R3] rfl h0ne h1ne
  have hjs1 := hjs_ok [R0] R1 R2 [R3] rfl h1ne h2ne
  have hjs2 := hjs_ok [R0, R1] R2 R3 [] rfl h2ne h3ne
  dsimp only at hjs0 hjs1 hjs2
  rw [hQ0l, hQ1h] at hjs0
  rw [hQ1l, hQ2h] at hjs1
  rw [hQ2l, hQ3h] at hjs2
  have hd_l2 : s3 % 6 + 1 = R2.2.length := by omega
  have hd_t1 : s3 / 6 % 5 = t1 := by omega
  have hd_l1 : s3 / 6 / 5 % 6 + 1 = R1.2.length := by omega
  have hd_t0 : s3 / 6 / 5 / 6 % 5 = t0 := by omega
  have hd_l0 : s3 / 6 / 5 / 6 / 5 + 1 = R0.2.length := by omega
  have hs3_0 : (buildM3Allow.get! s3 == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hm3_s3
  have hns3_0 : (buildM3Allow.get! ns3 == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hm3_ns3
  have hs3_n1 : (buildS7K16Tabs.s3Arr[encB 7 (Q0.getLast hQ0ne) * 5 + t0]!).toNat =
      encB 7 (w3Step (Q0.getLast hQ0ne) t0) :=
    tabs_s3Arr_get (hW0 _ (List.getLast_mem hQ0ne)) ht0
  have hs3_n2 : (buildS7K16Tabs.s3Arr[encB 7 (Q1.getLast hQ1ne) * 5 + t1]!).toNat =
      encB 7 (w3Step (Q1.getLast hQ1ne) t1) :=
    tabs_s3Arr_get (hW1 _ (List.getLast_mem hQ1ne)) ht1
  have hs3_n3 : (buildS7K16Tabs.s3Arr[encB 7 (Q2.getLast hQ2ne) * 5 + t2]!).toNat =
      encB 7 (w3Step (Q2.getLast hQ2ne) t2) :=
    tabs_s3Arr_get (hW2 _ (List.getLast_mem hQ2ne)) ht2
  unfold stateEdges
  simp only [hs3_0, Bool.false_eq_true, ite_false, hd_l2, hd_t1, hd_l1, hd_t0, hd_l0, hst,
    ← hQ0len, hpr0, hs3_n1]
  rw [hjs0]
  simp only [Bool.false_eq_true, ite_false, ← hQ1len, hpr1, hs3_n2]
  rw [hjs1]
  simp only [Bool.false_eq_true, ite_false, ← hQ2len, hpr2]
  have hR3m1_lt : R3.2.length - 1 < 6 := by omega
  refine List.mem_flatMap.mpr ⟨t2, List.mem_range.mpr ht2,
    List.mem_filterMap.mpr ⟨R3.2.length - 1, List.mem_range.mpr hR3m1_lt, ?_⟩⟩
  have hl3_eq : R3.2.length - 1 + 1 = R3.2.length := by omega
  have hns3_calc : ((R1.2.length - 1) * 30 + t1 * 6 + (R2.2.length - 1)) * 30 + t2 * 6 + (R3.2.length - 1) = ns3 := by
    omega
  simp only [hs3_n3, hl3_eq]
  rw [hjs2]
  simp only [Bool.false_eq_true, ite_false, ← hQ3len, hpr3]
  rw [hQ1len, hQ2len, hQ3len, hns3_calc, hns3_0]
  rfl

/-! ### Pure `iterN` GFP Soundness for `buildU3Rows` and `buildU3MinR` -/

/-- Row `row` (length `5400`) is a sound upper bound at holes `y` for all pure-`w3` suffixes
    of length `≤ maxLen` following any 3 `w3`-rows `(R0, R1, R2)` in state `s3`. -/
def SoundU3Row (maxLen : ℕ) (js : Bool) (y : ℕ) (row : Array ℕ) : Prop :=
  row.size = 5400 ∧
  ∀ (R0 R1 R2 : TRow) (rest : List TRow) (s3 : ℕ),
    rest.length ≤ maxLen →
    IsSeq 7 (R0 :: R1 :: R2 :: rest) →
    NoM3 (R0 :: R1 :: R2 :: rest) →
    (js = true → NoJS 7 (R0 :: R1 :: R2 :: rest)) →
    (∀ r ∈ rest, r.1 = 0) →
    holesT 7 rest = y →
    matchesM3Idx R0 R1 R2 s3 →
    rest.length ≤ row[s3]!

private theorem foldl_max_ge_elem {α : Type} (l : List α) (f : α → ℕ) (init : ℕ) :
    ∀ x ∈ l, f x ≤ l.foldl (fun acc a => max acc (f a)) init := by
  have hge_init : ∀ (m : List α) (acc : ℕ), acc ≤ m.foldl (fun a b => max a (f b)) acc := by
    intro m; induction m with
    | nil => intro acc; exact le_rfl
    | cons b t ih => intro acc; exact (le_max_left acc (f b)).trans (ih _)
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact (le_max_right init (f x)).trans (hge_init t _)
    · exact ih (max init (f a)) x hxt

private theorem array_push_get_eq {α : Type} [Inhabited α] (a : Array α) (x : α) (k : ℕ)
    (hk : k = a.size) : (a.push x)[k]! = x := by
  subst hk
  have hlt : a.size < (a.push x).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.push x) a.size hlt]
  exact Array.getElem_push_eq

private theorem array_push_get_lt {α : Type} [Inhabited α] (a : Array α) (x : α) (k : ℕ)
    (hk : k < a.size) : (a.push x)[k]! = a[k]! := by
  have hlt : k < (a.push x).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.push x) k hlt, Array.getElem_push_lt hk, getElem!_pos a k hk]

theorem relaxRow_sound (maxLen : ℕ) (js : Bool) (y : ℕ)
    (adj : Array (List (ℕ × ℕ)))
    (hadj : ∀ s < 5400, adj[s]! = stateEdges buildS7K16Tabs buildM3Allow js s)
    (prevRows : Array (Array ℕ)) (hprev_sz : prevRows.size = y)
    (hprev : ∀ y' < y, SoundU3Row maxLen js y' prevRows[y']!)
    (cur : Array ℕ) (hcur : SoundU3Row maxLen js y cur) :
    SoundU3Row maxLen js y (relaxRow adj prevRows y cur) := by
  refine ⟨by simp [relaxRow], ?_⟩
  intro R0 R1 R2 rest s3 hml hseq hnoM3 hnoJS hw3 hholes hm1
  have hs3_lt : s3 < 5400 := by
    obtain ⟨_, _, t0, t1, h0ne, h1ne, h2ne, ht0, ht1, _, _, heq⟩ := hm1
    have := hseq.size_le R0 List.mem_cons_self
    have := hseq.size_le R1 (by simp)
    have := hseq.size_le R2 (by simp)
    have : 1 ≤ R0.2.length := List.length_pos_iff.mpr h0ne
    have : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
    have : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
    omega
  unfold relaxRow
  rw [getElem!_pos _ s3 (by simp [hs3_lt]), Array.getElem_ofFn]
  dsimp only
  refine le_min (hcur.2 R0 R1 R2 rest s3 hml hseq hnoM3 hnoJS hw3 hholes hm1) ?_
  cases rest with
  | nil => exact Nat.zero_le _
  | cons R3 rest' =>
    have hR3k : R3.1 = 0 := hw3 R3 List.mem_cons_self
    have h2ne := hseq.pieces_ne R2 (by simp)
    have h3ne := hseq.pieces_ne R3 (by simp)
    have h1ne := hseq.pieces_ne R1 (by simp)
    have hinf23 : IsSeq 7 [R2, R3] := hseq.infix ⟨[R0, R1], rest', by simp⟩
    have hlink23 : WLink 7 3 (R2.2.getLast h2ne) (R3.2.head h3ne) :=
      ((List.isChain_cons_cons.mp hinf23.links).1 h2ne h3ne).1 hR3k
    have hrot23 : ¬ R2.2.getLast h2ne ~r R3.2.head h3ne := by
      have hcl2 := hinf23.classes
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.pairwise_append] at hcl2
      exact hcl2.2.2 _ (List.getLast_mem h2ne) _ (List.head_mem h3ne)
    obtain ⟨t2, ht2, hh3⟩ := w3Step_complete (hseq.words R2 (by simp) _ (List.getLast_mem h2ne))
      (hseq.words R3 (by simp) _ (List.head_mem h3ne)) hlink23 hrot23
    have hm1_copy := hm1
    obtain ⟨_, hR2k, _, t1, _, _, _, _, ht1, _, hh2, _⟩ := hm1
    set ns3 := ((R1.2.length - 1) * 30 + t1 * 6 + (R2.2.length - 1)) * 30 + t2 * 6 + (R3.2.length - 1)
    have hm2 : matchesM3Idx R1 R2 R3 ns3 :=
      ⟨hR2k, hR3k, t1, t2, h1ne, h2ne, h3ne, ht1, ht2, hh2, hh3, rfl⟩
    have h4seq : IsSeq 7 [R0, R1, R2, R3] := hseq.infix ⟨[], rest', by simp⟩
    have h4M3 : NoM3 [R0, R1, R2, R3] := fun U A B C W idx heq hm =>
      hnoM3 U A B C (W ++ rest') idx (by rw [show R0 :: R1 :: R2 :: R3 :: rest' = [R0, R1, R2, R3] ++ rest' from rfl, heq]; simp) hm
    have h4JS : js = true → NoJS 7 [R0, R1, R2, R3] := fun hj U A B W heq hbad =>
      hnoJS hj U A B (W ++ rest') (by rw [show R0 :: R1 :: R2 :: R3 :: rest' = [R0, R1, R2, R3] ++ rest' from rfl, heq]; simp) hbad
    have hedge : (ns3, 6 - R3.2.length) ∈ adj[s3]! := by
      rw [hadj s3 hs3_lt]
      exact stateEdges_mem h4seq h4M3 h4JS hm1_copy hm2
    have htail_seq : IsSeq 7 (R1 :: R2 :: R3 :: rest') := hseq.infix ⟨[R0], [], by simp⟩
    have htail_M3 : NoM3 (R1 :: R2 :: R3 :: rest') := fun U A B C W idx heq hm =>
      hnoM3 (R0 :: U) A B C W idx (by simp [heq]) hm
    have htail_JS : js = true → NoJS 7 (R1 :: R2 :: R3 :: rest') := fun hj U A B W heq hbad =>
      hnoJS hj (R0 :: U) A B W (by simp [heq]) hbad
    have htail_w3 : ∀ r ∈ rest', r.1 = 0 := fun r hr => hw3 r (List.mem_cons_of_mem _ hr)
    have hholes_split : (6 - R3.2.length) + holesT 7 rest' = y := by
      simpa [holesT] using hholes
    have hfold := foldl_max_ge_elem adj[s3]! (fun (ns, h) =>
      if h == 0 then 1 + cur[ns]!
      else if h <= y then 1 + (prevRows[y - h]!)[ns]!
      else 0) 0 (ns3, 6 - R3.2.length) hedge
    have hfold_eq : (adj[s3]!).foldl (fun acc (ns, h) =>
        if h == 0 then max acc (1 + cur[ns]!)
        else if h <= y then max acc (1 + (prevRows[y - h]!)[ns]!)
        else acc) 0 =
        (adj[s3]!).foldl (fun acc p => max acc (
          if p.2 == 0 then 1 + cur[p.1]!
          else if p.2 <= y then 1 + (prevRows[y - p.2]!)[p.1]!
          else 0)) 0 := by
      have hgen : ∀ (l : List (ℕ × ℕ)) (init : ℕ),
          l.foldl (fun acc (ns, h) =>
            if h == 0 then max acc (1 + cur[ns]!)
            else if h <= y then max acc (1 + (prevRows[y - h]!)[ns]!)
            else acc) init =
          l.foldl (fun acc p => max acc (
            if p.2 == 0 then 1 + cur[p.1]!
            else if p.2 <= y then 1 + (prevRows[y - p.2]!)[p.1]!
            else 0)) init := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons p t ih =>
          intro init
          simp only [List.foldl_cons]
          by_cases h0 : p.2 = 0
          · simp only [h0, beq_self_eq_true, ite_true]; exact ih _
          · have h0f : (p.2 == 0) = false := beq_false_of_ne h0
            simp only [h0f, Bool.false_eq_true, ite_false]
            by_cases hle : p.2 ≤ y
            · simp only [hle, ite_true]; exact ih _
            · simp only [hle, ite_false, Nat.max_zero]; exact ih _
      exact hgen _ 0
    rw [hfold_eq]
    by_cases hh0 : 6 - R3.2.length = 0
    · have hy' : holesT 7 rest' = y := by omega
      have hlen' := hcur.2 R1 R2 R3 rest' ns3 (by simp at hml; omega) htail_seq htail_M3 htail_JS
        htail_w3 hy' hm2
      simp only [hh0, beq_self_eq_true, ite_true] at hfold
      simp only [List.length_cons]
      omega
    · have hhy : 6 - R3.2.length ≤ y := by omega
      have hy' : holesT 7 rest' = y - (6 - R3.2.length) := by omega
      have hlen' := (hprev (y - (6 - R3.2.length)) (by omega)).2 R1 R2 R3 rest' ns3
        (by simp at hml; omega) htail_seq htail_M3 htail_JS htail_w3 hy' hm2
      have h0f : (6 - R3.2.length == 0) = false := beq_false_of_ne hh0
      simp only [h0f, Bool.false_eq_true, ite_false, hhy, ite_true] at hfold
      simp only [List.length_cons]
      omega

theorem iterN_preserves {α : Type} (P : α → Prop) (f : α → α) (hf : ∀ x, P x → P (f x)) :
    ∀ n x, P x → P (iterN f n x)
  | 0, _, hx => hx
  | n + 1, x, hx => iterN_preserves P f hf n (f x) (hf x hx)

theorem buildU3Rows_sound (maxLen : ℕ) (P0 : ℕ → ℕ) (js : Bool)
    (adj : Array (List (ℕ × ℕ)))
    (hadj : ∀ s < 5400, adj[s]! = stateEdges buildS7K16Tabs buildM3Allow js s) :
    ∀ hi : ℕ,
      (∀ rest : List TRow, rest.length ≤ maxLen → IsSeq 7 rest → (∀ x ∈ rest, x.1 ≤ 1) →
        linksT rest = 0 → ∀ y ≤ hi, holesT 7 rest = y → rest.length ≤ P0 y) →
      (buildU3Rows adj P0 hi).size = hi + 1 ∧
      ∀ y ≤ hi, SoundU3Row maxLen js y (buildU3Rows adj P0 hi)[y]!
  | 0, hcap0 => by
    have hinit : SoundU3Row maxLen js 0 (Array.replicate 5400 (P0 0)) := by
      refine ⟨Array.size_replicate, ?_⟩
      intro R0 R1 R2 rest s3 hml hseq _ _ hw3 hholes hm1
      have hs3_lt : s3 < 5400 := by
        obtain ⟨_, _, t0, t1, h0ne, h1ne, h2ne, ht0, ht1, _, _, heq⟩ := hm1
        have := hseq.size_le R0 List.mem_cons_self; have := hseq.size_le R1 (by simp)
        have := hseq.size_le R2 (by simp)
        have : 1 ≤ R0.2.length := List.length_pos_iff.mpr h0ne
        have : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
        have : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
        omega
      rw [getElem!_pos _ s3 (by simp [hs3_lt]), Array.getElem_replicate]
      have hrest_seq : IsSeq 7 rest := hseq.infix ⟨[R0, R1, R2], [], by simp⟩
      have hrest_lk : linksT rest = 0 := by
        cases rest with
        | nil => rfl
        | cons a t =>
          simp only [linksT, List.tail_cons, List.countP_eq_zero]
          intro x hx; simp [hw3 x (List.mem_cons_of_mem _ hx)]
      exact hcap0 rest hml hrest_seq (fun x hx => by rw [hw3 x hx]; omega) hrest_lk 0 le_rfl hholes
    have hiter := iterN_preserves (SoundU3Row maxLen js 0) (relaxRow adj #[] 0)
      (fun cur hc => relaxRow_sound maxLen js 0 adj hadj #[] rfl (fun _ h => absurd h (Nat.not_lt_zero _)) cur hc)
      15 (Array.replicate 5400 (P0 0)) hinit
    refine ⟨rfl, fun y hy => ?_⟩
    have hy0 : y = 0 := by omega
    subst hy0
    simpa [buildU3Rows] using hiter
  | y + 1, hcap0 => by
    obtain ⟨hpsz, hp⟩ := buildU3Rows_sound maxLen P0 js adj hadj y
      (fun r hm h1 h2 h3 y' hy' => hcap0 r hm h1 h2 h3 y' (by omega))
    have hinit : SoundU3Row maxLen js (y + 1) (Array.replicate 5400 (P0 (y + 1))) := by
      refine ⟨Array.size_replicate, ?_⟩
      intro R0 R1 R2 rest s3 hml hseq _ _ hw3 hholes hm1
      have hs3_lt : s3 < 5400 := by
        obtain ⟨_, _, t0, t1, h0ne, h1ne, h2ne, ht0, ht1, _, _, heq⟩ := hm1
        have := hseq.size_le R0 List.mem_cons_self; have := hseq.size_le R1 (by simp)
        have := hseq.size_le R2 (by simp)
        have : 1 ≤ R0.2.length := List.length_pos_iff.mpr h0ne
        have : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
        have : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
        omega
      rw [getElem!_pos _ s3 (by simp [hs3_lt]), Array.getElem_replicate]
      have hrest_seq : IsSeq 7 rest := hseq.infix ⟨[R0, R1, R2], [], by simp⟩
      have hrest_lk : linksT rest = 0 := by
        cases rest with
        | nil => rfl
        | cons a t =>
          simp only [linksT, List.tail_cons, List.countP_eq_zero]
          intro x hx; simp [hw3 x (List.mem_cons_of_mem _ hx)]
      exact hcap0 rest hml hrest_seq (fun x hx => by rw [hw3 x hx]; omega) hrest_lk (y + 1) le_rfl hholes
    have hiter := iterN_preserves (SoundU3Row maxLen js (y + 1)) (relaxRow adj (buildU3Rows adj P0 y) (y + 1))
      (fun cur hc => relaxRow_sound maxLen js (y + 1) adj hadj (buildU3Rows adj P0 y) hpsz
        (fun y' hy' => hp y' (by omega)) cur hc)
      20 (Array.replicate 5400 (P0 (y + 1))) hinit
    set newRow := iterN (relaxRow adj (buildU3Rows adj P0 y) (y + 1)) 20 (Array.replicate 5400 (P0 (y + 1)))
    refine ⟨by change ((buildU3Rows adj P0 y).push newRow).size = y + 2; rw [Array.size_push, hpsz], fun y' hy' => ?_⟩
    by_cases hlt : y' < y + 1
    · change SoundU3Row maxLen js y' (((buildU3Rows adj P0 y).push newRow)[y']!)
      rw [array_push_get_lt _ _ y' (by omega)]
      exact hp y' (by omega)
    · have heq : y' = y + 1 := by omega
      subst heq
      change SoundU3Row maxLen js (y + 1) (((buildU3Rows adj P0 y).push newRow)[y + 1]!)
      rw [array_push_get_eq _ _ (y + 1) hpsz.symm]
      exact hiter

private theorem foldl_min_le_elem {α : Type} (l : List α) (f : α → ℕ) (init : ℕ) :
    (∀ x ∈ l, l.foldl (fun acc a => min acc (f a)) init ≤ f x) ∧
    l.foldl (fun acc a => min acc (f a)) init ≤ init := by
  have hle_init : ∀ (m : List α) (acc : ℕ), m.foldl (fun a b => min a (f b)) acc ≤ acc := by
    intro m; induction m with
    | nil => intro acc; exact le_rfl
    | cons b t ih => intro acc; exact (ih _).trans (min_le_left acc (f b))
  refine ⟨?_, hle_init l init⟩
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact (hle_init t _).trans (min_le_right init (f x))
    · exact ih (min init (f a)) x hxt

private theorem array_ofFn_get! {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  have hlt : i < (Array.ofFn f).size := by rw [Array.size_ofFn]; exact hi
  rw [getElem!_pos (Array.ofFn f) i hlt, Array.getElem_ofFn]

/-- **Soundness of `buildU3MinR`:**
If `R0, R1, R2` end a prefix of `nr` rows and `nd` holes (`nd ≤ x`, `lo ≤ x ≤ hi`, `x < 256`),
followed by a pure-`w3` suffix `rest` with `holesT 7 rest = x - nd` and `nr + rest.length > Ps x`,
then `nr > (baGetU8 (buildU3MinR ...) (nd * 5400 + ns3)).toNat`! -/
theorem u3MinR_lt_nr {maxLen lo hi nd nr ns3 x : ℕ} {P0 Ps : ℕ → ℕ} {js : Bool}
    {R0 R1 R2 : TRow} {rest : List TRow}
    (hhi : hi < 200) (hnr : 0 < nr)
    (hlo_x : lo ≤ x) (hx_hi : x ≤ hi) (hnd_x : nd ≤ x) (hns3_lt : ns3 < 5400)
    (hcap0 : ∀ rest' : List TRow, rest'.length ≤ maxLen → IsSeq 7 rest' → (∀ w ∈ rest', w.1 ≤ 1) →
      linksT rest' = 0 → ∀ y ≤ hi, holesT 7 rest' = y → rest'.length ≤ P0 y)
    (hml : rest.length ≤ maxLen)
    (hseq : IsSeq 7 (R0 :: R1 :: R2 :: rest))
    (hnoM3 : NoM3 (R0 :: R1 :: R2 :: rest))
    (hnoJS : js = true → NoJS 7 (R0 :: R1 :: R2 :: rest))
    (hw3 : ∀ r ∈ rest, r.1 = 0)
    (hholes : holesT 7 rest = x - nd)
    (hm : matchesM3Idx R0 R1 R2 ns3)
    (hgt : Ps x < nr + rest.length) :
    (FastK16.baGetU8 (buildU3MinR buildS7K16Tabs buildM3Allow P0 Ps lo hi js)
      (USize.ofNat (nd * 5400 + ns3))).toNat < nr := by
  have hallow : buildM3Allow.get! ns3 ≠ 0 :=
    hnoM3 [] R0 R1 R2 rest ns3 rfl hm
  have hallow_f : (buildM3Allow.get! ns3 == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hallow
  set adj := Array.ofFn (n := 5400) fun s => stateEdges buildS7K16Tabs buildM3Allow js s.val
  have hadj : ∀ s < 5400, adj[s]! = stateEdges buildS7K16Tabs buildM3Allow js s :=
    fun s hs => array_ofFn_get! (fun k : Fin 5400 => stateEdges buildS7K16Tabs buildM3Allow js k.val) s hs
  set rows := buildU3Rows adj P0 hi
  obtain ⟨_, hrows⟩ := buildU3Rows_sound maxLen P0 js adj hadj hi hcap0
  have hcap : rest.length ≤ (rows[x - nd]!)[ns3]! :=
    (hrows (x - nd) (by omega)).2 R0 R1 R2 rest ns3 hml hseq hnoM3 hnoJS hw3 hholes hm
  have hidx_lt : nd * 5400 + ns3 < (hi + 1) * 5400 := by omega
  have hsz_lt : (hi + 1) * 5400 < 2 ^ 32 := by omega
  unfold buildU3MinR
  dsimp only
  rw [baGetU8_ofFn _ hsz_lt hidx_lt]
  dsimp only
  have hdiv : (nd * 5400 + ns3) / 5400 = nd := by omega
  have hmod : (nd * 5400 + ns3) % 5400 = ns3 := by omega
  rw [hdiv, hmod, hallow_f, ite_eq_right (by decide)]
  set xStart := max lo nd
  have hoff_in : x - xStart ∈ List.range (hi + 1 - xStart) := List.mem_range.mpr (by omega)
  have hx_eq : xStart + (x - xStart) = x := by omega
  obtain ⟨hle_elem, hle_255⟩ := foldl_min_le_elem (List.range (hi + 1 - xStart))
    (fun off => Ps (xStart + off) - (rows[xStart + off - nd]!)[ns3]!) 255
  have hbest_le : (List.range (hi + 1 - xStart)).foldl
      (fun acc off => min acc (Ps (xStart + off) - (rows[xStart + off - nd]!)[ns3]!)) 255 ≤
      Ps x - (rows[x - nd]!)[ns3]! := by
    have h1 := hle_elem (x - xStart) hoff_in
    rwa [hx_eq] at h1
  change (UInt8.ofNat ((List.range (hi + 1 - xStart)).foldl
      (fun acc off => min acc (Ps (xStart + off) - (rows[xStart + off - nd]!)[ns3]!)) 255)).toNat < nr
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

end FastSound
end SuperpermLowerBounds
