import LowerBounds.DualRingSearch
import LowerBounds.PLevels
import LowerBounds.PRules

/-!
# Soundness of `PS.ringSearchDual` (Dual Cycle Lemma)

Proves `PS.ringCapRange_of_searchDual`: if `PS.ringSearchDual k M PR Glo G` returns `false` across
all parts, then every valid ring with `Glo ≤ holesT k L ≤ G` satisfies `L.length ≤ PR.getD (holesT k L) 0`.

Derived in 3 lines from the existing `PS.cycle_lemma` applied to row lengths `x.2.length`.
ZERO `sorry`, ZERO `native_decide`, axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace SuperpermLowerBounds
namespace PS

private theorem holesT_add_lenSum (k : ℕ) : ∀ (L : List TRow),
    (∀ x ∈ L, x.2.length ≤ k - 1) →
    holesT k L + (L.map fun x => x.2.length).sum = L.length * (k - 1)
  | [], _ => by simp [holesT]
  | x :: xs, hle => by
    have hx := hle x List.mem_cons_self
    have ih := holesT_add_lenSum k xs (fun y hy => hle y (List.mem_cons_of_mem _ hy))
    simp only [holesT, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
    omega

/-- Dual Cycle Lemma: every list of rows with lengths `≤ k - 1` has a rotation `B ++ A` where
every prefix `u` satisfies `u.length * holesT k (A ++ B) ≤ holesT k u * (A ++ B).length`. -/
theorem dual_cycle_lemma (k : ℕ) (L : List TRow) (hle : ∀ x ∈ L, x.2.length ≤ k - 1) :
    ∃ A B : List TRow, L = A ++ B ∧
      ∀ u v, B ++ A = u ++ v → u.length * holesT k (A ++ B) ≤ holesT k u * (A ++ B).length := by
  obtain ⟨A, B, hAB, hcyc⟩ := cycle_lemma (fun x : TRow => x.2.length) L
  refine ⟨A, B, hAB, fun u v huv => ?_⟩
  have h1 := hcyc u v huv
  have hle_BA : ∀ x ∈ B ++ A, x.2.length ≤ k - 1 := by
    intro x hx; apply hle; rw [hAB]; simp only [List.mem_append] at hx ⊢; tauto
  have hle_u : ∀ x ∈ u, x.2.length ≤ k - 1 := fun x hx =>
    hle_BA x (by rw [huv]; exact List.mem_append_left _ hx)
  have hsu := holesT_add_lenSum k u hle_u
  have hsL := holesT_add_lenSum k (A ++ B) (by rwa [← hAB])
  rw [hAB] at h1
  nlinarith

/-- Dual ring cap on `[Glo .. G]`. -/
def RingCapRange (k : ℕ) (PR : ℕ → ℕ) (Glo G : ℕ) : Prop :=
  ∀ L : List TRow, IsSeq k L → (∀ x ∈ L, x.1 = 0) → 2 ≤ L.length → Closes k L →
    Glo ≤ holesT k L → holesT k L ≤ G → L.length ≤ PR (holesT k L)

theorem ringCapRange_of_stmt {k Glo G : ℕ} {M PR : List ℕ}
    (hM : SeqCapLt k 0 (fun x => M.getD x 0) (G + 1))
    (hst : PStmt k false noRule (ringBadDual PR Glo G) (ringKeepDual M PR Glo G) noRule noRule) :
    RingCapRange k (fun x => PR.getD x 0) Glo G := by
  intro L hL h0 h2 hc hGlo hG
  by_contra hnb0
  have hnb : PR.getD (holesT k L) 0 < L.length := Nat.lt_of_not_le hnb0
  obtain ⟨A, B, hAB, hcyc⟩ := dual_cycle_lemma k L hL.size_le
  subst hAB
  obtain ⟨hL', hc'⟩ := isSeq_rotate A B hL h0 hc
  have h0' : ∀ x ∈ B ++ A, x.1 = 0 := by
    intro x hx; apply h0; simp only [List.mem_append] at hx ⊢; tauto
  have hlen : (B ++ A).length = (A ++ B).length := by simp only [List.length_append]; omega
  have hhol : holesT k (B ++ A) = holesT k (A ++ B) := by rw [holesT_append, holesT_append]; omega
  have hne : B ++ A ≠ [] := by intro e; rw [e] at hlen; simp only [List.length_nil] at hlen; omega
  have hcapL : (A ++ B).length ≤ M.getD (holesT k (A ++ B)) 0 :=
    hM (A ++ B) hL (fun x hx => by rw [h0 x hx]; omega) (linksT_zero h0) (by omega)
  have hkeep : ∀ u x w, B ++ A = u ++ x :: w → u ≠ [] →
      ap (keepK (ringKeepDual M PR Glo G) noRule noRule x.1) (cnt k false u) = true := by
    intro u x w huw hu
    rw [cnt_false hu]
    have hx0 : x.1 = 0 := h0' x (by rw [huw]; simp)
    have hB : IsSeq k (x :: w) := hL'.infix ⟨u, [], by simp [huw]⟩
    have hB0 : ∀ y ∈ x :: w, y.1 = 0 :=
      fun y hy => h0' y (by rw [huw]; exact List.mem_append_right _ hy)
    have hlen2 : (A ++ B).length = u.length + (x :: w).length := by
      rw [← hlen, huw, List.length_append]
    have hh : holesT k (A ++ B) = holesT k u + holesT k (x :: w) := by
      rw [← hhol, huw, holesT_append]
    have hBcap : (x :: w).length ≤ M.getD (holesT k (x :: w)) 0 :=
      hM (x :: w) hB (fun y hy => by rw [hB0 y hy]; omega) (linksT_zero hB0) (by omega)
    have hcy := hcyc u (x :: w) huw
    obtain ⟨kd, Q⟩ := x
    simp only at hx0; subst hx0
    show ringKeepDual M PR Glo G (linksT u) u.length (holesT k u) = true
    simp only [ringKeepDual, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    refine ⟨holesT k (A ++ B), by omega, ⟨by omega, by omega⟩, (A ++ B).length, by omega,
      ⟨⟨by omega, ?_⟩, hcy⟩, ?_⟩
    · simp only [List.length_cons] at hlen2; omega
    · have e2 : holesT k (A ++ B) - holesT k u = holesT k ((0, Q) :: w) := by omega
      rw [e2]; omega
  have hb : ap (ringBadDual PR Glo G) (cnt k false (B ++ A)) = true := by
    rw [cnt_false hne, hlen, hhol]
    simp only [ap, ringBadDual, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h2, hGlo⟩, hG⟩, by omega⟩
  exact (hst (B ++ A) hL' hne hkeep).2 hb hc'

theorem ringSearchDual_direct {k Glo G fuel ds nt pa pb : ℕ} {M PR : List ℕ}
    (h : ringSearchDual k M PR Glo G fuel ds nt pa pb = false) :
    searchB k false noRule (ringBadDual PR Glo G) (ringKeepDual M PR Glo G) noRule noRule
      fuel ds nt pa pb = false := by
  unfold ringSearchDual at h
  simp only [look3_tab3] at h
  exact h

/-- **Dual Cycle Lemma ring cap on `[Glo .. G]`**, from compiled `ringSearchDual`. -/
theorem ringCapRange_of_searchDual {k Glo G fuel ds nt : ℕ} {M PR : List ℕ}
    (hk : 4 ≤ k) (hk15 : k ≤ 15) (hnt : 0 < nt)
    (hM : SeqCapLt k 0 (fun x => M.getD x 0) (G + 1))
    (hs : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      ringSearchDual k M PR Glo G fuel ds nt pa pb = false) :
    RingCapRange k (fun x => PR.getD x 0) Glo G :=
  ringCapRange_of_stmt hM (stmt_of_searchB hk hk15 hnt (fun tp htp => by
    obtain ⟨pa, pb, h1, h2, h⟩ := hs tp htp
    exact ⟨pa, pb, h1, h2, ringSearchDual_direct h⟩))

end PS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.PS.ringCapRange_of_searchDual
