import LowerBounds.FastJ16Sound
import LowerBounds.DualRingSound
import LowerBounds.J15Final
import LowerBounds.KFinal
import LowerBounds.J5900Defs

/-!
# The joint statements of 5,900 from `FastJ16` accelerated searches

`J5900.joint_of_fast`: proves all five joint statements `S1 .. S5` (`KS.Joint`), given
`KS.TableT`, `KS.TheoremK`, and the evaluated `FastJ16.jSearch` statements `J5900.FastJEvals`:

- `tr15`: exact 15-hole ring cap `TRex15` (`PS.ringSearch`)
- `s1`: `J(S4 S4; 55, 78; 1)` with Rule PREV (`rp = 0`, `(10, 16, 25)`), Rule ORD (`oi = 0`), Rule JS
- `s2a1_hi`: `J(R[16..83, v ≥ 12] S5; 51, 83; 1)` with ring first, `rp = 1`, `clip = true`, Rule JS
- `s2a1_lo`: `J(S5 R[16..83, v ≤ 11]; 51, 83; 1)` with `S5` first, `TRlo11` ring cap, `rp = 0`, Rule JS
- `s2a2`: `J(S5 R[8..15]; 51, 83; 1)` with `S5` first, `TRex15` ring cap, `rp = 0`, Rule JS
- `s3`: `J(S2 R R; 57, 76; 2)` with `rp = 0`, `(10, 16, 25)`, Rule JS
- `s4`: `J(S1 S1 R; 61, 71; 1)` with `rp = 0`, `(10, 15, 30)`, `oi = 0`, Rule JS
- `s5`: `J(S0 S0 R; 62, 70; 2)` with `rp = 0`, `(2, 3, 5)`, `oi = 0`, Rule JS

No `native_decide` and no `sorry`.
-/

namespace SuperpermLowerBounds
namespace J5900

open PS (TRow holesT linksT RingCapT capF)
open T5900

/-- Evaluated `FastJ16.jSearch` statement on `Dtab` (Theorem K). -/
def FastJEv (PRl : List ℕ) (qs : List J16.Q) (R : J16.Rules) (V W B : ℕ) (js : Bool) : Prop :=
  ∃ fuel gs, fuel < 2 ^ 31 ∧ gs.length < 100 ∧
    (∀ g ∈ gs, g.1 < 16 ∧ g.2.1 < 256 ∧ 0 < g.2.2 ∧ g.2.2 < 65536) ∧
    J15.Cov (J15.gprod gs) (FastJ16.jSearch Dtab PRl (qs.map Prod.fst) R V W B fuel gs js)

/-- Evaluated `PS.ringSearchDual` statement on `[Glo..G]`. -/
def DualEv (M PR : List ℕ) (Glo G : ℕ) : Prop :=
  ∃ fuel ds nt, 0 < nt ∧ PS.Covered nt (PS.ringSearchDual 7 M PR Glo G fuel ds nt)

/-- Pointwise Dual Cycle Lemma evaluations on `H = 70..83`. -/
def DualEv70_83 : Prop :=
  ∀ H, 70 ≤ H → H ≤ 83 → DualEv (Dtab.getD 0 []) TRdual H H

/-- The evaluated statements for the joint part of `5,900` using `FastJ16` on `Dtab` + `TRdual`. -/
structure FastJEvals : Prop where
  tr15 : KS.EvR (Ttab.getD 0 []) TRex15 15
  trdual : DualEv70_83
  s1 : FastJEv TRdual [((5, 0, 0), (-99, 99)), ((5, 0, 0), (-99, 99))] rulesS1 55 78 1 true
  s2a1_hi : FastJEv TRdual [((0, 16, 83), (12, 99)), ((6, 0, 0), (-99, 99))] rulesS2a1Hi 51 83 1 true
  s2a1_lo : FastJEv TRlo11 [((6, 0, 0), (-99, 99)), ((0, 16, 83), (-99, 11))] rulesS2a1Lo 51 83 1 true
  s2a2 : FastJEv TRex15 [((6, 0, 0), (-99, 99)), ((0, 8, 15), (-99, 99))] rulesS2a2 51 83 1 true
  s3 : FastJEv TRdual [((3, 0, 0), (-99, 99)), ((0, 0, 76), (-99, 99)), ((0, 0, 76), (-99, 99))] rulesS3 57 76 2 true
  s4 : FastJEv TRdual [((2, 0, 0), (-99, 99)), ((2, 0, 0), (-99, 99)), ((0, 0, 71), (-99, 99))] rulesS4 61 71 1 true
  s5 : FastJEv TRdual [((1, 0, 0), (-99, 99)), ((1, 0, 0), (-99, 99)), ((0, 0, 70), (-99, 99))] rulesS5 62 70 2 true

/-! ### Finite table bounds (kernel-checked) -/

private theorem dtab_le_200 : ∀ row ∈ Dtab, ∀ v ∈ row, v ≤ 200 := by decide +kernel

private theorem trdual_le_200 : ∀ v ∈ TRdual, v ≤ 200 := by decide +kernel

private theorem trlo11_le_200 : ∀ v ∈ TRlo11, v ≤ 200 := by decide +kernel

private theorem trex15_le_200 : ∀ v ∈ TRex15, v ≤ 200 := by decide +kernel

private theorem trtab_le_add99 : ∀ H ≤ 83, TRtab.getD H 0 ≤ H + 99 := by decide +kernel

private theorem trdual_ge_min : ∀ H ≤ 69, min (TRtab.getD H 0) (capF Dtab 0 H) ≤ TRdual.getD H 0 := by
  decide +kernel

private theorem trlo11_ge_min : ∀ H ≤ 83, min (TRtab.getD H 0) (H + 11) ≤ TRlo11.getD H 0 := by
  decide +kernel

private theorem vbd_of_le100 {f : ℕ → ℤ} {n : ℕ} (h : ∀ i < n, -100 ≤ f i ∧ f i ≤ 100) :
    ∀ i < n, -2 ^ 27 ≤ f i ∧ f i ≤ 2 ^ 27 := fun i hi => by
  have := h i hi; omega

/-! ### `CapsOKV` builders on `Dtab` and `TRdual` / `TRlo11` / `TRex15` -/

private theorem ringCap_TRdual (hK : KS.TheoremK) (hdual : DualEv70_83) :
    PS.RingCapRange 7 (fun x => TRdual.getD x 0) 70 83 := by
  intro L hL h0 h2 hcl h70 h83
  obtain ⟨fuel, ds, nt, hnt, hcov⟩ := hdual (holesT 7 L) h70 h83
  have hM : PS.SeqCapLt 7 0 (fun x => (Dtab.getD 0 []).getD x 0) (holesT 7 L + 1) := by
    have h0' := hK 0 (by norm_num)
    exact h0'.mono (by omega)
  exact PS.ringCapRange_of_searchDual (by norm_num) (by norm_num) hnt hM hcov
    L hL h0 h2 hcl (le_refl _) (le_refl _)

private theorem capsOKV_Dtab (hT : KS.TableT) (hK : KS.TheoremK)
    (hdual : DualEv70_83) {W sm : ℕ} (hW : W ≤ 83) (hsm : sm ≤ 8)
    (qs : List J16.Q) :
    J16.CapsOKV 7 (capF Dtab) (fun x => TRdual.getD x 0) W sm qs := by
  have hRdual := ringCap_TRdual hK hdual
  refine ⟨?_, ?_⟩
  · intro t ht L h1 h2 h3 h4
    exact hK t (by omega) L h1 h2 h3 (by omega)
  · intro q _ hq0 L hL hh
    have hw := hL.1
    unfold J15.IsPieceW at hw
    rw [if_pos hq0] at hw
    by_cases h69 : holesT 7 L ≤ 69
    · have h1 : L.length ≤ TRtab.getD (holesT 7 L) 0 :=
        hT.2 L hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 (by omega)
      have h2 : L.length ≤ capF Dtab 0 (holesT 7 L) :=
        hK 0 (by norm_num) L hw.1 (fun x hx => by rw [hw.2.1 x hx]; exact Nat.zero_le 1)
          (PS.linksT_zero hw.2.1) (by omega)
      exact le_trans (le_min h1 h2) (trdual_ge_min (holesT 7 L) h69)
    · exact hRdual L hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 (by omega) (by omega)

private theorem capsOKV_TRlo11 (hT : KS.TableT) (hK : KS.TheoremK) {sm : ℕ} (hsm : sm ≤ 8) :
    J16.CapsOKV 7 (capF Dtab) (fun x => TRlo11.getD x 0) 83 sm
      [((6, 0, 0), (-99, 99)), ((0, 16, 83), (-99, 11))] := by
  refine ⟨?_, ?_⟩
  · intro t ht L h1 h2 h3 h4
    exact hK t (by omega) L h1 h2 h3 (by omega)
  · intro q hq hq0 L hL hh
    rcases List.mem_cons.mp hq with rfl | hq'
    · simp at hq0
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · have hw := hL.1
        unfold J15.IsPieceW at hw
        rw [if_pos rfl] at hw
        have h1 : L.length ≤ TRtab.getD (holesT 7 L) 0 :=
          hT.2 L hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 (by omega)
        have hv : J15.valK 7 L ≤ 11 := (hL.2 rfl).2
        rw [J16.ring_val hw.2.1] at hv
        have h2 : L.length ≤ holesT 7 L + 11 := by omega
        exact le_trans (le_min h1 h2) (trlo11_ge_min (holesT 7 L) hh)
      · simp at hq''

private theorem ringCap_TRex15 (hT : KS.TableT) (htr15 : KS.EvR (Ttab.getD 0 []) TRex15 15) :
    RingCapT 7 (fun x => TRex15.getD x 0) 15 := by
  obtain ⟨fuel, ds, nt, hnt, hcov⟩ := htr15
  have hM : PS.SeqCapLt 7 0 (fun x => (Ttab.getD 0 []).getD x 0) (15 + 1) := by
    have h0 := hT.1 0 (by norm_num)
    exact h0.mono (by decide)
  exact PS.ringCapT_of_search (by norm_num) (by norm_num) hnt hM hcov

private theorem capsOKV_TRex15 (hT : KS.TableT) (hK : KS.TheoremK)
    (htr15 : KS.EvR (Ttab.getD 0 []) TRex15 15) {sm : ℕ} (hsm : sm ≤ 8) :
    J16.CapsOKV 7 (capF Dtab) (fun x => TRex15.getD x 0) 83 sm
      [((6, 0, 0), (-99, 99)), ((0, 8, 15), (-99, 99))] := by
  have hR15 := ringCap_TRex15 hT htr15
  refine ⟨?_, ?_⟩
  · intro t ht L h1 h2 h3 h4
    exact hK t (by omega) L h1 h2 h3 (by omega)
  · intro q hq hq0 L hL _
    rcases List.mem_cons.mp hq with rfl | hq'
    · simp at hq0
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · have hw := hL.1
        unfold J15.IsPieceW at hw
        rw [if_pos rfl] at hw
        exact hR15 L hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.2
      · simp at hq''

/-! ### Piece helpers -/

private theorem seq_pieceV {s lo hi : ℕ} {vlo vhi : ℤ} {L : List TRow} (h : KS.IsPiece (.seq s) L) :
    J16.IsPieceV 7 ((s + 1, lo, hi), (vlo, vhi)) L :=
  ⟨J15.seq_piece h, fun h0 => absurd h0 (Nat.succ_ne_zero s)⟩

private theorem ring_val_bounds (hT : KS.TableT) {L : List TRow} (h : KS.IsPiece .ring L)
    (hh : holesT 7 L ≤ 83) : -99 ≤ J15.valK 7 L ∧ J15.valK 7 L ≤ 99 := by
  have hcap := hT.2 L h.1 h.2.1 h.2.2.1 h.2.2.2 (by omega)
  have h99 := trtab_le_add99 (holesT 7 L) hh
  have hle : L.length ≤ holesT 7 L + 99 := le_trans hcap h99
  rw [J16.ring_val h.2.1]
  omega

private theorem ring_pieceV (hT : KS.TableT) {lo hi : ℕ} {L : List TRow} (h : KS.IsPiece .ring L)
    (hlo : lo ≤ holesT 7 L) (hhi : holesT 7 L ≤ hi) (h83 : holesT 7 L ≤ 83) :
    J16.IsPieceV 7 ((0, lo, hi), (-99, 99)) L :=
  ⟨J15.ring_piece h hlo hhi, fun _ => ring_val_bounds hT h h83⟩

/-! ### The five joint statements from `FastJ16` -/

/-- `S1`: `J(S4 S4; 55, 78; 1)`. -/
theorem s1_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hdual : DualEv70_83)
    (h : FastJEv TRdual [((5, 0, 0), (-99, 99)), ((5, 0, 0), (-99, 99))] rulesS1 55 78 1 true) :
    KS.J [.seq 4, .seq 4] 55 78 1 := by
  obtain ⟨fuel, gs, hfuel, hgslen, hgs, hcov⟩ := h
  have hjv : J16.JV 7 [((5, 0, 0), (-99, 99)), ((5, 0, 0), (-99, 99))] 55 78 1 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hfuel
      dtab_le_200 trdual_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_Dtab hT hK hdual (by decide) (by decide) _)
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS1])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS1]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS1]))
      hgs hgslen hcov
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, rfl, h1, h2⟩ := J15.forall₂_two hLs
  have := hjv [L1, L2]
    (List.Forall₂.cons (seq_pieceV h1) (List.Forall₂.cons (seq_pieceV h2) List.Forall₂.nil))
    (J15.sh_of_sharedLe hsh) (by simpa [J15.wtT_eq] using hw)
  simpa [J15.valT_eq] using this

/-- `S2`: `J(S5 R; 51, 83; 1)` from `s2a1_hi`, `s2a1_lo`, `s2a2`, `tr15`, `trdual`, and Theorem K. -/
theorem s2_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hdual : DualEv70_83)
    (htr15 : KS.EvR (Ttab.getD 0 []) TRex15 15)
    (hhi : FastJEv TRdual [((0, 16, 83), (12, 99)), ((6, 0, 0), (-99, 99))] rulesS2a1Hi 51 83 1 true)
    (hlo : FastJEv TRlo11 [((6, 0, 0), (-99, 99)), ((0, 16, 83), (-99, 11))] rulesS2a1Lo 51 83 1 true)
    (ha2 : FastJEv TRex15 [((6, 0, 0), (-99, 99)), ((0, 8, 15), (-99, 99))] rulesS2a2 51 83 1 true) :
    KS.J [.seq 5, .ring] 51 83 1 := by
  obtain ⟨f1, gs1, hf1, hgl1, hgs1, hc1⟩ := hhi
  have hjv_hi : J16.JV 7 [((0, 16, 83), (12, 99)), ((6, 0, 0), (-99, 99))] 51 83 1 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hf1
      dtab_le_200 trdual_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_Dtab hT hK hdual (by decide) (by decide) _)
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS2a1Hi])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS2a1Hi]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS2a1Hi]))
      hgs1 hgl1 hc1
  obtain ⟨f2, gs2, hf2, hgl2, hgs2, hc2⟩ := hlo
  have hjv_lo : J16.JV 7 [((6, 0, 0), (-99, 99)), ((0, 16, 83), (-99, 11))] 51 83 1 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hf2
      dtab_le_200 trlo11_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_TRlo11 hT hK (by decide))
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS2a1Lo])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS2a1Lo]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS2a1Lo]))
      hgs2 hgl2 hc2
  obtain ⟨f3, gs3, hf3, hgl3, hgs3, hc3⟩ := ha2
  have hjv_a2 : J16.JV 7 [((6, 0, 0), (-99, 99)), ((0, 8, 15), (-99, 99))] 51 83 1 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hf3
      dtab_le_200 trex15_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_TRex15 hT hK htr15 (by decide))
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS2a2])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS2a2]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS2a2]))
      hgs3 hgl3 hc3
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, rfl, h1, h2⟩ := J15.forall₂_two hLs
  have hw' : KS.wtT L1 + KS.wtT L2 ≤ 83 := by simpa using hw
  have g2 := J15.holes_le_wtT L2
  have hsh0 := J15.sh_of_sharedLe hsh
  by_cases h16 : 16 ≤ holesT 7 L2
  · have hvb := ring_val_bounds hT h2 (by omega)
    by_cases hv12 : 12 ≤ J15.valK 7 L2
    · have := hjv_hi [L2, L1]
        (List.Forall₂.cons ⟨J15.ring_piece h2 h16 (by omega), fun _ => ⟨hv12, hvb.2⟩⟩
          (List.Forall₂.cons (seq_pieceV h1) List.Forall₂.nil))
        (J15.sh_swap hsh0)
        (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← J15.wtT_eq]; omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ← J15.valT_eq] at this ⊢
      push_cast at this; linarith
    · have := hjv_lo [L1, L2]
        (List.Forall₂.cons (seq_pieceV h1)
          (List.Forall₂.cons ⟨J15.ring_piece h2 h16 (by omega), fun _ => ⟨hvb.1, by linarith⟩⟩ List.Forall₂.nil))
        hsh0 (by simpa [J15.wtT_eq] using hw)
      simpa [J15.valT_eq] using this
  by_cases h8 : 8 ≤ holesT 7 L2
  · have := hjv_a2 [L1, L2]
      (List.Forall₂.cons (seq_pieceV h1)
        (List.Forall₂.cons (ring_pieceV hT h2 h8 (by omega) (by omega)) List.Forall₂.nil))
      hsh0 (by simpa [J15.wtT_eq] using hw)
    simpa [J15.valT_eq] using this
  · -- S2b: rings with at most 7 holes follow from Theorem K
    obtain ⟨hR, hR0, hR2, hRc⟩ := h2
    obtain ⟨hS, _, hS1, hSl⟩ := h1
    have hlR : linksT L2 = 0 := PS.linksT_zero hR0
    have c1 := hT.2 L2 hR hR0 hR2 hRc (by omega)
    have c2 := J15.trtab_le (holesT 7 L2) (by omega)
    have hwS : holesT 7 L1 + 6 * linksT L1 ≤ 83 := by unfold KS.wtT at hw'; omega
    have c3 := hK (linksT L1) (by omega) L1 hS hS1 rfl (by omega)
    have c4 := J15.dtab_le (linksT L1) (by omega) (holesT 7 L1) (by omega) hwS
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, KS.valT, hlR]
    have c1' : (L2.length : ℤ) ≤ (holesT 7 L2 : ℤ) + 5 := by exact_mod_cast le_trans c1 c2
    have c3' : (L1.length : ℤ) ≤ (holesT 7 L1 : ℤ) + 5 * (linksT L1 : ℤ) + 45 := by
      exact_mod_cast le_trans c3 c4
    push_cast; linarith

/-- `S3`: `J(S2 R R; 57, 76; 2)`. -/
theorem s3_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hdual : DualEv70_83)
    (h : FastJEv TRdual [((3, 0, 0), (-99, 99)), ((0, 0, 76), (-99, 99)), ((0, 0, 76), (-99, 99))]
      rulesS3 57 76 2 true) :
    KS.J [.seq 2, .ring, .ring] 57 76 2 := by
  obtain ⟨fuel, gs, hfuel, hgslen, hgs, hcov⟩ := h
  have hjv : J16.JV 7 [((3, 0, 0), (-99, 99)), ((0, 0, 76), (-99, 99)), ((0, 0, 76), (-99, 99))] 57 76 2 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hfuel
      dtab_le_200 trdual_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_Dtab hT hK hdual (by decide) (by decide) _)
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS3])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS3]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS3]))
      hgs hgslen hcov
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := J15.forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 76 := by simpa using hw
  have g2 := J15.holes_le_wtT L2
  have g3 := J15.holes_le_wtT L3
  have := hjv [L1, L2, L3]
    (List.Forall₂.cons (seq_pieceV h1)
      (List.Forall₂.cons (ring_pieceV hT h2 (Nat.zero_le _) (by omega) (by omega))
        (List.Forall₂.cons (ring_pieceV hT h3 (Nat.zero_le _) (by omega) (by omega)) List.Forall₂.nil)))
    (J15.sh_of_sharedLe hsh) (by simpa [J15.wtT_eq] using hw)
  simpa [J15.valT_eq] using this

/-- `S4`: `J(S1 S1 R; 61, 71; 1)`. -/
theorem s4_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hdual : DualEv70_83)
    (h : FastJEv TRdual [((2, 0, 0), (-99, 99)), ((2, 0, 0), (-99, 99)), ((0, 0, 71), (-99, 99))]
      rulesS4 61 71 1 true) :
    KS.J [.seq 1, .seq 1, .ring] 61 71 1 := by
  obtain ⟨fuel, gs, hfuel, hgslen, hgs, hcov⟩ := h
  have hjv : J16.JV 7 [((2, 0, 0), (-99, 99)), ((2, 0, 0), (-99, 99)), ((0, 0, 71), (-99, 99))] 61 71 1 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hfuel
      dtab_le_200 trdual_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_Dtab hT hK hdual (by decide) (by decide) _)
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS4])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS4]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS4]))
      hgs hgslen hcov
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := J15.forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 71 := by simpa using hw
  have g3 := J15.holes_le_wtT L3
  have := hjv [L1, L2, L3]
    (List.Forall₂.cons (seq_pieceV h1)
      (List.Forall₂.cons (seq_pieceV h2)
        (List.Forall₂.cons (ring_pieceV hT h3 (Nat.zero_le _) (by omega) (by omega)) List.Forall₂.nil)))
    (J15.sh_of_sharedLe hsh) (by simpa [J15.wtT_eq] using hw)
  simpa [J15.valT_eq] using this

/-- `S5`: `J(S0 S0 R; 62, 70; 2)`. -/
theorem s5_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hdual : DualEv70_83)
    (h : FastJEv TRdual [((1, 0, 0), (-99, 99)), ((1, 0, 0), (-99, 99)), ((0, 0, 70), (-99, 99))]
      rulesS5 62 70 2 true) :
    KS.J [.seq 0, .seq 0, .ring] 62 70 2 := by
  obtain ⟨fuel, gs, hfuel, hgslen, hgs, hcov⟩ := h
  have hjv : J16.JV 7 [((1, 0, 0), (-99, 99)), ((1, 0, 0), (-99, 99)), ((0, 0, 70), (-99, 99))] 62 70 2 :=
    FastJ16Sound.jv_of_fastJ16 (by simp) (by decide) (by decide) (by decide) (by decide) hfuel
      dtab_le_200 trdual_le_200 (by decide) (by decide) rfl (by decide)
      (capsOKV_Dtab hT hK hdual (by decide) (by decide) _)
      (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, J16.vhiF, rulesS5])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vloF, rulesS5]))
      (vbd_of_le100 (by intro i hi; simp at hi; interval_cases i <;> simp [J16.vhiF, rulesS5]))
      hgs hgslen hcov
  intro Ls hLs hsh hw
  obtain ⟨L1, L2, L3, rfl, h1, h2, h3⟩ := J15.forall₂_three hLs
  have hw' : KS.wtT L1 + (KS.wtT L2 + KS.wtT L3) ≤ 70 := by simpa using hw
  have g3 := J15.holes_le_wtT L3
  have := hjv [L1, L2, L3]
    (List.Forall₂.cons (seq_pieceV h1)
      (List.Forall₂.cons (seq_pieceV h2)
        (List.Forall₂.cons (ring_pieceV hT h3 (Nat.zero_le _) (by omega) (by omega)) List.Forall₂.nil)))
    (J15.sh_of_sharedLe hsh) (by simpa [J15.wtT_eq] using hw)
  simpa [J15.valT_eq] using this

/-- **The joint statements of `5,900`**, from table `T'`, Theorem K, and the accelerated `FastJ16` searches. -/
theorem joint_of_fast (hT : KS.TableT) (hK : KS.TheoremK) (hE : FastJEvals) : KS.Joint :=
  ⟨s1_of_fast hT hK hE.trdual hE.s1,
   s2_of_fast hT hK hE.trdual hE.tr15 hE.s2a1_hi hE.s2a1_lo hE.s2a2,
   s3_of_fast hT hK hE.trdual hE.s3,
   s4_of_fast hT hK hE.trdual hE.s4,
   s5_of_fast hT hK hE.trdual hE.s5⟩

end J5900
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.J5900.joint_of_fast
