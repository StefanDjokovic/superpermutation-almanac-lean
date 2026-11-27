import LowerBounds.FastCommonSound

/-!
# Kernel-Verified Soundness of `DomTables.m3Witnesses` (`440`) and `DomTables.w4Witnesses` (`271`)

* Verifies every explicit replacement witness in `DomTables.m3Witnesses` and `DomTables.w4Witnesses`
  at `id7 = [1, 2, 3, 4, 5, 6, 7]` using Lean kernel `decide`.
* Proves `noM3_of_min_rows` (under monotonicity `hM3`) and `noW4_of_hlow` (under `hW4` + `hlowW4`)
  by relabeling the matched motif's start word to `id7` (`PS.IsSeq.relabel`) and splicing the
  verified replacement directly into the sequence.
* Connects directly to `FastK16.buildM3Allow` and `FastK16.buildW4Allow`.
-/

namespace SuperpermLowerBounds
namespace FastSound

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT LinkK SeqCapLt relabSeq)
open K16 (tau2 permW_tau2 wlink2_tau2)
open DomTables (m3Witnesses w4Witnesses)
open FastK16 (buildM3Allow buildW4Allow)

/-! ### Canonical `id7`, `buildRow7`, and Rotation Equivalence `rotTo7` -/

def id7 : List ℕ := [1, 2, 3, 4, 5, 6, 7]

/-- Build a row of `L` blocks starting at `u` by repeatedly applying `tau2 7`. -/
def buildRow7 : List ℕ → ℕ → List (List ℕ)
  | _, 0 => []
  | u, L + 1 => u :: buildRow7 (tau2 7 u) L

/-- Canonical rotation of a `PermW 7` word starting with `7`. -/
def rotTo7 (w : List ℕ) : List ℕ := w.rotate (w.idxOf 7)

theorem rotTo7_isRotated (w : List ℕ) : w ~r rotTo7 w :=
  ⟨w.idxOf 7, rfl⟩

theorem isRotated_of_rotTo7_eq {u v : List ℕ} (h : rotTo7 u = rotTo7 v) : u ~r v :=
  (rotTo7_isRotated u).trans (h ▸ (rotTo7_isRotated v).symm)

theorem rotTo7_eq_of_isRotated {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (hr : u ~r v) :
    rotTo7 u = rotTo7 v := by
  have h7u : 7 ∈ u := (hu.2.2 7).mpr (by omega)
  have h7v : 7 ∈ v := (hv.2.2 7).mpr (by omega)
  have hru := hu.rotate (u.idxOf 7)
  have hrot : rotTo7 u ~r rotTo7 v := (rotTo7_isRotated u).symm.trans (hr.trans (rotTo7_isRotated v))
  have hh_u : (rotTo7 u).head? = some 7 := by
    unfold rotTo7
    have hi : u.idxOf 7 < u.length := List.idxOf_lt_length_of_mem h7u
    rw [List.head?_rotate hi, List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  have hh_v : (rotTo7 v).head? = some 7 := by
    unfold rotTo7
    have hi : v.idxOf 7 < v.length := List.idxOf_lt_length_of_mem h7v
    rw [List.head?_rotate hi, List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  have heq := K16.eq_rotate_of_head hru.1 hrot (j := 0) (by rw [hru.2.1]; omega)
    (by rw [← List.head?_eq_getElem?]; change (rotTo7 v).head? = (rotTo7 u).head?; rw [hh_u, hh_v])
  rw [List.rotate_zero] at heq
  exact heq.symm

theorem buildRow7_length : ∀ (u : List ℕ) (L : ℕ), (buildRow7 u L).length = L
  | _, 0 => rfl
  | u, L + 1 => by simp [buildRow7, buildRow7_length _ L]

theorem buildRow7_permW : ∀ (L : ℕ) (u : List ℕ), PermW 7 u → ∀ w ∈ buildRow7 u L, PermW 7 w
  | 0, _, _, _, hw => absurd hw (by simp [buildRow7])
  | L + 1, u, hu, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hu
    · exact buildRow7_permW L (tau2 7 u) (permW_tau2 (by omega) hu) w hw'

theorem buildRow7_doors : ∀ (L : ℕ) (u : List ℕ), PermW 7 u → List.IsChain (WLink 7 2) (buildRow7 u L)
  | 0, _, _ => List.isChain_nil
  | 1, _, _ => List.isChain_singleton _
  | L + 2, u, hu => by
    show List.IsChain (WLink 7 2) (u :: tau2 7 u :: buildRow7 (tau2 7 (tau2 7 u)) L)
    exact List.isChain_cons_cons.mpr ⟨wlink2_tau2 (by omega) hu.2.1,
      buildRow7_doors (L + 1) (tau2 7 u) (permW_tau2 (by omega) hu)⟩

theorem eq_buildRow7_of_chain (R : List (List ℕ)) :
    ∀ (u : List ℕ) (hne : R ≠ []),
    R.head hne = u → List.IsChain (DoorEq 7) R → R = buildRow7 u R.length := by
  induction R with
  | nil => intro _ h; exact absurd rfl h
  | cons v rest ih =>
    intro u _ hh hch
    simp only [List.head_cons] at hh
    subst hh
    cases rest with
    | nil => rfl
    | cons v' R' =>
      obtain ⟨hd, htl⟩ := List.isChain_cons_cons.mp hch
      have hv' : v' = tau2 7 v := hd
      have ih' := ih v' (List.cons_ne_nil _ _) rfl htl
      simp only [List.length_cons, buildRow7]
      rw [← hv']
      exact congrArg (v :: ·) ih'

theorem getLastD_of_ne_nil {α : Type} : ∀ (l : List α) (d : α) (h : l ≠ []), l.getLastD d = l.getLast h
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | _ :: b :: t, d, _ => by
    have ih := getLastD_of_ne_nil (b :: t) d (List.cons_ne_nil b t)
    simpa [List.getLastD] using ih

/-! ### Path Construction & Kernel Verification for `m3Witnesses` and `w4Witnesses` -/

/-- Build a `w3`-linked replacement sequence starting at `u`, with first row having kind `kd0`. -/
def buildReplRows (kd0 : ℕ) : List ℕ → List (ℕ × ℕ) → List TRow
  | _, [] => []
  | u, [(_, L)] => [(kd0, buildRow7 u L)]
  | u, (_, L) :: (t, L') :: rest =>
    let row := buildRow7 u L
    match h : row with
    | [] => []
    | _ :: _ =>
      let e := row.getLast (by rw [h]; exact List.cons_ne_nil _ _)
      (kd0, row) :: buildReplRows 0 (w3Step e t) ((t, L') :: rest)

/-- Build the original 3-row `w3` motif at `id7`. -/
def buildOrigM3 (kd0 l0 t0 l1 t1 l2 : ℕ) : List TRow :=
  let r0 := buildRow7 id7 l0
  let e0 := r0.getLastD id7
  let r1 := buildRow7 (w3Step e0 t0) l1
  let e1 := r1.getLastD id7
  let r2 := buildRow7 (w3Step e1 t1) l2
  [(kd0, r0), (0, r1), (0, r2)]

/-- Build the original 2-row `w4` motif at `id7`. -/
def buildOrigW4 (kd0 l1 t4 l2 : ℕ) : List TRow :=
  let r1 := buildRow7 id7 l1
  let e1 := r1.getLastD id7
  let r2 := buildRow7 (w4Step e1 t4) l2
  [(kd0, r1), (1, r2)]

/-- Extract all canonicalized rotation classes of a list of rows. -/
def allCanons (rows : List TRow) : List (List ℕ) :=
  (rows.map Prod.snd).flatten.map rotTo7

/-- Check a list has no duplicate elements (decidable `Bool` helper). -/
def listNoDupB {α : Type} [BEq α] : List α → Bool
  | [] => true
  | a :: t => !(t.contains a) && listNoDupB t

def checkM3One (w : ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ)) : Bool :=
  let (l0, t0, l1, t1, l2, repl) := w
  let orig := buildOrigM3 0 l0 t0 l1 t1 l2
  let rep := buildReplRows 0 id7 repl
  let cOrig := allCanons orig
  let cRep := allCanons rep
  let eOrig := (orig.getLastD (0, [])).2.getLastD []
  let eRep := (rep.getLastD (0, [])).2.getLastD []
  let hOrig := holesT 7 orig
  let hRep := holesT 7 rep
  decide (1 ≤ l0) && decide (l0 ≤ 6) && decide (t0 < 5) &&
  decide (1 ≤ l1) && decide (l1 ≤ 6) && decide (t1 < 5) &&
  decide (1 ≤ l2) && decide (l2 ≤ 6) &&
  (!repl.isEmpty) && decide (repl.length ≤ 2) &&
  repl.all (fun (t, L) => decide (t < 5) && decide (1 ≤ L) && decide (L ≤ 6)) &&
  listNoDupB cRep &&
  cRep.all (fun c => cOrig.contains c) &&
  (eRep == eOrig) &&
  decide (rep.length < 3) &&
  decide (hRep < hOrig) &&
  decide (3 + hRep ≤ rep.length + hOrig)

def checkW4One (w : ℕ × ℕ × ℕ × List (ℕ × ℕ)) : Bool :=
  let (l1, t4, l2, repl) := w
  let orig := buildOrigW4 0 l1 t4 l2
  let rep := buildReplRows 0 id7 repl
  let cOrig := allCanons orig
  let cRep := allCanons rep
  let eOrig := (orig.getLastD (0, [])).2.getLastD []
  let eRep := (rep.getLastD (0, [])).2.getLastD []
  let hOrig := holesT 7 orig
  let hRep := holesT 7 rep
  decide (1 ≤ l1) && decide (l1 ≤ 6) && decide (t4 < 23) &&
  decide (1 ≤ l2) && decide (l2 ≤ 6) &&
  (!repl.isEmpty) &&
  repl.all (fun (t, L) => decide (t < 5) && decide (1 ≤ L) && decide (L ≤ 6)) &&
  listNoDupB cRep &&
  cRep.all (fun c => cOrig.contains c) &&
  (eRep == eOrig) &&
  decide (hRep ≤ hOrig + 6) &&
  decide (2 + hRep ≤ rep.length + hOrig + 5)

-- Chunked kernel verification (stays well under default `maxRecDepth` with ZERO option overrides!)
private theorem list_all_of_split {α : Type} (p : α → Bool) (l : List α) (k : ℕ)
    (h1 : (l.take k).all p = true) (h2 : (l.drop k).all p = true) : l.all p = true := by
  rw [← List.take_append_drop k l, List.all_append, h1, h2]; rfl

theorem m3Witnesses_valid : m3Witnesses.all checkM3One = true := by
  apply list_all_of_split _ _ 100 (by decide)
  apply list_all_of_split _ _ 100 (by decide)
  apply list_all_of_split _ _ 100 (by decide)
  apply list_all_of_split _ _ 100 (by decide)
  decide

theorem w4Witnesses_valid : w4Witnesses.all checkW4One = true := by
  apply list_all_of_split _ _ 100 (by decide)
  apply list_all_of_split _ _ 100 (by decide)
  decide

/-! ### Properties of `buildReplRows` -/

theorem id7_permW : PermW 7 id7 := by
  change PermW 7 (List.range' 1 7)
  exact PS.permW_range' 7

theorem wlink3_w3Step {u : List ℕ} (hu : PermW 7 u) (t : ℕ) : WLink 7 3 u (w3Step u t) := by
  have hrot := hu.rotate 6
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, he⟩ := list7_exists hrot.2.1
  unfold WLink w3Step
  rw [he]
  rfl

theorem buildReplRows_ne_nil (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ))
    (hne : repl ≠ []) (hL : ∀ p ∈ repl, 1 ≤ p.2) :
    buildReplRows kd0 u repl ≠ [] := by
  match repl, hne with
  | [(_, L)], _ => simp [buildReplRows]
  | (_, L) :: (t, L') :: rest, _ =>
    have hL1 : 1 ≤ L := hL _ List.mem_cons_self
    match L, hL1 with
    | L0 + 1, _ => simp [buildReplRows, buildRow7]

theorem buildReplRows_head (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ))
    (hne : repl ≠ []) (hL : ∀ p ∈ repl, 1 ≤ p.2) :
    ∀ h1 : buildReplRows kd0 u repl ≠ [],
    ∃ h2 : ((buildReplRows kd0 u repl).head h1).2 ≠ [],
      ((buildReplRows kd0 u repl).head h1).1 = kd0 ∧
      ((buildReplRows kd0 u repl).head h1).2.head h2 = u := by
  intro h1
  match repl, hne with
  | [(_, L)], _ =>
    have hL1 : 1 ≤ L := hL _ List.mem_cons_self
    match L, hL1 with
    | L0 + 1, _ => exact ⟨List.cons_ne_nil _ _, rfl, rfl⟩
  | (_, L) :: (t, L') :: rest, _ =>
    have hL1 : 1 ≤ L := hL _ List.mem_cons_self
    match L, hL1 with
    | L0 + 1, _ => exact ⟨List.cons_ne_nil _ _, rfl, rfl⟩

theorem buildReplRows_kd0_indep_snd (kd0 : ℕ) :
    ∀ (u : List ℕ) (repl : List (ℕ × ℕ)),
      (buildReplRows kd0 u repl).map Prod.snd = (buildReplRows 0 u repl).map Prod.snd
  | _, [] => rfl
  | _, [(_, _)] => rfl
  | u, (_, L) :: (t, L') :: rest => by
    match L with
    | 0 => rfl
    | L0 + 1 => simp only [buildReplRows, buildRow7, List.map_cons]

theorem buildReplRows_kd0_length (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ)) :
    (buildReplRows kd0 u repl).length = (buildReplRows 0 u repl).length := by
  have h := congrArg List.length (buildReplRows_kd0_indep_snd kd0 u repl)
  simpa using h

theorem buildReplRows_kd0_holesT (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ)) :
    holesT 7 (buildReplRows kd0 u repl) = holesT 7 (buildReplRows 0 u repl) := by
  have haux : ∀ l₁ l₂ : List TRow, l₁.map Prod.snd = l₂.map Prod.snd → holesT 7 l₁ = holesT 7 l₂ := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ h; cases l₂ <;> simp at h ⊢
    | cons a t ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b s =>
        simp only [List.map_cons, List.cons.injEq] at h
        have hts := ih s h.2
        unfold holesT at hts ⊢
        simp only [List.map_cons, List.sum_cons, h.1, hts]
  exact haux _ _ (buildReplRows_kd0_indep_snd kd0 u repl)

theorem buildReplRows_kd0_last (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ)) :
    ((buildReplRows kd0 u repl).getLastD (0, [])).2 =
      ((buildReplRows 0 u repl).getLastD (0, [])).2 := by
  have haux : ∀ l₁ l₂ : List TRow, l₁.map Prod.snd = l₂.map Prod.snd →
      (l₁.getLastD (0, [])).2 = (l₂.getLastD (0, [])).2 := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ h; cases l₂ <;> simp at h ⊢
    | cons a t ih =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons b s =>
        simp only [List.map_cons, List.cons.injEq] at h
        cases t with
        | nil =>
          cases s with
          | nil => simpa using h.1
          | cons _ _ => simp at h
        | cons a' t' =>
          cases s with
          | nil => simp at h
          | cons b' s' =>
            have ih' := ih (b' :: s') h.2
            simpa [List.getLastD] using ih'
  exact haux _ _ (buildReplRows_kd0_indep_snd kd0 u repl)

private theorem buildReplRows_zero_kinds :
    ∀ (r : List (ℕ × ℕ)) (v : List ℕ), ∀ x ∈ buildReplRows 0 v r, x.1 = 0
  | [], _, _, hx => absurd hx (by simp [buildReplRows])
  | [(_, _)], _, x, hx => by simp only [buildReplRows, List.mem_singleton] at hx; rw [hx]
  | (_, L) :: (t, L') :: rest, v, x, hx => by
    match L with
    | 0 => simp [buildReplRows, buildRow7] at hx
    | L0 + 1 =>
      simp only [buildReplRows, buildRow7, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · rfl
      · exact buildReplRows_zero_kinds ((t, L') :: rest) _ x hx'

theorem buildReplRows_linksT (kd0 : ℕ) (u : List ℕ) (repl : List (ℕ × ℕ)) :
    linksT (buildReplRows kd0 u repl) = 0 := by
  match repl with
  | [] => rfl
  | [(_, _)] => rfl
  | (_, L) :: (t, L') :: rest =>
    match L with
    | 0 => rfl
    | L0 + 1 =>
      simp only [buildReplRows, buildRow7, linksT, List.tail_cons]
      have ht := buildReplRows_zero_kinds ((t, L') :: rest)
        (w3Step ((u :: buildRow7 (tau2 7 u) L0).getLast (List.cons_ne_nil _ _)) t)
      rw [List.countP_eq_zero]
      intro x hx
      simp [ht x hx]

theorem buildReplRows_tags (kd0 : ℕ) (hkd0 : kd0 ≤ 1) :
    ∀ (u : List ℕ) (repl : List (ℕ × ℕ)), ∀ x ∈ buildReplRows kd0 u repl, x.1 ≤ 1
  | _, [], _, hx => absurd hx (by simp [buildReplRows])
  | _, [(_, _)], x, hx => by
    simp only [buildReplRows, List.mem_singleton] at hx
    rw [hx]; exact hkd0
  | u, (_, L) :: (t, L') :: rest, x, hx => by
    match L with
    | 0 => simp [buildReplRows, buildRow7] at hx
    | L0 + 1 =>
      simp only [buildReplRows, buildRow7, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact hkd0
      · exact buildReplRows_tags 0 (by omega) _ ((t, L') :: rest) x hx'

theorem buildReplRows_struct (kd0 : ℕ) :
    ∀ (repl : List (ℕ × ℕ)) (u : List ℕ), PermW 7 u →
      (∀ p ∈ repl, 1 ≤ p.2 ∧ p.2 ≤ 6) →
      (∀ x ∈ buildReplRows kd0 u repl, ∀ w ∈ x.2, PermW 7 w) ∧
      (∀ x ∈ buildReplRows kd0 u repl, x.2 ≠ []) ∧
      (∀ x ∈ buildReplRows kd0 u repl, x.2.length ≤ 6) ∧
      (∀ x ∈ buildReplRows kd0 u repl, List.IsChain (WLink 7 2) x.2) ∧
      List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
        LinkK 7 y.1 (x.2.getLast hx) (y.2.head hy)) (buildReplRows kd0 u repl)
  | [], _, _, _ => ⟨by simp [buildReplRows], by simp [buildReplRows], by simp [buildReplRows],
      by simp [buildReplRows], List.isChain_nil⟩
  | [(_, L)], u, hu, hL => by
    have ⟨hL1, hL6⟩ := hL _ List.mem_cons_self
    have hne : buildRow7 u L ≠ [] := by match L, hL1 with | _ + 1, _ => exact List.cons_ne_nil _ _
    refine ⟨?_, ?_, ?_, ?_, List.isChain_singleton _⟩
    · intro x hx w hw; simp only [buildReplRows, List.mem_singleton] at hx; rw [hx] at hw
      exact buildRow7_permW L u hu w hw
    · intro x hx; simp only [buildReplRows, List.mem_singleton] at hx; rw [hx]; exact hne
    · intro x hx; simp only [buildReplRows, List.mem_singleton] at hx; rw [hx]
      rw [buildRow7_length]; exact hL6
    · intro x hx; simp only [buildReplRows, List.mem_singleton] at hx; rw [hx]
      exact buildRow7_doors L u hu
  | (_, L) :: (t, L') :: rest, u, hu, hL => by
    have ⟨hL1, hL6⟩ := hL _ List.mem_cons_self
    have hLrest : ∀ p ∈ (t, L') :: rest, 1 ≤ p.2 ∧ p.2 ≤ 6 :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    match L, hL1 with
    | L0 + 1, _ =>
      let row := u :: buildRow7 (tau2 7 u) L0
      have hrow_perm : ∀ w ∈ row, PermW 7 w := buildRow7_permW (L0 + 1) u hu
      have he_perm : PermW 7 (row.getLast (List.cons_ne_nil _ _)) := hrow_perm _ (List.getLast_mem _)
      let u' := w3Step (row.getLast (List.cons_ne_nil _ _)) t
      have hu' : PermW 7 u' := permW_w3Step he_perm t
      obtain ⟨ihw, ihne, ihsz, ihd, ihl⟩ := buildReplRows_struct 0 ((t, L') :: rest) u' hu' hLrest
      simp only [buildReplRows, buildRow7]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx w hw
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hrow_perm w hw
        · exact ihw x hx' w hw
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.cons_ne_nil _ _
        · exact ihne x hx'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · change (buildRow7 u (L0 + 1)).length ≤ 6; rw [buildRow7_length]; exact hL6
        · exact ihsz x hx'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact buildRow7_doors (L0 + 1) u hu
        · exact ihd x hx'
      · have hne_tl := buildReplRows_ne_nil 0 u' ((t, L') :: rest) (List.cons_ne_nil _ _)
          (fun p hp => (hLrest p hp).1)
        obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne_tl
        rw [hy] at ihl ⊢
        refine List.isChain_cons_cons.mpr ⟨?_, ihl⟩
        intro hx hy'
        obtain ⟨h2, hy1, hyhead⟩ := buildReplRows_head 0 u' ((t, L') :: rest) (List.cons_ne_nil _ _)
          (fun p hp => (hLrest p hp).1) hne_tl
        simp only [hy, List.head_cons] at hy1 hyhead
        rw [hy1, hyhead]
        exact ⟨fun _ => wlink3_w3Step he_perm t, fun h1 => absurd h1 (by omega)⟩

theorem pairwise_of_listNoDupB : ∀ (l : List (List ℕ)),
    (∀ w ∈ l, PermW 7 w) → listNoDupB (l.map rotTo7) = true → List.Pairwise (fun u v => ¬ u ~r v) l
  | [], _, _ => List.Pairwise.nil
  | a :: t, hperm, h => by
    simp only [List.map_cons, listNoDupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.pairwise_cons.mpr ⟨?_, pairwise_of_listNoDupB t (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) h.2⟩
    intro b hb hr
    have heq := rotTo7_eq_of_isRotated (hperm a List.mem_cons_self) (hperm b (List.mem_cons_of_mem _ hb)) hr
    have hmem : rotTo7 a ∈ t.map rotTo7 := List.mem_map.mpr ⟨b, hb, heq.symm⟩
    have hcont : (t.map rotTo7).contains (rotTo7 a) = true := List.contains_iff_mem.mpr hmem
    rw [hcont] at h
    exact Bool.false_ne_true h.1.symm

/-! ### Generic Splicing Lemma for `IsSeq 7` -/

private theorem linksT_append_nonempty (A B : List TRow) (hA : A ≠ []) (hB : B ≠ []) :
    linksT (A ++ B) = linksT A + (if (B.head hB).1 = 0 then 0 else 1) + linksT B := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hA
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hB
  simp only [List.cons_append, linksT, List.tail_cons, List.head_cons, List.countP_append,
    List.countP_cons]
  by_cases hb : b.1 = 0 <;> simp [hb] <;> omega

theorem linksT_splice (U M R W : List TRow) (hM : M ≠ []) (hR : R ≠ [])
    (hkd : (R.head hR).1 = (M.head hM).1) :
    linksT (U ++ R ++ W) + linksT M = linksT (U ++ M ++ W) + linksT R := by
  have hUM : U ++ M ≠ [] := by intro h; exact hM (List.append_eq_nil_iff.mp h).2
  have hUR : U ++ R ≠ [] := by intro h; exact hR (List.append_eq_nil_iff.mp h).2
  have h1 : linksT (U ++ R) + linksT M = linksT (U ++ M) + linksT R := by
    cases U with
    | nil => simp; omega
    | cons u us =>
      rw [linksT_append_nonempty (u :: us) R (List.cons_ne_nil _ _) hR,
        linksT_append_nonempty (u :: us) M (List.cons_ne_nil _ _) hM, hkd]
      omega
  cases W with
  | nil => simpa using h1
  | cons w ws =>
    rw [linksT_append_nonempty (U ++ R) (w :: ws) hUR (List.cons_ne_nil _ _),
      linksT_append_nonempty (U ++ M) (w :: ws) hUM (List.cons_ne_nil _ _)]
    omega

private theorem isChain_append_iff {α : Type} {r : α → α → Prop} (A B : List α) :
    List.IsChain r (A ++ B) ↔
      List.IsChain r A ∧ List.IsChain r B ∧
      ∀ (hA : A ≠ []) (hB : B ≠ []), r (A.getLast hA) (B.head hB) := by
  induction A with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      cases B with
      | nil => simp
      | cons b bs =>
        simp only [List.cons_append, List.nil_append, List.isChain_cons_cons, List.isChain_singleton,
          true_and, ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_singleton,
          List.head_cons, forall_const]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, fun _ => h1⟩, fun ⟨h1, h2⟩ => ⟨h2 (List.cons_ne_nil b bs), h1⟩⟩
    | cons a2 t2 =>
      simp only [List.cons_append, List.isChain_cons_cons]
      rw [← List.cons_append, ih]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨h1, h2⟩, h3, fun _ hB => ?_⟩
        rw [List.getLast_cons (List.cons_ne_nil a2 t2)]
        exact h4 (List.cons_ne_nil a2 t2) hB
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        refine ⟨h1, h2, h3, fun _ hB => ?_⟩
        have h := h4 (List.cons_ne_nil a (a2 :: t2)) hB
        rwa [List.getLast_cons (List.cons_ne_nil a2 t2)] at h

private theorem getLast_append_snd_getLast (U M : List TRow) (hM : M ≠ [])
    (hUM : U ++ M ≠ []) (h1 : ((U ++ M).getLast hUM).2 ≠ []) (h2 : (M.getLast hM).2 ≠ []) :
    ((U ++ M).getLast hUM).2.getLast h1 = (M.getLast hM).2.getLast h2 := by
  have heq : (U ++ M).getLast hUM = M.getLast hM := List.getLast_append_of_ne_nil hUM hM
  rw [← getLastD_of_ne_nil _ [] h1, ← getLastD_of_ne_nil _ [] h2, heq]

theorem isSeq_splice (U M R W : List TRow)
    (hL : IsSeq 7 (U ++ M ++ W))
    (hM : M ≠ []) (hR : R ≠ [])
    (hR_w : ∀ x ∈ R, ∀ w ∈ x.2, PermW 7 w)
    (hR_ne : ∀ x ∈ R, x.2 ≠ [])
    (hR_sz : ∀ x ∈ R, x.2.length ≤ 6)
    (hR_d : ∀ x ∈ R, List.IsChain (WLink 7 2) x.2)
    (hR_l : List.IsChain (fun x y : TRow => ∀ (hx : x.2 ≠ []) (hy : y.2 ≠ []),
      LinkK 7 y.1 (x.2.getLast hx) (y.2.head hy)) R)
    (hR_cl : List.Pairwise (fun u v => ¬ u ~r v) (R.map Prod.snd).flatten)
    (hkd : (R.head hR).1 = (M.head hM).1)
    (hhead : (R.head hR).2.head (hR_ne _ (List.head_mem hR)) =
      (M.head hM).2.head (hL.pieces_ne _ (by simp [List.head_mem hM])))
    (hlast : (R.getLast hR).2.getLast (hR_ne _ (List.getLast_mem hR)) =
      (M.getLast hM).2.getLast (hL.pieces_ne _ (by simp [List.getLast_mem hM])))
    (hsub : ∀ w ∈ (R.map Prod.snd).flatten, ∃ v ∈ (M.map Prod.snd).flatten, w ~r v) :
    IsSeq 7 (U ++ R ++ W) := by
  have hU_mem : ∀ x ∈ U, x ∈ U ++ M ++ W := fun x hx => by simp [hx]
  have hW_mem : ∀ x ∈ W, x ∈ U ++ M ++ W := fun x hx => by simp [hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact hL.words x (hU_mem x h) w hw
    · exact hR_w x h w hw
    · exact hL.words x (hW_mem x h) w hw
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact hL.pieces_ne x (hU_mem x h)
    · exact hR_ne x h
    · exact hL.pieces_ne x (hW_mem x h)
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact hL.size_le x (hU_mem x h)
    · exact hR_sz x h
    · exact hL.size_le x (hW_mem x h)
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact hL.doors x (hU_mem x h)
    · exact hR_d x h
    · exact hL.doors x (hW_mem x h)
  · have hlinks := hL.links
    rw [isChain_append_iff, isChain_append_iff] at hlinks ⊢
    obtain ⟨⟨hU_l, hM_l, hUM_l⟩, hW_l, hUMW_l⟩ := hlinks
    refine ⟨⟨hU_l, hR_l, fun hU _ => ?_⟩, hW_l, fun hUR hW => ?_⟩
    · intro hx hy
      have h := hUM_l hU hM hx (hL.pieces_ne _ (by simp [List.head_mem hM]))
      rw [hkd, hhead]
      exact h
    · intro hx hy
      have hUM : U ++ M ≠ [] := by intro h; exact hM (List.append_eq_nil_iff.mp h).2
      have hM_last_ne : (M.getLast hM).2 ≠ [] := hL.pieces_ne _ (by simp [List.getLast_mem hM])
      have hUM_last_ne : ((U ++ M).getLast hUM).2 ≠ [] := by
        rw [List.getLast_append_of_ne_nil hUM hM]; exact hM_last_ne
      have h := hUMW_l hUM hW hUM_last_ne hy
      rw [getLast_append_snd_getLast U M hM hUM hUM_last_ne hM_last_ne] at h
      rw [getLast_append_snd_getLast U R hR hUR hx (hR_ne _ (List.getLast_mem hR)), hlast]
      exact h
  · have hcl := hL.classes
    simp only [List.map_append, List.flatten_append, List.pairwise_append] at hcl ⊢
    obtain ⟨⟨hU_c, hM_c, hUM_c⟩, hW_c, hUMW_c⟩ := hcl
    refine ⟨⟨hU_c, hR_cl, fun u hu r hr => ?_⟩, hW_c, fun x hx w hw => ?_⟩
    · obtain ⟨m, hm, hrm⟩ := hsub r hr
      intro hur
      exact hUM_c u hu m hm (hur.trans hrm)
    · rcases List.mem_append.mp hx with hu | hr
      · exact hUMW_c x (List.mem_append_left _ hu) w hw
      · obtain ⟨m, hm, hrm⟩ := hsub x hr
        intro hxw
        exact hUMW_c m (List.mem_append_right _ hm) w hw (hrm.symm.trans hxw)

/-! ### `NoM3` and `NoW4` Predicates and Soundness Theorems -/

/-- Check whether `R0, R1, R2` (with `R1.1 = 0, R2.1 = 0`) match an `m3Witnesses` index `idx`. -/
def matchesM3Idx (R0 R1 R2 : TRow) (idx : ℕ) : Prop :=
  R1.1 = 0 ∧ R2.1 = 0 ∧
  ∃ (t0 t1 : ℕ) (h0 : R0.2 ≠ []) (h1 : R1.2 ≠ []) (h2 : R2.2 ≠ []),
    t0 < 5 ∧ t1 < 5 ∧
    R1.2.head h1 = w3Step (R0.2.getLast h0) t0 ∧
    R2.2.head h2 = w3Step (R1.2.getLast h1) t1 ∧
    idx = ((R0.2.length - 1) * 30 + t0 * 6 + (R1.2.length - 1)) * 30 + t1 * 6 + (R2.2.length - 1)

/-- Check whether `R1, R2` (with `R2.1 = 1`) match a `w4Witnesses` entry `(l1, t4, l2)`. -/
def matchesW4Entry (R1 R2 : TRow) (l1 t4 l2 : ℕ) : Prop :=
  R2.1 = 1 ∧ R1.2.length = l1 ∧ R2.2.length = l2 ∧ t4 < 23 ∧
  ∃ (h1 : R1.2 ≠ []) (h2 : R2.2 ≠ []),
    R2.2.head h2 = w4Step (R1.2.getLast h1) t4

/-- Sequence has no 3-row `w3` motif whose index is forbidden by `buildM3Allow`. -/
def NoM3 (L : List TRow) : Prop :=
  ∀ U R0 R1 R2 W idx, L = U ++ [R0, R1, R2] ++ W → matchesM3Idx R0 R1 R2 idx →
    buildM3Allow.get! idx ≠ 0

/-- Sequence has no 2-row `w4` transition whose bit is cleared in `buildW4Allow`. -/
def NoW4 (L : List TRow) : Prop :=
  ∀ U R1 R2 W l1 t4 l2, L = U ++ [R1, R2] ++ W → matchesW4Entry R1 R2 l1 t4 l2 →
    ((buildW4Allow.get! ((l1 - 1) * 23 + t4)).toNat >>> (l2 - 1)) % 2 = 1

private theorem ba_set_get_ne (ba : ByteArray) (j idx : ℕ) (v : UInt8) (hne : idx ≠ j) :
    (ba.set! j v).get! idx = ba.get! idx := by
  simp only [ByteArray.set!, ByteArray.get!, Array.set!, Array.setIfInBounds]
  by_cases hj : j < ba.data.size
  · simp only [hj, dite_true]
    by_cases hidx : idx < ba.data.size
    · have hidx' : idx < (ba.data.set j v hj).size := by rw [Array.size_set]; exact hidx
      rw [getElem!_pos _ idx hidx', Array.getElem_set_ne (h := fun h => hne h.symm),
        getElem!_pos _ idx hidx]
    · have hidx' : ¬ idx < (ba.data.set j v hj).size := by rw [Array.size_set]; exact hidx
      rw [getElem!_neg _ idx hidx', getElem!_neg _ idx hidx]
  · simp only [hj, dite_false]

private theorem ba_set_get_eq (ba : ByteArray) (j : ℕ) (v : UInt8) (hj : j < ba.size) :
    (ba.set! j v).get! j = v := by
  have hj' : j < ba.data.size := hj
  simp only [ByteArray.set!, ByteArray.get!, Array.set!, Array.setIfInBounds, hj', dite_true]
  have hlt : j < (ba.data.set j v hj').size := by rw [Array.size_set]; exact hj'
  rw [getElem!_pos (ba.data.set j v hj') j hlt, Array.getElem_set_self]

private theorem foldl_m3_zero_imp (ws : List (ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ)))
    (ba : ByteArray) (idx : ℕ) (hba : ba.size = 5400) (hinit : ba.get! idx ≠ 0)
    (h0 : (ws.foldl (fun b (l0, t0, l1, t1, l2, _) =>
        let j := ((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1)
        b.set! j 0) ba).get! idx = 0) :
    ∃ w ∈ ws, let (l0, t0, l1, t1, l2, _) := w
      idx = ((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1) := by
  induction ws generalizing ba with
  | nil => exact absurd h0 hinit
  | cons w rest ih =>
    rcases w with ⟨l0, t0, l1, t1, l2, repl⟩
    set j := ((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1)
    by_cases heq : idx = j
    · exact ⟨(l0, t0, l1, t1, l2, repl), List.mem_cons_self, heq⟩
    · have hget := ba_set_get_ne ba j idx 0 heq
      have hsz : (ba.set! j 0).size = 5400 := by rw [ByteArray.size_set!, hba]
      obtain ⟨w', hw', hidx⟩ := ih (ba.set! j 0) hsz (by rw [hget]; exact hinit) h0
      exact ⟨w', List.mem_cons_of_mem _ hw', hidx⟩

theorem m3Allow_zero_imp {idx : ℕ} (hidx : idx < 5400) (h0 : buildM3Allow.get! idx = 0) :
    ∃ w ∈ m3Witnesses, let (l0, t0, l1, t1, l2, _) := w
      idx = ((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1) := by
  apply foldl_m3_zero_imp m3Witnesses (ByteArray.mk (Array.replicate 5400 1)) idx
  · simp [ByteArray.size]
  · simp [ByteArray.get!, getElem!_pos, hidx]
  · exact h0

private theorem bit_and_clear_ne {cur : UInt8} {b1 b2 : ℕ} (hb1 : b1 < 6) (hb2 : b2 < 6) (hne : b1 ≠ b2) :
    ((cur &&& UInt8.ofNat (63 - (1 <<< b2))).toNat >>> b1) % 2 = (cur.toNat >>> b1) % 2 := by
  have hmask : (UInt8.ofNat (63 - (1 <<< b2))).toNat = 63 - (1 <<< b2) := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt]
    match b2, hb2 with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  rw [UInt8.toNat_and, hmask]
  have hbit : ∀ a : ℕ, (a >>> b1) % 2 = if a.testBit b1 then 1 else 0 := by
    intro a
    rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
    have hlt2 : (a >>> b1) % 2 < 2 := Nat.mod_lt _ (by omega)
    match h : (a >>> b1) % 2, hlt2 with
    | 0, _ => rfl
    | 1, _ => rfl
  rw [hbit, hbit, Nat.testBit_and]
  have htrue : (63 - (1 <<< b2)).testBit b1 = true := by
    match b1, hb1, b2, hb2 with
    | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ | 4, _, 4, _ | 5, _, 5, _ => exact absurd rfl hne
    | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _
    | 1, _, 0, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _
    | 2, _, 0, _ | 2, _, 1, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _
    | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 4, _ | 3, _, 5, _
    | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 5, _
    | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ => decide
  rw [htrue, Bool.and_true]

private theorem foldl_w4_bit_zero_imp (ws : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)))
    (ba : ByteArray) (idx b : ℕ) (hba : ba.size = 138) (hidx : idx < 138) (hb : b < 6)
    (hws : ∀ w ∈ ws, 1 ≤ w.2.2.1 ∧ w.2.2.1 ≤ 6)
    (hinit : ((ba.get! idx).toNat >>> b) % 2 = 1)
    (h0 : (((ws.foldl (fun a (l1, t4, l2, _) =>
        let j := (l1 - 1) * 23 + t4
        let cur := a.get! j
        a.set! j (cur &&& UInt8.ofNat (63 - (1 <<< (l2 - 1))))) ba).get! idx).toNat >>> b) % 2 ≠ 1) :
    ∃ w ∈ ws, let (l1, t4, l2, _) := w
      idx = (l1 - 1) * 23 + t4 ∧ b = l2 - 1 := by
  induction ws generalizing ba with
  | nil => exact absurd hinit h0
  | cons w rest ih =>
    rcases w with ⟨l1, t4, l2, repl⟩
    have hl2 : 1 ≤ l2 ∧ l2 ≤ 6 := hws (l1, t4, l2, repl) List.mem_cons_self
    set j := (l1 - 1) * 23 + t4
    by_cases hmatch : idx = j ∧ b = l2 - 1
    · exact ⟨(l1, t4, l2, repl), List.mem_cons_self, hmatch⟩
    · set v := ba.get! j &&& UInt8.ofNat (63 - (1 <<< (l2 - 1)))
      have hkeep : (((ba.set! j v).get! idx).toNat >>> b) % 2 = 1 := by
        by_cases heq : idx = j
        · have hne : b ≠ l2 - 1 := fun h => hmatch ⟨heq, h⟩
          rw [← heq, ba_set_get_eq ba idx v (by omega)]
          dsimp only [v]
          rw [← heq, bit_and_clear_ne hb (by omega) hne, hinit]
        · rw [ba_set_get_ne ba j idx v heq, hinit]
      have hsz : (ba.set! j v).size = 138 := by rw [ByteArray.size_set!, hba]
      obtain ⟨w', hw', hm⟩ := ih (ba.set! j v) hsz (fun x hx => hws x (List.mem_cons_of_mem _ hx)) hkeep h0
      exact ⟨w', List.mem_cons_of_mem _ hw', hm⟩

theorem w4Allow_bit_zero_imp {idx b : ℕ} (hidx : idx < 138) (hb : b < 6)
    (h0 : ((buildW4Allow.get! idx).toNat >>> b) % 2 ≠ 1) :
    ∃ w ∈ w4Witnesses, let (l1, t4, l2, _) := w
      idx = (l1 - 1) * 23 + t4 ∧ b = l2 - 1 := by
  have hws : ∀ w ∈ w4Witnesses, 1 ≤ w.2.2.1 ∧ w.2.2.1 ≤ 6 := by
    intro w hw
    have hv := List.all_eq_true.mp w4Witnesses_valid w hw
    rcases w with ⟨l1, t4, l2, repl⟩
    unfold checkW4One at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hl2_1⟩, hl2_6⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hv
    exact ⟨hl2_1, hl2_6⟩
  apply foldl_w4_bit_zero_imp w4Witnesses (ByteArray.mk (Array.replicate 138 63)) idx b
    (by simp [ByteArray.size]) hidx hb hws
  · have hget : (ByteArray.mk (Array.replicate 138 (63 : UInt8))).get! idx = (63 : UInt8) := by
      simp [ByteArray.get!, getElem!_pos, hidx]
    rw [hget]
    match b, hb with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  · exact h0

/-! ### `NoM3` and `NoW4` for Minimal Counterexamples -/

theorem relabSeq_length (e : List ℕ) (L : List TRow) : (relabSeq e L).length = L.length := by
  simp [relabSeq]

theorem relabSeq_linksT (e : List ℕ) (L : List TRow) : linksT (relabSeq e L) = linksT L := by
  cases L with
  | nil => rfl
  | cons a t =>
    simp only [relabSeq, List.map_cons, linksT, List.tail_cons, List.countP_map]
    rfl

theorem relabSeq_holesT (e : List ℕ) (L : List TRow) : holesT 7 (relabSeq e L) = holesT 7 L := by
  unfold holesT relabSeq
  simp [List.map_map, Function.comp_def]

theorem relabSeq_tags (e : List ℕ) (L : List TRow) (ht : ∀ x ∈ L, x.1 ≤ 1) :
    ∀ x ∈ relabSeq e L, x.1 ≤ 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact ht y hy

/-- **Soundness of `M3` dominance (`buildM3Allow`):**
Under `hM3 : ∀ x, lo ≤ x → x ≤ hi → ∀ y < x, P s y + x ≤ P s x + y`, any sequence `L` of length
`n` exceeding `P s (holesT 7 L)` whose strictly shorter `s`-link sequences obey `P s` has `NoM3 L`! -/
theorem noM3_of_min_rows {P : ℕ → ℕ → ℕ} {s lo hi : ℕ}
    (hM3 : ∀ x, lo ≤ x → x ≤ hi → ∀ y, y < x → P s y + x ≤ P s x + y)
    (hshort : ∀ L' : List TRow, L'.length < L.length → IsSeq 7 L' → (∀ x ∈ L', x.1 ≤ 1) →
      linksT L' = s → holesT 7 L' < hi + 1 → L'.length ≤ P s (holesT 7 L'))
    (hL : IsSeq 7 L) (htag : ∀ x ∈ L, x.1 ≤ 1) (hlinks : linksT L = s)
    (hlo : lo ≤ holesT 7 L) (hhi : holesT 7 L ≤ hi) (hgt : P s (holesT 7 L) < L.length) :
    NoM3 L := by
  intro U R0 R1 R2 W idx hEq hmatch hzero
  obtain ⟨hR1_k, hR2_k, t0, t1, h0ne, h1ne, h2ne, ht0, ht1, hhead1, hhead2, hidx_eq⟩ := hmatch
  have hR0_mem : R0 ∈ L := by rw [hEq]; simp
  have hR1_mem : R1 ∈ L := by rw [hEq]; simp
  have hR2_mem : R2 ∈ L := by rw [hEq]; simp
  have hL0_le := hL.size_le R0 hR0_mem
  have hL1_le := hL.size_le R1 hR1_mem
  have hL2_le := hL.size_le R2 hR2_mem
  have hL0_pos : 1 ≤ R0.2.length := List.length_pos_iff.mpr h0ne
  have hL1_pos : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
  have hL2_pos : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
  have hidx_lt : idx < 5400 := by omega
  obtain ⟨⟨l0, t0', l1, t1', l2, repl⟩, hw_mem, hidx'⟩ := m3Allow_zero_imp hidx_lt hzero
  have hv := List.all_eq_true.mp m3Witnesses_valid _ hw_mem
  unfold checkM3One at hv
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl0_1, hl0_6⟩, ht0'⟩, hl1_1⟩, hl1_6⟩, ht1'⟩, hl2_1⟩, hl2_6⟩,
    hrepl_neB⟩, _⟩, hrepl_allB⟩, hnodup⟩, hsubc⟩, hexit⟩, hrlen⟩, hhrlt⟩, hvle⟩ := hv
  have hrepl_ne : repl ≠ [] := by intro h; subst h; simp at hrepl_neB
  have hrepl_all : ∀ p ∈ repl, p.1 < 5 ∧ 1 ≤ p.2 ∧ p.2 ≤ 6 := by
    intro p hp
    have := List.all_eq_true.mp hrepl_allB p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hdec0 : l0 = R0.2.length := by omega
  have hdec1 : t0' = t0 := by omega
  have hdec2 : l1 = R1.2.length := by omega
  have hdec3 : t1' = t1 := by omega
  have hdec4 : l2 = R2.2.length := by omega
  rw [hdec0, hdec1, hdec2, hdec3, hdec4] at hsubc hexit hhrlt hvle
  -- Relabel L so R0.head becomes id7!
  set v0 := R0.2.head h0ne
  have hv0 : PermW 7 v0 := hL.words R0 hR0_mem v0 (List.head_mem h0ne)
  have hL1 := hL.relabel hv0
  have hEq1 : relabSeq v0 L = relabSeq v0 U ++ relabSeq v0 [R0, R1, R2] ++ relabSeq v0 W := by
    rw [hEq]; simp [relabSeq]
  set M1 := relabSeq v0 [R0, R1, R2]
  have hM1_eq : M1 = buildOrigM3 R0.1 R0.2.length t0 R1.2.length t1 R2.2.length := by
    have hM_inf : IsSeq 7 M1 := hL1.infix ⟨relabSeq v0 U, relabSeq v0 W, hEq1.symm⟩
    have hcl := hM_inf.classes
    simp only [M1, relabSeq, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.pairwise_append] at hcl
    have hR0' : R0.2.map (List.map (S.relab v0)) = buildRow7 id7 R0.2.length := by
      have hne' : R0.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h0ne
      have hch := S.door_chain (by omega) _ (hM_inf.words _ List.mem_cons_self)
        (hM_inf.doors _ List.mem_cons_self) hcl.1
      have hh : (R0.2.map (List.map (S.relab v0))).head hne' = id7 := by
        rw [List.head_map]; exact (S.map_relab_self hv0.1).trans (by rw [hv0.2.1]; rfl)
      have := eq_buildRow7_of_chain _ id7 hne' hh hch
      simpa using this
    have he0' : (buildRow7 id7 R0.2.length).getLastD id7 = (R0.2.getLast h0ne).map (S.relab v0) := by
      rw [← hR0']
      have hne' : R0.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h0ne
      rw [getLastD_of_ne_nil _ _ hne', List.getLast_map]
    have hR1' : R1.2.map (List.map (S.relab v0)) =
        buildRow7 (w3Step ((buildRow7 id7 R0.2.length).getLastD id7) t0) R1.2.length := by
      have hne' : R1.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h1ne
      have hmem1 : (R1.1, R1.2.map (List.map (S.relab v0))) ∈ M1 :=
        List.mem_cons_of_mem _ List.mem_cons_self
      have hch := S.door_chain (by omega) _ (hM_inf.words _ hmem1) (hM_inf.doors _ hmem1) hcl.2.1.1
      have hh : (R1.2.map (List.map (S.relab v0))).head hne' =
          w3Step ((buildRow7 id7 R0.2.length).getLastD id7) t0 := by
        rw [List.head_map, hhead1, he0', w3Step_map _ (hL.words R0 hR0_mem _ (List.getLast_mem h0ne)).2.1]
      have := eq_buildRow7_of_chain _ _ hne' hh hch
      simpa using this
    have he1' : (buildRow7 (w3Step ((buildRow7 id7 R0.2.length).getLastD id7) t0) R1.2.length).getLastD id7 =
        (R1.2.getLast h1ne).map (S.relab v0) := by
      rw [← hR1']
      have hne' : R1.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h1ne
      rw [getLastD_of_ne_nil _ _ hne', List.getLast_map]
    have hR2' : R2.2.map (List.map (S.relab v0)) =
        buildRow7 (w3Step ((buildRow7 (w3Step ((buildRow7 id7 R0.2.length).getLastD id7) t0) R1.2.length).getLastD id7) t1) R2.2.length := by
      have hne' : R2.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h2ne
      have hmem2 : (R2.1, R2.2.map (List.map (S.relab v0))) ∈ M1 :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have hch := S.door_chain (by omega) _ (hM_inf.words _ hmem2) (hM_inf.doors _ hmem2) hcl.2.1.2.1
      have hh : (R2.2.map (List.map (S.relab v0))).head hne' =
          w3Step ((buildRow7 (w3Step ((buildRow7 id7 R0.2.length).getLastD id7) t0) R1.2.length).getLastD id7) t1 := by
        rw [List.head_map, hhead2, he1', w3Step_map _ (hL.words R1 hR1_mem _ (List.getLast_mem h1ne)).2.1]
      have := eq_buildRow7_of_chain _ _ hne' hh hch
      simpa using this
    simp [M1, relabSeq, buildOrigM3, hR0', hR1', hR2', hR1_k, hR2_k]
  set R' := buildReplRows R0.1 id7 repl
  have hR'_ne : R' ≠ [] := buildReplRows_ne_nil R0.1 id7 repl hrepl_ne (fun p hp => (hrepl_all p hp).2.1)
  have hM1_ne : M1 ≠ [] := by simp [M1, relabSeq]
  obtain ⟨hR'_w, hR'_pe, hR'_sz, hR'_d, hR'_l⟩ :=
    buildReplRows_struct R0.1 repl id7 id7_permW (fun p hp => (hrepl_all p hp).2)
  have hR'_cl : List.Pairwise (fun u v => ¬ u ~r v) (R'.map Prod.snd).flatten := by
    apply pairwise_of_listNoDupB
    · intro w hw
      obtain ⟨P, hP, hwP⟩ := List.mem_flatten.mp hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hP
      exact hR'_w x hx w hwP
    · rw [buildReplRows_kd0_indep_snd R0.1 id7 repl]
      exact hnodup
  obtain ⟨h2, hR'_kd, hR'_hd⟩ := buildReplRows_head R0.1 id7 repl hrepl_ne
    (fun p hp => (hrepl_all p hp).2.1) hR'_ne
  have hM1_hd : (M1.head hM1_ne).1 = R0.1 ∧
      (M1.head hM1_ne).2.head (hL1.pieces_ne _ (by rw [hEq1]; simp [List.head_mem hM1_ne])) = id7 := by
    refine ⟨rfl, ?_⟩
    simp only [M1, relabSeq, List.map_cons, List.head_cons, List.head_map]
    exact (S.map_relab_self hv0.1).trans (by rw [hv0.2.1]; rfl)
  have hM1_snd : M1.map Prod.snd = (buildOrigM3 0 R0.2.length t0 R1.2.length t1 R2.2.length).map Prod.snd := by
    rw [hM1_eq]; rfl
  have hR'_last : (R'.getLast hR'_ne).2.getLast (hR'_pe _ (List.getLast_mem hR'_ne)) =
      (M1.getLast hM1_ne).2.getLast (hL1.pieces_ne _ (by rw [hEq1]; simp [List.getLast_mem hM1_ne])) := by
    have hlR : (R'.getLast hR'_ne).2 = ((buildReplRows 0 id7 repl).getLastD (0, [])).2 := by
      rw [← getLastD_of_ne_nil _ (0, []) hR'_ne]; exact buildReplRows_kd0_last R0.1 id7 repl
    have hlM : (M1.getLast hM1_ne).2 = ((buildOrigM3 0 R0.2.length t0 R1.2.length t1 R2.2.length).getLastD (0, [])).2 := by
      rw [← getLastD_of_ne_nil _ (0, []) hM1_ne, hM1_eq]; rfl
    rw [← getLastD_of_ne_nil _ [] (hR'_pe _ (List.getLast_mem hR'_ne)),
      ← getLastD_of_ne_nil _ [] (hL1.pieces_ne _ (by rw [hEq1]; simp [List.getLast_mem hM1_ne])),
      hlR, hlM]
    exact hexit
  have hR'_sub : ∀ w ∈ (R'.map Prod.snd).flatten, ∃ v ∈ (M1.map Prod.snd).flatten, w ~r v := by
    intro w hw
    rw [buildReplRows_kd0_indep_snd R0.1 id7 repl] at hw
    have hw_in : rotTo7 w ∈ allCanons (buildReplRows 0 id7 repl) := List.mem_map.mpr ⟨w, hw, rfl⟩
    have hc := List.all_eq_true.mp hsubc (rotTo7 w) hw_in
    have hmem := List.contains_iff_mem.mp hc
    obtain ⟨v, hv, hrot⟩ := List.mem_map.mp hmem
    rw [← hM1_snd] at hv
    exact ⟨v, hv, isRotated_of_rotTo7_eq hrot.symm⟩
  set L' := relabSeq v0 U ++ R' ++ relabSeq v0 W
  have hL'_seq : IsSeq 7 L' :=
    isSeq_splice (relabSeq v0 U) M1 R' (relabSeq v0 W) (hEq1 ▸ hL1) hM1_ne hR'_ne
      hR'_w hR'_pe hR'_sz hR'_d hR'_l hR'_cl (hR'_kd.trans hM1_hd.1.symm)
      (by convert hR'_hd.trans hM1_hd.2.symm) hR'_last hR'_sub
  have hL'_tag : ∀ x ∈ L', x.1 ≤ 1 := by
    intro x hx
    simp only [L', List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact relabSeq_tags v0 U (fun y hy => htag y (by rw [hEq]; simp [hy])) x h
    · exact buildReplRows_tags R0.1 (htag R0 hR0_mem) id7 repl x h
    · exact relabSeq_tags v0 W (fun y hy => htag y (by rw [hEq]; simp [hy])) x h
  have hL'_links : linksT L' = s := by
    have hls := linksT_splice (relabSeq v0 U) M1 R' (relabSeq v0 W) hM1_ne hR'_ne (hR'_kd.trans hM1_hd.1.symm)
    have hM1_l : linksT M1 = 0 := by simp [M1, relabSeq, linksT, hR1_k, hR2_k]
    have hR'_lk : linksT R' = 0 := buildReplRows_linksT R0.1 id7 repl
    have hU_M1_W : linksT (relabSeq v0 U ++ M1 ++ relabSeq v0 W) = s := by
      rw [← hEq1, relabSeq_linksT, hlinks]
    rw [hU_M1_W, hM1_l, hR'_lk] at hls
    exact Nat.add_zero (linksT L') ▸ hls
  have hM1_holes : holesT 7 M1 = holesT 7 (buildOrigM3 0 R0.2.length t0 R1.2.length t1 R2.2.length) := by
    rw [hM1_eq]; simp [buildOrigM3, holesT]
  have hR'_holes : holesT 7 R' = holesT 7 (buildReplRows 0 id7 repl) := buildReplRows_kd0_holesT R0.1 id7 repl
  have hL'_holes : holesT 7 L' + holesT 7 M1 = holesT 7 L + holesT 7 R' := by
    have h1 := congrArg (holesT 7) hEq1
    rw [relabSeq_holesT, PS.holesT_append, PS.holesT_append] at h1
    simp only [L', PS.holesT_append]
    omega
  have hL'_len : L'.length + 3 = L.length + (buildReplRows 0 id7 repl).length := by
    have h1 := congrArg List.length hEq1
    rw [relabSeq_length, List.length_append, List.length_append] at h1
    have hM1_len : M1.length = 3 := rfl
    have hR'_len : R'.length = (buildReplRows 0 id7 repl).length := buildReplRows_kd0_length R0.1 id7 repl
    simp only [L', List.length_append, hM1_len, hR'_len] at h1 ⊢
    omega
  have hL'_cap := hshort L' (by omega) hL'_seq hL'_tag hL'_links (by omega)
  have hmono := hM3 (holesT 7 L) hlo hhi (holesT 7 L') (by omega)
  omega

/-- **Soundness of `W4` dominance (`buildW4Allow`):**
Under `hW4 : ∀ x, lo ≤ x → x ≤ hi → ∀ y ≤ x + 6, P (s - 1) y + x + 5 ≤ P s x + y` and
`hlowW4 : SeqCapLt 7 (s - 1) (P (s - 1)) (hi + 7)`, any counterexample `L` has `NoW4 L`! -/
theorem noW4_of_hlow {P : ℕ → ℕ → ℕ} {s lo hi : ℕ} (hs : 1 ≤ s)
    (hW4 : ∀ x, lo ≤ x → x ≤ hi → ∀ y, y ≤ x + 6 → P (s - 1) y + x + 5 ≤ P s x + y)
    (hlowW4 : SeqCapLt 7 (s - 1) (P (s - 1)) (hi + 7))
    (hL : IsSeq 7 L) (htag : ∀ x ∈ L, x.1 ≤ 1) (hlinks : linksT L = s)
    (hlo : lo ≤ holesT 7 L) (hhi : holesT 7 L ≤ hi) (hgt : P s (holesT 7 L) < L.length) :
    NoW4 L := by
  intro U R1 R2 W l1 t4 l2 hEq hmatch
  by_contra hzero
  obtain ⟨hR2_k, hR1_len, hR2_len, ht4, h1ne, h2ne, hhead2⟩ := hmatch
  have hR1_mem : R1 ∈ L := by rw [hEq]; simp
  have hR2_mem : R2 ∈ L := by rw [hEq]; simp
  have hL1_le := hL.size_le R1 hR1_mem
  have hL2_le := hL.size_le R2 hR2_mem
  have hL1_pos : 1 ≤ R1.2.length := List.length_pos_iff.mpr h1ne
  have hL2_pos : 1 ≤ R2.2.length := List.length_pos_iff.mpr h2ne
  have hidx_lt : (l1 - 1) * 23 + t4 < 138 := by omega
  have hb_lt : l2 - 1 < 6 := by omega
  obtain ⟨⟨l1', t4', l2', repl⟩, hw_mem, hidx', hb'⟩ := w4Allow_bit_zero_imp hidx_lt hb_lt hzero
  have hv := List.all_eq_true.mp w4Witnesses_valid _ hw_mem
  unfold checkW4One at hv
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl1_1, hl1_6⟩, ht4'⟩, hl2_1⟩, hl2_6⟩, hrepl_neB⟩, hrepl_allB⟩,
    hnodup⟩, hsubc⟩, hexit⟩, hhrle⟩, hvle⟩ := hv
  have hrepl_ne : repl ≠ [] := by intro h; subst h; simp at hrepl_neB
  have hrepl_all : ∀ p ∈ repl, p.1 < 5 ∧ 1 ≤ p.2 ∧ p.2 ≤ 6 := by
    intro p hp
    have := List.all_eq_true.mp hrepl_allB p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hdec0 : l1' = l1 := by omega
  have hdec1 : t4' = t4 := by omega
  have hdec2 : l2' = l2 := by omega
  rw [hdec0, hdec1, hdec2] at hsubc hexit hhrle hvle
  -- Relabel L so R1.head becomes id7!
  set v0 := R1.2.head h1ne
  have hv0 : PermW 7 v0 := hL.words R1 hR1_mem v0 (List.head_mem h1ne)
  have hL1 := hL.relabel hv0
  have hEq1 : relabSeq v0 L = relabSeq v0 U ++ relabSeq v0 [R1, R2] ++ relabSeq v0 W := by
    rw [hEq]; simp [relabSeq]
  set M1 := relabSeq v0 [R1, R2]
  have hM1_eq : M1 = buildOrigW4 R1.1 l1 t4 l2 := by
    have hM_inf : IsSeq 7 M1 := hL1.infix ⟨relabSeq v0 U, relabSeq v0 W, hEq1.symm⟩
    have hcl := hM_inf.classes
    simp only [M1, relabSeq, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.pairwise_append] at hcl
    have hR1' : R1.2.map (List.map (S.relab v0)) = buildRow7 id7 l1 := by
      have hne' : R1.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h1ne
      have hch := S.door_chain (by omega) _ (hM_inf.words _ List.mem_cons_self)
        (hM_inf.doors _ List.mem_cons_self) hcl.1
      have hh : (R1.2.map (List.map (S.relab v0))).head hne' = id7 := by
        rw [List.head_map]; exact (S.map_relab_self hv0.1).trans (by rw [hv0.2.1]; rfl)
      have := eq_buildRow7_of_chain _ id7 hne' hh hch
      simpa [hR1_len] using this
    have he1' : (buildRow7 id7 l1).getLastD id7 = (R1.2.getLast h1ne).map (S.relab v0) := by
      rw [← hR1']
      have hne' : R1.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h1ne
      rw [getLastD_of_ne_nil _ _ hne', List.getLast_map]
    have hR2' : R2.2.map (List.map (S.relab v0)) =
        buildRow7 (w4Step ((buildRow7 id7 l1).getLastD id7) t4) l2 := by
      have hne' : R2.2.map (List.map (S.relab v0)) ≠ [] := by simpa using h2ne
      have hmem2 : (R2.1, R2.2.map (List.map (S.relab v0))) ∈ M1 :=
        List.mem_cons_of_mem _ List.mem_cons_self
      have hch := S.door_chain (by omega) _ (hM_inf.words _ hmem2) (hM_inf.doors _ hmem2) hcl.2.1
      have hh : (R2.2.map (List.map (S.relab v0))).head hne' =
          w4Step ((buildRow7 id7 l1).getLastD id7) t4 := by
        rw [List.head_map, hhead2, he1', w4Step_map _ (hL.words R1 hR1_mem _ (List.getLast_mem h1ne)).2.1]
      have := eq_buildRow7_of_chain _ _ hne' hh hch
      simpa [hR2_len] using this
    simp [M1, relabSeq, buildOrigW4, hR1', hR2', hR2_k]
  set R' := buildReplRows R1.1 id7 repl
  have hR'_ne : R' ≠ [] := buildReplRows_ne_nil R1.1 id7 repl hrepl_ne (fun p hp => (hrepl_all p hp).2.1)
  have hM1_ne : M1 ≠ [] := by simp [M1, relabSeq]
  obtain ⟨hR'_w, hR'_pe, hR'_sz, hR'_d, hR'_l⟩ :=
    buildReplRows_struct R1.1 repl id7 id7_permW (fun p hp => (hrepl_all p hp).2)
  have hR'_cl : List.Pairwise (fun u v => ¬ u ~r v) (R'.map Prod.snd).flatten := by
    apply pairwise_of_listNoDupB
    · intro w hw
      obtain ⟨P, hP, hwP⟩ := List.mem_flatten.mp hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hP
      exact hR'_w x hx w hwP
    · rw [buildReplRows_kd0_indep_snd R1.1 id7 repl]
      exact hnodup
  obtain ⟨h2, hR'_kd, hR'_hd⟩ := buildReplRows_head R1.1 id7 repl hrepl_ne
    (fun p hp => (hrepl_all p hp).2.1) hR'_ne
  have hM1_hd : (M1.head hM1_ne).1 = R1.1 ∧
      (M1.head hM1_ne).2.head (hL1.pieces_ne _ (by rw [hEq1]; simp [List.head_mem hM1_ne])) = id7 := by
    refine ⟨rfl, ?_⟩
    simp only [M1, relabSeq, List.map_cons, List.head_cons, List.head_map]
    exact (S.map_relab_self hv0.1).trans (by rw [hv0.2.1]; rfl)
  have hM1_snd : M1.map Prod.snd = (buildOrigW4 0 l1 t4 l2).map Prod.snd := by
    rw [hM1_eq]; rfl
  have hR'_last : (R'.getLast hR'_ne).2.getLast (hR'_pe _ (List.getLast_mem hR'_ne)) =
      (M1.getLast hM1_ne).2.getLast (hL1.pieces_ne _ (by rw [hEq1]; simp [List.getLast_mem hM1_ne])) := by
    have hlR : (R'.getLast hR'_ne).2 = ((buildReplRows 0 id7 repl).getLastD (0, [])).2 := by
      rw [← getLastD_of_ne_nil _ (0, []) hR'_ne]; exact buildReplRows_kd0_last R1.1 id7 repl
    have hlM : (M1.getLast hM1_ne).2 = ((buildOrigW4 0 l1 t4 l2).getLastD (0, [])).2 := by
      rw [← getLastD_of_ne_nil _ (0, []) hM1_ne, hM1_eq]; rfl
    rw [← getLastD_of_ne_nil _ [] (hR'_pe _ (List.getLast_mem hR'_ne)),
      ← getLastD_of_ne_nil _ [] (hL1.pieces_ne _ (by rw [hEq1]; simp [List.getLast_mem hM1_ne])),
      hlR, hlM]
    exact hexit
  have hR'_sub : ∀ w ∈ (R'.map Prod.snd).flatten, ∃ v ∈ (M1.map Prod.snd).flatten, w ~r v := by
    intro w hw
    rw [buildReplRows_kd0_indep_snd R1.1 id7 repl] at hw
    have hw_in : rotTo7 w ∈ allCanons (buildReplRows 0 id7 repl) := List.mem_map.mpr ⟨w, hw, rfl⟩
    have hc := List.all_eq_true.mp hsubc (rotTo7 w) hw_in
    have hmem := List.contains_iff_mem.mp hc
    obtain ⟨v, hv, hrot⟩ := List.mem_map.mp hmem
    rw [← hM1_snd] at hv
    exact ⟨v, hv, isRotated_of_rotTo7_eq hrot.symm⟩
  set L' := relabSeq v0 U ++ R' ++ relabSeq v0 W
  have hL'_seq : IsSeq 7 L' :=
    isSeq_splice (relabSeq v0 U) M1 R' (relabSeq v0 W) (hEq1 ▸ hL1) hM1_ne hR'_ne
      hR'_w hR'_pe hR'_sz hR'_d hR'_l hR'_cl (hR'_kd.trans hM1_hd.1.symm)
      (by convert hR'_hd.trans hM1_hd.2.symm) hR'_last hR'_sub
  have hL'_tag : ∀ x ∈ L', x.1 ≤ 1 := by
    intro x hx
    simp only [L', List.mem_append] at hx
    rcases hx with (h | h) | h
    · exact relabSeq_tags v0 U (fun y hy => htag y (by rw [hEq]; simp [hy])) x h
    · exact buildReplRows_tags R1.1 (htag R1 hR1_mem) id7 repl x h
    · exact relabSeq_tags v0 W (fun y hy => htag y (by rw [hEq]; simp [hy])) x h
  have hL'_links : linksT L' = s - 1 := by
    have hls := linksT_splice (relabSeq v0 U) M1 R' (relabSeq v0 W) hM1_ne hR'_ne (hR'_kd.trans hM1_hd.1.symm)
    have hM1_l : linksT M1 = 1 := by simp [M1, relabSeq, linksT, hR2_k]
    have hR'_lk : linksT R' = 0 := buildReplRows_linksT R1.1 id7 repl
    have hU_M1_W : linksT (relabSeq v0 U ++ M1 ++ relabSeq v0 W) = s := by
      rw [← hEq1, relabSeq_linksT, hlinks]
    change linksT L' + linksT M1 = linksT (relabSeq v0 U ++ M1 ++ relabSeq v0 W) + linksT R' at hls
    rw [hU_M1_W, hM1_l, hR'_lk] at hls
    omega
  have hM1_holes : holesT 7 M1 = holesT 7 (buildOrigW4 0 l1 t4 l2) := by
    rw [hM1_eq]; simp [buildOrigW4, holesT]
  have hR'_holes : holesT 7 R' = holesT 7 (buildReplRows 0 id7 repl) := buildReplRows_kd0_holesT R1.1 id7 repl
  have hL'_holes : holesT 7 L' + holesT 7 M1 = holesT 7 L + holesT 7 R' := by
    have h1 := congrArg (holesT 7) hEq1
    rw [relabSeq_holesT, PS.holesT_append, PS.holesT_append] at h1
    simp only [L', PS.holesT_append]
    omega
  have hL'_len : L'.length + 2 = L.length + (buildReplRows 0 id7 repl).length := by
    have h1 := congrArg List.length hEq1
    rw [relabSeq_length, List.length_append, List.length_append] at h1
    have hM1_len : M1.length = 2 := rfl
    have hR'_len : R'.length = (buildReplRows 0 id7 repl).length := buildReplRows_kd0_length R1.1 id7 repl
    simp only [L', List.length_append, hM1_len, hR'_len] at h1 ⊢
    omega
  have hL'_cap := hlowW4 L' hL'_seq hL'_tag hL'_links (by omega)
  have hmono := hW4 (holesT 7 L) hlo hhi (holesT 7 L') (by omega)
  omega

end FastSound
end SuperpermLowerBounds
