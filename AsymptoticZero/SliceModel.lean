import AsymptoticZero.Eulerian
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Pure-`F/S` Selections, De Bruijn Slices, Transitions, and Permutation Coverage

Defines:
* Permutations (`IsPerm K p`) and canonical loops (`canonLoop p`) on `Fin K` (`(K - 1)!` loops).
* Step operators `FStep`, `SStep` on `List α`.
* `PureSelection K` (assignments of `'D'`, `'F'`, `'S'` rows to canonical loops, closed under `F`/`S`).
* Explicit slice word builder `buildSliceFull`, `insSlice`, `repSlice`, `rowSlices` on `Fin (K + 2)`.
* Exact total slice length `= F_3(K + 2) + Q`, exact `head`/`tail` transition formulas for `'D'`, `'F'`, `'S'` rows,
  and 100% `Almanac.IsSuperpermutation (K + 2)` coverage.
* Length-`h` connector cycles `connCycleEdges ck` in `B(K + 2, K - 1)`.
-/

namespace AsymptoticZero

open Almanac

/-! ### 1. Permutations, canonical loops, and `F`/`S` step operators -/

/-- `p` is a permutation of `Fin K` as a duplicate-free list of length `K`. -/
def IsPerm (K : Nat) (p : List (Fin K)) : Prop :=
  p.Nodup ∧ p.length = K

/-- Every element of `Fin K` appears in any `IsPerm K p`. -/
theorem mem_of_isPerm {K : Nat} {p : List (Fin K)} (hp : IsPerm K p) (a : Fin K) : a ∈ p := by
  have hcard : p.toFinset.card = Fintype.card (Fin K) := by
    rw [List.toFinset_card_of_nodup hp.1, hp.2, Fintype.card_fin]
  have huniv : p.toFinset = Finset.univ := Finset.eq_univ_of_card _ hcard
  have : a ∈ p.toFinset := by rw [huniv]; exact Finset.mem_univ a
  exact List.mem_toFinset.mp this

theorem isPerm_rotate {K : Nat} {p : List (Fin K)} (hp : IsPerm K p) (r : Nat) :
    IsPerm K (p.rotate r) :=
  ⟨List.nodup_rotate.mpr hp.1, by rw [List.length_rotate, hp.2]⟩

/-- Canonical loop representative: rotate `p` so `(0 : Fin K)` is at index `0`. -/
def canonLoop {K : Nat} [NeZero K] (p : List (Fin K)) : List (Fin K) :=
  p.rotate (p.idxOf 0)

/-- `L` is a canonical loop on `Fin K`: a permutation starting with `0`. -/
def IsCanonLoop (K : Nat) [NeZero K] (L : List (Fin K)) : Prop :=
  IsPerm K L ∧ L.head? = some 0

theorem canonLoop_isRotated {K : Nat} [NeZero K] (p : List (Fin K)) :
    p ~r canonLoop p :=
  ⟨p.idxOf 0, rfl⟩

theorem canonLoop_isCanonLoop {K : Nat} [NeZero K] {p : List (Fin K)} (hp : IsPerm K p) :
    IsCanonLoop K (canonLoop p) := by
  refine ⟨isPerm_rotate hp _, ?_⟩
  have h0 : (0 : Fin K) ∈ p := mem_of_isPerm hp 0
  have hidx : p.idxOf 0 < p.length := List.idxOf_lt_length_of_mem h0
  have hpos : 0 < (p.rotate (p.idxOf 0)).length := by
    rw [List.length_rotate, hp.2]; exact NeZero.pos K
  rw [canonLoop, List.head?_eq_getElem?, List.getElem?_eq_getElem hpos, List.getElem_rotate]
  have hmod : (0 + p.idxOf 0) % p.length = p.idxOf 0 := by
    rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hidx
  simp only [hmod, List.getElem_idxOf]

theorem isCanonLoop_eq_of_isRotated {K : Nat} [NeZero K] {L1 L2 : List (Fin K)}
    (h1 : IsCanonLoop K L1) (h2 : IsCanonLoop K L2) (hrot : L1 ~r L2) : L1 = L2 := by
  obtain ⟨r, rfl⟩ := hrot
  have hlen : 0 < L1.length := by rw [h1.1.2]; exact NeZero.pos K
  have hhd1 : L1[0]'hlen = 0 := by
    have := h1.2
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at this
    exact Option.some.inj this
  have hlenr : 0 < (L1.rotate r).length := by rw [List.length_rotate]; exact hlen
  have hhd2 : (L1.rotate r)[0]'hlenr = 0 := by
    have := h2.2
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlenr] at this
    exact Option.some.inj this
  rw [List.getElem_rotate] at hhd2
  have heq_idx : (0 + r) % L1.length = 0 :=
    (List.Nodup.getElem_inj_iff h1.1.1).mp (hhd2.trans hhd1.symm)
  have hdvd : L1.length ∣ r := Nat.dvd_of_mod_eq_zero (by simpa using heq_idx)
  obtain ⟨q, rfl⟩ := hdvd
  rw [← List.rotate_mod, Nat.mul_mod_right, List.rotate_zero]

theorem canonLoop_eq_iff {K : Nat} [NeZero K] {p q : List (Fin K)}
    (hp : IsPerm K p) (hq : IsPerm K q) :
    canonLoop p = canonLoop q ↔ p ~r q := by
  constructor
  · intro h
    exact (canonLoop_isRotated p).trans (h ▸ (canonLoop_isRotated q).symm)
  · intro h
    exact isCanonLoop_eq_of_isRotated (canonLoop_isCanonLoop hp) (canonLoop_isCanonLoop hq)
      ((canonLoop_isRotated p).symm.trans (h.trans (canonLoop_isRotated q)))

theorem canonLoop_self {K : Nat} [NeZero K] {L : List (Fin K)} (hL : IsCanonLoop K L) :
    canonLoop L = L :=
  isCanonLoop_eq_of_isRotated (canonLoop_isCanonLoop hL.1) hL (canonLoop_isRotated L).symm

/-- Number of canonical loops on `Fin K` (`K ≥ 1`) equals `(K - 1)!`. -/
def allCanonLoops (K : Nat) [NeZero K] : List (List (Fin K)) :=
  (List.finRange (K - 1)).permutations.map fun tail =>
    (0 : Fin K) :: tail.map fun x => ⟨x.1 + 1, by have := x.2; have := NeZero.pos K; omega⟩

theorem allCanonLoops_length (K : Nat) [NeZero K] :
    (allCanonLoops K).length = Almanac.fact (K - 1) := by
  have hfact : ∀ m : Nat, m.factorial = Almanac.fact m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => simp [Nat.factorial_succ, Almanac.fact, ih]
  simp [allCanonLoops, List.length_permutations, hfact]

theorem allCanonLoops_nodup (K : Nat) [NeZero K] : (allCanonLoops K).Nodup := by
  unfold allCanonLoops
  refine List.Nodup.map ?_ (List.nodup_permutations _ (List.nodup_finRange (K - 1)))
  intro a b hab
  simp only [List.cons.injEq, true_and] at hab
  refine List.map_injective_iff.mpr ?_ hab
  intro x y hxy
  ext
  have := congrArg Fin.val hxy
  dsimp at this
  omega

theorem mem_allCanonLoops_iff {K : Nat} [NeZero K] (L : List (Fin K)) :
    L ∈ allCanonLoops K ↔ IsCanonLoop K L := by
  constructor
  · intro h
    unfold allCanonLoops at h
    rw [List.mem_map] at h
    obtain ⟨tail, htail_mem, rfl⟩ := h
    rw [List.mem_permutations] at htail_mem
    have hnd_tail : tail.Nodup := htail_mem.nodup_iff.mpr (List.nodup_finRange (K - 1))
    have hlen_tail : tail.length = K - 1 := by
      rw [htail_mem.length_eq, List.length_finRange]
    have hinj : Function.Injective (fun x : Fin (K - 1) =>
        (⟨x.1 + 1, by have := x.2; have := NeZero.pos K; omega⟩ : Fin K)) := by
      intro x y hxy; ext; have := congrArg Fin.val hxy; dsimp at this; omega
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · refine List.nodup_cons.mpr ⟨?_, hnd_tail.map hinj⟩
      intro h0
      rw [List.mem_map] at h0
      obtain ⟨x, _, hx⟩ := h0
      have := congrArg Fin.val hx
      dsimp at this; omega
    · simp [hlen_tail]; have := NeZero.pos K; omega
  · rintro ⟨⟨hnd, hlen⟩, hhd⟩
    cases L with
    | nil => simp at hhd
    | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      have h0_notin : (0 : Fin K) ∉ rest := (List.nodup_cons.mp hnd).1
      have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hlen_rest : rest.length = K - 1 := by simp at hlen; omega
      have hpos_mem : ∀ x ∈ rest, 0 < x.1 := by
        intro x hx
        by_contra hle
        have hx0 : x = 0 := Fin.ext (by change x.1 = 0; omega)
        exact h0_notin (hx0 ▸ hx)
      let tail : List (Fin (K - 1)) := rest.pmap
        (fun x (hx : 0 < x.1) => ⟨x.1 - 1, by have := x.2; omega⟩) hpos_mem
      have hmap : tail.map (fun x : Fin (K - 1) =>
          (⟨x.1 + 1, by have := x.2; have := NeZero.pos K; omega⟩ : Fin K)) = rest := by
        dsimp [tail]
        have haux : ∀ (l : List (Fin K)) (hl : ∀ x ∈ l, 0 < x.1),
            (l.pmap (fun x (hx : 0 < x.1) => (⟨x.1 - 1, by have := x.2; omega⟩ : Fin (K - 1))) hl).map
              (fun x : Fin (K - 1) => (⟨x.1 + 1, by have := x.2; have := NeZero.pos K; omega⟩ : Fin K)) = l := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons b bs ih =>
            intro hl
            simp only [List.pmap, List.map_cons]
            congr 1
            · apply Fin.ext; dsimp; have := hl b List.mem_cons_self; omega
            · exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        exact haux rest hpos_mem
      have hnd_tail : tail.Nodup := by
        have := hnd_rest
        rw [← hmap] at this
        exact List.Nodup.of_map _ this
      have hlen_tail : tail.length = K - 1 := by
        have := hlen_rest; rw [← hmap, List.length_map] at this; exact this
      have hperm_tail : tail.Perm (List.finRange (K - 1)) := by
        refine (List.perm_ext_iff_of_nodup hnd_tail (List.nodup_finRange (K - 1))).mpr ?_
        intro y
        constructor
        · intro _; exact List.mem_finRange y
        · intro _
          have hy_card : tail.toFinset.card = Fintype.card (Fin (K - 1)) := by
            rw [List.toFinset_card_of_nodup hnd_tail, hlen_tail, Fintype.card_fin]
          have huniv := Finset.eq_univ_of_card _ hy_card
          exact List.mem_toFinset.mp (huniv ▸ Finset.mem_univ y)
      unfold allCanonLoops
      rw [List.mem_map]
      exact ⟨tail, List.mem_permutations.mpr hperm_tail, by rw [hmap]⟩

/-- The `F`-step operator on any list of length `K`:
`(p_0, ..., p_{K-1}) ↦ (p_1, ..., p_{K-2}, p_0, p_{K-1})`. -/
def FStep {α : Type} (p : List α) : List α :=
  (p.take (p.length - 1)).rotate 1 ++ p.drop (p.length - 1)

/-- The `S`-step operator on any list of length `K`:
`(p_0, ..., p_{K-1}) ↦ (p_{K-1}, p_0, ..., p_{K-4}, p_{K-2}, p_{K-3})`. -/
def SStep {α : Type} (p : List α) : List α :=
  p.drop (p.length - 1) ++ p.take (p.length - 3) ++ ((p.drop (p.length - 3)).take 2).reverse

theorem FStep_perm {α : Type} (p : List α) : (FStep p).Perm p := by
  unfold FStep
  refine (List.Perm.append_right _ (List.rotate_perm _ _)).trans ?_
  rw [List.take_append_drop]

theorem SStep_perm {α : Type} (p : List α) (h3 : 3 ≤ p.length) : (SStep p).Perm p := by
  unfold SStep
  let A := p.take (p.length - 3)
  let B := (p.drop (p.length - 3)).take 2
  let C := p.drop (p.length - 1)
  have hsplit : p = A ++ (B ++ C) := by
    have h1 : p = A ++ p.drop (p.length - 3) := (List.take_append_drop (p.length - 3) p).symm
    have h2 : p.drop (p.length - 3) = B ++ C := by
      have := (List.take_append_drop 2 (p.drop (p.length - 3))).symm
      rw [List.drop_drop] at this
      have hidx : p.length - 3 + 2 = p.length - 1 := by omega
      rwa [hidx] at this
    rw [h1, h2]
  change (C ++ A ++ B.reverse).Perm p
  rw [hsplit]
  have hp1 : (C ++ A ++ B.reverse).Perm (C ++ A ++ B) := List.Perm.append_left _ (List.reverse_perm B)
  have hp2 : (C ++ A ++ B).Perm ((A ++ B) ++ C) := by
    rw [List.append_assoc]; exact List.perm_append_comm
  exact (hp1.trans hp2).trans (by rw [List.append_assoc])

theorem FStep_isPerm {K : Nat} {p : List (Fin K)} (hp : IsPerm K p) : IsPerm K (FStep p) :=
  ⟨(FStep_perm p).nodup_iff.mpr hp.1, (FStep_perm p).length_eq.trans hp.2⟩

theorem SStep_isPerm {K : Nat} (hK : 3 ≤ K) {p : List (Fin K)} (hp : IsPerm K p) :
    IsPerm K (SStep p) :=
  ⟨(SStep_perm p (by rw [hp.2]; omega)).nodup_iff.mpr hp.1,
    (SStep_perm p (by rw [hp.2]; omega)).length_eq.trans hp.2⟩

theorem FStep_map {α β : Type} (f : α → β) (p : List α) : FStep (p.map f) = (FStep p).map f := by
  simp [FStep, List.map_append, List.map_rotate, List.map_take, List.map_drop]

theorem SStep_map {α β : Type} (f : α → β) (p : List α) : SStep (p.map f) = (SStep p).map f := by
  simp [SStep, List.map_append, List.map_reverse, List.map_take, List.map_drop]

/-! ### 2. Pure-`F/S` selection -/

inductive RowType where
  | D | F | S
  deriving DecidableEq

/-- A valid pure-`F/S` selection on `Fin K` (`K ≥ 4`). -/
structure PureSelection (K : Nat) [NeZero K] where
  row : List (Fin K) → List (Fin K) × RowType
  row_perm : ∀ L, IsCanonLoop K L → IsPerm K (row L).1 ∧ (row L).1 ~r L
  closed_F : ∀ L, IsCanonLoop K L → (row L).2 = .F →
    let x' := FStep (row L).1
    (row (canonLoop x')).1 = x' ∧ (row (canonLoop x')).2 ≠ .D
  closed_S : ∀ L, IsCanonLoop K L → (row L).2 = .S →
    let x' := SStep (row L).1
    (row (canonLoop x')).1 = x' ∧ (row (canonLoop x')).2 ≠ .D

/-! ### 3. Slice words, exact lengths, `head`/`tail` transitions, and `IsSuperpermutation` coverage -/

/-- Build the full word of a slice with `vv ≥ 1` consecutive `1`-cycles on base word `y` and separator `sep`. -/
def buildSliceFull {n : Nat} (y : Word n) (sep : Fin n) : Nat → Word n
  | 0 => []
  | 1 => y ++ [sep] ++ y
  | c + 2 => buildSliceFull y sep (c + 1) ++ [y.getD c sep, sep] ++ y.rotate (c + 1)

theorem buildSliceFull_length {n : Nat} (y : Word n) (sep : Fin n) :
    ∀ vv : Nat, 1 ≤ vv → (buildSliceFull y sep vv).length = (y.length + 2) * vv + y.length - 1
  | 0, h => by omega
  | 1, _ => by
    simp only [buildSliceFull, List.length_append, List.length_singleton]
    omega
  | c + 2, _ => by
    have ih := buildSliceFull_length y sep (c + 1) (by omega)
    simp only [buildSliceFull, List.length_append, List.length_cons, List.length_nil,
      List.length_rotate]
    rw [ih]
    have hmul : (y.length + 2) * (c + 2) = (y.length + 2) * (c + 1) + (y.length + 2) := by ring
    have hge : 1 ≤ (y.length + 2) * (c + 1) := Nat.mul_pos (by omega) (by omega)
    omega

theorem buildSliceFull_prefix {n : Nat} (y : Word n) (sep : Fin n) :
    ∀ vv : Nat, 1 ≤ vv → y <+: buildSliceFull y sep vv
  | 0, h => by omega
  | 1, _ => ⟨[sep] ++ y, by simp [buildSliceFull, List.append_assoc]⟩
  | c + 2, _ => by
    simp only [buildSliceFull, List.append_assoc]
    exact (buildSliceFull_prefix y sep (c + 1) (by omega)).trans (List.prefix_append _ _)

theorem buildSliceFull_suffix {n : Nat} (y : Word n) (sep : Fin n) :
    ∀ vv : Nat, 1 ≤ vv → y.rotate (vv - 1) <:+ buildSliceFull y sep vv
  | 0, h => by omega
  | 1, _ => ⟨y ++ [sep], by simp [buildSliceFull]⟩
  | c + 2, _ => ⟨buildSliceFull y sep (c + 1) ++ [y.getD c sep, sep], by simp [buildSliceFull]⟩

theorem rotate_succ_eq_tail_append_head {α : Type} (l : List α) {c : Nat} (d : α) (hc : c < l.length) :
    [l.getD c d] ++ l.rotate (c + 1) = l.rotate c ++ [l.getD c d] := by
  have hl : 0 < l.length := by omega
  have hmod : c % l.length = c := Nat.mod_eq_of_lt hc
  have hgd : l.getD c d = l[c]'hc := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
  have h1 : l.rotate c = l[c]'hc :: (l.rotate c).tail := by
    cases hr : l.rotate c with
    | nil =>
      have hnil := congrArg List.length hr
      rw [List.length_rotate, List.length_nil] at hnil; omega
    | cons a as =>
      have ha : a = l[c]'hc := by
        have hpos : 0 < (l.rotate c).length := by rw [List.length_rotate]; exact hl
        have := List.getElem_rotate l c 0 hpos
        simp only [Nat.zero_add, hmod] at this
        have h0 : (l.rotate c)[0]'hpos = a := by simp [hr]
        rw [h0] at this; exact this
      simp [ha]
  have h2 : l.rotate (c + 1) = (l.rotate c).tail ++ [l[c]'hc] := by
    rw [← List.rotate_rotate, h1, List.rotate_cons_succ]; simp
  rw [hgd, h2]
  conv_rhs => rw [h1]
  simp

/-- Every `1`-cycle `y.rotate c ++ [sep] ++ y.rotate c` (`c < vv ≤ y.length`) appears as an infix of `buildSliceFull y sep vv`. -/
theorem buildSliceFull_contains_cycle {n : Nat} (y : Word n) (sep : Fin n) :
    ∀ (vv : Nat), vv ≤ y.length → ∀ c < vv,
      y.rotate c ++ [sep] ++ y.rotate c <:+: buildSliceFull y sep vv
  | 0, _, _, hc => by omega
  | 1, _, c, hc => by
    have hc0 : c = 0 := by omega
    subst hc0
    exact ⟨[], [], by simp [buildSliceFull]⟩
  | k + 2, hle, c, hc => by
    by_cases hlast : c = k + 1
    · subst hlast
      obtain ⟨pre, hpre⟩ := buildSliceFull_suffix y sep (k + 1) (by omega)
      have hk_lt : k < y.length := by omega
      have hrot := rotate_succ_eq_tail_append_head y sep hk_lt
      refine ⟨pre ++ [y.getD k sep], [], ?_⟩
      simp only [buildSliceFull, List.append_nil]
      rw [← hpre]
      have h1 : pre ++ [y.getD k sep] ++ (y.rotate (k + 1) ++ [sep] ++ y.rotate (k + 1)) =
          pre ++ ([y.getD k sep] ++ y.rotate (k + 1)) ++ [sep] ++ y.rotate (k + 1) := by
        simp [List.append_assoc]
      rw [h1, hrot]
      simp [List.append_assoc]
    · have hc' : c < k + 1 := by omega
      obtain ⟨p, q, hpq⟩ := buildSliceFull_contains_cycle y sep (k + 1) (by omega) c hc'
      exact ⟨p, q ++ [y.getD k sep, sep] ++ y.rotate (k + 1), by
        simp only [buildSliceFull]
        rw [← hpq]; simp [List.append_assoc]⟩

/-- Any cyclic rotation of `w ++ [sep]` appears as a contiguous infix of `w ++ [sep] ++ w`! -/
theorem rotate_mem_infix_double {α : Type} (w : List α) (sep : α) (r : Nat) :
    (w ++ [sep]).rotate r <:+: w ++ [sep] ++ w := by
  have hlen : (w ++ [sep]).length = w.length + 1 := by simp
  have hmod : (w ++ [sep]).rotate r = (w ++ [sep]).rotate (r % (w.length + 1)) := by
    rw [← hlen, List.rotate_mod]
  rw [hmod]
  let r' := r % (w.length + 1)
  have hr' : r' ≤ w.length := by
    have : r % (w.length + 1) < w.length + 1 := Nat.mod_lt r (by omega)
    omega
  have hrot : (w ++ [sep]).rotate r' = (w ++ [sep]).drop r' ++ (w ++ [sep]).take r' :=
    List.rotate_eq_drop_append_take (by rw [hlen]; omega)
  have hdrop : (w ++ [sep]).drop r' = w.drop r' ++ [sep] := by
    rw [List.drop_append_of_le_length hr']
  have htake : (w ++ [sep]).take r' = w.take r' := by
    rw [List.take_append_of_le_length hr']
  rw [hrot, hdrop, htake]
  refine ⟨w.take r', w.drop r', ?_⟩
  have h1 : w = w.take r' ++ w.drop r' := (List.take_append_drop r' w).symm
  conv_rhs => rw [h1]
  simp only [List.append_assoc]

/-- Turn `buildSliceFull y sep vv` into a well-formed `RawEdge (K + 2)` of overlap width `h = K - 1`. -/
def sliceEdge (K : Nat) (y : Word (K + 2)) (sep : Fin (K + 2)) (vv : Nat) : RawEdge (K + 2) :=
  let full := buildSliceFull y sep vv
  ⟨full.take (K - 1), full.drop (full.length - (K - 1)), full.drop (K - 1)⟩

theorem sliceEdge_full {K : Nat} (y : Word (K + 2)) (sep : Fin (K + 2)) (vv : Nat) :
    (sliceEdge K y sep vv).u ++ (sliceEdge K y sep vv).body = buildSliceFull y sep vv := by
  simp [sliceEdge, List.take_append_drop]

theorem sliceEdge_ok {K : Nat} (hK : 4 ≤ K) {y : Word (K + 2)} (hy : y.length = K + 1)
    (sep : Fin (K + 2)) {vv : Nat} (hvv : 1 ≤ vv) :
    EdgeOk (K - 1) (sliceEdge K y sep vv) ∧
    (sliceEdge K y sep vv).body.length = (K + 3) * vv + 1 := by
  have hflen : (buildSliceFull y sep vv).length = (K + 3) * vv + K := by
    rw [buildSliceFull_length y sep vv hvv, hy]
    have h1 : K + 1 + 2 = K + 3 := by omega
    rw [h1]; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [sliceEdge, List.length_take, hflen]; omega
  · simp only [sliceEdge, List.length_drop, hflen]; omega
  · rw [sliceEdge_full]
    exact List.drop_suffix _ _
  · simp only [sliceEdge, List.length_drop, hflen]; omega

theorem sliceEdge_u {K : Nat} (hK : 4 ≤ K) {y : Word (K + 2)} (hy : y.length = K + 1)
    (sep : Fin (K + 2)) {vv : Nat} (hvv : 1 ≤ vv) :
    (sliceEdge K y sep vv).u = y.take (K - 1) := by
  obtain ⟨post, hpost⟩ := buildSliceFull_prefix y sep vv hvv
  simp only [sliceEdge, ← hpost]
  rw [List.take_append_of_le_length (by omega)]

theorem sliceEdge_v {K : Nat} (hK : 4 ≤ K) {y : Word (K + 2)} (hy : y.length = K + 1)
    (sep : Fin (K + 2)) {vv : Nat} (hvv : 1 ≤ vv) :
    (sliceEdge K y sep vv).v = (y.rotate (vv - 1)).drop 2 := by
  obtain ⟨pre, hpre⟩ := buildSliceFull_suffix y sep vv hvv
  simp only [sliceEdge]
  have hflen : (buildSliceFull y sep vv).length = pre.length + (K + 1) := by
    have := congrArg List.length hpre
    rw [List.length_append, List.length_rotate, hy] at this
    exact this.symm
  rw [hflen]
  have hsub : pre.length + (K + 1) - (K - 1) = pre.length + 2 := by omega
  rw [hsub, ← hpre, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
  have h2 : pre.length + 2 - pre.length = 2 := by omega
  rw [h2]

theorem rotate_drop2_eq_take {α : Type} {y : List α} {m : Nat} (hy : y.length = m + 2) (r : Nat) :
    (y.rotate r).drop 2 = (y.rotate (r + 2)).take m := by
  have hlen : (y.rotate r).length = m + 2 := by rw [List.length_rotate, hy]
  have hrot : y.rotate (r + 2) = (y.rotate r).rotate 2 := (List.rotate_rotate y r 2).symm
  rw [hrot]
  have hrot2 : (y.rotate r).rotate 2 = (y.rotate r).drop 2 ++ (y.rotate r).take 2 :=
    List.rotate_eq_drop_append_take (by omega)
  rw [hrot2]
  have hdl : ((y.rotate r).drop 2).length = m := by rw [List.length_drop, hlen]; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem sliceEdge_v_take {K : Nat} (hK : 4 ≤ K) {y : Word (K + 2)} (hy : y.length = K + 1)
    (sep : Fin (K + 2)) {vv : Nat} (hvv : 1 ≤ vv) :
    (sliceEdge K y sep vv).v = (y.rotate (vv + 1)).take (K - 1) := by
  rw [sliceEdge_v hK hy sep hvv, rotate_drop2_eq_take (m := K - 1) (by omega)]
  congr 2; omega

/-! ### 4. Embedding `Fin K ↪ Fin (K + 2)`, row slices, length identity, and coverage -/

def embK {K : Nat} (i : Fin K) : Fin (K + 2) := ⟨i.1, by omega⟩
def symS (K : Nat) : Fin (K + 2) := ⟨K, by omega⟩
def symZ (K : Nat) : Fin (K + 2) := ⟨K + 1, by omega⟩

theorem embK_injective (K : Nat) : Function.Injective (@embK K) := by
  intro a b h
  have hv : (embK a).1 = (embK b).1 := congrArg Fin.val h
  exact Fin.ext hv

theorem embK_ne_symS {K : Nat} (i : Fin K) : embK i ≠ symS K := by
  intro h; have := congrArg Fin.val h; dsimp [embK, symS] at this; omega

theorem embK_ne_symZ {K : Nat} (i : Fin K) : embK i ≠ symZ K := by
  intro h; have := congrArg Fin.val h; dsimp [embK, symZ] at this; omega

theorem symS_ne_symZ (K : Nat) : symS K ≠ symZ K := by
  intro h; have := congrArg Fin.val h; dsimp [symS, symZ] at this; omega

/-- Base `(K + 1)`-word for inserted slice `(x, j)`: insert `Z` at position `j` in `x`. -/
def insBase {K : Nat} (x : List (Fin K)) (j : Nat) : Word (K + 2) :=
  (x.take j).map embK ++ [symZ K] ++ (x.drop j).map embK

theorem insBase_length {K : Nat} {x : List (Fin K)} (hx : x.length = K) (j : Nat) :
    (insBase x j).length = K + 1 := by
  unfold insBase
  simp only [List.length_append, List.length_map, List.length_singleton, List.length_take,
    List.length_drop, hx]
  omega

/-- Inserted slice edge `(x, v, j)` with `vv = v + (if j < v then 1 else 0)`. -/
def insSlice {K : Nat} (x : List (Fin K)) (v j : Nat) : RawEdge (K + 2) :=
  sliceEdge K (insBase x j) (symS K) (v + if j < v then 1 else 0)

/-- Base `(K + 1)`-word for repair slice `(x, j)`: `x.rotate j ++ [S]`. -/
def repBase {K : Nat} (x : List (Fin K)) (j : Nat) : Word (K + 2) :=
  (x.rotate j).map embK ++ [symS K]

theorem repBase_length {K : Nat} {x : List (Fin K)} (hx : x.length = K) (j : Nat) :
    (repBase x j).length = K + 1 := by
  unfold repBase; simp [hx]

/-- Repair slice edge `(x, j)` with `vv = K + 1`. -/
def repSlice {K : Nat} (x : List (Fin K)) (j : Nat) : RawEdge (K + 2) :=
  sliceEdge K (repBase x j) (symZ K) (K + 1)

/-- All slices produced by row `(x, rt)`. -/
def rowSlices {K : Nat} (x : List (Fin K)) : RowType → List (RawEdge (K + 2))
  | .D => (List.range K).map (repSlice x)
  | .F => (List.range K).map (insSlice x K)
  | .S => (List.range K).map (insSlice x (K - 2)) ++ [repSlice x (K - 2), repSlice x (K - 1)]

theorem rowSlices_ok {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) (rt : RowType) :
    ∀ e ∈ rowSlices x rt, EdgeOk (K - 1) e := by
  intro e he
  cases rt with
  | D =>
    simp only [rowSlices, List.mem_map, List.mem_range] at he
    obtain ⟨j, _, rfl⟩ := he
    exact (sliceEdge_ok hK (repBase_length hx j) (symZ K) (by omega)).1
  | F =>
    simp only [rowSlices, List.mem_map, List.mem_range] at he
    obtain ⟨j, _, rfl⟩ := he
    exact (sliceEdge_ok hK (insBase_length hx j) (symS K) (by omega)).1
  | S =>
    simp only [rowSlices, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with ⟨j, _, rfl⟩ | rfl | rfl
    · exact (sliceEdge_ok hK (insBase_length hx j) (symS K) (by omega)).1
    · exact (sliceEdge_ok hK (repBase_length hx _) (symZ K) (by omega)).1
    · exact (sliceEdge_ok hK (repBase_length hx _) (symZ K) (by omega)).1

/-- Exact net body length of a single row `(x, rt)`: `(K + 2)^2 * K + (if rt = .S then 2 else 0)`. -/
theorem rowSlices_body_sum {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) (rt : RowType) :
    ((rowSlices x rt).map (fun e => e.body.length)).sum =
      (K + 2) * (K + 2) * K + (if rt = .S then 2 else 0) := by
  have hrep : ∀ j, (repSlice x j).body.length = (K + 3) * (K + 1) + 1 := fun j =>
    (sliceEdge_ok hK (repBase_length hx j) (symZ K) (by omega)).2
  have hins : ∀ v j, 1 ≤ v → (insSlice x v j).body.length =
      (K + 3) * (v + if j < v then 1 else 0) + 1 := fun v j hv =>
    (sliceEdge_ok hK (insBase_length hx j) (symS K) (by omega)).2
  cases rt with
  | D =>
    simp only [rowSlices, List.map_map, Function.comp_def, hrep, List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul, reduceCtorEq, ↓reduceIte, Nat.add_zero]
    ring
  | F =>
    have hF : ∀ j ∈ List.range K, (insSlice x K j).body.length = (K + 3) * (K + 1) + 1 := by
      intro j hj
      rw [List.mem_range] at hj
      rw [hins K j (by omega), if_pos hj]
    simp only [rowSlices, List.map_map, Function.comp_def, reduceCtorEq, ↓reduceIte, Nat.add_zero]
    rw [List.map_congr_left hF, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  | S =>
    have hsplit : List.range K = List.range (K - 2) ++ [K - 2, K - 1] := by
      have h1 : K = (K - 2) + 1 + 1 := by omega
      conv_lhs => rw [h1]
      rw [List.range_succ, List.range_succ]
      have h2 : K - 2 + 1 = K - 1 := by omega
      simp [h2, List.append_assoc]
    have h1 : ∀ j ∈ List.range (K - 2), (insSlice x (K - 2) j).body.length = (K + 3) * (K - 1) + 1 := by
      intro j hj
      rw [List.mem_range] at hj
      rw [hins (K - 2) j (by omega), if_pos hj]
      have : K - 2 + 1 = K - 1 := by omega
      rw [this]
    have h2 : (insSlice x (K - 2) (K - 2)).body.length = (K + 3) * (K - 2) + 1 := by
      rw [hins (K - 2) (K - 2) (by omega), if_neg (Nat.lt_irrefl _)]; simp
    have h3 : (insSlice x (K - 2) (K - 1)).body.length = (K + 3) * (K - 2) + 1 := by
      rw [hins (K - 2) (K - 1) (by omega), if_neg (by omega)]; simp
    simp only [rowSlices, hsplit, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      ↓reduceIte, h2, h3, hrep]
    rw [List.map_congr_left h1, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    zify [hK]
    have hK1 : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by omega
    have hK2 : ((K - 2 : Nat) : Int) = (K : Int) - 2 := by omega
    rw [hK1, hK2]; ring

/-- Key algebraic identity: `(K - 1)! * (K + 2)^2 * K = F_3(K + 2)`. -/
theorem F3_eq_mul_fact (K : Nat) (hK : 2 ≤ K) :
    Almanac.fact (K + 2) + Almanac.fact (K + 1) + Almanac.fact K =
      Almanac.fact (K - 1) * ((K + 2) * (K + 2) * K) := by
  have h1 : Almanac.fact K = K * Almanac.fact (K - 1) := by
    cases K with
    | zero => omega
    | succ m => rfl
  have h2 : Almanac.fact (K + 1) = (K + 1) * Almanac.fact K := rfl
  have h3 : Almanac.fact (K + 2) = (K + 2) * Almanac.fact (K + 1) := rfl
  rw [h3, h2, h1]; ring

/-! ### 5. Exact permutation coverage of `rowSlices` -/

/-- Helper: rotating `insBase x j` by `c` when `c ≤ j < K` yields `insBase (x.rotate c) (j - c)`. -/
theorem insBase_rotate_le {K : Nat} {x : List (Fin K)} (hx : x.length = K) {j c : Nat}
    (hcj : c ≤ j) (hj : j < K) :
    (insBase x j).rotate c = insBase (x.rotate c) (j - c) := by
  unfold insBase
  have hlen_t : ((x.take j).map embK).length = j := by simp [hx]; omega
  rw [List.rotate_eq_drop_append_take (by simp [hx]; omega)]
  rw [List.append_assoc, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by omega), ← List.map_take, ← List.map_drop,
    List.take_take, Nat.min_eq_left hcj]
  have hrot : x.rotate c = x.drop c ++ x.take c := List.rotate_eq_drop_append_take (by omega)
  have hlen_dc : (x.drop c).length = K - c := by simp [hx]
  have htake_rot : (x.rotate c).take (j - c) = (x.take j).drop c := by
    rw [hrot, List.take_append_of_le_length (by omega), List.take_drop]
    have : c + (j - c) = j := by omega
    rw [this]
  have hdrop_rot : (x.rotate c).drop (j - c) = x.drop j ++ x.take c := by
    rw [hrot, List.drop_append_of_le_length (by omega), List.drop_drop]
    have : c + (j - c) = j := by omega
    rw [this]
  rw [htake_rot, hdrop_rot, List.map_append]
  simp [List.append_assoc]

/-- Helper: rotating `insBase x j` by `r + 1` when `j ≤ r < K` yields `insBase (x.rotate r) (K - r + j)`. -/
theorem insBase_rotate_gt {K : Nat} {x : List (Fin K)} (hx : x.length = K) {j r : Nat}
    (hjr : j ≤ r) (hr : r < K) :
    (insBase x j).rotate (r + 1) = insBase (x.rotate r) (K - r + j) := by
  unfold insBase
  have hlen1 : ((x.take j).map embK ++ [symZ K]).length = j + 1 := by simp [hx]; omega
  have hdrop : (((x.take j).map embK ++ [symZ K]) ++ (x.drop j).map embK).drop (r + 1) =
      (x.drop r).map embK := by
    rw [List.drop_append, hlen1]
    have hsub2 : r + 1 - (j + 1) = r - j := by omega
    rw [List.drop_eq_nil_of_le (by omega), List.nil_append, hsub2, ← List.map_drop, List.drop_drop]
    have : j + (r - j) = r := by omega
    rw [this]
  have htake : (((x.take j).map embK ++ [symZ K]) ++ (x.drop j).map embK).take (r + 1) =
      (x.take j).map embK ++ [symZ K] ++ ((x.drop j).take (r - j)).map embK := by
    rw [List.take_append, hlen1, List.take_of_length_le (by omega)]
    have hsub2 : r + 1 - (j + 1) = r - j := by omega
    rw [hsub2, ← List.map_take]
  have hLHS : (((x.take j).map embK ++ [symZ K]) ++ (x.drop j).map embK).rotate (r + 1) =
      (x.drop r).map embK ++ (x.take j).map embK ++ [symZ K] ++ ((x.drop j).take (r - j)).map embK := by
    rw [List.rotate_eq_drop_append_take (by simp [hx]; omega), hdrop, htake]
    simp [List.append_assoc]
  have hrot : x.rotate r = x.drop r ++ x.take r := List.rotate_eq_drop_append_take (by omega)
  have hlen_dr : (x.drop r).length = K - r := by simp [hx]
  have htake_rot : (x.rotate r).take (K - r + j) = x.drop r ++ x.take j := by
    rw [hrot, List.take_append, hlen_dr, List.take_of_length_le (by omega)]
    have hsub : K - r + j - (K - r) = j := by omega
    rw [hsub, List.take_take, Nat.min_eq_left hjr]
  have hdrop_rot : (x.rotate r).drop (K - r + j) = (x.drop j).take (r - j) := by
    rw [hrot, List.drop_append, hlen_dr, List.drop_eq_nil_of_le (by omega), List.nil_append]
    have hsub : K - r + j - (K - r) = j := by omega
    rw [hsub, List.drop_take]
  rw [hLHS, htake_rot, hdrop_rot, List.map_append]

/-- Helper: rotating `repBase x r ++ [symZ K]` by `K + 1 - pos` (`0 ≤ pos ≤ K`) gives `insBase (x.rotate r) pos ++ [symS K]`! -/
theorem repBase_covers_insBase {K : Nat} {x : List (Fin K)} (hx : x.length = K) {r pos : Nat}
    (hpos : pos ≤ K) :
    (insBase (x.rotate r) pos ++ [symS K]) ~r (repBase x r).rotate pos ++ [symZ K] := by
  -- Both are cyclic rotations of `((x.rotate r).take pos).map embK ++ [symZ K] ++ ((x.rotate r).drop pos).map embK ++ [symS K]`!
  let A := ((x.rotate r).take pos).map embK
  let B := ((x.rotate r).drop pos).map embK
  have hxr : (x.rotate r).map embK = A ++ B := by
    dsimp [A, B]; rw [← List.map_append, List.take_append_drop]
  have hA : A.length = pos := by dsimp [A]; simp [hx]; omega
  have h1 : insBase (x.rotate r) pos ++ [symS K] = A ++ ([symZ K] ++ B ++ [symS K]) := by
    simp [insBase, A, B, List.append_assoc]
  have h2 : (repBase x r).rotate pos = B ++ [symS K] ++ A := by
    unfold repBase
    rw [hxr, List.append_assoc, List.rotate_eq_drop_append_take (by simp [A, B, hx]; omega)]
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
      List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]
    simp [List.append_assoc]
  rw [h1, h2]
  refine ⟨A.length + 1, ?_⟩
  have hlen : (A ++ [symZ K]).length = A.length + 1 := by simp
  have hL : A ++ ([symZ K] ++ B ++ [symS K]) = (A ++ [symZ K]) ++ (B ++ [symS K]) := by
    simp [List.append_assoc]
  rw [hL, ← hlen, List.rotate_append_length_eq]
  simp [List.append_assoc]

/-- **Row Coverage Lemma:** For any permutation `x` of `Fin K`, any `rt : RowType`,
any `r < K` and `pos ≤ K`, every cyclic rotation of `insBase (x.rotate r) pos ++ [symS K]`
appears as an infix of `e.u ++ e.body` for some slice `e ∈ rowSlices x rt`! -/
theorem rowSlices_covers_rot {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K)
    (rt : RowType) {r pos : Nat} (hr : r < K) (hpos : pos ≤ K) (q : Word (K + 2))
    (hq : q ~r insBase (x.rotate r) pos ++ [symS K]) :
    ∃ e ∈ rowSlices x rt, q <:+: e.u ++ e.body := by
  let v : Nat := match rt with | .D => 0 | .F => K | .S => K - 2
  by_cases hrv : r < v
  · -- Covered by an inserted slice `(x, v, j)`!
    have hrt_neD : rt ≠ .D := by intro h; subst h; simp [v] at hrv
    have hv_pos : 1 ≤ v := by cases rt <;> simp [v] at hrv ⊢ <;> omega
    by_cases hsplit : pos + r < K
    · -- Use `j = pos + r`, `c = r` (so `c ≤ j < K`)
      let j := pos + r
      have hj : j < K := hsplit
      have he_mem : insSlice x v j ∈ rowSlices x rt := by
        cases rt with
        | D => exact absurd rfl hrt_neD
        | F => exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
        | S => exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      refine ⟨insSlice x v j, he_mem, ?_⟩
      rw [insSlice, sliceEdge_full]
      have hvv_le : v + (if j < v then 1 else 0) ≤ (insBase x j).length := by
        rw [insBase_length hx j]; cases rt <;> simp [v] <;> split_ifs <;> omega
      have hcyc := buildSliceFull_contains_cycle (insBase x j) (symS K)
        (v + if j < v then 1 else 0) hvv_le r (by omega)
      rw [insBase_rotate_le hx (by omega) hj] at hcyc
      have hsub : j - r = pos := by omega
      rw [hsub] at hcyc
      obtain ⟨s, hs⟩ := hq.symm
      rw [← hs]
      exact (rotate_mem_infix_double _ _ s).trans hcyc
    · -- Use `j = pos + r - K`, `c = r + 1` (so `j ≤ r < v`, hence `c = r + 1 < v + 1 = vv`!)
      let j := pos + r - K
      have hjr : j ≤ r := by omega
      have hjv : j < v := by omega
      have hjK : j < K := by omega
      have he_mem : insSlice x v j ∈ rowSlices x rt := by
        cases rt with
        | D => exact absurd rfl hrt_neD
        | F => exact List.mem_map.mpr ⟨j, List.mem_range.mpr hjK, rfl⟩
        | S => exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hjK, rfl⟩)
      refine ⟨insSlice x v j, he_mem, ?_⟩
      rw [insSlice, sliceEdge_full]
      have hvv_le : v + (if j < v then 1 else 0) ≤ (insBase x j).length := by
        rw [insBase_length hx j]; cases rt <;> simp [v] <;> split_ifs <;> omega
      have hr1_lt : r + 1 < v + (if j < v then 1 else 0) := by rw [if_pos hjv]; omega
      have hcyc := buildSliceFull_contains_cycle (insBase x j) (symS K)
        (v + if j < v then 1 else 0) hvv_le (r + 1) hr1_lt
      rw [insBase_rotate_gt hx hjr hr] at hcyc
      have hpos_eq : K - r + j = pos := by omega
      rw [hpos_eq] at hcyc
      obtain ⟨s, hs⟩ := hq.symm
      rw [← hs]
      exact (rotate_mem_infix_double _ _ s).trans hcyc
  · -- Covered by repair slice `repSlice x r` (`v ≤ r < K`)!
    have he_mem : repSlice x r ∈ rowSlices x rt := by
      cases rt with
      | D => exact List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
      | F => simp [v] at hrv; omega
      | S =>
        simp only [v] at hrv
        have hcases : r = K - 2 ∨ r = K - 1 := by omega
        rcases hcases with rfl | rfl <;> simp [rowSlices]
    refine ⟨repSlice x r, he_mem, ?_⟩
    rw [repSlice, sliceEdge_full]
    have hcyc := buildSliceFull_contains_cycle (repBase x r) (symZ K) (K + 1)
      (by rw [repBase_length hx r]) pos (by omega)
    have hrot_eq : q ~r (repBase x r).rotate pos ++ [symZ K] :=
      hq.trans (repBase_covers_insBase hx hpos)
    obtain ⟨s, hs⟩ := hrot_eq.symm
    rw [← hs]
    exact (rotate_mem_infix_double _ _ s).trans hcyc

/-- **Main Superpermutation Coverage Theorem:** If a word `w : Word (K + 2)` contains `e.u ++ e.body`
as an infix for EVERY slice `e` of EVERY canonical loop `L ∈ allCanonLoops K` of a `PureSelection K`,
then `Almanac.IsSuperpermutation (K + 2) w`! -/
theorem isSuperpermutation_of_covers_all_slices {K : Nat} [NeZero K] (hK : 4 ≤ K)
    (sel : PureSelection K) (w : Word (K + 2))
    (hcov : ∀ L ∈ allCanonLoops K, ∀ e ∈ rowSlices (sel.row L).1 (sel.row L).2,
      e.u ++ e.body <:+: w) :
    Almanac.IsSuperpermutation (K + 2) w := by
  intro p hp_nd hp_len
  have hp_perm : IsPerm (K + 2) p := ⟨hp_nd, hp_len⟩
  -- Rotate `p` so `symS K` is at the very end: `p ~r q ++ [symS K]`!
  have hS_mem : symS K ∈ p := mem_of_isPerm hp_perm (symS K)
  let p1 := p.rotate (p.idxOf (symS K) + 1)
  have hp1_perm : IsPerm (K + 2) p1 := isPerm_rotate hp_perm _
  have hp1_last : p1.getLast (by intro h; have := hp1_perm.2; rw [h] at this; simp at this) = symS K := by
    have hidx : p.idxOf (symS K) < p.length := List.idxOf_lt_length_of_mem hS_mem
    rw [List.getLast_eq_getElem]
    have hlen_eq : p1.length = p.length := List.length_rotate p _
    have hmod : (p1.length - 1 + (p.idxOf (symS K) + 1)) % p.length = p.idxOf (symS K) := by
      rw [hlen_eq]
      have : p.length - 1 + (p.idxOf (symS K) + 1) = p.idxOf (symS K) + p.length := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
    have hstep : (p.rotate (p.idxOf (symS K) + 1))[p1.length - 1]'(by rw [List.length_rotate]; omega) =
        p[(p1.length - 1 + (p.idxOf (symS K) + 1)) % p.length]'(Nat.mod_lt _ (by omega)) :=
      List.getElem_rotate p _ _ _
    exact hstep.trans (by simp only [hmod, List.getElem_idxOf])
  let wS := p1.dropLast
  have hp1_eq : p1 = wS ++ [symS K] := by
    have hne : p1 ≠ [] := by intro h; have := hp1_perm.2; rw [h] at this; simp at this
    rw [← hp1_last]; exact (List.dropLast_append_getLast hne).symm
  have hwS_nd : wS.Nodup := by
    have := hp1_perm.1; rw [hp1_eq, List.nodup_append] at this; exact this.1
  have hwS_len : wS.length = K + 1 := by
    have := hp1_perm.2; rw [hp1_eq, List.length_append, List.length_singleton] at this; omega
  have hS_notin_wS : symS K ∉ wS := by
    have := hp1_perm.1; rw [hp1_eq, List.nodup_append] at this
    intro hm; exact this.2.2 _ hm _ List.mem_cons_self rfl
  -- Locate `symZ K` inside `wS`: `wS = u ++ [symZ K] ++ v`!
  have hZ_mem : symZ K ∈ wS := by
    have hZ_p1 : symZ K ∈ p1 := mem_of_isPerm hp1_perm (symZ K)
    rw [hp1_eq, List.mem_append, List.mem_singleton] at hZ_p1
    exact hZ_p1.resolve_right (Ne.symm (symS_ne_symZ K))
  obtain ⟨uZ, vZ, hwS_eq⟩ := List.append_of_mem hZ_mem
  have hZ_notin_uv : symZ K ∉ uZ ++ vZ := by
    have := hwS_nd; rw [hwS_eq] at this
    have h1 := List.nodup_append.mp this
    have h2 := List.nodup_cons.mp h1.2.1
    intro hm
    rcases List.mem_append.mp hm with hu | hv
    · exact h1.2.2 _ hu _ List.mem_cons_self rfl
    · exact h2.1 hv
  have hS_notin_uv : symS K ∉ uZ ++ vZ := by
    intro hm; apply hS_notin_wS; rw [hwS_eq]
    rcases List.mem_append.mp hm with hu | hv
    · exact List.mem_append_left _ hu
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hv)
  -- Every element of `uZ ++ vZ` has `.1 < K`, so `uZ ++ vZ = yK.map embK` for a permutation `yK` of `Fin K`!
  have hltK : ∀ a ∈ uZ ++ vZ, a.1 < K := by
    intro a ha
    have hneS : a ≠ symS K := fun h => hS_notin_uv (h ▸ ha)
    have hneZ : a ≠ symZ K := fun h => hZ_notin_uv (h ▸ ha)
    have ha2 := a.2
    have h1 : a.1 ≠ K := fun h => hneS (by ext; exact h)
    have h2 : a.1 ≠ K + 1 := fun h => hneZ (by ext; exact h)
    omega
  let yK : List (Fin K) := (uZ ++ vZ).pmap (fun a (ha : a.1 < K) => ⟨a.1, ha⟩) hltK
  have hyK_map : yK.map embK = uZ ++ vZ := by
    dsimp [yK]; rw [List.map_pmap]
    have : ∀ (a : Fin (K + 2)) (ha : a.1 < K), embK ⟨a.1, ha⟩ = a := fun a _ => by ext; rfl
    simpa [this] using List.pmap_eq_map (p := fun a : Fin (K + 2) => a.1 < K)
      (f := fun a _ => a) (H := hltK)
  have huv_nd : (uZ ++ vZ).Nodup := by
    have := hwS_nd; rw [hwS_eq] at this
    have h1 := List.nodup_append.mp this
    have h2 := List.nodup_cons.mp h1.2.1
    exact List.nodup_append.mpr ⟨h1.1, h2.2, fun a ha b hb => h1.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
  have hyK_perm : IsPerm K yK := by
    refine ⟨?_, ?_⟩
    · rw [← hyK_map] at huv_nd; exact List.Nodup.of_map _ huv_nd
    · have := congrArg List.length hyK_map
      have hlen_uv : (uZ ++ vZ).length = K := by
        have := congrArg List.length hwS_eq; rw [hwS_len] at this; simp at this ⊢; omega
      rw [List.length_map, hlen_uv] at this; exact this
  -- Locate the canonical loop `L = canonLoop yK` and rotation `r < K` such that `yK = (sel.row L).1.rotate r`!
  let L := canonLoop yK
  have hL_canon : IsCanonLoop K L := canonLoop_isCanonLoop hyK_perm
  have hL_mem : L ∈ allCanonLoops K := (mem_allCanonLoops_iff L).mpr hL_canon
  have hrow := sel.row_perm L hL_canon
  have hrot_xy : (sel.row L).1 ~r yK := hrow.2.trans (canonLoop_isRotated yK).symm
  obtain ⟨r0, hr0⟩ := hrot_xy
  let r := r0 % K
  have hr : r < K := Nat.mod_lt r0 (by omega)
  have hyK_eq_rot : (sel.row L).1.rotate r = yK := by
    have : (sel.row L).1.rotate r0 = (sel.row L).1.rotate (r0 % (sel.row L).1.length) :=
      (List.rotate_mod _ _).symm
    rw [hrow.1.2] at this
    exact this.symm.trans hr0
  -- Check `wS = insBase ((sel.row L).1.rotate r) uZ.length`!
  have huZ_le : uZ.length ≤ K := by
    have := congrArg List.length hwS_eq; rw [hwS_len] at this; simp at this; omega
  have hwS_ins : wS = insBase ((sel.row L).1.rotate r) uZ.length := by
    rw [hyK_eq_rot, insBase, List.map_take, List.map_drop, hyK_map,
      List.take_left, List.drop_left, hwS_eq]
    simp [List.append_assoc]
  have hp_rot_ins : p ~r insBase ((sel.row L).1.rotate r) uZ.length ++ [symS K] := by
    rw [← hwS_ins, ← hp1_eq]
    exact ⟨p.idxOf (symS K) + 1, rfl⟩
  obtain ⟨e, he_row, hp_inf⟩ := rowSlices_covers_rot hK hrow.1.2 (sel.row L).2 hr huZ_le p hp_rot_ins
  exact hp_inf.trans (hcov L hL_mem e he_row)

/-! ### 6. Connector cycle edges in `B(n, h)` -/

/-- Length-`h` directed cycle in `B(n, h)` visiting all `h` cyclic rotations of `ck`. -/
def connCycleEdges {n : Nat} [NeZero n] (ck : Word n) : List (RawEdge n) :=
  (List.range ck.length).map fun r =>
    ⟨ck.rotate r, ck.rotate (r + 1), [ck.getD r 0]⟩

theorem connCycleEdges_ok {n h : Nat} [NeZero n] {ck : Word n} (hck : ck.length = h) :
    ∀ e ∈ connCycleEdges ck, EdgeOk h e := by
  intro e he
  simp only [connCycleEdges, List.mem_map, List.mem_range] at he
  obtain ⟨r, hr, rfl⟩ := he
  refine ⟨by rw [List.length_rotate, hck], by rw [List.length_rotate, hck], ?_⟩
  refine ⟨[ck.getD r 0], ?_⟩
  exact rotate_succ_eq_tail_append_head ck (0 : Fin n) hr

theorem connCycleEdges_body_sum {n h : Nat} [NeZero n] {ck : Word n} (hck : ck.length = h) :
    ((connCycleEdges ck).map (fun e => e.body.length)).sum = h := by
  simp [connCycleEdges, Function.comp_def, hck]

theorem connCycleEdges_isCircuit {n : Nat} [NeZero n] {ck : Word n} (hne : 0 < ck.length) :
    IsCircuitAt (connCycleEdges ck) ck := by
  let f : Nat → RawEdge n := fun r => ⟨ck.rotate r, ck.rotate (r + 1), [ck.getD r 0]⟩
  have hchain : ∀ m (hm : m ≤ ck.length), IsChainE ((List.range m).map f) := by
    intro m
    induction m with
    | zero => intro _; trivial
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.map_singleton]
      cases m with
      | zero => trivial
      | succ m' =>
        have hne_pre : (List.range (m' + 1)).map f ≠ [] := by simp
        refine isChainE_append _ _ hne_pre (List.cons_ne_nil _ _) (ih (by omega)) trivial ?_
        rw [List.getLast_eq_getElem]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range,
          Nat.add_sub_cancel, List.head_cons, f]
  have hne_e : connCycleEdges ck ≠ [] := by
    unfold connCycleEdges; simp [Nat.ne_of_gt hne]
  refine ⟨hne_e, hchain ck.length (Nat.le_refl _), ?_, ?_⟩
  · rw [List.head_eq_getElem]
    simp only [connCycleEdges, List.getElem_map, List.getElem_range, List.rotate_zero]
  · rw [List.getLast_eq_getElem]
    simp only [connCycleEdges, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]
    have : ck.length - 1 + 1 = ck.length := by omega
    rw [this, List.rotate_length]

theorem connCycleEdges_balanced {n : Nat} [NeZero n] {ck : Word n} (hne : 0 < ck.length) :
    Balanced (connCycleEdges ck) :=
  balanced_of_isCircuitAt (connCycleEdges_isCircuit hne)

theorem connCycleEdges_mem_rot {n : Nat} [NeZero n] {ck : Word n} (r : Nat) (hr : r < ck.length) :
    ∃ e ∈ connCycleEdges ck, e.u = ck.rotate r :=
  ⟨⟨ck.rotate r, ck.rotate (r + 1), [ck.getD r 0]⟩,
    List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, rfl⟩

/-! ### 7. Exact `head`/`tail` transitions for `'D'`, `'F'`, and `'S'` slices -/

/-- For a repair slice `repSlice x j` (`j < K`): `u = ((x.rotate j).take (K - 1)).map embK`. -/
theorem repSlice_u {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) (j : Nat) :
    (repSlice x j).u = ((x.rotate j).take (K - 1)).map embK := by
  unfold repSlice
  rw [sliceEdge_u hK (repBase_length hx j) (symZ K) (by omega), repBase,
    List.take_append_of_le_length (by simp [hx]), ← List.map_take]

/-- For a repair slice `repSlice x j`: `v = ((x.rotate (j + 1)).take (K - 1)).map embK`! -/
theorem repSlice_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) (j : Nat) :
    (repSlice x j).v = ((x.rotate (j + 1)).take (K - 1)).map embK := by
  unfold repSlice
  rw [sliceEdge_v_take hK (repBase_length hx j) (symZ K) (by omega)]
  have hmod : (repBase x j).rotate (K + 1 + 1) = (repBase x j).rotate 1 := by
    have h1 : (repBase x j).length = K + 1 := repBase_length hx j
    rw [← List.rotate_mod, h1]
    have : (K + 1 + 1) % (K + 1) = 1 := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [this]
  rw [hmod, repBase]
  cases hxr : x.rotate j with
  | nil => have := congrArg List.length hxr; simp [hx] at this; omega
  | cons a rest =>
    have hrot1 : x.rotate (j + 1) = rest ++ [a] := by
      rw [← List.rotate_rotate, hxr, List.rotate_cons_succ]; simp
    have hlen_rest : rest.length = K - 1 := by
      have := congrArg List.length hxr; simp [hx] at this; omega
    rw [hrot1]
    simp only [List.map_cons, List.cons_append, List.rotate_cons_succ, List.rotate_zero]
    rw [List.append_assoc, List.take_append_of_le_length (by simp [hlen_rest]),
      List.take_of_length_le (by simp [hlen_rest]),
      List.take_append_of_le_length (by simp [hlen_rest]),
      List.take_of_length_le (by simp [hlen_rest])]

/-- A `'D'`-row's slices form a single `K`-cycle circuit in `B(K + 2, K - 1)`! -/
theorem rowSlices_D_isCircuit {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) :
    IsCircuitAt (rowSlices x .D) ((x.take (K - 1)).map embK) := by
  have hchain : ∀ m (hm : m ≤ K), IsChainE ((List.range m).map (repSlice x)) := by
    intro m
    induction m with
    | zero => intro _; trivial
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.map_singleton]
      cases m with
      | zero => trivial
      | succ m' =>
        have hne_pre : (List.range (m' + 1)).map (repSlice x) ≠ [] := by simp
        refine isChainE_append _ _ hne_pre (List.cons_ne_nil _ _) (ih (by omega)) trivial ?_
        rw [List.getLast_eq_getElem]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range,
          Nat.add_sub_cancel, List.head_cons]
        rw [repSlice_v hK hx m', repSlice_u hK hx (m' + 1)]
  have hne : rowSlices x .D ≠ [] := by simp [rowSlices]; omega
  refine ⟨hne, hchain K (Nat.le_refl K), ?_, ?_⟩
  · rw [List.head_eq_getElem]
    simp only [rowSlices, List.getElem_map, List.getElem_range]
    rw [repSlice_u hK hx 0, List.rotate_zero]
  · rw [List.getLast_eq_getElem]
    simp only [rowSlices, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [repSlice_v hK hx (K - 1)]
    have h1 : K - 1 + 1 = x.length := by omega
    rw [h1, List.rotate_length]

theorem rowSlices_D_balanced {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) :
    Balanced (rowSlices x .D) :=
  balanced_of_isCircuitAt (rowSlices_D_isCircuit hK hx)

/-- For an inserted slice `insSlice x v j`: `u = (insBase x j).take (K - 1)`. -/
theorem insSlice_u {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) {v : Nat}
    (hv : 1 ≤ v) (j : Nat) :
    (insSlice x v j).u = (insBase x j).take (K - 1) :=
  sliceEdge_u hK (insBase_length hx j) (symS K) (by omega)

/-- For an `'F'`-row (`v = K`), port `0` jumps to port `K - 1` on the SAME row `x`:
`(insSlice x K 0).v = (insSlice x K (K - 1)).u`! -/
theorem insSlice_F_zero_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) :
    (insSlice x K 0).v = (insSlice x K (K - 1)).u := by
  rw [insSlice, sliceEdge_v_take hK (insBase_length hx 0) (symS K) (by omega),
    insSlice_u hK hx (by omega) (K - 1)]
  have hvv : K + (if 0 < K then 1 else 0) + 1 = K + 2 := by
    have : 0 < K := by omega
    simp [this]
  rw [hvv]
  have hmod : (insBase x 0).rotate (K + 2) = (insBase x 0).rotate 1 := by
    rw [← List.rotate_mod, insBase_length hx 0]
    have : (K + 2) % (K + 1) = 1 := by
      have h1 : K + 2 = 1 + (K + 1) := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [this]
  rw [hmod]
  unfold insBase
  simp only [List.take_zero, List.drop_zero, List.map_nil, List.nil_append, List.singleton_append,
    List.rotate_cons_succ, List.rotate_zero]
  have hL : (x.map embK ++ [symZ K]).take (K - 1) = (x.take (K - 1)).map embK := by
    rw [List.take_append_of_le_length (by simp [hx]), ← List.map_take]
  have hR : ((x.take (K - 1)).map embK ++ [symZ K] ++ (x.drop (K - 1)).map embK).take (K - 1) =
      (x.take (K - 1)).map embK := by
    rw [List.append_assoc, List.take_append_of_le_length (by simp [hx]),
      List.take_of_length_le (by simp [hx])]
  rw [hL, hR]

/-- For an `'F'`-row (`v = K`), port `j` (`1 ≤ j < K`) transitions to `(FStep x, j - 1)`:
`(insSlice x K j).v = (insSlice (FStep x) K (j - 1)).u`! -/
theorem insSlice_F_pos_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K)
    {j : Nat} (hj1 : 1 ≤ j) (hjK : j < K) :
    (insSlice x K j).v = (insSlice (FStep x) K (j - 1)).u := by
  rw [insSlice, sliceEdge_v_take hK (insBase_length hx j) (symS K) (by omega),
    insSlice_u hK ((FStep_perm x).length_eq.trans hx) (by omega) (j - 1)]
  have hvv : K + (if j < K then 1 else 0) + 1 = K + 2 := by simp [hjK]
  rw [hvv]
  have hmod : (insBase x j).rotate (K + 2) = (insBase x j).rotate 1 := by
    rw [← List.rotate_mod, insBase_length hx j]
    have : (K + 2) % (K + 1) = 1 := by
      have h1 : K + 2 = 1 + (K + 1) := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [this]
  rw [hmod, insBase_rotate_le hx hj1 hjK]
  have hagree : (x.rotate 1).take (K - 2) = (FStep x).take (K - 2) := by
    unfold FStep
    rw [hx]
    have h1 : x = x.take (K - 1) ++ x.drop (K - 1) := (List.take_append_drop (K - 1) x).symm
    cases hpre : x.take (K - 1) with
    | nil => have := congrArg List.length hpre; simp [hx] at this; omega
    | cons a rest =>
      have hlen_r : rest.length = K - 2 := by
        have := congrArg List.length hpre; simp [hx] at this; omega
      have hx_eq : x = a :: (rest ++ x.drop (K - 1)) := by
        conv_lhs => rw [h1, hpre, List.cons_append]
      rw [hx_eq, List.rotate_cons_succ, List.rotate_zero, List.rotate_cons_succ, List.rotate_zero]
      simp only [List.append_assoc]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  unfold insBase
  have hj_le : j - 1 ≤ K - 2 := by omega
  have htake_eq : (x.rotate 1).take (j - 1) = (FStep x).take (j - 1) := by
    have h1 := congrArg (List.take (j - 1)) hagree
    simpa [List.take_take, Nat.min_eq_left hj_le] using h1
  have hdrop_take_eq : ((x.rotate 1).drop (j - 1)).take (K - 2 - (j - 1)) =
      ((FStep x).drop (j - 1)).take (K - 2 - (j - 1)) := by
    have h1 := congrArg (List.drop (j - 1)) hagree
    simpa [List.drop_take] using h1
  rw [htake_eq]
  let P := ((FStep x).take (j - 1)).map embK ++ [symZ K]
  have hP : P.length = j := by dsimp [P]; simp [(FStep_perm x).length_eq, hx]; omega
  change (P ++ ((x.rotate 1).drop (j - 1)).map embK).take (K - 1) =
    (P ++ ((FStep x).drop (j - 1)).map embK).take (K - 1)
  have htake_P : ∀ rest : List (Fin (K + 2)),
      (P ++ rest).take (K - 1) = P ++ rest.take (K - 1 - j) := by
    intro rest
    rw [List.take_append, hP, List.take_of_length_le (by omega)]
  rw [htake_P, htake_P]
  congr 1
  have hsub : K - 1 - j = K - 2 - (j - 1) := by omega
  rw [hsub, ← List.map_take, ← List.map_take, hdrop_take_eq]

/-- For an `'S'`-row (`v = K - 2`), port `j` (`j ≤ K - 3`) transitions to `(SStep x, j + 1)`:
`(insSlice x (K - 2) j).v = (insSlice (SStep x) (K - 2) (j + 1)).u`! -/
theorem insSlice_S_lt_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K)
    {j : Nat} (hj : j ≤ K - 3) :
    (insSlice x (K - 2) j).v = (insSlice (SStep x) (K - 2) (j + 1)).u := by
  rw [insSlice, sliceEdge_v_take hK (insBase_length hx j) (symS K) (by omega),
    insSlice_u hK ((SStep_perm x (by omega)).length_eq.trans hx) (by omega) (j + 1)]
  have hjv : j < K - 2 := by omega
  have hvv : K - 2 + (if j < K - 2 then 1 else 0) + 1 = K := by simp [hjv]; omega
  rw [hvv]
  have hdrop1 : (x.drop (K - 1)).length = 1 := by simp [hx]; omega
  let A := (x.take j).map embK ++ [symZ K] ++ ((x.drop j).take (K - 1 - j)).map embK
  let B := (x.drop (K - 1)).map embK
  have hins_eq : insBase x j = A ++ B := by
    have hdx : x.drop j = (x.drop j).take (K - 1 - j) ++ x.drop (K - 1) := by
      have := (List.take_append_drop (K - 1 - j) (x.drop j)).symm
      rw [List.drop_drop] at this
      have hidx : j + (K - 1 - j) = K - 1 := by omega
      rwa [hidx] at this
    conv_lhs => unfold insBase; rw [hdx, List.map_append]
    simp [A, B, List.append_assoc]
  have hA : A.length = K := by dsimp [A]; simp [hx]; omega
  have hrot_AB : (insBase x j).rotate K = B ++ A := by
    have hrot := List.rotate_append_length_eq A B
    rw [hA] at hrot
    rw [hins_eq, hrot]
  rw [hrot_AB]
  dsimp [A, B]
  have hS_take : (SStep x).take (K - 2) = x.drop (K - 1) ++ x.take (K - 3) := by
    unfold SStep; rw [hx]
    have hlen12 : (x.drop (K - 1) ++ x.take (K - 3)).length = K - 2 := by simp [hx]; omega
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hS_take_j1 : (SStep x).take (j + 1) = x.drop (K - 1) ++ x.take j := by
    have h := congrArg (List.take (j + 1)) hS_take
    rw [List.take_take, Nat.min_eq_left (by omega), List.take_append, hdrop1,
      List.take_of_length_le (l := x.drop (K - 1)) (by omega)] at h
    simpa [List.take_take, Nat.min_eq_left hj] using h
  have hS_drop_take : ((SStep x).drop (j + 1)).take (K - 3 - j) = (x.drop j).take (K - 3 - j) := by
    have h := congrArg (List.drop (j + 1)) hS_take
    have hnil : (x.drop (K - 1)).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [List.drop_take, List.drop_append, hdrop1, hnil, List.nil_append] at h
    have hsub : K - 2 - (j + 1) = K - 3 - j := by omega
    rw [hsub] at h
    have hj1 : j + 1 - 1 = j := by omega
    rw [hj1] at h
    rw [h, List.drop_take]
  unfold insBase
  rw [hS_take_j1, List.map_append]
  let P := (x.drop (K - 1)).map embK ++ (x.take j).map embK ++ [symZ K]
  have hP : P.length = j + 2 := by dsimp [P]; simp [hx]; omega
  have hL : ((x.drop (K - 1)).map embK ++ ((x.take j).map embK ++ [symZ K] ++
      ((x.drop j).take (K - 1 - j)).map embK)) =
      P ++ ((x.drop j).take (K - 1 - j)).map embK := by simp [P, List.append_assoc]
  rw [hL]
  change (P ++ ((x.drop j).take (K - 1 - j)).map embK).take (K - 1) =
    (P ++ ((SStep x).drop (j + 1)).map embK).take (K - 1)
  have htake_P : ∀ rest : List (Fin (K + 2)),
      (P ++ rest).take (K - 1) = P ++ rest.take (K - 1 - (j + 2)) := by
    intro rest
    rw [List.take_append, hP, List.take_of_length_le (by omega)]
  rw [htake_P, htake_P]
  congr 1
  have hsub : K - 1 - (j + 2) = K - 3 - j := by omega
  rw [hsub, ← List.map_take, ← List.map_take, hS_drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- For an `'S'`-row (`v = K - 2`), port `K - 2` transitions to `repSlice x (K - 2)`. -/
theorem insSlice_S_km2_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) :
    (insSlice x (K - 2) (K - 2)).v = (repSlice x (K - 2)).u := by
  rw [insSlice, sliceEdge_v_take hK (insBase_length hx (K - 2)) (symS K) (by omega),
    repSlice_u hK hx (K - 2)]
  have hvv : K - 2 + (if K - 2 < K - 2 then 1 else 0) + 1 = K - 1 := by simp; omega
  rw [hvv]
  let A := (x.take (K - 2)).map embK ++ [symZ K]
  let B := (x.drop (K - 2)).map embK
  have hA : A.length = K - 1 := by dsimp [A]; simp [hx]; omega
  have hrot_ins : (insBase x (K - 2)).rotate (K - 1) = B ++ A := by
    have hrot := List.rotate_append_length_eq A B
    rw [hA] at hrot
    exact hrot
  rw [hrot_ins, List.rotate_eq_drop_append_take (by omega)]
  dsimp [A, B]
  have hdl : (x.drop (K - 2)).length = 2 := by simp [hx]; omega
  have hL : ((x.drop (K - 2)).map embK ++ ((x.take (K - 2)).map embK ++ [symZ K])).take (K - 1) =
      (x.drop (K - 2)).map embK ++ ((x.take (K - 2)).map embK ++ [symZ K]).take (K - 3) := by
    rw [List.take_append, List.length_map, hdl, List.take_of_length_le (by simp [hdl]; omega)]
    have hsub : K - 1 - 2 = K - 3 := by omega
    rw [hsub]
  have hR : ((x.drop (K - 2) ++ x.take (K - 2)).take (K - 1)).map embK =
      (x.drop (K - 2)).map embK ++ ((x.take (K - 2)).take (K - 3)).map embK := by
    rw [List.take_append, hdl, List.take_of_length_le (by omega), List.map_append]
    have hsub : K - 1 - 2 = K - 3 := by omega
    rw [hsub]
  rw [hL, hR]
  congr 1
  rw [List.take_append_of_le_length (by simp [hx]; omega), ← List.map_take]

/-- For an `'S'`-row (`v = K - 2`), `repSlice x (K - 1)` transitions to `insSlice x (K - 2) (K - 1)`. -/
theorem repSlice_km1_v_eq_ins_km1_u {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K)
    {v : Nat} (hv : 1 ≤ v) :
    (repSlice x (K - 1)).v = (insSlice x v (K - 1)).u := by
  rw [repSlice_v hK hx (K - 1), insSlice_u hK hx hv (K - 1)]
  have hrotK : x.rotate (K - 1 + 1) = x := by
    have : K - 1 + 1 = x.length := by omega
    rw [this, List.rotate_length]
  rw [hrotK]
  unfold insBase
  conv_rhs =>
    rw [List.append_assoc, List.take_append_of_le_length (by simp [hx]),
      List.take_of_length_le (by simp [hx])]

/-- For an `'S'`-row (`v = K - 2`), port `K - 1` transitions to `(SStep x, 0)`! -/
theorem insSlice_S_km1_v {K : Nat} (hK : 4 ≤ K) {x : List (Fin K)} (hx : x.length = K) :
    (insSlice x (K - 2) (K - 1)).v = (insSlice (SStep x) (K - 2) 0).u := by
  rw [insSlice, sliceEdge_v_take hK (insBase_length hx (K - 1)) (symS K) (by omega),
    insSlice_u hK ((SStep_perm x (by omega)).length_eq.trans hx) (by omega) 0]
  have hvv : K - 2 + (if K - 1 < K - 2 then 1 else 0) + 1 = K - 1 := by
    have : ¬(K - 1 < K - 2) := by omega
    simp [this]; omega
  rw [hvv]
  let A := (x.take (K - 1)).map embK
  let B := [symZ K] ++ (x.drop (K - 1)).map embK
  have hA : A.length = K - 1 := by dsimp [A]; simp [hx]
  have hrot_ins : (insBase x (K - 1)).rotate (K - 1) = B ++ A := by
    have hins : insBase x (K - 1) = A ++ B := by simp [insBase, A, B, List.append_assoc]
    have hrot := List.rotate_append_length_eq A B
    rw [hA] at hrot
    rw [hins, hrot]
  rw [hrot_ins]
  dsimp [A, B, insBase]
  simp only [List.drop_zero, List.map_nil, List.nil_append, List.cons_append]
  have htake_cons : ∀ (a : Fin (K + 2)) (l : List (Fin (K + 2))),
      (a :: l).take (K - 1) = a :: l.take (K - 2) := by
    intro a l
    cases hm : K - 1 with
    | zero => omega
    | succ m =>
      have : m = K - 2 := by omega
      subst this; rfl
  rw [htake_cons, htake_cons]
  congr 1
  have hS_take : (SStep x).take (K - 2) = x.drop (K - 1) ++ x.take (K - 3) := by
    unfold SStep; rw [hx]
    have hlen12 : (x.drop (K - 1) ++ x.take (K - 3)).length = K - 2 := by simp [hx]; omega
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [← List.map_take, hS_take, List.map_append]
  have hdl : ((x.drop (K - 1)).map embK).length = 1 := by simp [hx]; omega
  rw [List.take_append, hdl, List.take_of_length_le (by omega)]
  congr 1
  have hsub : K - 2 - 1 = K - 3 := by omega
  rw [hsub, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]

end AsymptoticZero


