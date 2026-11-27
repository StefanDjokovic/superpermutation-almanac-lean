import AlmanacDefs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Infix
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Eulerian Circuit Existence & Bag Assembly for De Bruijn Words

Given any finite list of balanced, weakly-connected directed edge-bags `B_1, ..., B_κ`
whose edges `(u, v, body)` satisfy `u.length = h`, `v.length = h`, and `v <:+ u ++ body`,
constructs a single word `w : Almanac.Word n` of exact length
`h * κ + ∑_{B ∈ bags} ∑_{e ∈ B} e.body.length`
containing `e.u ++ e.body` as a contiguous infix for every edge `e` in every bag.
-/

namespace AsymptoticZero

open Almanac

/-- A directed multigraph edge labeled by its starting `h`-mer `u`, ending `h`-mer `v`,
and appended `body` (so `v` is a suffix of `u ++ body`). -/
structure RawEdge (n : Nat) where
  u : Word n
  v : Word n
  body : Word n
  deriving DecidableEq

/-- Well-formedness of a directed edge at overlap width `h`. -/
def EdgeOk {n : Nat} (h : Nat) (e : RawEdge n) : Prop :=
  e.u.length = h ∧ e.v.length = h ∧ e.v <:+ e.u ++ e.body

/-- Out-degree of vertex `x` in edge multiset `E`. -/
def outDeg {n : Nat} (E : List (RawEdge n)) (x : Word n) : Nat :=
  (E.filter (fun e => decide (e.u = x))).length

/-- In-degree of vertex `x` in edge multiset `E`. -/
def inDeg {n : Nat} (E : List (RawEdge n)) (x : Word n) : Nat :=
  (E.filter (fun e => decide (e.v = x))).length

/-- Eulerian balance: every vertex has equal in-degree and out-degree. -/
def Balanced {n : Nat} (E : List (RawEdge n)) : Prop :=
  ∀ x : Word n, outDeg E x = inDeg E x

/-- Directed chain of edges: consecutive endpoints match. -/
def IsChainE {n : Nat} : List (RawEdge n) → Prop
  | [] => True
  | [_] => True
  | e1 :: e2 :: rest => e1.v = e2.u ∧ IsChainE (e2 :: rest)

/-- Non-empty closed directed trail starting at `v0`. -/
def IsCircuitAt {n : Nat} (C : List (RawEdge n)) (v0 : Word n) : Prop :=
  ∃ hne : C ≠ [], IsChainE C ∧ (C.head hne).u = v0 ∧ (C.getLast hne).v = v0

/-- Non-empty closed directed trail. -/
def IsCircuit {n : Nat} (C : List (RawEdge n)) : Prop :=
  ∃ v0, IsCircuitAt C v0

/-- Underlying undirected adjacency relation of edge list `E`. -/
def UndirAdj {n : Nat} (E : List (RawEdge n)) (x y : Word n) : Prop :=
  ∃ e ∈ E, (e.u = x ∧ e.v = y) ∨ (e.v = x ∧ e.u = y)

/-- Weak connectivity on the active edges of `E`. -/
def WeaklyConnected {n : Nat} (E : List (RawEdge n)) : Prop :=
  ∀ e1 ∈ E, ∀ e2 ∈ E, Relation.ReflTransGen (UndirAdj E) e1.u e2.u

/-! ### Basic degree & permutation lemmas -/

theorem outDeg_nil {n : Nat} (x : Word n) : outDeg ([] : List (RawEdge n)) x = 0 := rfl
theorem inDeg_nil {n : Nat} (x : Word n) : inDeg ([] : List (RawEdge n)) x = 0 := rfl

theorem outDeg_cons {n : Nat} (e : RawEdge n) (E : List (RawEdge n)) (x : Word n) :
    outDeg (e :: E) x = (if e.u = x then 1 else 0) + outDeg E x := by
  unfold outDeg
  by_cases h : e.u = x <;> simp [h, Nat.add_comm]

theorem inDeg_cons {n : Nat} (e : RawEdge n) (E : List (RawEdge n)) (x : Word n) :
    inDeg (e :: E) x = (if e.v = x then 1 else 0) + inDeg E x := by
  unfold inDeg
  by_cases h : e.v = x <;> simp [h, Nat.add_comm]

theorem outDeg_append {n : Nat} (E1 E2 : List (RawEdge n)) (x : Word n) :
    outDeg (E1 ++ E2) x = outDeg E1 x + outDeg E2 x := by
  unfold outDeg; simp [List.filter_append]

theorem inDeg_append {n : Nat} (E1 E2 : List (RawEdge n)) (x : Word n) :
    inDeg (E1 ++ E2) x = inDeg E1 x + inDeg E2 x := by
  unfold inDeg; simp [List.filter_append]

theorem outDeg_perm {n : Nat} {E1 E2 : List (RawEdge n)} (h : E1.Perm E2) (x : Word n) :
    outDeg E1 x = outDeg E2 x :=
  (h.filter _).length_eq

theorem inDeg_perm {n : Nat} {E1 E2 : List (RawEdge n)} (h : E1.Perm E2) (x : Word n) :
    inDeg E1 x = inDeg E2 x :=
  (h.filter _).length_eq

theorem balanced_nil {n : Nat} : Balanced ([] : List (RawEdge n)) := fun _ => rfl

theorem balanced_perm {n : Nat} {E1 E2 : List (RawEdge n)} (h : E1.Perm E2) (hb : Balanced E1) :
    Balanced E2 := fun x => by
  rw [← outDeg_perm h x, ← inDeg_perm h x]; exact hb x

theorem balanced_append {n : Nat} {E1 E2 : List (RawEdge n)} (h1 : Balanced E1) (h2 : Balanced E2) :
    Balanced (E1 ++ E2) := fun x => by
  rw [outDeg_append, inDeg_append, h1 x, h2 x]

theorem balanced_flatten {n : Nat} :
    ∀ (Ls : List (List (RawEdge n))), (∀ L ∈ Ls, Balanced L) → Balanced Ls.flatten
  | [], _ => balanced_nil
  | L :: rest, h => balanced_append (h L List.mem_cons_self)
      (balanced_flatten rest (fun M hM => h M (List.mem_cons_of_mem _ hM)))

theorem balanced_of_perm_append {n : Nat} {E C R : List (RawEdge n)}
    (hp : E.Perm (C ++ R)) (hE : Balanced E) (hC : Balanced C) : Balanced R := fun x => by
  have h1 := balanced_perm hp hE x
  rw [outDeg_append, inDeg_append, hC x] at h1
  omega

theorem exists_edge_out_of_pos {n : Nat} {E : List (RawEdge n)} {x : Word n}
    (h : 0 < outDeg E x) : ∃ e ∈ E, e.u = x := by
  unfold outDeg at h
  have hne : E.filter (fun e => decide (e.u = x)) ≠ [] := List.ne_nil_of_length_pos h
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter, decide_eq_true_eq] at he
  exact ⟨e, he.1, he.2⟩

theorem outDeg_pos_of_mem {n : Nat} {E : List (RawEdge n)} {e : RawEdge n} (he : e ∈ E) :
    0 < outDeg E e.u := by
  unfold outDeg
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩)

theorem inDeg_pos_of_mem {n : Nat} {E : List (RawEdge n)} {e : RawEdge n} (he : e ∈ E) :
    0 < inDeg E e.v := by
  unfold inDeg
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩)

/-! ### Chain degree accounting & circuit extraction -/

theorem chain_deg_balance {n : Nat} :
    ∀ (P : List (RawEdge n)) (hne : P ≠ []), IsChainE P →
      ∀ x : Word n,
        outDeg P x + (if (P.getLast hne).v = x then 1 else 0) =
        inDeg P x + (if (P.head hne).u = x then 1 else 0)
  | [], hne, _, _ => absurd rfl hne
  | [e], _, _, x => by
    simp only [outDeg_cons, outDeg_nil, inDeg_cons, inDeg_nil, List.getLast_singleton,
      List.head_cons, Nat.add_zero]
    by_cases h1 : e.u = x <;> by_cases h2 : e.v = x <;> simp [h1, h2]
  | e1 :: e2 :: rest, _, hc, x => by
    have ih := chain_deg_balance (e2 :: rest) (List.cons_ne_nil _ _) hc.2 x
    rw [outDeg_cons, inDeg_cons, List.getLast_cons (List.cons_ne_nil _ _), List.head_cons]
    simp only [List.head_cons] at ih
    rw [hc.1]
    by_cases h1 : e2.u = x <;> simp only [h1, ↓reduceIte] at ih ⊢ <;> omega

theorem balanced_of_isCircuitAt {n : Nat} {C : List (RawEdge n)} {v0 : Word n}
    (hC : IsCircuitAt C v0) : Balanced C := by
  obtain ⟨hne, hch, hhd, htl⟩ := hC
  intro x
  have h := chain_deg_balance C hne hch x
  rw [hhd, htl] at h
  omega

theorem balanced_of_isCircuit {n : Nat} {C : List (RawEdge n)} (hC : IsCircuit C) : Balanced C := by
  obtain ⟨v0, h⟩ := hC; exact balanced_of_isCircuitAt h

theorem isChainE_append {n : Nat} :
    ∀ (P1 P2 : List (RawEdge n)) (h1 : P1 ≠ []) (h2 : P2 ≠ []),
      IsChainE P1 → IsChainE P2 → (P1.getLast h1).v = (P2.head h2).u →
      IsChainE (P1 ++ P2)
  | [], _, h1, _, _, _, _ => absurd rfl h1
  | [e1], e2 :: rest, _, _, _, hc2, hlink => by
    simpa [IsChainE] using And.intro hlink hc2
  | e1 :: e2 :: r1, P2, _, h2, hc1, hc2, hlink => by
    refine ⟨hc1.1, isChainE_append (e2 :: r1) P2 (List.cons_ne_nil _ _) h2 hc1.2 hc2 ?_⟩
    simpa [List.getLast_cons] using hlink

theorem isChainE_split {n : Nat} :
    ∀ (P1 P2 : List (RawEdge n)), IsChainE (P1 ++ P2) →
      IsChainE P1 ∧ IsChainE P2 ∧
      ∀ (h1 : P1 ≠ []) (h2 : P2 ≠ []), (P1.getLast h1).v = (P2.head h2).u
  | [], P2, h => ⟨trivial, h, fun h1 _ => absurd rfl h1⟩
  | [_], [], _ => ⟨trivial, trivial, fun _ h2 => absurd rfl h2⟩
  | [e1], e2 :: r2, h => ⟨trivial, h.2, fun _ _ => h.1⟩
  | e1 :: e2 :: r1, P2, h => by
    have ⟨hc1, hc2, hlink⟩ := isChainE_split (e2 :: r1) P2 h.2
    refine ⟨⟨h.1, hc1⟩, hc2, fun _ h2 => ?_⟩
    simpa [List.getLast_cons] using hlink (List.cons_ne_nil _ _) h2

/-- Extend a non-empty directed trail `acc` in balanced multiset `R` until it closes back at `v0`. -/
private theorem extend_to_circuit {n : Nat} {R : List (RawEdge n)} (hR : Balanced R) (v0 : Word n) :
    ∀ (k : Nat) (rem acc : List (RawEdge n)) (hacc : acc ≠ []),
      rem.length ≤ k →
      R.Perm (acc ++ rem) →
      IsChainE acc →
      (acc.head hacc).u = v0 →
      ∃ C R', R.Perm (C ++ R') ∧ IsCircuitAt C v0 := by
  intro k
  induction k with
  | zero =>
    intro rem acc hacc hlen hperm hch hhd
    have hrem_nil : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrem_nil
    simp only [List.append_nil] at hperm
    have hbal := balanced_perm hperm hR
    have hdeg := chain_deg_balance acc hacc hch (acc.getLast hacc).v
    have hbal_v := hbal (acc.getLast hacc).v
    have htl : (acc.getLast hacc).v = v0 := by
      by_contra hne
      rw [hhd] at hdeg
      split_ifs at hdeg with h1 h2
      · exact absurd h2.symm hne
      · omega
      · exact absurd rfl h1
      · exact absurd rfl h1
    exact ⟨acc, [], by simpa using hperm, ⟨hacc, hch, hhd, htl⟩⟩
  | succ k ih =>
    intro rem acc hacc hlen hperm hch hhd
    by_cases hclosed : (acc.getLast hacc).v = v0
    · exact ⟨acc, rem, hperm, ⟨hacc, hch, hhd, hclosed⟩⟩
    · -- Since cur ≠ v0, outDeg rem cur > 0!
      let cur := (acc.getLast hacc).v
      have hdeg_acc := chain_deg_balance acc hacc hch cur
      rw [hhd] at hdeg_acc
      have hbal_all := balanced_perm hperm hR cur
      rw [outDeg_append, inDeg_append] at hbal_all
      have hout_pos : 0 < outDeg rem cur := by
        have hne_cur : v0 ≠ cur := Ne.symm hclosed
        have heq_cur : (acc.getLast hacc).v = cur := rfl
        simp only [heq_cur, hne_cur, ↓reduceIte] at hdeg_acc
        omega
      obtain ⟨e, he_mem, he_u⟩ := exists_edge_out_of_pos hout_pos
      have hperm_rem : rem.Perm (e :: rem.erase e) := List.perm_cons_erase he_mem
      have hlen_er : (rem.erase e).length ≤ k := by
        have := hperm_rem.length_eq
        simp only [List.length_cons] at this
        omega
      have hperm' : R.Perm ((acc ++ [e]) ++ rem.erase e) := by
        refine hperm.trans ((List.Perm.append_left acc hperm_rem).trans ?_)
        simp [List.append_assoc]
      have hch' : IsChainE (acc ++ [e]) :=
        isChainE_append acc [e] hacc (List.cons_ne_nil _ _) hch trivial he_u.symm
      have hhd' : ((acc ++ [e]).head (List.append_ne_nil_of_left_ne_nil hacc _)).u = v0 := by
        rw [List.head_append_of_ne_nil hacc]; exact hhd
      exact ih (rem.erase e) (acc ++ [e]) (List.append_ne_nil_of_left_ne_nil hacc _)
        hlen_er hperm' hch' hhd'

/-- Extract a non-empty circuit starting at `v0` from any balanced multiset `R` having an edge out of `v0`. -/
theorem extract_circuit {n : Nat} {R : List (RawEdge n)} (hR : Balanced R)
    {v0 : Word n} (hex : ∃ e ∈ R, e.u = v0) :
    ∃ C R', R.Perm (C ++ R') ∧ IsCircuitAt C v0 := by
  obtain ⟨e, he_mem, he_u⟩ := hex
  have hperm : R.Perm ([e] ++ R.erase e) := by simpa using List.perm_cons_erase he_mem
  exact extend_to_circuit hR v0 (R.erase e).length (R.erase e) [e] (List.cons_ne_nil _ _)
    (Nat.le_refl _) hperm trivial he_u

/-- Rotate a circuit `C` to start at the origin `e.u` of any edge `e ∈ C`. -/
theorem rotate_circuit_to {n : Nat} {C : List (RawEdge n)} {v0 : Word n}
    (hC : IsCircuitAt C v0) {e : RawEdge n} (he : e ∈ C) :
    ∃ C', C'.Perm C ∧ IsCircuitAt C' e.u := by
  obtain ⟨hne, hch, hhd, htl⟩ := hC
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
  cases pre with
  | nil =>
    exact ⟨e :: post, List.Perm.refl _, ⟨List.cons_ne_nil _ _, hch, rfl, htl.trans hhd.symm⟩⟩
  | cons p0 pre' =>
    have hpre_ne : (p0 :: pre') ≠ [] := List.cons_ne_nil _ _
    have hpost_ne : (e :: post) ≠ [] := List.cons_ne_nil _ _
    have ⟨hc_pre, hc_post, hlink_mid⟩ := isChainE_split (p0 :: pre') (e :: post) hch
    have hlink_wrap : ((e :: post).getLast hpost_ne).v = ((p0 :: pre').head hpre_ne).u := by
      have hgl : ((p0 :: pre') ++ e :: post).getLast hne = (e :: post).getLast hpost_ne :=
        List.getLast_append_of_ne_nil _ hpost_ne
      have hhd' : ((p0 :: pre') ++ e :: post).head hne = (p0 :: pre').head hpre_ne :=
        List.head_append_of_ne_nil hpre_ne
      rw [← hgl, ← hhd', hhd, htl]
    have hch' : IsChainE ((e :: post) ++ (p0 :: pre')) :=
      isChainE_append (e :: post) (p0 :: pre') hpost_ne hpre_ne hc_post hc_pre hlink_wrap
    have hne' : (e :: post) ++ (p0 :: pre') ≠ [] := List.cons_ne_nil _ _
    have htl' : (((e :: post) ++ (p0 :: pre')).getLast hne').v = e.u := by
      rw [List.getLast_append_of_ne_nil _ hpre_ne]
      exact hlink_mid hpre_ne hpost_ne
    exact ⟨(e :: post) ++ (p0 :: pre'), List.perm_append_comm, ⟨hne', hch', rfl, htl'⟩⟩

/-- Splice two circuits starting at the same vertex `v`. -/
theorem splice_circuits {n : Nat} {C1 C2 : List (RawEdge n)} {v : Word n}
    (h1 : IsCircuitAt C1 v) (h2 : IsCircuitAt C2 v) :
    IsCircuitAt (C1 ++ C2) v := by
  obtain ⟨hne1, hc1, hhd1, htl1⟩ := h1
  obtain ⟨hne2, hc2, hhd2, htl2⟩ := h2
  refine ⟨List.append_ne_nil_of_left_ne_nil hne1 _,
    isChainE_append C1 C2 hne1 hne2 hc1 hc2 (htl1.trans hhd2.symm), ?_, ?_⟩
  · rw [List.head_append_of_ne_nil hne1]; exact hhd1
  · rw [List.getLast_append_of_ne_nil _ hne2]; exact htl2

/-- Every vertex endpoint `e.v` of an edge `e ∈ C` in a circuit `C` is also `e'.u` for some `e' ∈ C`. -/
theorem circuit_v_is_some_u {n : Nat} {C : List (RawEdge n)} {v0 : Word n}
    (hC : IsCircuitAt C v0) {e : RawEdge n} (he : e ∈ C) :
    ∃ e' ∈ C, e'.u = e.v := by
  have hbal := balanced_of_isCircuitAt hC e.v
  have hin := inDeg_pos_of_mem he
  exact exists_edge_out_of_pos (by omega)

/-- Crossing lemma along an `UndirAdj` path: from `x ∈ S` to `y ∉ S`, some edge crosses `S` to `¬S`. -/
private theorem crossing_edge {n : Nat} {E : List (RawEdge n)} {S : Word n → Prop}
    {x y : Word n} (hpath : Relation.ReflTransGen (UndirAdj E) x y)
    (hx : S x) (hy : ¬ S y) :
    ∃ e ∈ E, (S e.u ∧ ¬ S e.v) ∨ (S e.v ∧ ¬ S e.u) := by
  induction hpath with
  | refl => exact absurd hx hy
  | @tail b c _ hadj ih =>
    by_cases hb : S b
    · obtain ⟨e, he, hdir⟩ := hadj
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨e, he, Or.inl ⟨hb, hy⟩⟩
      · exact ⟨e, he, Or.inr ⟨hb, hy⟩⟩
    · exact ih hb

/-- Main Hierholzer theorem: every non-empty balanced, weakly-connected edge list has an Eulerian circuit! -/
theorem eulerian_circuit_exists {n : Nat} {E : List (RawEdge n)}
    (hne : E ≠ []) (hbal : Balanced E) (hconn : WeaklyConnected E) :
    ∃ C, C.Perm E ∧ IsCircuit C := by
  -- Helper by induction on `k ≥ R.length`
  have hgrow : ∀ (k : Nat) (C R : List (RawEdge n)),
      R.length ≤ k → E.Perm (C ++ R) → IsCircuit C →
      ∃ C_full, C_full.Perm E ∧ IsCircuit C_full := by
    intro k
    induction k with
    | zero =>
      intro C R hlen hperm hC
      have hR : R = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hR
      exact ⟨C, by simpa using hperm.symm, hC⟩
    | succ k ih =>
      intro C R hlen hperm hC
      cases hR : R with
      | nil =>
        rw [hR, List.append_nil] at hperm
        exact ⟨C, hperm.symm, hC⟩
      | cons er Rrest =>
        rw [hR] at hperm hlen
        obtain ⟨v0, hC0⟩ := hC
        have hC_ne : C ≠ [] := hC0.1
        obtain ⟨ec, hec⟩ := List.exists_mem_of_ne_nil C hC_ne
        have hR_bal : Balanced (er :: Rrest) :=
          balanced_of_perm_append hperm hbal (balanced_of_isCircuitAt hC0)
        -- Find a vertex `v` present in `C` (`∃ e ∈ C, e.u = v`) that also has an outgoing edge in `R`!
        let S : Word n → Prop := fun x => ∃ e ∈ C, e.u = x
        have hex_shared : ∃ ec' ∈ C, ∃ er' ∈ (er :: Rrest), er'.u = ec'.u := by
          by_cases herS : S er.u
          · obtain ⟨ec', hec', hu⟩ := herS
            exact ⟨ec', hec', er, List.mem_cons_self, hu.symm⟩
          · have hec_E : ec ∈ E := hperm.mem_iff.mpr (List.mem_append_left _ hec)
            have her_E : er ∈ E := hperm.mem_iff.mpr (List.mem_append_right _ List.mem_cons_self)
            have hpath := hconn ec hec_E er her_E
            obtain ⟨ex, hex_E, hcross⟩ := crossing_edge hpath ⟨ec, hec, rfl⟩ herS
            have hex_notC : ex ∉ C := by
              intro hmem
              rcases hcross with ⟨_, hnotv⟩ | ⟨_, hnotu⟩
              · exact hnotv (circuit_v_is_some_u hC0 hmem)
              · exact hnotu ⟨ex, hmem, rfl⟩
            have hex_R : ex ∈ er :: Rrest := by
              have hmem := hperm.mem_iff.mp hex_E
              rcases List.mem_append.mp hmem with h1 | h2
              · exact absurd h1 hex_notC
              · exact h2
            rcases hcross with ⟨⟨ec', hec', hu⟩, _⟩ | ⟨⟨ec', hec', hu⟩, _⟩
            · exact ⟨ec', hec', ex, hex_R, hu.symm⟩
            · have hin : 0 < inDeg (er :: Rrest) ec'.u := by
                rw [hu]; exact inDeg_pos_of_mem hex_R
              have hout : 0 < outDeg (er :: Rrest) ec'.u := by
                rw [hR_bal ec'.u]; exact hin
              obtain ⟨er', her', her'_u⟩ := exists_edge_out_of_pos hout
              exact ⟨ec', hec', er', her', her'_u⟩
        obtain ⟨ec', hec', er', her', her'_u⟩ := hex_shared
        obtain ⟨C_rot, hCrot_perm, hCrot_at⟩ := rotate_circuit_to hC0 hec'
        obtain ⟨C_new, R', hR_perm, hCnew_at⟩ := extract_circuit hR_bal ⟨er', her', her'_u⟩
        have hCnew_ne : C_new ≠ [] := hCnew_at.1
        have hR'_len : R'.length ≤ k := by
          have h1 := hR_perm.length_eq
          rw [List.length_append] at h1
          have h2 : 0 < C_new.length := List.length_pos_of_ne_nil hCnew_ne
          omega
        have hperm' : E.Perm ((C_new ++ C_rot) ++ R') := by
          refine hperm.trans ?_
          have h1 : (C ++ (er :: Rrest)).Perm (C_rot ++ (C_new ++ R')) :=
            List.Perm.append hCrot_perm.symm hR_perm
          refine h1.trans ?_
          rw [← List.append_assoc]
          exact List.Perm.append_right R' List.perm_append_comm
        exact ih (C_new ++ C_rot) R' hR'_len hperm' ⟨ec'.u, splice_circuits hCnew_at hCrot_at⟩
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil E hne
  obtain ⟨C0, R0, hperm0, hC0⟩ := extract_circuit hbal ⟨e0, he0, rfl⟩
  exact hgrow R0.length C0 R0 (Nat.le_refl _) hperm0 ⟨e0.u, hC0⟩

/-! ### Converting an Eulerian circuit / list of bags into a literal `Word n` -/

/-- Assemble a directed chain of edges into a literal word. -/
def wordOfChain {n : Nat} : List (RawEdge n) → Word n
  | [] => []
  | e :: rest => e.u ++ (e :: rest).flatMap (·.body)

theorem wordOfChain_length {n h : Nat} :
    ∀ (C : List (RawEdge n)), C ≠ [] → (∀ e ∈ C, EdgeOk h e) →
      (wordOfChain C).length = h + (C.map (fun e => e.body.length)).sum
  | [], hne, _ => absurd rfl hne
  | e :: rest, _, hok => by
    have he := hok e List.mem_cons_self
    simp [wordOfChain, List.length_append, he.1, List.length_flatMap]

theorem suffix_wordOfChain_of_chain {n h : Nat} :
    ∀ (C : List (RawEdge n)) (hne : C ≠ []),
      IsChainE C → (∀ e ∈ C, EdgeOk h e) →
      (C.getLast hne).v <:+ wordOfChain C ∧ ∀ e ∈ C, e.u ++ e.body <:+: wordOfChain C
  | [], hne, _, _ => absurd rfl hne
  | [e], _, _, hok => by
    have he := hok e List.mem_cons_self
    refine ⟨by simpa [wordOfChain] using he.2.2, fun e' he' => ?_⟩
    rw [List.mem_singleton.mp he']
    exact ⟨[], [], by simp [wordOfChain]⟩
  | e1 :: e2 :: rest, _, hch, hok => by
    have hok1 := hok e1 List.mem_cons_self
    have hok_rest : ∀ e ∈ e2 :: rest, EdgeOk h e := fun e he => hok e (List.mem_cons_of_mem _ he)
    obtain ⟨hsuf_rest, hinf_rest⟩ := suffix_wordOfChain_of_chain (e2 :: rest) (List.cons_ne_nil _ _) hch.2 hok_rest
    -- `e1.v = e2.u` is a suffix of `e1.u ++ e1.body`, so `e1.u ++ e1.body = pre ++ e2.u`!
    obtain ⟨pre, hpre⟩ := hch.1 ▸ hok1.2.2
    have hw_eq : wordOfChain (e1 :: e2 :: rest) = pre ++ wordOfChain (e2 :: rest) := by
      simp only [wordOfChain, List.flatMap_cons, ← List.append_assoc]
      rw [← hpre]
    refine ⟨?_, ?_⟩
    · rw [List.getLast_cons (List.cons_ne_nil _ _), hw_eq]
      exact hsuf_rest.trans (List.suffix_append _ _)
    · intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · refine ⟨[], (e2 :: rest).flatMap (·.body), ?_⟩
        simp [wordOfChain, List.append_assoc]
      · rw [hw_eq]
        obtain ⟨p, q, hpq⟩ := hinf_rest e he'
        exact ⟨pre ++ p, q, by rw [← hpq]; simp [List.append_assoc]⟩

/-- Every non-empty balanced, weakly-connected edge bag yields a single word of exact length
`h + ∑ e.body.length` containing `e.u ++ e.body` as an infix for every `e ∈ B`. -/
theorem word_of_eulerian_bag {n h : Nat} {B : List (RawEdge n)}
    (hne : B ≠ []) (hok : ∀ e ∈ B, EdgeOk h e) (hbal : Balanced B) (hconn : WeaklyConnected B) :
    ∃ w : Word n, w.length = h + (B.map (fun e => e.body.length)).sum ∧
      ∀ e ∈ B, e.u ++ e.body <:+: w := by
  obtain ⟨C, hperm, ⟨v0, hCne, hCch, _, _⟩⟩ := eulerian_circuit_exists hne hbal hconn
  have hCok : ∀ e ∈ C, EdgeOk h e := fun e he => hok e (hperm.mem_iff.mp he)
  refine ⟨wordOfChain C, ?_, ?_⟩
  · rw [wordOfChain_length C hCne hCok, (hperm.map (fun e => e.body.length)).sum_eq]
  · intro e he
    exact (suffix_wordOfChain_of_chain C hCne hCch hCok).2 e (hperm.mem_iff.mpr he)

/-- Concatenate words from a list of balanced, weakly-connected edge bags:
total length is `h * bags.length + ∑_{B ∈ bags} ∑_{e ∈ B} e.body.length`,
covering `e.u ++ e.body` for every edge `e` in every bag! -/
theorem word_of_bags {n h : Nat} :
    ∀ (bags : List (List (RawEdge n))),
      (∀ B ∈ bags, B ≠ [] ∧ (∀ e ∈ B, EdgeOk h e) ∧ Balanced B ∧ WeaklyConnected B) →
      ∃ w : Word n,
        w.length = h * bags.length + (bags.flatten.map (fun e => e.body.length)).sum ∧
        ∀ B ∈ bags, ∀ e ∈ B, e.u ++ e.body <:+: w
  | [], _ => ⟨[], by simp, fun _ hB => False.elim (List.not_mem_nil hB)⟩
  | B :: rest, hbags => by
    obtain ⟨hBne, hBok, hBbal, hBconn⟩ := hbags B List.mem_cons_self
    obtain ⟨w1, hw1_len, hw1_cov⟩ := word_of_eulerian_bag hBne hBok hBbal hBconn
    obtain ⟨w2, hw2_len, hw2_cov⟩ :=
      word_of_bags rest (fun B' hB' => hbags B' (List.mem_cons_of_mem _ hB'))
    refine ⟨w1 ++ w2, ?_, ?_⟩
    · rw [List.length_append, hw1_len, hw2_len, List.length_cons, List.flatten_cons,
        List.map_append, List.sum_append]
      ring
    · intro B' hB' e he
      rcases List.mem_cons.mp hB' with rfl | hB''
      · obtain ⟨p, q, hpq⟩ := hw1_cov e he
        exact ⟨p, q ++ w2, by rw [← List.append_assoc, hpq]⟩
      · obtain ⟨p, q, hpq⟩ := hw2_cov B' hB'' e he
        exact ⟨w1 ++ p, q, by rw [List.append_assoc, List.append_assoc, ← List.append_assoc p, hpq]⟩

end AsymptoticZero
