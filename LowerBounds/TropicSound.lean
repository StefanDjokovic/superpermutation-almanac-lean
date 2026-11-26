import LowerBounds.SBridgeTheoremC
import LowerBounds.SModel
import LowerBounds.SSound

/-!
# Pure-Kernel Soundness Bridge for `TropicCEGAR-Macro` Certificates

Proves `covers_length_ge_boundC_of_tropic`: any valid exact-integer `TropicCEGAR-Macro`
certificate (verified entirely by `decide +kernel` with zero `native_decide` and zero
Aho-Corasick theory inside Lean) implies `ModelStatement k cn bn q`, and therefore
`∀ w : List (Fin k), Covers w → boundC k cn bn q ≤ w.length`.
-/

namespace SuperpermLowerBounds
namespace Tropic

open Hunter PreimageChain SuperpermutationBounds S ChainC

/-! ### 1. Fast 16-way lookup tree & Option-Int potential helpers -/

/-- 16-way balanced lookup tree for O(log₁₆ V) kernel reduction (depth 4 covers 65,536 states). -/
inductive Tree16 (α : Type) where
  | leaf (v : α)
  | node (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : Tree16 α)

def Tree16.get {α : Type} : Nat → Tree16 α → Nat → α
  | _, .leaf v, _ => v
  | 0, .node c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, _ => Tree16.get 0 c0 0
  | d + 1, .node c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15, i =>
    let q := i / 16
    match i % 16 with
    | 0 => c0.get d q | 1 => c1.get d q | 2 => c2.get d q | 3 => c3.get d q
    | 4 => c4.get d q | 5 => c5.get d q | 6 => c6.get d q | 7 => c7.get d q
    | 8 => c8.get d q | 9 => c9.get d q | 10 => c10.get d q | 11 => c11.get d q
    | 12 => c12.get d q | 13 => c13.get d q | 14 => c14.get d q | _ => c15.get d q

/-- Check `p i = true` for all `lo ≤ i < hi`, chunked for shallow kernel recursion depth. -/
def checkRangeAux (lo : Nat) (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p (lo + n) && checkRangeAux lo p n

theorem checkRangeAux_spec {lo : Nat} {p : Nat → Bool} :
    ∀ {n : Nat}, checkRangeAux lo p n = true → ∀ i, lo ≤ i → i < lo + n → p i = true
  | 0, _, _, h1, h2 => by omega
  | n + 1, h, i, h1, h2 => by
    simp only [checkRangeAux, Bool.and_eq_true] at h
    by_cases heq : i = lo + n
    · rw [heq]; exact h.1
    · exact checkRangeAux_spec h.2 i h1 (by omega)

/-- Chunked range check (block size 64) to avoid kernel `maxRecDepth` on large ranges. -/
def checkRangeChunked (lo len : Nat) (p : Nat → Bool) : Bool :=
  let full := len / 64
  let rem := len % 64
  checkRangeAux 0 (fun b => checkRangeAux (lo + b * 64) p 64) full &&
    checkRangeAux (lo + full * 64) p rem

theorem checkRangeChunked_spec {lo len : Nat} {p : Nat → Bool}
    (h : checkRangeChunked lo len p = true) :
    ∀ i, lo ≤ i → i < lo + len → p i = true := by
  unfold checkRangeChunked at h
  simp only [Bool.and_eq_true] at h
  intro i h1 h2
  by_cases hlt : i < lo + (len / 64) * 64
  · let b := (i - lo) / 64
    have hb : b < len / 64 := by omega
    have hblk := checkRangeAux_spec h.1 b (Nat.zero_le _) (by omega)
    exact checkRangeAux_spec hblk i (by omega) (by omega)
  · exact checkRangeAux_spec h.2 i (by omega) (by omega)

/-- Potential ordering on `Option Int` (`none` = unreachable = `-∞`). -/
def oLe : Option Int → Option Int → Bool
  | none, _ => true
  | some _, none => false
  | some x, some y => decide (x ≤ y)

def oAdd : Option Int → Int → Option Int
  | none, _ => none
  | some x, w => some (x + w)

theorem oLe_some_of_le {x : Int} {o : Option Int} (h : oLe (some x) o = true) :
    ∃ y, o = some y ∧ x ≤ y := by
  cases o with
  | none => simp [oLe] at h
  | some y => exact ⟨y, rfl, by simpa [oLe] using h⟩

theorem oLe_trans_some {x : Int} {o1 o2 : Option Int}
    (h1 : oLe (some x) o1 = true) (h2 : oLe o1 o2 = true) : oLe (some x) o2 = true := by
  obtain ⟨y, rfl, hxy⟩ := oLe_some_of_le h1
  obtain ⟨z, rfl, hyz⟩ := oLe_some_of_le h2
  simpa [oLe] using le_trans hxy hyz

theorem oLe_add_of_le {x y w : Int} {o : Option Int} (hxy : x ≤ y)
    (h : oLe (oAdd (some y) w) o = true) : oLe (some (x + w)) o = true := by
  obtain ⟨z, rfl, hz⟩ := oLe_some_of_le h
  simpa [oLe] using (by omega : x + w ≤ z)

/-! ### 2. Exact `w3` transitions & collision verification against `SWord.lean` -/

/-- The 5 non-identity weight-3 seam successors of exit code `y` (matching `PM5` in `exp9`). -/
def w3Code (k y t : Nat) : Nat :=
  let base := (y % S.pw (k - 3)) * 4096
  let a := y / S.pw (k - 1)
  let b := (y / S.pw (k - 2)) % 16
  let c := (y / S.pw (k - 3)) % 16
  match t with
  | 0 => base + (a * 256 + c * 16 + b)
  | 1 => base + (b * 256 + a * 16 + c)
  | 2 => base + (b * 256 + c * 16 + a)
  | 3 => base + (c * 256 + a * 16 + b)
  | _ => base + (c * 256 + b * 16 + a)

/-- Every weight-3 seam between distinct-class permutation words corresponds to some `t < 5`. -/
theorem seam_w3Code {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) {u v : List Nat}
    (hu : S.PermW k u) (hv : S.PermW k v) (hlink : S.WLink k 3 u v) (hne : ¬ u ~r v) :
    ∃ t < 5, S.code v = w3Code k (S.exc k (S.code u)) t := by
  have hxp : S.PermW k (u.rotate (k - 1)) := hu.rotate _
  obtain ⟨a, b, c, Y, t0, t1, t2, hxe, hYl, hv2, ht0, ht1, ht2, h01, h02, h12⟩ :=
    S.seam_cases hk hxp hv hlink
  have hdu : ∀ z ∈ u, z < 16 := hu.lt16 hk15
  have hdx : ∀ z ∈ a :: b :: c :: Y, z < 16 := fun z hz => hxp.lt16 hk15 z (hxe ▸ hz)
  have hex : S.exc k (S.code u) = S.code (a :: b :: c :: Y) := by
    rw [S.exc_code k u hu.2.1 hdu (by omega), hxe]
  obtain ⟨hpY, hpa, hpb, hpc⟩ := S.six_parts k a b c Y hYl hdx hk
  rw [hex, hv2, S.code_append3]
  -- Eliminate identity (a, b, c): it gives v = u.rotate 2, contradicting hne!
  have hid : ¬ (t0 = a ∧ t1 = b ∧ t2 = c) := by
    rintro ⟨rfl, rfl, rfl⟩
    apply hne
    refine ⟨k - 1 + 3, ?_⟩
    rw [← List.rotate_rotate, hxe, hv2]
    simp [List.rotate_cons_succ]
  rcases ht0 with rfl | rfl | rfl <;>
  rcases ht1 with rfl | rfl | rfl <;>
  rcases ht2 with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl h01
    | exact absurd rfl h02
    | exact absurd rfl h12
    | exact absurd ⟨rfl, rfl, rfl⟩ hid
    | (first
        | (refine ⟨0, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []; done)
        | (refine ⟨1, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []; done)
        | (refine ⟨2, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []; done)
        | (refine ⟨3, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []; done)
        | (refine ⟨4, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []))

/-- Walk a single piece of length `L` starting at block code `cur`, inserting canonical class codes. -/
noncomputable def walkPieceC (k : Nat) : Nat → Nat → S.Tr → Bool × Nat × S.Tr
  | 0, cur, T => (false, cur, T)
  | 1, cur, T =>
    let cn := S.canon k cur
    if S.Tr.mem T cn then (true, cur, T) else (false, cur, S.Tr.ins T cn)
  | n + 2, cur, T =>
    let cn := S.canon k cur
    if S.Tr.mem T cn then (true, cur, T)
    else walkPieceC k (n + 1) (S.doorc k (S.exc k cur)) (S.Tr.ins T cn)

/-- Walk a piece-transition word `[(d_0, t_0), ...]` from `(cur, T)`. -/
noncomputable def walkWordC (k : Nat) : List (Nat × Nat) → Nat → S.Tr → Bool × Nat × S.Tr
  | [], cur, T => (false, cur, T)
  | (d, t) :: rest, cur, T =>
    let L := k - 1 - d
    let (col, endP, T') := walkPieceC k L cur T
    if col then (true, endP, T')
    else walkWordC k rest (w3Code k (S.exc k endP) t) T'

/-- True iff piece-word `w` plus the entry block of the next piece self-collides starting at `idc k`. -/
noncomputable def wordCollides (k : Nat) (w : List (Nat × Nat)) : Bool :=
  let (col, cur, T) := walkWordC k w (S.idc k) S.Tr.leaf
  col || S.Tr.mem T (S.canon k cur)

theorem walkWordC_append (k : Nat) (w1 w2 : List (Nat × Nat)) (cur : Nat) (T : S.Tr) :
    walkWordC k (w1 ++ w2) cur T =
      let (col1, cur1, T1) := walkWordC k w1 cur T
      if col1 then (true, cur1, T1) else walkWordC k w2 cur1 T1 := by
  induction w1 generalizing cur T with
  | nil => simp [walkWordC]
  | cons dt rest ih =>
    rcases dt with ⟨d, t⟩
    rw [List.cons_append]
    change (let (col1, endP, T') := walkPieceC k (k - 1 - d) cur T
      if col1 then (true, endP, T') else walkWordC k (rest ++ w2) (w3Code k (S.exc k endP) t) T') =
      (let (col1, cur1, T1) := (let (col1, endP, T') := walkPieceC k (k - 1 - d) cur T
        if col1 then (true, endP, T') else walkWordC k rest (w3Code k (S.exc k endP) t) T')
      if col1 then (true, cur1, T1) else walkWordC k w2 cur1 T1)
    rcases walkPieceC k (k - 1 - d) cur T with ⟨col1, endP, T1⟩
    cases col1 with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (w3Code k (S.exc k endP) t) T1

/-- Fast shared-prefix verifier for a group of length-2 colliding pairs sharing first word `w1`. -/
noncomputable def checkForb2Group (k : Nat) (w1 : List (Nat × Nat)) (w2s : List (List (Nat × Nat))) : Bool :=
  let (col1, cur1, T1) := walkWordC k w1 (S.idc k) S.Tr.leaf
  if col1 then true
  else w2s.all fun w2 =>
    let (col2, cur2, T2) := walkWordC k w2 cur1 T1
    col2 || S.Tr.mem T2 (S.canon k cur2)

theorem wordCollides_of_checkForb2Group {k : Nat} {w1 : List (Nat × Nat)}
    {w2s : List (List (Nat × Nat))} (h : checkForb2Group k w1 w2s = true) :
    ∀ w2 ∈ w2s, wordCollides k (w1 ++ w2) = true := by
  intro w2 hw2
  unfold checkForb2Group at h
  unfold wordCollides
  rw [walkWordC_append]
  cases h1 : walkWordC k w1 (S.idc k) S.Tr.leaf with
  | mk col1 r1 =>
    rcases r1 with ⟨cur1, T1⟩
    rw [h1] at h
    cases col1 with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact List.all_eq_true.mp h w2 hw2

/-! ### 3. Soundness of `wordCollides` on `S.IsWChain` -/

/-- Walk of a valid piece `P` never collides against `used` and preserves `TInv`. -/
theorem walkPieceC_valid {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) :
    ∀ (P : List (List Nat)) (hP : P ≠ []) (used : List (List Nat)) (T : S.Tr),
      (∀ w ∈ P, S.PermW k w) →
      List.IsChain (S.DoorEq k) P →
      List.Pairwise (fun u v => ¬ u ~r v) (used ++ P) →
      (∀ u ∈ used, S.PermW k u) →
      S.TInv k T used →
      ∃ T', walkPieceC k P.length (S.code (P.head hP)) T =
        (false, S.code (P.getLast hP), T') ∧ S.TInv k T' (used ++ P)
  | [], hP, _, _, _, _, _, _, _ => absurd rfl hP
  | [x], _, used, T, hperm, _, hpair, hup, hT => by
    have hx : S.PermW k x := hperm x List.mem_cons_self
    have hnew : ∀ u ∈ used, ¬ u ~r x := by
      intro u hu
      have := (List.pairwise_append.mp hpair).2.2 u hu x List.mem_cons_self
      exact this
    have hm : S.Tr.mem T (S.canon k (S.code x)) = false :=
      S.mem_false_of_new hk15 hT hup hx hnew
    refine ⟨S.Tr.ins T (S.canon k (S.code x)), ?_, S.tinv_ins hT x⟩
    simp [walkPieceC, hm]
  | x :: y :: rest, _, used, T, hperm, hdoor, hpair, hup, hT => by
    have hx : S.PermW k x := hperm x List.mem_cons_self
    have hnew : ∀ u ∈ used, ¬ u ~r x := fun u hu =>
      (List.pairwise_append.mp hpair).2.2 u hu x List.mem_cons_self
    have hm : S.Tr.mem T (S.canon k (S.code x)) = false :=
      S.mem_false_of_new hk15 hT hup hx hnew
    have hd : y = S.doorW (x.rotate (k - 1)) := (List.isChain_cons_cons.mp hdoor).1
    have hcode_y : S.code y = S.doorc k (S.exc k (S.code x)) := by
      rw [hd, S.exc_code k x hx.2.1 (hx.lt16 hk15) (by omega),
        S.doorc_code k (x.rotate (k - 1)) (by rw [List.length_rotate]; exact hx.2.1)
          (fun a ha => hx.lt16 hk15 a (List.mem_rotate.mp ha)) (by omega)]
    have hpair' : List.Pairwise (fun u v => ¬ u ~r v) ((used ++ [x]) ++ (y :: rest)) := by
      simpa [List.append_assoc] using hpair
    have hup' : ∀ u ∈ used ++ [x], S.PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h1 | h1
      · exact hup u h1
      · rw [List.mem_singleton.mp h1]; exact hx
    obtain ⟨T', hwalk, hT'⟩ := walkPieceC_valid hk hk15 (y :: rest) (List.cons_ne_nil _ _)
      (used ++ [x]) (S.Tr.ins T (S.canon k (S.code x)))
      (fun w hw => hperm w (List.mem_cons_of_mem _ hw))
      (List.isChain_cons_cons.mp hdoor).2 hpair' hup' (S.tinv_ins hT x)
    refine ⟨T', ?_, by simpa [List.append_assoc] using hT'⟩
    simp only [List.length_cons, walkPieceC, List.head_cons, hm, Bool.false_eq_true, ↓reduceIte,
      ← hcode_y, List.getLast_cons_cons]
    exact hwalk

/-- A sequence of pieces matching `w = [(d_0, t_0), ...]` followed by next piece `Q`. -/
def MatchesWord (k : Nat) : List (Nat × Nat) → List (List (List Nat)) → Prop
  | [], Q :: _ => Q ≠ []
  | [], [] => False
  | (d, t) :: rest, P :: Q :: tail =>
    ∃ (hP : P ≠ []) (hQ : Q ≠ []),
      k - 1 - P.length = d ∧
      S.code (Q.head hQ) = w3Code k (S.exc k (S.code (P.getLast hP))) t ∧
      MatchesWord k rest (Q :: tail)
  | _ :: _, _ => False

theorem walkWordC_valid {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) :
    ∀ (w : List (Nat × Nat)) (L : List (List (List Nat))) (used : List (List Nat)) (T : S.Tr)
      (hL : L ≠ []) (hhead : L.head hL ≠ []),
      S.IsWChain k L →
      MatchesWord k w L →
      List.Pairwise (fun u v => ¬ u ~r v) (used ++ L.flatten) →
      (∀ u ∈ used, S.PermW k u) →
      S.TInv k T used →
      (let (col, cur, T') := walkWordC k w (S.code ((L.head hL).head hhead)) T
       col || S.Tr.mem T' (S.canon k cur)) = false
  | [], Q :: tail, used, T, _, hhead, hchain, _, hpair, hup, hT => by
    simp only [walkWordC, List.head_cons, Bool.false_or]
    have hq : S.PermW k (Q.head hhead) :=
      hchain.words Q List.mem_cons_self _ (List.head_mem hhead)
    have hmem_flat : Q.head hhead ∈ (Q :: tail).flatten :=
      List.mem_flatten.mpr ⟨Q, List.mem_cons_self, List.head_mem hhead⟩
    have hnew : ∀ u ∈ used, ¬ u ~r Q.head hhead := fun u hu =>
      (List.pairwise_append.mp hpair).2.2 u hu _ hmem_flat
    exact S.mem_false_of_new hk15 hT hup hq hnew
  | [], [], _, _, hL, _, _, _, _, _, _ => absurd rfl hL
  | (d, t) :: rest, P :: Q :: tail, used, T, _, hhead, hchain, hmatch, hpair, hup, hT => by
    obtain ⟨hP, hQ, hd, hcodeQ, hmatch'⟩ := hmatch
    have hPle : P.length ≤ k - 1 := hchain.size_le P List.mem_cons_self
    have hL_eq : k - 1 - d = P.length := by omega
    have hpairP : List.Pairwise (fun u v => ¬ u ~r v) (used ++ P) := by
      have hs : List.Sublist (used ++ P) (used ++ (P :: Q :: tail).flatten) := by
        rw [List.flatten_cons]
        exact List.Sublist.append_left (List.sublist_append_left P _) _
      exact hpair.sublist hs
    have hPpair : List.Pairwise (fun u v => ¬ u ~r v) P :=
      (List.pairwise_append.mp hpairP).2.1
    have hdoorP : List.IsChain (S.DoorEq k) P :=
      S.door_chain hk P (hchain.words P List.mem_cons_self)
        (hchain.doors P List.mem_cons_self) hPpair
    obtain ⟨T1, hwp, hT1⟩ := walkPieceC_valid hk hk15 P hP used T
      (hchain.words P List.mem_cons_self) hdoorP hpairP hup hT
    have hchain' : S.IsWChain k (Q :: tail) :=
      hchain.infix ⟨[P], [], by simp⟩
    have hpair' : List.Pairwise (fun u v => ¬ u ~r v) ((used ++ P) ++ (Q :: tail).flatten) := by
      simpa [List.flatten_cons, List.append_assoc] using hpair
    have hup' : ∀ u ∈ used ++ P, S.PermW k u := by
      intro u hu
      rcases List.mem_append.mp hu with h1 | h1
      · exact hup u h1
      · exact hchain.words P List.mem_cons_self u h1
    have ih := walkWordC_valid hk hk15 rest (Q :: tail) (used ++ P) T1
      (List.cons_ne_nil _ _) hQ hchain' hmatch' hpair' hup' hT1
    simp only [walkWordC, List.head_cons, hL_eq, hwp, Bool.false_eq_true, ↓reduceIte, ← hcodeQ]
    exact ih
  | _ :: _, [], _, _, hL, _, _, _, _, _, _ => absurd rfl hL
  | _ :: _, [_], _, _, _, _, _, hmatch, _, _, _ => False.elim hmatch

/-- Relabelling preserves `MatchesWord` when `w3Code` matches `t` (via `S.relab`). -/
theorem matchesWord_relabel {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) {e : List Nat}
    (he : S.PermW k e) :
    ∀ (w : List (Nat × Nat)) (L : List (List (List Nat))),
      S.IsWChain k L → MatchesWord k w L → MatchesWord k w (S.relabChain e L)
  | [], Q :: tail, _, hne => by
    simp only [MatchesWord, S.relabChain, List.map_cons, ne_eq, List.map_eq_nil_iff]
    exact hne
  | [], [], _, h => False.elim h
  | (d, t) :: rest, P :: Q :: tail, hchain, hmatch => by
    obtain ⟨hP, hQ, hd, hcodeQ, hmatch'⟩ := hmatch
    have hP' : P.map (List.map (S.relab e)) ≠ [] := by simpa using hP
    have hQ' : Q.map (List.map (S.relab e)) ≠ [] := by simpa using hQ
    refine ⟨hP', hQ', by simpa using hd, ?_,
      matchesWord_relabel hk hk15 he rest (Q :: tail) (hchain.infix ⟨[P], [], by simp⟩) hmatch'⟩
    -- Show w3 transition index t is preserved under symbol relabelling!
    have hu : S.PermW k (P.getLast hP) := hchain.words P List.mem_cons_self _ (List.getLast_mem hP)
    have hv : S.PermW k (Q.head hQ) := hchain.words Q (by simp) _ (List.head_mem hQ)
    have hlink : S.WLink k 3 (P.getLast hP) (Q.head hQ) :=
      (List.isChain_cons_cons.mp hchain.seams).1 hP hQ
    have hxp : S.PermW k ((P.getLast hP).rotate (k - 1)) := hu.rotate _
    obtain ⟨a, b, c, Y, t0, t1, t2, hxe, hYl, hv2, ht0, ht1, ht2, h01, h02, h12⟩ :=
      S.seam_cases hk hxp hv hlink
    -- Relabelled exit & entry
    have hdu := hu.lt16 hk15
    have hdx : ∀ z ∈ a :: b :: c :: Y, z < 16 := fun z hz => hxp.lt16 hk15 z (hxe ▸ hz)
    have hex : S.exc k (S.code (P.getLast hP)) = S.code (a :: b :: c :: Y) := by
      rw [S.exc_code k _ hu.2.1 hdu (by omega), hxe]
    obtain ⟨hpY, hpa, hpb, hpc⟩ := S.six_parts k a b c Y hYl hdx hk
    let f := S.relab e
    have huf : S.PermW k ((P.getLast hP).map f) := he.map_relab hu
    have hvf : S.PermW k ((Q.head hQ).map f) := he.map_relab hv
    have hxpf : S.PermW k (((P.getLast hP).map f).rotate (k - 1)) := huf.rotate _
    have hxef : ((P.getLast hP).map f).rotate (k - 1) = f a :: f b :: f c :: Y.map f := by
      rw [← List.map_rotate, hxe]; simp
    have hYlf : (Y.map f).length = k - 3 := by rw [List.length_map]; exact hYl
    have hdxf : ∀ z ∈ f a :: f b :: f c :: Y.map f, z < 16 :=
      fun z hz => hxpf.lt16 hk15 z (hxef ▸ hz)
    have hexf : S.exc k (S.code ((P.getLast hP).map f)) = S.code (f a :: f b :: f c :: Y.map f) := by
      rw [S.exc_code k _ huf.2.1 (huf.lt16 hk15) (by omega), hxef]
    obtain ⟨hpYf, hpaf, hpbf, hpcf⟩ := S.six_parts k (f a) (f b) (f c) (Y.map f) hYlf hdxf hk
    have hv2f : (Q.head hQ).map f = Y.map f ++ [f t0, f t1, f t2] := by rw [hv2]; simp
    -- Deduce exact triple (t0, t1, t2) from hcodeQ, then evaluate both sides!
    have hbase_lt : ∀ p q r, p < 16 → q < 16 → r < 16 → p * 256 + q * 16 + r < 4096 := by
      intro p q r hp hq hr; omega
    have ha16 : a < 16 := hdx a (by simp)
    have hb16 : b < 16 := hdx b (by simp)
    have hc16 : c < 16 := hdx c (by simp)
    have hmod_eq : ∀ p1 q1 r1 p2 q2 r2, p1 < 16 → q1 < 16 → r1 < 16 →
        p2 < 16 → q2 < 16 → r2 < 16 →
        S.code Y * 4096 + (p1 * 256 + q1 * 16 + r1) = S.code Y * 4096 + (p2 * 256 + q2 * 16 + r2) →
        p1 = p2 ∧ q1 = q2 ∧ r1 = r2 := by
      intro p1 q1 r1 p2 q2 r2 hp1 hq1 hr1 hp2 hq2 hr2 heq
      have hsub : p1 * 256 + q1 * 16 + r1 = p2 * 256 + q2 * 16 + r2 := Nat.add_left_cancel heq
      omega
    rw [hex, hv2, S.code_append3] at hcodeQ
    rw [List.head_map, List.getLast_map, hexf, hv2f, S.code_append3]
    have ht0_16 : t0 < 16 := hv.lt16 hk15 t0 (by rw [hv2]; simp)
    have ht1_16 : t1 < 16 := hv.lt16 hk15 t1 (by rw [hv2]; simp)
    have ht2_16 : t2 < 16 := hv.lt16 hk15 t2 (by rw [hv2]; simp)
    match t, hcodeQ with
    | 0, hq =>
      dsimp only [w3Code] at hq ⊢; rw [hpY, hpa, hpb, hpc] at hq; rw [hpYf, hpaf, hpbf, hpcf]
      obtain ⟨rfl, rfl, rfl⟩ := hmod_eq t0 t1 t2 a c b ht0_16 ht1_16 ht2_16 ha16 hc16 hb16 hq; rfl
    | 1, hq =>
      dsimp only [w3Code] at hq ⊢; rw [hpY, hpa, hpb, hpc] at hq; rw [hpYf, hpaf, hpbf, hpcf]
      obtain ⟨rfl, rfl, rfl⟩ := hmod_eq t0 t1 t2 b a c ht0_16 ht1_16 ht2_16 hb16 ha16 hc16 hq; rfl
    | 2, hq =>
      dsimp only [w3Code] at hq ⊢; rw [hpY, hpa, hpb, hpc] at hq; rw [hpYf, hpaf, hpbf, hpcf]
      obtain ⟨rfl, rfl, rfl⟩ := hmod_eq t0 t1 t2 b c a ht0_16 ht1_16 ht2_16 hb16 hc16 ha16 hq; rfl
    | 3, hq =>
      dsimp only [w3Code] at hq ⊢; rw [hpY, hpa, hpb, hpc] at hq; rw [hpYf, hpaf, hpbf, hpcf]
      obtain ⟨rfl, rfl, rfl⟩ := hmod_eq t0 t1 t2 c a b ht0_16 ht1_16 ht2_16 hc16 ha16 hb16 hq; rfl
    | _ + 4, hq =>
      dsimp only [w3Code] at hq ⊢; rw [hpY, hpa, hpb, hpc] at hq; rw [hpYf, hpaf, hpbf, hpcf]
      obtain ⟨rfl, rfl, rfl⟩ := hmod_eq t0 t1 t2 c b a ht0_16 ht1_16 ht2_16 hc16 hb16 ha16 hq; rfl
  | _ :: _, [], _, h => False.elim h
  | _ :: _, [_], _, h => False.elim h

/-- **Main Collision Soundness Lemma:** If `wordCollides k w = true`, NO valid `IsWChain` can match `w`! -/
theorem not_matchesWord_of_wordCollides {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {w : List (Nat × Nat)} (hcol : wordCollides k w = true)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) (hmatch : MatchesWord k w L) : False := by
  have hL : L ≠ [] := by
    cases L with
    | nil => cases w <;> exact False.elim hmatch
    | cons _ _ => exact List.cons_ne_nil _ _
  have hhead : L.head hL ≠ [] := hchain.pieces_ne _ (List.head_mem hL)
  let e := (L.head hL).head hhead
  have he : S.PermW k e := hchain.words _ (List.head_mem hL) e (List.head_mem hhead)
  let L' := S.relabChain e L
  have hchain' : S.IsWChain k L' := hchain.relabel he
  have hmatch' : MatchesWord k w L' := matchesWord_relabel hk hk15 he w L hchain hmatch
  have hL' : L' ≠ [] := by simp [L', S.relabChain, hL]
  have hhead' : L'.head hL' ≠ [] := hchain'.pieces_ne _ (List.head_mem hL')
  have hcode_id : S.code ((L'.head hL').head hhead') = S.idc k := by
    have h1 : (L'.head hL').head hhead' = e.map (S.relab e) := by
      cases L with
      | nil => exact absurd rfl hL
      | cons P tail =>
        cases P with
        | nil => exact absurd rfl hhead
        | cons x xs => rfl
    rw [h1, S.map_relab_self he.1, he.2.1, ← S.idc_code]
  have hfalse := walkWordC_valid hk hk15 w L' [] S.Tr.leaf hL' hhead' hchain' hmatch'
    (by simpa using hchain'.classes) (by simp) (S.tinv_leaf k [])
  rw [hcode_id] at hfalse
  unfold wordCollides at hcol
  rw [hcol] at hfalse
  exact absurd hfalse (by decide)

/-! ### 4. Extracting the transition sequence `(d_i, t_i)` of any valid `IsWChain` -/

theorem matchesWord_prefix {k : Nat} :
    ∀ (w1 w2 : List (Nat × Nat)) (L : List (List (List Nat))),
      MatchesWord k (w1 ++ w2) L → MatchesWord k w1 L
  | [], [], Q :: _, h => h
  | [], _ :: _, Q :: _ :: _, h => h.1
  | [], _ :: _, [_], h => False.elim h
  | [], [], [], h => False.elim h
  | [], _ :: _, [], h => False.elim h
  | (d, t) :: rest, w2, P :: Q :: tail, h => by
    obtain ⟨hP, hQ, hd, hcode, hrest⟩ := h
    exact ⟨hP, hQ, hd, hcode, matchesWord_prefix rest w2 (Q :: tail) hrest⟩
  | _ :: _, _, [], h => False.elim h
  | _ :: _, _, [_], h => False.elim h

theorem matchesWord_drop {k : Nat} :
    ∀ (w1 w2 : List (Nat × Nat)) (L : List (List (List Nat))),
      MatchesWord k (w1 ++ w2) L → MatchesWord k w2 (L.drop w1.length)
  | [], _, L, h => by simpa using h
  | (d, t) :: rest, w2, P :: Q :: tail, h => by
    obtain ⟨_, _, _, _, hrest⟩ := h
    simpa [List.length_cons, List.drop_succ_cons] using matchesWord_drop rest w2 (Q :: tail) hrest
  | _ :: _, _, [], h => False.elim h
  | _ :: _, _, [_], h => False.elim h

theorem drop_infix {α : Type} (n : Nat) (L : List α) : L.drop n <:+: L :=
  ⟨L.take n, [], by simp⟩

/-- Every non-empty valid `IsWChain k L` yields `ts : List (Nat × Nat)` + final deficit `d_last`
matching `L`, with `wdef k L = ts.map Prod.fst ++ [d_last]` and `MatchesWord k ts L`. -/
theorem extract_transitions {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) :
    ∀ (L : List (List (List Nat))), L ≠ [] → S.IsWChain k L →
      ∃ (ts : List (Nat × Nat)) (d_last : Nat),
        S.wdef k L = ts.map Prod.fst ++ [d_last] ∧
        (∀ dt ∈ ts, dt.2 < 5) ∧
        MatchesWord k ts L
  | [], hne, _ => absurd rfl hne
  | [P], _, hchain =>
    ⟨[], k - 1 - P.length, by simp [S.wdef], by simp, hchain.pieces_ne P List.mem_cons_self⟩
  | P :: Q :: tail, _, hchain => by
    have hP : P ≠ [] := hchain.pieces_ne P List.mem_cons_self
    have hQ : Q ≠ [] := hchain.pieces_ne Q (by simp)
    have hchain' : S.IsWChain k (Q :: tail) := hchain.infix ⟨[P], [], by simp⟩
    obtain ⟨ts', d_last, hwdef', ht5', hmatch'⟩ :=
      extract_transitions hk hk15 (Q :: tail) (List.cons_ne_nil _ _) hchain'
    have hu : S.PermW k (P.getLast hP) := hchain.words P List.mem_cons_self _ (List.getLast_mem hP)
    have hv : S.PermW k (Q.head hQ) := hchain.words Q (by simp) _ (List.head_mem hQ)
    have hlink : S.WLink k 3 (P.getLast hP) (Q.head hQ) :=
      (List.isChain_cons_cons.mp hchain.seams).1 hP hQ
    have hne_uv : ¬ P.getLast hP ~r Q.head hQ := by
      have hp := hchain.classes
      rw [List.flatten_cons, List.pairwise_append] at hp
      exact hp.2.2 _ (List.getLast_mem hP) _
        (List.mem_flatten.mpr ⟨Q, List.mem_cons_self, List.head_mem hQ⟩)
    obtain ⟨t, ht5, hcodeQ⟩ := seam_w3Code hk hk15 hu hv hlink hne_uv
    refine ⟨(k - 1 - P.length, t) :: ts', d_last, ?_, ?_, ⟨hP, hQ, rfl, hcodeQ, hmatch'⟩⟩
    · simp only [S.wdef, List.map_cons, List.cons_append] at hwdef' ⊢
      exact congrArg (List.cons (k - 1 - P.length)) hwdef'
    · intro dt hdt
      rcases List.mem_cons.mp hdt with rfl | hdt'
      · exact ht5
      · exact ht5' dt hdt'

/-- No colliding piece-word can appear as a contiguous subword of `ts`. -/
theorem not_infix_of_wordCollides {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) {w : List (Nat × Nat)} (hcol : wordCollides k w = true)
    (hinf : w <:+: ts) : False := by
  obtain ⟨pre, post, rfl⟩ := hinf
  have h1 : MatchesWord k (w ++ post) (L.drop pre.length) := by
    rw [List.append_assoc] at hmatch
    exact matchesWord_drop pre (w ++ post) L hmatch
  have h2 : MatchesWord k w (L.drop pre.length) := matchesWord_prefix w post _ h1
  exact not_matchesWord_of_wordCollides hk hk15 hcol (hchain.infix (drop_infix pre.length L)) h2

/-! ### 4b. O(1)-per-piece Two-Point Collision Witness (`checkWitness`) -/

/-- Advance `r` door-steps inside a single piece of length `≤ k - 1` in `O(1)` via `rotl (k - 1)`. -/
def pieceAdvance (k r c : Nat) : Nat :=
  S.rotl (k - 1) (c / 16) r * 16 + c % 16

theorem pieceAdvance_code {k : Nat} (hk : 2 ≤ k) {pre : List Nat} {last : Nat}
    (hpre : pre.length = k - 1) (hd : ∀ a ∈ pre, a < 16) (hlast : last < 16)
    {r : Nat} (hr : r ≤ k - 1) :
    pieceAdvance k r (S.code (pre ++ [last])) = S.code (pre.rotate r ++ [last]) := by
  have hc : S.code (pre ++ [last]) = S.code pre * 16 + last := by
    rw [S.code_append, S.code_singleton, List.length_singleton, pow_one]
  have hdiv : (S.code pre * 16 + last) / 16 = S.code pre := by omega
  have hmod : (S.code pre * 16 + last) % 16 = last := by omega
  unfold pieceAdvance
  rw [hc, hdiv, hmod, S.rotl_code (k - 1) pre hpre hd r hr, S.code_append, S.code_singleton,
    List.length_singleton, pow_one]

theorem doorW_rot_last {k : Nat} (hk : 2 ≤ k) {pre : List Nat} {last : Nat}
    (hpre : pre.length = k - 1) :
    S.doorW ((pre ++ [last]).rotate (k - 1)) = pre.rotate 1 ++ [last] := by
  have hrot : (pre ++ [last]).rotate (k - 1) = last :: pre := by
    rw [← hpre, List.rotate_append_length_eq]; rfl
  rw [hrot]
  cases pre with
  | nil => simp at hpre; omega
  | cons a rest =>
    rw [S.doorW_cons]
    simp [List.rotate_cons_succ, List.append_assoc]

theorem piece_getElem_rot {k : Nat} (hk : 2 ≤ k) :
    ∀ (P : List (List Nat)) (pre : List Nat) (last : Nat),
      pre.length = k - 1 →
      List.IsChain (S.DoorEq k) P →
      (h0 : 0 < P.length) →
      P[0] = pre ++ [last] →
      ∀ (j : Nat) (hj : j < P.length), P[j] = pre.rotate j ++ [last] := by
  intro P pre last hpre hdoor h0 hp0 j
  induction j with
  | zero => intro _; simpa using hp0
  | succ j ih =>
    intro hj
    have hj' : j < P.length := by omega
    have hstep : S.DoorEq k P[j] P[j + 1] := (List.isChain_iff_getElem.mp hdoor) j hj
    unfold S.DoorEq at hstep
    rw [hstep, ih hj']
    have hrotlen : (pre.rotate j).length = k - 1 := by rw [List.length_rotate, hpre]
    rw [doorW_rot_last hk hrotlen, List.rotate_rotate]

theorem piece_getElem_code {k : Nat} (hk : 2 ≤ k) (hk15 : k ≤ 15)
    {P : List (List Nat)} (hP : P ≠ []) (hperm : ∀ w ∈ P, S.PermW k w)
    (hdoor : List.IsChain (S.DoorEq k) P) (hPle : P.length ≤ k - 1)
    {j : Nat} (hj : j < P.length) :
    S.code P[j] = pieceAdvance k j (S.code (P.head hP)) := by
  have h0 : 0 < P.length := List.length_pos_of_ne_nil hP
  have hp0_perm : S.PermW k P[0] := hperm P[0] (List.getElem_mem h0)
  have hp0_ne : P[0] ≠ [] := by intro hnil; have := hp0_perm.2.1; rw [hnil] at this; simp at this; omega
  let pre := P[0].dropLast
  let last := P[0].getLast hp0_ne
  have hp0_eq : P[0] = pre ++ [last] := (List.dropLast_append_getLast hp0_ne).symm
  have hpre_len : pre.length = k - 1 := by
    have := congrArg List.length hp0_eq; rw [hp0_perm.2.1] at this; simp at this; omega
  have hhd : ∀ a ∈ pre, a < 16 := fun a ha =>
    hp0_perm.lt16 hk15 a (by rw [hp0_eq]; exact List.mem_append_left _ ha)
  have hlast16 : last < 16 := hp0_perm.lt16 hk15 last (by rw [hp0_eq]; simp)
  have hrot := piece_getElem_rot hk P pre last hpre_len hdoor h0 hp0_eq j hj
  have hhead : P.head hP = P[0] := List.head_eq_getElem_zero hP
  rw [hrot, hhead, hp0_eq, pieceAdvance_code hk hpre_len hhd hlast16 (by omega)]

/-- Fast `O(|w|)` word walk computing the entry code of piece `w.length` with zero `Tr` or `canon`. -/
def walkWordFast (k : Nat) : List (Nat × Nat) → Nat → Nat
  | [], cur => cur
  | (d, t) :: rest, cur =>
    let endP := pieceAdvance k (k - 2 - d) cur
    walkWordFast k rest (w3Code k (S.exc k endP) t)

theorem walkWordFast_append (k : Nat) (w1 w2 : List (Nat × Nat)) (cur : Nat) :
    walkWordFast k (w1 ++ w2) cur = walkWordFast k w2 (walkWordFast k w1 cur) := by
  induction w1 generalizing cur with
  | nil => rfl
  | cons dt rest ih =>
    rcases dt with ⟨d, t⟩
    exact ih _

theorem walkWordFast_valid {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15) :
    ∀ (w : List (Nat × Nat)) (L : List (List (List Nat))),
      S.IsWChain k L → MatchesWord k w L →
      ∃ (hw : w.length < L.length) (h0 : 0 < L.length)
        (hPw : L[w.length] ≠ []) (hP0 : L[0] ≠ []),
        S.code (L[w.length].head hPw) = walkWordFast k w (S.code (L[0].head hP0))
  | [], [], _, hmatch => False.elim hmatch
  | [], Q :: tail, _, hmatch => ⟨by simp, by simp, hmatch, hmatch, rfl⟩
  | (d, t) :: rest, [], _, hmatch => False.elim hmatch
  | (d, t) :: rest, [_], _, hmatch => False.elim hmatch
  | (d, t) :: rest, P :: Q :: tail, hchain, hmatch => by
    obtain ⟨hP, hQ, hlenP, hcodeQ, hrest⟩ := hmatch
    have hchain' : S.IsWChain k (Q :: tail) := hchain.infix ⟨[P], [], by simp⟩
    obtain ⟨hw', h0', hPw', hP0', hcode_end⟩ := walkWordFast_valid hk hk15 rest (Q :: tail) hchain' hrest
    have hP_pos : 0 < P.length := List.length_pos_of_ne_nil hP
    have hP_le : P.length ≤ k - 1 := hchain.size_le P List.mem_cons_self
    have hpermP : ∀ w ∈ P, S.PermW k w := hchain.words P List.mem_cons_self
    have hclP : List.Pairwise (fun a b => ¬ a ~r b) P := by
      have hp := hchain.classes
      rw [List.flatten_cons, List.pairwise_append] at hp
      exact hp.1
    have hdoorP : List.IsChain (S.DoorEq k) P :=
      S.door_chain hk P hpermP (hchain.doors P List.mem_cons_self) hclP
    have hlast_eq : P.getLast hP = P[k - 2 - d]'(by omega) := by
      rw [List.getLast_eq_getElem]
      congr 1; omega
    have hlast_code : S.code (P.getLast hP) = pieceAdvance k (k - 2 - d) (S.code (P.head hP)) := by
      rw [hlast_eq]
      exact piece_getElem_code (by omega) hk15 hP hpermP hdoorP hP_le (by omega)
    refine ⟨by simp only [List.length_cons] at hw' ⊢; omega, by simp, hPw', hP, ?_⟩
    simpa [walkWordFast, hcodeQ, hlast_code] using hcode_end

theorem matchesWord_piece_len {k : Nat} :
    ∀ (w : List (Nat × Nat)) (L : List (List (List Nat))) (i : Nat),
      S.IsWChain k L → MatchesWord k w L → (hi : i < w.length) →
      ∃ (hL : i < L.length), L[i].length = k - 1 - (w.getD i (0, 0)).1
  | [], _, _, _, _, hi => by simp at hi
  | (d, t) :: rest, P :: Q :: tail, 0, hchain, hmatch, _ => by
    have hle := hchain.size_le P List.mem_cons_self
    have hd := hmatch.2.2.1
    exact ⟨by simp, by simp only [List.getElem_cons_zero, List.getD_cons_zero]; omega⟩
  | (d, t) :: rest, P :: Q :: tail, i + 1, hchain, hmatch, hi => by
    have hchain' : S.IsWChain k (Q :: tail) := hchain.infix ⟨[P], [], by simp⟩
    obtain ⟨hL', hlen'⟩ := matchesWord_piece_len rest (Q :: tail) i hchain' hmatch.2.2.2.2 (by simp at hi; omega)
    exact ⟨by simp only [List.length_cons] at hL' ⊢; omega, by simpa using hlen'⟩
  | _ :: _, [], _, _, hmatch, _ => False.elim hmatch
  | _ :: _, [_], _, _, hmatch, _ => False.elim hmatch

/-- Pure-kernel `O(i2)` two-point collision witness verifier (zero `Tr`, 2 `canon` calls!). -/
noncomputable def checkWitness (k : Nat) (w : List (Nat × Nat)) (wit : Nat × Nat × Nat × Nat) : Bool :=
  let (i1, j1, i2, j2) := wit
  if !(decide (i1 < i2) && decide (i2 ≤ w.length)) then false
  else
    let ok1 := decide (j1 < k - 1 - (w.getD i1 (0, 0)).1)
    let ok2 :=
      if i2 < w.length then decide (j2 < k - 1 - (w.getD i2 (0, 0)).1)
      else decide (j2 = 0)
    if !(ok1 && ok2) then false
    else
      let e1 := walkWordFast k (w.take i1) (S.idc k)
      let c1 := pieceAdvance k j1 e1
      let e2 := walkWordFast k ((w.drop i1).take (i2 - i1)) e1
      let c2 := pieceAdvance k j2 e2
      S.canon k c1 == S.canon k c2

theorem pairwise_flatten_distinct_pieces {α : Type} {R : α → α → Prop}
    {L : List (List α)} (hpw : List.Pairwise R L.flatten)
    {i1 i2 : Nat} (hlt : i1 < i2) (hi2 : i2 < L.length)
    {x y : α} (hx : x ∈ L[i1]'(by omega)) (hy : y ∈ L[i2]) : R x y := by
  have hsplit : L = L.take i1 ++ [L[i1]'(by omega)] ++
      ((L.drop (i1 + 1)).take (i2 - i1 - 1) ++ [L[i2]] ++ L.drop (i2 + 1)) := by
    have h1 : L = L.take i1 ++ L.drop i1 := (List.take_append_drop i1 L).symm
    have h2 : L.drop i1 = L[i1]'(by omega) :: L.drop (i1 + 1) := List.drop_eq_getElem_cons (by omega)
    have hlen_d : i2 - i1 - 1 < (L.drop (i1 + 1)).length := by simp; omega
    have h3 : L.drop (i1 + 1) = (L.drop (i1 + 1)).take (i2 - i1 - 1) ++ (L.drop (i1 + 1)).drop (i2 - i1 - 1) :=
      (List.take_append_drop _ _).symm
    have h4 : (L.drop (i1 + 1)).drop (i2 - i1 - 1) = L.drop i2 := by
      rw [List.drop_drop]; congr 1; omega
    have h5 : L.drop i2 = L[i2] :: L.drop (i2 + 1) := List.drop_eq_getElem_cons hi2
    conv_lhs => rw [h1, h2, h3, h4, h5]
    simp only [List.append_assoc, List.singleton_append]
  rw [hsplit] at hpw
  simp only [List.flatten_append, List.flatten_singleton, List.pairwise_append] at hpw
  have hx_mem : x ∈ L[i1]'(by omega) := hx
  have hy_mem : y ∈ ((L.drop (i1 + 1)).take (i2 - i1 - 1)).flatten ++ L[i2] ++ (L.drop (i2 + 1)).flatten :=
    List.mem_append_left _ (List.mem_append_right _ hy)
  exact hpw.2.2 x (List.mem_append_right _ hx_mem) y hy_mem

theorem not_matchesWord_of_checkWitness {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {w : List (Nat × Nat)} {wit : Nat × Nat × Nat × Nat} (hwit : checkWitness k w wit = true)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) (hmatch : MatchesWord k w L) : False := by
  rcases wit with ⟨i1, j1, i2, j2⟩
  unfold checkWitness at hwit
  by_cases hrange : i1 < i2 ∧ i2 ≤ w.length
  · have hrb : (decide (i1 < i2) && decide (i2 ≤ w.length)) = true := by simp [hrange]
    simp only [hrb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwit
    have hok12 : (decide (j1 < k - 1 - (w.getD i1 (0, 0)).1) &&
        (if i2 < w.length then decide (j2 < k - 1 - (w.getD i2 (0, 0)).1) else decide (j2 = 0))) = true := by
      cases hok : (decide (j1 < k - 1 - (w.getD i1 (0, 0)).1) &&
          (if i2 < w.length then decide (j2 < k - 1 - (w.getD i2 (0, 0)).1) else decide (j2 = 0))) with
      | true => rfl
      | false =>
        change (if !((decide (j1 < k - 1 - (w.getD i1 (0, 0)).1) &&
          (if i2 < w.length then decide (j2 < k - 1 - (w.getD i2 (0, 0)).1) else decide (j2 = 0)))) = true then false else _) = true at hwit
        rw [hok] at hwit; cases hwit
    simp only [hok12, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hwit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok12
    -- Relabel L so L'[0][0] has code S.idc k!
    have hL : L ≠ [] := by
      cases L with
      | nil => cases w <;> exact False.elim hmatch
      | cons _ _ => exact List.cons_ne_nil _ _
    have hhead : L.head hL ≠ [] := hchain.pieces_ne _ (List.head_mem hL)
    let e := (L.head hL).head hhead
    have he : S.PermW k e := hchain.words _ (List.head_mem hL) e (List.head_mem hhead)
    let L' := S.relabChain e L
    have hchain' : S.IsWChain k L' := hchain.relabel he
    have hmatch' : MatchesWord k w L' := matchesWord_relabel hk hk15 he w L hchain hmatch
    have hL' : L' ≠ [] := by simp [L', S.relabChain, hL]
    have hhead' : L'.head hL' ≠ [] := hchain'.pieces_ne _ (List.head_mem hL')
    have hcode_id : S.code ((L'.head hL').head hhead') = S.idc k := by
      have h1 : (L'.head hL').head hhead' = e.map (S.relab e) := by
        cases L with
        | nil => exact absurd rfl hL
        | cons P tail =>
          cases P with
          | nil => exact absurd rfl hhead
          | cons x xs => rfl
      rw [h1, S.map_relab_self he.1, he.2.1, ← S.idc_code]
    -- Apply walkWordFast_valid to w.take i1 and w.take i2!
    have hm1 : MatchesWord k (w.take i1) L' :=
      matchesWord_prefix (w.take i1) (w.drop i1) L' (by simpa using hmatch')
    have hm2 : MatchesWord k (w.take i2) L' :=
      matchesWord_prefix (w.take i2) (w.drop i2) L' (by simpa using hmatch')
    obtain ⟨hw1, h0', hP1, hP0, hc1_hd⟩ := walkWordFast_valid hk hk15 (w.take i1) L' hchain' hm1
    obtain ⟨hw2, _, hP2, _, hc2_hd⟩ := walkWordFast_valid hk hk15 (w.take i2) L' hchain' hm2
    have hlen_t1 : (w.take i1).length = i1 := by rw [List.length_take]; omega
    have hlen_t2 : (w.take i2).length = i2 := by rw [List.length_take]; omega
    have hi1_L : i1 < L'.length := by omega
    have hi2_L : i2 < L'.length := by omega
    have htake_eq : w.take i2 = w.take i1 ++ (w.drop i1).take (i2 - i1) := by
      have := List.take_append_drop i1 (w.take i2)
      rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take] at this
      exact this.symm
    have hP0_code : S.code (L'[0].head hP0) = S.idc k := by
      have h0eq : L'[0] = L'.head hL' := (List.head_eq_getElem_zero hL').symm
      simpa [h0eq] using hcode_id
    have he1_eq : S.code (L'[i1].head (by simpa [hlen_t1] using hP1)) = walkWordFast k (w.take i1) (S.idc k) := by
      simpa [hlen_t1, hP0_code] using hc1_hd
    have he2_eq : S.code (L'[i2].head (by simpa [hlen_t2] using hP2)) =
        walkWordFast k ((w.drop i1).take (i2 - i1)) (walkWordFast k (w.take i1) (S.idc k)) := by
      rw [← walkWordFast_append, ← htake_eq]
      simpa [hlen_t2, hP0_code] using hc2_hd
    -- Establish j1 < L'[i1].length and j2 < L'[i2].length!
    obtain ⟨_, hlen1⟩ := matchesWord_piece_len w L' i1 hchain' hmatch' (by omega)
    have hj1_lt : j1 < L'[i1].length := by omega
    have hj2_lt : j2 < L'[i2].length := by
      by_cases hi2w : i2 < w.length
      · simp only [hi2w, ↓reduceIte, decide_eq_true_eq] at hok12
        obtain ⟨_, hlen2⟩ := matchesWord_piece_len w L' i2 hchain' hmatch' hi2w
        omega
      · simp only [hi2w, ↓reduceIte, decide_eq_true_eq] at hok12
        have hne2 : L'[i2] ≠ [] := hchain'.pieces_ne _ (List.getElem_mem hi2_L)
        have hpos2 : 0 < L'[i2].length := List.length_pos_of_ne_nil hne2
        omega
    -- Compute codes of L'[i1][j1] and L'[i2][j2]!
    have hcode_piece : ∀ (idx : Nat) (hidx : idx < L'.length) (j : Nat) (hj : j < L'[idx].length)
        (hne : L'[idx] ≠ []), S.code (L'[idx][j]) = pieceAdvance k j (S.code (L'[idx].head hne)) := by
      intro idx hidx j hj hne
      have hperm := hchain'.words L'[idx] (List.getElem_mem hidx)
      have hPle := hchain'.size_le L'[idx] (List.getElem_mem hidx)
      have hcl : List.Pairwise (fun a b => ¬ a ~r b) L'[idx] := by
        have hsp : L' = L'.take idx ++ [L'[idx]] ++ L'.drop (idx + 1) := by
          have := (List.take_append_drop idx L').symm
          rw [List.drop_eq_getElem_cons hidx] at this
          exact this.trans (by simp)
        have hpw := hchain'.classes
        rw [hsp] at hpw
        simp only [List.flatten_append, List.flatten_singleton, List.pairwise_append] at hpw
        exact hpw.1.2.1
      have hdoor := S.door_chain hk L'[idx] hperm (hchain'.doors L'[idx] (List.getElem_mem hidx)) hcl
      exact piece_getElem_code (by omega) hk15 hne hperm hdoor hPle hj
    have hc1_eq : S.code (L'[i1][j1]) = pieceAdvance k j1 (walkWordFast k (w.take i1) (S.idc k)) := by
      rw [hcode_piece i1 hi1_L j1 hj1_lt (by simpa [hlen_t1] using hP1), he1_eq]
    have hc2_eq : S.code (L'[i2][j2]) =
        pieceAdvance k j2 (walkWordFast k ((w.drop i1).take (i2 - i1)) (walkWordFast k (w.take i1) (S.idc k))) := by
      rw [hcode_piece i2 hi2_L j2 hj2_lt (by simpa [hlen_t2] using hP2), he2_eq]
    rw [← hc1_eq, ← hc2_eq] at hwit
    have hp1 : S.PermW k (L'[i1][j1]) := hchain'.words _ (List.getElem_mem hi1_L) _ (List.getElem_mem hj1_lt)
    have hp2 : S.PermW k (L'[i2][j2]) := hchain'.words _ (List.getElem_mem hi2_L) _ (List.getElem_mem hj2_lt)
    have hrot : L'[i1][j1] ~r L'[i2][j2] :=
      S.isRotated_of_canon_eq hp1.2.1 hp2.2.1 (hp1.lt16 hk15) (hp2.lt16 hk15) hwit
    have hnot_rot : ¬ L'[i1][j1] ~r L'[i2][j2] :=
      pairwise_flatten_distinct_pieces hchain'.classes hrange.1 hi2_L
        (List.getElem_mem hj1_lt) (List.getElem_mem hj2_lt)
    exact hnot_rot hrot
  · have hrb : (decide (i1 < i2) && decide (i2 ≤ w.length)) = false := by
      by_cases h1 : i1 < i2 <;> by_cases h2 : i2 ≤ w.length <;> simp_all
    simp [hrb] at hwit

theorem not_infix_of_checkWitness {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) {w : List (Nat × Nat)} {wit : Nat × Nat × Nat × Nat}
    (hwit : checkWitness k w wit = true) (hinf : w <:+: ts) : False := by
  obtain ⟨pre, post, rfl⟩ := hinf
  have h1 : MatchesWord k (w ++ post) (L.drop pre.length) := by
    rw [List.append_assoc] at hmatch
    exact matchesWord_drop pre (w ++ post) L hmatch
  have h2 : MatchesWord k w (L.drop pre.length) := matchesWord_prefix w post _ h1
  exact not_matchesWord_of_checkWitness hk hk15 hwit (hchain.infix (drop_infix pre.length L)) h2

/-! ### 5. Macro-alphabet, base checks, `IsWindow` flag evolution, and segmentation -/

/-- Expand a single macro-symbol `(m, d, t)` into `m` copies of `(0, 4)` followed by `(d, t)`. -/
def expandSym (m d t : Nat) : List (Nat × Nat) :=
  List.replicate m (0, 4) ++ [(d, t)]

/-- Expand a list of macro-symbol IDs into raw `(d, t)` transitions. -/
def expandWord (symInfo : Nat → Nat × Nat × Nat) (w : List Nat) : List (Nat × Nat) :=
  w.flatMap fun a => let (m, d, t) := symInfo a; expandSym m d t

/-- Base structural collision checks for `k`:
  1. `(0, 4)^{k - 2}` collides (so every run of `(0, 4)` has `m ≤ k - 3`);
  2. `[(0, t), (0, 4)]` collides for all `t < 4` (so after any `d = 0, t ≠ 4` piece, `m = 0`). -/
noncomputable def baseCheck (k : Nat) : Bool :=
  wordCollides k (List.replicate (k - 2) (0, 4)) &&
  checkRangeAux 0 (fun t => wordCollides k [(0, t), (0, 4)]) 4

/-- `IsWindow` flag transition for a single deficit `d` (0=after zero, 1=in block needing ≥2, 2=in block with ≥2). -/
def stepF (f d : Nat) : Option Nat :=
  if d == 0 then
    if f == 1 then none else some 0
  else if d == 1 then
    if f == 2 then some 2 else some 1
  else
    some 2

/-- `IsWindow` flag transition for a macro-symbol `(m, d)` = `m` zeros followed by `d`. -/
def nextF (f m d : Nat) : Option Nat :=
  if f == 1 && (m ≥ 1 || d == 0) then none
  else
    let fm := if m ≥ 1 then 0 else f
    if d == 0 then some 0
    else if d == 1 then some (if fm == 2 then 2 else 1)
    else some 2

/-- Walk `stepF` across a list of deficits. -/
def walkF : Nat → List Nat → Option Nat
  | f, [] => some f
  | f, d :: rest => match stepF f d with
    | none => none
    | some f' => walkF f' rest

theorem walkF_append : ∀ (ds1 ds2 : List Nat) (f : Nat),
    walkF f (ds1 ++ ds2) = match walkF f ds1 with
      | none => none
      | some f' => walkF f' ds2
  | [], _, _ => rfl
  | d :: rest, ds2, f => by
    simp only [List.cons_append, walkF]
    cases stepF f d with
    | none => rfl
    | some f' => exact walkF_append rest ds2 f'

theorem walkF_replicate_zero (f : Nat) :
    ∀ m : Nat, walkF f (List.replicate m 0) = if m = 0 then some f else if f = 1 then none else some 0
  | 0 => by simp [walkF]
  | m + 1 => by
    simp only [List.replicate_succ, walkF, stepF, beq_self_eq_true, ↓reduceIte]
    by_cases hf : f = 1
    · simp [hf]
    · have hf' : (f == 1) = false := S.beq_false_of_ne hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte]
      rw [walkF_replicate_zero 0 m]
      cases m <;> simp [hf]

theorem walkF_expandSym (f m d : Nat) :
    walkF f (List.replicate m 0 ++ [d]) = nextF f m d := by
  rw [walkF_append, walkF_replicate_zero]
  unfold nextF
  by_cases hm : m = 0
  · subst hm
    simp only [↓reduceIte, walkF, stepF]
    by_cases hf : f = 1 <;> by_cases hd0 : d = 0 <;> by_cases hd1 : d = 1 <;> by_cases hf2 : f = 2 <;>
      simp_all
  · have hm1 : m ≥ 1 := by omega
    by_cases hf : f = 1
    · simp [hm, hm1, hf]
    · simp only [hm, hm1, hf, ↓reduceIte, walkF, stepF]
      by_cases hd0 : d = 0 <;> by_cases hd1 : d = 1 <;> simp_all

/-- Every `ChainC.IsWindow ds` reaches `some 2` under `walkF 1 ds`! -/
theorem walkF_window_aux :
    ∀ (ds : List Nat) (pre blk : List Nat) (f : Nat),
      f < 3 →
      (∀ pre' blk' post', (pre ++ blk ++ ds) = pre' ++ blk' ++ post' → blk' ≠ [] →
        (∀ x ∈ blk', 0 < x) →
        (pre' = [] ∨ ∃ p, pre' = p ++ [0]) →
        (post' = [] ∨ ∃ p, post' = 0 :: p) →
        ∃ x ∈ blk', 2 ≤ x) →
      (pre = [] ∨ ∃ p, pre = p ++ [0]) →
      (∀ x ∈ blk, 0 < x) →
      (f = 0 → blk = []) →
      (f = 1 → blk ≠ [] → ∀ x ∈ blk, x = 1) →
      (f = 2 → ∃ x ∈ blk, 2 ≤ x) →
      (f = 1 → blk = [] → pre = [] ∧ ds ≠ [] ∧ 0 < ds.headD 0) →
      (∀ y, ds.getLast? = some y → 0 < y) →
      (ds = [] → blk ≠ []) →
      walkF f ds = some 2
  | [], pre, blk, f, hf3, hex, hpre, hpos, hf0, hf1, _, _, _, hne => by
    have hblk_ne : blk ≠ [] := hne rfl
    have hex_blk : ∃ x ∈ blk, 2 ≤ x := hex pre blk [] (by simp) hblk_ne hpos hpre (Or.inl rfl)
    by_cases h0 : f = 0
    · exact absurd (hf0 h0) hblk_ne
    · by_cases h1 : f = 1
      · obtain ⟨x, hx, hx2⟩ := hex_blk
        have := hf1 h1 hblk_ne x hx
        omega
      · have h2 : f = 2 := by omega
        simp [walkF, h2]
  | d :: rest, pre, blk, f, hf3, hex, hpre, hpos, hf0, hf1, hf2, hf1nil, hlast, _ => by
    have hlast_rest : ∀ y, rest.getLast? = some y → 0 < y := by
      intro y hy
      apply hlast y
      cases rest with
      | nil => simp at hy
      | cons r rs => simpa [List.getLast?_cons_cons] using hy
    by_cases hd0 : d = 0
    · subst hd0
      have hrest_ne : rest ≠ [] := by
        intro hr
        subst hr
        have := hlast 0 (by simp)
        omega
      have hf_ne1 : f ≠ 1 := by
        intro h1
        cases blk with
        | nil =>
          have := (hf1nil h1 rfl).2.2
          simp at this
        | cons b bs =>
          have hblk_ne : b :: bs ≠ [] := List.cons_ne_nil _ _
          have hex_blk : ∃ x ∈ b :: bs, 2 ≤ x :=
            hex pre (b :: bs) (0 :: rest) rfl hblk_ne hpos hpre (Or.inr ⟨rest, rfl⟩)
          obtain ⟨x, hx, hx2⟩ := hex_blk
          have := hf1 h1 hblk_ne x hx
          omega
      have hsf : stepF f 0 = some 0 := by
        unfold stepF
        have h1 : (f == 1) = false := S.beq_false_of_ne hf_ne1
        simp [h1]
      simp only [walkF, hsf]
      refine walkF_window_aux rest (pre ++ blk ++ [0]) [] 0 (by omega) ?_
        (Or.inr ⟨pre ++ blk, rfl⟩) (by simp) (fun _ => rfl) (by omega) (by omega) (by omega)
        hlast_rest (fun h => absurd h hrest_ne)
      intro pre' blk' post' heq
      apply hex pre' blk' post'
      simpa [List.append_assoc] using heq
    · have hdpos : 0 < d := by omega
      have hpos' : ∀ x ∈ blk ++ [d], 0 < x := by
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · exact hpos x h1
        · rw [List.mem_singleton.mp h1]; exact hdpos
      by_cases hd1 : d = 1
      · subst hd1
        by_cases hf2eq : f = 2
        · subst hf2eq
          have hsf : stepF 2 1 = some 2 := rfl
          simp only [walkF, hsf]
          refine walkF_window_aux rest pre (blk ++ [1]) 2 (by omega) ?_ hpre hpos'
            (by omega) (by omega) ?_ (by omega) hlast_rest (fun _ => by simp)
          · intro pre' blk' post' heq; apply hex pre' blk' post'; simpa [List.append_assoc] using heq
          · intro _; obtain ⟨x, hx, hx2⟩ := hf2 rfl; exact ⟨x, List.mem_append_left _ hx, hx2⟩
        · have hsf : stepF f 1 = some 1 := by
            unfold stepF
            have h2 : (f == 2) = false := S.beq_false_of_ne hf2eq
            simp [h2]
          simp only [walkF, hsf]
          refine walkF_window_aux rest pre (blk ++ [1]) 1 (by omega) ?_ hpre hpos'
            (by omega) ?_ (by omega) (fun _ h => by simp at h) hlast_rest (fun _ => by simp)
          · intro pre' blk' post' heq; apply hex pre' blk' post'; simpa [List.append_assoc] using heq
          · intro _ _ x hx
            rcases List.mem_append.mp hx with hx1 | hx1
            · by_cases h0 : f = 0
              · rw [hf0 h0] at hx1; simp at hx1
              · have h1 : f = 1 := by omega
                exact hf1 h1 (List.ne_nil_of_mem hx1) x hx1
            · exact List.mem_singleton.mp hx1
      · have hd2 : 2 ≤ d := by omega
        have hsf : stepF f d = some 2 := by
          unfold stepF
          have h0 : (d == 0) = false := S.beq_false_of_ne hd0
          have h1 : (d == 1) = false := S.beq_false_of_ne hd1
          simp [h0, h1]
        simp only [walkF, hsf]
        refine walkF_window_aux rest pre (blk ++ [d]) 2 (by omega) ?_ hpre hpos'
          (by omega) (by omega) (fun _ => ⟨d, by simp, hd2⟩) (by omega) hlast_rest (fun _ => by simp)
        intro pre' blk' post' heq; apply hex pre' blk' post'; simpa [List.append_assoc] using heq

theorem walkF_isWindow {ds : List Nat} (hw : ChainC.IsWindow ds) : walkF 1 ds = some 2 := by
  obtain ⟨x0, r0, hfirst, hx0⟩ := hw.first_partial
  obtain ⟨init, y0, hlast, hy0⟩ := hw.last_partial
  refine walkF_window_aux ds [] [] 1 (by omega) (by simpa using hw.excess) (Or.inl rfl)
    (by simp) (by omega) (by simp) (by omega) ?_ ?_ ?_
  · intro _ _
    rw [hfirst]
    exact ⟨rfl, List.cons_ne_nil _ _, by simpa using hx0⟩
  · intro y hy
    rw [hlast, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hy
    simp only [List.getLast?_singleton, Option.some.injEq] at hy
    omega
  · intro hnil
    rw [hnil] at hfirst
    cases hfirst

/-! ### 6. Sparse-Override Certificate & Verification Combinators -/

/-- Result of an explicit override transition: alive state `v` (with `steps` fail hops) or CEGAR dead witness `fid`. -/
inductive EdgeRes where
  | alive (v : Nat) (steps : Nat)
  | dead (fid : Nat)
  deriving DecidableEq

/-- Lookup symbol `a` in a tiny association list of overrides for state `u`. -/
def lookupOv : List (Nat × EdgeRes) → Nat → Option EdgeRes
  | [], _ => none
  | (k, v) :: rest, a => if k == a then some v else lookupOv rest a

/-- Pure-GMP-`Nat` potential ordering (`none` = unreachable = `-∞`). -/
def oLeN : Option Nat → Option Nat → Bool
  | none, _ => true
  | some _, none => false
  | some x, some y => Nat.ble x y

/-- Pure-GMP-`Nat` shifted step inequality `src + pos - neg ≤ dst` (ZERO `Int` in kernel!). -/
def oStepLeN (src : Option Nat) (pos neg : Nat) (dst : Option Nat) : Bool :=
  match src, dst with
  | none, _ => true
  | some _, none => false
  | some x, some y => Nat.ble (x + pos) (y + neg)

/-- Mathematical interpretation of shifted `Option Nat` potential as `Option Int` (used only in proofs). -/
def psiInt (bias : Nat) : Option Nat → Option Int
  | none => none
  | some x => some ((x : Int) - (bias : Int))

theorem oLe_of_oLeN {bias : Nat} {a b : Option Nat} (h : oLeN a b = true) :
    oLe (psiInt bias a) (psiInt bias b) = true := by
  cases a with
  | none => rfl
  | some x =>
    cases b with
    | none => simp [oLeN] at h
    | some y =>
      have hxy : x ≤ y := Nat.le_of_ble_eq_true h
      simp only [psiInt, oLe, decide_eq_true_eq]
      omega

theorem oLe_add_of_oStepLeN {bias pos neg : Nat} {a b : Option Nat}
    (h : oStepLeN a pos neg b = true) :
    oLe (oAdd (psiInt bias a) ((pos : Int) - (neg : Int))) (psiInt bias b) = true := by
  cases a with
  | none => rfl
  | some x =>
    cases b with
    | none => simp [oStepLeN] at h
    | some y =>
      have hxy : x + pos ≤ y + neg := Nat.le_of_ble_eq_true h
      simp only [psiInt, oAdd, oLe, decide_eq_true_eq]
      omega

/-- Complete exact-integer `TropicCEGAR-Macro` certificate (pure-`Nat` GMP + O(1) fail-link + two-point witness). -/
structure TropicCert where
  k : Nat
  D_track : Nat
  cn : Nat
  bn : Nat
  q : Nat
  A : Nat
  bias : Nat
  ALPHA : Nat
  V : Nat
  numCegar : Nat
  symInfo : Nat → Nat × Nat × Nat
  symId : Nat → Nat → Nat → Option Nat
  d1State : Nat → Nat
  stD0 : Nat → Bool
  stPsi : Nat → Nat → Option Nat
  stPar : Nat → Nat
  stSym : Nat → Nat
  stFail : Nat → Nat
  stFailSteps : Nat → Nat
  maxPsi : Nat → Nat → Option Nat
  cegarForb : Nat → List Nat
  cegarWit : Nat → Nat × Nat × Nat × Nat
  pairMode : Nat → Nat → Nat       -- 0 = depth1Ok, 1 = forb2, 2 = override
  ovList : Nat → List Nat          -- for each `s`, list of symbols `a` with `pairMode s a ≥ 2`
  ovMap : Nat → List (Nat × EdgeRes)  -- for each `u`, tiny assoc list of overrides `(a, res)`

/-- Iterate the Aho-Corasick failure link `n` times from `u`. -/
def failIter (cert : TropicCert) : Nat → Nat → Nat
  | 0, u => u
  | n + 1, u => failIter cert n (cert.stFail u)

/-- Check that `revW` matches the reversed prefix ending at state `u` (walks only `revW.length` hops!). -/
def matchesRevPref (cert : TropicCert) : Nat → List Nat → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | u, s :: rest => cert.stSym u == s && matchesRevPref cert (cert.stPar u) rest

/-- Check that `w` is a suffix of `statePref cert u ++ [a]` in `O(|w|)` parent hops. -/
def matchesRevSuffix (cert : TropicCert) (u a : Nat) (w : List Nat) : Bool :=
  match w.reverse with
  | [] => true
  | last :: restRev => last == a && matchesRevPref cert u restRev

/-- Reconstruct prefix word of state `u` using bounded fuel (exact since `stPar u < u`). -/
def statePrefAux (cert : TropicCert) : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, u => statePrefAux cert fuel (cert.stPar u) ++ [cert.stSym u]

def statePref (cert : TropicCert) (u : Nat) : List Nat :=
  statePrefAux cert u u

theorem statePrefAux_eq_of_ge (cert : TropicCert)
    (hpar : ∀ u, 0 < u → u < cert.V → cert.stPar u < u) :
    ∀ (u fuel : Nat), u < cert.V → u ≤ fuel → statePrefAux cert fuel u = statePref cert u
  | 0, fuel, _, _ => by cases fuel <;> rfl
  | u + 1, fuel + 1, hu, hle => by
    have hp : cert.stPar (u + 1) < u + 1 := hpar (u + 1) (by omega) hu
    unfold statePref
    simp only [statePrefAux]
    congr 1
    rw [statePrefAux_eq_of_ge cert hpar (cert.stPar (u + 1)) fuel (by omega) (by omega),
      statePrefAux_eq_of_ge cert hpar (cert.stPar (u + 1)) u (by omega) (by omega)]
  | u + 1, 0, _, hle => by omega

theorem statePref_pos (cert : TropicCert)
    (hpar : ∀ u, 0 < u → u < cert.V → cert.stPar u < u) {u : Nat} (h0 : 0 < u) (hu : u < cert.V) :
    statePref cert u = statePref cert (cert.stPar u) ++ [cert.stSym u] := by
  cases u with
  | zero => omega
  | succ u' =>
    have hp : cert.stPar (u' + 1) < u' + 1 := hpar (u' + 1) (by omega) hu
    unfold statePref
    simp only [statePrefAux]
    congr 1
    exact statePrefAux_eq_of_ge cert hpar (cert.stPar (u' + 1)) u' (by omega) (by omega)

/-- Decidable list suffix test. -/
def isSuffixB (s t : List Nat) : Bool :=
  s.length ≤ t.length && decide (t.drop (t.length - s.length) = s)

theorem suffix_of_isSuffixB {s t : List Nat} (h : isSuffixB s t = true) : s <:+ t := by
  unfold isSuffixB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨t.take (t.length - s.length), ?_⟩
  conv_rhs => rw [← List.take_append_drop (t.length - s.length) t]
  rw [h.2]

/-- Weight `2*q*(m + 1) - A*d` of macro-symbol `a`. -/
def symWeight (cert : TropicCert) (a : Nat) : Int :=
  let (m, d, _) := cert.symInfo a
  2 * (cert.q : Int) * ((m + 1 : Nat) : Int) - (cert.A : Int) * (d : Int)

/-- RESET weight at `(u, f)`. -/
def resetWeight (cert : TropicCert) (u f : Nat) : Int :=
  let rrows : Nat := if f == 1 || cert.stD0 u then 1 else cert.k - 2
  2 * (cert.q : Int) * (rrows : Int) - (cert.A : Int) * ((cert.D_track + 1 : Nat) : Int)

/-- Pure-GMP-`Nat` final-piece bound check for `(u, f)` (ZERO `Int` in kernel!). -/
def endBoundCheck (cert : TropicCert) (u f : Nat) : Bool :=
  match cert.stPsi u f with
  | none => true
  | some pu =>
    let c1 : Nat := 2 * cert.q * (cert.k - 4)
    let kA : Nat := if f == 2 then 1 else 2
    let okA : Bool := Nat.ble (pu + 2 * cert.q + c1) (cert.bias + cert.bn + kA * cert.A)
    let okB : Bool :=
      if f == 1 || cert.stD0 u then true
      else Nat.ble (pu + 2 * cert.q * (cert.k - 2) + c1) (cert.bias + cert.bn + 2 * cert.A)
    okA && okB

theorem suffix_of_matchesRevPref {cert : TropicCert}
    (hpar : ∀ u, 0 < u → u < cert.V → cert.stPar u < u) :
    ∀ (revW : List Nat) (u : Nat), u < cert.V → matchesRevPref cert u revW = true →
      revW.reverse <:+ statePref cert u
  | [], u, _, _ => by simp
  | _ :: _, 0, _, h => by simp [matchesRevPref] at h
  | s :: rest, u + 1, hu, h => by
    simp only [matchesRevPref, Bool.and_eq_true, beq_iff_eq] at h
    have hp : cert.stPar (u + 1) < u + 1 := hpar (u + 1) (by omega) hu
    obtain ⟨pre, hpre⟩ := suffix_of_matchesRevPref hpar rest (cert.stPar (u + 1)) (by omega) h.2
    rw [List.reverse_cons, statePref_pos cert hpar (by omega) hu, h.1]
    exact ⟨pre, by rw [← List.append_assoc, hpre]⟩

theorem suffix_of_matchesRevSuffix {cert : TropicCert}
    (hpar : ∀ u, 0 < u → u < cert.V → cert.stPar u < u)
    {u a : Nat} {w : List Nat} (hu : u < cert.V) (h : matchesRevSuffix cert u a w = true) :
    w <:+ statePref cert u ++ [a] := by
  unfold matchesRevSuffix at h
  cases hrev : w.reverse with
  | nil =>
    have hw : w = [] := List.reverse_eq_nil_iff.mp hrev
    rw [hw]; exact List.nil_suffix
  | cons last restRev =>
    rw [hrev] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨pre, hpre⟩ := suffix_of_matchesRevPref hpar restRev u hu h.2
    have hw : w = restRev.reverse ++ [a] := by
      have := congrArg List.reverse hrev
      simpa [h.1] using this
    rw [hw]
    exact ⟨pre, by rw [← List.append_assoc, hpre]⟩

/-- Pure-GMP-`Nat` check of a single state `u < V` (ZERO `Int` in kernel!). -/
def stateCheck (cert : TropicCert) (u : Nat) : Bool :=
  let okStruct :=
    if u == 0 then
      !cert.stD0 0 && oLeN (some cert.bias) (cert.stPsi 0 1) && (cert.stFail 0 == 0)
    else
      let s := cert.stSym u
      let f := cert.stFail u
      let okFail :=
        if f == 0 then true
        else Nat.ble (f + 1) u && (cert.stSym f == s) &&
          (failIter cert (cert.stFailSteps u) (cert.stPar u) == cert.stPar f)
      Nat.ble (cert.stPar u + 1) u && Nat.ble (s + 1) cert.ALPHA &&
      (!cert.stD0 u || ((cert.symInfo s).2.1 == 0)) &&
      okFail &&
      oLeN (cert.stPsi u 0) (cert.maxPsi s 0) &&
      oLeN (cert.stPsi u 1) (cert.maxPsi s 1) &&
      oLeN (cert.stPsi u 2) (cert.maxPsi s 2)
  let rst (f : Nat) : Bool :=
    let rrows : Nat := if f == 1 || cert.stD0 u then 1 else cert.k - 2
    oStepLeN (cert.stPsi u f) (2 * cert.q * rrows) (cert.A * (cert.D_track + 1)) (cert.stPsi 0 2)
  let okReset := rst 0 && rst 1 && rst 2
  let okEnd :=
    endBoundCheck cert u 0 && endBoundCheck cert u 1 && endBoundCheck cert u 2
  okStruct && okReset && okEnd

/-- Pure-GMP-`Nat` potential propagation along `(psi_src, a) → v` for all `f ∈ {0, 1, 2}`. -/
def edgePsiCheck (cert : TropicCert) (psiSrc : Nat → Option Nat) (a v : Nat) : Bool :=
  let (m, d, _) := cert.symInfo a
  let pos : Nat := 2 * cert.q * (m + 1)
  let neg : Nat := cert.A * d
  let chk (f : Nat) : Bool :=
    match nextF f m d with
    | none => true
    | some nf => oStepLeN (psiSrc f) pos neg (cert.stPsi v nf)
  chk 0 && chk 1 && chk 2

/-- Check a `(s, a)` pair: `depth1Ok` when `pairMode = 0`, membership in `ovList s` when `pairMode ≥ 2`. -/
def pairDepth1Check (cert : TropicCert) (s a : Nat) : Bool :=
  let pm := cert.pairMode s a
  if pm == 0 then
    edgePsiCheck cert (cert.maxPsi s) a (cert.d1State a)
  else if pm == 1 then true
  else (cert.ovList s).contains a

/-- Check root transition `(0, a)` (either explicit override or `d1State a`). -/
def rootEdgeCheck (cert : TropicCert) (a : Nat) : Bool :=
  match lookupOv (cert.ovMap 0) a with
  | none => edgePsiCheck cert (cert.stPsi 0) a (cert.d1State a)
  | some (.alive v _) =>
    decide (v < cert.V) &&
      (v == 0 || (decide (cert.stPar v = 0) && decide (cert.stSym v = a))) &&
      edgePsiCheck cert (cert.stPsi 0) a v
  | some (.dead fid) =>
    decide (fid < cert.numCegar) && matchesRevSuffix cert 0 a (cert.cegarForb fid)

/-- Check one explicit override `(u, a)` for `u > 0` in `O(1)` using `failIter` / `matchesRevSuffix`! -/
def overrideCheckOne (cert : TropicCert) (u a : Nat) : Bool :=
  match lookupOv (cert.ovMap u) a with
  | none => false
  | some (.alive v steps) =>
    decide (v < cert.V) &&
      (v == 0 || (decide (cert.stSym v = a) && decide (failIter cert steps u = cert.stPar v))) &&
      edgePsiCheck cert (cert.stPsi u) a v
  | some (.dead fid) =>
    decide (fid < cert.numCegar) && matchesRevSuffix cert u a (cert.cegarForb fid)

/-- Check all overrides for state `u` (iterating ONLY over the tiny `ovList (stSym u)`!). -/
def checkOverridesState (cert : TropicCert) (u : Nat) : Bool :=
  if u == 0 then true
  else (cert.ovList (cert.stSym u)).all (overrideCheckOne cert u)

/-- Check alphabet completeness for `(m, d, t)`. -/
noncomputable def alphaTripleCheck (cert : TropicCert) (m d t : Nat) : Bool :=
  if d == 0 && t == 4 then true
  else match cert.symId m d t with
    | some a => decide (a < cert.ALPHA) && decide (cert.symInfo a = (m, d, t))
    | none => wordCollides cert.k (expandSym m d t)

/-- Check `d1State a` invariant for `a < ALPHA`. -/
def d1Check (cert : TropicCert) (a : Nat) : Bool :=
  let u := cert.d1State a
  decide (0 < u) && decide (u < cert.V) && decide (cert.stPar u = 0) && decide (cert.stSym u = a)

/-- Shared-prefix kernel check for all `pairMode s a = 1` (`forb2`) pairs with fixed first symbol `s`. -/
noncomputable def checkForb2Sym (cert : TropicCert) (s : Nat) : Bool :=
  let (ms, ds, ts) := cert.symInfo s
  let (col1, cur1, T1) := walkWordC cert.k (expandSym ms ds ts) (S.idc cert.k) S.Tr.leaf
  if col1 then true
  else checkRangeChunked 0 cert.ALPHA fun a =>
    if cert.pairMode s a == 1 then
      let (ma, da, ta) := cert.symInfo a
      let (col2, cur2, T2) := walkWordC cert.k (expandSym ma da ta) cur1 T1
      col2 || S.Tr.mem T2 (S.canon cert.k cur2)
    else true

theorem forb2_of_checkForb2Sym {cert : TropicCert} {s : Nat} (h : checkForb2Sym cert s = true) :
    ∀ a < cert.ALPHA, cert.pairMode s a = 1 →
      wordCollides cert.k (let (ms, ds, ts) := cert.symInfo s; let (ma, da, ta) := cert.symInfo a;
        expandSym ms ds ts ++ expandSym ma da ta) = true := by
  intro a ha hpm
  unfold checkForb2Sym at h
  unfold wordCollides
  rcases hms : cert.symInfo s with ⟨ms, ds, ts⟩
  rcases hma : cert.symInfo a with ⟨ma, da, ta⟩
  rw [hms] at h
  dsimp only
  rw [walkWordC_append]
  cases h1 : walkWordC cert.k (expandSym ms ds ts) (S.idc cert.k) S.Tr.leaf with
  | mk col1 r1 =>
    rcases r1 with ⟨cur1, T1⟩
    simp only [h1] at h ⊢
    cases col1 with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      have ha_ok := checkRangeChunked_spec h a (Nat.zero_le _) (by omega)
      simp only [hpm, beq_self_eq_true, ↓reduceIte, hma] at ha_ok
      exact ha_ok

/-- Full certificate validity predicate (every field is a pure-kernel sharded check!). -/
structure CertValid (cert : TropicCert) : Prop where
  hk5 : 5 ≤ cert.k
  hk15 : cert.k ≤ 15
  hD1 : 1 ≤ cert.D_track
  hq : 0 < cert.q
  hcn : cert.cn ≤ cert.q * (cert.k - 5)
  hA : cert.A = cert.q * (cert.k - 3) - cert.cn
  hV : 0 < cert.V
  hbase : baseCheck cert.k = true
  halpha : ∀ m ≤ cert.k - 3, ∀ d ≤ cert.D_track, ∀ t < 5, alphaTripleCheck cert m d t = true
  hd1 : ∀ a < cert.ALPHA, d1Check cert a = true
  hcegar : ∀ fid < cert.numCegar,
    checkWitness cert.k (expandWord cert.symInfo (cert.cegarForb fid)) (cert.cegarWit fid) = true
  hforb2 : ∀ s < cert.ALPHA, ∀ a < cert.ALPHA, cert.pairMode s a = 1 →
    wordCollides cert.k (let (ms, ds, ts) := cert.symInfo s; let (ma, da, ta) := cert.symInfo a;
      expandSym ms ds ts ++ expandSym ma da ta) = true
  hstates : ∀ u < cert.V, stateCheck cert u = true
  hroot : ∀ a < cert.ALPHA, rootEdgeCheck cert a = true
  hpairs : ∀ s < cert.ALPHA, ∀ a < cert.ALPHA, pairDepth1Check cert s a = true
  hover : ∀ u < cert.V, checkOverridesState cert u = true

/-! ### 7. Macro-segmentation, inductive simulation, and main Theorem C bridge -/

/-- Greedily split a raw transition list `ts` into macro-tokens `[(m, d, t), ...]`
plus a trailing count `m_tail` of `(0, 4)` pieces. -/
def splitMacroAux : Nat → List (Nat × Nat) → List (Nat × Nat × Nat) × Nat
  | acc, [] => ([], acc)
  | acc, (d, t) :: rest =>
    if d == 0 && t == 4 then splitMacroAux (acc + 1) rest
    else
      let (ms, mt) := splitMacroAux 0 rest
      ((acc, d, t) :: ms, mt)

def expandMacroList (ms : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  ms.flatMap fun (m, d, t) => expandSym m d t

theorem splitMacroAux_expand :
    ∀ (acc : Nat) (ts : List (Nat × Nat)),
      let (ms, mt) := splitMacroAux acc ts
      List.replicate acc (0, 4) ++ ts = expandMacroList ms ++ List.replicate mt (0, 4)
  | acc, [] => by simp [splitMacroAux, expandMacroList]
  | acc, (d, t) :: rest => by
    simp only [splitMacroAux]
    by_cases h : d = 0 ∧ t = 4
    · rcases h with ⟨rfl, rfl⟩
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      have ih := splitMacroAux_expand (acc + 1) rest
      simpa [List.replicate_succ', List.append_assoc] using ih
    · have hne : (d == 0 && t == 4) = false := by
        cases hd : (d == 0) <;> cases ht : (t == 4) <;> simp_all
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitMacroAux_expand 0 rest
      cases hs : splitMacroAux 0 rest with
      | mk ms mt =>
        rw [hs] at ih
        simp only [expandMacroList, List.flatMap_cons, expandSym, List.append_assoc,
          List.singleton_append]
        simpa [expandMacroList, expandSym] using ih

theorem splitMacroAux_props :
    ∀ (acc : Nat) (ts : List (Nat × Nat)),
      (∀ dt ∈ ts, dt.2 < 5) →
      let (ms, _mt) := splitMacroAux acc ts
      ∀ x ∈ ms, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5
  | _, [], _ => by simp [splitMacroAux]
  | acc, (d, t) :: rest, ht5 => by
    simp only [splitMacroAux]
    have ht5' : ∀ dt ∈ rest, dt.2 < 5 := fun dt hdt => ht5 dt (List.mem_cons_of_mem _ hdt)
    by_cases h : d = 0 ∧ t = 4
    · rcases h with ⟨rfl, rfl⟩
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      exact splitMacroAux_props (acc + 1) rest ht5'
    · have hne : (d == 0 && t == 4) = false := by
        cases hd : (d == 0) <;> cases ht : (t == 4) <;> simp_all
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitMacroAux_props 0 rest ht5'
      cases hs : splitMacroAux 0 rest with
      | mk ms mt =>
        rw [hs] at ih
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨h, ht5 (d, t) List.mem_cons_self⟩
        · exact ih x hx'

/-- Any `baseCheck k = true` forbids `k - 2` consecutive `(0, 4)` and forbids `[(0, t), (0, 4)]` (`t < 4`). -/
theorem baseCheck_conseq {k : Nat} (hb : baseCheck k = true) :
    wordCollides k (List.replicate (k - 2) (0, 4)) = true ∧
    ∀ t < 4, wordCollides k [(0, t), (0, 4)] = true := by
  unfold baseCheck at hb
  simp only [Bool.and_eq_true] at hb
  exact ⟨hb.1, fun t ht => checkRangeAux_spec hb.2 t (Nat.zero_le _) (by omega)⟩

/-- Extract `stPar u < u` from `CertValid`. -/
theorem CertValid.par_lt {cert : TropicCert} (hv : CertValid cert) {u : Nat}
    (h0 : 0 < u) (hu : u < cert.V) : cert.stPar u < u := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  have hne : (u == 0) = false := S.beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hs
  have := Nat.le_of_ble_eq_true hs.1.1.1.1.1.1.1.1
  omega

/-- Extract `stSym u < ALPHA` from `CertValid`. -/
theorem CertValid.sym_lt {cert : TropicCert} (hv : CertValid cert) {u : Nat}
    (h0 : 0 < u) (hu : u < cert.V) : cert.stSym u < cert.ALPHA := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  have hne : (u == 0) = false := S.beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hs
  have := Nat.le_of_ble_eq_true hs.1.1.1.1.1.1.1.2
  omega

/-- Extract `stD0 u = true → (symInfo (stSym u)).2.1 = 0` for `u > 0`. -/
theorem CertValid.d0_zero {cert : TropicCert} (hv : CertValid cert) {u : Nat}
    (h0 : 0 < u) (hu : u < cert.V) (hd0 : cert.stD0 u = true) :
    (cert.symInfo (cert.stSym u)).2.1 = 0 := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  have hne : (u == 0) = false := S.beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, hd0,
    Bool.not_true, Bool.false_or, beq_iff_eq] at hs
  exact hs.1.1.1.1.1.1.2

/-- Extract `stD0 0 = false` and `0 ≤ psiInt[0, 1]`. -/
theorem CertValid.root_ok {cert : TropicCert} (hv : CertValid cert) :
    cert.stD0 0 = false ∧ oLe (some 0) (psiInt cert.bias (cert.stPsi 0 1)) = true := by
  have hs := hv.hstates 0 hv.hV
  unfold stateCheck at hs
  simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hs
  refine ⟨hs.1.1.1.1, ?_⟩
  have hle := oLe_of_oLeN (bias := cert.bias) hs.1.1.1.2
  simpa [psiInt] using hle

theorem CertValid.fail_zero {cert : TropicCert} (hv : CertValid cert) :
    cert.stFail 0 = 0 := by
  have hs := hv.hstates 0 hv.hV
  unfold stateCheck at hs
  simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hs
  exact hs.1.1.2

theorem CertValid.fail_check {cert : TropicCert} (hv : CertValid cert) {u : Nat}
    (h0 : 0 < u) (hu : u < cert.V) :
    cert.stFail u = 0 ∨
      (cert.stFail u < u ∧ cert.stSym (cert.stFail u) = cert.stSym u ∧
        failIter cert (cert.stFailSteps u) (cert.stPar u) = cert.stPar (cert.stFail u)) := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  have hne : (u == 0) = false := S.beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hs
  have hf := hs.1.1.1.1.1.2
  by_cases hf0 : cert.stFail u = 0
  · exact Or.inl hf0
  · right
    have hfne : (cert.stFail u == 0) = false := S.beq_false_of_ne hf0
    simp only [hfne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hf
    have hlt := Nat.le_of_ble_eq_true hf.1.1
    exact ⟨by omega, hf.1.2, hf.2⟩

/-- Strong induction: every failure link `stFail u` satisfies `stFail u ≤ u` and `statePref (stFail u) <:+ statePref u`! -/
theorem CertValid.fail_le_and_suffix {cert : TropicCert} (hv : CertValid cert) :
    ∀ u : Nat, u < cert.V →
      cert.stFail u ≤ u ∧ statePref cert (cert.stFail u) <:+ statePref cert u := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu
    cases u with
    | zero =>
      rw [hv.fail_zero]
      exact ⟨Nat.le_refl 0, List.suffix_refl _⟩
    | succ u' =>
      -- Helper: iterating stFail on any w ≤ u' preserves ≤ w and suffix!
      have hiter : ∀ r w, w ≤ u' →
          failIter cert r w ≤ w ∧ statePref cert (failIter cert r w) <:+ statePref cert w := by
        intro r
        induction r with
        | zero => intro w _; exact ⟨Nat.le_refl _, List.suffix_refl _⟩
        | succ r' ihr =>
          intro w hw
          have hstep := ih w (by omega) (by omega)
          have hrest := ihr (cert.stFail w) (by omega)
          exact ⟨Nat.le_trans hrest.1 hstep.1, hrest.2.trans hstep.2⟩
      rcases hv.fail_check (by omega) hu with hf0 | ⟨hflt, hfsym, hfpar⟩
      · rw [hf0]
        exact ⟨Nat.zero_le _, by simp [statePref, statePrefAux]⟩
      · have hpar_lt : cert.stPar (u' + 1) < u' + 1 := hv.par_lt (by omega) hu
        have hpar_suf := (hiter (cert.stFailSteps (u' + 1)) (cert.stPar (u' + 1)) (by omega)).2
        rw [hfpar] at hpar_suf
        have hp_u := statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) (by omega) hu
        by_cases hfz : cert.stFail (u' + 1) = 0
        · rw [hfz]; exact ⟨Nat.zero_le _, by simp [statePref, statePrefAux]⟩
        · have hp_f := @statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) (cert.stFail (u' + 1)) (by omega) (by omega)
          refine ⟨by omega, ?_⟩
          rw [hp_f, hp_u, hfsym]
          obtain ⟨pre, hpre⟩ := hpar_suf
          exact ⟨pre, by rw [← List.append_assoc, hpre]⟩

theorem CertValid.failIter_suffix {cert : TropicCert} (hv : CertValid cert) :
    ∀ (r u : Nat), u < cert.V →
      failIter cert r u < cert.V ∧ statePref cert (failIter cert r u) <:+ statePref cert u
  | 0, u, hu => ⟨hu, List.suffix_refl _⟩
  | r + 1, u, hu => by
    have h1 := hv.fail_le_and_suffix u hu
    have h2 := hv.failIter_suffix r (cert.stFail u) (by omega)
    exact ⟨h2.1, h2.2.trans h1.2⟩

/-- Extract `oLe (psiInt (stPsi u f)) (psiInt (maxPsi (stSym u) f)) = true` for `0 < u < V` and `f < 3`. -/
theorem CertValid.le_maxPsi {cert : TropicCert} (hv : CertValid cert) {u f : Nat}
    (h0 : 0 < u) (hu : u < cert.V) (hf : f < 3) :
    oLe (psiInt cert.bias (cert.stPsi u f)) (psiInt cert.bias (cert.maxPsi (cert.stSym u) f)) = true := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  have hne : (u == 0) = false := S.beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hs
  match f, hf with
  | 0, _ => exact oLe_of_oLeN hs.1.1.1.1.2
  | 1, _ => exact oLe_of_oLeN hs.1.1.1.2
  | 2, _ => exact oLe_of_oLeN hs.1.1.2

/-- Extract RESET check for `u < V, f < 3`. -/
theorem CertValid.reset_ok {cert : TropicCert} (hv : CertValid cert) {u f : Nat}
    (hu : u < cert.V) (hf : f < 3) :
    oLe (oAdd (psiInt cert.bias (cert.stPsi u f)) (resetWeight cert u f)) (psiInt cert.bias (cert.stPsi 0 2)) = true := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  simp only [Bool.and_eq_true] at hs
  have hstep : oStepLeN (cert.stPsi u f)
      (2 * cert.q * (if f == 1 || cert.stD0 u then 1 else cert.k - 2))
      (cert.A * (cert.D_track + 1)) (cert.stPsi 0 2) = true := by
    match f, hf with
    | 0, _ => exact hs.1.2.1.1
    | 1, _ => exact hs.1.2.1.2
    | 2, _ => exact hs.1.2.2
  have hle := oLe_add_of_oStepLeN (bias := cert.bias) hstep
  have hrw : (((2 * cert.q * (if f == 1 || cert.stD0 u then 1 else cert.k - 2) : Nat) : Int) -
      ((cert.A * (cert.D_track + 1) : Nat) : Int)) = resetWeight cert u f := by
    unfold resetWeight
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  rwa [hrw] at hle

/-- Extract final-piece bound check for `u < V, f < 3`. -/
theorem CertValid.end_ok {cert : TropicCert} (hv : CertValid cert) {u f : Nat}
    (hu : u < cert.V) (hf : f < 3) : endBoundCheck cert u f = true := by
  have hs := hv.hstates u hu
  unfold stateCheck at hs
  simp only [Bool.and_eq_true] at hs
  match f, hf with
  | 0, _ => exact hs.2.1.1
  | 1, _ => exact hs.2.1.2
  | 2, _ => exact hs.2.2

/-- Extract `edgePsiCheck` at a specific `f < 3`. -/
theorem edgePsiCheck_at {cert : TropicCert} {psiSrc : Nat → Option Nat} {a v f nf : Nat}
    (h : edgePsiCheck cert psiSrc a v = true) (hf : f < 3)
    (hnf : nextF f (cert.symInfo a).1 (cert.symInfo a).2.1 = some nf) :
    oLe (oAdd (psiInt cert.bias (psiSrc f)) (symWeight cert a)) (psiInt cert.bias (cert.stPsi v nf)) = true := by
  unfold edgePsiCheck at h
  simp only [Bool.and_eq_true] at h
  have hchk : (match nextF f (cert.symInfo a).1 (cert.symInfo a).2.1 with
      | none => true
      | some nf => oStepLeN (psiSrc f) (2 * cert.q * ((cert.symInfo a).1 + 1)) (cert.A * (cert.symInfo a).2.1) (cert.stPsi v nf)) = true := by
    match f, hf with
    | 0, _ => exact h.1.1
    | 1, _ => exact h.1.2
    | 2, _ => exact h.2
  rw [hnf] at hchk
  have hle := oLe_add_of_oStepLeN (bias := cert.bias) hchk
  have hsw : (((2 * cert.q * ((cert.symInfo a).1 + 1) : Nat) : Int) -
      ((cert.A * (cert.symInfo a).2.1 : Nat) : Int)) = symWeight cert a := by
    unfold symWeight
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  rwa [hsw] at hle

/-- State `u` invariant during simulation of prefix `done : List (Nat × Nat × Nat)`:
  `expandWord symInfo (statePref u)` is a suffix of `expandMacroList done`! -/
def StateInv (cert : TropicCert) (u : Nat) (done : List (Nat × Nat × Nat)) : Prop :=
  u < cert.V ∧ expandWord cert.symInfo (statePref cert u) <:+ expandMacroList done

theorem stateInv_zero (cert : TropicCert) (hv : CertValid cert) (done : List (Nat × Nat × Nat)) :
    StateInv cert 0 done := ⟨hv.hV, by simp [statePref, statePrefAux, expandWord]⟩

theorem expandWord_append (symInfo : Nat → Nat × Nat × Nat) (w1 w2 : List Nat) :
    expandWord symInfo (w1 ++ w2) = expandWord symInfo w1 ++ expandWord symInfo w2 :=
  List.flatMap_append

theorem expandWord_singleton (symInfo : Nat → Nat × Nat × Nat) (a : Nat) :
    expandWord symInfo [a] = let (m, d, t) := symInfo a; expandSym m d t := by
  simp [expandWord]

theorem expandWord_suffix {symInfo : Nat → Nat × Nat × Nat} {s t : List Nat} (h : s <:+ t) :
    expandWord symInfo s <:+ expandWord symInfo t := by
  obtain ⟨pre, rfl⟩ := h
  exact ⟨expandWord symInfo pre, (expandWord_append symInfo pre s).symm⟩

theorem suffix_trans_append {α : Type} {a b c d : List α} (h1 : a <:+ b ++ d) (h2 : b <:+ c) :
    a <:+ c ++ d := by
  obtain ⟨p1, hp1⟩ := h1
  obtain ⟨p2, hp2⟩ := h2
  refine ⟨p2 ++ p1, ?_⟩
  rw [List.append_assoc, hp1, ← List.append_assoc, hp2]

/-- If `stD0 u = true` and `StateInv cert u done`, then `expandMacroList done` ends in `(0, t)` for some `t < 4`! -/
theorem d0_ends_zero {cert : TropicCert} (hv : CertValid cert) {u : Nat}
    {done : List (Nat × Nat × Nat)} (hinv : StateInv cert u done) (hd0 : cert.stD0 u = true)
    (hdone_t5 : ∀ x ∈ done, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5) :
    ∃ t < 4, [(0, t)] <:+ expandMacroList done := by
  have hu0 : 0 < u := by
    by_contra h
    have heq : u = 0 := by omega
    rw [heq, hv.root_ok.1] at hd0
    cases hd0
  have hd_zero := hv.d0_zero hu0 hinv.1 hd0
  have hpref := statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) hu0 hinv.1
  -- Since statePref u ends in [stSym u], expandWord (statePref u) ends in expandSym m 0 t, hence ends in [(0, t)]!
  have hsuf_a : [cert.stSym u] <:+ statePref cert u := ⟨statePref cert (cert.stPar u), hpref.symm⟩
  have hexp_a : expandWord cert.symInfo [cert.stSym u] <:+ expandMacroList done :=
    (expandWord_suffix hsuf_a).trans hinv.2
  rw [expandWord_singleton] at hexp_a
  have hm_eq : cert.symInfo (cert.stSym u) =
      ((cert.symInfo (cert.stSym u)).1, 0, (cert.symInfo (cert.stSym u)).2.2) := by
    cases hsi : cert.symInfo (cert.stSym u) with
    | mk m dt => cases dt with | mk d t => simp only [hsi] at hd_zero; subst hd_zero; rfl
  let t := (cert.symInfo (cert.stSym u)).2.2
  have hsuf_t : [(0, t)] <:+ expandMacroList done := by
    have h1 : [(0, t)] <:+ expandSym (cert.symInfo (cert.stSym u)).1 0 t :=
      ⟨List.replicate (cert.symInfo (cert.stSym u)).1 (0, 4), rfl⟩
    rw [hm_eq] at hexp_a
    exact h1.trans hexp_a
  -- Show t < 4: since [(0, t)] is a suffix of expandMacroList done, (0, t) is the last pair of some token in done!
  -- Wait: any token in done has (d, t) ≠ (0, 4) and t < 5, and its last pair is (d, t)!
  have ht4 : t < 4 := by
    obtain ⟨pre, hpre⟩ := hsuf_t
    cases hdone : done.reverse with
    | nil =>
      have : done = [] := List.reverse_eq_nil_iff.mp hdone
      rw [this] at hpre
      simp [expandMacroList] at hpre
    | cons last init_rev =>
      have hdone_eq : done = init_rev.reverse ++ [last] := by
        have := congrArg List.reverse hdone
        simpa using this
      have hlast_mem : last ∈ done := by rw [hdone_eq]; simp
      have hlast_prop := hdone_t5 last hlast_mem
      rw [hdone_eq] at hpre
      simp only [expandMacroList, List.flatMap_append, List.flatMap_singleton, expandSym,
        ← List.append_assoc] at hpre
      have heq_last : (0, t) = last.2 := by
        have := congrArg List.getLast? hpre
        simp at this
        exact this
      have hd_eq : last.2.1 = 0 := by rw [← heq_last]
      have ht_eq : last.2.2 = t := by rw [← heq_last]
      have hne4 : t ≠ 4 := fun h4 => hlast_prop.1 ⟨hd_eq, ht_eq.trans h4⟩
      omega
  exact ⟨t, ht4, hsuf_t⟩

/-- `m ≤ k - 3` whenever `List.replicate m (0, 4)` is an infix of `ts`! -/
theorem m_le_of_no_km2 {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) (hcol : wordCollides k (List.replicate (k - 2) (0, 4)) = true)
    {m : Nat} (hinf : List.replicate m (0, 4) <:+: ts) : m ≤ k - 3 := by
  by_contra hgt
  have hge : k - 2 ≤ m := by omega
  have hsub : List.replicate (k - 2) (0, 4) <:+: List.replicate m (0, 4) := by
    refine ⟨[], List.replicate (m - (k - 2)) (0, 4), ?_⟩
    simp only [List.nil_append, ← List.replicate_add]
    congr 1; omega
  exact not_infix_of_wordCollides hk hk15 hchain hmatch hcol (hsub.trans hinf)

/-- `m = 0` whenever `[(0, t)] ++ List.replicate m (0, 4)` is an infix of `ts` with `t < 4`! -/
theorem m_eq_zero_after_d0 {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) (hcol : ∀ t < 4, wordCollides k [(0, t), (0, 4)] = true)
    {t m : Nat} (ht4 : t < 4) (hinf : ([(0, t)] ++ List.replicate m (0, 4)) <:+: ts) : m = 0 := by
  cases m with
  | zero => rfl
  | succ m' =>
    have hsub : [(0, t), (0, 4)] <:+: ([(0, t)] ++ List.replicate (m' + 1) (0, 4)) :=
      ⟨[], List.replicate m' (0, 4), by simp [List.replicate_succ]⟩
    exact False.elim (not_infix_of_wordCollides hk hk15 hchain hmatch (hcol t ht4) (hsub.trans hinf))

/-- Main inductive simulation of macro-tokens `rem` starting from state `(u, f)` with accumulated score `sc`. -/
theorem simulate_tokens {cert : TropicCert} (hv : CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain cert.k L)
    {ts : List (Nat × Nat)} (hmatch : MatchesWord cert.k ts L) :
    ∀ (rem done : List (Nat × Nat × Nat)) (tail_z : List (Nat × Nat))
      (u f : Nat) (sc : Int),
      ts = expandMacroList done ++ expandMacroList rem ++ tail_z →
      (∀ x ∈ done, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5) →
      (∀ x ∈ rem, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5) →
      StateInv cert u done →
      f < 3 →
      oLe (some sc) (psiInt cert.bias (cert.stPsi u f)) = true →
      ∀ f_end, walkF f ((expandMacroList rem).map Prod.fst) = some f_end →
      ∃ u' : Nat,
        StateInv cert u' (done ++ rem) ∧
        f_end < 3 ∧
        oLe (some (sc + 2 * (cert.q : Int) * ((expandMacroList rem).length : Int) -
            (cert.A : Int) * (((expandMacroList rem).map Prod.fst).sum : Int)))
          (psiInt cert.bias (cert.stPsi u' f_end)) = true
  | [], done, _, u, f, sc, _, _, _, hinv, hf3, hsc, f_end, hwalk => by
    simp only [expandMacroList, List.flatMap_nil, List.map_nil, walkF, Option.some.injEq] at hwalk
    subst hwalk
    refine ⟨u, by simpa using hinv, hf3, ?_⟩
    simpa [expandMacroList] using hsc
  | (m, d, t) :: rest, done, tail_z, u, f, sc, hts, hdone_p, hrem_p, hinv, hf3, hsc, f_end, hwalk => by
    have hcur_p := hrem_p (m, d, t) List.mem_cons_self
    have hrest_p : ∀ x ∈ rest, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5 :=
      fun x hx => hrem_p x (List.mem_cons_of_mem _ hx)
    have hbase := baseCheck_conseq hv.hbase
    have hk3 : 3 ≤ cert.k := by have := hv.hk5; omega
    -- Expand walkF across this single macro-token (m, d, t)
    have hexp_eq : expandMacroList ((m, d, t) :: rest) = expandSym m d t ++ expandMacroList rest := by
      simp [expandMacroList]
    have hmap_sym : (expandSym m d t).map Prod.fst = List.replicate m 0 ++ [d] := by
      simp [expandSym, List.map_replicate]
    rw [hexp_eq, List.map_append, hmap_sym, walkF_append, walkF_expandSym] at hwalk
    cases hnf : nextF f m d with
    | none => rw [hnf] at hwalk; cases hwalk
    | some nf =>
      rw [hnf] at hwalk
      have hnf3 : nf < 3 := by
        unfold nextF at hnf
        split_ifs at hnf <;> cases hnf <;> (try split_ifs) <;> omega
      -- Establish m ≤ k - 3, and m = 0 if f = 1 or stD0 u = true!
      have hinf_m : List.replicate m (0, 4) <:+: ts := by
        refine ⟨expandMacroList done, [(d, t)] ++ expandMacroList rest ++ tail_z, ?_⟩
        rw [hts, hexp_eq]; simp [expandSym, List.append_assoc]
      have hm_le : m ≤ cert.k - 3 := m_le_of_no_km2 hk3 hv.hk15 hchain hmatch hbase.1 hinf_m
      have hm_zero_if_f1 : f = 1 → m = 0 := by
        intro hf1
        unfold nextF at hnf
        by_contra hm0
        have hm1 : m ≥ 1 := by omega
        simp [hf1, hm1] at hnf
      have hm_zero_if_d0 : cert.stD0 u = true → m = 0 := by
        intro hd0
        obtain ⟨tprev, htprev4, ⟨pre0, hpre0⟩⟩ := d0_ends_zero hv hinv hd0 hdone_p
        have hinf2 : ([(0, tprev)] ++ List.replicate m (0, 4)) <:+: ts := by
          refine ⟨pre0, [(d, t)] ++ expandMacroList rest ++ tail_z, ?_⟩
          rw [hts, hexp_eq, ← hpre0]; simp [expandSym, List.append_assoc]
        exact m_eq_zero_after_d0 hk3 hv.hk15 hchain hmatch hbase.2 htprev4 hinf2
      -- Step weight for this token
      have hlen_sym : (expandSym m d t).length = m + 1 := by simp [expandSym]
      have hsum_sym : ((expandSym m d t).map Prod.fst).sum = d := by simp [hmap_sym]
      let w_tok : Int := 2 * (cert.q : Int) * ((m + 1 : Nat) : Int) - (cert.A : Int) * (d : Int)
      -- Advance state to next state v!
      have hstep : ∃ v : Nat, StateInv cert v (done ++ [(m, d, t)]) ∧
          oLe (some (sc + w_tok)) (psiInt cert.bias (cert.stPsi v nf)) = true := by
        by_cases hd_hi : cert.D_track < d
        · -- Case 1: RESET transition to (0, 2)!
          have hd_ge : cert.D_track + 1 ≤ d := by omega
          have hd2 : 2 ≤ d := by have := hv.hD1; omega
          have hnf2 : nf = 2 := by
            unfold nextF at hnf
            split at hnf
            · cases hnf
            · have h0 : (d == 0) = false := S.beq_false_of_ne (by omega)
              have h1 : (d == 1) = false := S.beq_false_of_ne (by omega)
              simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hnf
              exact hnf.symm
          subst hnf2
          refine ⟨0, stateInv_zero cert hv _, ?_⟩
          have hrst := hv.reset_ok hinv.1 hf3
          obtain ⟨pu, hpu, hsc_le⟩ := oLe_some_of_le hsc
          rw [hpu] at hrst
          have hw_le : w_tok ≤ resetWeight cert u f := by
            unfold w_tok resetWeight
            have hm_bound : m + 1 ≤ if f == 1 || cert.stD0 u then 1 else cert.k - 2 := by
              by_cases hc : f = 1 ∨ cert.stD0 u = true
              · have hc_b : (f == 1 || cert.stD0 u) = true := by
                  rcases hc with rfl | hd0 <;> simp [*]
                simp only [hc_b, ↓reduceIte]
                rcases hc with hf1 | hd0
                · have := hm_zero_if_f1 hf1; omega
                · have := hm_zero_if_d0 hd0; omega
              · push Not at hc
                have h1 : (f == 1) = false := S.beq_false_of_ne hc.1
                have h2 : cert.stD0 u = false := Bool.eq_false_iff.mpr hc.2
                rw [h1, h2]; simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
                have := hv.hk5; omega
            have hq_nonneg : (0 : Int) ≤ 2 * (cert.q : Int) := by omega
            have hA_nonneg : (0 : Int) ≤ (cert.A : Int) := Int.natCast_nonneg _
            have h1 : 2 * (cert.q : Int) * ((m + 1 : Nat) : Int) ≤
                2 * (cert.q : Int) * (((if f == 1 || cert.stD0 u then 1 else cert.k - 2) : Nat) : Int) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hm_bound) hq_nonneg
            have h2 : (cert.A : Int) * ((cert.D_track + 1 : Nat) : Int) ≤ (cert.A : Int) * (d : Int) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge) hA_nonneg
            linarith
          obtain ⟨z, hz, hle_z⟩ := oLe_some_of_le hrst
          rw [hz]; simp only [oLe, decide_eq_true_eq]
          linarith
        · -- Case 2: d ≤ D_track! Look up macro-symbol a = symId m d t!
          have hd_le : d ≤ cert.D_track := by omega
          have ha_chk := hv.halpha m hm_le d hd_le t hcur_p.2
          unfold alphaTripleCheck at ha_chk
          have hne04 : (d == 0 && t == 4) = false := by
            have hnot := hcur_p.1
            cases h0 : (d == 0) <;> cases h4 : (t == 4) <;> simp_all
          simp only [hne04, Bool.false_eq_true, ↓reduceIte] at ha_chk
          cases hsid : cert.symId m d t with
          | none =>
            rw [hsid] at ha_chk
            have hinf_tok : expandSym m d t <:+: ts := by
              refine ⟨expandMacroList done, expandMacroList rest ++ tail_z, ?_⟩
              rw [hts, hexp_eq]; simp [List.append_assoc]
            exact False.elim (not_infix_of_wordCollides hk3 hv.hk15 hchain hmatch ha_chk hinf_tok)
          | some a =>
            rw [hsid] at ha_chk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at ha_chk
            obtain ⟨ha_lt, ha_info⟩ := ha_chk
            have hw_eq : symWeight cert a = w_tok := by
              unfold symWeight w_tok; rw [ha_info]
            have hnf_a : nextF f (cert.symInfo a).1 (cert.symInfo a).2.1 = some nf := by
              rw [ha_info]; exact hnf
            have hdone_exp : expandMacroList (done ++ [(m, d, t)]) =
                expandMacroList done ++ expandWord cert.symInfo [a] := by
              simp [expandMacroList, expandWord, ha_info]
            -- Subcase 2a: u = 0 (root)
            by_cases hu0 : u = 0
            · subst hu0
              have hrc := hv.hroot a ha_lt
              unfold rootEdgeCheck at hrc
              cases hov : lookupOv (cert.ovMap 0) a with
              | none =>
                rw [hov] at hrc
                have hd1 := hv.hd1 a ha_lt
                unfold d1Check at hd1
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hd1
                obtain ⟨⟨⟨hd1_pos, hd1_lt⟩, hd1_par⟩, hd1_sym⟩ := hd1
                have hpref_d1 : statePref cert (cert.d1State a) = [a] := by
                  rw [statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) hd1_pos hd1_lt,
                    hd1_par, hd1_sym]
                  rfl
                refine ⟨cert.d1State a, ⟨hd1_lt, ?_⟩, ?_⟩
                · rw [hpref_d1, hdone_exp]; exact List.suffix_append _ _
                · have hep := edgePsiCheck_at hrc hf3 hnf_a
                  rw [hw_eq] at hep
                  obtain ⟨pu, hpu, hsc_le⟩ := oLe_some_of_le hsc
                  rw [hpu] at hep
                  exact oLe_add_of_le hsc_le hep
              | some res =>
                rw [hov] at hrc
                cases res with
                | alive v _ =>
                  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hrc
                  obtain ⟨⟨hv_lt, hv_suf_chk⟩, hep_v⟩ := hrc
                  have hsuf_v : statePref cert v <:+ [a] := by
                    rcases hv_suf_chk with rfl | ⟨hpar0, hsym_a⟩
                    · simp [statePref, statePrefAux]
                    · by_cases hv0 : v = 0
                      · subst hv0; simp [statePref, statePrefAux]
                      · rw [statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) (by omega) hv_lt,
                          hpar0, hsym_a]
                        simp [statePref, statePrefAux]
                  refine ⟨v, ⟨hv_lt, ?_⟩, ?_⟩
                  · rw [hdone_exp]
                    exact (expandWord_suffix hsuf_v).trans (List.suffix_append _ _)
                  · have hep := edgePsiCheck_at hep_v hf3 hnf_a
                    rw [hw_eq] at hep
                    obtain ⟨pu, hpu, hsc_le⟩ := oLe_some_of_le hsc
                    rw [hpu] at hep
                    exact oLe_add_of_le hsc_le hep
                | dead fid =>
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
                  obtain ⟨hfid, hsuf_f⟩ := hrc
                  have hsuf_w : cert.cegarForb fid <:+ [a] := by
                    simpa [statePref, statePrefAux] using
                      suffix_of_matchesRevSuffix (fun _ h1 h2 => hv.par_lt h1 h2) hv.hV hsuf_f
                  have hinf_f : expandWord cert.symInfo (cert.cegarForb fid) <:+: ts := by
                    have hs1 : expandWord cert.symInfo (cert.cegarForb fid) <:+ expandMacroList (done ++ [(m, d, t)]) := by
                      rw [hdone_exp]
                      exact (expandWord_suffix hsuf_w).trans (List.suffix_append _ _)
                    obtain ⟨pre1, hpre1⟩ := hs1
                    refine ⟨pre1, expandMacroList rest ++ tail_z, ?_⟩
                    rw [hts, hexp_eq]; simp only [← List.append_assoc]
                    rw [hpre1, hdone_exp]; simp [expandWord, ha_info, List.append_assoc]
                  exact False.elim (not_infix_of_checkWitness hk3 hv.hk15 hchain hmatch (hv.hcegar fid hfid) hinf_f)
            · -- Subcase 2b: u > 0
              have hu_pos : 0 < u := by omega
              let s := cert.stSym u
              have hs_lt : s < cert.ALPHA := hv.sym_lt hu_pos hinv.1
              have hua_suf : expandWord cert.symInfo (statePref cert u ++ [a]) <:+
                  expandMacroList (done ++ [(m, d, t)]) := by
                rw [expandWord_append, hdone_exp]
                exact suffix_trans_append (List.suffix_refl _) hinv.2
              cases hpm : cert.pairMode s a with
              | zero =>
                -- depth1Ok!
                have hp0 := hv.hpairs s hs_lt a ha_lt
                unfold pairDepth1Check at hp0
                rw [hpm] at hp0
                simp only [beq_self_eq_true, ↓reduceIte] at hp0
                have hd1 := hv.hd1 a ha_lt
                unfold d1Check at hd1
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hd1
                obtain ⟨⟨⟨hd1_pos, hd1_lt⟩, hd1_par⟩, hd1_sym⟩ := hd1
                have hpref_d1 : statePref cert (cert.d1State a) = [a] := by
                  rw [statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) hd1_pos hd1_lt,
                    hd1_par, hd1_sym]
                  rfl
                refine ⟨cert.d1State a, ⟨hd1_lt, ?_⟩, ?_⟩
                · rw [hpref_d1, hdone_exp]; exact List.suffix_append _ _
                · have hep := edgePsiCheck_at hp0 hf3 hnf_a
                  rw [hw_eq] at hep
                  have hle_m := oLe_trans_some hsc (hv.le_maxPsi hu_pos hinv.1 hf3)
                  obtain ⟨pm, hpm_eq, hsc_le⟩ := oLe_some_of_le hle_m
                  rw [hpm_eq] at hep
                  exact oLe_add_of_le hsc_le hep
              | succ pm' =>
                cases pm' with
                | zero =>
                  -- pairMode s a = 1: forb2 collision!
                  have hf2 := hv.hforb2 s hs_lt a ha_lt hpm
                  have hpref_u := statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) hu_pos hinv.1
                  have hsa_suf : [s, a] <:+ statePref cert u ++ [a] := by
                    refine ⟨statePref cert (cert.stPar u), ?_⟩
                    rw [hpref_u]; simp [s]
                  have hexp_sa : expandWord cert.symInfo [s, a] =
                      (let (ms, ds, ts') := cert.symInfo s; let (ma, da, ta) := cert.symInfo a;
                       expandSym ms ds ts' ++ expandSym ma da ta) := by
                    simp [expandWord]
                  have hinf_sa : expandWord cert.symInfo [s, a] <:+: ts := by
                    have hs1 := (expandWord_suffix hsa_suf).trans hua_suf
                    obtain ⟨pre1, hpre1⟩ := hs1
                    refine ⟨pre1, expandMacroList rest ++ tail_z, ?_⟩
                    rw [hts, hexp_eq]; simp only [← List.append_assoc]
                    rw [hpre1, hdone_exp]; simp [expandWord, ha_info, List.append_assoc]
                  rw [hexp_sa] at hinf_sa
                  exact False.elim (not_infix_of_wordCollides hk3 hv.hk15 hchain hmatch hf2 hinf_sa)
                | succ pm'' =>
                  -- pairMode s a ≥ 2: explicit override via ovList + failIter / matchesRevSuffix!
                  have hmem_ov : a ∈ cert.ovList s := by
                    have hp2 := hv.hpairs s hs_lt a ha_lt
                    unfold pairDepth1Check at hp2
                    rw [hpm] at hp2
                    have hne0 : ((pm'' + 1 + 1) == 0) = false := S.beq_false_of_ne (by omega)
                    have hne1 : ((pm'' + 1 + 1) == 1) = false := S.beq_false_of_ne (by omega)
                    simp only [hne0, hne1, Bool.false_eq_true, ↓reduceIte] at hp2
                    exact List.contains_iff_mem.mp hp2
                  have hov_all := hv.hover u hinv.1
                  unfold checkOverridesState at hov_all
                  have hu_ne0 : (u == 0) = false := S.beq_false_of_ne hu0
                  simp only [hu_ne0, Bool.false_eq_true, ↓reduceIte] at hov_all
                  have hov := List.all_eq_true.mp hov_all a hmem_ov
                  unfold overrideCheckOne at hov
                  cases hg : lookupOv (cert.ovMap u) a with
                  | none => rw [hg] at hov; cases hov
                  | some res =>
                    rw [hg] at hov
                    cases res with
                    | alive v steps =>
                      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hov
                      obtain ⟨⟨hv_lt, hv_suf_chk⟩, hep_v⟩ := hov
                      have hsuf_v : statePref cert v <:+ statePref cert u ++ [a] := by
                        rcases hv_suf_chk with rfl | ⟨hvsym, hfail_eq⟩
                        · simp [statePref, statePrefAux]
                        · by_cases hv0 : v = 0
                          · subst hv0; simp [statePref, statePrefAux]
                          · have hpv := statePref_pos cert (fun _ h1 h2 => hv.par_lt h1 h2) (by omega) hv_lt
                            have hf_suf := (hv.failIter_suffix steps u hinv.1).2
                            rw [hpv, hvsym, ← hfail_eq]
                            exact suffix_trans_append (List.suffix_refl _) hf_suf
                      refine ⟨v, ⟨hv_lt, (expandWord_suffix hsuf_v).trans hua_suf⟩, ?_⟩
                      have hep := edgePsiCheck_at hep_v hf3 hnf_a
                      rw [hw_eq] at hep
                      obtain ⟨pu, hpu, hsc_le⟩ := oLe_some_of_le hsc
                      rw [hpu] at hep
                      exact oLe_add_of_le hsc_le hep
                    | dead fid =>
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hov
                      obtain ⟨hfid, hsuf_f⟩ := hov
                      have hsuf_w : cert.cegarForb fid <:+ statePref cert u ++ [a] :=
                        suffix_of_matchesRevSuffix (fun _ h1 h2 => hv.par_lt h1 h2) hinv.1 hsuf_f
                      have hinf_f : expandWord cert.symInfo (cert.cegarForb fid) <:+: ts := by
                        have hs1 := (expandWord_suffix hsuf_w).trans hua_suf
                        obtain ⟨pre1, hpre1⟩ := hs1
                        refine ⟨pre1, expandMacroList rest ++ tail_z, ?_⟩
                        rw [hts, hexp_eq]; simp only [← List.append_assoc]
                        rw [hpre1, hdone_exp]; simp [expandWord, ha_info, List.append_assoc]
                      exact False.elim (not_infix_of_checkWitness hk3 hv.hk15 hchain hmatch (hv.hcegar fid hfid) hinf_f)
      -- Complete induction on `rest`!
      obtain ⟨v, hinv_v, hsc_v⟩ := hstep
      have hts' : ts = expandMacroList (done ++ [(m, d, t)]) ++ expandMacroList rest ++ tail_z := by
        rw [hts, hexp_eq]
        simp [expandMacroList, List.append_assoc]
      have hdone_p' : ∀ x ∈ done ++ [(m, d, t)], ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5 := by
        intro x hx
        rcases List.mem_append.mp hx with h1 | h1
        · exact hdone_p x h1
        · rw [List.mem_singleton.mp h1]; exact hcur_p
      obtain ⟨u', hinv_u', hf_end3, hsc_end⟩ :=
        simulate_tokens hv hchain hmatch rest (done ++ [(m, d, t)]) tail_z v nf (sc + w_tok)
          hts' hdone_p' hrest_p hinv_v hnf3 hsc_v f_end hwalk
      refine ⟨u', by simpa [List.append_assoc] using hinv_u', hf_end3, ?_⟩
      -- Match score algebra!
      have hlen_tot : (expandMacroList ((m, d, t) :: rest)).length =
          (m + 1) + (expandMacroList rest).length := by
        rw [hexp_eq, List.length_append, hlen_sym]
      have hsum_tot : ((expandMacroList ((m, d, t) :: rest)).map Prod.fst).sum =
          d + ((expandMacroList rest).map Prod.fst).sum := by
        rw [hexp_eq, List.map_append, List.sum_append, hsum_sym]
      have hsc_eq : sc + w_tok + 2 * (cert.q : Int) * ((expandMacroList rest).length : Int) -
          (cert.A : Int) * (((expandMacroList rest).map Prod.fst).sum : Int) =
          sc + 2 * (cert.q : Int) * ((expandMacroList ((m, d, t) :: rest)).length : Int) -
          (cert.A : Int) * (((expandMacroList ((m, d, t) :: rest)).map Prod.fst).sum : Int) := by
        rw [hlen_tot, hsum_tot]; unfold w_tok; push_cast; ring
      rw [← hsc_eq]
      exact hsc_end

/-- **`WStatement` from a valid `TropicCEGAR-Macro` certificate!** -/
theorem wstatement_of_tropic {cert : TropicCert} (hv : CertValid cert) :
    S.WStatement cert.k cert.cn cert.bn cert.q := by
  intro L hchain hwin
  have hLne : L ≠ [] := by
    obtain ⟨x, rest, hne, _⟩ := hwin.first_partial
    intro h0; rw [h0] at hne; simp [S.wdef] at hne
  have hk3 : 3 ≤ cert.k := by have := hv.hk5; omega
  obtain ⟨ts, d_last, hwdef, ht5, hmatch⟩ := extract_transitions hk3 hv.hk15 L hLne hchain
  have hd_last_pos : 0 < d_last := by
    obtain ⟨init, y, hy, hypos⟩ := hwin.last_partial
    rw [hwdef] at hy
    have heq : d_last = y := ChainC.last_eq_of_concat_eq hy
    omega
  have hwalk_all : walkF 1 (S.wdef cert.k L) = some 2 := walkF_isWindow hwin
  -- Split ts into macro-tokens ms + trailing mt copies of (0, 4)
  cases hsp : splitMacroAux 0 ts with
  | mk ms mt =>
    have hts_eq : ts = expandMacroList ms ++ List.replicate mt (0, 4) := by
      have h := splitMacroAux_expand 0 ts
      rw [hsp] at h
      simpa using h
    have hms_p : ∀ x ∈ ms, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5 := by
      have h := splitMacroAux_props 0 ts ht5
      rw [hsp] at h
      exact h
    -- Split walkF 1 (wdef L) = walkF 1 (ms_defs ++ replicate mt 0 ++ [d_last]) = some 2!
    rw [hwdef, hts_eq, List.map_append, List.map_replicate, List.append_assoc, walkF_append] at hwalk_all
    cases hwf_ms : walkF 1 ((expandMacroList ms).map Prod.fst) with
    | none => rw [hwf_ms] at hwalk_all; cases hwalk_all
    | some f_end =>
      rw [hwf_ms] at hwalk_all
      -- Simulate ms from (0, 1) with sc = 0!
      have hts_sim : ts = expandMacroList [] ++ expandMacroList ms ++ List.replicate mt (0, 4) := by
        simpa [expandMacroList] using hts_eq
      obtain ⟨u', hinv_u', hf_end3, hsc_end⟩ :=
        simulate_tokens hv hchain hmatch ms [] (List.replicate mt (0, 4)) 0 1 0
          hts_sim (by simp) hms_p (stateInv_zero cert hv []) (by omega) hv.root_ok.2 f_end hwf_ms
      obtain ⟨pu_int, hpu_int, hsc_le⟩ := oLe_some_of_le hsc_end
      cases hpu_nat : cert.stPsi u' f_end with
      | none => rw [hpu_nat] at hpu_int; simp [psiInt] at hpu_int
      | some pu_n =>
      rw [hpu_nat] at hpu_int
      have hpu_val : pu_int = (pu_n : Int) - (cert.bias : Int) := by
        simp [psiInt] at hpu_int; exact hpu_int.symm
      subst hpu_val
      have hbase := baseCheck_conseq hv.hbase
      have hmt_le : mt ≤ cert.k - 3 :=
        m_le_of_no_km2 hk3 hv.hk15 hchain hmatch hbase.1 ⟨expandMacroList ms, [], by rw [hts_eq]; simp⟩
      -- Final piece + trailing mt zeros bound via endBoundCheck!
      have hend := hv.end_ok hinv_u'.1 hf_end3
      unfold endBoundCheck at hend
      rw [hpu_nat] at hend
      simp only [Bool.and_eq_true] at hend
      -- Compute total length and total sum of wdef L
      have hlen_L : (S.wdef cert.k L).length = (expandMacroList ms).length + mt + 1 := by
        rw [hwdef, hts_eq]; simp; omega
      have hsum_L : (S.wdef cert.k L).sum = ((expandMacroList ms).map Prod.fst).sum + d_last := by
        rw [hwdef, hts_eq]; simp [List.map_append, List.sum_append]
      have hA_nonneg : (0 : Int) ≤ (cert.A : Int) := Int.natCast_nonneg _
      have hq_nonneg : (0 : Int) ≤ 2 * (cert.q : Int) := by omega
      -- Analyze mt = 0 vs mt ≥ 1
      have hfinal_int :
          2 * (cert.q : Int) * ((S.wdef cert.k L).length : Int) +
            2 * (cert.q : Int) * ((cert.k - 4 : Nat) : Int) -
            (cert.A : Int) * ((S.wdef cert.k L).sum : Int) ≤ (cert.bn : Int) := by
        rw [hlen_L, hsum_L]
        simp only [Nat.cast_add, Nat.cast_one]
        by_cases hmt0 : mt = 0
        · subst hmt0
          simp only [List.replicate_zero, List.nil_append, walkF] at hwalk_all
          simp only [Nat.cast_zero, add_zero]
          simp only [zero_add] at hsc_le
          by_cases hf2 : f_end = 2
          · subst hf2
            have h1 : (cert.A : Int) * 1 ≤ (cert.A : Int) * (d_last : Int) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hd_last_pos) hA_nonneg
            have hA_nat : pu_n + 2 * cert.q + 2 * cert.q * (cert.k - 4) ≤
                cert.bias + cert.bn + 1 * cert.A := by
              have hA_b := hend.1
              simp only [beq_self_eq_true, ↓reduceIte] at hA_b
              exact Nat.le_of_ble_eq_true hA_b
            have hA_int : (pu_n : Int) + 2 * (cert.q : Int) + 2 * (cert.q : Int) * ((cert.k - 4 : Nat) : Int) ≤
                (cert.bias : Int) + (cert.bn : Int) + (cert.A : Int) := by
              have : ((pu_n + 2 * cert.q + 2 * cert.q * (cert.k - 4) : Nat) : Int) ≤
                  ((cert.bias + cert.bn + 1 * cert.A : Nat) : Int) := by exact_mod_cast hA_nat
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at this
              linarith
            linarith
          · -- f_end ≠ 2 and walkF f_end [d_last] = some 2 forces d_last ≥ 2!
            have hd_ge2 : 2 ≤ d_last := by
              by_contra hlt
              have hd1 : d_last = 1 := by omega
              subst hd1
              unfold stepF at hwalk_all
              have hne2 : (f_end == 2) = false := S.beq_false_of_ne hf2
              simp [hne2] at hwalk_all
            have h2 : (cert.A : Int) * 2 ≤ (cert.A : Int) * (d_last : Int) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge2) hA_nonneg
            have hA_nat : pu_n + 2 * cert.q + 2 * cert.q * (cert.k - 4) ≤
                cert.bias + cert.bn + 2 * cert.A := by
              have hA_b := hend.1
              have hne2 : (f_end == 2) = false := S.beq_false_of_ne hf2
              simp only [hne2, Bool.false_eq_true, ↓reduceIte] at hA_b
              exact Nat.le_of_ble_eq_true hA_b
            have hA_int : (pu_n : Int) + 2 * (cert.q : Int) + 2 * (cert.q : Int) * ((cert.k - 4 : Nat) : Int) ≤
                (cert.bias : Int) + (cert.bn : Int) + 2 * (cert.A : Int) := by
              have : ((pu_n + 2 * cert.q + 2 * cert.q * (cert.k - 4) : Nat) : Int) ≤
                  ((cert.bias + cert.bn + 2 * cert.A : Nat) : Int) := by exact_mod_cast hA_nat
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
              linarith
            linarith
        · -- mt ≥ 1: cannot have f_end = 1 or stD0 u' = true, and d_last ≥ 2!
          have hmt1 : 1 ≤ mt := by omega
          dsimp only at hwalk_all
          rw [walkF_expandSym] at hwalk_all
          have hf_ne1 : f_end ≠ 1 := by
            intro hf1; unfold nextF at hwalk_all; simp [hf1, hmt1] at hwalk_all
          have hd0_false : cert.stD0 u' = false := by
            by_contra hd0t
            have hd0' : cert.stD0 u' = true := Bool.eq_true_of_not_eq_false hd0t
            obtain ⟨tprev, htprev4, ⟨pre0, hpre0⟩⟩ := d0_ends_zero hv (by simpa using hinv_u') hd0' hms_p
            have hinf2 : ([(0, tprev)] ++ List.replicate mt (0, 4)) <:+: ts := by
              refine ⟨pre0, [], ?_⟩
              rw [hts_eq, ← hpre0]; simp [List.append_assoc]
            exact hmt0 (m_eq_zero_after_d0 hk3 hv.hk15 hchain hmatch hbase.2 htprev4 hinf2)
          have hd_ge2 : 2 ≤ d_last := by
            by_contra hlt
            have hd1 : d_last = 1 := by omega
            subst hd1
            unfold nextF at hwalk_all
            have hne1 : (f_end == 1) = false := S.beq_false_of_ne hf_ne1
            simp [hne1, hmt1] at hwalk_all
          have hB_nat : pu_n + 2 * cert.q * (cert.k - 2) + 2 * cert.q * (cert.k - 4) ≤
              cert.bias + cert.bn + 2 * cert.A := by
            have hB_b := hend.2
            have hne1 : (f_end == 1) = false := S.beq_false_of_ne hf_ne1
            simp only [hne1, hd0_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hB_b
            exact Nat.le_of_ble_eq_true hB_b
          have hB_int : (pu_n : Int) + 2 * (cert.q : Int) * ((cert.k - 2 : Nat) : Int) +
              2 * (cert.q : Int) * ((cert.k - 4 : Nat) : Int) ≤
              (cert.bias : Int) + (cert.bn : Int) + 2 * (cert.A : Int) := by
            have : ((pu_n + 2 * cert.q * (cert.k - 2) + 2 * cert.q * (cert.k - 4) : Nat) : Int) ≤
                ((cert.bias + cert.bn + 2 * cert.A : Nat) : Int) := by exact_mod_cast hB_nat
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
            linarith
          have hmt_bound : 2 * (cert.q : Int) * ((mt + 1 : Nat) : Int) ≤
              2 * (cert.q : Int) * ((cert.k - 2 : Nat) : Int) :=
            mul_le_mul_of_nonneg_left (by have := hv.hk5; exact_mod_cast (by omega : mt + 1 ≤ cert.k - 2)) hq_nonneg
          have hd_bound : 2 * (cert.A : Int) ≤ (cert.A : Int) * (d_last : Int) := by
            have := mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge2 : (2 : Int) ≤ d_last) hA_nonneg
            linarith
          simp only [Nat.cast_add, Nat.cast_one] at hmt_bound
          simp only [zero_add] at hsc_le
          linarith
      -- Convert back to Nat WindowBound!
      unfold ChainC.WindowBound
      have hA_cast : (cert.A : Int) = (cert.q : Int) * ((cert.k - 3 : Nat) : Int) - (cert.cn : Int) := by
        have hle : cert.cn ≤ cert.q * (cert.k - 3) := by
          have := hv.hcn; have := hv.hk5
          calc cert.cn ≤ cert.q * (cert.k - 5) := hv.hcn
            _ ≤ cert.q * (cert.k - 3) := Nat.mul_le_mul_left _ (by omega)
        rw [hv.hA, Nat.cast_sub hle]; simp only [Nat.cast_mul]
      rw [hA_cast] at hfinal_int
      have hnat_int :
          ((cert.q * (2 * (S.wdef cert.k L).length + 2 * (cert.k - 4)) +
            cert.cn * (S.wdef cert.k L).sum : Nat) : Int) ≤
          ((cert.q * ((cert.k - 3) * (S.wdef cert.k L).sum) + cert.bn : Nat) : Int) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact_mod_cast hnat_int

/-- **Main Pure-Kernel Theorem:** Any valid `TropicCEGAR-Macro` certificate satisfying `ConditionsC`
proves `∀ w : List (Fin k), Covers w → boundC k cn bn q ≤ w.length`! -/
theorem covers_length_ge_boundC_of_tropic {cert : TropicCert} (hv : CertValid cert)
    (hcond : ConditionsC cert.k cert.cn cert.bn cert.q) :
    ∀ w : List (Fin cert.k), Covers w → boundC cert.k cert.cn cert.bn cert.q ≤ w.length :=
  covers_length_ge_boundC_of_model hv.hk5 hcond (modelStatement_of_wstatement (wstatement_of_tropic hv))

end Tropic
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.Tropic.covers_length_ge_boundC_of_tropic


