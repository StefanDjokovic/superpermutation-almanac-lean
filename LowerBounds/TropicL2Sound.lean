import LowerBounds.TropicL2Core
import LowerBounds.SBridgeTheoremC
import LowerBounds.SModel
import LowerBounds.SSound

/-!
# Pure-Kernel Soundness Bridge for Level-2 `TropicCEGAR` Certificates (`k = 13`)

Proves `covers_length_ge_boundC_of_tropicL2`: any valid exact-integer Level-2
`TropicCEGAR` certificate (verified purely by `decide +kernel` with zero `native_decide`
and zero `sorry`) implies `S.WStatement 13 cert.cn cert.bn cert.q`, and therefore
`∀ w : List (Fin 13), Covers w → boundC 13 cert.cn cert.bn cert.q ≤ w.length`.
-/

namespace SuperpermLowerBounds
namespace TropicL2

open Hunter PreimageChain SuperpermutationBounds S ChainC

/-! ### 1. Range checks and `Option Int` potential ordering -/

theorem checkRangeAux_spec {lo : Nat} {p : Nat → Bool} :
    ∀ {n : Nat}, checkRangeAux lo p n = true → ∀ i, lo ≤ i → i < lo + n → p i = true
  | 0, _, _, h1, h2 => by omega
  | n + 1, h, i, h1, h2 => by
    simp only [checkRangeAux, Bool.and_eq_true] at h
    by_cases heq : i = lo + n
    · rw [heq]; exact h.1
    · exact checkRangeAux_spec h.2 i h1 (by omega)

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

/-- Mathematical interpretation of shifted `Option Nat` potential as `Option Int`. -/
def psiInt (bias : Nat) : Option Nat → Option Int
  | none => none
  | some x => some ((x : Int) - (bias : Int))

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

/-! ### 2. `w3Code`, `MatchesWord`, `walkWordFast`, and `checkWitness` soundness -/

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
        | (refine ⟨4, by omega, ?_⟩; dsimp only [w3Code]; rw [hpY, hpa, hpb, hpc]; simp only []; done))

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
    have hu : S.PermW k (P.getLast hP) := hchain.words P List.mem_cons_self _ (List.getLast_mem hP)
    have hv : S.PermW k (Q.head hQ) := hchain.words Q (by simp) _ (List.head_mem hQ)
    have hlink : S.WLink k 3 (P.getLast hP) (Q.head hQ) :=
      (List.isChain_cons_cons.mp hchain.seams).1 hP hQ
    have hxp : S.PermW k ((P.getLast hP).rotate (k - 1)) := hu.rotate _
    obtain ⟨a, b, c, Y, t0, t1, t2, hxe, hYl, hv2, ht0, ht1, ht2, h01, h02, h12⟩ :=
      S.seam_cases hk hxp hv hlink
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

theorem walkWordFast_append (k : Nat) (w1 w2 : List (Nat × Nat)) (cur : Nat) :
    walkWordFast k (w1 ++ w2) cur = walkWordFast k w2 (walkWordFast k w1 cur) := by
  induction w1 generalizing cur with
  | nil => rfl
  | cons dt rest ih => rcases dt with ⟨d, t⟩; exact ih _

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
      rw [List.getLast_eq_getElem]; congr 1; omega
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

theorem pairwise_flatten_distinct_pieces {α : Type} {R : α → α → Prop}
    {L : List (List α)} (hpw : List.Pairwise R L.flatten)
    {i1 i2 : Nat} (hlt : i1 < i2) (hi2 : i2 < L.length)
    {x y : α} (hx : x ∈ L[i1]'(by omega)) (hy : y ∈ L[i2]) : R x y := by
  have hsplit : L = L.take i1 ++ [L[i1]'(by omega)] ++
      ((L.drop (i1 + 1)).take (i2 - i1 - 1) ++ [L[i2]] ++ L.drop (i2 + 1)) := by
    have h1 : L = L.take i1 ++ L.drop i1 := (List.take_append_drop i1 L).symm
    have h2 : L.drop i1 = L[i1]'(by omega) :: L.drop (i1 + 1) := List.drop_eq_getElem_cons (by omega)
    have h3 : L.drop (i1 + 1) = (L.drop (i1 + 1)).take (i2 - i1 - 1) ++ (L.drop (i1 + 1)).drop (i2 - i1 - 1) :=
      (List.take_append_drop _ _).symm
    have h4 : (L.drop (i1 + 1)).drop (i2 - i1 - 1) = L.drop i2 := by
      rw [List.drop_drop]; congr 1; omega
    have h5 : L.drop i2 = L[i2] :: L.drop (i2 + 1) := List.drop_eq_getElem_cons hi2
    conv_lhs => rw [h1, h2, h3, h4, h5]
    simp only [List.append_assoc, List.singleton_append]
  rw [hsplit] at hpw
  simp only [List.flatten_append, List.flatten_singleton, List.pairwise_append] at hpw
  exact hpw.2.2 x (List.mem_append_right _ hx) y (List.mem_append_left _ (List.mem_append_right _ hy))

/-- Generalized two-point collision contradiction: if two distinct positions `(i1, j1)` and
`(i2, j2)` in `w` have equal `S.canon k` codes, no valid `IsWChain` can match `w`! -/
theorem not_matchesWord_of_two_point {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {w : List (Nat × Nat)} {i1 j1 i2 j2 : Nat}
    (h12 : i1 < i2) (hi2 : i2 ≤ w.length)
    (hj1 : j1 < k - 1 - (w.getD i1 (0, 0)).1)
    (hj2 : if i2 < w.length then j2 < k - 1 - (w.getD i2 (0, 0)).1 else j2 = 0)
    (hcanon : S.canon k (pieceAdvance k j1 (walkWordFast k (w.take i1) (S.idc k))) =
              S.canon k (pieceAdvance k j2 (walkWordFast k (w.take i2) (S.idc k))))
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
  have hm1 : MatchesWord k (w.take i1) L' :=
    matchesWord_prefix (w.take i1) (w.drop i1) L' (by simpa using hmatch')
  have hm2 : MatchesWord k (w.take i2) L' :=
    matchesWord_prefix (w.take i2) (w.drop i2) L' (by simpa using hmatch')
  obtain ⟨hw1, _, hP1, hP0, hc1_hd⟩ := walkWordFast_valid hk hk15 (w.take i1) L' hchain' hm1
  obtain ⟨hw2, _, hP2, _, hc2_hd⟩ := walkWordFast_valid hk hk15 (w.take i2) L' hchain' hm2
  have hlen_t1 : (w.take i1).length = i1 := by rw [List.length_take]; omega
  have hlen_t2 : (w.take i2).length = i2 := by rw [List.length_take]; omega
  have hi1_L : i1 < L'.length := by omega
  have hi2_L : i2 < L'.length := by omega
  have hP0_code : S.code (L'[0].head hP0) = S.idc k := by
    have h0eq : L'[0] = L'.head hL' := (List.head_eq_getElem_zero hL').symm
    simpa [h0eq] using hcode_id
  have he1_eq : S.code (L'[i1].head (by simpa [hlen_t1] using hP1)) = walkWordFast k (w.take i1) (S.idc k) := by
    simpa [hlen_t1, hP0_code] using hc1_hd
  have he2_eq : S.code (L'[i2].head (by simpa [hlen_t2] using hP2)) = walkWordFast k (w.take i2) (S.idc k) := by
    simpa [hlen_t2, hP0_code] using hc2_hd
  obtain ⟨_, hlen1⟩ := matchesWord_piece_len w L' i1 hchain' hmatch' (by omega)
  have hj1_lt : j1 < L'[i1].length := by omega
  have hj2_lt : j2 < L'[i2].length := by
    by_cases hi2w : i2 < w.length
    · simp only [hi2w, ↓reduceIte] at hj2
      obtain ⟨_, hlen2⟩ := matchesWord_piece_len w L' i2 hchain' hmatch' hi2w
      omega
    · simp only [hi2w, ↓reduceIte] at hj2
      have hne2 : L'[i2] ≠ [] := hchain'.pieces_ne _ (List.getElem_mem hi2_L)
      have hpos2 : 0 < L'[i2].length := List.length_pos_of_ne_nil hne2
      omega
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
  have hc2_eq : S.code (L'[i2][j2]) = pieceAdvance k j2 (walkWordFast k (w.take i2) (S.idc k)) := by
    rw [hcode_piece i2 hi2_L j2 hj2_lt (by simpa [hlen_t2] using hP2), he2_eq]
  rw [← hc1_eq, ← hc2_eq] at hcanon
  have hp1 : S.PermW k (L'[i1][j1]) := hchain'.words _ (List.getElem_mem hi1_L) _ (List.getElem_mem hj1_lt)
  have hp2 : S.PermW k (L'[i2][j2]) := hchain'.words _ (List.getElem_mem hi2_L) _ (List.getElem_mem hj2_lt)
  have hrot : L'[i1][j1] ~r L'[i2][j2] :=
    S.isRotated_of_canon_eq hp1.2.1 hp2.2.1 (hp1.lt16 hk15) (hp2.lt16 hk15) hcanon
  exact pairwise_flatten_distinct_pieces hchain'.classes h12 hi2_L
    (List.getElem_mem hj1_lt) (List.getElem_mem hj2_lt) hrot

theorem not_infix_of_two_point {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) {w : List (Nat × Nat)} {i1 j1 i2 j2 : Nat}
    (h12 : i1 < i2) (hi2 : i2 ≤ w.length)
    (hj1 : j1 < k - 1 - (w.getD i1 (0, 0)).1)
    (hj2 : if i2 < w.length then j2 < k - 1 - (w.getD i2 (0, 0)).1 else j2 = 0)
    (hcanon : S.canon k (pieceAdvance k j1 (walkWordFast k (w.take i1) (S.idc k))) =
              S.canon k (pieceAdvance k j2 (walkWordFast k (w.take i2) (S.idc k))))
    (hinf : w <:+: ts) : False := by
  obtain ⟨pre, post, rfl⟩ := hinf
  have h1 : MatchesWord k (w ++ post) (L.drop pre.length) := by
    rw [List.append_assoc] at hmatch
    exact matchesWord_drop pre (w ++ post) L hmatch
  exact not_matchesWord_of_two_point hk hk15 h12 hi2 hj1 hj2 hcanon
    (hchain.infix (drop_infix pre.length L)) (matchesWord_prefix w post _ h1)

theorem not_infix_of_checkWitness {k : Nat} (hk : 3 ≤ k) (hk15 : k ≤ 15)
    {L : List (List (List Nat))} (hchain : S.IsWChain k L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord k ts L) {w : List (Nat × Nat)} {wit : Nat × Nat × Nat × Nat}
    (hwit : checkWitness k w wit = true) (hinf : w <:+: ts) : False := by
  rcases wit with ⟨i1, j1, i2, j2⟩
  unfold checkWitness at hwit
  cases hr : (Nat.ble (i1 + 1) i2 && Nat.ble i2 w.length) with
  | false => simp [hr] at hwit
  | true =>
    simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwit
    simp only [Bool.and_eq_true] at hr
    have h12 : i1 < i2 := by have := Nat.le_of_ble_eq_true hr.1; omega
    have hi2 : i2 ≤ w.length := Nat.le_of_ble_eq_true hr.2
    cases hok : (Nat.ble (j1 + 1) (k - 1 - (w.getD i1 (0, 0)).1) &&
        (if Nat.ble (i2 + 1) w.length then Nat.ble (j2 + 1) (k - 1 - (w.getD i2 (0, 0)).1) else Nat.beq j2 0)) with
    | false =>
      change (if !((Nat.ble (j1 + 1) (k - 1 - (w.getD i1 (0, 0)).1) &&
        (if Nat.ble (i2 + 1) w.length then Nat.ble (j2 + 1) (k - 1 - (w.getD i2 (0, 0)).1) else Nat.beq j2 0))) = true then false else _) = true at hwit
      rw [hok] at hwit; cases hwit
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwit
      have hcan := Nat.eq_of_beq_eq_true hwit
      simp only [Bool.and_eq_true] at hok
      have hj1 : j1 < k - 1 - (w.getD i1 (0, 0)).1 := by have := Nat.le_of_ble_eq_true hok.1; omega
      have hj2 : if i2 < w.length then j2 < k - 1 - (w.getD i2 (0, 0)).1 else j2 = 0 := by
        by_cases hlt : i2 < w.length
        · have hb : Nat.ble (i2 + 1) w.length = true := Nat.ble_eq_true_of_le (by omega)
          have h2 := hok.2; simp only [hb, ↓reduceIte] at h2
          simp only [hlt, ↓reduceIte]; have := Nat.le_of_ble_eq_true h2; omega
        · have hb : Nat.ble (i2 + 1) w.length = false := by
            cases hc : Nat.ble (i2 + 1) w.length with
            | false => rfl
            | true => have := Nat.le_of_ble_eq_true hc; omega
          have h2 := hok.2; simp only [hb, Bool.false_eq_true, ↓reduceIte] at h2
          simp only [hlt, ↓reduceIte]; exact Nat.eq_of_beq_eq_true h2
      have htake : w.take i2 = w.take i1 ++ (w.drop i1).take (i2 - i1) := by
        have := List.take_append_drop i1 (w.take i2)
        rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take] at this
        exact this.symm
      rw [← walkWordFast_append, ← htake] at hcan
      exact not_infix_of_two_point hk hk15 hchain hmatch h12 hi2 hj1 hj2 hcan hinf

/-! ### 3. `S_{13}` Group Homomorphism (`compose13` = right multiplication in `S_{13}`) -/

/-- List-level `w3` transition on a 13-element exit word. -/
def w3Perm (x : List Nat) (t : Nat) : List Nat :=
  match x with
  | a :: b :: c :: Y =>
    match t with
    | 0 => Y ++ [a, c, b]
    | 1 => Y ++ [b, a, c]
    | 2 => Y ++ [b, c, a]
    | 3 => Y ++ [c, a, b]
    | _ => Y ++ [c, b, a]
  | _ => x

/-- List-level `walkWordFast` on a 13-element permutation word. -/
def walkWordPerm : List (Nat × Nat) → List Nat → List Nat
  | [], u => u
  | (d, t) :: rest, u =>
    let endP := u.dropLast.rotate (11 - d) ++ [u.getLastD 0]
    walkWordPerm rest (w3Perm (endP.rotate 12) t)

theorem w3Perm_map (x : List Nat) (t : Nat) (f : Nat → Nat) :
    w3Perm (x.map f) t = (w3Perm x t).map f := by
  cases x with
  | nil => rfl
  | cons a r1 => cases r1 with
    | nil => rfl
    | cons b r2 => cases r2 with
      | nil => rfl
      | cons c Y => cases t with
        | zero => simp [w3Perm]
        | succ t => cases t with
          | zero => simp [w3Perm]
          | succ t => cases t with
            | zero => simp [w3Perm]
            | succ t => cases t with
              | zero => simp [w3Perm]
              | succ t => simp [w3Perm]

theorem walkWordPerm_map (f : Nat → Nat) :
    ∀ (w : List (Nat × Nat)) (u : List Nat), u ≠ [] →
      walkWordPerm w (u.map f) = (walkWordPerm w u).map f
  | [], _, _ => rfl
  | (d, t) :: rest, u, hu => by
    have hdrop : (u.map f).dropLast = u.dropLast.map f := by
      induction u with
      | nil => rfl
      | cons a xs ih => cases xs <;> simp [ih]
    have hlast : (u.map f).getLastD 0 = f (u.getLastD 0) := by
      cases hu_rev : u.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp hu_rev) hu
      | cons l ls =>
        have hueq : u = ls.reverse ++ [l] := by have := congrArg List.reverse hu_rev; simpa using this
        rw [hueq]; simp
    have hend_ne : u.dropLast.rotate (11 - d) ++ [u.getLastD 0] ≠ [] := by simp
    have hend_map : (u.map f).dropLast.rotate (11 - d) ++ [(u.map f).getLastD 0] =
        (u.dropLast.rotate (11 - d) ++ [u.getLastD 0]).map f := by
      rw [hdrop, hlast, List.map_append, List.map_rotate]; rfl
    have hw3_ne : w3Perm ((u.dropLast.rotate (11 - d) ++ [u.getLastD 0]).rotate 12) t ≠ [] := by
      cases hrot : (u.dropLast.rotate (11 - d) ++ [u.getLastD 0]).rotate 12 with
      | nil => exact absurd (List.rotate_eq_nil_iff.mp hrot) hend_ne
      | cons a r1 => cases r1 with
        | nil => simp [w3Perm]
        | cons b r2 => cases r2 with
          | nil => simp [w3Perm]
          | cons c Y => cases t with
            | zero => simp [w3Perm]
            | succ t => cases t with
              | zero => simp [w3Perm]
              | succ t => cases t with
                | zero => simp [w3Perm]
                | succ t => cases t with
                  | zero => simp [w3Perm]
                  | succ t => simp [w3Perm]
    simp only [walkWordPerm, hend_map, ← List.map_rotate, w3Perm_map]
    exact walkWordPerm_map f rest _ hw3_ne

theorem w3Perm_permW {x : List Nat} (hx : S.PermW 13 x) (t : Nat) :
    S.PermW 13 (w3Perm x t) ∧ S.code (w3Perm x t) = w3Code 13 (S.code x) t := by
  obtain ⟨a, b, c, Y, rfl, hYl⟩ := S.exists_cons3 hx.2.1 (by omega)
  have hdx : ∀ z ∈ a :: b :: c :: Y, z < 16 := hx.lt16 (by omega)
  obtain ⟨hpY, hpa, hpb, hpc⟩ := S.six_parts 13 a b c Y hYl hdx (by omega)
  have hperm_aux : ∀ p q r : Nat,
      (p = a ∧ q = c ∧ r = b) ∨ (p = b ∧ q = a ∧ r = c) ∨ (p = b ∧ q = c ∧ r = a) ∨
      (p = c ∧ q = a ∧ r = b) ∨ (p = c ∧ q = b ∧ r = a) →
      S.PermW 13 (Y ++ [p, q, r]) := by
    intro p q r hcase
    have hnd := hx.1
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    have hndY : Y.Nodup := hnd.2.2.2
    have hab : a ≠ b := hnd.1.1
    have hac : a ≠ c := hnd.1.2.1
    have haY : a ∉ Y := hnd.1.2.2
    have hbc : b ≠ c := hnd.2.1.1
    have hbY : b ∉ Y := hnd.2.1.2
    have hcY : c ∉ Y := hnd.2.2.1
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      refine ⟨?_, by simp [hYl], fun z => ?_⟩
      · rw [List.nodup_append]
        refine ⟨hndY, by simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc], ?_⟩
        intro y hy w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> (intro heq; subst heq; contradiction)
      · rw [← hx.2.2 z]; simp [or_comm, or_left_comm, or_assoc]
  cases t with
  | zero =>
    refine ⟨hperm_aux a c b (Or.inl ⟨rfl, rfl, rfl⟩), ?_⟩
    simp only [w3Perm, S.code_append3, w3Code, hpY, hpa, hpb, hpc]
  | succ t => cases t with
    | zero =>
      refine ⟨hperm_aux b a c (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), ?_⟩
      simp only [w3Perm, S.code_append3, w3Code, hpY, hpa, hpb, hpc]
    | succ t => cases t with
      | zero =>
        refine ⟨hperm_aux b c a (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))), ?_⟩
        simp only [w3Perm, S.code_append3, w3Code, hpY, hpa, hpb, hpc]
      | succ t => cases t with
        | zero =>
          refine ⟨hperm_aux c a b (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))), ?_⟩
          simp only [w3Perm, S.code_append3, w3Code, hpY, hpa, hpb, hpc]
        | succ t =>
          refine ⟨hperm_aux c b a (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))), ?_⟩
          simp only [w3Perm, S.code_append3, w3Code, hpY, hpa, hpb, hpc]

theorem walkWordPerm_spec :
    ∀ (w : List (Nat × Nat)) (u : List Nat),
      S.PermW 13 u →
      S.PermW 13 (walkWordPerm w u) ∧ S.code (walkWordPerm w u) = walkWordFast 13 w (S.code u)
  | [], u, hu => ⟨hu, rfl⟩
  | (d, t) :: rest, u, hu => by
    have hu_ne : u ≠ [] := by intro h; have := hu.2.1; rw [h] at this; simp at this
    let pre := u.dropLast
    let last := u.getLastD 0
    have hlast_eq : last = u.getLast hu_ne := by
      cases hr : u.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hu_ne
      | cons l ls =>
        have hueq : u = ls.reverse ++ [l] := by have := congrArg List.reverse hr; simpa using this
        simp [last, hueq]
    have hu_eq : u = pre ++ [last] := by rw [hlast_eq]; exact (List.dropLast_append_getLast hu_ne).symm
    have hpre_len : pre.length = 12 := by
      have := congrArg List.length hu_eq; rw [hu.2.1] at this; simp at this; omega
    have hpre16 : ∀ a ∈ pre, a < 16 := fun a ha => hu.lt16 (by omega) a (by rw [hu_eq]; exact List.mem_append_left _ ha)
    have hlast16 : last < 16 := hu.lt16 (by omega) last (by rw [hu_eq]; simp)
    let endP := pre.rotate (11 - d) ++ [last]
    have hend_perm : S.PermW 13 endP := by
      have hnd := hu.1; rw [hu_eq, List.nodup_append] at hnd
      refine ⟨?_, by simp [endP, hpre_len], fun z => ?_⟩
      · rw [List.nodup_append]
        refine ⟨List.nodup_rotate.mpr hnd.1, hnd.2.1, fun a ha b hb => hnd.2.2 a (List.mem_rotate.mp ha) b hb⟩
      · rw [← hu.2.2 z, hu_eq]; simp [endP]
    have hend_code : S.code endP = pieceAdvance 13 (11 - d) (S.code u) := by
      conv_rhs => rw [hu_eq]
      exact (pieceAdvance_code (k := 13) (by omega) hpre_len hpre16 hlast16 (by omega)).symm
    have hrot_perm : S.PermW 13 (endP.rotate 12) := hend_perm.rotate 12
    have hrot_code : S.code (endP.rotate 12) = S.exc 13 (S.code endP) := by
      rw [S.exc_code 13 endP hend_perm.2.1 (hend_perm.lt16 (by omega)) (by omega)]
    obtain ⟨hw3_perm, hw3_code⟩ := w3Perm_permW hrot_perm t
    obtain ⟨ih_perm, ih_code⟩ := walkWordPerm_spec rest (w3Perm (endP.rotate 12) t) hw3_perm
    refine ⟨ih_perm, ?_⟩
    simp only [walkWordPerm, walkWordFast]
    change S.code (walkWordPerm rest (w3Perm (endP.rotate 12) t)) =
      walkWordFast 13 rest (w3Code 13 (S.exc 13 (pieceAdvance 13 (11 - d) (S.code u))) t)
    rw [ih_code, hw3_code, hrot_code, hend_code]

theorem getNib13_spec {g : List Nat} (hg_len : g.length = 13) (hg16 : ∀ a ∈ g, a < 16)
    {b : Nat} (hb1 : 1 ≤ b) (hb13 : b ≤ 13) :
    getNib13 (S.code g) b = S.unrelab g b := by
  match g, hg_len with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _ =>
    have h0 : x0 < 16 := hg16 x0 (by simp)
    have h1 : x1 < 16 := hg16 x1 (by simp)
    have h2 : x2 < 16 := hg16 x2 (by simp)
    have h3 : x3 < 16 := hg16 x3 (by simp)
    have h4 : x4 < 16 := hg16 x4 (by simp)
    have h5 : x5 < 16 := hg16 x5 (by simp)
    have h6 : x6 < 16 := hg16 x6 (by simp)
    have h7 : x7 < 16 := hg16 x7 (by simp)
    have h8 : x8 < 16 := hg16 x8 (by simp)
    have h9 : x9 < 16 := hg16 x9 (by simp)
    have h10 : x10 < 16 := hg16 x10 (by simp)
    have h11 : x11 < 16 := hg16 x11 (by simp)
    have h12 : x12 < 16 := hg16 x12 (by simp)
    have hcode : S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] =
        ((((((((((((x0 * 16 + x1) * 16 + x2) * 16 + x3) * 16 + x4) * 16 + x5) * 16 + x6) * 16 + x7)
          * 16 + x8) * 16 + x9) * 16 + x10) * 16 + x11) * 16 + x12) := by simp [S.code]
    interval_cases b
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x1000000000000 % 16 = x0; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x100000000000 % 16 = x1; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x10000000000 % 16 = x2; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x1000000000 % 16 = x3; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x100000000 % 16 = x4; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x10000000 % 16 = x5; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x1000000 % 16 = x6; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x100000 % 16 = x7; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x10000 % 16 = x8; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x1000 % 16 = x9; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x100 % 16 = x10; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] / 0x10 % 16 = x11; rw [hcode]; omega
    · change S.code [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] % 16 = x12; rw [hcode]; omega

theorem compose13_code {g h : List Nat} (hg : S.PermW 13 g) (hh : S.PermW 13 h) :
    compose13 (S.code g) (S.code h) = S.code (h.map (S.unrelab g)) := by
  have hg16 := hg.lt16 (by omega)
  have hh16 := hh.lt16 (by omega)
  match h, hh.2.1 with
  | [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12], _ =>
    have hy : ∀ a ∈ [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12], 1 ≤ a ∧ a ≤ 13 :=
      fun a ha => (hh.2.2 a).mp ha
    have h0 : y0 < 16 := hh16 y0 (by simp)
    have h1 : y1 < 16 := hh16 y1 (by simp)
    have h2 : y2 < 16 := hh16 y2 (by simp)
    have h3 : y3 < 16 := hh16 y3 (by simp)
    have h4 : y4 < 16 := hh16 y4 (by simp)
    have h5 : y5 < 16 := hh16 y5 (by simp)
    have h6 : y6 < 16 := hh16 y6 (by simp)
    have h7 : y7 < 16 := hh16 y7 (by simp)
    have h8 : y8 < 16 := hh16 y8 (by simp)
    have h9 : y9 < 16 := hh16 y9 (by simp)
    have h10 : y10 < 16 := hh16 y10 (by simp)
    have h11 : y11 < 16 := hh16 y11 (by simp)
    have h12 : y12 < 16 := hh16 y12 (by simp)
    have hc : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] =
        ((((((((((((y0 * 16 + y1) * 16 + y2) * 16 + y3) * 16 + y4) * 16 + y5) * 16 + y6) * 16 + y7)
          * 16 + y8) * 16 + y9) * 16 + y10) * 16 + y11) * 16 + y12) := by simp [S.code]
    have hd0 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000000000 % 16 = y0 := by rw [hc]; omega
    have hd1 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000000000 % 16 = y1 := by rw [hc]; omega
    have hd2 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000000000 % 16 = y2 := by rw [hc]; omega
    have hd3 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000000 % 16 = y3 := by rw [hc]; omega
    have hd4 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000000 % 16 = y4 := by rw [hc]; omega
    have hd5 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000000 % 16 = y5 := by rw [hc]; omega
    have hd6 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000 % 16 = y6 := by rw [hc]; omega
    have hd7 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000 % 16 = y7 := by rw [hc]; omega
    have hd8 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000 % 16 = y8 := by rw [hc]; omega
    have hd9 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000 % 16 = y9 := by rw [hc]; omega
    have hd10 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100 % 16 = y10 := by rw [hc]; omega
    have hd11 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10 % 16 = y11 := by rw [hc]; omega
    have hd12 : S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] % 16 = y12 := by rw [hc]; omega
    unfold compose13
    change Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000000000 % 16)) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x1000 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x100 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] / 0x10 % 16))) 16)
      (getNib13 (S.code g) (S.code [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12] % 16)) = _
    rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12]
    rw [getNib13_spec hg.2.1 hg16 (hy y0 (by simp)).1 (hy y0 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y1 (by simp)).1 (hy y1 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y2 (by simp)).1 (hy y2 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y3 (by simp)).1 (hy y3 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y4 (by simp)).1 (hy y4 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y5 (by simp)).1 (hy y5 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y6 (by simp)).1 (hy y6 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y7 (by simp)).1 (hy y7 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y8 (by simp)).1 (hy y8 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y9 (by simp)).1 (hy y9 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y10 (by simp)).1 (hy y10 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y11 (by simp)).1 (hy y11 (by simp)).2,
      getNib13_spec hg.2.1 hg16 (hy y12 (by simp)).1 (hy y12 (by simp)).2]
    simp [S.code]

theorem permW_range13 : S.PermW 13 (List.range' 1 13) := by
  refine ⟨List.nodup_range', List.length_range', fun a => ?_⟩
  rw [List.mem_range']; constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro ⟨h1, h2⟩; exact ⟨a - 1, by omega, by omega⟩

theorem map_unrelab_range13 {g : List Nat} (hg : g.length = 13) :
    (List.range' 1 13).map (S.unrelab g) = g := by
  apply List.ext_getElem
  · simp [hg]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', S.unrelab]
    have hi : i < g.length := by simpa [hg] using h2
    rw [Nat.one_mul, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl

/-- **`S_{13}` Group-Homomorphism Theorem:** `walkWordFast 13 (w1 ++ w2) (idc 13) = compose13 (walkWordFast 13 w1 (idc 13)) (walkWordFast 13 w2 (idc 13))`! -/
theorem walkWordFast_append_compose13 (w1 w2 : List (Nat × Nat)) :
    walkWordFast 13 (w1 ++ w2) (S.idc 13) =
      compose13 (walkWordFast 13 w1 (S.idc 13)) (walkWordFast 13 w2 (S.idc 13)) := by
  have hid : S.idc 13 = S.code (List.range' 1 13) := S.idc_code 13
  rw [walkWordFast_append, hid]
  obtain ⟨hp1, hc1⟩ := walkWordPerm_spec w1 (List.range' 1 13) permW_range13
  obtain ⟨hp2, hc2⟩ := walkWordPerm_spec w2 (List.range' 1 13) permW_range13
  obtain ⟨_, hc12⟩ := walkWordPerm_spec w2 (walkWordPerm w1 (List.range' 1 13)) hp1
  rw [← hc1, ← hc2, ← hc12, compose13_code hp1 hp2]
  have hmap : walkWordPerm w2 (walkWordPerm w1 (List.range' 1 13)) =
      (walkWordPerm w2 (List.range' 1 13)).map (S.unrelab (walkWordPerm w1 (List.range' 1 13))) := by
    conv_lhs => rw [← map_unrelab_range13 hp1.2.1]
    exact walkWordPerm_map (S.unrelab (walkWordPerm w1 (List.range' 1 13))) w2 (List.range' 1 13) (by simp)
  rw [hmap]

/-! ### 4. `IsWindow` flag evolution (`walkF`, `nextF`, `nextFL2`) -/

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

theorem walkF_expandSymARep (f : Nat) :
    ∀ r : Nat, walkF f ((expandSymARep r).map Prod.fst) =
      if r = 0 then some f else if f = 1 then none else some 2
  | 0 => by simp [expandSymARep, walkF]
  | r + 1 => by
    have hstep : expandSymARep (r + 1) = expandSym 9 2 4 ++ expandSymARep r := by
      simp [expandSymARep, List.replicate_succ, symA13]
    rw [hstep, List.map_append, walkF_append]
    have hm : (expandSym 9 2 4).map Prod.fst = List.replicate 9 0 ++ [2] := by
      simp [expandSym, List.map_replicate]
    rw [hm, walkF_expandSym]
    by_cases hf1 : f = 1
    · subst hf1; simp [nextF]
    · have hnf : nextF f 9 2 = some 2 := by
        unfold nextF
        have : (f == 1) = false := S.beq_false_of_ne hf1
        simp [this]
      rw [hnf]; dsimp only; rw [walkF_expandSymARep 2 r]
      cases r <;> simp [hf1]

theorem walkF_expandL2Sym (f r m d t : Nat) :
    walkF f ((expandL2Sym r m d t).map Prod.fst) = nextFL2 f r m d := by
  unfold expandL2Sym nextFL2
  rw [List.map_append, walkF_append, walkF_expandSymARep]
  have hm : (expandSym m d t).map Prod.fst = List.replicate m 0 ++ [d] := by
    simp [expandSym]
  rw [hm]
  by_cases hr : r = 0
  · subst hr; simp [walkF_expandSym]
  · have hr' : (r == 0) = false := S.beq_false_of_ne hr
    by_cases hf : f = 1
    · subst hf; simp [hr, hr']
    · have hf' : (f == 1) = false := S.beq_false_of_ne hf
      simp [hr, hr', hf, hf', walkF_expandSym]

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
      · obtain ⟨x, hx, hx2⟩ := hex_blk; have := hf1 h1 hblk_ne x hx; omega
      · have h2 : f = 2 := by omega
        subst h2; rfl
  | d :: rest, pre, blk, f, hf3, hex, hpre, hpos, hf0, hf1, hf2, hf1nil, hlast, _ => by
    have hlast_rest : ∀ y, rest.getLast? = some y → 0 < y := by
      intro y hy; apply hlast y
      cases rest with
      | nil => simp at hy
      | cons r rs => simpa [List.getLast?_cons_cons] using hy
    by_cases hd0 : d = 0
    · subst hd0
      have hrest_ne : rest ≠ [] := by
        intro hr; subst hr; have := hlast 0 (by simp); omega
      have hf_ne1 : f ≠ 1 := by
        intro h1
        cases blk with
        | nil => have := (hf1nil h1 rfl).2.2; simp at this
        | cons b bs =>
          have hblk_ne : b :: bs ≠ [] := List.cons_ne_nil _ _
          obtain ⟨x, hx, hx2⟩ := hex pre (b :: bs) (0 :: rest) rfl hblk_ne hpos hpre (Or.inr ⟨rest, rfl⟩)
          have := hf1 h1 hblk_ne x hx; omega
      have hsf : stepF f 0 = some 0 := by
        unfold stepF; have h1 : (f == 1) = false := S.beq_false_of_ne hf_ne1; simp [h1]
      simp only [walkF, hsf]
      refine walkF_window_aux rest (pre ++ blk ++ [0]) [] 0 (by omega) ?_
        (Or.inr ⟨pre ++ blk, rfl⟩) (by simp) (fun _ => rfl) (by omega) (by omega) (by omega)
        hlast_rest (fun h => absurd h hrest_ne)
      intro pre' blk' post' heq; apply hex pre' blk' post'; simpa [List.append_assoc] using heq
    · have hdpos : 0 < d := by omega
      have hpos' : ∀ x ∈ blk ++ [d], 0 < x := by
        intro x hx; rcases List.mem_append.mp hx with h1 | h1
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
            unfold stepF; have h2 : (f == 2) = false := S.beq_false_of_ne hf2eq; simp [h2]
          simp only [walkF, hsf]
          refine walkF_window_aux rest pre (blk ++ [1]) 1 (by omega) ?_ hpre hpos'
            (by omega) ?_ (by omega) (fun _ h => by simp at h) hlast_rest (fun _ => by simp)
          · intro pre' blk' post' heq; apply hex pre' blk' post'; simpa [List.append_assoc] using heq
          · intro _ _ x hx
            rcases List.mem_append.mp hx with hx1 | hx1
            · by_cases h0 : f = 0
              · rw [hf0 h0] at hx1; simp at hx1
              · exact hf1 (by omega) (List.ne_nil_of_mem hx1) x hx1
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
  · intro _ _; rw [hfirst]; exact ⟨rfl, List.cons_ne_nil _ _, by simpa using hx0⟩
  · intro y hy
    rw [hlast, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hy
    simp only [List.getLast?_singleton, Option.some.injEq] at hy; omega
  · intro hnil; rw [hnil] at hfirst; cases hfirst

/-! ### 5. `L2CertValid`, BPE DAG Semantics, and O(1) AC Automaton Invariant -/

/-- Full Level-2 certificate validity predicate (every condition is a pure-kernel sharded check). -/
structure L2CertValid (cert : L2Cert) : Prop where
  hD1 : 1 ≤ cert.D_track
  hD11 : cert.D_track ≤ 11
  hR1 : 1 ≤ cert.R_max
  hq : 0 < cert.q
  hcn : cert.cn ≤ cert.q * 8
  hA : cert.A = cert.q * 10 - cert.cn
  hAlive : 1 < cert.nAlive
  hAliveBound : cert.nAlive ≤ deadLeafBase
  hBpeGe : cert.nLong + cert.nPair ≤ cert.nBpe
  hbase : baseCheckL2 cert = true
  halpha1 : ∀ m ≤ 10, ∀ d ≤ cert.D_track, ∀ t < 5, alpha1TripleCheck cert m d t = true
  hl1Elem : ∀ s1 < cert.alpha1, l1ElemCheck cert s1 = true
  hforb1 : ∀ a < cert.alpha1, forb1RowCheck cert a = true
  hl2Single : ∀ r ≤ cert.R_max, ∀ s1 < cert.alpha1, l2SingleCheck cert r s1 = true
  hbpe : ∀ t < cert.nBpe, bpeElemCheck cert t = true
  hcegarWit : ∀ fid < cert.nCegar, cegarWitCheck cert fid = true
  hcegarLeaf : ∀ fid < cert.nCegar, cegarLeafCheck cert fid = true
  hroot : checkRoot cert = true
  hpair : ∀ pi < cert.nPair, checkPair cert pi = true
  hrootS1 : ∀ s1 < cert.alpha1, checkRootS1 cert s1 = true
  hmaxTr : ∀ li < cert.nLong, checkMaxTr cert li = true
  htrie : ∀ u, 1 ≤ u → u < cert.nAlive → trieStateCheck cert u = true

/-- Expand a tracked L2 symbol ID `ti < nLong + nPair` into raw `(d, t)` transitions. -/
def expandTrSym (cert : L2Cert) (ti : Nat) : List (Nat × Nat) :=
  let (r, s1) := cert.trInfo ti
  let (m, d, t) := cert.sym1Info s1
  expandL2Sym r m d t

/-- Expand a list of tracked L2 symbol IDs into raw `(d, t)` transitions. -/
def expandTrWord (cert : L2Cert) (ws : List Nat) : List (Nat × Nat) :=
  ws.flatMap (expandTrSym cert)

theorem expandTrWord_append (cert : L2Cert) (w1 w2 : List Nat) :
    expandTrWord cert (w1 ++ w2) = expandTrWord cert w1 ++ expandTrWord cert w2 :=
  List.flatMap_append

theorem expandTrWord_suffix (cert : L2Cert) {s t : List Nat} (h : s <:+ t) :
    expandTrWord cert s <:+ expandTrWord cert t := by
  obtain ⟨pre, rfl⟩ := h
  exact ⟨expandTrWord cert pre, (expandTrWord_append cert pre s).symm⟩

theorem suffix_trans_append {α : Type} {a b c d : List α} (h1 : a <:+ b ++ d) (h2 : b <:+ c) :
    a <:+ c ++ d := by
  obtain ⟨p1, hp1⟩ := h1
  obtain ⟨p2, hp2⟩ := h2
  refine ⟨p2 ++ p1, ?_⟩
  rw [List.append_assoc, hp1, ← List.append_assoc, hp2]

/-- Expand a BPE token `t` using bounded fuel (exact whenever `fuel ≥ t + 1` and `bpeLeft, bpeRight < t`). -/
def bpeWordAux (cert : L2Cert) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, t =>
    if t < cert.nLong + cert.nPair then [t]
    else bpeWordAux cert fuel (cert.bpeLeft t) ++ bpeWordAux cert fuel (cert.bpeRight t)

def bpeWord (cert : L2Cert) (t : Nat) : List Nat :=
  bpeWordAux cert (t + 1) t

/-- Full tracked-symbol word of CEGAR word `fid < nCegar`. -/
def cegarWord (cert : L2Cert) (fid : Nat) : List Nat :=
  [cert.cegarFirst fid] ++ (cert.cegarMid fid).flatMap (bpeWord cert) ++ [cert.cegarLast fid]

/-- Reconstruct trie state prefix word (list of `li < nLong`) using bounded fuel. -/
def statePrefAux (cert : L2Cert) : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, u => statePrefAux cert fuel (getStPar cert u) ++ [getStSym cert u]

def statePref (cert : L2Cert) (u : Nat) : List Nat :=
  statePrefAux cert u u

/-! #### 5a. Extracting basic consequences from `L2CertValid` -/

theorem L2CertValid.base_parts {cert : L2Cert} (hv : L2CertValid cert) :
    checkWitness 13 (List.replicate 11 (0, 4)) cert.witZeroRun = true ∧
    checkRangeAux 0 (fun t => checkWitness 13 [(0, t), (0, 4)] (cert.witAfterD0 t)) 4 = true ∧
    checkWitness 13 (expandSymARep (cert.R_max + 1)) cert.witSymARun = true ∧
    Nat.ble (cert.idA + 1) cert.alpha1 = true ∧
    (cert.sym1Info cert.idA == symA13) = true ∧
    (cert.sym1Id 9 2 4 == some cert.idA) = true ∧
    checkRangeAux 0 (fun m => Nat.beq (cert.pow04 m) (walkWordFast 13 (List.replicate m (0, 4)) (S.idc 13))) 11 = true ∧
    checkRangeAux 0 (fun r => Nat.beq (cert.powA r) (walkWordFast 13 (expandSymARep r) (S.idc 13))) (cert.R_max + 1) = true ∧
    Nat.beq cert.nLong 10 = true ∧
    oLeN (some cert.bias) (cert.rootPsi 1) = true ∧
    checkRangeAux 0 (fun li =>
      let u := cert.d1Long li
      let r := (cert.trInfo li).1; let s1 := (cert.trInfo li).2
      let m := (cert.sym1Info s1).1; let d := (cert.sym1Info s1).2.1
      Nat.ble 1 u && Nat.ble (u + 1) cert.nAlive &&
      Nat.beq (getStPar cert u) 0 && Nat.beq (getStSym cert u) li &&
      Nat.beq (getStFail cert u) 0 && Nat.beq (getGo cert 0 li) u &&
      Nat.beq (cert.longPos li) (2 * cert.q * (10 * r + m + 1)) &&
      Nat.beq (cert.longNeg li) (cert.A * (2 * r + d)) &&
      Nat.beq (cert.longD1Psi li) (getStPsi cert u) &&
      !isForb1 cert s1 cert.idA) cert.nLong = true ∧
    checkRangeAux 0 (fun ti =>
      let r := (cert.trInfo ti).1; let s1 := (cert.trInfo ti).2
      let m := (cert.sym1Info s1).1; let d := (cert.sym1Info s1).2.1
      Nat.ble r cert.R_max && Nat.ble (s1 + 1) cert.alpha1 &&
      !Nat.beq s1 cert.idA && cert.l2Valid r s1 &&
      (cert.trId r s1 == some ti) && Nat.ble 1 m && Nat.beq d 2) (cert.nLong + cert.nPair) = true ∧
    checkRangeAux 0 (fun ti1 =>
      checkRangeAux 0 (fun ti2 =>
        if cert.forb2 ti1 ti2 then
          let fid := cert.forb2Fid ti1 ti2
          Nat.ble (fid + 1) cert.nCegar && Nat.beq (cert.cegarFirst fid) ti1 &&
          (cert.cegarMid fid == []) && Nat.beq (cert.cegarLast fid) ti2
        else true) (cert.nLong + cert.nPair)) (cert.nLong + cert.nPair) = true := by
  have h := hv.hbase; unfold baseCheckL2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, _⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14⟩

theorem L2CertValid.nLong_eq {cert : L2Cert} (hv : L2CertValid cert) : cert.nLong = 10 :=
  Nat.eq_of_beq_eq_true hv.base_parts.2.2.2.2.2.2.2.2.1

theorem L2CertValid.base_collisions {cert : L2Cert} (hv : L2CertValid cert) :
    checkWitness 13 (List.replicate 11 (0, 4)) cert.witZeroRun = true ∧
    (∀ t < 4, checkWitness 13 [(0, t), (0, 4)] (cert.witAfterD0 t) = true) ∧
    checkWitness 13 (expandSymARep (cert.R_max + 1)) cert.witSymARun = true :=
  ⟨hv.base_parts.1,
   fun t ht => checkRangeAux_spec hv.base_parts.2.1 t (Nat.zero_le _) (by omega),
   hv.base_parts.2.2.1⟩

theorem L2CertValid.idA_spec {cert : L2Cert} (hv : L2CertValid cert) :
    cert.idA < cert.alpha1 ∧ cert.sym1Info cert.idA = symA13 ∧ cert.sym1Id 9 2 4 = some cert.idA := by
  have hb := hv.base_parts
  have hlt := Nat.le_of_ble_eq_true hb.2.2.2.1
  exact ⟨by omega, beq_iff_eq.mp hb.2.2.2.2.1, beq_iff_eq.mp hb.2.2.2.2.2.1⟩

theorem L2CertValid.pow04_spec {cert : L2Cert} (hv : L2CertValid cert) {m : Nat} (hm : m ≤ 10) :
    cert.pow04 m = walkWordFast 13 (List.replicate m (0, 4)) (S.idc 13) :=
  Nat.eq_of_beq_eq_true (checkRangeAux_spec hv.base_parts.2.2.2.2.2.2.1 m (Nat.zero_le _) (by omega))

theorem L2CertValid.powA_spec {cert : L2Cert} (hv : L2CertValid cert) {r : Nat} (hr : r ≤ cert.R_max) :
    cert.powA r = walkWordFast 13 (expandSymARep r) (S.idc 13) :=
  Nat.eq_of_beq_eq_true (checkRangeAux_spec hv.base_parts.2.2.2.2.2.2.2.1 r (Nat.zero_le _) (by omega))

theorem L2CertValid.root_start {cert : L2Cert} (hv : L2CertValid cert) :
    oLe (some 0) (psiInt cert.bias (cert.rootPsi 1)) = true := by
  have hle := oLe_of_oLeN (bias := cert.bias) hv.base_parts.2.2.2.2.2.2.2.2.2.1
  simpa [psiInt] using hle

theorem L2CertValid.d1Long_spec {cert : L2Cert} (hv : L2CertValid cert) {li : Nat} (hli : li < cert.nLong) :
    1 ≤ cert.d1Long li ∧ cert.d1Long li < cert.nAlive ∧
    getStPar cert (cert.d1Long li) = 0 ∧
    getStSym cert (cert.d1Long li) = li ∧
    getStFail cert (cert.d1Long li) = 0 ∧
    getGo cert 0 li = cert.d1Long li ∧
    cert.longPos li = 2 * cert.q * (10 * (cert.trInfo li).1 + (cert.sym1Info (cert.trInfo li).2).1 + 1) ∧
    cert.longNeg li = cert.A * (2 * (cert.trInfo li).1 + (cert.sym1Info (cert.trInfo li).2).2.1) ∧
    cert.longD1Psi li = getStPsi cert (cert.d1Long li) ∧
    isForb1 cert (cert.trInfo li).2 cert.idA = false := by
  have hi := checkRangeAux_spec hv.base_parts.2.2.2.2.2.2.2.2.2.2.1 li (Nat.zero_le _) (by omega)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hi
  exact ⟨Nat.le_of_ble_eq_true h1, by have := Nat.le_of_ble_eq_true h2; omega,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h9, h10⟩

theorem L2CertValid.trInfo_spec {cert : L2Cert} (hv : L2CertValid cert) {ti : Nat}
    (hti : ti < cert.nLong + cert.nPair) :
    (cert.trInfo ti).1 ≤ cert.R_max ∧
    (cert.trInfo ti).2 < cert.alpha1 ∧
    (cert.trInfo ti).2 ≠ cert.idA ∧
    cert.l2Valid (cert.trInfo ti).1 (cert.trInfo ti).2 = true ∧
    cert.trId (cert.trInfo ti).1 (cert.trInfo ti).2 = some ti ∧
    1 ≤ (cert.sym1Info (cert.trInfo ti).2).1 ∧
    (cert.sym1Info (cert.trInfo ti).2).2.1 = 2 := by
  have hi := checkRangeAux_spec hv.base_parts.2.2.2.2.2.2.2.2.2.2.2.1 ti (Nat.zero_le _) (by omega)
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hi
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hi
  exact ⟨Nat.le_of_ble_eq_true h1, by have := Nat.le_of_ble_eq_true h2; omega,
    fun heq => by rw [heq, Nat.beq_refl] at h3; exact Bool.noConfusion h3,
    h4, h5, Nat.le_of_ble_eq_true h6, Nat.eq_of_beq_eq_true h7⟩

theorem L2CertValid.forb2_spec {cert : L2Cert} (hv : L2CertValid cert)
    {ti1 ti2 : Nat} (h1 : ti1 < cert.nLong + cert.nPair) (h2 : ti2 < cert.nLong + cert.nPair)
    (hf : cert.forb2 ti1 ti2 = true) :
    cert.forb2Fid ti1 ti2 < cert.nCegar ∧
    cegarWord cert (cert.forb2Fid ti1 ti2) = [ti1, ti2] := by
  have h1' := checkRangeAux_spec hv.base_parts.2.2.2.2.2.2.2.2.2.2.2.2 ti1 (Nat.zero_le _) (by omega)
  have h2' := checkRangeAux_spec h1' ti2 (Nat.zero_le _) (by omega)
  simp only [hf, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h2'
  refine ⟨by have := Nat.le_of_ble_eq_true h2'.1.1.1; omega, ?_⟩
  unfold cegarWord
  rw [Nat.eq_of_beq_eq_true h2'.1.1.2, h2'.1.2, Nat.eq_of_beq_eq_true h2'.2]
  rfl

theorem L2CertValid.l1Elem_spec {cert : L2Cert} (hv : L2CertValid cert) {s1 : Nat} (hs : s1 < cert.alpha1) :
    (cert.sym1Info s1).1 ≤ 10 ∧
    (cert.sym1Info s1).2.1 ≤ cert.D_track ∧
    (cert.sym1Info s1).2.2 < 5 ∧
    cert.l1Elem s1 = walkWordFast 13 (expandSym (cert.sym1Info s1).1 (cert.sym1Info s1).2.1 (cert.sym1Info s1).2.2) (S.idc 13) := by
  have h := hv.hl1Elem s1 hs; unfold l1ElemCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1.1.1.1, Nat.le_of_ble_eq_true h.1.1.1.2,
    by have := Nat.le_of_ble_eq_true h.1.1.2; omega, Nat.eq_of_beq_eq_true h.2⟩

/-! #### 5b. `forb1` and BPE CEGAR collision soundness -/

theorem expandSym_len (m d t : Nat) : (expandSym m d t).length = m + 1 := by simp [expandSym]

theorem expandSym_getD (m d t i : Nat) (hi : i < m + 1) :
    ((expandSym m d t).getD i (0, 0)).1 = if i = m then d else 0 := by
  unfold expandSym
  by_cases him : i < m
  · have h1 : (List.replicate m (0, 4) ++ [(d, t)])[i]'(by simp; omega) = (0, 4) := by
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some, h1]
    simp [show i ≠ m by omega]
  · have heq : i = m := by omega
    subst heq
    have h1 : (List.replicate i (0, 4) ++ [(d, t)])[i]'(by simp) = (d, t) := by
      rw [List.getElem_append_right (by simp)]; simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some, h1]
    simp

theorem expandSym_take (m d t i : Nat) (hi : i ≤ m) :
    (expandSym m d t).take i = List.replicate i (0, 4) := by
  unfold expandSym
  rw [List.take_append_of_le_length (by simp; omega), List.take_replicate, Nat.min_eq_left hi]

/-- Soundness of `forb1Pack a b ≠ 0`: `[a, b]` cannot occur as an infix of a valid chain! -/
theorem not_infix_of_isForb1 {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {a b : Nat} (ha : a < cert.alpha1) (hb : b < cert.alpha1)
    (hf : isForb1 cert a b = true)
    (hinf : (expandSym (cert.sym1Info a).1 (cert.sym1Info a).2.1 (cert.sym1Info a).2.2 ++
             expandSym (cert.sym1Info b).1 (cert.sym1Info b).2.1 (cert.sym1Info b).2.2) <:+: ts) : False := by
  have hrow := hv.hforb1 a ha
  have hp := checkRangeChunked_spec hrow b (Nat.zero_le _) (by omega)
  unfold forb1PairCheck at hp
  unfold isForb1 at hf
  have hne0 : Nat.beq (cert.forb1Pack a b) 0 = false := by
    cases hb0 : Nat.beq (cert.forb1Pack a b) 0 <;> simp_all
  simp only [hne0, Bool.false_eq_true, ↓reduceIte] at hp
  let w := cert.forb1Pack a b - 1
  let i1 := w % 16; let j1 := (w / 16) % 16; let i2 := (w / 256) % 16; let j2 := (w / 4096) % 16
  rcases ha_info : cert.sym1Info a with ⟨m1, d1, t1⟩
  rcases hb_info : cert.sym1Info b with ⟨m2, d2, t2⟩
  rw [ha_info, hb_info] at hp hinf
  dsimp only at hp hinf
  have ha_sp := hv.l1Elem_spec ha; rw [ha_info] at ha_sp
  have hb_sp := hv.l1Elem_spec hb; rw [hb_info] at hb_sp
  cases hok : (Nat.ble i1 m1 && Nat.ble (j1 + 1) (12 - (if Nat.beq i1 m1 then d1 else 0)) &&
      (Nat.ble i2 (m2 + 1) && (if Nat.beq i2 (m2 + 1) then Nat.beq j2 0
        else Nat.ble (j2 + 1) (12 - (if Nat.beq i2 m2 then d2 else 0))))) with
  | false =>
    change (if !(Nat.ble i1 m1 && Nat.ble (j1 + 1) (12 - (if Nat.beq i1 m1 then d1 else 0)) &&
      (Nat.ble i2 (m2 + 1) && (if Nat.beq i2 (m2 + 1) then Nat.beq j2 0
        else Nat.ble (j2 + 1) (12 - (if Nat.beq i2 m2 then d2 else 0))))) = true then false else _) = true at hp
    rw [hok] at hp; cases hp
  | true =>
    change (if !(Nat.ble i1 m1 && Nat.ble (j1 + 1) (12 - (if Nat.beq i1 m1 then d1 else 0)) &&
      (Nat.ble i2 (m2 + 1) && (if Nat.beq i2 (m2 + 1) then Nat.beq j2 0
        else Nat.ble (j2 + 1) (12 - (if Nat.beq i2 m2 then d2 else 0))))) = true then false else _) = true at hp
    rw [hok] at hp
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
    have hcan := Nat.eq_of_beq_eq_true hp
    simp only [Bool.and_eq_true] at hok
    have hi1_le : i1 ≤ m1 := Nat.le_of_ble_eq_true hok.1.1
    have hi2_le : i2 ≤ m2 + 1 := Nat.le_of_ble_eq_true hok.2.1
    let w1 := expandSym m1 d1 t1
    let w2 := expandSym m2 d2 t2
    let wab := w1 ++ w2
    have hlen1 : w1.length = m1 + 1 := expandSym_len m1 d1 t1
    have hlen2 : w2.length = m2 + 1 := expandSym_len m2 d2 t2
    have h12 : i1 < m1 + 1 + i2 := by omega
    have hi2_w : m1 + 1 + i2 ≤ wab.length := by simp [wab, hlen1, hlen2]; omega
    have hj1 : j1 < 12 - (wab.getD i1 (0, 0)).1 := by
      have hgd : (wab.getD i1 (0, 0)).1 = (w1.getD i1 (0, 0)).1 := by
        simp only [wab, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rw [hgd, expandSym_getD m1 d1 t1 i1 (by omega)]
      have hb := Nat.le_of_ble_eq_true hok.1.2
      by_cases heq : i1 = m1
      · subst heq; simp only [Nat.beq_refl, ↓reduceIte] at hb ⊢; omega
      · have hne : Nat.beq i1 m1 = false := by cases hc : Nat.beq i1 m1 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at hb; simp only [heq, ↓reduceIte]; omega
    have hj2 : if m1 + 1 + i2 < wab.length then j2 < 12 - (wab.getD (m1 + 1 + i2) (0, 0)).1 else j2 = 0 := by
      by_cases hlt : i2 < m2 + 1
      · have hlt' : m1 + 1 + i2 < wab.length := by simp [wab, hlen1, hlen2]; omega
        simp only [hlt', ↓reduceIte]
        have hgd : (wab.getD (m1 + 1 + i2) (0, 0)).1 = (w2.getD i2 (0, 0)).1 := by
          simp only [wab, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), hlen1, Nat.add_sub_cancel_left]
        rw [hgd, expandSym_getD m2 d2 t2 i2 hlt]
        have hne : Nat.beq i2 (m2 + 1) = false := by cases hc : Nat.beq i2 (m2 + 1) with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc; omega
        have h2 := hok.2.2; simp only [hne, Bool.false_eq_true, ↓reduceIte] at h2
        have hb := Nat.le_of_ble_eq_true h2
        by_cases heq : i2 = m2
        · subst heq; simp only [Nat.beq_refl, ↓reduceIte] at hb ⊢; omega
        · have hne2 : Nat.beq i2 m2 = false := by cases hc : Nat.beq i2 m2 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) heq
          simp only [hne2, Bool.false_eq_true, ↓reduceIte] at hb; simp only [heq, ↓reduceIte]; omega
      · have heq : i2 = m2 + 1 := by omega
        have hnotlt : ¬ (m1 + 1 + i2 < wab.length) := by simp [wab, hlen1, hlen2]; omega
        simp only [hnotlt, ↓reduceIte]
        have h2 := hok.2.2; simp only [heq, Nat.beq_refl, ↓reduceIte] at h2
        exact Nat.eq_of_beq_eq_true h2
    have htake1 : wab.take i1 = List.replicate i1 (0, 4) := by
      rw [List.take_append_of_le_length (by omega)]; exact expandSym_take m1 d1 t1 i1 hi1_le
    have he1 : cert.pow04 i1 = walkWordFast 13 (wab.take i1) (S.idc 13) := by
      rw [htake1, hv.pow04_spec (by omega)]
    have he2 : compose13 (cert.l1Elem a) (if Nat.beq i2 (m2 + 1) then cert.l1Elem b else cert.pow04 i2) =
        walkWordFast 13 (wab.take (m1 + 1 + i2)) (S.idc 13) := by
      have htake2 : wab.take (m1 + 1 + i2) = w1 ++ w2.take i2 := by
        simp [wab, List.take_append, hlen1]
      rw [htake2, walkWordFast_append_compose13, ← ha_sp.2.2.2]
      congr 1
      by_cases heq : i2 = m2 + 1
      · have hb : Nat.beq i2 (m2 + 1) = true := by rw [heq]; exact Nat.beq_refl _
        simp only [hb, ↓reduceIte, hb_sp.2.2.2]
        rw [List.take_of_length_le (by omega)]
      · have hne : Nat.beq i2 (m2 + 1) = false := by cases hc : Nat.beq i2 (m2 + 1) with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) heq
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [expandSym_take m2 d2 t2 i2 (by omega), hv.pow04_spec (by omega)]
    change S.canon 13 (pieceAdvance 13 j1 (cert.pow04 i1)) =
      S.canon 13 (pieceAdvance 13 j2 (compose13 (cert.l1Elem a)
        (if Nat.beq i2 (m2 + 1) then cert.l1Elem b else cert.pow04 i2))) at hcan
    rw [he1, he2] at hcan
    exact not_infix_of_two_point (by omega) (by omega) hchain hmatch h12 hi2_w hj1 hj2 hcan hinf

theorem expandSymARep_len (r : Nat) : (expandSymARep r).length = 10 * r := by
  induction r with
  | zero => simp [expandSymARep]
  | succ r ih =>
    have h : expandSymARep (r + 1) = expandSym 9 2 4 ++ expandSymARep r := by
      simp [expandSymARep, List.replicate_succ, symA13]
    rw [h, List.length_append, expandSym_len, ih]; omega

theorem expandSymARep_add (r1 r2 : Nat) :
    expandSymARep (r1 + r2) = expandSymARep r1 ++ expandSymARep r2 := by
  unfold expandSymARep; rw [List.replicate_add, List.flatMap_append]

theorem expandSymARep_take (r i : Nat) (hi : i < 10 * r) :
    (expandSymARep r).take i = expandSymARep (i / 10) ++ List.replicate (i % 10) (0, 4) := by
  have hq : i / 10 < r := by omega
  have hsplit : r = i / 10 + 1 + (r - i / 10 - 1) := by omega
  conv_lhs => rw [hsplit, expandSymARep_add, expandSymARep_add]
  have hlen1 : (expandSymARep (i / 10)).length = 10 * (i / 10) := expandSymARep_len _
  have h1 : expandSymARep 1 = expandSym 9 2 4 := by simp [expandSymARep, symA13]
  rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega)]
  congr 1
  rw [hlen1, show i - 10 * (i / 10) = i % 10 by omega, h1,
    List.take_append_of_le_length (by rw [expandSym_len]; omega)]
  exact expandSym_take 9 2 4 (i % 10) (by omega)

theorem expandL2Sym_len (r m d t : Nat) : (expandL2Sym r m d t).length = 10 * r + m + 1 := by
  unfold expandL2Sym; rw [List.length_append, expandSymARep_len, expandSym_len]; omega

theorem expandL2Sym_getD (r m d t i : Nat) (hi : i < 10 * r + m + 1) :
    ((expandL2Sym r m d t).getD i (0, 0)).1 = l2PieceDef r m d i := by
  unfold expandL2Sym l2PieceDef
  by_cases hlt : i < 10 * r
  · have hb : Nat.ble (i + 1) (10 * r) = true := Nat.ble_eq_true_of_le (by omega)
    simp only [hb, ↓reduceIte]
    have hq : i / 10 < r := by omega
    have hsplit : r = i / 10 + 1 + (r - i / 10 - 1) := by omega
    have hgd1 : ((expandSymARep r ++ expandSym m d t).getD i (0, 0)).1 =
        ((expandSymARep r).getD i (0, 0)).1 := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [expandSymARep_len]; exact hlt)]
    rw [hgd1, hsplit, expandSymARep_add, expandSymARep_add, List.append_assoc]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [expandSymARep_len]; omega), expandSymARep_len]
    have h1 : expandSymARep 1 = expandSym 9 2 4 := by simp [expandSymARep, symA13]
    rw [h1, List.getElem?_append_left (by rw [expandSym_len]; omega)]
    have heq : i - 10 * (i / 10) = i % 10 := by omega
    rw [heq]
    have hres := expandSym_getD 9 2 4 (i % 10) (by omega)
    simp only [List.getD_eq_getElem?_getD] at hres
    rw [hres]
    by_cases hm9 : i % 10 = 9
    · have hm9' : Nat.beq (Nat.mod i 10) 9 = true := by change Nat.beq (i % 10) 9 = true; rw [hm9]; rfl
      simp [hm9, hm9']
    · have hm9' : Nat.beq (Nat.mod i 10) 9 = false := by
        change Nat.beq (i % 10) 9 = false
        cases hc : Nat.beq (i % 10) 9 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hm9
      simp [hm9, hm9']
  · have hb : Nat.ble (i + 1) (10 * r) = false := by cases hc : Nat.ble (i + 1) (10 * r) with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [expandSymARep_len]; omega), expandSymARep_len]
    have hres := expandSym_getD m d t (i - 10 * r) (by omega)
    simp only [List.getD_eq_getElem?_getD] at hres
    rw [hres]
    by_cases him : i = 10 * r + m
    · subst him; simp
    · have hne1 : i - 10 * r ≠ m := by omega
      have hne2 : Nat.beq i (10 * r + m) = false := by cases hc : Nat.beq i (10 * r + m) with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) him
      simp [hne1, hne2]

theorem walkL2Prefix13_spec {cert : L2Cert} (hv : L2CertValid cert)
    {r s1 i : Nat} (hr : r ≤ cert.R_max) (hs : s1 < cert.alpha1)
    (hi : i ≤ 10 * r + (cert.sym1Info s1).1 + 1) :
    walkL2Prefix13 cert r s1 (cert.sym1Info s1).1 i =
      walkWordFast 13 ((expandL2Sym r (cert.sym1Info s1).1 (cert.sym1Info s1).2.1 (cert.sym1Info s1).2.2).take i) (S.idc 13) := by
  have hs_sp := hv.l1Elem_spec hs
  rcases hinfo : cert.sym1Info s1 with ⟨m, d, t⟩
  simp only [hinfo] at hs_sp hi ⊢
  unfold walkL2Prefix13
  by_cases h1 : i < 10 * r
  · have hb : Nat.ble (i + 1) (10 * r) = true := Nat.ble_eq_true_of_le (by omega)
    simp only [hb, ↓reduceIte]
    have htake : (expandL2Sym r m d t).take i = expandSymARep (i / 10) ++ List.replicate (i % 10) (0, 4) := by
      unfold expandL2Sym
      rw [List.take_append_of_le_length (by rw [expandSymARep_len]; omega)]
      exact expandSymARep_take r i h1
    rw [htake]
    by_cases hq0 : i / 10 = 0
    · have hq0' : Nat.beq (Nat.div i 10) 0 = true := by change Nat.beq (i / 10) 0 = true; rw [hq0]; rfl
      simp only [hq0', ↓reduceIte, hq0, expandSymARep, List.replicate_zero, List.flatMap_nil, List.nil_append]
      exact hv.pow04_spec (m := i % 10) (by omega)
    · have hne : Nat.beq (Nat.div i 10) 0 = false := by
        change Nat.beq (i / 10) 0 = false
        cases hc : Nat.beq (i / 10) 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hq0
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      change compose13 (cert.powA (i / 10)) (cert.pow04 (i % 10)) = _
      rw [walkWordFast_append_compose13, hv.powA_spec (r := i / 10) (by omega), hv.pow04_spec (m := i % 10) (by omega)]
  · have hb1 : Nat.ble (i + 1) (10 * r) = false := by cases hc : Nat.ble (i + 1) (10 * r) with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
    simp only [hb1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : i ≤ 10 * r + m
    · have hb2 : Nat.ble i (10 * r + m) = true := Nat.ble_eq_true_of_le h2
      simp only [hb2, ↓reduceIte]
      have htake : (expandL2Sym r m d t).take i = expandSymARep r ++ List.replicate (i - 10 * r) (0, 4) := by
        unfold expandL2Sym
        rw [List.take_append, expandSymARep_len, List.take_of_length_le (by rw [expandSymARep_len]; omega),
          expandSym_take m d t (i - 10 * r) (by omega)]
      rw [htake]
      by_cases hr0 : r = 0
      · subst hr0; simp only [Nat.beq_refl, ↓reduceIte, expandSymARep, List.replicate_zero, List.flatMap_nil, List.nil_append, Nat.mul_zero, Nat.sub_zero]
        exact hv.pow04_spec (by omega)
      · have hne : Nat.beq r 0 = false := by cases hc : Nat.beq r 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hr0
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [walkWordFast_append_compose13, hv.powA_spec hr, hv.pow04_spec (by omega)]
    · have hb2 : Nat.ble i (10 * r + m) = false := by cases hc : Nat.ble i (10 * r + m) with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
      simp only [hb2, Bool.false_eq_true, ↓reduceIte]
      have htake : (expandL2Sym r m d t).take i = expandSymARep r ++ expandSym m d t := by
        rw [List.take_of_length_le (by rw [expandL2Sym_len]; omega)]; rfl
      rw [htake]
      by_cases hr0 : r = 0
      · subst hr0; simp only [Nat.beq_refl, ↓reduceIte, expandSymARep, List.replicate_zero, List.flatMap_nil, List.nil_append]
        exact hs_sp.2.2.2
      · have hne : Nat.beq r 0 = false := by cases hc : Nat.beq r 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hr0
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [walkWordFast_append_compose13, hv.powA_spec hr, hs_sp.2.2.2]

theorem bpeWordAux_eq_of_ge {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ (t fuel : Nat), t < cert.nBpe → t + 1 ≤ fuel → bpeWordAux cert fuel t = bpeWord cert t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro fuel ht hle
    cases fuel with
    | zero => omega
    | succ fuel' =>
      unfold bpeWord
      simp only [bpeWordAux]
      by_cases hlt : t < cert.nLong + cert.nPair
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hchk := hv.hbpe t ht; unfold bpeElemCheck at hchk
        have hbf : Nat.ble (t + 1) (cert.nLong + cert.nPair) = false := by
          cases hc : Nat.ble (t + 1) (cert.nLong + cert.nPair) with
          | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hchk
        have hl : cert.bpeLeft t < t := by have := Nat.le_of_ble_eq_true hchk.1.1; omega
        have hr : cert.bpeRight t < t := by have := Nat.le_of_ble_eq_true hchk.1.2; omega
        rw [ih _ hl fuel' (by omega) (by omega), ih _ hl t (by omega) (by omega),
          ih _ hr fuel' (by omega) (by omega), ih _ hr t (by omega) (by omega)]

theorem bpeWord_merge {cert : L2Cert} (hv : L2CertValid cert) {t : Nat}
    (ht : t < cert.nBpe) (hge : cert.nLong + cert.nPair ≤ t) :
    cert.bpeLeft t < t ∧ cert.bpeRight t < t ∧
    bpeWord cert t = bpeWord cert (cert.bpeLeft t) ++ bpeWord cert (cert.bpeRight t) := by
  have hchk := hv.hbpe t ht; unfold bpeElemCheck at hchk
  have hbf : Nat.ble (t + 1) (cert.nLong + cert.nPair) = false := by
    cases hc : Nat.ble (t + 1) (cert.nLong + cert.nPair) with
    | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
  simp only [hbf, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hchk
  have hl : cert.bpeLeft t < t := by have := Nat.le_of_ble_eq_true hchk.1.1; omega
  have hr : cert.bpeRight t < t := by have := Nat.le_of_ble_eq_true hchk.1.2; omega
  refine ⟨hl, hr, ?_⟩
  conv_lhs => unfold bpeWord; simp only [bpeWordAux, show ¬ (t < cert.nLong + cert.nPair) by omega, ↓reduceIte]
  rw [bpeWordAux_eq_of_ge hv _ t (by omega) (by omega),
    bpeWordAux_eq_of_ge hv _ t (by omega) (by omega)]

/-- Every BPE token `t < nBpe` has `bpeElem t = walkWordFast 13 (expandTrWord (bpeWord t)) (idc 13)`. -/
theorem bpeElem_spec {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ t < cert.nBpe, cert.bpeElem t = walkWordFast 13 (expandTrWord cert (bpeWord cert t)) (S.idc 13) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    have hchk := hv.hbpe t ht; unfold bpeElemCheck at hchk
    by_cases hlt : t < cert.nLong + cert.nPair
    · have hbt : Nat.ble (t + 1) (cert.nLong + cert.nPair) = true := Nat.ble_eq_true_of_le (by omega)
      simp only [hbt, ↓reduceIte] at hchk
      have heq := Nat.eq_of_beq_eq_true hchk
      have hbw : bpeWord cert t = [t] := by unfold bpeWord; simp [bpeWordAux, hlt]
      rw [heq, hbw]
      have htr := hv.trInfo_spec hlt
      have hs1 := hv.l1Elem_spec htr.2.1
      rcases hti : cert.trInfo t with ⟨r, s1⟩
      simp only [hti] at htr hs1 ⊢
      rcases hsi : cert.sym1Info s1 with ⟨m, d, tp⟩
      simp only [hsi] at hs1 ⊢
      simp only [expandTrWord, List.flatMap_singleton, expandTrSym, hti, hsi, expandL2Sym]
      by_cases hr0 : r = 0
      · subst hr0; simp only [Nat.beq_refl, ↓reduceIte, expandSymARep, List.replicate_zero, List.flatMap_nil, List.nil_append]
        exact hs1.2.2.2
      · have hne : Nat.beq r 0 = false := by cases hc : Nat.beq r 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hr0
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        rw [walkWordFast_append_compose13, hv.powA_spec htr.1, hs1.2.2.2]
    · have hbf : Nat.ble (t + 1) (cert.nLong + cert.nPair) = false := by
        cases hc : Nat.ble (t + 1) (cert.nLong + cert.nPair) with
        | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hchk
      obtain ⟨hl, hr, hbw⟩ := bpeWord_merge hv ht (by omega)
      rw [Nat.eq_of_beq_eq_true hchk.2, hbw, expandTrWord_append, walkWordFast_append_compose13,
        ih _ hl (by omega), ih _ hr (by omega)]

theorem foldl_bpeElem_spec {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ (toks : List Nat) (pre : List (Nat × Nat)),
      (∀ t ∈ toks, t < cert.nBpe) →
      toks.foldl (fun acc tok => compose13 acc (cert.bpeElem tok)) (walkWordFast 13 pre (S.idc 13)) =
        walkWordFast 13 (pre ++ expandTrWord cert (toks.flatMap (bpeWord cert))) (S.idc 13)
  | [], pre, _ => by simp [expandTrWord]
  | tok :: rest, pre, htoks => by
    have ht : tok < cert.nBpe := htoks tok List.mem_cons_self
    have hrest : ∀ t ∈ rest, t < cert.nBpe := fun t h => htoks t (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons, List.flatMap_cons, expandTrWord_append, ← List.append_assoc]
    rw [bpeElem_spec hv tok ht, ← walkWordFast_append_compose13]
    exact foldl_bpeElem_spec hv rest (pre ++ expandTrWord cert (bpeWord cert tok)) hrest

/-- **Main BPE CEGAR Soundness Theorem:** No `cegarWord cert fid` (`fid < nCegar`) can appear in a valid chain! -/
theorem not_infix_of_cegar {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {fid : Nat} (hfid : fid < cert.nCegar)
    (hinf : expandTrWord cert (cegarWord cert fid) <:+: ts) : False := by
  have hc := hv.hcegarWit fid hfid
  unfold cegarWitCheck at hc
  let nTr := cert.nLong + cert.nPair
  let s0 := cert.cegarFirst fid
  let mid := cert.cegarMid fid
  let sL := cert.cegarLast fid
  have hhdr : (Nat.ble (s0 + 1) nTr && Nat.ble (sL + 1) nTr && mid.all (fun t => Nat.ble (t + 1) cert.nBpe)) = true := by
    by_contra hf
    have hff : (Nat.ble (s0 + 1) nTr && Nat.ble (sL + 1) nTr && mid.all (fun t => Nat.ble (t + 1) cert.nBpe)) = false :=
      Bool.eq_false_iff.mpr hf
    change (if !(Nat.ble (s0 + 1) nTr && Nat.ble (sL + 1) nTr && mid.all (fun t => Nat.ble (t + 1) cert.nBpe)) = true then false else _) = true at hc
    rw [hff] at hc; cases hc
  change (if !(Nat.ble (s0 + 1) nTr && Nat.ble (sL + 1) nTr && mid.all (fun t => Nat.ble (t + 1) cert.nBpe)) = true then false else _) = true at hc
  rw [hhdr] at hc
  simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hhdr
  have hs0_lt : s0 < nTr := by have := Nat.le_of_ble_eq_true hhdr.1.1; omega
  have hsL_lt : sL < nTr := by have := Nat.le_of_ble_eq_true hhdr.1.2; omega
  have hmid_lt : ∀ t ∈ mid, t < cert.nBpe := fun t ht => by
    have := Nat.le_of_ble_eq_true (hhdr.2 t ht); omega
  have htr0 := hv.trInfo_spec hs0_lt
  have htrL := hv.trInfo_spec hsL_lt
  let w := cert.cegarWit fid
  let i1 := w % 128; let j1 := (w / 128) % 16; let i2 := (w / 2048) % 128; let j2 := (w / 262144) % 16
  rcases hti0 : cert.trInfo s0 with ⟨r0, s1_0⟩
  rcases htiL : cert.trInfo sL with ⟨rL, s1_L⟩
  simp only [hti0] at htr0; simp only [htiL] at htrL
  rcases hsi0 : cert.sym1Info s1_0 with ⟨m0, d0, t0⟩
  rcases hsiL : cert.sym1Info s1_L with ⟨mL, dL, tL⟩
  let len0 := 10 * r0 + m0 + 1
  let lenL := 10 * rL + mL + 1
  have hti0' : cert.trInfo (cert.cegarFirst fid) = (r0, s1_0) := hti0
  have htiL' : cert.trInfo (cert.cegarLast fid) = (rL, s1_L) := htiL
  simp only [hti0', htiL', hsi0, hsiL] at hc
  have hok : (Nat.ble (i1 + 1) len0 && Nat.ble (j1 + 1) (12 - l2PieceDef r0 m0 d0 i1) &&
      (Nat.ble i2 lenL && (if Nat.beq i2 lenL then Nat.beq j2 0
        else Nat.ble (j2 + 1) (12 - l2PieceDef rL mL dL i2)))) = true := by
    by_contra hf
    have hff := Bool.eq_false_iff.mpr hf
    change (if !(Nat.ble (i1 + 1) len0 && Nat.ble (j1 + 1) (12 - l2PieceDef r0 m0 d0 i1) &&
      (Nat.ble i2 lenL && (if Nat.beq i2 lenL then Nat.beq j2 0
        else Nat.ble (j2 + 1) (12 - l2PieceDef rL mL dL i2)))) = true then false else _) = true at hc
    rw [hff] at hc; cases hc
  change (if !(Nat.ble (i1 + 1) len0 && Nat.ble (j1 + 1) (12 - l2PieceDef r0 m0 d0 i1) &&
    (Nat.ble i2 lenL && (if Nat.beq i2 lenL then Nat.beq j2 0
      else Nat.ble (j2 + 1) (12 - l2PieceDef rL mL dL i2)))) = true then false else _) = true at hc
  rw [hok] at hc
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  have hcan : S.canon 13 (pieceAdvance 13 j1 (walkL2Prefix13 cert r0 s1_0 m0 i1)) =
      S.canon 13 (pieceAdvance 13 j2 (compose13
        (mid.foldl (fun acc tok => compose13 acc (cert.bpeElem tok)) (cert.bpeElem s0))
        (walkL2Prefix13 cert rL s1_L mL i2))) := Nat.eq_of_beq_eq_true hc
  simp only [Bool.and_eq_true] at hok
  have hi1_lt : i1 < len0 := by have := Nat.le_of_ble_eq_true hok.1.1; omega
  have hi2_le : i2 ≤ lenL := Nat.le_of_ble_eq_true hok.2.1
  let W0 := expandTrSym cert s0
  let WM := expandTrWord cert (mid.flatMap (bpeWord cert))
  let WL := expandTrSym cert sL
  let W := expandTrWord cert (cegarWord cert fid)
  have hW_eq : W = (W0 ++ WM) ++ WL := by
    simp [W, cegarWord, expandTrWord, W0, WM, WL, s0, mid, sL]
  have hW0_eq : W0 = expandL2Sym r0 m0 d0 t0 := by simp [W0, expandTrSym, hti0, hsi0]
  have hWL_eq : WL = expandL2Sym rL mL dL tL := by simp [WL, expandTrSym, htiL, hsiL]
  have hlenW0 : W0.length = len0 := by rw [hW0_eq]; exact expandL2Sym_len r0 m0 d0 t0
  have hlenWL : WL.length = lenL := by rw [hWL_eq]; exact expandL2Sym_len rL mL dL tL
  let i2_abs := (W0 ++ WM).length + i2
  have h12 : i1 < i2_abs := by simp [i2_abs, hlenW0]; omega
  have hi2_W : i2_abs ≤ W.length := by rw [hW_eq, List.length_append, hlenWL]; omega
  have hj1 : j1 < 12 - (W.getD i1 (0, 0)).1 := by
    have hgd : (W.getD i1 (0, 0)).1 = (W0.getD i1 (0, 0)).1 := by
      rw [hW_eq, List.append_assoc]; simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rw [hgd, hW0_eq, expandL2Sym_getD r0 m0 d0 t0 i1 hi1_lt]
    have := Nat.le_of_ble_eq_true hok.1.2; omega
  have hj2 : if i2_abs < W.length then j2 < 12 - (W.getD i2_abs (0, 0)).1 else j2 = 0 := by
    by_cases hlt : i2 < lenL
    · have hlt' : i2_abs < W.length := by rw [hW_eq, List.length_append, hlenWL]; omega
      simp only [hlt', ↓reduceIte]
      have hgd : (W.getD i2_abs (0, 0)).1 = (WL.getD i2 (0, 0)).1 := by
        rw [hW_eq]; simp only [i2_abs, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      rw [hgd, hWL_eq, expandL2Sym_getD rL mL dL tL i2 hlt]
      have hne : Nat.beq i2 lenL = false := by cases hc2 : Nat.beq i2 lenL with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc2; omega
      have h2 := hok.2.2; simp only [hne, Bool.false_eq_true, ↓reduceIte] at h2
      have := Nat.le_of_ble_eq_true h2; omega
    · have heq : i2 = lenL := by omega
      have hnotlt : ¬ (i2_abs < W.length) := by rw [hW_eq, List.length_append, hlenWL]; omega
      simp only [hnotlt, ↓reduceIte]
      have h2 := hok.2.2; have hb : Nat.beq i2 lenL = true := by rw [heq]; exact Nat.beq_refl _
      simp only [hb, ↓reduceIte] at h2
      exact Nat.eq_of_beq_eq_true h2
  have he1 : walkL2Prefix13 cert r0 s1_0 m0 i1 = walkWordFast 13 (W.take i1) (S.idc 13) := by
    have ht1 : W.take i1 = W0.take i1 := by
      rw [hW_eq, List.append_assoc, List.take_append_of_le_length (by omega)]
    rw [ht1, hW0_eq]
    have hsp := walkL2Prefix13_spec hv htr0.1 htr0.2.1 (i := i1) (by rw [hsi0]; omega)
    simpa [hsi0] using hsp
  have hgMid : mid.foldl (fun acc tok => compose13 acc (cert.bpeElem tok)) (cert.bpeElem s0) =
      walkWordFast 13 (W0 ++ WM) (S.idc 13) := by
    have hs0_bpe : s0 < cert.nBpe := by have := hv.hBpeGe; omega
    rw [bpeElem_spec hv s0 hs0_bpe]
    have hbw0 : bpeWord cert s0 = [s0] := by unfold bpeWord; simp [bpeWordAux]; omega
    rw [hbw0]
    simpa [expandTrWord, W0, WM] using foldl_bpeElem_spec hv mid W0 hmid_lt
  have he2 : compose13 (mid.foldl (fun acc tok => compose13 acc (cert.bpeElem tok)) (cert.bpeElem s0))
      (walkL2Prefix13 cert rL s1_L mL i2) = walkWordFast 13 (W.take i2_abs) (S.idc 13) := by
    rw [hgMid]
    have hsp := walkL2Prefix13_spec hv htrL.1 htrL.2.1 (i := i2) (by rw [hsiL]; omega)
    have hsp' : walkL2Prefix13 cert rL s1_L mL i2 = walkWordFast 13 (WL.take i2) (S.idc 13) := by
      rw [hWL_eq]; simpa [hsiL] using hsp
    rw [hsp', ← walkWordFast_append_compose13]
    have ht2 : W.take i2_abs = (W0 ++ WM) ++ WL.take i2 := by
      rw [hW_eq, List.take_append]
      simp [i2_abs, List.take_of_length_le]
    rw [ht2]
  rw [he1, he2] at hcan
  exact not_infix_of_two_point (by omega) (by omega) hchain hmatch h12 hi2_W hj1 hj2 hcan hinf

/-! #### 5c. O(1) AC Automaton Invariant & Direct Dead Leaf Suffix Soundness -/

theorem L2CertValid.trie_struct {cert : L2Cert} (hv : L2CertValid cert) {u : Nat}
    (h1 : 1 ≤ u) (hu : u < cert.nAlive) :
    getStPar cert u < u ∧ getStSym cert u < 10 ∧ getStFail cert u < u ∧
    getStPsi cert u ≤ cert.maxTrPsi (getStSym cert u) := by
  have h := hv.htrie u h1 hu; unfold trieStateCheck at h
  cases hok : (Nat.ble (getStPar cert u + 1) u && Nat.ble (getStSym cert u + 1) 10 &&
      Nat.ble (getStFail cert u + 1) u && Nat.ble (getStPsi cert u) (cert.maxTrPsi (getStSym cert u))) with
  | false =>
    change (if !(Nat.ble (getStPar cert u + 1) u && Nat.ble (getStSym cert u + 1) 10 &&
      Nat.ble (getStFail cert u + 1) u && Nat.ble (getStPsi cert u) (cert.maxTrPsi (getStSym cert u))) = true then false else _) = true at h
    rw [hok] at h; cases h
  | true =>
    simp only [Bool.and_eq_true] at hok
    exact ⟨by have := Nat.le_of_ble_eq_true hok.1.1.1; omega,
      by have := Nat.le_of_ble_eq_true hok.1.1.2; omega,
      by have := Nat.le_of_ble_eq_true hok.1.2; omega,
      Nat.le_of_ble_eq_true hok.2⟩

theorem L2CertValid.trie_fail_and_edges {cert : L2Cert} (hv : L2CertValid cert) {u : Nat}
    (h1 : 1 ≤ u) (hu : u < cert.nAlive) :
    (if getStPar cert u = 0 then getStFail cert u = 0
     else 1 ≤ getStFail cert u ∧ getStFail cert u = getGo cert (getStFail cert (getStPar cert u)) (getStSym cert u)) ∧
    (∀ li < 10, trieEdgeCheckOne cert u (getStPsi cert u) li
      (getGo cert u li) (getGo cert (getStFail cert u) li)
      (cert.longPos li) (cert.longNeg li) (cert.longD1Psi li) = true) := by
  have h := hv.htrie u h1 hu; unfold trieStateCheck at h
  have hst := hv.trie_struct h1 hu
  have hok1 : (Nat.ble (getStPar cert u + 1) u && Nat.ble (getStSym cert u + 1) 10 &&
      Nat.ble (getStFail cert u + 1) u && Nat.ble (getStPsi cert u) (cert.maxTrPsi (getStSym cert u))) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨Nat.ble_eq_true_of_le (by omega), Nat.ble_eq_true_of_le (by omega)⟩,
      Nat.ble_eq_true_of_le (by omega)⟩, Nat.ble_eq_true_of_le hst.2.2.2⟩
  change (if !(Nat.ble (getStPar cert u + 1) u && Nat.ble (getStSym cert u + 1) 10 &&
    Nat.ble (getStFail cert u + 1) u && Nat.ble (getStPsi cert u) (cert.maxTrPsi (getStSym cert u))) = true then false else _) = true at h
  rw [hok1] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  cases hokf : (if Nat.beq (getStPar cert u) 0 then Nat.beq (getStFail cert u) 0
      else Nat.ble 1 (getStFail cert u) &&
        Nat.beq (getStFail cert u) (getGo cert (getStFail cert (getStPar cert u)) (getStSym cert u))) with
  | false =>
    change (if !(if Nat.beq (getStPar cert u) 0 then Nat.beq (getStFail cert u) 0
      else Nat.ble 1 (getStFail cert u) &&
        Nat.beq (getStFail cert u) (getGo cert (getStFail cert (getStPar cert u)) (getStSym cert u))) = true then false else _) = true at h
    rw [hokf] at h; cases h
  | true =>
    change (if !(if Nat.beq (getStPar cert u) 0 then Nat.beq (getStFail cert u) 0
      else Nat.ble 1 (getStFail cert u) &&
        Nat.beq (getStFail cert u) (getGo cert (getStFail cert (getStPar cert u)) (getStSym cert u))) = true then false else _) = true at h
    rw [hokf] at h; simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    constructor
    · by_cases hp0 : getStPar cert u = 0
      · simp only [hp0, ↓reduceIte]; simp only [hp0, Nat.beq_refl, ↓reduceIte] at hokf
        exact Nat.eq_of_beq_eq_true hokf
      · have hne : Nat.beq (getStPar cert u) 0 = false := by
          cases hc : Nat.beq (getStPar cert u) 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hp0
        simp only [hp0, ↓reduceIte]; simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hokf
        exact ⟨Nat.le_of_ble_eq_true hokf.1, Nat.eq_of_beq_eq_true hokf.2⟩
    · intro li hli
      interval_cases li
      · exact h.1.1.1.1.1.1.1.1.1
      · exact h.1.1.1.1.1.1.1.1.2
      · exact h.1.1.1.1.1.1.1.2
      · exact h.1.1.1.1.1.1.2
      · exact h.1.1.1.1.1.2
      · exact h.1.1.1.1.2
      · exact h.1.1.1.2
      · exact h.1.1.2
      · exact h.1.2
      · exact h.2

theorem statePrefAux_eq_of_ge {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ (u fuel : Nat), u < cert.nAlive → u ≤ fuel → statePrefAux cert fuel u = statePref cert u
  | 0, fuel, _, _ => by cases fuel <;> rfl
  | u + 1, fuel + 1, hu, hle => by
    have hp : getStPar cert (u + 1) < u + 1 := (hv.trie_struct (by omega) hu).1
    unfold statePref; simp only [statePrefAux]; congr 1
    rw [statePrefAux_eq_of_ge hv _ fuel (by omega) (by omega),
      statePrefAux_eq_of_ge hv _ u (by omega) (by omega)]
  | u + 1, 0, _, hle => by omega

theorem statePref_pos {cert : L2Cert} (hv : L2CertValid cert) {u : Nat} (h1 : 1 ≤ u) (hu : u < cert.nAlive) :
    statePref cert u = statePref cert (getStPar cert u) ++ [getStSym cert u] := by
  cases u with
  | zero => omega
  | succ u' =>
    have hp : getStPar cert (u' + 1) < u' + 1 := (hv.trie_struct (by omega) hu).1
    unfold statePref; simp only [statePrefAux]; congr 1
    exact statePrefAux_eq_of_ge hv _ u' (by omega) (by omega)

theorem matchBPETokRev_spec {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ (fuel u tok u' : Nat), u < cert.nAlive → tok < cert.nBpe →
      matchBPETokRev cert fuel u tok = some u' →
      u' < cert.nAlive ∧ statePref cert u = statePref cert u' ++ bpeWord cert tok
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, u, tok, u', hu, htok, h => by
    unfold matchBPETokRev at h
    by_cases hlt : tok < cert.nLong + cert.nPair
    · have hbt : Nat.ble (tok + 1) (cert.nLong + cert.nPair) = true := Nat.ble_eq_true_of_le (by omega)
      simp only [hbt, ↓reduceIte] at h
      by_cases hu0 : u = 0
      · subst hu0; simp at h
      · have hne0 : Nat.beq u 0 = false := by cases hc : Nat.beq u 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hu0
        simp only [hne0, Bool.false_eq_true, ↓reduceIte] at h
        cases hsym : Nat.beq (getStSym cert u) tok with
        | false =>
          change (if Nat.beq (getStSym cert u) tok = true then some (getStPar cert u) else none) = some u' at h
          rw [hsym] at h; cases h
        | true =>
          change (if Nat.beq (getStSym cert u) tok = true then some (getStPar cert u) else none) = some u' at h
          rw [hsym] at h; simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          have hp := (hv.trie_struct (by omega) hu).1
          have hbw : bpeWord cert tok = [tok] := by unfold bpeWord; simp [bpeWordAux, hlt]
          rw [hbw, ← Nat.eq_of_beq_eq_true hsym]
          exact ⟨by omega, statePref_pos hv (by omega) hu⟩
    · have hbf : Nat.ble (tok + 1) (cert.nLong + cert.nPair) = false := by
        cases hc : Nat.ble (tok + 1) (cert.nLong + cert.nPair) with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hl, hr, hbw⟩ := bpeWord_merge hv htok (by omega)
      cases h1 : matchBPETokRev cert fuel u (cert.bpeRight tok) with
      | none => rw [h1] at h; cases h
      | some u1 =>
        rw [h1] at h
        obtain ⟨hu1, hp1⟩ := matchBPETokRev_spec hv fuel u (cert.bpeRight tok) u1 hu (by omega) h1
        obtain ⟨hu', hp2⟩ := matchBPETokRev_spec hv fuel u1 (cert.bpeLeft tok) u' hu1 (by omega) h
        refine ⟨hu', ?_⟩
        rw [hp1, hp2, hbw, List.append_assoc]

theorem matchBPEListRev_spec {cert : L2Cert} (hv : L2CertValid cert) (fuel : Nat) :
    ∀ (toks : List Nat) (u u' : Nat), u < cert.nAlive → (∀ t ∈ toks, t < cert.nBpe) →
      matchBPEListRev cert fuel u toks.reverse = some u' →
      u' < cert.nAlive ∧ statePref cert u = statePref cert u' ++ toks.flatMap (bpeWord cert) := by
  intro toks
  induction toks using List.reverseRecOn with
  | nil =>
    intro u u' hu _ h
    simp only [List.reverse_nil, matchBPEListRev, Option.some.injEq] at h
    subst h; exact ⟨hu, by simp⟩
  | append_singleton init tok ih =>
    intro u u' hu htoks h
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at h
    unfold matchBPEListRev at h
    cases h1 : matchBPETokRev cert fuel u tok with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      obtain ⟨hu1, hp1⟩ := matchBPETokRev_spec hv fuel u tok u1 hu (htoks tok (by simp)) h1
      obtain ⟨hu', hp2⟩ := ih u1 u' hu1 (fun t ht => htoks t (List.mem_append_left _ ht)) h
      refine ⟨hu', ?_⟩
      rw [hp1, hp2, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-- If `deadLeafU fid = u > 0` and `deadLeafLi fid = li`, then `cegarWord cert fid <:+ statePref cert u ++ [li]`. -/
theorem cegarLeaf_suffix {cert : L2Cert} (hv : L2CertValid cert) {fid : Nat} (hfid : fid < cert.nCegar)
    (hpos : 0 < cert.deadLeafU fid) :
    cegarWord cert fid <:+ statePref cert (cert.deadLeafU fid) ++ [cert.deadLeafLi fid] := by
  have hchk := hv.hcegarLeaf fid hfid; unfold cegarLeafCheck at hchk
  have hne0 : Nat.beq (cert.deadLeafU fid) 0 = false := by
    cases hc : Nat.beq (cert.deadLeafU fid) 0 with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc; omega
  simp only [hne0, Bool.false_eq_true, ↓reduceIte] at hchk
  cases hhdr : (Nat.ble (cert.deadLeafU fid + 1) cert.nAlive && Nat.ble (cert.deadLeafLi fid + 1) cert.nLong &&
      Nat.beq (cert.cegarLast fid) (cert.deadLeafLi fid)) with
  | false => simp only [hhdr, Bool.not_false, ↓reduceIte] at hchk; cases hchk
  | true =>
    simp only [hhdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
    simp only [Bool.and_eq_true] at hhdr
    have hu_lt : cert.deadLeafU fid < cert.nAlive := by have := Nat.le_of_ble_eq_true hhdr.1.1; omega
    have hlast : cert.cegarLast fid = cert.deadLeafLi fid := Nat.eq_of_beq_eq_true hhdr.2
    -- Extract mid tokens < nBpe from cegarWitCheck!
    have hmid_lt : ∀ t ∈ cert.cegarMid fid, t < cert.nBpe := by
      have hw := hv.hcegarWit fid hfid; unfold cegarWitCheck at hw
      cases hb : (Nat.ble (cert.cegarFirst fid + 1) (cert.nLong + cert.nPair) &&
          Nat.ble (cert.cegarLast fid + 1) (cert.nLong + cert.nPair) &&
          (cert.cegarMid fid).all (fun t => Nat.ble (t + 1) cert.nBpe)) with
      | false => simp only [hb, Bool.not_false, ↓reduceIte] at hw; cases hw
      | true =>
        simp only [Bool.and_eq_true, List.all_eq_true] at hb
        intro t ht; have := Nat.le_of_ble_eq_true (hb.2 t ht); omega
    cases hm : matchBPEListRev cert 64 (cert.deadLeafU fid) (cert.cegarMid fid).reverse with
    | none => rw [hm] at hchk; cases hchk
    | some u1 =>
      rw [hm] at hchk
      by_cases hu10 : u1 = 0
      · subst hu10; simp at hchk
      · have hne1 : Nat.beq u1 0 = false := by cases hc : Nat.beq u1 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hu10
        simp only [hne1, Bool.false_eq_true, ↓reduceIte] at hchk
        have hfst : getStSym cert u1 = cert.cegarFirst fid := Nat.eq_of_beq_eq_true hchk
        obtain ⟨hu1_lt, hpref_u⟩ := matchBPEListRev_spec hv 64 (cert.cegarMid fid) (cert.deadLeafU fid) u1 hu_lt hmid_lt hm
        have hpref_u1 := statePref_pos hv (by omega) hu1_lt
        refine ⟨statePref cert (getStPar cert u1), ?_⟩
        unfold cegarWord
        rw [hpref_u, hpref_u1, hfst, hlast]
        simp only [List.append_assoc]

/-- **Simultaneous O(1) AC Soundness Induction** on `u < nAlive`:
  1. `statePref (getStFail u) <:+ statePref u` (for `u > 0`),
  2. For every `li < 10`, let `v = getGo u li`:
     - if `1 ≤ v < nAlive`, then `statePref v <:+ statePref u ++ [li]`;
     - if `v = 0 ∨ deadLeafBase ≤ v`, then `∃ fid < nCegar, cegarWord fid <:+ statePref u ++ [li]`. -/
theorem ac_sound {cert : L2Cert} (hv : L2CertValid cert) :
    ∀ u < cert.nAlive,
      (1 ≤ u → statePref cert (getStFail cert u) <:+ statePref cert u) ∧
      (∀ li < 10,
        let v := getGo cert u li
        (1 ≤ v → v < cert.nAlive → statePref cert v <:+ statePref cert u ++ [li]) ∧
        (v = 0 ∨ deadLeafBase ≤ v → ∃ fid < cert.nCegar, cegarWord cert fid <:+ statePref cert u ++ [li])) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu
    cases u with
    | zero =>
      refine ⟨fun h => by omega, fun li hli => ?_⟩
      have hd1 := hv.d1Long_spec (by rw [hv.nLong_eq]; exact hli)
      have hgo : getGo cert 0 li = cert.d1Long li := hd1.2.2.2.2.2.1
      rw [hgo]
      refine ⟨fun _ _ => ?_, fun hbad => ?_⟩
      · have hp := statePref_pos hv hd1.1 hd1.2.1
        rw [hp, hd1.2.2.1, hd1.2.2.2.1]
      · have := hv.hAliveBound; have := hd1.1; have := hd1.2.1; omega
    | succ u' =>
      have hu1 : 1 ≤ u' + 1 := by omega
      have hst := hv.trie_struct hu1 hu
      obtain ⟨hfail_chk, hedges⟩ := hv.trie_fail_and_edges hu1 hu
      -- Part 1: statePref (getStFail (u'+1)) <:+ statePref (u'+1)
      have hfail_suf : statePref cert (getStFail cert (u' + 1)) <:+ statePref cert (u' + 1) := by
        by_cases hp0 : getStPar cert (u' + 1) = 0
        · simp only [hp0, ↓reduceIte] at hfail_chk
          rw [hfail_chk]; simp [statePref, statePrefAux]
        · simp only [hp0, ↓reduceIte] at hfail_chk
          have hpar_lt : getStPar cert (u' + 1) < u' + 1 := hst.1
          have hpar_ih := ih (getStPar cert (u' + 1)) hpar_lt (by omega)
          have hpar_fail_suf : statePref cert (getStFail cert (getStPar cert (u' + 1))) <:+
              statePref cert (getStPar cert (u' + 1)) := hpar_ih.1 (by omega)
          have hfp_lt : getStFail cert (getStPar cert (u' + 1)) < getStPar cert (u' + 1) :=
            (hv.trie_struct (by omega) (by omega)).2.2.1
          have hgo_ih := (ih (getStFail cert (getStPar cert (u' + 1))) (by omega) (by omega)).2 (getStSym cert (u' + 1)) hst.2.1
          have hgo_suf : statePref cert (getStFail cert (u' + 1)) <:+
              statePref cert (getStFail cert (getStPar cert (u' + 1))) ++ [getStSym cert (u' + 1)] := by
            have := hgo_ih.1 (by rw [← hfail_chk.2]; exact hfail_chk.1) (by rw [← hfail_chk.2]; omega)
            rwa [← hfail_chk.2] at this
          rw [statePref_pos hv hu1 hu]
          exact suffix_trans_append hgo_suf hpar_fail_suf
      refine ⟨fun _ => hfail_suf, fun li hli => ?_⟩
      have he := hedges li hli
      unfold trieEdgeCheckOne at he
      set v := getGo cert (u' + 1) li
      set fv := getGo cert (getStFail cert (u' + 1)) li
      have hf_ih := (ih (getStFail cert (u' + 1)) hst.2.2.1 (by omega)).2 li hli
      refine ⟨fun hv1 hv_lt => ?_, fun hdead => ?_⟩
      · have hne0 : Nat.beq v 0 = false := by cases hc : Nat.beq v 0 with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc; omega
        have hnd : Nat.ble deadLeafBase v = false := by
          cases hc : Nat.ble deadLeafBase v with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; have := hv.hAliveBound; omega
        simp only [hne0, hnd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at he
        by_cases hvf : v = fv
        · have hs1 : statePref cert v <:+ statePref cert (getStFail cert (u' + 1)) ++ [li] := by
            rw [hvf]; exact hf_ih.1 (by omega) (by omega)
          exact suffix_trans_append hs1 hfail_suf
        · have hne_f : Nat.beq v fv = false := by cases hc : Nat.beq v fv with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hvf
          have h2 := he.2; simp only [hne_f, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h2
          have hparv : getStPar cert v = u' + 1 := Nat.eq_of_beq_eq_true h2.1.1
          have hsymv : getStSym cert v = li := Nat.eq_of_beq_eq_true h2.1.2
          rw [statePref_pos hv hv1 hv_lt, hparv, hsymv]
      · rcases hdead with hv0 | hvd
        · simp only [hv0, Nat.beq_refl, ↓reduceIte, Bool.or_eq_true] at he
          have hfv_dead : fv = 0 ∨ deadLeafBase ≤ fv := by
            rcases he with h0 | hd
            · exact Or.inl (Nat.eq_of_beq_eq_true h0)
            · exact Or.inr (Nat.le_of_ble_eq_true hd)
          obtain ⟨fid, hfid, hsuf⟩ := hf_ih.2 hfv_dead
          exact ⟨fid, hfid, suffix_trans_append hsuf hfail_suf⟩
        · have hne0 : Nat.beq v 0 = false := by cases hc : Nat.beq v 0 with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc; unfold deadLeafBase at hvd; omega
          have hbd : Nat.ble deadLeafBase v = true := Nat.ble_eq_true_of_le hvd
          simp only [hne0, hbd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at he
          let fid := v - deadLeafBase
          have hfid : fid < cert.nCegar := by have := Nat.le_of_ble_eq_true he.1.1; omega
          have hdu : cert.deadLeafU fid = u' + 1 := Nat.eq_of_beq_eq_true he.1.2
          have hdli : cert.deadLeafLi fid = li := Nat.eq_of_beq_eq_true he.2
          have hsuf := cegarLeaf_suffix hv hfid (by rw [hdu]; omega)
          rw [hdu, hdli] at hsuf
          exact ⟨fid, hfid, hsuf⟩

/-! ### 6. Level-1 & Level-2 Segmentation and Inductive Simulation -/

/-- Greedily split raw transitions `ts` into L1 tokens `[(m, d, t), ...]` + trailing `(0, 4)` count. -/
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
      simpa [List.replicate_succ', List.append_assoc] using splitMacroAux_expand (acc + 1) rest
    · have hne : (d == 0 && t == 4) = false := by cases hd : (d == 0) <;> cases ht : (t == 4) <;> simp_all
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitMacroAux_expand 0 rest
      cases hs : splitMacroAux 0 rest with
      | mk ms mt =>
        rw [hs] at ih
        simp only [expandMacroList, List.flatMap_cons, expandSym, List.append_assoc, List.singleton_append]
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
    · have hne : (d == 0 && t == 4) = false := by cases hd : (d == 0) <;> cases ht : (t == 4) <;> simp_all
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitMacroAux_props 0 rest ht5'
      cases hs : splitMacroAux 0 rest with
      | mk ms mt =>
        rw [hs] at ih
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨h, ht5 (d, t) List.mem_cons_self⟩
        · exact ih x hx'

/-- Greedily split L1 tokens `ms` into L2 tokens `[(r, (m, d, t)), ...]` + trailing `symA13` count. -/
def splitL2Aux : Nat → List (Nat × Nat × Nat) → List (Nat × (Nat × Nat × Nat)) × Nat
  | r, [] => ([], r)
  | r, tok :: rest =>
    if tok == symA13 then splitL2Aux (r + 1) rest
    else
      let (l2s, rt) := splitL2Aux 0 rest
      ((r, tok) :: l2s, rt)

def expandL2List (l2s : List (Nat × (Nat × Nat × Nat))) : List (Nat × Nat) :=
  l2s.flatMap fun (r, (m, d, t)) => expandL2Sym r m d t

theorem splitL2Aux_expand :
    ∀ (r : Nat) (ms : List (Nat × Nat × Nat)),
      let (l2s, rt) := splitL2Aux r ms
      expandSymARep r ++ expandMacroList ms = expandL2List l2s ++ expandSymARep rt
  | r, [] => by simp [splitL2Aux, expandMacroList, expandL2List]
  | r, tok :: rest => by
    simp only [splitL2Aux]
    by_cases h : tok = symA13
    · subst h
      simp only [beq_self_eq_true, ↓reduceIte]
      have ih := splitL2Aux_expand (r + 1) rest
      have h1 : expandSymARep (r + 1) = expandSymARep r ++ expandSym 9 2 4 := by
        rw [expandSymARep_add]; simp [expandSymARep, symA13]
      simpa [h1, expandMacroList, symA13, List.append_assoc] using ih
    · have hne : (tok == symA13) = false := by cases hc : (tok == symA13) with | false => rfl | true => exact absurd (beq_iff_eq.mp hc) h
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitL2Aux_expand 0 rest
      cases hs : splitL2Aux 0 rest with
      | mk l2s rt =>
        rw [hs] at ih
        rcases tok with ⟨m, d, t⟩
        simp only [expandL2List, List.flatMap_cons, expandL2Sym, expandMacroList, List.append_assoc]
        simpa [expandSymARep, expandL2List, expandL2Sym, expandMacroList] using ih

theorem splitL2Aux_props :
    ∀ (r : Nat) (ms : List (Nat × Nat × Nat)),
      (∀ x ∈ ms, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5) →
      let (l2s, _rt) := splitL2Aux r ms
      ∀ x ∈ l2s, x.2 ≠ symA13 ∧ ¬ (x.2.2.1 = 0 ∧ x.2.2.2 = 4) ∧ x.2.2.2 < 5
  | _, [], _ => by simp [splitL2Aux]
  | r, tok :: rest, hp => by
    simp only [splitL2Aux]
    have hp' : ∀ x ∈ rest, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5 := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    by_cases h : tok = symA13
    · subst h; simp only [beq_self_eq_true, ↓reduceIte]; exact splitL2Aux_props (r + 1) rest hp'
    · have hne : (tok == symA13) = false := by cases hc : (tok == symA13) with | false => rfl | true => exact absurd (beq_iff_eq.mp hc) h
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have ih := splitL2Aux_props 0 rest hp'
      cases hs : splitL2Aux 0 rest with
      | mk l2s rt =>
        rw [hs] at ih
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨h, hp tok List.mem_cons_self⟩
        · exact ih x hx'

/-- The 4 disjoint state kinds of the Level-2 automaton. -/
inductive L2State where
  | root
  | trie (u : Nat)
  | pair (pi : Nat)
  | rootS1 (s1 : Nat)

def statePsi (cert : L2Cert) : L2State → Nat → Option Nat
  | .root, f => cert.rootPsi f
  | .trie u, f => if f == 2 then some (getStPsi cert u) else none
  | .pair pi, f => cert.pairPsi pi f
  | .rootS1 s1, f => cert.rootS1Psi s1 f

def stateLastS1 (cert : L2Cert) : L2State → Option Nat
  | .root => none
  | .trie u => some (cert.trInfo (getStSym cert u)).2
  | .pair pi => some (cert.trInfo (cert.nLong + pi)).2
  | .rootS1 s1 => some s1

def stateD0 (cert : L2Cert) : L2State → Bool
  | .root => false
  | .trie _ => false
  | .pair _ => false
  | .rootS1 s1 => Nat.beq (cert.sym1Info s1).2.1 0

def stateCanA (cert : L2Cert) (st : L2State) : Bool :=
  match stateLastS1 cert st with
  | none => true
  | some lc => !isForb1 cert lc cert.idA

def StateInv (cert : L2Cert) (st : L2State) (done : List (Nat × (Nat × Nat × Nat))) : Prop :=
  match st with
  | .root => True
  | .trie u => 1 ≤ u ∧ u < cert.nAlive ∧ expandTrWord cert (statePref cert u) <:+ expandL2List done
  | .pair pi => pi < cert.nPair ∧ expandTrWord cert [cert.nLong + pi] <:+ expandL2List done
  | .rootS1 s1 => s1 < cert.alpha1 ∧ s1 ≠ cert.idA ∧
      (let (m, d, t) := cert.sym1Info s1; expandSym m d t <:+ expandL2List done)

/-- If `stateLastS1 cert st = some lc` and `StateInv cert st done`, then `lc < alpha1` and `expandSym lc <:+ expandL2List done`. -/
theorem stateLastS1_suffix {cert : L2Cert} (hv : L2CertValid cert) {st : L2State}
    {done : List (Nat × (Nat × Nat × Nat))} (hinv : StateInv cert st done) {lc : Nat}
    (hlc : stateLastS1 cert st = some lc) :
    lc < cert.alpha1 ∧
    expandSym (cert.sym1Info lc).1 (cert.sym1Info lc).2.1 (cert.sym1Info lc).2.2 <:+ expandL2List done := by
  cases st with
  | root => cases hlc
  | trie u =>
    simp only [stateLastS1, Option.some.injEq] at hlc; subst hlc
    obtain ⟨hu1, hu, hsuf⟩ := hinv
    have hsym_lt : getStSym cert u < 10 := (hv.trie_struct hu1 hu).2.1
    have htr := hv.trInfo_spec (ti := getStSym cert u) (by rw [hv.nLong_eq]; omega)
    refine ⟨htr.2.1, ?_⟩
    have hpref := statePref_pos hv hu1 hu
    have hs1 : expandTrSym cert (getStSym cert u) <:+ expandTrWord cert (statePref cert u) := by
      have : [getStSym cert u] <:+ statePref cert u := ⟨statePref cert (getStPar cert u), hpref.symm⟩
      simpa [expandTrWord] using expandTrWord_suffix cert this
    have hs2 : expandSym (cert.sym1Info (cert.trInfo (getStSym cert u)).2).1
        (cert.sym1Info (cert.trInfo (getStSym cert u)).2).2.1
        (cert.sym1Info (cert.trInfo (getStSym cert u)).2).2.2 <:+ expandTrSym cert (getStSym cert u) := by
      unfold expandTrSym expandL2Sym; exact List.suffix_append _ _
    exact (hs2.trans hs1).trans hsuf
  | pair pi =>
    simp only [stateLastS1, Option.some.injEq] at hlc; subst hlc
    obtain ⟨hpi, hsuf⟩ := hinv
    have htr := hv.trInfo_spec (ti := cert.nLong + pi) (by omega)
    refine ⟨htr.2.1, ?_⟩
    have hs2 : expandSym (cert.sym1Info (cert.trInfo (cert.nLong + pi)).2).1
        (cert.sym1Info (cert.trInfo (cert.nLong + pi)).2).2.1
        (cert.sym1Info (cert.trInfo (cert.nLong + pi)).2).2.2 <:+ expandTrWord cert [cert.nLong + pi] := by
      simp only [expandTrWord, List.flatMap_singleton, expandTrSym, expandL2Sym]
      exact List.suffix_append _ _
    exact hs2.trans hsuf
  | rootS1 s1 =>
    simp only [stateLastS1, Option.some.injEq] at hlc; subst hlc
    exact ⟨hinv.1, hinv.2.2⟩

/-- If `stateD0 cert st = true` and `StateInv cert st done`, then `[(0, t)] <:+ expandL2List done` for some `t < 4`. -/
theorem stateD0_ends_zero {cert : L2Cert} (hv : L2CertValid cert) {st : L2State}
    {done : List (Nat × (Nat × Nat × Nat))} (hinv : StateInv cert st done) (hd0 : stateD0 cert st = true) :
    ∃ t < 4, [(0, t)] <:+ expandL2List done := by
  cases st with
  | root => cases hd0
  | trie _ => cases hd0
  | pair _ => cases hd0
  | rootS1 s1 =>
    simp only [stateD0] at hd0
    have hd_eq : (cert.sym1Info s1).2.1 = 0 := Nat.eq_of_beq_eq_true hd0
    have hchk := hv.hl1Elem s1 hinv.1; unfold l1ElemCheck at hchk
    rcases hsi : cert.sym1Info s1 with ⟨m, d, t⟩
    rw [hsi] at hd_eq hchk; dsimp only at hd_eq hchk; subst hd_eq
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_self_eq_true,
      Bool.true_eq_false, false_or, beq_eq_false_iff_ne] at hchk
    have ht5 : t < 5 := by have := Nat.le_of_ble_eq_true hchk.1.1.2; omega
    have htne4 : t ≠ 4 := hchk.1.2
    refine ⟨t, by omega, ?_⟩
    have hsuf := hinv.2.2; rw [hsi] at hsuf
    exact (List.suffix_append (List.replicate m (0, 4)) [(0, t)]).trans hsuf

theorem m_le_10_of_base {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {m : Nat} (hinf : List.replicate m (0, 4) <:+: ts) : m ≤ 10 := by
  by_contra hgt
  have hsub : List.replicate 11 (0, 4) <:+: List.replicate m (0, 4) := by
    refine ⟨[], List.replicate (m - 11) (0, 4), ?_⟩
    simp only [List.nil_append, ← List.replicate_add]; congr 1; omega
  exact not_infix_of_checkWitness (by omega) (by omega) hchain hmatch hv.base_collisions.1 (hsub.trans hinf)

theorem m_eq_zero_after_d0 {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {t m : Nat} (ht4 : t < 4)
    (hinf : ([(0, t)] ++ List.replicate m (0, 4)) <:+: ts) : m = 0 := by
  cases m with
  | zero => rfl
  | succ m' =>
    have hsub : [(0, t), (0, 4)] <:+: ([(0, t)] ++ List.replicate (m' + 1) (0, 4)) :=
      ⟨[], List.replicate m' (0, 4), by simp [List.replicate_succ]⟩
    exact False.elim (not_infix_of_checkWitness (by omega) (by omega) hchain hmatch
      (hv.base_collisions.2.1 t ht4) (hsub.trans hinf))

theorem r_le_Rmax_of_base {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {r : Nat} (hinf : expandSymARep r <:+: ts) : r ≤ cert.R_max := by
  by_contra hgt
  have hsub : expandSymARep (cert.R_max + 1) <:+: expandSymARep r := by
    refine ⟨[], expandSymARep (r - (cert.R_max + 1)), ?_⟩
    rw [List.nil_append, ← expandSymARep_add]; congr 1; omega
  exact not_infix_of_checkWitness (by omega) (by omega) hchain hmatch hv.base_collisions.2.2 (hsub.trans hinf)

theorem r_eq_zero_after_d0 {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L) {ts : List (Nat × Nat)}
    (hmatch : MatchesWord 13 ts L) {t r : Nat} (ht4 : t < 4)
    (hinf : ([(0, t)] ++ expandSymARep r) <:+: ts) : r = 0 := by
  cases r with
  | zero => rfl
  | succ r' =>
    have hsub : [(0, t), (0, 4)] <:+: ([(0, t)] ++ expandSymARep (r' + 1)) := by
      have h1 : expandSymARep (r' + 1) = (0, 4) :: (List.replicate 8 (0, 4) ++ [(2, 4)] ++ expandSymARep r') := by
        simp [expandSymARep, List.replicate_succ, symA13, expandSym, List.append_assoc]
      rw [h1]
      exact ⟨[], List.replicate 8 (0, 4) ++ [(2, 4)] ++ expandSymARep r', by simp⟩
    exact False.elim (not_infix_of_checkWitness (by omega) (by omega) hchain hmatch
      (hv.base_collisions.2.1 t ht4) (hsub.trans hinf))

/-- Extract `resetCheckL2`, `endBoundCheckL2`, and `edgesFromSrcF` for any `L2State` satisfying `StateInv`! -/
theorem state_checks_ok {cert : L2Cert} (hv : L2CertValid cert) {st : L2State}
    {done : List (Nat × (Nat × Nat × Nat))} (hinv : StateInv cert st done) {f : Nat} (hf3 : f < 3)
    {sc : Int} (hsc : oLe (some sc) (psiInt cert.bias (statePsi cert st f)) = true) :
    ∃ pu : Nat,
      (sc ≤ (pu : Int) - (cert.bias : Int)) ∧
      resetCheckL2 cert (some pu) f (stateD0 cert st) (stateCanA cert st) = true ∧
      endBoundCheckL2 cert (some pu) f (stateD0 cert st) (stateCanA cert st) = true ∧
      match st with
      | .trie u =>
        f = 2 ∧ pu = cert.maxTrPsi (getStSym cert u) ∧
        edgesFromSrcF cert (some pu) 2 (stateLastS1 cert st) (some (getStSym cert u)) true = true
      | .root =>
        edgesFromSrcF cert (some pu) f none none false = true
      | .pair pi =>
        edgesFromSrcF cert (some pu) f (stateLastS1 cert st) (some (cert.nLong + pi)) false = true
      | .rootS1 _ =>
        edgesFromSrcF cert (some pu) f (stateLastS1 cert st) none false = true := by
  cases st with
  | root =>
    cases hp : cert.rootPsi f with
    | none => simp [statePsi, hp, psiInt, oLe] at hsc
    | some pu =>
      have hsc_le : sc ≤ (pu : Int) - (cert.bias : Int) := by
        simpa [statePsi, hp, psiInt, oLe] using hsc
      have hr := checkRangeAux_spec hv.hroot f (Nat.zero_le _) (by omega)
      simp only [Nat.zero_add, hp, Bool.and_eq_true] at hr
      exact ⟨pu, hsc_le, hr.1.1, hr.1.2, hr.2⟩
  | pair pi =>
    cases hp : cert.pairPsi pi f with
    | none => simp [statePsi, hp, psiInt, oLe] at hsc
    | some pu =>
      have hsc_le : sc ≤ (pu : Int) - (cert.bias : Int) := by
        simpa [statePsi, hp, psiInt, oLe] using hsc
      have hchk := checkRangeAux_spec (hv.hpair pi hinv.1) f (Nat.zero_le _) (by omega)
      simp only [Nat.zero_add, hp, Bool.and_eq_true] at hchk
      exact ⟨pu, hsc_le, hchk.1.1, hchk.1.2, hchk.2⟩
  | rootS1 s1 =>
    cases hp : cert.rootS1Psi s1 f with
    | none => simp [statePsi, hp, psiInt, oLe] at hsc
    | some pu =>
      have hsc_le : sc ≤ (pu : Int) - (cert.bias : Int) := by
        simpa [statePsi, hp, psiInt, oLe] using hsc
      have hchk := hv.hrootS1 s1 hinv.1; unfold checkRootS1 at hchk
      have hne : Nat.beq s1 cert.idA = false := by
        cases hc : Nat.beq s1 cert.idA with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hinv.2.1
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hchk
      have hf := checkRangeAux_spec hchk f (Nat.zero_le _) (by omega)
      simp only [Nat.zero_add, hp, Bool.and_eq_true] at hf
      exact ⟨pu, hsc_le, hf.1.1, hf.1.2, hf.2⟩
  | trie u =>
    have hf2 : f = 2 := by
      by_contra hne
      have hbf : (f == 2) = false := S.beq_false_of_ne hne
      simp [statePsi, hbf, psiInt, oLe] at hsc
    subst hf2
    have hsc_le : sc ≤ (getStPsi cert u : Int) - (cert.bias : Int) := by
      simpa [statePsi, psiInt, oLe] using hsc
    have hst := hv.trie_struct hinv.1 hinv.2.1
    have hli : getStSym cert u < cert.nLong := by rw [hv.nLong_eq]; exact hst.2.1
    have hcanA : stateCanA cert (.trie u) = true := by
      simp only [stateCanA, stateLastS1, (hv.d1Long_spec hli).2.2.2.2.2.2.2.2.2, Bool.not_false]
    have hmax := hv.hmaxTr (getStSym cert u) hli
    unfold checkMaxTr at hmax; simp only [Bool.and_eq_true] at hmax
    have hsc_max : sc ≤ (cert.maxTrPsi (getStSym cert u) : Int) - (cert.bias : Int) := by
      have : (getStPsi cert u : Int) ≤ (cert.maxTrPsi (getStSym cert u) : Int) := by exact_mod_cast hst.2.2.2
      linarith
    exact ⟨cert.maxTrPsi (getStSym cert u), hsc_max, by simpa [stateD0, hcanA] using hmax.1.1,
      by simpa [stateD0, hcanA] using hmax.1.2, rfl, rfl, hmax.2⟩

/-- Clean extraction of a single transition `(r, s1)` from `edgesFromSrcF`. -/
theorem edgesFromSrcF_at {cert : L2Cert} {pu f r s1 m d t nf : Nat}
    {lastS1 lastTr : Option Nat} {skipLong : Bool}
    (he : edgesFromSrcF cert (some pu) f lastS1 lastTr skipLong = true)
    (hr : r ≤ cert.R_max) (hs1 : s1 < cert.alpha1) (hneA : s1 ≠ cert.idA)
    (hl2v : cert.l2Valid r s1 = true)
    (hfb : (match (generalizing := false) lastS1 with | none => false | some lc => isForb1 cert lc (if Nat.beq r 0 then s1 else cert.idA)) = false)
    (hinfo : cert.sym1Info s1 = (m, d, t))
    (hnf : nextFL2 f r m d = some nf) :
    match (generalizing := false) cert.trId r s1 with
    | none => oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d)) (cert.rootS1Psi s1 nf) = true
    | some ti =>
      (match (generalizing := false) lastTr with | none => false | some lt => cert.forb2 lt ti) = false →
      if ti < cert.nLong then
        skipLong = false →
        oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
          (if Nat.beq nf 2 then some (cert.longD1Psi ti) else none) = true
      else
        oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d)) (cert.pairPsi (ti - cert.nLong) nf) = true := by
  have hr_c := checkRangeAux_spec he r (Nat.zero_le _) (by omega)
  have hs_c := checkRangeChunked_spec hr_c s1 (Nat.zero_le _) (by omega)
  dsimp only at hs_c
  have hneA_b : Nat.beq s1 cert.idA = false := by
    cases hc : Nat.beq s1 cert.idA with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hneA
  rw [hneA_b, hl2v] at hs_c
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hs_c
  cases lastS1 <;> (
    simp only [hfb, Bool.false_eq_true, ↓reduceIte, hinfo, hnf] at hs_c
    cases htid : cert.trId r s1 with
    | none => rw [htid] at hs_c; exact hs_c
    | some ti =>
      rw [htid] at hs_c
      intro hnotf2
      cases lastTr <;> (
        simp only [hnotf2, Bool.false_eq_true, ↓reduceIte] at hs_c
        by_cases hlt : ti < cert.nLong
        · have hbt : Nat.ble (ti + 1) cert.nLong = true := Nat.ble_eq_true_of_le (by omega)
          rw [hbt] at hs_c; simp only [hlt, ↓reduceIte] at hs_c ⊢
          intro hsk; rw [hsk] at hs_c; simpa using hs_c
        · have hbf : Nat.ble (ti + 1) cert.nLong = false := by
            cases hc : Nat.ble (ti + 1) cert.nLong with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
          rw [hbf] at hs_c; simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hs_c ⊢
          exact hs_c))

/-- Main inductive simulation of remaining L2 tokens `rem` starting from `(st, f)` with score `sc`. -/
theorem simulate_l2 {cert : L2Cert} (hv : L2CertValid cert)
    {L : List (List (List Nat))} (hchain : S.IsWChain 13 L)
    {ts : List (Nat × Nat)} (hmatch : MatchesWord 13 ts L) :
    ∀ (rem done : List (Nat × (Nat × Nat × Nat))) (tail_raw : List (Nat × Nat))
      (st : L2State) (f : Nat) (sc : Int),
      ts = expandL2List done ++ expandL2List rem ++ tail_raw →
      (∀ x ∈ rem, x.2 ≠ symA13 ∧ ¬ (x.2.2.1 = 0 ∧ x.2.2.2 = 4) ∧ x.2.2.2 < 5) →
      StateInv cert st done →
      f < 3 →
      oLe (some sc) (psiInt cert.bias (statePsi cert st f)) = true →
      ∀ f_end, walkF f ((expandL2List rem).map Prod.fst) = some f_end →
      ∃ st' : L2State,
        StateInv cert st' (done ++ rem) ∧
        f_end < 3 ∧
        oLe (some (sc + 2 * (cert.q : Int) * ((expandL2List rem).length : Int) -
            (cert.A : Int) * (((expandL2List rem).map Prod.fst).sum : Int)))
          (psiInt cert.bias (statePsi cert st' f_end)) = true
  | [], done, _, st, f, sc, _, _, hinv, hf3, hsc, f_end, hwalk => by
    simp only [expandL2List, List.flatMap_nil, List.map_nil, walkF, Option.some.injEq] at hwalk
    subst hwalk
    exact ⟨st, by simpa using hinv, hf3, by simpa [expandL2List] using hsc⟩
  | (r, (m, d, t)) :: rest, done, tail_raw, st, f, sc, hts, hrem_p, hinv, hf3, hsc, f_end, hwalk => by
    have hcur_p := hrem_p (r, (m, d, t)) List.mem_cons_self
    have hrest_p : ∀ x ∈ rest, x.2 ≠ symA13 ∧ ¬ (x.2.2.1 = 0 ∧ x.2.2.2 = 4) ∧ x.2.2.2 < 5 :=
      fun x hx => hrem_p x (List.mem_cons_of_mem _ hx)
    have hexp_eq : expandL2List ((r, (m, d, t)) :: rest) = expandL2Sym r m d t ++ expandL2List rest := by
      simp [expandL2List]
    rw [hexp_eq, List.map_append, walkF_append, walkF_expandL2Sym] at hwalk
    cases hnf : nextFL2 f r m d with
    | none => rw [hnf] at hwalk; cases hwalk
    | some nf =>
      rw [hnf] at hwalk
      have hnf3 : nf < 3 := by
        unfold nextFL2 nextF at hnf
        split_ifs at hnf <;> cases hnf <;> (try split_ifs) <;> omega
      -- Establish r ≤ R_max, m ≤ 10, and constraints on r, m when f=1 / d0 / !canA!
      have hr_le : r ≤ cert.R_max := r_le_Rmax_of_base hv hchain hmatch
        ⟨expandL2List done, expandSym m d t ++ expandL2List rest ++ tail_raw, by
          rw [hts, hexp_eq]; simp [expandL2Sym, List.append_assoc]⟩
      have hm_le : m ≤ 10 := m_le_10_of_base hv hchain hmatch
        ⟨expandL2List done ++ expandSymARep r, [(d, t)] ++ expandL2List rest ++ tail_raw, by
          rw [hts, hexp_eq]; simp [expandL2Sym, expandSym, List.append_assoc]⟩
      have hr_zero_f1 : f = 1 → r = 0 := by
        intro hf1; by_contra hr0
        have hr' : (r == 0) = false := S.beq_false_of_ne hr0
        unfold nextFL2 at hnf; simp [hr', hf1] at hnf
      have hm_zero_f1 : f = 1 → m = 0 := by
        intro hf1; have hr0 := hr_zero_f1 hf1; subst hr0
        unfold nextFL2 nextF at hnf
        by_contra hm0; have hm1 : m ≥ 1 := by omega
        simp only [hf1, hm1, beq_self_eq_true, decide_true, Bool.true_or, Bool.and_true, ↓reduceIte] at hnf
        cases hnf
      have hr_zero_d0 : stateD0 cert st = true → r = 0 := by
        intro hd0
        obtain ⟨tprev, ht4, ⟨pre0, hpre0⟩⟩ := stateD0_ends_zero hv hinv hd0
        exact r_eq_zero_after_d0 hv hchain hmatch ht4
          ⟨pre0, expandSym m d t ++ expandL2List rest ++ tail_raw, by
            rw [hts, hexp_eq, ← hpre0]; simp [expandL2Sym, List.append_assoc]⟩
      have hm_zero_d0 : stateD0 cert st = true → m = 0 := by
        intro hd0; have hr0 := hr_zero_d0 hd0; subst hr0
        obtain ⟨tprev, ht4, ⟨pre0, hpre0⟩⟩ := stateD0_ends_zero hv hinv hd0
        exact m_eq_zero_after_d0 hv hchain hmatch ht4
          ⟨pre0, [(d, t)] ++ expandL2List rest ++ tail_raw, by
            rw [hts, hexp_eq, ← hpre0]; simp [expandL2Sym, expandSymARep, expandSym, List.append_assoc]⟩
      have hr_zero_notA : stateCanA cert st = false → r = 0 := by
        intro hnoA
        cases hls : stateLastS1 cert st with
        | none => simp [stateCanA, hls] at hnoA
        | some lc =>
          have hforb : isForb1 cert lc cert.idA = true := by
            simp only [stateCanA, hls, Bool.not_eq_false'] at hnoA; exact hnoA
          cases r with
          | zero => rfl
          | succ r' =>
            obtain ⟨hlc_lt, ⟨pre0, hpre0⟩⟩ := stateLastS1_suffix hv hinv hls
            have hidA := hv.idA_spec
            have hinf : (expandSym (cert.sym1Info lc).1 (cert.sym1Info lc).2.1 (cert.sym1Info lc).2.2 ++
                expandSym (cert.sym1Info cert.idA).1 (cert.sym1Info cert.idA).2.1 (cert.sym1Info cert.idA).2.2) <:+: ts := by
              rw [hidA.2.1]
              have h1 : expandSymARep (r' + 1) = expandSym 9 2 4 ++ expandSymARep r' := by
                simp [expandSymARep, List.replicate_succ, symA13]
              refine ⟨pre0, expandSymARep r' ++ expandSym m d t ++ expandL2List rest ++ tail_raw, ?_⟩
              rw [hts, hexp_eq, ← hpre0]; simp [expandL2Sym, h1, symA13, List.append_assoc]
            exact False.elim (not_infix_of_isForb1 hv hchain hmatch hlc_lt hidA.1 hforb hinf)
      -- Length, sum, and integer weight of this L2 token
      have hlen_l2 : (expandL2Sym r m d t).length = 10 * r + m + 1 := expandL2Sym_len r m d t
      have hsum_l2 : ((expandL2Sym r m d t).map Prod.fst).sum = 2 * r + d := by
        have hsumA : ∀ k, ((expandSymARep k).map Prod.fst).sum = 2 * k := by
          intro k; induction k with
          | zero => simp [expandSymARep]
          | succ k ih =>
            have h1 : expandSymARep (k + 1) = expandSym 9 2 4 ++ expandSymARep k := by
              simp [expandSymARep, List.replicate_succ, symA13]
            rw [h1, List.map_append, List.sum_append, ih]
            simp [expandSym, List.map_replicate]; omega
        unfold expandL2Sym
        rw [List.map_append, List.sum_append, hsumA]
        simp [expandSym, List.map_replicate]
      let w_tok : Int := 2 * (cert.q : Int) * ((10 * r + m + 1 : Nat) : Int) -
          (cert.A : Int) * ((2 * r + d : Nat) : Int)
      obtain ⟨pu, hsc_le, hrst_chk, _, hsrc_edges⟩ := state_checks_ok hv hinv hf3 hsc
      -- Advance state to next L2State `v`!
      have hstep : ∃ v : L2State, StateInv cert v (done ++ [(r, (m, d, t))]) ∧
          oLe (some (sc + w_tok)) (psiInt cert.bias (statePsi cert v nf)) = true := by
        by_cases hd_hi : cert.D_track < d
        · -- Case 1: RESET transition to (.root, 2)!
          have hd_ge : cert.D_track + 1 ≤ d := by omega
          have hd2 : 2 ≤ d := by have := hv.hD1; omega
          have hnf2 : nf = 2 := by
            unfold nextFL2 nextF at hnf
            have h0 : (d == 0) = false := S.beq_false_of_ne (by omega)
            have h1 : (d == 1) = false := S.beq_false_of_ne (by omega)
            split_ifs at hnf <;> simp_all
          subst hnf2
          refine ⟨.root, trivial, ?_⟩
          unfold resetCheckL2 at hrst_chk
          have hq_nn : (0 : Int) ≤ 2 * (cert.q : Int) := by omega
          have hA_nn : (0 : Int) ≤ (cert.A : Int) := Int.natCast_nonneg _
          by_cases hf1d0 : f = 1 ∨ stateD0 cert st = true
          · have hb : (Nat.beq f 1 || stateD0 cert st) = true := by
              rcases hf1d0 with rfl | hd0 <;> simp [*]
            simp only [hb, ↓reduceIte] at hrst_chk
            have hr0 : r = 0 := by rcases hf1d0 with h | h; exact hr_zero_f1 h; exact hr_zero_d0 h
            have hm0 : m = 0 := by rcases hf1d0 with h | h; exact hm_zero_f1 h; exact hm_zero_d0 h
            have hle := oLe_add_of_oStepLeN (bias := cert.bias) hrst_chk
            obtain ⟨z, hz, hpu_z⟩ := oLe_some_of_le hle
            rw [statePsi, hz]; simp only [oLe, decide_eq_true_eq]
            have hd_int : (cert.A : Int) * ((cert.D_track + 1 : Nat) : Int) ≤ (cert.A : Int) * (d : Int) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge) hA_nn
            simp only [w_tok, hr0, hm0, Nat.mul_zero, Nat.zero_add, Nat.cast_one, Nat.cast_mul,
              Nat.cast_add, Nat.cast_ofNat] at hpu_z hd_int ⊢
            linarith
          · push Not at hf1d0
            have hbf : (Nat.beq f 1 || stateD0 cert st) = false := by
              have h1 : Nat.beq f 1 = false := by cases hc : Nat.beq f 1 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hf1d0.1
              have h2 : stateD0 cert st = false := Bool.eq_false_iff.mpr hf1d0.2
              simp [h1, h2]
            simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hrst_chk
            by_cases hcanA : stateCanA cert st = true
            · simp only [hcanA, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hrst_chk
              have hle0 := oLe_add_of_oStepLeN (bias := cert.bias) hrst_chk.1
              have hleR := oLe_add_of_oStepLeN (bias := cert.bias) hrst_chk.2
              obtain ⟨z, hz, hz0⟩ := oLe_some_of_le hle0
              rw [hz] at hleR
              obtain ⟨_, hz_eq, hzR⟩ := oLe_some_of_le hleR
              cases hz_eq
              rw [statePsi, hz]; simp only [oLe, decide_eq_true_eq]
              have hA_d : (cert.A : Int) * ((cert.D_track + 1 : Nat) : Int) ≤ (cert.A : Int) * (d : Int) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge) hA_nn
              have hm_int : 2 * (cert.q : Int) * ((m + 1 : Nat) : Int) ≤ 2 * (cert.q : Int) * 11 :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : m + 1 ≤ 11)) hq_nn
              -- Linear interpolation in r ∈ [0, R_max] between hz0 and hzR!
              let wA : Int := 2 * (cert.q : Int) * 10 - (cert.A : Int) * 2
              have hr_bound : (r : Int) * wA ≤ max 0 ((cert.R_max : Int) * wA) := by
                by_cases hwA : 0 ≤ wA
                · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr_le) hwA) (le_max_right _ _)
                · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg r) (by omega)) (le_max_left _ _)
              simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hz0 hzR hm_int hA_d
              simp only [w_tok, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
              rcases le_max_iff.mp hr_bound with h0 | hR
              · dsimp only [wA] at h0; linarith
              · dsimp only [wA] at hR; linarith
            · have hcanAf : stateCanA cert st = false := Bool.eq_false_iff.mpr hcanA
              have hr0 : r = 0 := hr_zero_notA hcanAf
              simp only [hcanAf, Bool.not_false, ↓reduceIte] at hrst_chk
              have hle := oLe_add_of_oStepLeN (bias := cert.bias) hrst_chk
              obtain ⟨z, hz, hz0⟩ := oLe_some_of_le hle
              rw [statePsi, hz]; simp only [oLe, decide_eq_true_eq]
              have hA_d : (cert.A : Int) * ((cert.D_track + 1 : Nat) : Int) ≤ (cert.A : Int) * (d : Int) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge) hA_nn
              have hm_int : 2 * (cert.q : Int) * ((m + 1 : Nat) : Int) ≤ 2 * (cert.q : Int) * 11 :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : m + 1 ≤ 11)) hq_nn
              simp only [w_tok, hr0, Nat.mul_zero, Nat.zero_add, Nat.cast_add, Nat.cast_mul,
                Nat.cast_one, Nat.cast_ofNat] at hz0 hm_int hA_d ⊢
              linarith
        · -- Case 2: d ≤ D_track! Look up L1 symbol s1 = sym1Id m d t!
          have hd_le : d ≤ cert.D_track := by omega
          have ha_chk := hv.halpha1 m hm_le d hd_le t hcur_p.2.2
          unfold alpha1TripleCheck at ha_chk
          have hne04 : (d == 0 && t == 4) = false := by
            have := hcur_p.2.1; cases h0 : (d == 0) <;> cases h4 : (t == 4) <;> simp_all
          simp only [hne04, Bool.false_eq_true, ↓reduceIte] at ha_chk
          cases hsid : cert.sym1Id m d t with
          | none =>
            rw [hsid] at ha_chk
            exact False.elim (not_infix_of_checkWitness (by omega) (by omega) hchain hmatch ha_chk
              ⟨expandL2List done ++ expandSymARep r, expandL2List rest ++ tail_raw, by
                rw [hts, hexp_eq]; simp [expandL2Sym, List.append_assoc]⟩)
          | some s1 =>
            rw [hsid] at ha_chk
            simp only [Bool.and_eq_true, beq_iff_eq] at ha_chk
            have hs1_lt : s1 < cert.alpha1 := by have := Nat.le_of_ble_eq_true ha_chk.1; omega
            have hs1_info : cert.sym1Info s1 = (m, d, t) := ha_chk.2
            have hs1_neA : s1 ≠ cert.idA := by
              intro heq; subst heq; exact hcur_p.1 (hs1_info.symm.trans hv.idA_spec.2.1)
            -- Check l2Valid r s1!
            have hl2 := hv.hl2Single r hr_le s1 hs1_lt
            unfold l2SingleCheck at hl2
            have hneA_b : Nat.beq s1 cert.idA = false := by
              cases hc : Nat.beq s1 cert.idA with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hs1_neA
            simp only [hneA_b, Bool.false_eq_true, ↓reduceIte, hs1_info] at hl2
            cases hl2v : cert.l2Valid r s1 with
            | false =>
              rw [hl2v] at hl2; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hl2
              exact False.elim (not_infix_of_checkWitness (by omega) (by omega) hchain hmatch hl2.2
                ⟨expandL2List done, expandL2List rest ++ tail_raw, by
                  rw [hts, hexp_eq]; simp [List.append_assoc]⟩)
            | true =>
              rw [hl2v] at hl2; simp only [↓reduceIte] at hl2
              -- Check forb1(last_s1, first_s1)!
              let fstS1 := if Nat.beq r 0 then s1 else cert.idA
              have hnot_forb1 : (match stateLastS1 cert st with | none => false | some lc => isForb1 cert lc fstS1) = false := by
                cases hls : stateLastS1 cert st with
                | none => rfl
                | some lc =>
                  by_contra hf1
                  have hf1t : isForb1 cert lc fstS1 = true := Bool.eq_true_of_not_eq_false hf1
                  obtain ⟨hlc_lt, ⟨pre0, hpre0⟩⟩ := stateLastS1_suffix hv hinv hls
                  by_cases hr0 : r = 0
                  · have hfst : fstS1 = s1 := by simp [fstS1, hr0]
                    rw [hfst] at hf1t
                    exact not_infix_of_isForb1 hv hchain hmatch hlc_lt hs1_lt hf1t
                      ⟨pre0, expandL2List rest ++ tail_raw, by
                        rw [hts, hexp_eq, ← hpre0, hs1_info]; simp [expandL2Sym, hr0, expandSymARep, List.append_assoc]⟩
                  · have hne0 : Nat.beq r 0 = false := by cases hc : Nat.beq r 0 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hr0
                    have hfst : fstS1 = cert.idA := by simp [fstS1, hne0]
                    rw [hfst] at hf1t
                    cases r with
                    | zero => contradiction
                    | succ r' =>
                      have h1 : expandSymARep (r' + 1) = expandSym 9 2 4 ++ expandSymARep r' := by
                        simp [expandSymARep, List.replicate_succ, symA13]
                      exact not_infix_of_isForb1 hv hchain hmatch hlc_lt hv.idA_spec.1 hf1t
                        ⟨pre0, expandSymARep r' ++ expandSym m d t ++ expandL2List rest ++ tail_raw, by
                          rw [hts, hexp_eq, ← hpre0, hv.idA_spec.2.1]; simp [expandL2Sym, h1, symA13, List.append_assoc]⟩
              -- Helper to extract the checked step from edgesFromSrcF
              have hdone_exp : expandL2List (done ++ [(r, (m, d, t))]) = expandL2List done ++ expandL2Sym r m d t := by
                simp [expandL2List]
              have hdone_s1_suf : expandSym m d t <:+ expandL2List (done ++ [(r, (m, d, t))]) := by
                rw [hdone_exp]; exact (List.suffix_append _ _).trans (List.suffix_append _ _)
              -- Now dispatch on `trId r s1`!
              cases htrid : cert.trId r s1 with
              | none =>
                -- Inactive L2 symbol -> transitions to (.rootS1 s1, nf)!
                have hedge_ok : oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
                    (cert.rootS1Psi s1 nf) = true := by
                  have run_src : ∀ (lastTr : Option Nat) (skipLong : Bool),
                      edgesFromSrcF cert (some pu) f (stateLastS1 cert st) lastTr skipLong = true →
                      oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d)) (cert.rootS1Psi s1 nf) = true := by
                    intro lastTr skipLong he
                    have h := edgesFromSrcF_at he hr_le hs1_lt hs1_neA hl2v hnot_forb1 hs1_info hnf
                    rw [htrid] at h; exact h
                  cases st with
                  | root => exact run_src none false hsrc_edges
                  | pair pi => exact run_src (some (cert.nLong + pi)) false hsrc_edges
                  | rootS1 _ => exact run_src none false hsrc_edges
                  | trie u =>
                    obtain ⟨rfl, _, he⟩ := hsrc_edges
                    exact run_src (some (getStSym cert u)) true he
                refine ⟨.rootS1 s1, ⟨hs1_lt, hs1_neA, by rw [hs1_info]; exact hdone_s1_suf⟩, ?_⟩
                have hle := oLe_add_of_oStepLeN (bias := cert.bias) hedge_ok
                have hw_cast : (((2 * cert.q * (10 * r + m + 1) : Nat) : Int) - ((cert.A * (2 * r + d) : Nat) : Int)) = w_tok := by
                  unfold w_tok; simp only [Nat.cast_mul, Nat.cast_ofNat]
                rw [hw_cast] at hle
                exact oLe_add_of_le hsc_le hle
              | some ti =>
                rw [htrid] at hl2
                simp only [Bool.and_eq_true, beq_iff_eq] at hl2
                have hti_lt : ti < cert.nLong + cert.nPair := by have := Nat.le_of_ble_eq_true hl2.1; omega
                have hti_info : cert.trInfo ti = (r, s1) := hl2.2
                have hexp_ti : expandTrSym cert ti = expandL2Sym r m d t := by
                  simp [expandTrSym, hti_info, hs1_info]
                -- Check if ti < nLong (long symbol) or nLong ≤ ti (pair symbol)
                by_cases hti_long : ti < cert.nLong
                · -- Long L2 symbol `ti < 10`!
                  have hti10 : ti < 10 := by rw [← hv.nLong_eq]; exact hti_long
                  have hd1 := hv.d1Long_spec hti_long
                  have htr_sp := hv.trInfo_spec hti_lt
                  rw [hti_info, hs1_info] at htr_sp; dsimp only at htr_sp
                  have hnf2 : nf = 2 := by
                    have hd2 : d = 2 := htr_sp.2.2.2.2.2.2
                    subst hd2
                    unfold nextFL2 nextF at hnf
                    by_cases hr0 : r = 0
                    · subst hr0
                      simp only [beq_self_eq_true, ↓reduceIte] at hnf
                      by_cases hbad : (f == 1 && (decide (m ≥ 1) || (2 == 0))) = true
                      · simp only [hbad, ↓reduceIte] at hnf; cases hnf
                      · simp only [Bool.not_eq_true] at hbad
                        simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hnf
                        cases hnf; rfl
                    · have hr' : (r == 0) = false := S.beq_false_of_ne hr0
                      simp only [hr', Bool.false_eq_true, ↓reduceIte] at hnf
                      by_cases hf1 : f = 1
                      · subst hf1; simp at hnf
                      · have hf' : (f == 1) = false := S.beq_false_of_ne hf1
                        simp only [hf', Bool.false_eq_true, ↓reduceIte] at hnf
                        cases hnf; rfl
                  subst hnf2
                  have finish_d1 : oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
                      (some (cert.longD1Psi ti)) = true →
                      ∃ v : L2State, StateInv cert v (done ++ [(r, (m, d, t))]) ∧
                        oLe (some (sc + w_tok)) (psiInt cert.bias (statePsi cert v 2)) = true := by
                    intro hstep_ok
                    have hpref_d1 : statePref cert (cert.d1Long ti) = [ti] := by
                      rw [statePref_pos hv hd1.1 hd1.2.1, hd1.2.2.1, hd1.2.2.2.1]; rfl
                    refine ⟨.trie (cert.d1Long ti), ⟨hd1.1, hd1.2.1, ?_⟩, ?_⟩
                    · rw [hpref_d1, hdone_exp]; simp only [expandTrWord, List.flatMap_singleton, hexp_ti]; exact List.suffix_append _ _
                    · have hle := oLe_add_of_oStepLeN (bias := cert.bias) hstep_ok
                      have hw_cast : (((2 * cert.q * (10 * r + m + 1) : Nat) : Int) - ((cert.A * (2 * r + d) : Nat) : Int)) = w_tok := by
                        unfold w_tok; simp only [Nat.cast_mul, Nat.cast_ofNat]
                      rw [hw_cast, hd1.2.2.2.2.2.2.2.2.1] at hle
                      simpa [statePsi] using oLe_add_of_le hsc_le hle
                  have run_long : ∀ (lastS1' lastTr : Option Nat),
                      (match (generalizing := false) lastS1' with | none => false | some lc => isForb1 cert lc (if Nat.beq r 0 then s1 else cert.idA)) = false →
                      (match (generalizing := false) lastTr with | none => false | some lt => cert.forb2 lt ti) = false →
                      edgesFromSrcF cert (some pu) f lastS1' lastTr false = true →
                      oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
                        (some (cert.longD1Psi ti)) = true := by
                    intro lastS1' lastTr hfb hnotf2 he
                    have h := edgesFromSrcF_at he hr_le hs1_lt hs1_neA hl2v hfb hs1_info hnf
                    rw [htrid] at h
                    have h2 := h hnotf2
                    simp only [hti_long, ↓reduceIte] at h2
                    simpa using h2 trivial
                  cases st with
                  | trie u =>
                    -- Trie-to-trie transition via O(1) `trieStateCheck`!
                    obtain ⟨rfl, _, _⟩ := hsrc_edges
                    have hsc_u : sc ≤ (getStPsi cert u : Int) - (cert.bias : Int) := by
                      simpa [statePsi, psiInt, oLe] using hsc
                    have hedge := (hv.trie_fail_and_edges hinv.1 hinv.2.1).2 ti hti10
                    have hac := (ac_sound hv u hinv.2.1).2 ti hti10
                    set v := getGo cert u ti
                    set fv := getGo cert (getStFail cert u) ti
                    have hua_suf : expandTrWord cert (statePref cert u ++ [ti]) <:+ expandL2List (done ++ [(r, (m, d, t))]) := by
                      rw [expandTrWord_append, hdone_exp]
                      have h1 : expandTrWord cert [ti] = expandL2Sym r m d t := by simp only [expandTrWord, List.flatMap_singleton, hexp_ti]
                      rw [h1]; exact suffix_trans_append (List.suffix_refl _) hinv.2.2
                    by_cases hdead : v = 0 ∨ deadLeafBase ≤ v
                    · obtain ⟨fid, hfid, hcsuf⟩ := hac.2 hdead
                      have hinf_c : expandTrWord cert (cegarWord cert fid) <:+: ts := by
                        obtain ⟨pre1, hpre1⟩ := (expandTrWord_suffix cert hcsuf).trans hua_suf
                        refine ⟨pre1, expandL2List rest ++ tail_raw, ?_⟩
                        rw [hts, hexp_eq, ← List.append_assoc, ← List.append_assoc, ← hdone_exp, ← hpre1]
                      exact False.elim (not_infix_of_cegar hv hchain hmatch hfid hinf_c)
                    · push Not at hdead
                      have hv1 : 1 ≤ v := by omega
                      have hne0 : Nat.beq v 0 = false := by cases hc : Nat.beq v 0 with | false => rfl | true => have := Nat.eq_of_beq_eq_true hc; omega
                      have hnd : Nat.ble deadLeafBase v = false := by cases hc : Nat.ble deadLeafBase v with | false => rfl | true => have := Nat.le_of_ble_eq_true hc; omega
                      unfold trieEdgeCheckOne at hedge
                      simp only [hne0, hnd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hedge
                      have hv_lt : v < cert.nAlive := by have := Nat.le_of_ble_eq_true hedge.1; omega
                      have hpsi_or : getStPsi cert u + cert.longPos ti ≤ cert.longD1Psi ti + cert.longNeg ti ∨
                          getStPsi cert u + cert.longPos ti ≤ getStPsi cert v + cert.longNeg ti := by
                        by_cases hvf : v = fv
                        · have h2 := hedge.2; simp only [hvf, Nat.beq_refl, ↓reduceIte, Bool.or_eq_true] at h2
                          rcases h2 with h1' | h2'
                          · exact Or.inl (Nat.le_of_ble_eq_true h1')
                          · exact Or.inr (Nat.le_of_ble_eq_true (by simpa [hvf] using h2'))
                        · have hnef : Nat.beq v fv = false := by cases hc : Nat.beq v fv with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hvf
                          have h2 := hedge.2; simp only [hnef, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true] at h2
                          rcases h2.2 with h1' | h2'
                          · exact Or.inl (Nat.le_of_ble_eq_true h1')
                          · exact Or.inr (Nat.le_of_ble_eq_true h2')
                      have hpos_eq : cert.longPos ti = 2 * cert.q * (10 * r + m + 1) := by
                        simpa [hti_info, hs1_info] using hd1.2.2.2.2.2.2.1
                      have hneg_eq : cert.longNeg ti = cert.A * (2 * r + d) := by
                        simpa [hti_info, hs1_info] using hd1.2.2.2.2.2.2.2.1
                      rcases hpsi_or with hd1_le | hv_le
                      · -- d1-shortcut! Transition to `.trie (d1Long ti)`!
                        have hpref_d1 : statePref cert (cert.d1Long ti) = [ti] := by
                          rw [statePref_pos hv hd1.1 hd1.2.1, hd1.2.2.1, hd1.2.2.2.1]; rfl
                        refine ⟨.trie (cert.d1Long ti), ⟨hd1.1, hd1.2.1, ?_⟩, ?_⟩
                        · rw [hpref_d1, hdone_exp]; simp [expandTrWord, hexp_ti]
                        · rw [hd1.2.2.2.2.2.2.2.2.1, hpos_eq, hneg_eq] at hd1_le
                          simp only [statePsi, beq_self_eq_true, ↓reduceIte, psiInt, oLe, decide_eq_true_eq]
                          have hcast : ((getStPsi cert u + 2 * cert.q * (10 * r + m + 1) : Nat) : Int) ≤
                              ((getStPsi cert (cert.d1Long ti) + cert.A * (2 * r + d) : Nat) : Int) := by exact_mod_cast hd1_le
                          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
                          simp only [w_tok, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
                          linarith
                      · -- Normal transition to `.trie v`!
                        refine ⟨.trie v, ⟨hv1, hv_lt, (expandTrWord_suffix cert (hac.1 hv1 hv_lt)).trans hua_suf⟩, ?_⟩
                        rw [hpos_eq, hneg_eq] at hv_le
                        simp only [statePsi, beq_self_eq_true, ↓reduceIte, psiInt, oLe, decide_eq_true_eq]
                        have hcast : ((getStPsi cert u + 2 * cert.q * (10 * r + m + 1) : Nat) : Int) ≤
                            ((getStPsi cert v + cert.A * (2 * r + d) : Nat) : Int) := by exact_mod_cast hv_le
                        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
                        simp only [w_tok, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
                        linarith
                  | root => exact finish_d1 (run_long none none rfl rfl hsrc_edges)
                  | rootS1 s1_0 => exact finish_d1 (run_long (some s1_0) none hnot_forb1 rfl hsrc_edges)
                  | pair pi =>
                    by_cases hf2 : cert.forb2 (cert.nLong + pi) ti = true
                    · obtain ⟨hfid, hcw⟩ := hv.forb2_spec (by have := hinv.1; omega) hti_lt hf2
                      obtain ⟨pre0, hpre0⟩ := hinv.2
                      have hinf2 : expandTrWord cert (cegarWord cert (cert.forb2Fid (cert.nLong + pi) ti)) <:+: ts := by
                        rw [hcw]
                        refine ⟨pre0, expandL2List rest ++ tail_raw, ?_⟩
                        rw [hts, hexp_eq, ← hpre0]; simp [expandTrWord, hexp_ti, List.append_assoc]
                      exact False.elim (not_infix_of_cegar hv hchain hmatch hfid hinf2)
                    · exact finish_d1 (run_long (stateLastS1 cert (.pair pi)) (some (cert.nLong + pi))
                        hnot_forb1 (Bool.eq_false_iff.mpr hf2) hsrc_edges)
                · -- Pair L2 symbol `nLong ≤ ti < nLong + nPair`!
                  let pi := ti - cert.nLong
                  have hpi_lt : pi < cert.nPair := by omega
                  have hti_eq : cert.nLong + pi = ti := by omega
                  have run_pair : ∀ (lastTr : Option Nat) (skipLong : Bool),
                      (match (generalizing := false) lastTr with | none => false | some lt => cert.forb2 lt ti) = false →
                      edgesFromSrcF cert (some pu) f (stateLastS1 cert st) lastTr skipLong = true →
                      oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
                        (cert.pairPsi pi nf) = true := by
                    intro lastTr skipLong hnotf2 he
                    have h := edgesFromSrcF_at he hr_le hs1_lt hs1_neA hl2v hnot_forb1 hs1_info hnf
                    rw [htrid] at h
                    have h2 := h hnotf2
                    simp only [hti_long, ↓reduceIte] at h2
                    exact h2
                  have hstep_ok : oStepLeN (some pu) (2 * cert.q * (10 * r + m + 1)) (cert.A * (2 * r + d))
                      (cert.pairPsi pi nf) = true := by
                    cases st with
                    | root => exact run_pair none false rfl hsrc_edges
                    | rootS1 _ => exact run_pair none false rfl hsrc_edges
                    | pair pi0 =>
                      by_cases hf2 : cert.forb2 (cert.nLong + pi0) ti = true
                      · obtain ⟨hfid, hcw⟩ := hv.forb2_spec (by have := hinv.1; omega) hti_lt hf2
                        obtain ⟨pre0, hpre0⟩ := hinv.2
                        have hinf2 : expandTrWord cert (cegarWord cert (cert.forb2Fid (cert.nLong + pi0) ti)) <:+: ts := by
                          rw [hcw]
                          refine ⟨pre0, expandL2List rest ++ tail_raw, ?_⟩
                          rw [hts, hexp_eq, ← hpre0]; simp [expandTrWord, hexp_ti, List.append_assoc]
                        exact False.elim (not_infix_of_cegar hv hchain hmatch hfid hinf2)
                      · exact run_pair (some (cert.nLong + pi0)) false (Bool.eq_false_iff.mpr hf2) hsrc_edges
                    | trie u =>
                      obtain ⟨rfl, _, he⟩ := hsrc_edges
                      have hsym_lt : getStSym cert u < cert.nLong := by
                        rw [hv.nLong_eq]; exact (hv.trie_struct hinv.1 hinv.2.1).2.1
                      by_cases hf2 : cert.forb2 (getStSym cert u) ti = true
                      · obtain ⟨hfid, hcw⟩ := hv.forb2_spec (by omega) hti_lt hf2
                        have hpref := statePref_pos hv hinv.1 hinv.2.1
                        have hs1 : expandTrSym cert (getStSym cert u) <:+ expandL2List done := by
                          have : [getStSym cert u] <:+ statePref cert u := ⟨statePref cert (getStPar cert u), hpref.symm⟩
                          have h1 : expandTrSym cert (getStSym cert u) <:+ expandTrWord cert (statePref cert u) := by
                            simpa [expandTrWord] using expandTrWord_suffix cert this
                          exact h1.trans hinv.2.2
                        obtain ⟨pre0, hpre0⟩ := hs1
                        have hinf2 : expandTrWord cert (cegarWord cert (cert.forb2Fid (getStSym cert u) ti)) <:+: ts := by
                          rw [hcw]
                          refine ⟨pre0, expandL2List rest ++ tail_raw, ?_⟩
                          rw [hts, hexp_eq, ← hpre0]; simp [expandTrWord, hexp_ti, List.append_assoc]
                        exact False.elim (not_infix_of_cegar hv hchain hmatch hfid hinf2)
                      · exact run_pair (some (getStSym cert u)) true (Bool.eq_false_iff.mpr hf2) he
                  refine ⟨.pair pi, ⟨hpi_lt, ?_⟩, ?_⟩
                  · rw [hti_eq, hdone_exp]; simp [expandTrWord, hexp_ti]
                  · have hle := oLe_add_of_oStepLeN (bias := cert.bias) hstep_ok
                    have hw_cast : (((2 * cert.q * (10 * r + m + 1) : Nat) : Int) - ((cert.A * (2 * r + d) : Nat) : Int)) = w_tok := by
                      unfold w_tok; simp only [Nat.cast_mul, Nat.cast_ofNat]
                    rw [hw_cast] at hle
                    exact oLe_add_of_le hsc_le hle
      -- Complete induction on `rest`!
      obtain ⟨v, hinv_v, hsc_v⟩ := hstep
      have hts' : ts = expandL2List (done ++ [(r, (m, d, t))]) ++ expandL2List rest ++ tail_raw := by
        rw [hts, hexp_eq]; simp [expandL2List, List.append_assoc]
      obtain ⟨st', hinv', hf_end3, hsc_end⟩ :=
        simulate_l2 hv hchain hmatch rest (done ++ [(r, (m, d, t))]) tail_raw v nf (sc + w_tok)
          hts' hrest_p hinv_v hnf3 hsc_v f_end hwalk
      refine ⟨st', by simpa [List.append_assoc] using hinv', hf_end3, ?_⟩
      have hlen_tot : (expandL2List ((r, (m, d, t)) :: rest)).length =
          (10 * r + m + 1) + (expandL2List rest).length := by
        rw [hexp_eq, List.length_append, hlen_l2]
      have hsum_tot : ((expandL2List ((r, (m, d, t)) :: rest)).map Prod.fst).sum =
          (2 * r + d) + ((expandL2List rest).map Prod.fst).sum := by
        rw [hexp_eq, List.map_append, List.sum_append, hsum_l2]
      have hsc_eq : sc + w_tok + 2 * (cert.q : Int) * ((expandL2List rest).length : Int) -
          (cert.A : Int) * (((expandL2List rest).map Prod.fst).sum : Int) =
          sc + 2 * (cert.q : Int) * ((expandL2List ((r, (m, d, t)) :: rest)).length : Int) -
          (cert.A : Int) * (((expandL2List ((r, (m, d, t)) :: rest)).map Prod.fst).sum : Int) := by
        rw [hlen_tot, hsum_tot]; unfold w_tok; push_cast; ring
      rw [← hsc_eq]
      exact hsc_end

theorem sum_expandSymARep : ∀ r : Nat, ((expandSymARep r).map Prod.fst).sum = 2 * r
  | 0 => by simp [expandSymARep]
  | k + 1 => by
    have h1 : expandSymARep (k + 1) = expandSym 9 2 4 ++ expandSymARep k := by
      simp [expandSymARep, List.replicate_succ, symA13]
    rw [h1, List.map_append, List.sum_append, sum_expandSymARep k]; simp [expandSym]; omega

/-! ### 7. Main `WStatement` and Theorem C Bridge -/

theorem wstatement_of_tropicL2 {cert : L2Cert} (hv : L2CertValid cert) :
    S.WStatement 13 cert.cn cert.bn cert.q := by
  intro L hchain hwin
  have hLne : L ≠ [] := by
    obtain ⟨x, rest, hne, _⟩ := hwin.first_partial
    intro h0; rw [h0] at hne; simp [S.wdef] at hne
  obtain ⟨ts, d_last, hwdef, ht5, hmatch⟩ := extract_transitions (k := 13) (by omega) (by omega) L hLne hchain
  have hd_last_pos : 0 < d_last := by
    obtain ⟨init, y, hy, hypos⟩ := hwin.last_partial
    rw [hwdef] at hy
    have heq : d_last = y := ChainC.last_eq_of_concat_eq hy
    omega
  have hwalk_all : walkF 1 (S.wdef 13 L) = some 2 := walkF_isWindow hwin
  -- Split ts into L1 tokens ms + trailing mt copies of (0, 4), then L2 tokens l2s + trailing rt copies of symA13!
  cases hsp1 : splitMacroAux 0 ts with
  | mk ms mt =>
    have hts1 : ts = expandMacroList ms ++ List.replicate mt (0, 4) := by
      have h := splitMacroAux_expand 0 ts; rw [hsp1] at h; simpa using h
    have hms_p : ∀ x ∈ ms, ¬ (x.2.1 = 0 ∧ x.2.2 = 4) ∧ x.2.2 < 5 := by
      have h := splitMacroAux_props 0 ts ht5; rw [hsp1] at h; exact h
    cases hsp2 : splitL2Aux 0 ms with
    | mk l2s rt =>
      have hms2 : expandMacroList ms = expandL2List l2s ++ expandSymARep rt := by
        have h := splitL2Aux_expand 0 ms; rw [hsp2] at h; simpa [expandSymARep] using h
      have hl2_p : ∀ x ∈ l2s, x.2 ≠ symA13 ∧ ¬ (x.2.2.1 = 0 ∧ x.2.2.2 = 4) ∧ x.2.2.2 < 5 := by
        have h := splitL2Aux_props 0 ms hms_p; rw [hsp2] at h; exact h
      have hts_eq : ts = expandL2List l2s ++ (expandSymARep rt ++ List.replicate mt (0, 4)) := by
        rw [hts1, hms2, List.append_assoc]
      rw [hwdef, hts_eq, List.map_append, List.append_assoc, walkF_append] at hwalk_all
      cases hwf_l2 : walkF 1 ((expandL2List l2s).map Prod.fst) with
      | none => rw [hwf_l2] at hwalk_all; cases hwalk_all
      | some f_end =>
        rw [hwf_l2] at hwalk_all
        have hts_sim : ts = expandL2List [] ++ expandL2List l2s ++ (expandSymARep rt ++ List.replicate mt (0, 4)) := by
          simpa [expandL2List] using hts_eq
        obtain ⟨st', hinv_st', hf_end3, hsc_end⟩ :=
          simulate_l2 hv hchain hmatch l2s [] (expandSymARep rt ++ List.replicate mt (0, 4)) .root 1 0
            hts_sim hl2_p trivial (by omega) hv.root_start f_end hwf_l2
        simp only [List.nil_append, zero_add] at hinv_st' hsc_end
        obtain ⟨pu, hsc_le, _, hend, _⟩ := state_checks_ok hv hinv_st' hf_end3 hsc_end
        have hrt_le : rt ≤ cert.R_max := r_le_Rmax_of_base hv hchain hmatch
          ⟨expandL2List l2s, List.replicate mt (0, 4), by rw [hts_eq, List.append_assoc]⟩
        have hmt_le : mt ≤ 10 := m_le_10_of_base hv hchain hmatch
          ⟨expandL2List l2s ++ expandSymARep rt, [], by rw [hts_eq]; simp [List.append_assoc]⟩
        have hlen_L : (S.wdef 13 L).length = (expandL2List l2s).length + 10 * rt + mt + 1 := by
          rw [hwdef, hts_eq]; simp [expandSymARep_len]; omega
        have hsumA_rt : ((expandSymARep rt).map Prod.fst).sum = 2 * rt := sum_expandSymARep rt
        have hsum_L : (S.wdef 13 L).sum = ((expandL2List l2s).map Prod.fst).sum + 2 * rt + d_last := by
          rw [hwdef, hts_eq]; simp [List.map_append, List.sum_append, hsumA_rt, List.map_replicate]; omega
        have hA_nn : (0 : Int) ≤ (cert.A : Int) := Int.natCast_nonneg _
        have hq_nn : (0 : Int) ≤ 2 * (cert.q : Int) := by omega
        unfold endBoundCheckL2 at hend
        simp only [Bool.and_eq_true] at hend
        have hfinal_int :
            2 * (cert.q : Int) * ((S.wdef 13 L).length : Int) +
              2 * (cert.q : Int) * (9 : Int) -
              (cert.A : Int) * ((S.wdef 13 L).sum : Int) ≤ (cert.bn : Int) := by
          rw [hlen_L, hsum_L]
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
          dsimp only at hwalk_all
          rw [List.map_append, List.map_replicate, List.append_assoc, walkF_append, walkF_expandSymARep] at hwalk_all
          by_cases hrt0 : rt = 0
          · -- Subcase rt = 0: identical to Level-1 (`eA` for mt = 0, `eB` for mt ≥ 1)!
            subst hrt0
            simp only [↓reduceIte, Nat.cast_zero, mul_zero, add_zero] at hwalk_all ⊢
            by_cases hmt0 : mt = 0
            · subst hmt0
              simp only [List.replicate_zero, List.nil_append, walkF] at hwalk_all
              simp only [Nat.cast_zero, add_zero]
              by_cases hf2 : f_end = 2
              · subst hf2
                have hA_nat := Nat.le_of_ble_eq_true (by simpa using hend.1.1)
                have hA_int : ((pu + 2 * cert.q + 2 * cert.q * 9 : Nat) : Int) ≤
                    ((cert.bias + cert.bn + cert.A : Nat) : Int) := by exact_mod_cast hA_nat
                have hd1 : (cert.A : Int) * 1 ≤ (cert.A : Int) * (d_last : Int) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hd_last_pos) hA_nn
                simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA_int; linarith
              · have hd_ge2 : 2 ≤ d_last := by
                  by_contra hlt; have hd1 : d_last = 1 := by omega
                  rw [hd1] at hwalk_all; unfold stepF at hwalk_all
                  have hne2 : (f_end == 2) = false := S.beq_false_of_ne hf2
                  simp [hne2] at hwalk_all
                have hne2 : Nat.beq f_end 2 = false := by cases hc : Nat.beq f_end 2 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hf2
                have hA_nat := Nat.le_of_ble_eq_true (by simpa [hne2] using hend.1.1)
                have hA_int : ((pu + 2 * cert.q + 2 * cert.q * 9 : Nat) : Int) ≤
                    ((cert.bias + cert.bn + 2 * cert.A : Nat) : Int) := by exact_mod_cast hA_nat
                have hd2 : (cert.A : Int) * 2 ≤ (cert.A : Int) * (d_last : Int) :=
                  mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge2) hA_nn
                simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA_int; linarith
            · -- rt = 0, mt ≥ 1 -> `eB`!
              have hmt1 : 1 ≤ mt := by omega
              rw [walkF_expandSym] at hwalk_all
              have hf_ne1 : f_end ≠ 1 := by intro hf1; unfold nextF at hwalk_all; simp [hf1, hmt1] at hwalk_all
              have hd0_false : stateD0 cert st' = false := by
                by_contra hd0t; have hd0' := Bool.eq_true_of_not_eq_false hd0t
                obtain ⟨tprev, ht4, ⟨pre0, hpre0⟩⟩ := stateD0_ends_zero hv hinv_st' hd0'
                exact hmt0 (m_eq_zero_after_d0 hv hchain hmatch ht4
                  ⟨pre0, [], by rw [hts_eq, ← hpre0]; simp [expandSymARep, List.append_assoc]⟩)
              have hd_ge2 : 2 ≤ d_last := by
                by_contra hlt; have hd1 : d_last = 1 := by omega
                rw [hd1] at hwalk_all; unfold nextF at hwalk_all
                have hne1 : (f_end == 1) = false := S.beq_false_of_ne hf_ne1
                simp [hne1, hmt1] at hwalk_all
              have hne1 : Nat.beq f_end 1 = false := by cases hc : Nat.beq f_end 1 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hf_ne1
              have hB_nat := Nat.le_of_ble_eq_true (by simpa [hne1, hd0_false] using hend.1.2)
              have hB_int : ((pu + 2 * cert.q * 11 + 2 * cert.q * 9 : Nat) : Int) ≤
                  ((cert.bias + cert.bn + 2 * cert.A : Nat) : Int) := by exact_mod_cast hB_nat
              have hmt_b : 2 * (cert.q : Int) * ((mt + 1 : Nat) : Int) ≤ 2 * (cert.q : Int) * 11 :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : mt + 1 ≤ 11)) hq_nn
              have hd2 : 2 * (cert.A : Int) ≤ (cert.A : Int) * (d_last : Int) := by
                have := mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge2 : (2 : Int) ≤ d_last) hA_nn; linarith
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hB_int hmt_b; linarith
          · -- Subcase rt ≥ 1 -> `eC`!
            have hrt1 : 1 ≤ rt := by omega
            have hf_ne1 : f_end ≠ 1 := by intro hf1; simp [hrt0, hf1] at hwalk_all
            simp only [hrt0, hf_ne1, ↓reduceIte] at hwalk_all
            have hd0_false : stateD0 cert st' = false := by
              by_contra hd0t; have hd0' := Bool.eq_true_of_not_eq_false hd0t
              obtain ⟨tprev, ht4, ⟨pre0, hpre0⟩⟩ := stateD0_ends_zero hv hinv_st' hd0'
              exact hrt0 (r_eq_zero_after_d0 hv hchain hmatch ht4
                ⟨pre0, List.replicate mt (0, 4), by rw [hts_eq, ← hpre0]; simp [List.append_assoc]⟩)
            have hcanA_true : stateCanA cert st' = true := by
              by_contra hnoA
              have hnoAf := Bool.eq_false_iff.mpr hnoA
              cases hls : stateLastS1 cert st' with
              | none => simp [stateCanA, hls] at hnoAf
              | some lc =>
                have hforb : isForb1 cert lc cert.idA = true := by
                  simp only [stateCanA, hls, Bool.not_eq_false'] at hnoAf; exact hnoAf
                obtain ⟨hlc_lt, ⟨pre0, hpre0⟩⟩ := stateLastS1_suffix hv hinv_st' hls
                cases rt with
                | zero => contradiction
                | succ rt' =>
                  have h1 : expandSymARep (rt' + 1) = expandSym 9 2 4 ++ expandSymARep rt' := by
                    simp [expandSymARep, List.replicate_succ, symA13]
                  exact not_infix_of_isForb1 hv hchain hmatch hlc_lt hv.idA_spec.1 hforb
                    ⟨pre0, expandSymARep rt' ++ List.replicate mt (0, 4), by
                      rw [hts_eq, ← hpre0, hv.idA_spec.2.1]; simp [h1, symA13, List.append_assoc]⟩
            have hne1 : Nat.beq f_end 1 = false := by cases hc : Nat.beq f_end 1 with | false => rfl | true => exact absurd (Nat.eq_of_beq_eq_true hc) hf_ne1
            have hC := hend.2
            simp only [hne1, hd0_false, hcanA_true, Bool.not_true, Bool.or_self,
              Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hC
            -- Extract the 4 endpoint bounds (r = 1 vs R_max) x (mt = 0 vs mt ≥ 1)!
            have hC10 : ((pu + 2 * cert.q * 10 + 2 * cert.q + 2 * cert.q * 9 : Nat) : Int) ≤
                ((cert.bias + cert.bn + 3 * cert.A : Nat) : Int) := by exact_mod_cast Nat.le_of_ble_eq_true hC.1.1.1
            have hC11 : ((pu + 2 * cert.q * 10 + 2 * cert.q * 11 + 2 * cert.q * 9 : Nat) : Int) ≤
                ((cert.bias + cert.bn + 4 * cert.A : Nat) : Int) := by exact_mod_cast Nat.le_of_ble_eq_true hC.1.1.2
            have hCR0 : ((pu + 2 * cert.q * 10 * cert.R_max + 2 * cert.q + 2 * cert.q * 9 : Nat) : Int) ≤
                ((cert.bias + cert.bn + (2 * cert.R_max + 1) * cert.A : Nat) : Int) := by exact_mod_cast Nat.le_of_ble_eq_true hC.1.2
            have hCR1 : ((pu + 2 * cert.q * 10 * cert.R_max + 2 * cert.q * 11 + 2 * cert.q * 9 : Nat) : Int) ≤
                ((cert.bias + cert.bn + (2 * cert.R_max + 2) * cert.A : Nat) : Int) := by exact_mod_cast Nat.le_of_ble_eq_true hC.2
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hC10 hC11 hCR0 hCR1
            let wA : Int := 2 * (cert.q : Int) * 10 - (cert.A : Int) * 2
            have hrt_b : (rt : Int) * wA ≤ max (1 * wA) ((cert.R_max : Int) * wA) := by
              by_cases hwA : 0 ≤ wA
              · exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrt_le) hwA) (le_max_right _ _)
              · exact le_trans (mul_le_mul_of_nonpos_right (by exact_mod_cast hrt1) (by omega)) (le_max_left _ _)
            by_cases hmt0 : mt = 0
            · subst hmt0
              simp only [Nat.cast_zero, add_zero]
              have hd1 : (cert.A : Int) * 1 ≤ (cert.A : Int) * (d_last : Int) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hd_last_pos) hA_nn
              rcases le_max_iff.mp hrt_b with h1 | hR <;> (dsimp only [wA] at *; linarith)
            · have hmt1 : 1 ≤ mt := by omega
              rw [walkF_expandSym] at hwalk_all
              have hd_ge2 : 2 ≤ d_last := by
                by_contra hlt; have hd1 : d_last = 1 := by omega
                rw [hd1] at hwalk_all; unfold nextF at hwalk_all; simp [hmt1] at hwalk_all
              have hmt_b : 2 * (cert.q : Int) * ((mt + 1 : Nat) : Int) ≤ 2 * (cert.q : Int) * 11 :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : mt + 1 ≤ 11)) hq_nn
              have hd2 : 2 * (cert.A : Int) ≤ (cert.A : Int) * (d_last : Int) := by
                have := mul_le_mul_of_nonneg_left (by exact_mod_cast hd_ge2 : (2 : Int) ≤ d_last) hA_nn; linarith
              simp only [Nat.cast_add, Nat.cast_one] at hmt_b
              rcases le_max_iff.mp hrt_b with h1 | hR <;> (dsimp only [wA] at *; linarith)
        -- Convert back to Nat WindowBound!
        unfold ChainC.WindowBound
        have hA_cast : (cert.A : Int) = (cert.q : Int) * 10 - (cert.cn : Int) := by
          have hle : cert.cn ≤ cert.q * 10 := by
            calc cert.cn ≤ cert.q * 8 := hv.hcn
              _ ≤ cert.q * 10 := Nat.mul_le_mul_left _ (by omega)
          rw [hv.hA, Nat.cast_sub hle]; simp only [Nat.cast_mul, Nat.cast_ofNat]
        rw [hA_cast] at hfinal_int
        have hnat_int :
            ((cert.q * (2 * (S.wdef 13 L).length + 2 * (13 - 4)) +
              cert.cn * (S.wdef 13 L).sum : Nat) : Int) ≤
            ((cert.q * ((13 - 3) * (S.wdef 13 L).sum) + cert.bn : Nat) : Int) := by
          have h13_4 : (13 - 4 : Nat) = 9 := rfl
          have h13_3 : (13 - 3 : Nat) = 10 := rfl
          rw [h13_4, h13_3]
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          linarith
        exact_mod_cast hnat_int

/-- **Main Pure-Kernel Theorem (`k = 13`):** Any valid Level-2 `TropicCEGAR` certificate
satisfying `ConditionsC 13 cert.cn cert.bn cert.q` proves
`∀ w : List (Fin 13), Covers w → boundC 13 cert.cn cert.bn cert.q ≤ w.length`! -/
theorem covers_length_ge_boundC_of_tropicL2 {cert : L2Cert} (hv : L2CertValid cert)
    (hcond : ConditionsC 13 cert.cn cert.bn cert.q) :
    ∀ w : List (Fin 13), Covers w → boundC 13 cert.cn cert.bn cert.q ≤ w.length :=
  covers_length_ge_boundC_of_model (by omega) hcond (modelStatement_of_wstatement (wstatement_of_tropicL2 hv))

end TropicL2
end SuperpermLowerBounds
