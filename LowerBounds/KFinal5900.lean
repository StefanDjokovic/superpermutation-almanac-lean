import LowerBounds.FastK16Sound
import LowerBounds.KFinal
import LowerBounds.PFinalK16

/-!
# Table T' and Theorem K from `FastK16.seqSearch`

ZERO `sorry`, ZERO `native_decide`! This module connects:
1. `setB_of_k16`: derives `KS.SetB` from the 6 `K16.seqSearch` equations (`PK16F0Native`,
   `PK16F1Native`, `PK16Native`) + `PS.ringSearch` (`PRingNative`) of the fast 5,899 proof.
2. `tableT_of_fast` & `theoremK_of_fast`: derives `KS.TableT` and `KS.TheoremK` from
   `FastEvalsT` and `FastEvalsK` evaluated by `FastK16.seqSearch` (with exact soundness
   from `FastK16Sound.seqCap_of_fastK16` and kernel `decide` checks on `Ttab`/`Dtab`).
-/

namespace SuperpermLowerBounds
namespace K5900

open T5899 T5900
open PS (SeqCapLt RingCapT capF holesT linksT)
open KS (SetB TableT TheoremK EvR capF_row)

/-! ### 1. Set B from the fast 5,899 `K16.seqSearch` equations -/

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
variable {a₀ b₀ h₀ a₁ b₁ h₁ a₂ b₂ h₂ a₃ b₃ h₃ a₄ b₄ h₄ a₅ b₅ h₅ : ℕ}
variable {j₀ j₁ j₂ j₃ j₄ j₅ : Bool}

theorem setB_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (K16.seqSearch 7 Ptabs 1 0 78 a₁ b₁ h₁ j₁ f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (K16.seqSearch 7 Ptabs 2 0 72 a₂ b₂ h₂ j₂ f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (K16.seqSearch 7 Ptabs 3 0 66 a₃ b₃ h₃ j₃ f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (K16.seqSearch 7 Ptabs 4 0 60 a₄ b₄ h₄ j₄ f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (K16.seqSearch 7 Ptabs 5 0 54 a₅ b₅ h₅ j₅ f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR)) : SetB := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ h0 h1 h2 h3 h4 h5
  refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
  have hM : SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
    rw [← capF_zero]
    exact c0.mono (by norm_num)
  exact PS.ringCapT_of_search (by norm_num) (by norm_num) hnR hM hR

end

/-! ### 2. `FastEv` and `FastEvalsT` / `FastEvalsK` -/

/-- `FastK16.seqSearch` covers all `nt` parts for `(tab, s, lo, hi, a, b, h, js, useM3, useW4)`. -/
def FastEv (tab : List (List ℕ)) (s lo hi a b h : ℕ) (js useM3 useW4 : Bool) : Prop :=
  ∃ fuel ds nt, fuel < 250 ∧ 0 < nt ∧ nt < 65536 ∧
    PS.Covered nt (FastK16.seqSearch tab s lo hi a b h js useM3 useW4 fuel ds nt)

/-- The evaluated statements behind table `T'`. -/
structure FastEvalsT : Prop where
  c59 : FastEv Ttab 0 59 59 5 8 5 true true false
  c62 : FastEv Ttab 0 62 75 50 79 5 true true false
  c76 : FastEv Ttab 0 76 76 25 39 5 true true false
  ring : EvR (Ttab.getD 0 []) TRtab 69
  k5 : FastEv Dtab 5 44 60 10 17 25 true true true
  k6a : FastEv Dtab 6 0 43 10 17 25 true false false
  k6b : FastEv Dtab 6 44 54 10 18 25 true true true
  k7 : FastEv Ttab 7 0 48 1 0 0 true false false
  k8 : FastEv Ttab 8 0 42 1 0 0 true false false

/-- The evaluated statements for `0..4` links on table `D`. -/
structure FastEvalsK : Prop where
  k0 : FastEv Dtab 0 77 90 50 74 5 true true false
  k1 : FastEv Dtab 1 62 84 25 38 70 true true true
  k2 : FastEv Dtab 2 61 78 25 39 75 true true true
  k3 : FastEv Dtab 3 55 72 20 31 60 true true true
  k4 : FastEv Dtab 4 48 66 10 16 25 true true true

/-! ### 3. Kernel-checked side conditions on `Ttab` and `Dtab` -/

private theorem ttab_le_200 : ∀ row ∈ Ttab, ∀ v ∈ row, v ≤ 200 := by decide +kernel
private theorem dtab_le_200 : ∀ row ∈ Dtab, ∀ v ∈ row, v ≤ 200 := by decide +kernel

private theorem m3_c59 : ∀ x, 59 ≤ x → x ≤ 59 → ∀ y, y < x → capF Ttab 0 y + x ≤ capF Ttab 0 x + y := by decide +kernel
private theorem m3_c62 : ∀ x, 62 ≤ x → x ≤ 75 → ∀ y, y < x → capF Ttab 0 y + x ≤ capF Ttab 0 x + y := by decide +kernel
private theorem m3_c76 : ∀ x, 76 ≤ x → x ≤ 76 → ∀ y, y < x → capF Ttab 0 y + x ≤ capF Ttab 0 x + y := by decide +kernel
private theorem m3_k0  : ∀ x, 77 ≤ x → x ≤ 90 → ∀ y, y < x → capF Dtab 0 y + x ≤ capF Dtab 0 x + y := by decide +kernel
private theorem m3_k1  : ∀ x, 62 ≤ x → x ≤ 84 → ∀ y, y < x → capF Dtab 1 y + x ≤ capF Dtab 1 x + y := by decide +kernel
private theorem m3_k2  : ∀ x, 61 ≤ x → x ≤ 78 → ∀ y, y < x → capF Dtab 2 y + x ≤ capF Dtab 2 x + y := by decide +kernel
private theorem m3_k3  : ∀ x, 55 ≤ x → x ≤ 72 → ∀ y, y < x → capF Dtab 3 y + x ≤ capF Dtab 3 x + y := by decide +kernel
private theorem m3_k4  : ∀ x, 48 ≤ x → x ≤ 66 → ∀ y, y < x → capF Dtab 4 y + x ≤ capF Dtab 4 x + y := by decide +kernel
private theorem m3_k5  : ∀ x, 44 ≤ x → x ≤ 60 → ∀ y, y < x → capF Dtab 5 y + x ≤ capF Dtab 5 x + y := by decide +kernel
private theorem m3_k6b : ∀ x, 44 ≤ x → x ≤ 54 → ∀ y, y < x → capF Dtab 6 y + x ≤ capF Dtab 6 x + y := by decide +kernel

private theorem w4_k1 : ∀ x, 62 ≤ x → x ≤ 84 → ∀ y, y ≤ x + 6 → capF Dtab 0 y + x + 5 ≤ capF Dtab 1 x + y := by decide +kernel
private theorem w4_k2 : ∀ x, 61 ≤ x → x ≤ 78 → ∀ y, y ≤ x + 6 → capF Dtab 1 y + x + 5 ≤ capF Dtab 2 x + y := by decide +kernel
private theorem w4_k3 : ∀ x, 55 ≤ x → x ≤ 72 → ∀ y, y ≤ x + 6 → capF Dtab 2 y + x + 5 ≤ capF Dtab 3 x + y := by decide +kernel
private theorem w4_k4 : ∀ x, 48 ≤ x → x ≤ 66 → ∀ y, y ≤ x + 6 → capF Dtab 3 y + x + 5 ≤ capF Dtab 4 x + y := by decide +kernel
private theorem w4_k5 : ∀ x, 44 ≤ x → x ≤ 60 → ∀ y, y ≤ x + 6 → capF Dtab 4 y + x + 5 ≤ capF Dtab 5 x + y := by decide +kernel
private theorem w4_k6b : ∀ x, 44 ≤ x → x ≤ 54 → ∀ y, y ≤ x + 6 → capF Dtab 5 y + x + 5 ≤ capF Dtab 6 x + y := by decide +kernel

private theorem seqCap_of_fastEv {tab : List (List ℕ)} {s lo hi a b h : ℕ} {js useM3 useW4 : Bool}
    (hs : s < 15) (hhi : hi < 200) (hR : KS.rowsR tab s hi < 250)
    (habh : a ≤ 100 ∧ b ≤ 100 ∧ h ≤ 100)
    (hcaps : ∀ row ∈ tab, ∀ v ∈ row, v ≤ 200)
    (hlow : ∀ j, j < s → SeqCapLt 7 j (capF tab j) (hi + 1))
    (hprev : SeqCapLt 7 s (capF tab s) lo)
    (hM3 : useM3 = true → ∀ x, lo ≤ x → x ≤ hi → ∀ y, y < x → capF tab s y + x ≤ capF tab s x + y)
    (hW4 : useW4 = true → 1 ≤ s ∧ SeqCapLt 7 (s - 1) (capF tab (s - 1)) (hi + 7) ∧
      ∀ x, lo ≤ x → x ≤ hi → ∀ y, y ≤ x + 6 → capF tab (s - 1) y + x + 5 ≤ capF tab s x + y)
    (hE : FastEv tab s lo hi a b h js useM3 useW4) :
    SeqCapLt 7 s (capF tab s) (hi + 1) := by
  obtain ⟨fuel, ds, nt, hfuel, hnt0, hnt65, hcov⟩ := hE
  exact FastK16Sound.seqCap_of_fastK16 hs hhi hR hfuel habh ⟨hnt0, hnt65⟩ hcaps hlow hprev hM3 hW4 hcov

/-! ### 4. Table T' and Theorem K from `FastEvalsT` / `FastEvalsK` -/

theorem chainT_of_fast (hB : SetB) (hT : FastEvalsT) : SeqCapLt 7 0 (capF Ttab 0) 85 := by
  obtain ⟨b0, -⟩ := hB
  have none : ∀ j, j < 0 → SeqCapLt 7 j (capF Ttab j) (59 + 1) :=
    fun j hj => absurd hj (Nat.not_lt_zero j)
  have t59 : SeqCapLt 7 0 (capF Ttab 0) (59 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) ttab_le_200
      none ((b0.mono (b := 59) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_c59) (fun h => by cases h) hT.c59
  have t61 : SeqCapLt 7 0 (capF Ttab 0) 62 :=
    t59.glue (b0.mono (b := 62) (by norm_num)) (by decide +kernel)
  have t75 : SeqCapLt 7 0 (capF Ttab 0) (75 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) ttab_le_200
      (fun j hj => absurd hj (Nat.not_lt_zero j)) t61
      (fun _ => m3_c62) (fun h => by cases h) hT.c62
  have t76 : SeqCapLt 7 0 (capF Ttab 0) (76 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) ttab_le_200
      (fun j hj => absurd hj (Nat.not_lt_zero j)) t75
      (fun _ => m3_c76) (fun h => by cases h) hT.c76
  exact t76.glue b0 (by decide +kernel)

/-- Rows `0..4` of `Dtab`, proved from `SetB`, `c59..c76`, and `FastEvalsK` (`k0..k4`). -/
private theorem d04_of_fast (hB : SetB) (hT : FastEvalsT) (hK : FastEvalsK) :
    SeqCapLt 7 0 (capF Dtab 0) 91 ∧ SeqCapLt 7 1 (capF Dtab 1) 85 ∧
    SeqCapLt 7 2 (capF Dtab 2) 79 ∧ SeqCapLt 7 3 (capF Dtab 3) 73 ∧
    SeqCapLt 7 4 (capF Dtab 4) 67 := by
  have t0 := chainT_of_fast hB hT
  obtain ⟨-, b1, b2, b3, b4, -, -⟩ := hB
  have t1 : SeqCapLt 7 1 (capF Ttab 1) 79 := by
    rw [capF_row (show Ttab.getD 1 [] = Ptabs.getD 1 [] from by decide +kernel)]; exact b1
  have t2 : SeqCapLt 7 2 (capF Ttab 2) 73 := by
    rw [capF_row (show Ttab.getD 2 [] = Ptabs.getD 2 [] from by decide +kernel)]; exact b2
  have t3 : SeqCapLt 7 3 (capF Ttab 3) 67 := by
    rw [capF_row (show Ttab.getD 3 [] = Ptabs.getD 3 [] from by decide +kernel)]; exact b3
  have t4 : SeqCapLt 7 4 (capF Ttab 4) 61 := by
    rw [capF_row (show Ttab.getD 4 [] = Ptabs.getD 4 [] from by decide +kernel)]; exact b4
  have d0 : SeqCapLt 7 0 (capF Dtab 0) (90 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => absurd hj (Nat.not_lt_zero j))
      ((t0.mono (b := 77) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k0) (fun h => by cases h) hK.k0
  have d1 : SeqCapLt 7 1 (capF Dtab 1) (84 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by interval_cases j; exact d0.mono (by norm_num))
      ((t1.mono (b := 62) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k1) (fun _ => ⟨by norm_num, d0, w4_k1⟩) hK.k1
  have d2 : SeqCapLt 7 2 (capF Dtab 2) (78 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num))
      ((t2.mono (b := 61) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k2) (fun _ => ⟨by norm_num, d1, w4_k2⟩) hK.k2
  have d3 : SeqCapLt 7 3 (capF Dtab 3) (72 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num)
        · exact d2.mono (by norm_num))
      ((t3.mono (b := 55) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k3) (fun _ => ⟨by norm_num, d2, w4_k3⟩) hK.k3
  have d4 : SeqCapLt 7 4 (capF Dtab 4) (66 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num)
        · exact d2.mono (by norm_num)
        · exact d3.mono (by norm_num))
      ((t4.mono (b := 48) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k4) (fun _ => ⟨by norm_num, d3, w4_k4⟩) hK.k4
  exact ⟨d0, d1, d2, d3, d4⟩

/-- **Table T' is valid**, given `SetB`, `FastEvalsT`, and `FastEvalsK`. -/
theorem tableT_of_fast (hB : SetB) (hT : FastEvalsT) (hK : FastEvalsK) : TableT := by
  have t0 := chainT_of_fast hB hT
  obtain ⟨d0, d1, d2, d3, d4⟩ := d04_of_fast hB hT hK
  obtain ⟨-, b1, b2, b3, b4, b5, bR⟩ := hB
  have t1 : SeqCapLt 7 1 (capF Ttab 1) 79 := by
    rw [capF_row (show Ttab.getD 1 [] = Ptabs.getD 1 [] from by decide +kernel)]; exact b1
  have t2 : SeqCapLt 7 2 (capF Ttab 2) 73 := by
    rw [capF_row (show Ttab.getD 2 [] = Ptabs.getD 2 [] from by decide +kernel)]; exact b2
  have t3 : SeqCapLt 7 3 (capF Ttab 3) 67 := by
    rw [capF_row (show Ttab.getD 3 [] = Ptabs.getD 3 [] from by decide +kernel)]; exact b3
  have t4 : SeqCapLt 7 4 (capF Ttab 4) 61 := by
    rw [capF_row (show Ttab.getD 4 [] = Ptabs.getD 4 [] from by decide +kernel)]; exact b4
  have d5 : SeqCapLt 7 5 (capF Dtab 5) (60 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num)
        · exact d2.mono (by norm_num)
        · exact d3.mono (by norm_num)
        · exact d4.mono (by norm_num))
      ((b5.mono (b := 44) (by norm_num)).congr (by decide +kernel))
      (fun _ => m3_k5) (fun _ => ⟨by norm_num, d4, w4_k5⟩) hT.k5
  have t5 : SeqCapLt 7 5 (capF Ttab 5) (60 + 1) := by
    rw [capF_row (show Ttab.getD 5 [] = Dtab.getD 5 [] from by decide +kernel)]; exact d5
  have d6a : SeqCapLt 7 6 (capF Dtab 6) (43 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num)
        · exact d2.mono (by norm_num)
        · exact d3.mono (by norm_num)
        · exact d4.mono (by norm_num)
        · exact d5.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) (fun h => by cases h) (fun h => by cases h) hT.k6a
  have d6 : SeqCapLt 7 6 (capF Dtab 6) (54 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) dtab_le_200
      (fun j hj => by
        interval_cases j
        · exact d0.mono (by norm_num)
        · exact d1.mono (by norm_num)
        · exact d2.mono (by norm_num)
        · exact d3.mono (by norm_num)
        · exact d4.mono (by norm_num)
        · exact d5.mono (by norm_num))
      d6a (fun _ => m3_k6b) (fun _ => ⟨by norm_num, d5, w4_k6b⟩) hT.k6b
  have t6 : SeqCapLt 7 6 (capF Ttab 6) (54 + 1) := by
    rw [capF_row (show Ttab.getD 6 [] = Dtab.getD 6 [] from by decide +kernel)]; exact d6
  have t7 : SeqCapLt 7 7 (capF Ttab 7) (48 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) ttab_le_200
      (fun j hj => by
        interval_cases j
        · exact t0.mono (by norm_num)
        · exact t1.mono (by norm_num)
        · exact t2.mono (by norm_num)
        · exact t3.mono (by norm_num)
        · exact t4.mono (by norm_num)
        · exact t5.mono (by norm_num)
        · exact t6.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) (fun h => by cases h) (fun h => by cases h) hT.k7
  have t8 : SeqCapLt 7 8 (capF Ttab 8) (42 + 1) :=
    seqCap_of_fastEv (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) ttab_le_200
      (fun j hj => by
        interval_cases j
        · exact t0.mono (by norm_num)
        · exact t1.mono (by norm_num)
        · exact t2.mono (by norm_num)
        · exact t3.mono (by norm_num)
        · exact t4.mono (by norm_num)
        · exact t5.mono (by norm_num)
        · exact t6.mono (by norm_num)
        · exact t7.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) (fun h => by cases h) (fun h => by cases h) hT.k8
  refine ⟨fun s hs => ?_, ?_⟩
  · interval_cases s
    · exact t0
    · exact t1
    · exact t2
    · exact t3
    · exact t4
    · exact t5
    · exact t6
    · exact t7
    · exact t8
  · obtain ⟨fuel, ds, nt, hnt, hc⟩ := hT.ring
    have r69 : RingCapT 7 (fun x => TRtab.getD x 0) 69 :=
      PS.ringCapT_of_search (by norm_num) (by norm_num) hnt (t0.mono (by norm_num)) hc
    intro L hL h0 h2 hcl hG
    by_cases h69 : holesT 7 L ≤ 69
    · exact r69 L hL h0 h2 hcl h69
    have hchain : L.length ≤ capF Ttab 0 (holesT 7 L) :=
      t0 L hL (fun x hx => by rw [h0 x hx]; exact Nat.zero_le 1) (PS.linksT_zero h0) (by omega)
    by_cases h77 : holesT 7 L ≤ 77
    · have hring := bR L hL h0 h2 hcl h77
      have e : ∀ x, 70 ≤ x → x ≤ 77 →
          TRtab.getD x 0 = min (PRtab.getD x 0) (capF Ttab 0 x) := by decide +kernel
      show L.length ≤ TRtab.getD (holesT 7 L) 0
      rw [e _ (by omega) h77]
      exact le_min hring hchain
    · have e : ∀ x, 78 ≤ x → x ≤ 84 → TRtab.getD x 0 = capF Ttab 0 x := by decide +kernel
      show L.length ≤ TRtab.getD (holesT 7 L) 0
      rw [e _ (by omega) hG]
      exact hchain

/-- **Theorem K**, given `SetB`, `FastEvalsT`, and `FastEvalsK`. -/
theorem theoremK_of_fast (hB : SetB) (hT : FastEvalsT) (hK : FastEvalsK) : TheoremK := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := d04_of_fast hB hT hK
  obtain ⟨hrows, -⟩ := tableT_of_fast hB hT hK
  have t5 : SeqCapLt 7 5 (capF Ttab 5) 61 := hrows 5 (by norm_num)
  have t6 : SeqCapLt 7 6 (capF Ttab 6) 55 := hrows 6 (by norm_num)
  have t7 : SeqCapLt 7 7 (capF Ttab 7) 49 := hrows 7 (by norm_num)
  have t8 : SeqCapLt 7 8 (capF Ttab 8) 43 := hrows 8 (by norm_num)
  intro s hs
  interval_cases s
  · exact d0
  · exact d1
  · exact d2
  · exact d3
  · exact d4
  · rw [capF_row (show Dtab.getD 5 [] = Ttab.getD 5 [] from by decide +kernel)]; exact t5
  · rw [capF_row (show Dtab.getD 6 [] = Ttab.getD 6 [] from by decide +kernel)]; exact t6
  · rw [capF_row (show Dtab.getD 7 [] = Ttab.getD 7 [] from by decide +kernel)]; exact t7
  · rw [capF_row (show Dtab.getD 8 [] = Ttab.getD 8 [] from by decide +kernel)]; exact t8

end K5900
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K5900.setB_of_k16
#print axioms SuperpermLowerBounds.K5900.tableT_of_fast
#print axioms SuperpermLowerBounds.K5900.theoremK_of_fast
