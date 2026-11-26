import LowerBounds.TropicSound
import LowerBounds.TropicN10.Data
import LowerBounds.TropicN10.CheckBasic
import LowerBounds.TropicN10.CheckStates_0
import LowerBounds.TropicN10.CheckOver_0
import LowerBounds.TropicN10.CheckCegar_0
import LowerBounds.TropicN10.CheckCegar_1
import LowerBounds.TropicN10.CheckForb2_0
import LowerBounds.TropicN10.CheckForb2_1
import LowerBounds.TropicN10.CheckForb2_2
import LowerBounds.TropicN10.CheckForb2_3
import LowerBounds.TropicN10.CheckForb2_4
import LowerBounds.TropicN10.CheckForb2_5
import LowerBounds.TropicN10.CheckForb2_6
import LowerBounds.TropicN10.CheckForb2_7

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds SuperpermLowerBounds.Tropic SuperpermutationBounds

theorem conditionsC_cert : ConditionsC 10 1 28 4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem boundC_cert : boundC 10 1 28 4 = 4033380 := by decide +kernel

theorem certValid : CertValid cert where
  hk5 := by decide +kernel
  hk15 := by decide +kernel
  hD1 := by decide +kernel
  hq := by decide +kernel
  hcn := by decide +kernel
  hA := by decide +kernel
  hV := by decide +kernel
  hbase := chk_base
  halpha := fun m hm d hd t ht =>
    checkRangeAux_spec (checkRangeAux_spec (checkRangeAux_spec chk_alpha m (Nat.zero_le _) (by dsimp only [cert] at *; omega)) d (Nat.zero_le _) (by dsimp only [cert] at *; omega)) t (Nat.zero_le _) (by omega)
  hd1 := fun a ha => checkRangeChunked_spec chk_d1 a (Nat.zero_le _) (by dsimp only [cert] at *; omega)
  hcegar := fun fid hfid =>
    if h0 : fid < 22 then checkRangeAux_spec chk_cegar_0 fid (by omega) (by omega) else
    checkRangeAux_spec chk_cegar_1 fid (by omega) (by dsimp only [cert] at *; omega)
  hforb2 := fun s hs a ha hpm =>
    forb2_of_checkForb2Sym (
    if h0 : s < 20 then checkRangeAux_spec chk_forb2_0 s (by omega) (by omega) else
    if h1 : s < 40 then checkRangeAux_spec chk_forb2_1 s (by omega) (by omega) else
    if h2 : s < 60 then checkRangeAux_spec chk_forb2_2 s (by omega) (by omega) else
    if h3 : s < 80 then checkRangeAux_spec chk_forb2_3 s (by omega) (by omega) else
    if h4 : s < 100 then checkRangeAux_spec chk_forb2_4 s (by omega) (by omega) else
    if h5 : s < 120 then checkRangeAux_spec chk_forb2_5 s (by omega) (by omega) else
    if h6 : s < 140 then checkRangeAux_spec chk_forb2_6 s (by omega) (by omega) else
    checkRangeAux_spec chk_forb2_7 s (by omega) (by dsimp only [cert] at *; omega)
    ) a ha hpm
  hstates := fun u hu =>
    checkRangeChunked_spec chk_states_0 u (by omega) (by dsimp only [cert] at *; omega)
  hroot := fun a ha => checkRangeChunked_spec chk_root a (Nat.zero_le _) (by dsimp only [cert] at *; omega)
  hpairs := fun s hs a ha =>
    checkRangeChunked_spec (checkRangeChunked_spec chk_pairs s (Nat.zero_le _) (by dsimp only [cert] at *; omega)) a (Nat.zero_le _) (by dsimp only [cert] at *; omega)
  hover := fun u hu a ha =>
    checkRangeChunked_spec (
    checkRangeChunked_spec chk_over_0 u (by omega) (by dsimp only [cert] at *; omega)
    ) a (Nat.zero_le _) (by dsimp only [cert] at *; omega)

/-- Pure-kernel proof of `S(10) ≥ 4033380` via `TropicCEGAR-Macro` + Theorem C. -/
theorem covers_length_ge_4033380 : ∀ w : List (Fin 10), Covers w → 4033380 ≤ w.length := by
  have h := covers_length_ge_boundC_of_tropic certValid conditionsC_cert
  change ∀ w : List (Fin cert.k), Covers w → boundC cert.k cert.cn cert.bn cert.q ≤ w.length at h
  simpa [cert, boundC_cert] using h

end SuperpermLowerBounds.Tropic.TropicN10

#print axioms SuperpermLowerBounds.Tropic.TropicN10.covers_length_ge_4033380
