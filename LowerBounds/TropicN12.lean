import LowerBounds.TropicSound
import LowerBounds.TropicN12.Data
import LowerBounds.TropicN12.CheckBasic
import LowerBounds.TropicN12.CheckStates_0
import LowerBounds.TropicN12.CheckStates_1
import LowerBounds.TropicN12.CheckStates_2
import LowerBounds.TropicN12.CheckStates_3
import LowerBounds.TropicN12.CheckStates_4
import LowerBounds.TropicN12.CheckStates_5
import LowerBounds.TropicN12.CheckStates_6
import LowerBounds.TropicN12.CheckOver_0
import LowerBounds.TropicN12.CheckOver_1
import LowerBounds.TropicN12.CheckOver_2
import LowerBounds.TropicN12.CheckOver_3
import LowerBounds.TropicN12.CheckOver_4
import LowerBounds.TropicN12.CheckOver_5
import LowerBounds.TropicN12.CheckOver_6
import LowerBounds.TropicN12.CheckCegar_0
import LowerBounds.TropicN12.CheckCegar_1
import LowerBounds.TropicN12.CheckCegar_2
import LowerBounds.TropicN12.CheckCegar_3
import LowerBounds.TropicN12.CheckCegar_4
import LowerBounds.TropicN12.CheckCegar_5
import LowerBounds.TropicN12.CheckCegar_6
import LowerBounds.TropicN12.CheckForb2_0
import LowerBounds.TropicN12.CheckForb2_1
import LowerBounds.TropicN12.CheckForb2_2
import LowerBounds.TropicN12.CheckForb2_3
import LowerBounds.TropicN12.CheckForb2_4
import LowerBounds.TropicN12.CheckForb2_5

namespace SuperpermLowerBounds.Tropic.TropicN12
open SuperpermLowerBounds SuperpermLowerBounds.Tropic SuperpermutationBounds

theorem conditionsC_cert : ConditionsC 12 203 24408 4596 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem boundC_cert : boundC 12 203 24408 4596 = 522622407 := by decide +kernel

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
    if h0 : fid < 102 then checkRangeAux_spec chk_cegar_0 fid (by omega) (by dsimp only [cert] at *; omega) else
    if h1 : fid < 144 then checkRangeAux_spec chk_cegar_1 fid (by omega) (by dsimp only [cert] at *; omega) else
    if h2 : fid < 172 then checkRangeAux_spec chk_cegar_2 fid (by omega) (by dsimp only [cert] at *; omega) else
    if h3 : fid < 191 then checkRangeAux_spec chk_cegar_3 fid (by omega) (by dsimp only [cert] at *; omega) else
    if h4 : fid < 221 then checkRangeAux_spec chk_cegar_4 fid (by omega) (by dsimp only [cert] at *; omega) else
    if h5 : fid < 241 then checkRangeAux_spec chk_cegar_5 fid (by omega) (by dsimp only [cert] at *; omega) else
    checkRangeAux_spec chk_cegar_6 fid (by omega) (by dsimp only [cert] at *; omega)
  hforb2 := fun s hs a ha hpm =>
    forb2_of_checkForb2Sym (
    if h0 : s < 24 then checkRangeAux_spec chk_forb2_0 s (by omega) (by dsimp only [cert] at *; omega) else
    if h1 : s < 48 then checkRangeAux_spec chk_forb2_1 s (by omega) (by dsimp only [cert] at *; omega) else
    if h2 : s < 72 then checkRangeAux_spec chk_forb2_2 s (by omega) (by dsimp only [cert] at *; omega) else
    if h3 : s < 96 then checkRangeAux_spec chk_forb2_3 s (by omega) (by dsimp only [cert] at *; omega) else
    if h4 : s < 120 then checkRangeAux_spec chk_forb2_4 s (by omega) (by dsimp only [cert] at *; omega) else
    checkRangeAux_spec chk_forb2_5 s (by omega) (by dsimp only [cert] at *; omega)
    ) a ha hpm
  hstates := fun u hu =>
    if h0 : u < 8192 then checkRangeChunked_spec chk_states_0 u (by omega) (by dsimp only [cert] at *; omega) else
    if h1 : u < 16384 then checkRangeChunked_spec chk_states_1 u (by omega) (by dsimp only [cert] at *; omega) else
    if h2 : u < 24576 then checkRangeChunked_spec chk_states_2 u (by omega) (by dsimp only [cert] at *; omega) else
    if h3 : u < 32768 then checkRangeChunked_spec chk_states_3 u (by omega) (by dsimp only [cert] at *; omega) else
    if h4 : u < 40960 then checkRangeChunked_spec chk_states_4 u (by omega) (by dsimp only [cert] at *; omega) else
    if h5 : u < 49152 then checkRangeChunked_spec chk_states_5 u (by omega) (by dsimp only [cert] at *; omega) else
    checkRangeChunked_spec chk_states_6 u (by omega) (by dsimp only [cert] at *; omega)
  hroot := fun a ha => checkRangeChunked_spec chk_root a (Nat.zero_le _) (by dsimp only [cert] at *; omega)
  hpairs := fun s hs a ha =>
    checkRangeChunked_spec (checkRangeChunked_spec chk_pairs s (Nat.zero_le _) (by dsimp only [cert] at *; omega)) a (Nat.zero_le _) (by dsimp only [cert] at *; omega)
  hover := fun u hu =>
    if h0 : u < 8192 then checkRangeChunked_spec chk_over_0 u (by omega) (by dsimp only [cert] at *; omega) else
    if h1 : u < 16384 then checkRangeChunked_spec chk_over_1 u (by omega) (by dsimp only [cert] at *; omega) else
    if h2 : u < 24576 then checkRangeChunked_spec chk_over_2 u (by omega) (by dsimp only [cert] at *; omega) else
    if h3 : u < 32768 then checkRangeChunked_spec chk_over_3 u (by omega) (by dsimp only [cert] at *; omega) else
    if h4 : u < 40960 then checkRangeChunked_spec chk_over_4 u (by omega) (by dsimp only [cert] at *; omega) else
    if h5 : u < 49152 then checkRangeChunked_spec chk_over_5 u (by omega) (by dsimp only [cert] at *; omega) else
    checkRangeChunked_spec chk_over_6 u (by omega) (by dsimp only [cert] at *; omega)

/-- Pure-kernel proof of `S(12) ≥ 522622407` via `TropicCEGAR-Macro` + Theorem C. -/
theorem covers_length_ge_522622407 : ∀ w : List (Fin 12), Covers w → 522622407 ≤ w.length := by
  have h := covers_length_ge_boundC_of_tropic certValid conditionsC_cert
  change ∀ w : List (Fin cert.k), Covers w → boundC cert.k cert.cn cert.bn cert.q ≤ w.length at h
  simpa [cert, boundC_cert] using h

end SuperpermLowerBounds.Tropic.TropicN12

#print axioms SuperpermLowerBounds.Tropic.TropicN12.covers_length_ge_522622407
