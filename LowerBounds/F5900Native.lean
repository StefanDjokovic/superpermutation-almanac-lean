import LowerBounds.F5900Joint
import LowerBounds.PFinalK16
import LowerBounds.KFinal5900
import LowerBounds.J15Final5900
import LowerBounds.PK16F0Native
import LowerBounds.PK16F1Native
import LowerBounds.PK16Native
import LowerBounds.PRingNative
import LowerBounds.PProfNative
import LowerBounds.F5900K0_5Native

/-!
# 5,900 for 7 symbols, assembled from the evaluated equations (`native_decide`)

**Trusted here.**  This theorem combines:
1. The 12 evaluated equations of `5,899` (`PK16F0Native`, `PK16F1Native`, `PK16Native`,
   `PRingNative`, `PProfNative`), giving `Caps`, `Profiles`, and `KS.SetB`.
2. The accelerated `FastK16.seqSearch` + `PS.ringSearch` evaluations for Table `T'` and Theorem `K`
   (`F5900SmallNative` .. `F5900K0_5Native`), proven sound in `FastK16Sound.lean` and `KFinal5900.lean`.
3. The Dual Cycle Lemma ring evaluations on `H = 70..83` (`DualRingSound.lean`) and the accelerated
   `FastJ16.jSearch` evaluations for `S1 .. S5`, proven sound in `FastJ16Sound.lean` and `J15Final5900.lean`.

Every soundness theorem is kernel-checked with axioms `[propext, Classical.choice, Quot.sound]` only.
-/

namespace SuperpermLowerBounds

open T5899 T5900 J5900

private theorem cov_one_j {nt : ℕ} {f : ℕ → ℕ → Bool} (h : f 0 nt = false) :
    J15.Cov nt f :=
  fun _ htp => ⟨0, nt, Nat.zero_le _, htp, h⟩

private theorem fastEvalsT_native : K5900.FastEvalsT where
  c59 := ⟨200, 0, 1, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.c59⟩
  c62 := ⟨200, 18, 61, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.c62⟩
  c76 := ⟨200, 18, 61, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.c76⟩
  ring := ⟨400, 16, 61, by norm_num, PS.covered_one F5900Shards.ring69⟩
  k5 := ⟨200, 18, 61, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k5⟩
  k6a := ⟨200, 0, 1, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k6a⟩
  k6b := ⟨200, 0, 1, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k6b⟩
  k7 := ⟨200, 0, 1, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k7⟩
  k8 := ⟨200, 0, 1, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k8⟩

private theorem fastEvalsK_native : K5900.FastEvalsK where
  k0 := ⟨200, 20, 499, by norm_num, by norm_num, by norm_num, by
    intro tp htp
    by_cases h0 : tp < 84
    · exact ⟨0, 84, by omega, h0, F5900Shards.k0_0⟩
    by_cases h1 : tp < 167
    · exact ⟨84, 167, by omega, h1, F5900Shards.k0_1⟩
    by_cases h2 : tp < 250
    · exact ⟨167, 250, by omega, h2, F5900Shards.k0_2⟩
    by_cases h3 : tp < 333
    · exact ⟨250, 333, by omega, h3, F5900Shards.k0_3⟩
    by_cases h4 : tp < 416
    · exact ⟨333, 416, by omega, h4, F5900Shards.k0_4⟩
    exact ⟨416, 499, by omega, htp, F5900Shards.k0_5⟩⟩
  k1 := ⟨200, 20, 499, by norm_num, by norm_num, by norm_num, by
    intro tp htp
    by_cases h0 : tp < 100
    · exact ⟨0, 100, by omega, h0, F5900Shards.k1_0⟩
    by_cases h1 : tp < 200
    · exact ⟨100, 200, by omega, h1, F5900Shards.k1_1⟩
    by_cases h2 : tp < 300
    · exact ⟨200, 300, by omega, h2, F5900Shards.k1_2⟩
    by_cases h3 : tp < 400
    · exact ⟨300, 400, by omega, h3, F5900Shards.k1_3⟩
    exact ⟨400, 499, by omega, htp, F5900Shards.k1_4⟩⟩
  k2 := ⟨200, 18, 251, by norm_num, by norm_num, by norm_num, by
    intro tp htp
    by_cases h0 : tp < 84
    · exact ⟨0, 84, by omega, h0, F5900Shards.k2_0⟩
    by_cases h1 : tp < 168
    · exact ⟨84, 168, by omega, h1, F5900Shards.k2_1⟩
    exact ⟨168, 251, by omega, htp, F5900Shards.k2_2⟩⟩
  k3 := ⟨200, 20, 199, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k3⟩
  k4 := ⟨200, 18, 61, by norm_num, by norm_num, by norm_num, PS.covered_one F5900Shards.k4⟩

private theorem fastJEvals_native : J5900.FastJEvals where
  tr15 := ⟨100, 0, 1, by norm_num, PS.covered_one F5900Shards.tr15⟩
  trdual := by
    intro H h70 h83
    interval_cases H
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_70⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_71⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_72⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_73⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_74⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_75⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_76⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_77⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_78⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_79⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_80⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_81⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_82⟩
    · exact ⟨200, 0, 1, by norm_num, PS.covered_one F5900Shards.trdual_83⟩
  s1 := ⟨300, [(0, 14, 199)], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s1⟩
  s2a1_hi := ⟨300, [(0, 18, 199)], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s2a1_hi⟩
  s2a1_lo := ⟨300, [(0, 16, 199)], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s2a1_lo⟩
  s2a2 := ⟨300, [(0, 16, 199)], by norm_num, by decide, by decide, by
    intro tp htp
    simp only [J15.gprod, Nat.mul_one] at htp
    by_cases h0 : tp < 100
    · exact ⟨0, 100, by omega, h0, F5900Shards.s2a2_0⟩
    exact ⟨100, 199, by omega, htp, F5900Shards.s2a2_1⟩⟩
  s3 := ⟨300, [(0, 18, 199)], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s3⟩
  s4 := ⟨300, [(0, 14, 61)], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s4⟩
  s5 := ⟨300, [], by norm_num, by decide, by decide,
    cov_one_j F5900Shards.s5⟩

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters.** -/
theorem covers_lower_bound_7_5900_native :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length := by
  have hC := caps_of_k16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (PS.covered_one K16.f0k) (PS.covered_one K16.f1k) (PS.covered_one K16.f2k)
    (PS.covered_one K16.f3k) (PS.covered_one K16.f4k) (PS.covered_one K16.f5k)
    (PS.covered_one PS.ring)
  have hF := profiles_of_k16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (PS.covered_one K16.f0k)
    (PS.covered_one PS.prof36) (PS.covered_one PS.prof26) (PS.covered_one PS.prof34)
    (PS.covered_one PS.prof14) (PS.covered_one PS.prof4)
  have hB := K5900.setB_of_k16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (PS.covered_one K16.f0k) (PS.covered_one K16.f1k) (PS.covered_one K16.f2k)
    (PS.covered_one K16.f3k) (PS.covered_one K16.f4k) (PS.covered_one K16.f5k)
    (PS.covered_one PS.ring)
  have hT := K5900.tableT_of_fast hB fastEvalsT_native fastEvalsK_native
  have hK := K5900.theoremK_of_fast hB fastEvalsT_native fastEvalsK_native
  have hJ := J5900.joint_of_fast hT hK fastJEvals_native
  exact covers_5900_of_caps hC hF hT hK hJ

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_lower_bound_7_5900_native
