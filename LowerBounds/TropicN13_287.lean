import LowerBounds.TropicL2Sound
import LowerBounds.TropicN13_287.CheckBasic
import LowerBounds.TropicN13_287.CheckForb1_0
import LowerBounds.TropicN13_287.CheckForb1_1
import LowerBounds.TropicN13_287.CheckForb1_2
import LowerBounds.TropicN13_287.CheckForb1_3
import LowerBounds.TropicN13_287.CheckCegar_0
import LowerBounds.TropicN13_287.CheckCegar_1
import LowerBounds.TropicN13_287.CheckCegar_2
import LowerBounds.TropicN13_287.CheckCegar_3
import LowerBounds.TropicN13_287.CheckCegar_4
import LowerBounds.TropicN13_287.CheckCegar_5
import LowerBounds.TropicN13_287.CheckCegar_6
import LowerBounds.TropicN13_287.CheckCegar_7
import LowerBounds.TropicN13_287.CheckSmall_0
import LowerBounds.TropicN13_287.CheckSmall_1
import LowerBounds.TropicN13_287.CheckSmall_2
import LowerBounds.TropicN13_287.CheckSmall_3
import LowerBounds.TropicN13_287.CheckStates_0
import LowerBounds.TropicN13_287.CheckStates_1
import LowerBounds.TropicN13_287.CheckStates_2
import LowerBounds.TropicN13_287.CheckStates_3
import LowerBounds.TropicN13_287.CheckStates_4
import LowerBounds.TropicN13_287.CheckStates_5
import LowerBounds.TropicN13_287.CheckStates_6
import LowerBounds.TropicN13_287.CheckStates_7
import LowerBounds.TropicN13_287.CheckStates_8
import LowerBounds.TropicN13_287.CheckStates_9
import LowerBounds.TropicN13_287.CheckStates_10
import LowerBounds.TropicN13_287.CheckStates_11
import LowerBounds.TropicN13_287.CheckStates_12
import LowerBounds.TropicN13_287.CheckStates_13
import LowerBounds.TropicN13_287.CheckStates_14
import LowerBounds.TropicN13_287.CheckStates_15
import LowerBounds.TropicN13_287.CheckStates_16
import LowerBounds.TropicN13_287.CheckStates_17
import LowerBounds.TropicN13_287.CheckStates_18
import LowerBounds.TropicN13_287.CheckStates_19
import LowerBounds.TropicN13_287.CheckStates_20
import LowerBounds.TropicN13_287.CheckStates_21
import LowerBounds.TropicN13_287.CheckStates_22
import LowerBounds.TropicN13_287.CheckStates_23
import LowerBounds.TropicN13_287.CheckStates_24
import LowerBounds.TropicN13_287.CheckStates_25
import LowerBounds.TropicN13_287.CheckStates_26
import LowerBounds.TropicN13_287.CheckStates_27
import LowerBounds.TropicN13_287.CheckStates_28
import LowerBounds.TropicN13_287.CheckStates_29
import LowerBounds.TropicN13_287.CheckStates_30
import LowerBounds.TropicN13_287.CheckStates_31
import LowerBounds.TropicN13_287.CheckStates_32
import LowerBounds.TropicN13_287.CheckStates_33
import LowerBounds.TropicN13_287.CheckStates_34
import LowerBounds.TropicN13_287.CheckStates_35
import LowerBounds.TropicN13_287.CheckStates_36
import LowerBounds.TropicN13_287.CheckStates_37
import LowerBounds.TropicN13_287.CheckStates_38
import LowerBounds.TropicN13_287.CheckStates_39
import LowerBounds.TropicN13_287.CheckStates_40
import LowerBounds.TropicN13_287.CheckStates_41
import LowerBounds.TropicN13_287.CheckStates_42
import LowerBounds.TropicN13_287.CheckStates_43
import LowerBounds.TropicN13_287.CheckStates_44
import LowerBounds.TropicN13_287.CheckStates_45
import LowerBounds.TropicN13_287.CheckStates_46
import LowerBounds.TropicN13_287.CheckStates_47
import LowerBounds.TropicN13_287.CheckStates_48
import LowerBounds.TropicN13_287.CheckStates_49
import LowerBounds.TropicN13_287.CheckStates_50
import LowerBounds.TropicN13_287.CheckStates_51
import LowerBounds.TropicN13_287.CheckStates_52
import LowerBounds.TropicN13_287.CheckStates_53
import LowerBounds.TropicN13_287.CheckStates_54
import LowerBounds.TropicN13_287.CheckStates_55
import LowerBounds.TropicN13_287.CheckStates_56
import LowerBounds.TropicN13_287.CheckStates_57
import LowerBounds.TropicN13_287.CheckStates_58
import LowerBounds.TropicN13_287.CheckStates_59
import LowerBounds.TropicN13_287.CheckStates_60
import LowerBounds.TropicN13_287.CheckStates_61
import LowerBounds.TropicN13_287.CheckStates_62
import LowerBounds.TropicN13_287.CheckStates_63

namespace SuperpermLowerBounds.TropicL2.N13_287

open SuperpermutationBounds ChainC

private theorem cert_valid : L2CertValid cert where
  hD1 := by decide
  hD11 := by decide
  hR1 := by decide
  hq := by decide
  hcn := by decide
  hA := by decide
  hAlive := by decide
  hAliveBound := by decide
  hBpeGe := by decide
  hbase := chk_base
  halpha1 := fun m hm d hd t ht => by
    have hd3 : d ≤ 3 := hd
    exact checkRangeAux_spec (checkRangeAux_spec (checkRangeAux_spec chk_alpha1 m (Nat.zero_le _) (by omega)) d (Nat.zero_le _) (by omega)) t (Nat.zero_le _) (by omega)
  hl1Elem := fun s1 hs => checkRangeChunked_spec chk_l1Elem s1 (Nat.zero_le _) hs
  hforb1 := fun a ha => by
    have ha' : a < 144 := ha
    by_cases h0 : a < 36
    · exact checkRangeChunked_spec chk_forb1_0 a (by omega) (by omega)
    by_cases h1 : a < 72
    · exact checkRangeChunked_spec chk_forb1_1 a (by omega) (by omega)
    by_cases h2 : a < 108
    · exact checkRangeChunked_spec chk_forb1_2 a (by omega) (by omega)
    exact checkRangeChunked_spec chk_forb1_3 a (by omega) (by omega)
  hl2Single := fun r hr s1 hs => by
    have hr7 : r ≤ 7 := hr
    exact checkRangeChunked_spec (checkRangeAux_spec chk_l2Single r (Nat.zero_le _) (by omega)) s1 (Nat.zero_le _) hs
  hbpe := fun t ht => checkRangeChunked_spec chk_bpe t (Nat.zero_le _) ht
  hcegarWit := fun fid hfid => by
    have hfid' : fid < 3283 := hfid
    by_cases h0 : fid < 410
    · exact checkRangeChunked_spec chk_cegarWit_0 fid (by omega) (by omega)
    by_cases h1 : fid < 820
    · exact checkRangeChunked_spec chk_cegarWit_1 fid (by omega) (by omega)
    by_cases h2 : fid < 1231
    · exact checkRangeChunked_spec chk_cegarWit_2 fid (by omega) (by omega)
    by_cases h3 : fid < 1641
    · exact checkRangeChunked_spec chk_cegarWit_3 fid (by omega) (by omega)
    by_cases h4 : fid < 2051
    · exact checkRangeChunked_spec chk_cegarWit_4 fid (by omega) (by omega)
    by_cases h5 : fid < 2462
    · exact checkRangeChunked_spec chk_cegarWit_5 fid (by omega) (by omega)
    by_cases h6 : fid < 2872
    · exact checkRangeChunked_spec chk_cegarWit_6 fid (by omega) (by omega)
    exact checkRangeChunked_spec chk_cegarWit_7 fid (by omega) (by omega)
  hcegarLeaf := fun fid hfid => by
    have hfid' : fid < 3283 := hfid
    by_cases h0 : fid < 410
    · exact checkRangeChunked_spec chk_cegarLeaf_0 fid (by omega) (by omega)
    by_cases h1 : fid < 820
    · exact checkRangeChunked_spec chk_cegarLeaf_1 fid (by omega) (by omega)
    by_cases h2 : fid < 1231
    · exact checkRangeChunked_spec chk_cegarLeaf_2 fid (by omega) (by omega)
    by_cases h3 : fid < 1641
    · exact checkRangeChunked_spec chk_cegarLeaf_3 fid (by omega) (by omega)
    by_cases h4 : fid < 2051
    · exact checkRangeChunked_spec chk_cegarLeaf_4 fid (by omega) (by omega)
    by_cases h5 : fid < 2462
    · exact checkRangeChunked_spec chk_cegarLeaf_5 fid (by omega) (by omega)
    by_cases h6 : fid < 2872
    · exact checkRangeChunked_spec chk_cegarLeaf_6 fid (by omega) (by omega)
    exact checkRangeChunked_spec chk_cegarLeaf_7 fid (by omega) (by omega)
  hroot := chk_root
  hpair := fun pi hpi => checkRangeAux_spec chk_pair pi (Nat.zero_le _) hpi
  hrootS1 := fun s1 hs => by
    have hs' : s1 < 144 := hs
    by_cases h0 : s1 < 36
    · exact checkRangeChunked_spec chk_rootS1_0 s1 (by omega) (by omega)
    by_cases h1 : s1 < 72
    · exact checkRangeChunked_spec chk_rootS1_1 s1 (by omega) (by omega)
    by_cases h2 : s1 < 108
    · exact checkRangeChunked_spec chk_rootS1_2 s1 (by omega) (by omega)
    exact checkRangeChunked_spec chk_rootS1_3 s1 (by omega) (by omega)
  hmaxTr := fun li hli => checkRangeAux_spec chk_maxTr li (Nat.zero_le _) hli
  htrie := fun u hu1 hu => by
    have hu' : u < 573189 := hu
    by_cases h0 : u < 8957
    · exact checkRangeChunked_spec chk_states_0 u (by omega) (by omega)
    by_cases h1 : u < 17913
    · exact checkRangeChunked_spec chk_states_1 u (by omega) (by omega)
    by_cases h2 : u < 26869
    · exact checkRangeChunked_spec chk_states_2 u (by omega) (by omega)
    by_cases h3 : u < 35825
    · exact checkRangeChunked_spec chk_states_3 u (by omega) (by omega)
    by_cases h4 : u < 44781
    · exact checkRangeChunked_spec chk_states_4 u (by omega) (by omega)
    by_cases h5 : u < 53737
    · exact checkRangeChunked_spec chk_states_5 u (by omega) (by omega)
    by_cases h6 : u < 62693
    · exact checkRangeChunked_spec chk_states_6 u (by omega) (by omega)
    by_cases h7 : u < 71649
    · exact checkRangeChunked_spec chk_states_7 u (by omega) (by omega)
    by_cases h8 : u < 80605
    · exact checkRangeChunked_spec chk_states_8 u (by omega) (by omega)
    by_cases h9 : u < 89561
    · exact checkRangeChunked_spec chk_states_9 u (by omega) (by omega)
    by_cases h10 : u < 98517
    · exact checkRangeChunked_spec chk_states_10 u (by omega) (by omega)
    by_cases h11 : u < 107473
    · exact checkRangeChunked_spec chk_states_11 u (by omega) (by omega)
    by_cases h12 : u < 116429
    · exact checkRangeChunked_spec chk_states_12 u (by omega) (by omega)
    by_cases h13 : u < 125385
    · exact checkRangeChunked_spec chk_states_13 u (by omega) (by omega)
    by_cases h14 : u < 134341
    · exact checkRangeChunked_spec chk_states_14 u (by omega) (by omega)
    by_cases h15 : u < 143298
    · exact checkRangeChunked_spec chk_states_15 u (by omega) (by omega)
    by_cases h16 : u < 152254
    · exact checkRangeChunked_spec chk_states_16 u (by omega) (by omega)
    by_cases h17 : u < 161210
    · exact checkRangeChunked_spec chk_states_17 u (by omega) (by omega)
    by_cases h18 : u < 170166
    · exact checkRangeChunked_spec chk_states_18 u (by omega) (by omega)
    by_cases h19 : u < 179122
    · exact checkRangeChunked_spec chk_states_19 u (by omega) (by omega)
    by_cases h20 : u < 188078
    · exact checkRangeChunked_spec chk_states_20 u (by omega) (by omega)
    by_cases h21 : u < 197034
    · exact checkRangeChunked_spec chk_states_21 u (by omega) (by omega)
    by_cases h22 : u < 205990
    · exact checkRangeChunked_spec chk_states_22 u (by omega) (by omega)
    by_cases h23 : u < 214946
    · exact checkRangeChunked_spec chk_states_23 u (by omega) (by omega)
    by_cases h24 : u < 223902
    · exact checkRangeChunked_spec chk_states_24 u (by omega) (by omega)
    by_cases h25 : u < 232858
    · exact checkRangeChunked_spec chk_states_25 u (by omega) (by omega)
    by_cases h26 : u < 241814
    · exact checkRangeChunked_spec chk_states_26 u (by omega) (by omega)
    by_cases h27 : u < 250770
    · exact checkRangeChunked_spec chk_states_27 u (by omega) (by omega)
    by_cases h28 : u < 259726
    · exact checkRangeChunked_spec chk_states_28 u (by omega) (by omega)
    by_cases h29 : u < 268682
    · exact checkRangeChunked_spec chk_states_29 u (by omega) (by omega)
    by_cases h30 : u < 277638
    · exact checkRangeChunked_spec chk_states_30 u (by omega) (by omega)
    by_cases h31 : u < 286595
    · exact checkRangeChunked_spec chk_states_31 u (by omega) (by omega)
    by_cases h32 : u < 295551
    · exact checkRangeChunked_spec chk_states_32 u (by omega) (by omega)
    by_cases h33 : u < 304507
    · exact checkRangeChunked_spec chk_states_33 u (by omega) (by omega)
    by_cases h34 : u < 313463
    · exact checkRangeChunked_spec chk_states_34 u (by omega) (by omega)
    by_cases h35 : u < 322419
    · exact checkRangeChunked_spec chk_states_35 u (by omega) (by omega)
    by_cases h36 : u < 331375
    · exact checkRangeChunked_spec chk_states_36 u (by omega) (by omega)
    by_cases h37 : u < 340331
    · exact checkRangeChunked_spec chk_states_37 u (by omega) (by omega)
    by_cases h38 : u < 349287
    · exact checkRangeChunked_spec chk_states_38 u (by omega) (by omega)
    by_cases h39 : u < 358243
    · exact checkRangeChunked_spec chk_states_39 u (by omega) (by omega)
    by_cases h40 : u < 367199
    · exact checkRangeChunked_spec chk_states_40 u (by omega) (by omega)
    by_cases h41 : u < 376155
    · exact checkRangeChunked_spec chk_states_41 u (by omega) (by omega)
    by_cases h42 : u < 385111
    · exact checkRangeChunked_spec chk_states_42 u (by omega) (by omega)
    by_cases h43 : u < 394067
    · exact checkRangeChunked_spec chk_states_43 u (by omega) (by omega)
    by_cases h44 : u < 403023
    · exact checkRangeChunked_spec chk_states_44 u (by omega) (by omega)
    by_cases h45 : u < 411979
    · exact checkRangeChunked_spec chk_states_45 u (by omega) (by omega)
    by_cases h46 : u < 420935
    · exact checkRangeChunked_spec chk_states_46 u (by omega) (by omega)
    by_cases h47 : u < 429892
    · exact checkRangeChunked_spec chk_states_47 u (by omega) (by omega)
    by_cases h48 : u < 438848
    · exact checkRangeChunked_spec chk_states_48 u (by omega) (by omega)
    by_cases h49 : u < 447804
    · exact checkRangeChunked_spec chk_states_49 u (by omega) (by omega)
    by_cases h50 : u < 456760
    · exact checkRangeChunked_spec chk_states_50 u (by omega) (by omega)
    by_cases h51 : u < 465716
    · exact checkRangeChunked_spec chk_states_51 u (by omega) (by omega)
    by_cases h52 : u < 474672
    · exact checkRangeChunked_spec chk_states_52 u (by omega) (by omega)
    by_cases h53 : u < 483628
    · exact checkRangeChunked_spec chk_states_53 u (by omega) (by omega)
    by_cases h54 : u < 492584
    · exact checkRangeChunked_spec chk_states_54 u (by omega) (by omega)
    by_cases h55 : u < 501540
    · exact checkRangeChunked_spec chk_states_55 u (by omega) (by omega)
    by_cases h56 : u < 510496
    · exact checkRangeChunked_spec chk_states_56 u (by omega) (by omega)
    by_cases h57 : u < 519452
    · exact checkRangeChunked_spec chk_states_57 u (by omega) (by omega)
    by_cases h58 : u < 528408
    · exact checkRangeChunked_spec chk_states_58 u (by omega) (by omega)
    by_cases h59 : u < 537364
    · exact checkRangeChunked_spec chk_states_59 u (by omega) (by omega)
    by_cases h60 : u < 546320
    · exact checkRangeChunked_spec chk_states_60 u (by omega) (by omega)
    by_cases h61 : u < 555276
    · exact checkRangeChunked_spec chk_states_61 u (by omega) (by omega)
    by_cases h62 : u < 564232
    · exact checkRangeChunked_spec chk_states_62 u (by omega) (by omega)
    exact checkRangeChunked_spec chk_states_63 u (by omega) (by omega)

private theorem condC : ConditionsC 13 1474 68966 8953 :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem boundC_eq : boundC 13 1474 68966 8953 = 6746627287 := by
  decide +kernel

/-- **World Record (`S(13) >= 6,746,627,287`)**, verified 100% purely by the Lean kernel. -/
theorem covers_length_ge_6746627287 :
    ∀ w : List (Fin 13), Covers w → 6746627287 ≤ w.length := by
  have hcn : cert.cn = 1474 := rfl
  have hbn : cert.bn = 68966 := rfl
  have hq : cert.q = 8953 := rfl
  have hc : ConditionsC 13 cert.cn cert.bn cert.q := by rw [hcn, hbn, hq]; exact condC
  have h := covers_length_ge_boundC_of_tropicL2 cert_valid hc
  rw [hcn, hbn, hq, boundC_eq] at h
  exact h

end SuperpermLowerBounds.TropicL2.N13_287
