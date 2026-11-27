import LowerBounds.U3Sound
import LowerBounds.K16Rules

/-!
# Complete Soundness Proof for `FastK16Search` (`Rule JS` + `M3` + `W4` + `U3Fwd`)

Proves `seqCap_of_fastK16`: if all parts `tp < nt` of `FastK16.seqSearch` return `false`
(under the monotonicity hypotheses for `M3`/`W4` when enabled, and lightweight table-size
bounds), then `PS.SeqCapLt 7 s (PS.capF caps s) (hi + 1)` holds!

Zero `sorry`, zero extra axioms (`[propext, Classical.choice, Quot.sound]` only).
-/

namespace SuperpermLowerBounds
namespace FastK16Sound

open S (PermW WLink DoorEq Sub)
open PS (TRow Enc MInv LinkK PCont IsSeq holesT linksT SeqCapLt capF relabSeq encB ciTab nxtTab)
open KS (codeF potN potS cutF a1F a2F uF segF Good fK RuleK KAlong rowsR maxLeN tabA tab2 look2
  codeT maskG big)
open K16 (NoJS NoJSAlong noJSAlong_of_noJS noJSAlong_relab tau2 permW_tau2 shift_of_not_noJS psi_le)
open FastK16 (FastK16Ctx buildS7K16Tabs buildM3Allow buildW4Allow buildU3MinR buildProblem
  runPart seqSearch go loopSucc walkGo idx3 getCode getMask checkCut packMM unpackM unpackMax
  baGetU8 baSetU8 baGetU16 baGetI64 packU16Arr packI64Arr)
open FastSound

/-! ### Bit-Packing Lemmas for `UInt64` State & `mM` -/

theorem packMM_unpack (m M : Int32) :
    unpackM (packMM m M) = m ∧ unpackMax (packMM m M) = M := by
  unfold packMM unpackM unpackMax
  constructor
  · apply Int32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [UInt32.toBitVec_toInt32, UInt64.toBitVec_toUInt32, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_or]
    change (decide (j < 32) &&
        ((decide (j < 64) && m.toUInt32.toBitVec.getLsbD j) ||
         ((M.toUInt32.toBitVec.setWidth 64) <<< (32 : BitVec 64).toNat).getLsbD j)) =
      m.toBitVec.getLsbD j
    rw [BitVec.getLsbD_shiftLeft]
    have hlt32 : j < 32 := hj
    have hlt64 : j < 64 := by omega
    simp [hlt32, hlt64]
  · apply Int32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [UInt32.toBitVec_toInt32, UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64,
      BitVec.getLsbD_setWidth]
    change (decide (j < 32) &&
        ((m.toUInt32.toBitVec.setWidth 64 |||
          (M.toUInt32.toBitVec.setWidth 64) <<< (32 : BitVec 64).toNat) >>>
          (32 : BitVec 64).toNat).getLsbD j) = M.toBitVec.getLsbD j
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have h32 : (32 : BitVec 64).toNat = 32 := rfl
    rw [h32]
    have hlt64 : 32 + j < 64 := by omega
    have hnlt : ¬ 32 + j < 32 := by omega
    have hsub : 32 + j - 32 = j := by omega
    simp [hj, hlt64, hnlt, hsub]
    intro _; omega

/-- Canonical packed 64-bit state for `go`. -/
def mkState (q d r t w3 s1 s2 : ℕ) : UInt64 :=
  (UInt32.ofNat q).toUInt64 |||
  ((UInt32.ofNat d).toUInt64 <<< 13) |||
  ((UInt32.ofNat r).toUInt64 <<< 21) |||
  ((UInt32.ofNat t).toUInt64 <<< 29) |||
  ((UInt32.ofNat w3).toUInt64 <<< 33) |||
  ((UInt32.ofNat s1).toUInt64 <<< 35) |||
  ((UInt32.ofNat s2).toUInt64 <<< 38)

/-- Canonical packed `baseSt` passed to `loopSucc` / `walkGo`. -/
def mkBaseSt (d nr nt nw3 s1 s2 t3c : ℕ) : UInt64 :=
  ((UInt32.ofNat d).toUInt64 <<< 13) |||
  ((UInt32.ofNat nr).toUInt64 <<< 21) |||
  ((UInt32.ofNat nt).toUInt64 <<< 29) |||
  ((UInt32.ofNat nw3).toUInt64 <<< 33) |||
  ((UInt32.ofNat s1).toUInt64 <<< 35) |||
  ((UInt32.ofNat s2).toUInt64 <<< 38) |||
  ((UInt32.ofNat t3c).toUInt64 <<< 46)

/-- Canonical packed `lArg` passed to `loopSucc`. -/
def mkLArg (lim mk cq : ℕ) (isS4 : Bool) : UInt64 :=
  ((UInt64.ofNat lim) <<< 5) |||
  ((UInt32.ofNat mk).toUInt64 <<< 10) |||
  ((UInt32.ofNat cq).toUInt64 <<< 16) |||
  (if isS4 then (1 : UInt64) <<< 29 else 0)

private theorem u64_field_getLsbD {val w : ℕ} {sh : UInt64} (hval : val < 2 ^ w) (hw : w ≤ 32)
    (hsh64 : sh.toNat < 64) (hsh : sh.toNat + w ≤ 64) (j : ℕ) (hj : j < 64) :
    ((UInt32.ofNat val).toUInt64 <<< sh).toBitVec.getLsbD j =
      (decide (sh.toNat ≤ j ∧ j < sh.toNat + w) && Nat.testBit val (j - sh.toNat)) := by
  have hsh_mod : (sh.toBitVec % 64).toNat = sh.toNat := by
    rw [BitVec.toNat_umod]; change sh.toNat % 64 = sh.toNat; exact Nat.mod_eq_of_lt hsh64
  rw [UInt64.toBitVec_shiftLeft]
  change ((UInt32.ofNat val).toUInt64.toBitVec <<< (sh.toBitVec % 64).toNat).getLsbD j = _
  rw [hsh_mod, BitVec.getLsbD_shiftLeft]
  simp only [hj, decide_true, Bool.true_and]
  by_cases hge : sh.toNat ≤ j
  · have hnlt : ¬ j < sh.toNat := by omega
    simp only [hnlt, decide_false, Bool.not_false, Bool.true_and]
    rw [UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
    have hbv : (UInt32.ofNat val).toBitVec.getLsbD (j - sh.toNat) =
        (decide (j - sh.toNat < 32) && Nat.testBit val (j - sh.toNat)) := by
      change (BitVec.ofNat 32 val).getLsbD (j - sh.toNat) = _
      exact BitVec.getLsbD_ofNat 32 val (j - sh.toNat)
    rw [hbv]
    by_cases hlt : j < sh.toNat + w
    · simp [hge, hlt, show j - sh.toNat < 64 by omega, show j - sh.toNat < 32 by omega]
    · have hfalse : Nat.testBit val (j - sh.toNat) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have : val < 2 ^ (j - sh.toNat) := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.div_eq_of_lt this]; rfl
      simp [hge, hlt, hfalse]
  · simp [show j < sh.toNat by omega, hge]

private theorem testBit_add_mul_pow (a b k j : ℕ) (hak : a < 2 ^ k) :
    Nat.testBit (a + b * 2 ^ k) j = if j < k then Nat.testBit a j else Nat.testBit b (j - k) := by
  rw [Nat.testBit, Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  by_cases hjk : j < k
  · rw [if_pos hjk]
    have hk : b * 2 ^ k = (b * 2 ^ (k - j)) * 2 ^ j := by
      have : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      rw [this, Nat.mul_assoc]
    rw [hk, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega))]
    have heven : 2 ∣ b * 2 ^ (k - j) := by
      have : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by rw [← Nat.pow_succ']; congr 1; omega
      rw [this]; exact ⟨b * 2 ^ (k - j - 1), by ring⟩
    obtain ⟨m, hm⟩ := heven
    rw [hm, Nat.and_comm, Nat.and_one_is_mod, Nat.and_comm, Nat.and_one_is_mod]
    have : (a / 2 ^ j + 2 * m) % 2 = (a / 2 ^ j) % 2 := by omega
    rw [this]
  · rw [if_neg hjk]
    have hjk' : 2 ^ j = 2 ^ k * 2 ^ (j - k) := by rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    rw [hjk', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)),
      Nat.div_eq_of_lt hak, Nat.zero_add]

-- Clean arithmetic representation of `mkState` and `mkBaseSt`!
theorem mkState_toNat {q d r t w3 s1 s2 : ℕ}
    (hq : q < 8192) (hd : d < 256) (hr : r < 256) (ht : t < 16)
    (hw3 : w3 < 4) (hs1 : s1 < 8) (hs2 : s2 < 256) :
    (mkState q d r t w3 s1 s2).toNat =
      q + d * 2 ^ 13 + r * 2 ^ 21 + t * 2 ^ 29 + w3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 := by
  have hbits : ∀ j < 64, (mkState q d r t w3 s1 s2).toBitVec.getLsbD j =
      (Nat.testBit (q + d * 2 ^ 13 + r * 2 ^ 21 + t * 2 ^ 29 + w3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38) j) := by
    intro j hj
    unfold mkState
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
    have h0 : (UInt32.ofNat q).toUInt64.toBitVec.getLsbD j = (decide (0 ≤ j ∧ j < 13) && Nat.testBit q (j - 0)) := by
      have := u64_field_getLsbD (val := q) (sh := (0 : UInt64)) (w := 13) hq (by omega) (by decide) (by decide) j hj
      simpa using this
    have h1 := u64_field_getLsbD (val := d) (sh := (13 : UInt64)) (w := 8) hd (by omega) (by decide) (by decide) j hj
    have h2 := u64_field_getLsbD (val := r) (sh := (21 : UInt64)) (w := 8) hr (by omega) (by decide) (by decide) j hj
    have h3 := u64_field_getLsbD (val := t) (sh := (29 : UInt64)) (w := 4) ht (by omega) (by decide) (by decide) j hj
    have h4 := u64_field_getLsbD (val := w3) (sh := (33 : UInt64)) (w := 2) hw3 (by omega) (by decide) (by decide) j hj
    have h5 := u64_field_getLsbD (val := s1) (sh := (35 : UInt64)) (w := 3) hs1 (by omega) (by decide) (by decide) j hj
    have h6 := u64_field_getLsbD (val := s2) (sh := (38 : UInt64)) (w := 8) hs2 (by omega) (by decide) (by decide) j hj
    rw [h0, h1, h2, h3, h4, h5, h6]
    simp only [show (13 : UInt64).toNat = 13 from rfl, show (21 : UInt64).toNat = 21 from rfl,
      show (29 : UInt64).toNat = 29 from rfl, show (33 : UInt64).toNat = 33 from rfl,
      show (35 : UInt64).toNat = 35 from rfl, show (38 : UInt64).toNat = 38 from rfl]
    rw [testBit_add_mul_pow _ s2 38 j (by omega), testBit_add_mul_pow _ s1 35 j (by omega),
      testBit_add_mul_pow _ w3 33 j (by omega), testBit_add_mul_pow _ t 29 j (by omega),
      testBit_add_mul_pow _ r 21 j (by omega), testBit_add_mul_pow _ d 13 j (by omega)]
    by_cases c0 : j < 13
    · simp [c0, show ¬ 13 ≤ j by omega, show ¬ 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
        show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega,
        show j < 21 by omega, show j < 29 by omega, show j < 33 by omega, show j < 35 by omega, show j < 38 by omega]
    · by_cases c1 : j < 21
      · simp [c0, c1, show 13 ≤ j by omega, show ¬ 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
          show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega,
          show j < 29 by omega, show j < 33 by omega, show j < 35 by omega, show j < 38 by omega]
      · by_cases c2 : j < 29
        · simp [c0, c1, c2, show 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
            show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega,
            show j < 33 by omega, show j < 35 by omega, show j < 38 by omega]
        · by_cases c3 : j < 33
          · simp [c0, c1, c2, c3, show 29 ≤ j by omega,
              show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega,
              show j < 35 by omega, show j < 38 by omega]
          · by_cases c4 : j < 35
            · simp [c0, c1, c2, c3, c4, show 33 ≤ j by omega,
                show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show j < 38 by omega]
            · by_cases c5 : j < 38
              · simp [c0, c1, c2, c3, c4, c5, show 35 ≤ j by omega, show ¬ 38 ≤ j by omega]
              · by_cases c6 : j < 46
                · simp [c0, c1, c2, c3, c4, c5, c6, show 38 ≤ j by omega]
                · have hfalse : Nat.testBit s2 (j - 38) = false := by
                    rw [Nat.testBit, Nat.shiftRight_eq_div_pow,
                      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (show s2 < 2 ^ 8 by omega) (Nat.pow_le_pow_right (by omega) (show 8 ≤ j - 38 by omega)))]; rfl
                  simp [c0, c1, c2, c3, c4, c5, c6, hfalse]
  have hbv : (mkState q d r t w3 s1 s2).toBitVec =
      BitVec.ofNat 64 (q + d * 2 ^ 13 + r * 2 ^ 21 + t * 2 ^ 29 + w3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [hbits j hj, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hlt : q + d * 2 ^ 13 + r * 2 ^ 21 + t * 2 ^ 29 + w3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 < 2 ^ 64 := by omega
  change (mkState q d r t w3 s1 s2).toBitVec.toNat = _
  rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem mkBaseSt_toNat {d nr nt nw3 s1 s2 t3c : ℕ}
    (hd : d < 256) (hr : nr < 256) (ht : nt < 16)
    (hw3 : nw3 < 4) (hs1 : s1 < 8) (hs2 : s2 < 256) (ht3 : t3c < 8) :
    (mkBaseSt d nr nt nw3 s1 s2 t3c).toNat =
      d * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 + t3c * 2 ^ 46 := by
  have hbits : ∀ j < 64, (mkBaseSt d nr nt nw3 s1 s2 t3c).toBitVec.getLsbD j =
      (Nat.testBit (d * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 + t3c * 2 ^ 46) j) := by
    intro j hj
    unfold mkBaseSt
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
    have h1 := u64_field_getLsbD (val := d) (sh := (13 : UInt64)) (w := 8) hd (by omega) (by decide) (by decide) j hj
    have h2 := u64_field_getLsbD (val := nr) (sh := (21 : UInt64)) (w := 8) hr (by omega) (by decide) (by decide) j hj
    have h3 := u64_field_getLsbD (val := nt) (sh := (29 : UInt64)) (w := 4) ht (by omega) (by decide) (by decide) j hj
    have h4 := u64_field_getLsbD (val := nw3) (sh := (33 : UInt64)) (w := 2) hw3 (by omega) (by decide) (by decide) j hj
    have h5 := u64_field_getLsbD (val := s1) (sh := (35 : UInt64)) (w := 3) hs1 (by omega) (by decide) (by decide) j hj
    have h6 := u64_field_getLsbD (val := s2) (sh := (38 : UInt64)) (w := 8) hs2 (by omega) (by decide) (by decide) j hj
    have h7 := u64_field_getLsbD (val := t3c) (sh := (46 : UInt64)) (w := 3) ht3 (by omega) (by decide) (by decide) j hj
    rw [h1, h2, h3, h4, h5, h6, h7]
    simp only [show (13 : UInt64).toNat = 13 from rfl, show (21 : UInt64).toNat = 21 from rfl,
      show (29 : UInt64).toNat = 29 from rfl, show (33 : UInt64).toNat = 33 from rfl,
      show (35 : UInt64).toNat = 35 from rfl, show (38 : UInt64).toNat = 38 from rfl,
      show (46 : UInt64).toNat = 46 from rfl]
    have htb0 : Nat.testBit (0 + d * 2 ^ 13) j = if j < 13 then false else Nat.testBit d (j - 13) := by
      rw [testBit_add_mul_pow 0 d 13 j (by omega), Nat.zero_testBit]
    rw [testBit_add_mul_pow _ t3c 46 j (by omega), testBit_add_mul_pow _ s2 38 j (by omega),
      testBit_add_mul_pow _ s1 35 j (by omega), testBit_add_mul_pow _ nw3 33 j (by omega),
      testBit_add_mul_pow _ nt 29 j (by omega), testBit_add_mul_pow _ nr 21 j (by omega),
      ← Nat.zero_add (d * 2 ^ 13), htb0]
    by_cases c0 : j < 13
    · simp [c0, show ¬ 13 ≤ j by omega, show ¬ 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
        show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show ¬ 46 ≤ j by omega,
        show j < 21 by omega, show j < 29 by omega, show j < 33 by omega, show j < 35 by omega,
        show j < 38 by omega, show j < 46 by omega]
    · by_cases c1 : j < 21
      · simp [c0, c1, show 13 ≤ j by omega, show ¬ 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
          show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show ¬ 46 ≤ j by omega,
          show j < 29 by omega, show j < 33 by omega, show j < 35 by omega, show j < 38 by omega, show j < 46 by omega]
      · by_cases c2 : j < 29
        · simp [c0, c1, c2, show 21 ≤ j by omega, show ¬ 29 ≤ j by omega,
            show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show ¬ 46 ≤ j by omega,
            show j < 33 by omega, show j < 35 by omega, show j < 38 by omega, show j < 46 by omega]
        · by_cases c3 : j < 33
          · simp [c0, c1, c2, c3, show 29 ≤ j by omega,
              show ¬ 33 ≤ j by omega, show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show ¬ 46 ≤ j by omega,
              show j < 35 by omega, show j < 38 by omega, show j < 46 by omega]
          · by_cases c4 : j < 35
            · simp [c0, c1, c2, c3, c4, show 33 ≤ j by omega,
                show ¬ 35 ≤ j by omega, show ¬ 38 ≤ j by omega, show ¬ 46 ≤ j by omega,
                show j < 38 by omega, show j < 46 by omega]
            · by_cases c5 : j < 38
              · simp [c0, c1, c2, c3, c4, c5, show 35 ≤ j by omega, show ¬ 38 ≤ j by omega,
                  show ¬ 46 ≤ j by omega, show j < 46 by omega]
              · by_cases c6 : j < 46
                · simp [c0, c1, c2, c3, c4, c5, c6, show 38 ≤ j by omega, show ¬ 46 ≤ j by omega]
                · by_cases c7 : j < 49
                  · simp [c0, c1, c2, c3, c4, c5, c6, c7, show 46 ≤ j by omega]
                  · have hfalse : Nat.testBit t3c (j - 46) = false := by
                      rw [Nat.testBit, Nat.shiftRight_eq_div_pow,
                        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (show t3c < 2 ^ 3 by omega) (Nat.pow_le_pow_right (by omega) (show 3 ≤ j - 46 by omega)))]; rfl
                    simp [c0, c1, c2, c3, c4, c5, c6, c7, hfalse]
  have hbv : (mkBaseSt d nr nt nw3 s1 s2 t3c).toBitVec =
      BitVec.ofNat 64 (d * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 + t3c * 2 ^ 46) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [hbits j hj, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hlt : d * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 + s1 * 2 ^ 35 + s2 * 2 ^ 38 + t3c * 2 ^ 46 < 2 ^ 64 := by omega
  change (mkBaseSt d nr nt nw3 s1 s2 t3c).toBitVec.toNat = _
  rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem mkLArg_toNat {lim mk cq : ℕ} {isS4 : Bool} (hlim : lim < 32) (hmk : mk < 64) (hcq : cq < 8192) :
    (mkLArg lim mk cq isS4).toNat = lim * 2 ^ 5 + mk * 2 ^ 10 + cq * 2 ^ 16 + (if isS4 then 2 ^ 29 else 0) := by
  have hbits : ∀ j < 64, (mkLArg lim mk cq isS4).toBitVec.getLsbD j =
      Nat.testBit (lim * 2 ^ 5 + mk * 2 ^ 10 + cq * 2 ^ 16 + (if isS4 then 2 ^ 29 else 0)) j := by
    intro j hj
    unfold mkLArg
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
    have h0 : (UInt64.ofNat lim <<< 5).toBitVec.getLsbD j = (decide (5 ≤ j ∧ j < 10) && Nat.testBit lim (j - 5)) := by
      have : UInt64.ofNat lim = (UInt32.ofNat lim).toUInt64 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_ofNat', UInt32.toNat_toUInt64, UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega : lim < 2 ^ 64), Nat.mod_eq_of_lt (by omega : lim < 2 ^ 32)]
      rw [this]
      exact u64_field_getLsbD (sh := (5 : UInt64)) (w := 5) hlim (by omega) (by decide) (by decide) j hj
    have h1 := u64_field_getLsbD (val := mk) (sh := (10 : UInt64)) (w := 6) hmk (by omega) (by decide) (by decide) j hj
    have h2 := u64_field_getLsbD (val := cq) (sh := (16 : UInt64)) (w := 13) hcq (by omega) (by decide) (by decide) j hj
    have h3 : (if isS4 = true then (1 : UInt64) <<< 29 else 0).toBitVec.getLsbD j =
        (decide (29 ≤ j ∧ j < 30) && Nat.testBit (if isS4 then 1 else 0) (j - 29)) := by
      cases isS4
      · simp
      · have : (1 : UInt64) = (UInt32.ofNat 1).toUInt64 := rfl
        rw [if_pos rfl, this]
        exact u64_field_getLsbD (val := 1) (sh := (29 : UInt64)) (w := 1) (by omega) (by omega) (by decide) (by decide) j hj
    rw [h0, h1, h2, h3]
    simp only [show (10 : UInt64).toNat = 10 from rfl, show (16 : UInt64).toNat = 16 from rfl]
    have hs4 : (if isS4 = true then 2 ^ 29 else 0) = (if isS4 then 1 else 0) * 2 ^ 29 := by cases isS4 <;> simp
    rw [hs4, testBit_add_mul_pow _ _ 29 j (by omega), testBit_add_mul_pow _ _ 16 j (by omega),
      testBit_add_mul_pow _ _ 10 j (by omega), ← Nat.zero_add (lim * 2 ^ 5),
      testBit_add_mul_pow 0 lim 5 j (by omega), Nat.zero_testBit]
    by_cases c0 : j < 5
    · simp [c0, show ¬ 5 ≤ j by omega, show ¬ 10 ≤ j by omega, show ¬ 16 ≤ j by omega, show ¬ 29 ≤ j by omega,
        show j < 10 by omega, show j < 16 by omega, show j < 29 by omega]
    · by_cases c1 : j < 10
      · simp [c0, c1, show 5 ≤ j by omega, show ¬ 10 ≤ j by omega, show ¬ 16 ≤ j by omega, show ¬ 29 ≤ j by omega,
          show j < 16 by omega, show j < 29 by omega]
      · by_cases c2 : j < 16
        · simp [c0, c1, c2, show 10 ≤ j by omega, show ¬ 16 ≤ j by omega, show ¬ 29 ≤ j by omega,
            show j < 29 by omega]
        · by_cases c3 : j < 29
          · simp [c0, c1, c2, c3, show 16 ≤ j by omega, show ¬ 29 ≤ j by omega]
          · by_cases c4 : j < 30
            · simp [c0, c1, c2, c3, c4, show 29 ≤ j by omega]
            · have hfalse : Nat.testBit (if isS4 then 1 else 0) (j - 29) = false := by
                rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
                have : (if isS4 then 1 else 0) < 2 ^ (j - 29) := by
                  have h2 : 2 ≤ 2 ^ (j - 29) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by omega) (show 1 ≤ j - 29 by omega))
                  cases isS4 <;> simp <;> omega
                rw [Nat.div_eq_of_lt this]; rfl
              simp [c1, c2, c3, c4, hfalse]
  have hbv : (mkLArg lim mk cq isS4).toBitVec =
      BitVec.ofNat 64 (lim * 2 ^ 5 + mk * 2 ^ 10 + cq * 2 ^ 16 + (if isS4 then 2 ^ 29 else 0)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [hbits j hj, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hlt : lim * 2 ^ 5 + mk * 2 ^ 10 + cq * 2 ^ 16 + (if isS4 then 2 ^ 29 else 0) < 2 ^ 64 := by
    cases isS4 <;> simp <;> omega
  change (mkLArg lim mk cq isS4).toBitVec.toNat = _
  rw [hbv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem u64_shift_mask_toUInt32 (x sh m : UInt64) {shN k : ℕ} (hshN : sh.toNat = shN)
    (hsh : shN < 64) (hm : m.toNat = 2 ^ k - 1) (_hk : k ≤ 32) :
    ((x >>> sh) &&& m).toUInt32 =
      UInt32.ofNat ((x.toNat / 2 ^ shN) % 2 ^ k) := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_and, UInt64.toNat_shiftRight, hshN,
    Nat.mod_eq_of_lt hsh, Nat.shiftRight_eq_div_pow, hm, Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_ofNat']

theorem mkState_unpack {q d r t w3 s1 s2 : ℕ}
    (hq : q < 8192) (hd : d < 256) (hr : r < 256) (ht : t < 16)
    (hw3 : w3 < 4) (hs1 : s1 < 8) (hs2 : s2 < 256) :
    let st := mkState q d r t w3 s1 s2
    (st &&& 8191).toUInt32 = UInt32.ofNat q ∧
    ((st >>> 13) &&& 255).toUInt32 = UInt32.ofNat d ∧
    ((st >>> 21) &&& 255).toUInt32 = UInt32.ofNat r ∧
    ((st >>> 29) &&& 15).toUInt32 = UInt32.ofNat t ∧
    ((st >>> 33) &&& 3).toUInt32 = UInt32.ofNat w3 ∧
    ((st >>> 35) &&& 7).toUInt32 = UInt32.ofNat s1 ∧
    ((st >>> 38) &&& 255).toUInt32 = UInt32.ofNat s2 := by
  have hnat := mkState_toNat hq hd hr ht hw3 hs1 hs2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := u64_shift_mask_toUInt32 (mkState q d r t w3 s1 s2) 0 8191 (shN := 0) rfl (by omega) (k := 13) rfl (by omega)
    have h0 : mkState q d r t w3 s1 s2 >>> 0 = mkState q d r t w3 s1 s2 := by
      apply UInt64.toNat_inj.mp; simp
    rw [h0] at h
    rw [h, hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 13 255 (shN := 13) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 21 255 (shN := 21) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 29 15 (shN := 29) rfl (by omega) (k := 4) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 33 3 (shN := 33) rfl (by omega) (k := 2) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 35 7 (shN := 35) rfl (by omega) (k := 3) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 38 255 (shN := 38) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega

theorem mkBaseSt_unpack {d nr nt nw3 s1 s2 t3c : ℕ}
    (hd : d < 256) (hr : nr < 256) (ht : nt < 16)
    (hw3 : nw3 < 4) (hs1 : s1 < 8) (hs2 : s2 < 256) (ht3 : t3c < 8) :
    let bst := mkBaseSt d nr nt nw3 s1 s2 t3c
    ((bst >>> 13) &&& 255).toUInt32 = UInt32.ofNat d ∧
    ((bst >>> 21) &&& 255).toUInt32 = UInt32.ofNat nr ∧
    ((bst >>> 29) &&& 15).toUInt32 = UInt32.ofNat nt ∧
    ((bst >>> 33) &&& 3).toUInt32 = UInt32.ofNat nw3 ∧
    ((bst >>> 35) &&& 7).toUInt32 = UInt32.ofNat s1 ∧
    ((bst >>> 38) &&& 255).toUInt32 = UInt32.ofNat s2 ∧
    ((bst >>> 46) &&& 7).toUInt32 = UInt32.ofNat t3c := by
  have hnat := mkBaseSt_toNat hd hr ht hw3 hs1 hs2 ht3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u64_shift_mask_toUInt32 _ 13 255 (shN := 13) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 21 255 (shN := 21) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 29 15 (shN := 29) rfl (by omega) (k := 4) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 33 3 (shN := 33) rfl (by omega) (k := 2) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 35 7 (shN := 35) rfl (by omega) (k := 3) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 38 255 (shN := 38) rfl (by omega) (k := 8) rfl (by omega), hnat]; congr 1; omega
  · rw [u64_shift_mask_toUInt32 _ 46 7 (shN := 46) rfl (by omega) (k := 3) rfl (by omega), hnat]; congr 1; omega

theorem mkBaseSt_nextState {d nr nt nw3 s1 s2 t3c n D ns1 nextS2 : ℕ}
    (hdn : d + n < 256) (hr : nr < 256) (ht : nt < 16)
    (hw3 : nw3 < 4) (hs1 : s1 < 8) (hs2 : s2 < 256) (ht3 : t3c < 8)
    (hD : D < 8192) (hns1 : ns1 < 8) (hns2 : nextS2 < 256) :
    let bst := mkBaseSt d nr nt nw3 s1 s2 t3c
    let lowBits := (bst &&& (34359738367 : UInt64)) + ((UInt32.ofNat n).toUInt64 <<< 13)
    lowBits ||| (UInt32.ofNat D).toUInt64 ||| ((UInt32.ofNat ns1).toUInt64 <<< 35) |||
      ((UInt32.ofNat nextS2).toUInt64 <<< 38) =
      mkState D (d + n) nr nt nw3 ns1 nextS2 := by
  have hbn := mkBaseSt_toNat (by omega : d < 256) hr ht hw3 hs1 hs2 ht3
  have hlow_and : (mkBaseSt d nr nt nw3 s1 s2 t3c &&& (34359738367 : UInt64)).toNat =
      d * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 := by
    rw [UInt64.toNat_and, hbn]
    have hmask : (34359738367 : UInt64).toNat = 2 ^ 35 - 1 := by decide
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hnsh : ((UInt32.ofNat n).toUInt64 <<< 13).toNat = n * 2 ^ 13 := by
    rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
    change (n <<< 13) % 2 ^ 64 = n * 2 ^ 13
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hlow : ((mkBaseSt d nr nt nw3 s1 s2 t3c &&& (34359738367 : UInt64)) +
      ((UInt32.ofNat n).toUInt64 <<< 13)).toNat =
      (d + n) * 2 ^ 13 + nr * 2 ^ 21 + nt * 2 ^ 29 + nw3 * 2 ^ 33 := by
    rw [UInt64.toNat_add, hlow_and, hnsh, Nat.mod_eq_of_lt (by omega)]
    ring
  have hlow_eq : (mkBaseSt d nr nt nw3 s1 s2 t3c &&& (34359738367 : UInt64)) +
      ((UInt32.ofNat n).toUInt64 <<< 13) = mkState 0 (d + n) nr nt nw3 0 0 := by
    apply UInt64.toNat_inj.mp
    rw [hlow, mkState_toNat (by omega) hdn hr ht hw3 (by omega) (by omega)]
    omega
  dsimp only
  rw [hlow_eq]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  unfold mkState
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  have hz0 : (UInt32.ofNat 0).toUInt64.toBitVec.getLsbD j = false := by simp
  have hz1 : ((UInt32.ofNat 0).toUInt64 <<< 35).toBitVec.getLsbD j = false := by
    rw [u64_field_getLsbD (val := 0) (sh := (35 : UInt64)) (w := 3) (by omega) (by omega) (by decide) (by decide) j hj, Nat.zero_testBit, Bool.and_false]
  have hz2 : ((UInt32.ofNat 0).toUInt64 <<< 38).toBitVec.getLsbD j = false := by
    rw [u64_field_getLsbD (val := 0) (sh := (38 : UInt64)) (w := 8) (by omega) (by omega) (by decide) (by decide) j hj, Nat.zero_testBit, Bool.and_false]
  rw [hz0, hz1, hz2]
  simp only [Bool.false_or, Bool.or_false]
  -- Commutativity & associativity of Bool.or
  cases (UInt32.ofNat D).toUInt64.toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat (d + n)).toUInt64 <<< 13).toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat nr).toUInt64 <<< 21).toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat nt).toUInt64 <<< 29).toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat nw3).toUInt64 <<< 33).toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat ns1).toUInt64 <<< 35).toBitVec.getLsbD j <;>
  cases ((UInt32.ofNat nextS2).toUInt64 <<< 38).toBitVec.getLsbD j <;> rfl

theorem mkLArg_unpack {lim mk cq : ℕ} {isS4 : Bool} (hlim : lim < 32) (hmk : mk < 64) (hcq : cq < 8192) :
    let la := mkLArg lim mk cq isS4
    ((la >>> 5) &&& 31).toUInt32 = UInt32.ofNat lim ∧
    ((la >>> 10) &&& 63).toUInt32 = UInt32.ofNat mk ∧
    ((la >>> 16) &&& 8191).toUInt32 = UInt32.ofNat cq ∧
    ((la >>> 29) != 0) = isS4 := by
  have hnat := mkLArg_toNat hlim hmk hcq (isS4 := isS4)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u64_shift_mask_toUInt32 _ 5 31 (shN := 5) rfl (by omega) (k := 5) rfl (by omega), hnat]; congr 1; cases isS4 <;> simp <;> omega
  · rw [u64_shift_mask_toUInt32 _ 10 63 (shN := 10) rfl (by omega) (k := 6) rfl (by omega), hnat]; congr 1; cases isS4 <;> simp <;> omega
  · rw [u64_shift_mask_toUInt32 _ 16 8191 (shN := 16) rfl (by omega) (k := 13) rfl (by omega), hnat]; congr 1; cases isS4 <;> simp <;> omega
  · have hsh : (mkLArg lim mk cq isS4 >>> 29).toNat = if isS4 then 1 else 0 := by
      rw [UInt64.toNat_shiftRight, hnat, Nat.shiftRight_eq_div_pow]
      change (lim * 2 ^ 5 + mk * 2 ^ 10 + cq * 2 ^ 16 + if isS4 = true then 2 ^ 29 else 0) / 2 ^ 29 = _
      cases isS4 <;> simp <;> omega
    cases isS4
    · simp only [Bool.false_eq_true, ite_false] at hsh
      have hz : mkLArg lim mk cq false >>> 29 = 0 := UInt64.toNat_inj.mp hsh
      simp [hz]
    · simp only [ite_true] at hsh
      have hne : mkLArg lim mk cq true >>> 29 ≠ 0 := fun h => by rw [h] at hsh; simp at hsh
      simp [hne]

/-! ### `SubSz` Preservation for `go`, `loopSucc`, `walkGo` -/

/-- `B'` is either empty (found!) or has size `sz` and is a sub-table of `B`. -/
def SubSz (sz : ℕ) (B' B : ByteArray) : Prop :=
  (B'.size = 0 ∨ B'.size = sz) ∧ Sub B' B

theorem subSz_refl {sz : ℕ} {B : ByteArray} (hB : B.size = sz) : SubSz sz B B :=
  ⟨Or.inr hB, Sub.refl B⟩

theorem subSz_empty (sz : ℕ) (B : ByteArray) : SubSz sz ByteArray.empty B :=
  ⟨Or.inl ByteArray.size_empty, S.sub_of_size_zero ByteArray.size_empty B⟩

theorem subSz_trans {sz : ℕ} {B1 B2 B3 : ByteArray} (h1 : SubSz sz B1 B2) (h2 : SubSz sz B2 B3) :
    SubSz sz B1 B3 :=
  ⟨h1.1, h1.2.trans h2.2⟩

theorem subSz_clear {sz : ℕ} {B' B : ByteArray} {c : USize} (hsz : sz < 2 ^ 32)
    (hB : B.size = sz) (hc : c.toNat < sz)
    (hsub : SubSz sz B' (baSetU8 B c 1)) (hB'ne : B'.size ≠ 0) :
    SubSz sz (baSetU8 B' c 0) B := by
  have hB'sz : B'.size = sz := hsub.1.resolve_left hB'ne
  refine ⟨Or.inr (by rw [baSetU8_size, hB'sz]), ?_⟩
  rw [baSetU8_eq_set! (by omega) (by omega)]
  have h1 : Sub B' (B.set! c.toNat 1) := by
    rw [← baSetU8_eq_set! (by omega) (by omega)]
    exact hsub.2
  exact S.sub_clear h1

theorem fastK16_subSz (ctx : FastK16Ctx) (sz : ℕ) (hsz : sz < 2 ^ 32) :
    (∀ (fuel : UInt32) (state mM : UInt64) (B : ByteArray),
      B.size = sz → SubSz sz (go ctx fuel state mM B) B) ∧
    (∀ (fuel : UInt32) (baseSt mM lArg : UInt64) (sBase : USize) (rem : UInt32) (B : ByteArray),
      B.size = sz → SubSz sz (loopSucc ctx fuel baseSt mM lArg sBase rem B) B) ∧
    (∀ (fuel : UInt32) (baseSt mM : UInt64) (rem mk D : UInt32) (B : ByteArray),
      B.size = sz → SubSz sz (walkGo ctx fuel baseSt mM rem mk D B) B) := by
  -- Prove by well-founded induction on `(fuel.toNat, tag, rem.toNat)` matching `FastK16Search`!
  suffices h : ∀ (p : ℕ × ℕ × ℕ),
      (∀ (fuel : UInt32) (state mM : UInt64) (B : ByteArray),
        p = (fuel.toNat, 3, 0) → B.size = sz → SubSz sz (go ctx fuel state mM B) B) ∧
      (∀ (fuel : UInt32) (baseSt mM lArg : UInt64) (sBase : USize) (rem : UInt32) (B : ByteArray),
        p = (fuel.toNat + 1, 2, rem.toNat) → B.size = sz →
        SubSz sz (loopSucc ctx fuel baseSt mM lArg sBase rem B) B) ∧
      (∀ (fuel : UInt32) (baseSt mM : UInt64) (rem mk D : UInt32) (B : ByteArray),
        p = (fuel.toNat + 1, 1, rem.toNat) → B.size = sz →
        SubSz sz (walkGo ctx fuel baseSt mM rem mk D B) B) by
    exact ⟨fun fuel state mM B hB => (h (fuel.toNat, 3, 0)).1 fuel state mM B rfl hB,
      fun fuel baseSt mM lArg sBase rem B hB => (h (fuel.toNat + 1, 2, rem.toNat)).2.1 fuel baseSt mM lArg sBase rem B rfl hB,
      fun fuel baseSt mM rem mk D B hB => (h (fuel.toNat + 1, 1, rem.toNat)).2.2 fuel baseSt mM rem mk D B rfl hB⟩
  intro p
  induction p using WellFounded.induction (WellFounded.prod_lex Nat.lt_wfRel.wf (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)) with
  | h p ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro fuel state mM B hp hB
      rw [go]
      by_cases hf : fuel > 0
      · rw [dif_pos hf]
        have hfuel' : (fuel - 1).toNat + 1 = fuel.toNat := by
          have hle : (1 : UInt32) ≤ fuel := hf
          rw [UInt32.toNat_sub_of_le _ _ hle, UInt32.toNat_one]; have : 0 < fuel.toNat := hf; omega
        have hlt2 : ∀ k : UInt32, Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
            ((fuel - 1).toNat + 1, 2, k.toNat) p := by
          intro k; rw [hp, hfuel']; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
        dsimp only
        set c := getCode ctx ((state >>> 29) &&& 15).toUInt32 ((state >>> 21) &&& 255).toUInt32 ((state >>> 13) &&& 255).toUInt32
        by_cases hc0 : (c == 0) = true
        · rw [if_pos hc0]; exact subSz_refl hB
        · rw [if_neg hc0]
          by_cases hc1 : (c == 1) = true
          · rw [if_pos hc1]; exact subSz_empty sz B
          · rw [if_neg hc1]
            by_cases hgt : (fuel - 1 != ctx.fg || (((state &&& 8191).toUInt32 + (8192 : UInt32) * ((state >>> 13) &&& 255).toUInt32) % ctx.nt == ctx.tp)) = true
            · rw [if_pos hgt]
              have hsub_ite : ∀ {cond : Bool} {X Y B0 : ByteArray},
                  SubSz sz X B0 → SubSz sz Y B0 → SubSz sz (if cond then X else Y) B0 := by
                intro cond X Y B0 hX hY; cases cond <;> simp [hX, hY]
              have hbind : ∀ {B1 : ByteArray} {f : ByteArray → ByteArray},
                  SubSz sz B1 B → (B1.size = sz → SubSz sz (f B1) B1) →
                  SubSz sz (if (B1.usize == 0) = true then B1 else f B1) B := by
                intro B1 f h1 hf2
                by_cases hz : (B1.usize == 0) = true
                · rw [if_pos hz]; exact h1
                · rw [if_neg hz]
                  have hne : B1.size ≠ 0 := fun h0 => hz ((ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mpr h0)
                  exact subSz_trans (hf2 (h1.1.resolve_left hne)) h1
              refine hbind ?_ (fun hB1_sz => ?_)
              · refine hsub_ite (hsub_ite (hsub_ite (subSz_refl hB) ?_) (subSz_refl hB)) (subSz_refl hB)
                exact (ih _ (hlt2 5)).2.1 (fuel - 1) _ _ _ _ 5 B rfl hB
              · refine hsub_ite (hsub_ite (hsub_ite (subSz_refl hB1_sz) ?_) (subSz_refl hB1_sz)) (subSz_refl hB1_sz)
                exact (ih _ (hlt2 23)).2.1 (fuel - 1) _ _ _ _ 23 _ rfl hB1_sz
            · rw [if_neg hgt]; exact subSz_refl hB
      · rw [dif_neg hf]; exact subSz_empty sz B
    · intro fuel baseSt mM lArg sBase rem B hp hB
      rw [loopSucc]
      by_cases hr : rem > 0
      · rw [dif_pos hr]
        have hlt1 : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (fuel.toNat + 1, 1, (6 : UInt32).toNat) p := by
          rw [hp]; exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
        have hlt2 : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (fuel.toNat + 1, 2, (rem - 1).toNat) p := by
          rw [hp]; exact Prod.Lex.right _ (Prod.Lex.right _ (FastK16.u32_sub_one_lt hr))
        dsimp only
        have hbind : ∀ {B' : ByteArray} {f : ByteArray → ByteArray},
            SubSz sz B' B → (B'.size = sz → SubSz sz (f B') B') →
            SubSz sz (if (B'.usize == 0) = true then B' else f B') B := by
          intro B' f h1 hf2
          by_cases hz : (B'.usize == 0) = true
          · rw [if_pos hz]; exact h1
          · rw [if_neg hz]
            have hne : B'.size ≠ 0 := fun h0 => hz ((ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mpr h0)
            exact subSz_trans (hf2 (h1.1.resolve_left hne)) h1
        have hsub_ite : ∀ {cond : Bool} {X Y B0 : ByteArray},
            SubSz sz X B0 → SubSz sz Y B0 → SubSz sz (if cond then X else Y) B0 := by
          intro cond X Y B0 hX hY; cases cond <;> simp [hX, hY]
        refine hbind ?_ (fun hB'_sz => (ih _ hlt2).2.1 fuel baseSt mM lArg sBase (rem - 1) _ rfl hB'_sz)
        exact hsub_ite (subSz_refl hB) ((ih _ hlt1).2.2 fuel _ mM 6 _ _ B rfl hB)
      · rw [dif_neg hr]; exact subSz_refl hB
    · intro fuel baseSt mM rem mk D B hp hB
      rw [walkGo]
      by_cases hr : rem > 0
      · rw [dif_pos hr]
        by_cases hmk : (mk == 0) = true
        · rw [if_pos hmk]; exact subSz_refl hB
        · rw [if_neg hmk]
          dsimp only
          by_cases hused : (baGetU8 B (baGetU16 ctx.ciBA D.toUSize).toUSize != 0) = true
          · rw [if_pos hused]; exact subSz_refl hB
          · rw [if_neg hused]
            have hlt_go : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (fuel.toNat, 3, 0) p := by
              rw [hp]; exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
            have hlt_w : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (fuel.toNat + 1, 1, (rem - 1).toNat) p := by
              rw [hp]; exact Prod.Lex.right _ (Prod.Lex.right _ (FastK16.u32_sub_one_lt hr))
            set c := (baGetU16 ctx.ciBA D.toUSize).toUSize
            set B0 := baSetU8 B c 1
            have hB0_sz : B0.size = sz := by rw [baSetU8_size, hB]
            have hsub_if0 : ∀ {cond : Bool} {X Y : ByteArray},
                SubSz sz X B0 → SubSz sz Y B0 → SubSz sz (if cond then X else Y) B0 := by
              intro cond X Y hX hY; cases cond <;> simp [hX, hY]
            have hbind1 : ∀ {B1 B_else : ByteArray},
                SubSz sz B1 B0 → (B1.size = sz → SubSz sz B_else B1 → SubSz sz (if (B1.usize == 0) = true then B1 else B_else) B) →
                True := fun _ _ => trivial
            have hbind_step : ∀ {B1 B2 : ByteArray},
                SubSz sz B1 B0 → (B1.size = sz → SubSz sz B2 B1) →
                SubSz sz (if (B1.usize == 0) = true then B1 else if (B2.usize == 0) = true then B2 else baSetU8 B2 c 0) B := by
              intro B1 B2 h1 h2
              by_cases hz1 : (B1.usize == 0) = true
              · rw [if_pos hz1]
                have hB1_0 : B1.size = 0 := (ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mp hz1
                exact ⟨Or.inl hB1_0, S.sub_of_size_zero hB1_0 B⟩
              · rw [if_neg hz1]
                have hB1_sz : B1.size = sz := by
                  have hne : B1.size ≠ 0 := fun h0 => hz1 ((ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mpr h0)
                  exact h1.1.resolve_left hne
                have hB20 : SubSz sz B2 B0 := subSz_trans (h2 hB1_sz) h1
                by_cases hz2 : (B2.usize == 0) = true
                · rw [if_pos hz2]
                  have hB2_0 : B2.size = 0 := (ba_usize_eq_zero_iff (by rcases hB20.1 with h | h <;> omega)).mp hz2
                  exact ⟨Or.inl hB2_0, S.sub_of_size_zero hB2_0 B⟩
                · rw [if_neg hz2]
                  have hB2_ne : B2.size ≠ 0 := fun h0 => hz2 ((ba_usize_eq_zero_iff (by rcases hB20.1 with h | h <;> omega)).mpr h0)
                  by_cases hclt : c.toNat < sz
                  · exact subSz_clear hsz hB hclt hB20 hB2_ne
                  · have hB0_eq : B0 = B := by
                      unfold B0 baSetU8
                      have hnlt : ¬ c < B.usize := fun h => by
                        have h1 : c.toNat < B.usize.toNat := h
                        rw [ByteArray.usize, usize_ofNat_toNat (by omega)] at h1; omega
                      rw [dite_eq_right_of_eq_false (eq_false hnlt)]
                    have hB2_sz : B2.size = sz := hB20.1.resolve_left hB2_ne
                    have hcl_eq : baSetU8 B2 c 0 = B2 := by
                      unfold baSetU8
                      have hnlt : ¬ c < B2.usize := fun h => by
                        have h1 : c.toNat < B2.usize.toNat := h
                        rw [ByteArray.usize, usize_ofNat_toNat (by omega)] at h1; omega
                      rw [dite_eq_right_of_eq_false (eq_false hnlt)]
                    rw [hcl_eq]; rw [hB0_eq] at hB20; exact hB20
            refine hbind_step ?_ (fun hB1_sz => ?_)
            · exact hsub_if0 (hsub_if0 ((ih _ hlt_go).1 fuel _ mM B0 rfl hB0_sz) (subSz_refl hB0_sz)) (subSz_refl hB0_sz)
            · by_cases hmk' : (mk >>> 1 != 0) = true
              · rw [if_pos hmk']
                exact (ih _ hlt_w).2.2 fuel baseSt mM (rem - 1) (mk >>> 1) (baGetU16 ctx.nxtBA D.toUSize) _ rfl hB1_sz
              · rw [if_neg hmk']; exact subSz_refl hB1_sz
      · rw [dif_neg hr]; exact subSz_refl hB

/-! ### Arithmetic Bounds on `a1F`, `a2F`, `potN`, `potS`, and Table Equivalence -/

private theorem maxLe_bounds {f : ℕ → ℤ} {M : ℤ} (hM : 0 ≤ M)
    (hf : ∀ i ≤ n, -M ≤ f i ∧ f i ≤ M) :
    -M ≤ KS.maxLe f n ∧ KS.maxLe f n ≤ M := by
  induction n with
  | zero => exact hf 0 le_rfl
  | succ n ih =>
    have h1 := ih (fun i hi => hf i (by omega))
    have h2 := hf (n + 1) le_rfl
    unfold KS.maxLe
    exact ⟨le_trans h1.1 (le_max_left _ _), max_le h1.2 h2.2⟩

private theorem minLe_bounds {p : ℕ → Bool} {f : ℕ → ℤ} {init M : ℤ} (hinit : -M ≤ init ∧ init ≤ M)
    (hf : ∀ i ≤ n, -M ≤ f i ∧ f i ≤ M) :
    -M ≤ KS.minLe p f init n ∧ KS.minLe p f init n ≤ M := by
  induction n with
  | zero =>
    unfold KS.minLe
    split_ifs
    · exact ⟨le_min hinit.1 (hf 0 le_rfl).1, le_trans (min_le_left _ _) hinit.2⟩
    · exact hinit
  | succ n ih =>
    have h1 := ih (fun i hi => hf i (by omega))
    have h2 := hf (n + 1) le_rfl
    unfold KS.minLe
    split_ifs
    · exact ⟨le_min h1.1 h2.1, le_trans (min_le_left _ _) h1.2⟩
    · exact h1

private theorem capF_le_of_all {caps : List (List ℕ)} {B : ℕ}
    (hB : ∀ row ∈ caps, ∀ v ∈ row, v ≤ B) (u y : ℕ) : capF caps u y ≤ B := by
  unfold capF
  by_cases hu : u < caps.length
  · have hrow : caps.getD u [] = caps[u] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]; rfl
    rw [hrow]
    by_cases hy : y < caps[u].length
    · have hval : caps[u].getD y 0 = caps[u][y] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]; rfl
      rw [hval]
      exact hB caps[u] (List.getElem_mem hu) caps[u][y] (List.getElem_mem hy)
    · have hval : caps[u].getD y 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [hval]; omega
  · have hrow : caps.getD u [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hrow]; simp

/-- Context table-correctness bundle for `buildProblem`. -/
structure ValidCtx (caps : List (List ℕ)) (s lo hi a b h : ℕ) (js useM3 useW4 : Bool)
    (fuel ds nt tp : ℕ) (ctx : FastK16Ctx) : Prop where
  hA : ctx.A = UInt32.ofNat (s + 1)
  hS : ctx.S = UInt32.ofNat s
  hR : ctx.R = UInt32.ofNat (rowsR caps s hi)
  hC : ctx.C = UInt32.ofNat (hi + 1)
  hpa : ctx.pa = Int32.ofInt a
  hpb : ctx.pb = Int32.ofInt b
  hph : ctx.ph = Int32.ofInt h
  hph2 : ctx.ph2 = Int32.ofInt (2 * h)
  hjs : ctx.js = js
  hM3 : ctx.useM3 = useM3
  hW4 : ctx.useW4 = useW4
  hfg : ctx.fg = UInt32.ofNat (fuel - ds)
  hnt : ctx.nt = UInt32.ofNat nt
  htp : ctx.tp = UInt32.ofNat tp
  hciBA : ctx.ciBA = buildS7K16Tabs.ciBA
  hnxtBA : ctx.nxtBA = buildS7K16Tabs.nxtBA
  hb2CiBA : ctx.b2CiBA = buildS7K16Tabs.b2CiBA
  hs3BA : ctx.s3BA = buildS7K16Tabs.s3BA
  hs4BA : ctx.s4BA = buildS7K16Tabs.s4BA
  hm3BA : useM3 = true → ctx.m3AllowBA = buildM3Allow
  hw4BA : useW4 = true → ctx.w4AllowBA = buildW4Allow
  hu3BA : useM3 = true →
    ctx.u3MinRBA = buildU3MinR buildS7K16Tabs buildM3Allow (capF caps 0) (capF caps s) lo hi js
  hcode : ∀ t r d, t ≤ s → d ≤ hi → r < 256 →
    (getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)).toNat =
      codeF (capF caps) s lo hi t r d
  hmask : ∀ t r d j, t ≤ s → d ≤ hi → r < 256 → j < 6 →
    codeF (capF caps) s lo hi t r (d + (5 - j)) ≠ 0 →
    ((getMask ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)).toNat >>> j) % 2 = 1
  hmask_lt : ∀ t r d, t ≤ s → d ≤ hi → r < 256 →
    (getMask ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)).toNat < 64
  hcut : ∀ t r d (m M : ℤ), t ≤ s → r < 256 → d ≤ hi →
    -2 ^ 28 ≤ m → m ≤ 2 ^ 28 → -2 ^ 28 ≤ M → M ≤ 2 ^ 28 →
    cutF (a1F (capF caps) s lo hi a b h)
      (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h) t r d m M = true →
    checkCut ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int32.ofInt m) (Int32.ofInt M) = true

set_option maxHeartbeats 400000 in
theorem buildProblem_valid {caps : List (List ℕ)} {s lo hi a b h : ℕ} {js useM3 useW4 : Bool}
    {fuel ds nt tp : ℕ}
    (hs : s < 15) (hhi : hi < 200) (hR : rowsR caps s hi < 250)
    (habh : a ≤ 100 ∧ b ≤ 100 ∧ h ≤ 100)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) :
    let (ctx0, _, _) := buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt
    ValidCtx caps s lo hi a b h js useM3 useW4 fuel ds nt tp { ctx0 with tp := UInt32.ofNat tp } := by
  have hA : s + 1 ≤ 15 := by omega
  have hB : rowsR caps s hi + 1 ≤ 250 := by omega
  have hC : hi + 1 ≤ 200 := by omega
  have htot : (s + 1) * (rowsR caps s hi + 1) * (hi + 1) < 1000000 := by
    have : (s + 1) * (rowsR caps s hi + 1) ≤ 15 * 250 := Nat.mul_le_mul hA hB
    have : (s + 1) * (rowsR caps s hi + 1) * (hi + 1) ≤ 15 * 250 * 200 := Nat.mul_le_mul this hC
    omega
  have hcodeT := KS.codeT_eq (lo := lo) (KS.rowsR_spec caps s hi)
  have hcode_lt : ∀ t r d, codeF (capF caps) s lo hi t r d < 256 := by
    intro t r d; unfold codeF; split_ifs <;> omega
  have hmask_lt64 : ∀ f t r d, maskG f t r d 6 < 64 := by
    intro f t r d
    have hpow : ∀ n, maskG f t r d n < 2 ^ n := by
      intro n; induction n with
      | zero => simp [maskG]
      | succ n ih => unfold maskG; split_ifs <;> omega
    exact hpow 6
  -- Value bounds on a1F and a2F (< 2^31 << 2^62)
  have haZ : (0 : ℤ) ≤ a ∧ (a : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.1⟩
  have hbZ : (0 : ℤ) ≤ b ∧ (b : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.1⟩
  have hhZ : (0 : ℤ) ≤ h ∧ (h : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.2⟩
  have hpot_bd : ∀ u r e, u ≤ s → r ≤ rowsR caps s hi → e ≤ hi →
      -200000 ≤ potN a b h u r e ∧ potN a b h u r e ≤ 200000 := by
    intro u r e hu hr he
    have huZ : (0 : ℤ) ≤ u ∧ (u : ℤ) ≤ 15 := ⟨by positivity, by omega⟩
    have hrZ : (0 : ℤ) ≤ r ∧ (r : ℤ) ≤ 250 := ⟨by positivity, by omega⟩
    have heZ : (0 : ℤ) ≤ e ∧ (e : ℤ) ≤ 200 := ⟨by positivity, by omega⟩
    have h1 : (0 : ℤ) ≤ (a : ℤ) * r ∧ (a : ℤ) * r ≤ 25000 := ⟨by positivity, by nlinarith⟩
    have h2 : (0 : ℤ) ≤ (b : ℤ) * e ∧ (b : ℤ) * e ≤ 20000 := ⟨by positivity, by nlinarith⟩
    have h3 : (0 : ℤ) ≤ (h : ℤ) * u ∧ (h : ℤ) * u ≤ 1500 := ⟨by positivity, by nlinarith⟩
    unfold potN; push_cast; constructor <;> linarith
  have hlin_bd : ∀ u e, u ≤ s → e ≤ hi →
      -200000 ≤ KS.lin (capF caps) a b h u e ∧ KS.lin (capF caps) a b h u e ≤ 200000 := by
    intro u e hu he
    have hc := capF_le_of_all hcaps u e
    have huZ : (0 : ℤ) ≤ u ∧ (u : ℤ) ≤ 15 := ⟨by positivity, by omega⟩
    have hcZ : (0 : ℤ) ≤ capF caps u e ∧ (capF caps u e : ℤ) ≤ 200 := ⟨by positivity, by exact_mod_cast hc⟩
    have heZ : (0 : ℤ) ≤ e ∧ (e : ℤ) ≤ 200 := ⟨by positivity, by omega⟩
    have h1 : (0 : ℤ) ≤ (a : ℤ) * (capF caps u e : ℤ) ∧ (a : ℤ) * (capF caps u e : ℤ) ≤ 20000 := ⟨by positivity, by nlinarith⟩
    have h2 : (0 : ℤ) ≤ (b : ℤ) * e ∧ (b : ℤ) * e ≤ 20000 := ⟨by positivity, by nlinarith⟩
    have h3 : (0 : ℤ) ≤ (h : ℤ) * u ∧ (h : ℤ) * u ≤ 1500 := ⟨by positivity, by nlinarith⟩
    unfold KS.lin potN; push_cast; constructor <;> linarith
  have huF_bd : ∀ t y, t ≤ s → y ≤ hi → -200000 ≤ uF (capF caps) s a b h t y ∧ uF (capF caps) s a b h t y ≤ 200000 := by
    intro t y ht hy
    exact maxLe_bounds (by omega) (fun i hi' => hlin_bd (t + i) y (by omega) hy)
  have hsegF_bd : ∀ t e, t ≤ s → e ≤ hi → -200000 ≤ segF (capF caps) s a b h t e ∧ segF (capF caps) s a b h t e ≤ 200000 := by
    intro t e ht he
    exact maxLe_bounds (by omega) (fun u hu => hlin_bd u e (by omega) he)
  have hcF_bd : ∀ x, x ≤ hi → -200000 ≤ KS.cF (capF caps) s a b h x ∧ KS.cF (capF caps) s a b h x ≤ 200000 := by
    intro x hx
    have hc := capF_le_of_all hcaps s x
    have hsZ : (0 : ℤ) ≤ s ∧ (s : ℤ) ≤ 15 := ⟨by positivity, by omega⟩
    have hcZ : (0 : ℤ) ≤ capF caps s x + 1 ∧ ((capF caps s x + 1 : ℕ) : ℤ) ≤ 201 := ⟨by positivity, by omega⟩
    have hxZ : (0 : ℤ) ≤ x ∧ (x : ℤ) ≤ 200 := ⟨by positivity, by omega⟩
    have h1 : (0 : ℤ) ≤ (a : ℤ) * ((capF caps s x + 1 : ℕ) : ℤ) ∧ (a : ℤ) * ((capF caps s x + 1 : ℕ) : ℤ) ≤ 20100 :=
      ⟨by positivity, by nlinarith⟩
    have h2 : (0 : ℤ) ≤ (b : ℤ) * x ∧ (b : ℤ) * x ≤ 20000 := ⟨by positivity, by nlinarith⟩
    have h3 : (0 : ℤ) ≤ (h : ℤ) * s ∧ (h : ℤ) * s ≤ 1500 := ⟨by positivity, by nlinarith⟩
    unfold KS.cF potN; push_cast at h1 ⊢; constructor <;> linarith
  have ha1_bd : ∀ t r d, t ≤ s → r ≤ rowsR caps s hi → d ≤ hi →
      -2 ^ 60 ≤ a1F (capF caps) s lo hi a b h t r d ∧ a1F (capF caps) s lo hi a b h t r d ≤ 2 ^ 60 := by
    intro t r d ht hr hd
    apply minLe_bounds (by unfold big; omega)
    intro x hx
    have := hcF_bd x hx; omega
  have ha2_bd : ∀ t r d, t ≤ s → r ≤ rowsR caps s hi → d ≤ hi →
      -2 ^ 60 ≤ a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h t r d ∧
      a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h t r d ≤ 2 ^ 60 := by
    intro t r d ht hr hd
    apply minLe_bounds (by unfold big; omega)
    intro x hx
    have hpot := hpot_bd t r d ht hr hd
    have hpk : -500000 ≤ KS.pkF (uF (capF caps) s a b h) (segF (capF caps) s a b h) (potN a b h t r d) t d x ∧
        KS.pkF (uF (capF caps) s a b h) (segF (capF caps) s a b h) (potN a b h t r d) t d x ≤ 500000 := by
      apply maxLe_bounds (by omega)
      intro e he
      have h1 := huF_bd t (d + e) ht (by omega)
      have h2 := hsegF_bd t e ht (by omega)
      exact ⟨le_min (by omega) (by omega), le_trans (min_le_left _ _) (by omega)⟩
    have hcF := hcF_bd x hx
    omega
  -- Keep `buildS7K16Tabs`, `buildM3Allow`, `buildW4Allow`, `buildU3MinR` completely opaque!
  have hcapT_eq := KS.look2_tab2 (s + 1) (hi + 1) (capF caps)
  have huT_eq := KS.look2_tab2 (s + 1) (hi + 1) (uF (capF caps) s a b h)
  have hgT_eq := KS.look2_tab2 (s + 1) (hi + 1) (segF (capF caps) s a b h)
  have hrows_eq : maxLeN (capF caps s) hi + 1 = rowsR caps s hi := rfl
  have htot_eq : (s + 1) * (maxLeN (look2 (s + 1) (hi + 1) (tab2 (s + 1) (hi + 1) (capF caps)) (capF caps) s) hi + 1 + 1) * (hi + 1) =
      (s + 1) * (rowsR caps s hi + 1) * (hi + 1) := by rw [hcapT_eq]; rfl
  have hidx_lt_tot : ∀ t r d, t ≤ s → r ≤ rowsR caps s hi → d ≤ hi →
      (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d < (s + 1) * (rowsR caps s hi + 1) * (hi + 1) := by
    intro t r d ht hr hd
    have h1 : t * (rowsR caps s hi + 1) + (rowsR caps s hi + 1) = (t + 1) * (rowsR caps s hi + 1) := by ring
    have h2 : (t + 1) * (rowsR caps s hi + 1) ≤ (s + 1) * (rowsR caps s hi + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : t * (rowsR caps s hi + 1) + r + 1 ≤ (s + 1) * (rowsR caps s hi + 1) := by omega
    have h4 : (t * (rowsR caps s hi + 1) + r + 1) * (hi + 1) ≤ (s + 1) * (rowsR caps s hi + 1) * (hi + 1) :=
      Nat.mul_le_mul_right _ h3
    have h5 : (t * (rowsR caps s hi + 1) + r + 1) * (hi + 1) =
        (t * (rowsR caps s hi + 1) + r) * (hi + 1) + (hi + 1) := by ring
    omega
  have hidx3 : ∀ t r d, t < s + 1 → r < rowsR caps s hi + 1 → d < hi + 1 →
      ((UInt32.ofNat t * (UInt32.ofNat (rowsR caps s hi) + 1) + UInt32.ofNat r) *
        UInt32.ofNat (hi + 1) + UInt32.ofNat d).toUSize =
        USize.ofNat ((t * (rowsR caps s hi + 1) + r) * (hi + 1) + d) := by
    intro t r d ht hr hd
    have h1 : (UInt32.ofNat (rowsR caps s hi) + 1).toNat = rowsR caps s hi + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have h2 : (UInt32.ofNat t * (UInt32.ofNat (rowsR caps s hi) + 1) + UInt32.ofNat r).toNat =
        t * (rowsR caps s hi + 1) + r := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', h1, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : r < 2 ^ 32),
        Nat.mod_eq_of_lt (by nlinarith : t * (rowsR caps s hi + 1) < 2 ^ 32),
        Nat.mod_eq_of_lt (by nlinarith : t * (rowsR caps s hi + 1) + r < 2 ^ 32)]
    have hidx_small : (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d < 2 ^ 32 := by
      have h1 : t * (rowsR caps s hi + 1) + r < 15 * 250 := by
        have : t * (rowsR caps s hi + 1) ≤ 14 * 250 := Nat.mul_le_mul (by omega) (by omega)
        omega
      have h2 : (t * (rowsR caps s hi + 1) + r) * (hi + 1) ≤ (15 * 250) * 200 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have h3 : ((UInt32.ofNat t * (UInt32.ofNat (rowsR caps s hi) + 1) + UInt32.ofNat r) *
        UInt32.ofNat (hi + 1) + UInt32.ofNat d).toNat =
        (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d := by
      rw [UInt32.toNat_add, UInt32.toNat_mul, h2, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : hi + 1 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : (t * (rowsR caps s hi + 1) + r) * (hi + 1) < 2 ^ 32),
        Nat.mod_eq_of_lt hidx_small]
    apply USize.toNat_inj.mp
    rw [UInt32.toNat_toUSize, h3, usize_ofNat_toNat hidx_small]
  unfold buildProblem
  simp only [hcapT_eq, huT_eq, hgT_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    fun hm => by simp only [hm, ite_true],
    fun hw => by simp only [hw, ite_true],
    fun hm => by simp only [hm, ite_true],
    ?_, ?_, ?_, ?_⟩
  · -- hcode
    intro t r d ht hd hr
    unfold getCode idx3
    simp only [hcapT_eq, hrows_eq]
    have ht_lt : UInt32.ofNat t < UInt32.ofNat (s + 1) := by
      change (UInt32.ofNat t).toNat < (UInt32.ofNat (s + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hd_lt : UInt32.ofNat d < UInt32.ofNat (hi + 1) := by
      change (UInt32.ofNat d).toNat < (UInt32.ofNat (hi + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [ht_lt, hd_lt, decide_true, Bool.and_self, ite_true]
    set r' := min r (rowsR caps s hi)
    have hr'_eq : (if UInt32.ofNat r < UInt32.ofNat (rowsR caps s hi) then UInt32.ofNat r else UInt32.ofNat (rowsR caps s hi)) =
        UInt32.ofNat r' := by
      by_cases hlt : r < rowsR caps s hi
      · have : UInt32.ofNat r < UInt32.ofNat (rowsR caps s hi) := by
          change (UInt32.ofNat r).toNat < (UInt32.ofNat (rowsR caps s hi)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        rw [if_pos this]; congr 1; exact (Nat.min_eq_left (by omega)).symm
      · have : ¬ UInt32.ofNat r < UInt32.ofNat (rowsR caps s hi) := by
          change ¬ (UInt32.ofNat r).toNat < (UInt32.ofNat (rowsR caps s hi)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        rw [if_neg this]; congr 1; exact (Nat.min_eq_right (by omega)).symm
    rw [hr'_eq, hidx3 t r' d (by omega) (by omega) (by omega)]
    have hidx_lt : (t * (rowsR caps s hi + 1) + r') * (hi + 1) + d < (s + 1) * (rowsR caps s hi + 1) * (hi + 1) :=
      hidx_lt_tot t r' d ht (Nat.min_le_right _ _) hd
    rw [baGetU8_ofFn _ (by rw [htot_eq]; omega) (by rw [htot_eq]; exact hidx_lt)]
    dsimp only
    rw [KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega)]
    rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (hcode_lt t r' d)]
    have hct := congrFun (congrFun (congrFun hcodeT t) r) d
    unfold codeT at hct
    have hin : (decide (t < s + 1) && decide (d < hi + 1)) = true := by simp [show t < s + 1 by omega, show d < hi + 1 by omega]
    rw [if_pos hin, KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega)] at hct
    exact hct
  · -- hmask
    intro t r d j ht hd hr hj hne
    unfold getMask idx3
    simp only [hcapT_eq, hrows_eq]
    have ht_lt : UInt32.ofNat t < UInt32.ofNat (s + 1) := by
      change (UInt32.ofNat t).toNat < (UInt32.ofNat (s + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hd_lt : UInt32.ofNat d < UInt32.ofNat (hi + 1) := by
      change (UInt32.ofNat d).toNat < (UInt32.ofNat (hi + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    by_cases hrle : r ≤ rowsR caps s hi
    · have hr_u32 : UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
        change (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      simp only [ht_lt, hr_u32, hd_lt, decide_true, Bool.and_self, ite_true]
      rw [hidx3 t r d (by omega) (by omega) (by omega)]
      have hidx_lt : (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d < (s + 1) * (rowsR caps s hi + 1) * (hi + 1) :=
        hidx_lt_tot t r d ht hrle hd
      rw [baGetU8_ofFn _ (by rw [htot_eq]; omega) (by rw [htot_eq]; exact hidx_lt)]
      dsimp only
      rw [KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega), UInt8.toNat_toUInt32, UInt8.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans (hmask_lt64 _ t r d) (by decide)), Nat.shiftRight_eq_div_pow, hcodeT]
      exact KS.maskG_bit _ t r d 6 j hj hne
    · have hr_u32 : ¬ UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
        change ¬ (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      simp only [ht_lt, hr_u32, decide_false, Bool.and_false, Bool.false_and, ite_false]
      have hlt32 : maskG (fun _ _ _ => 1) 0 0 0 6 < 2 ^ 32 := by
        have := hmask_lt64 (fun _ _ _ => 1) 0 0 0; omega
      change (UInt32.ofNat (maskG (fun _ _ _ => 1) 0 0 0 6)).toNat >>> j % 2 = 1
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32, Nat.shiftRight_eq_div_pow]
      exact KS.maskG_bit (fun _ _ _ => 1) 0 0 0 6 j hj (by simp)
  · -- hmask_lt
    intro t r d ht hd hr
    unfold getMask idx3
    simp only [hcapT_eq, hrows_eq]
    have ht_lt : UInt32.ofNat t < UInt32.ofNat (s + 1) := by
      change (UInt32.ofNat t).toNat < (UInt32.ofNat (s + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hd_lt : UInt32.ofNat d < UInt32.ofNat (hi + 1) := by
      change (UInt32.ofNat d).toNat < (UInt32.ofNat (hi + 1)).toNat
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    by_cases hrle : r ≤ rowsR caps s hi
    · have hr_u32 : UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
        change (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      simp only [ht_lt, hr_u32, hd_lt, decide_true, Bool.and_self, ite_true]
      rw [hidx3 t r d (by omega) (by omega) (by omega)]
      have hidx_lt : (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d < (s + 1) * (rowsR caps s hi + 1) * (hi + 1) :=
        hidx_lt_tot t r d ht hrle hd
      rw [baGetU8_ofFn _ (by rw [htot_eq]; omega) (by rw [htot_eq]; exact hidx_lt)]
      dsimp only
      rw [KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega), UInt8.toNat_toUInt32, UInt8.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.lt_trans (hmask_lt64 _ t r d) (by decide))]
      exact hmask_lt64 _ t r d
    · have hr_u32 : ¬ UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
        change ¬ (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      simp only [ht_lt, hr_u32, decide_false, Bool.and_false, Bool.false_and, ite_false]
      have hlt32 : maskG (fun _ _ _ => 1) 0 0 0 6 < 2 ^ 32 := by
        have := hmask_lt64 (fun _ _ _ => 1) 0 0 0; omega
      change (UInt32.ofNat (maskG (fun _ _ _ => 1) 0 0 0 6)).toNat < 64
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]
      exact hmask_lt64 (fun _ _ _ => 1) 0 0 0
  · -- hcut
    intro t r d m M ht hr hd hm1 hm2 hM1 hM2 hcf
    unfold checkCut idx3
    simp only [hcapT_eq, huT_eq, hgT_eq, hrows_eq]
    by_cases hm0 : 0 ≤ m
    · have : Int32.ofInt m ≥ 0 := by
        rw [ge_iff_le, int32_le_iff_toInt, int32_toInt_ofInt (by omega) (by omega)]; exact hm0
      simp [this]
    · have hmn0 : ¬ Int32.ofInt m ≥ 0 := by
        rw [ge_iff_le, int32_le_iff_toInt, int32_toInt_ofInt (by omega) (by omega)]; exact hm0
      rw [if_neg hmn0]
      by_cases hin : r ≤ rowsR caps s hi
      · have ht_lt : UInt32.ofNat t < UInt32.ofNat (s + 1) := by
          change (UInt32.ofNat t).toNat < (UInt32.ofNat (s + 1)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        have hr_le : UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
          change (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        have hd_lt : UInt32.ofNat d < UInt32.ofNat (hi + 1) := by
          change (UInt32.ofNat d).toNat < (UInt32.ofNat (hi + 1)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        simp only [ht_lt, hr_le, hd_lt, decide_true, Bool.and_self, ite_true]
        rw [hidx3 t r d (by omega) (by omega) (by omega)]
        have hidx_lt : (t * (rowsR caps s hi + 1) + r) * (hi + 1) + d < (s + 1) * (rowsR caps s hi + 1) * (hi + 1) :=
          hidx_lt_tot t r d ht hin hd
        rw [baGetI64_packI64Arr (by simp [htot_eq]; omega) (by simp [htot_eq]; exact hidx_lt),
          baGetI64_packI64Arr (by simp [htot_eq]; omega) (by simp [htot_eq]; exact hidx_lt)]
        rw [getElem!_pos (Array.ofFn _) _ (by simp [htot_eq]; exact hidx_lt), Array.getElem_ofFn,
          getElem!_pos (Array.ofFn _) _ (by simp [htot_eq]; exact hidx_lt), Array.getElem_ofFn]
        dsimp only
        rw [KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega),
          KS.tabA_get _ _ _ _ (by omega) (by omega) (by omega)]
        have hm64 : (Int32.ofInt m).toInt64 = Int64.ofInt m := by
          apply Int64.toInt_inj.mp
          rw [int32_toInt64_toInt, int32_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
        have hM64 : (Int32.ofInt M).toInt64 = Int64.ofInt M := by
          apply Int64.toInt_inj.mp
          rw [int32_toInt64_toInt, int32_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
        have hsum64 : Int64.ofInt M + Int64.ofInt m = Int64.ofInt (M + m) :=
          int64_ofInt_add (by omega) (by omega) (by omega) (by omega)
        rw [hm64, hM64]
        unfold cutF at hcf
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcf
        rcases hcf with (h0 | h1) | h2
        · exact absurd h0 hm0
        · have hle1 : Int64.ofInt (a1F (capF caps) s lo hi a b h t r d) ≤ Int64.ofInt M + Int64.ofInt m := by
            rw [hsum64]
            have hb := ha1_bd t r d ht hin hd
            rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
            exact h1
          rw [if_pos hle1]
        · have hle2 : Int64.ofInt (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h t r d) ≤ Int64.ofInt m := by
            have hb := ha2_bd t r d ht hin hd
            rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
            exact h2
          split_ifs
          · rfl
          · exact decide_eq_true hle2
      · have hr_le : ¬ UInt32.ofNat r ≤ UInt32.ofNat (rowsR caps s hi) := by
          change ¬ (UInt32.ofNat r).toNat ≤ (UInt32.ofNat (rowsR caps s hi)).toNat
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        simp [hr_le]

/-! ### Prefix Tail Invariant & Completeness of `walkGo`, `loopSucc`, `go` -/

/-- Tracks the last 1–2 rows of `pref` to match `w3Run`, `s1`, `s2` in `FastK16.go`. -/
def TailInv (pref : List TRow) (w3 s1 s2 : ℕ) : Prop :=
  w3 ≤ 2 ∧ s1 < 6 ∧ s2 < 180 ∧
  (∃ (U : List TRow) (R1 : TRow), pref = U ++ [R1] ∧ R1.2.length = s1 + 1) ∧
  (1 ≤ w3 → ∃ (U : List TRow) (R0 R1 : TRow) (t0 : ℕ) (h0 : R0.2 ≠ []) (h1 : R1.2 ≠ []),
    pref = U ++ [R0, R1] ∧ R1.1 = 0 ∧ t0 < 5 ∧
    R1.2.head h1 = w3Step (R0.2.getLast h0) t0 ∧
    s2 = (R0.2.length - 1) * 30 + t0 * 6 + (R1.2.length - 1))

theorem tailInv_single (R0 : TRow) (hne : R0.2 ≠ []) (hsz : R0.2.length ≤ 6) :
    TailInv [R0] 0 (R0.2.length - 1) 0 := by
  have hpos : 1 ≤ R0.2.length := List.length_pos_iff.mpr hne
  exact ⟨by omega, by omega, by omega, ⟨[], R0, rfl, by omega⟩, fun h => by omega⟩

theorem tailInv_w4 (pref : List TRow) (R1 : TRow) (hne : R1.2 ≠ []) (hsz : R1.2.length ≤ 6) :
    TailInv (pref ++ [R1]) 0 (R1.2.length - 1) 0 := by
  have hpos : 1 ≤ R1.2.length := List.length_pos_iff.mpr hne
  exact ⟨by omega, by omega, by omega, ⟨pref, R1, rfl, by omega⟩, fun h => by omega⟩

theorem tailInv_w3 {pref : List TRow} {w3 s1 s2 t3 : ℕ} {R1 R2 : TRow}
    (htail : TailInv pref w3 s1 s2)
    (hpref_last : ∃ U, pref = U ++ [R1])
    (hR1ne : R1.2 ≠ []) (hR2ne : R2.2 ≠ []) (hR2sz : R2.2.length ≤ 6)
    (hR2k : R2.1 = 0) (ht3 : t3 < 5)
    (hstep : R2.2.head hR2ne = w3Step (R1.2.getLast hR1ne) t3) :
    let nw3 := if w3 < 2 then w3 + 1 else 2
    let ns1 := R2.2.length - 1
    let nextS2 := s1 * 30 + t3 * 6 + ns1
    TailInv (pref ++ [R2]) nw3 ns1 nextS2 := by
  obtain ⟨U0, hU0⟩ := hpref_last
  obtain ⟨_, hs1, _, ⟨U1, R1', hU1, hR1'_len⟩, _⟩ := htail
  have hR1_eq : R1' = R1 := by
    have h1 := hU1.symm.trans hU0
    exact (List.append_inj_right' h1 rfl |> List.cons.inj).1
  subst R1'
  have hR2pos : 1 ≤ R2.2.length := List.length_pos_iff.mpr hR2ne
  refine ⟨by split_ifs <;> omega, by omega, by omega, ⟨pref, R2, rfl, by omega⟩, fun _ => ?_⟩
  refine ⟨U0, R1, R2, t3, hR1ne, hR2ne, by rw [hU0]; simp, hR2k, ht3, hstep, ?_⟩
  omega

/-- Completeness of `walkGo` along a single row `v :: R`. -/
theorem walkGo_complete {ctx : FastK16Ctx} {sz : ℕ} (hsz_eq : sz = (PS.permCodes 7 7).length)
    (hciBA : ctx.ciBA = buildS7K16Tabs.ciBA) (hnxtBA : ctx.nxtBA = buildS7K16Tabs.nxtBA)
    (fuel : UInt32) (baseSt mM : UInt64)
    (d nr nt nw3 s1 s2 t3c : ℕ)
    (hd : d < 256) (hr : nr < 256) (ht : nt < 16) (hw3 : nw3 < 4)
    (hs1 : s1 < 6) (hs2 : s2 < 256) (ht3 : t3c < 5)
    (hbst : baseSt = mkBaseSt d nr nt nw3 s1 s2 t3c)
    (R : List (List ℕ)) (rem : ℕ) (mk : UInt32) (v : List ℕ) (B : ByteArray) (used : List (List ℕ))
    (hrem : rem ≤ 6) (hR : R.length < rem) (hrem_d : d + (rem - 1 - R.length) < 256)
    (hbit : (mk.toNat >>> R.length) % 2 = 1)
    (hperm : ∀ w ∈ v :: R, PermW 7 w)
    (hdoor : List.IsChain (DoorEq 7) (v :: R))
    (hB_sz : B.size = sz) (hM : MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!) B used)
    (hused : ∀ u ∈ used, PermW 7 u)
    (hnew : ∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w)
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (v :: R))
    (hokM3 : nw3 = 2 → ctx.useM3 = true →
      let ns1 := 5 - (rem - 1 - R.length)
      let ns3 := s2 * 30 + t3c * 6 + ns1
      (baGetU8 ctx.m3AllowBA (USize.ofNat ns3) != 0) = true ∧
      (nt = ctx.S.toNat →
        d + (rem - 1 - R.length) < ctx.C.toNat ∧
        (baGetU8 ctx.u3MinRBA (USize.ofNat ((d + (rem - 1 - R.length)) * 5400 + ns3))).toNat < nr))
    (hfin : ∀ B', B'.size = sz →
      MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!) B' (used ++ v :: R) →
      let n := rem - 1 - R.length
      let ns1 := 5 - n
      let nextS2 := if nw3 = 0 then 0 else s1 * 30 + t3c * 6 + ns1
      (go ctx fuel (mkState (encB 7 ((v :: R).getLast (List.cons_ne_nil v R))) (d + n) nr nt nw3 ns1 nextS2) mM B').size = 0) :
    (walkGo ctx fuel baseSt mM (UInt32.ofNat rem) mk (UInt32.ofNat (encB 7 v)) B).size = 0 := by
  have hsz_le : sz ≤ 5040 := hsz_eq ▸ permCodes7_length_le
  have hsz_u32 : sz < 2 ^ 32 := by omega
  induction R generalizing rem mk v B used with
  | nil =>
    have hrem_pos : 0 < rem := by simpa using hR
    have hrem_u : UInt32.ofNat rem > 0 := by
      change 0 < (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hrem_pos
    have hmk_ne : (mk == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      intro h0; subst h0; simp at hbit
    have hv := hperm v List.mem_cons_self
    have hv_lt := encB_lt hv
    have hD_us : (UInt32.ofNat (encB 7 v)).toUSize = USize.ofNat (encB 7 v) := by
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
    have hci_eq : (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize =
        USize.ofNat ((ciTab 7 (PS.permCodes 7 7))[encB 7 v]!) := by
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, hciBA, hD_us, tabs_ciBA_get hv, usize_ofNat_toNat (by have := ciTab_lt hv_lt; omega)]
    have hci_lt : (ciTab 7 (PS.permCodes 7 7))[encB 7 v]! < sz := hsz_eq ▸ ciTab_lt hv_lt
    have h0_raw := PS.unmarked_of_new (PS.encB_enc 7 (by omega) (by omega)) hM hused hv
      (fun u hu => hnew u hu v List.mem_cons_self)
    have h0_ba : (baGetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize != 0) = false := by
      rw [hci_eq, baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hB_sz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
      simp [h0_raw]
    have hbit0 : ((mk &&& 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h0
      have h1 : (mk &&& 1).toNat = 0 := congrArg UInt32.toNat h0
      rw [UInt32.toNat_and, UInt32.toNat_one, Nat.and_one_is_mod] at h1
      simp only [List.length_nil, Nat.shiftRight_zero] at hbit
      omega
    have hn_eq : UInt32.ofNat rem - 1 = UInt32.ofNat (rem - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hrem_pos),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hns1_eq : (5 : UInt32) - UInt32.ofNat (rem - 1) = UInt32.ofNat (5 - (rem - 1)) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (rem - 1)).toNat ≤ 5; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rfl
    have hB0_eq : baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1 =
        B.set! ((ciTab 7 (PS.permCodes 7 7))[encB 7 v]!) 1 := by
      rw [hci_eq, baSetU8_eq_set! (by omega) (by rw [usize_ofNat_toNat (by omega), hB_sz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    have hB0_sz : (baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1).size = sz := by
      rw [baSetU8_size, hB_sz]
    have hB0_inv : MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!)
        (baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1) (used ++ [v]) := by
      rw [hB0_eq]; exact PS.minv_set hM v
    -- Verify okM3 = true and nextS2 + nst match mkState!
    obtain ⟨ub_d, ub_nr, ub_nt, ub_nw3, ub_s1, ub_s2, ub_t3⟩ :=
      mkBaseSt_unpack (d := d) (nr := nr) (nt := nt) (nw3 := nw3) (s1 := s1) (s2 := s2) (t3c := t3c)
        hd hr ht hw3 (by omega) hs2 (by omega)
    rw [walkGo, dif_pos hrem_u, if_neg (by simp [hmk_ne]), if_neg (by simp [h0_ba])]
    dsimp only
    rw [hn_eq, if_pos hbit0, hns1_eq, hbst, ub_nw3]
    have hok_true :
        (if UInt32.ofNat nw3 == 2 && ctx.useM3 then
          let s2p := ((mkBaseSt d nr nt nw3 s1 s2 t3c >>> 38) &&& 255).toUInt32
          let t3c' := ((mkBaseSt d nr nt nw3 s1 s2 t3c >>> 46) &&& 7).toUInt32
          let ns3 := s2p * 30 + t3c' * 6 + UInt32.ofNat (5 - (rem - 1))
          if baGetU8 ctx.m3AllowBA ns3.toUSize == 0 then false
          else
            let nt' := ((mkBaseSt d nr nt nw3 s1 s2 t3c >>> 29) &&& 15).toUInt32
            if nt' == ctx.S then
              let nr' := ((mkBaseSt d nr nt nw3 s1 s2 t3c >>> 21) &&& 255).toUInt32
              let nd := ((mkBaseSt d nr nt nw3 s1 s2 t3c >>> 13) &&& 255).toUInt32 + UInt32.ofNat (rem - 1)
              if nd < ctx.C then nr' > (baGetU8 ctx.u3MinRBA (nd.toUSize * 5400 + ns3.toUSize)).toUInt32
              else false
            else true
        else true) = true := by
      by_cases hcond : (UInt32.ofNat nw3 == 2 && ctx.useM3) = true
      · rw [if_pos hcond]
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        have hnw3_2 : nw3 = 2 := by
          have := congrArg UInt32.toNat hcond.1
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this; exact this
        obtain ⟨hm3_ok, hu3_ok⟩ := hokM3 hnw3_2 hcond.2
        simp only [List.length_nil, Nat.sub_zero] at hm3_ok hu3_ok
        rw [ub_s2, ub_t3, ub_nt, ub_nr, ub_d]
        have hns3_eq : (UInt32.ofNat s2 * 30 + UInt32.ofNat t3c * 6 + UInt32.ofNat (5 - (rem - 1))).toUSize =
            USize.ofNat (s2 * 30 + t3c * 6 + (5 - (rem - 1))) := by
          have hs2n : (UInt32.ofNat s2).toNat = s2 := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          have ht3n : (UInt32.ofNat t3c).toNat = t3c := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          have hnsn : (UInt32.ofNat (5 - (rem - 1))).toNat = 5 - (rem - 1) := by
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          have h30 : (30 : UInt32).toNat = 30 := rfl
          have h6 : (6 : UInt32).toNat = 6 := rfl
          apply USize.toNat_inj.mp
          rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul,
            hs2n, ht3n, hnsn, h30, h6,
            Nat.mod_eq_of_lt (by omega : s2 * 30 < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : t3c * 6 < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : s2 * 30 + t3c * 6 < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : s2 * 30 + t3c * 6 + (5 - (rem - 1)) < 2 ^ 32),
            usize_ofNat_toNat (by omega)]
        dsimp only
        rw [hns3_eq]
        have hm3_f : (baGetU8 ctx.m3AllowBA (USize.ofNat (s2 * 30 + t3c * 6 + (5 - (rem - 1)))) == 0) = false := by
          simpa using hm3_ok
        rw [hm3_f]
        simp only [Bool.false_eq_true, ite_false]
        by_cases hntS : (UInt32.ofNat nt == ctx.S) = true
        · rw [if_pos hntS]
          have hnt_eq : nt = ctx.S.toNat := by
            have := congrArg UInt32.toNat (beq_iff_eq.mp hntS)
            rwa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
          obtain ⟨hndC, hu3lt⟩ := hu3_ok hnt_eq
          have hnd_eq : UInt32.ofNat d + UInt32.ofNat (rem - 1) = UInt32.ofNat (d + (rem - 1)) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          rw [hnd_eq]
          have hnd_lt_C : UInt32.ofNat (d + (rem - 1)) < ctx.C := by
            change (UInt32.ofNat (d + (rem - 1))).toNat < ctx.C.toNat
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hndC
          rw [if_pos hnd_lt_C]
          have hidx_u3 : (UInt32.ofNat (d + (rem - 1))).toUSize * 5400 +
              USize.ofNat (s2 * 30 + t3c * 6 + (5 - (rem - 1))) =
              USize.ofNat ((d + (rem - 1)) * 5400 + (s2 * 30 + t3c * 6 + (5 - (rem - 1)))) := by
            have hnd_u : (UInt32.ofNat (d + (rem - 1))).toNat = d + (rem - 1) := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have h5400 : (5400 : USize).toNat = 5400 := by
              change (USize.ofNat 5400).toNat = 5400; exact usize_ofNat_toNat (by omega)
            apply USize.toNat_inj.mp
            rw [USize.toNat_add, USize.toNat_mul, UInt32.toNat_toUSize, hnd_u, h5400,
              usize_ofNat_toNat (by omega : s2 * 30 + t3c * 6 + (5 - (rem - 1)) < 2 ^ 32),
              Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : (d + (rem - 1)) * 5400 < 2 ^ 32)),
              Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : (d + (rem - 1)) * 5400 + (s2 * 30 + t3c * 6 + (5 - (rem - 1))) < 2 ^ 32)),
              usize_ofNat_toNat (by omega)]
          rw [hidx_u3]
          simp only [decide_eq_true_eq]
          change (baGetU8 ctx.u3MinRBA _).toUInt32.toNat < (UInt32.ofNat nr).toNat
          rw [UInt8.toNat_toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          exact hu3lt
        · rw [if_neg hntS]
      · rw [if_neg hcond]
    rw [if_pos hok_true, ub_s1, ub_t3]
    have hns2_eq : (if UInt32.ofNat nw3 == 0 then (0 : UInt32)
        else UInt32.ofNat s1 * 30 + UInt32.ofNat t3c * 6 + UInt32.ofNat (5 - (rem - 1))) =
        UInt32.ofNat (if nw3 = 0 then 0 else s1 * 30 + t3c * 6 + (5 - (rem - 1))) := by
      by_cases h0 : nw3 = 0
      · subst h0; rfl
      · have hne : (UInt32.ofNat nw3 == 0) = false := by
          simp only [beq_eq_false_iff_ne]
          intro h; apply h0; have := congrArg UInt32.toNat h
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this; exact this
        rw [if_neg (by simp [hne]), if_neg h0]
        have hs1n : (UInt32.ofNat s1).toNat = s1 := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have ht3n : (UInt32.ofNat t3c).toNat = t3c := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have hnsn : (UInt32.ofNat (5 - (rem - 1))).toNat = 5 - (rem - 1) := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        have h30 : (30 : UInt32).toNat = 30 := rfl
        have h6 : (6 : UInt32).toNat = 6 := rfl
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul,
          hs1n, ht3n, hnsn, h30, h6,
          Nat.mod_eq_of_lt (by omega : s1 * 30 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : t3c * 6 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : s1 * 30 + t3c * 6 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : s1 * 30 + t3c * 6 + (5 - (rem - 1)) < 2 ^ 32),
          UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega : s1 * 30 + t3c * 6 + (5 - (rem - 1)) < 2 ^ 32)]
    rw [hns2_eq]
    have hns2_lt : (if nw3 = 0 then 0 else s1 * 30 + t3c * 6 + (5 - (rem - 1))) < 256 := by
      split_ifs <;> omega
    have hnst := mkBaseSt_nextState (d := d) (nr := nr) (nt := nt) (nw3 := nw3)
      (s1 := s1) (s2 := s2) (t3c := t3c) (n := rem - 1) (D := encB 7 v)
      (ns1 := 5 - (rem - 1)) (nextS2 := if nw3 = 0 then 0 else s1 * 30 + t3c * 6 + (5 - (rem - 1)))
      (by simpa using hrem_d) hr ht hw3 (by omega) hs2 (by omega) (by have := permCodes7_length_le; omega)
      (by omega) hns2_lt
    dsimp only at hnst
    rw [hnst]
    have hgo0 := hfin _ hB0_sz hB0_inv
    simp only [List.length_nil, Nat.sub_zero, List.getLast_singleton] at hgo0
    have hgo_us : ((go ctx fuel _ mM _).usize == 0) = true :=
      (ba_usize_eq_zero_iff (by omega)).mpr hgo0
    rw [if_pos hgo_us]
    exact hgo0
  | cons v' R' ih =>
    have hrem_ge2 : 2 ≤ rem := by simp only [List.length_cons] at hR; omega
    have hrem_u : UInt32.ofNat rem > 0 := by
      change 0 < (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    have hmk_ne : (mk == 0) = false := by
      simp only [beq_eq_false_iff_ne]
      intro h0; subst h0; simp at hbit
    have hv := hperm v List.mem_cons_self
    have hv_lt := encB_lt hv
    have hD_us : (UInt32.ofNat (encB 7 v)).toUSize = USize.ofNat (encB 7 v) := by
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
    have hci_eq : (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize =
        USize.ofNat ((ciTab 7 (PS.permCodes 7 7))[encB 7 v]!) := by
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, hciBA, hD_us, tabs_ciBA_get hv, usize_ofNat_toNat (by have := ciTab_lt hv_lt; omega)]
    have hci_lt : (ciTab 7 (PS.permCodes 7 7))[encB 7 v]! < sz := hsz_eq ▸ ciTab_lt hv_lt
    have h0_raw := PS.unmarked_of_new (PS.encB_enc 7 (by omega) (by omega)) hM hused hv
      (fun u hu => hnew u hu v List.mem_cons_self)
    have h0_ba : (baGetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize != 0) = false := by
      rw [hci_eq, baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hB_sz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
      simp [h0_raw]
    have hn_eq : UInt32.ofNat rem - 1 = UInt32.ofNat (rem - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hB0_eq : baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1 =
        B.set! ((ciTab 7 (PS.permCodes 7 7))[encB 7 v]!) 1 := by
      rw [hci_eq, baSetU8_eq_set! (by omega) (by rw [usize_ofNat_toNat (by omega), hB_sz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    have hB0_sz : (baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1).size = sz := by
      rw [baSetU8_size, hB_sz]
    have hB0_inv : MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!)
        (baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1) (used ++ [v]) := by
      rw [hB0_eq]; exact PS.minv_set hM v
    rw [walkGo, dif_pos hrem_u, if_neg (by simp [hmk_ne]), if_neg (by simp [h0_ba]), hn_eq]
    dsimp only
    set B0 := baSetU8 B (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize 1
    have hsub_ite : ∀ {cond : Bool} {X Y : ByteArray},
        SubSz sz X B0 → SubSz sz Y B0 → SubSz sz (if cond then X else Y) B0 := by
      intro cond X Y hX hY; cases cond <;> simp [hX, hY]
    have hbind0 : ∀ {B1 B_else : ByteArray},
        SubSz sz B1 B0 → (B1.size = sz → Sub B1 B0 → B_else.size = 0) →
        (if (B1.usize == 0) = true then B1 else B_else).size = 0 := by
      intro B1 B_else h1 hf
      by_cases hz1 : (B1.usize == 0) = true
      · rw [if_pos hz1]
        exact (ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mp hz1
      · rw [if_neg hz1]
        have hne : B1.size ≠ 0 := fun h0 => hz1 ((ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mpr h0)
        exact hf (h1.1.resolve_left hne) h1.2
    refine hbind0 ?_ (fun hB1_sz hB1_sub => ?_)
    · exact hsub_ite (hsub_ite ((fastK16_subSz ctx sz hsz_u32).1 fuel _ mM B0 hB0_sz) (subSz_refl hB0_sz)) (subSz_refl hB0_sz)
    · have hbit' : ((mk >>> 1).toNat >>> R'.length) % 2 = 1 := by
        rw [UInt32.toNat_shiftRight]
        change (mk.toNat >>> 1 >>> R'.length) % 2 = 1
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          ← Nat.pow_add, show 1 + R'.length = (v' :: R').length by simp; omega, ← Nat.shiftRight_eq_div_pow]
        exact hbit
      have hmk'_ne : (mk >>> 1 != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0; rw [h0] at hbit'; simp at hbit'
      rw [if_pos hmk'_ne]
      obtain ⟨hdc, hdtl⟩ := List.isChain_cons_cons.mp hdoor
      obtain ⟨hpc, hptl⟩ := List.pairwise_cons.mp hpw
      have hnxt_eq : baGetU16 ctx.nxtBA (UInt32.ofNat (encB 7 v)).toUSize = UInt32.ofNat (encB 7 v') := by
        apply UInt32.toNat_inj.mp
        rw [hnxtBA, hD_us, tabs_nxtBA_get hv, (PS.encB_enc 7 (by omega) (by omega)).nxt_eq v v' hv hdc,
          UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := encB_lt (hperm v' (by simp)); omega)]
      rw [hnxt_eq]
      have hrec := ih (rem - 1) (mk >>> 1) v' _ (used ++ [v]) (by omega) (by simp at hR; omega)
        (by simp only [List.length_cons] at hrem_d; omega) hbit'
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdtl hB1_sz (hB0_inv.sub hB1_sub)
        (fun u hu => by
          rcases List.mem_append.mp hu with h | h
          · exact hused u h
          · rw [List.mem_singleton.mp h]; exact hv)
        (fun u hu w hw => by
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]; exact hpc w hw)
        hptl
        (by
          intro hnw3 huse
          have h := hokM3 hnw3 huse
          simp only [List.length_cons] at h
          have heq : rem - 1 - 1 - R'.length = rem - 1 - (R'.length + 1) := by omega
          simpa [heq] using h)
        (by
          intro B' hB'sz hB'inv
          have heq_u : used ++ [v] ++ v' :: R' = used ++ v :: v' :: R' := by simp
          rw [heq_u] at hB'inv
          have hf := hfin B' hB'sz hB'inv
          rw [List.getLast_cons (List.cons_ne_nil v' R')] at hf
          have heq : rem - 1 - 1 - R'.length = rem - 1 - (v' :: R').length := by
            simp only [List.length_cons]; omega
          simpa [heq] using hf)
      have hz2 := (ba_usize_eq_zero_iff (b := walkGo ctx fuel baseSt mM (UInt32.ofNat (rem - 1)) (mk >>> 1) (UInt32.ofNat (encB 7 v')) _) (by rw [hrec]; omega)).mpr hrec
      rw [if_pos hz2]
      exact hrec

/-- Completeness of `loopSucc`: finds `idx = t` among `lim - rem .. lim - 1`. -/
theorem loopSucc_complete {ctx : FastK16Ctx} {sz : ℕ} (hsz_eq : sz = (PS.permCodes 7 7).length)
    (fuel : UInt32) (baseSt mM lArg : UInt64) (sBase : USize)
    (lim mk cq : ℕ) (isS4 : Bool)
    (hlim : lim < 32) (hmk : mk < 64) (hcq : cq < 8192)
    (hlArg : lArg = mkLArg lim mk cq isS4)
    (t : ℕ) (ht_lt : t < lim)
    (P : ByteArray → Prop) (hPsub : ∀ B' B, Sub B' B → P B → P B')
    (hstep : ∀ B, B.size = sz → P B →
      let D := baGetU16 (if isS4 then ctx.s4BA else ctx.s3BA) (sBase + USize.ofNat t)
      let emk0 := if ctx.js && baGetU16 ctx.ciBA D.toUSize == UInt32.ofNat cq then UInt32.ofNat mk &&& 1 else UInt32.ofNat mk
      let emk :=
        if isS4 && ctx.useW4 then
          let prevS1 := ((baseSt >>> 35) &&& 7).toUInt32
          emk0 &&& (baGetU8 ctx.w4AllowBA (prevS1 * 23 + UInt32.ofNat t).toUSize).toUInt32
        else emk0
      emk ≠ 0 ∧
      (walkGo ctx fuel (if isS4 then baseSt else baseSt ||| ((UInt32.ofNat t).toUInt64 <<< 46))
        mM 6 emk D B).size = 0) :
    ∀ (rem : ℕ), lim - t ≤ rem → rem ≤ lim →
    ∀ B, B.size = sz → P B →
      (loopSucc ctx fuel baseSt mM lArg sBase (UInt32.ofNat rem) B).size = 0 := by
  have hsz_le : sz ≤ 5040 := hsz_eq ▸ permCodes7_length_le
  have hsz_u32 : sz < 2 ^ 32 := by omega
  obtain ⟨ulim, umk, ucq, uis4⟩ := mkLArg_unpack hlim hmk hcq (isS4 := isS4)
  intro rem
  induction rem with
  | zero => intro h; omega
  | succ rem ih =>
    intro hge hle B hBsz hPB
    have hrem_pos : UInt32.ofNat (rem + 1) > 0 := by
      change 0 < (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    rw [loopSucc, dif_pos hrem_pos]
    dsimp only
    rw [hlArg, ulim, umk, ucq, uis4]
    have hidx_eq : UInt32.ofNat lim - UInt32.ofNat (rem + 1) = UInt32.ofNat (lim - (rem + 1)) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (rem + 1)).toNat ≤ (UInt32.ofNat lim).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hidx_eq]
    by_cases heq : lim - (rem + 1) = t
    · rw [heq]
      have hus : (UInt32.ofNat t).toUSize = USize.ofNat t := by
        apply USize.toNat_inj.mp; rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
      rw [hus]
      obtain ⟨hemk_ne, hw0⟩ := hstep B hBsz hPB
      have hemk_f :
          ((if (isS4 && ctx.useW4) = true then
              (if (ctx.js && baGetU16 ctx.ciBA (baGetU16 (if isS4 = true then ctx.s4BA else ctx.s3BA) (sBase + USize.ofNat t)).toUSize == UInt32.ofNat cq) = true then
                UInt32.ofNat mk &&& 1 else UInt32.ofNat mk) &&&
                (baGetU8 ctx.w4AllowBA (((baseSt >>> 35) &&& 7).toUInt32 * 23 + UInt32.ofNat t).toUSize).toUInt32
            else
              if (ctx.js && baGetU16 ctx.ciBA (baGetU16 (if isS4 = true then ctx.s4BA else ctx.s3BA) (sBase + USize.ofNat t)).toUSize == UInt32.ofNat cq) = true then
                UInt32.ofNat mk &&& 1 else UInt32.ofNat mk) == 0) = false := beq_false_of_ne hemk_ne
      simp only [hemk_f, Bool.false_eq_true, ite_false]
      have hw_us := (ba_usize_eq_zero_iff (b := walkGo ctx fuel
        (if isS4 = true then baseSt else baseSt ||| (UInt32.ofNat t).toUInt64 <<< 46) mM 6 _ _ B)
        (by rw [hw0]; omega)).mpr hw0
      rw [if_pos hw_us]
      exact hw0
    · have hsub_ite : ∀ {cond : Bool} {X Y : ByteArray},
          SubSz sz X B → SubSz sz Y B → SubSz sz (if cond then X else Y) B := by
        intro cond X Y hX hY; cases cond <;> simp [hX, hY]
      have hbind0 : ∀ {B' B_else : ByteArray},
          SubSz sz B' B → (B'.size = sz → Sub B' B → B_else.size = 0) →
          (if (B'.usize == 0) = true then B' else B_else).size = 0 := by
        intro B' B_else h1 hf
        by_cases hz : (B'.usize == 0) = true
        · rw [if_pos hz]
          exact (ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mp hz
        · rw [if_neg hz]
          have hne : B'.size ≠ 0 := fun h0 => hz ((ba_usize_eq_zero_iff (by rcases h1.1 with h | h <;> omega)).mpr h0)
          exact hf (h1.1.resolve_left hne) h1.2
      refine hbind0 ?_ (fun hB'_sz hB'_sub => ?_)
      · exact hsub_ite (subSz_refl hBsz) ((fastK16_subSz ctx sz hsz_u32).2.2 fuel _ mM 6 _ _ B hBsz)
      · have hsub1 : UInt32.ofNat (rem + 1) - 1 = UInt32.ofNat rem := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hsub1, ← hlArg]
        exact ih (by omega) (by omega) _ hB'_sz (hPsub _ B hB'_sub hPB)

set_option maxHeartbeats 800000 in
/-- Main completeness induction for `FastK16.go` along a full counterexample `pref ++ rest`! -/
theorem go_complete {caps : List (List ℕ)} {s lo hi a b h : ℕ} {js useM3 useW4 : Bool}
    {fuel0 ds nt tp x L_len : ℕ} {ctx : FastK16Ctx}
    (hvc : ValidCtx caps s lo hi a b h js useM3 useW4 fuel0 ds nt tp ctx)
    (hs : s < 15) (hhi : hi < 200) (hR : rowsR caps s hi < 250) (hfuel0 : fuel0 < 256)
    (habh : a ≤ 100 ∧ b ≤ 100 ∧ h ≤ 100) (hnt : 0 < nt ∧ nt < 65536)
    (hlo_x : lo ≤ x) (hx_hi : x ≤ hi) (hLlen_lt : L_len < 250)
    (hcap0 : ∀ rest' : List TRow, rest'.length < L_len → IsSeq 7 rest' → (∀ w ∈ rest', w.1 ≤ 1) →
      linksT rest' = 0 → ∀ y ≤ hi, holesT 7 rest' = y → rest'.length ≤ capF caps 0 y) :
    ∀ (fuel : ℕ) (pref rest : List TRow) (t r d w3 s1 s2 : ℕ) (m M : ℤ)
      (B : ByteArray) (last : List ℕ) (used : List (List ℕ)),
      fuel < 256 →
      pref.length + rest.length = L_len →
      pref.length = r → r < 250 → linksT pref = t → t ≤ s →
      holesT 7 pref = d → d ≤ x →
      linksT (pref ++ rest) = s → holesT 7 (pref ++ rest) = x →
      capF caps s x < L_len →
      IsSeq 7 (pref ++ rest) →
      (useM3 = true → NoM3 (pref ++ rest)) →
      (useW4 = true → NoW4 (pref ++ rest)) →
      (js = true → NoJS 7 (pref ++ rest)) →
      TailInv pref w3 s1 s2 →
      (∃ U R1, pref = U ++ [R1] ∧ ∃ h1 : R1.2 ≠ [], R1.2.getLast h1 = last) →
      -2 ^ 27 ≤ m → m ≤ 2 ^ 27 → -2 ^ 27 ≤ M → M ≤ 2 ^ 27 →
      PermW 7 last → (∀ u ∈ used, PermW 7 u) →
      B.size = (PS.permCodes 7 7).length →
      MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!) B used →
      PCont 7 last used rest →
      KAlong 7 (encB 7) (codeF (capF caps) s lo hi) (potN a b h) (potS a b h)
        (cutF (a1F (capF caps) s lo hi a b h)
          (a2F (uF (capF caps) s a b h) (segF (capF caps) s a b h) (capF caps) s lo hi a b h))
        (fuel0 - ds) nt tp fuel t r d m M last rest →
      (js = true → NoJSAlong 7 last rest) →
      (go ctx (UInt32.ofNat fuel) (mkState (encB 7 last) d r t w3 s1 s2)
        (packMM (Int32.ofInt m) (Int32.ofInt M)) B).size = 0 := by
  have hsz_le := permCodes7_length_le
  have hsz_u32 : (PS.permCodes 7 7).length < 2 ^ 32 := by omega
  intro fuel
  induction fuel with
  | zero =>
    intro pref rest t r d w3 s1 s2 m M B last used _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [go, dif_neg (by decide)]
    exact ByteArray.size_empty
  | succ fuel ih =>
    intro pref rest t r d w3 s1 s2 m M B last used hfuel hLlen hpr hr htl ht hdh hdx
      hLlinks hLholes hLgt hLseq hnoM3 hnoW4 hnoJS htail hlast_pref
      hm1 hm2 hM1 hM2 hlast hused hBsz hM hcont halong hjsA
    have hf_pos : UInt32.ofNat (fuel + 1) > 0 := by
      change 0 < (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    have hlast_lt : encB 7 last < 8192 := by have := encB_lt hlast; omega
    have hw3_lt : w3 < 4 := by have := htail.1; omega
    have hs1_lt : s1 < 8 := by have := htail.2.1; omega
    have hs2_lt : s2 < 256 := by have := htail.2.2.1; omega
    obtain ⟨uq, ud, ur, ut, uw3, us1, us2⟩ := mkState_unpack hlast_lt (by omega : d < 256)
      (by omega : r < 256) (by omega : t < 16) hw3_lt hs1_lt hs2_lt
    have hcode_eq := hvc.hcode t r d ht (by omega) (by omega)
    rw [go, dif_pos hf_pos]
    dsimp only
    rw [uq, ud, ur, ut]
    cases rest with
    | nil =>
      simp only [KAlong] at halong
      have hc_val : getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) = 1 := by
        apply UInt32.toNat_inj.mp; rw [hcode_eq, halong]; rfl
      rw [hc_val]; rfl
    | cons Q rest' =>
      obtain ⟨kd, Q⟩ := Q
      cases Q with
      | nil => exact hcont.elim
      | cons v R =>
        obtain ⟨hRlen, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
        unfold KAlong at halong
        obtain ⟨hkd, hcode_ne, hcut, hgate, hnext, halong'⟩ := halong
        have hcode_u32 : getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) =
            UInt32.ofNat (codeF (capF caps) s lo hi t r d) := by
          apply UInt32.toNat_inj.mp; rw [hcode_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by unfold codeF; split_ifs <;> omega)]
        have hc0 : ¬ getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) = 0 := by
          rw [hcode_u32]; intro h; have := congrArg UInt32.toNat h
          rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by unfold codeF; split_ifs <;> omega)] at this
          rcases hcode_ne with h1 | h1 <;> omega
        have hc1 : ¬ getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) = 1 := by
          rw [hcode_u32]; intro h; have := congrArg UInt32.toNat h
          rw [UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by unfold codeF; split_ifs <;> omega)] at this
          rcases hcode_ne with h1 | h1 <;> omega
        rw [if_neg (by simp [hc0]), if_neg (by simp [hc1])]
        have hsub1 : UInt32.ofNat (fuel + 1) - 1 = UInt32.ofNat fuel := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hsub1]
        have hgate_u : (UInt32.ofNat fuel != ctx.fg ||
            (UInt32.ofNat (encB 7 last) + 8192 * UInt32.ofNat d) % ctx.nt == ctx.tp) = true := by
          rw [hvc.hfg, hvc.hnt, hvc.htp]
          rcases hgate with hfg | htp
          · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
            left
            intro h; apply hfg
            have := congrArg UInt32.toNat h
            rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)] at this
            exact this
          · simp only [Bool.or_eq_true, beq_iff_eq]
            right
            have hlast_u : (UInt32.ofNat (encB 7 last)).toNat = encB 7 last := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have hd_u : (UInt32.ofNat d).toNat = d := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have hnt_u : (UInt32.ofNat nt).toNat = nt := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have htp_u : (UInt32.ofNat tp).toNat = tp := by
              have htp_lt : tp < nt := by
                have := Nat.mod_lt (encB 7 last + 8192 * d) hnt.1; omega
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            have h8192 : (8192 : UInt32).toNat = 8192 := rfl
            have hsum : (UInt32.ofNat (encB 7 last) + 8192 * UInt32.ofNat d).toNat = encB 7 last + 8192 * d := by
              rw [UInt32.toNat_add, UInt32.toNat_mul, hlast_u, hd_u, h8192,
                Nat.mod_eq_of_lt (by omega : 8192 * d < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : encB 7 last + 8192 * d < 2 ^ 32)]
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_mod, hsum, hnt_u, htp_u]
            exact htp
        rw [if_pos hgate_u]
        rw [uw3, us1, us2]
        obtain ⟨umm, uMM⟩ := packMM_unpack (Int32.ofInt m) (Int32.ofInt M)
        rw [umm, uMM, hvc.hpa, hvc.hpb, hvc.hph2, hvc.hph, hvc.hjs, hvc.hb2CiBA]
        have h_ar : (0 : ℤ) ≤ (a : ℤ) * r ∧ (a : ℤ) * r ≤ 25000 := by
          have ha : (a : ℤ) ≤ 100 := by exact_mod_cast habh.1
          exact ⟨by positivity, le_trans (mul_le_mul ha (by omega : (r : ℤ) ≤ 250) (by positivity) (by norm_num)) (by norm_num)⟩
        have h_bd : (0 : ℤ) ≤ (b : ℤ) * d ∧ (b : ℤ) * d ≤ 20000 := by
          have hb : (b : ℤ) ≤ 100 := by exact_mod_cast habh.2.1
          exact ⟨by positivity, le_trans (mul_le_mul hb (by omega : (d : ℤ) ≤ 200) (by positivity) (by norm_num)) (by norm_num)⟩
        have h_ht : (0 : ℤ) ≤ (2 * h : ℤ) * t ∧ (2 * h : ℤ) * t ≤ 3000 := by
          have hh : (h : ℤ) ≤ 100 := by exact_mod_cast habh.2.2
          exact ⟨by positivity, le_trans (mul_le_mul (by omega : (2 * h : ℤ) ≤ 200) (by omega : (t : ℤ) ≤ 15) (by positivity) (by norm_num)) (by norm_num)⟩
        have hfBase_eq : Int32.ofInt a * (UInt32.ofNat r).toInt32 - Int32.ofInt b * (UInt32.ofNat d).toInt32 -
            Int32.ofInt (2 * h) * (UInt32.ofNat t).toInt32 = Int32.ofInt (potN a b h t r d) := by
          rw [u32_toInt32_ofNat (by omega), u32_toInt32_ofNat (by omega), u32_toInt32_ofNat (by omega),
            int32_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int32_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int32_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int32_ofInt_sub (by omega) (by omega) (by omega) (by omega),
            int32_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
          congr 1
        rw [hfBase_eq]
        have hpotN_bd : -2 ^ 20 ≤ potN a b h t r d ∧ potN a b h t r d ≤ 2 ^ 20 := by
          unfold potN; push_cast; constructor <;> linarith
        have hpotS_bd : -2 ^ 20 ≤ potS a b h t r d ∧ potS a b h t r d ≤ 2 ^ 20 := by
          unfold potS potN; push_cast
          have : (0 : ℤ) ≤ h ∧ (h : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.2⟩
          constructor <;> linarith
        have hcq_eq : (if js then baGetU16 buildS7K16Tabs.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 0) =
            UInt32.ofNat (if js then (ciTab 7 (PS.permCodes 7 7))[(nxtTab 7 (PS.permCodes 7 7))[encB 7 last]!]! else 0) := by
          cases js
          · rfl
          · apply UInt32.toNat_inj.mp
            have hus : (UInt32.ofNat (encB 7 last)).toUSize = USize.ofNat (encB 7 last) := by
              apply USize.toNat_inj.mp; rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
            rw [if_pos rfl, if_pos rfl, hus, tabs_b2CiBA_get hlast, UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by have := ciTab_lt (nxtTab_lt (encB_lt hlast)); omega)]
        rw [hcq_eq]
        set cqN := if js then (ciTab 7 (PS.permCodes 7 7))[(nxtTab 7 (PS.permCodes 7 7))[encB 7 last]!]! else 0
        have hcq_lt : cqN < 8192 := by
          cases js
          · simp [cqN]
          · simp only [cqN, ite_true]; have := ciTab_lt (nxtTab_lt (encB_lt hlast)); omega
        have hv : PermW 7 v := hperm v List.mem_cons_self
        have hused' : ∀ u ∈ used ++ v :: R, PermW 7 u := by
          intro u hu
          rcases List.mem_append.mp hu with h | h
          · exact hused u h
          · exact hperm u h
        have hR_lt6 : R.length < 6 := by omega
        have hnr_eq : UInt32.ofNat r + 1 = UInt32.ofNat (r + 1) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_one, UInt32.toNat_ofNat',
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hnt_eq : UInt32.ofNat t + 1 = UInt32.ofNat (t + 1) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_one, UInt32.toNat_ofNat',
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hrot_ne : ¬ last ~r v := by
          obtain ⟨U0, R1, hU0, h1ne, hlast_eq⟩ := hlast_pref
          have hinf : IsSeq 7 [R1, (kd, v :: R)] :=
            hLseq.infix ⟨U0, rest', by rw [hU0]; simp⟩
          have hcl := hinf.classes
          simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.pairwise_append] at hcl
          rw [← hlast_eq]
          exact hcl.2.2 _ (List.getLast_mem h1ne) _ List.mem_cons_self
        have hjs1 : js = true → R ≠ [] → ¬ v ~r tau2 7 last := fun h => (hjsA h).1
        have hjs2 : js = true → NoJSAlong 7 ((v :: R).getLast (List.cons_ne_nil v R)) rest' := fun h => (hjsA h).2
        have hpref_next_eq : (pref ++ [(kd, v :: R)]) ++ rest' = pref ++ (kd, v :: R) :: rest' := by simp
        have hpref_holes : holesT 7 (pref ++ [(kd, v :: R)]) = d + (5 - R.length) := by
          rw [PS.holesT_append, hdh]; simp [holesT]
        have hpref_links : linksT (pref ++ [(kd, v :: R)]) = t + kd := by
          obtain ⟨U0, R1, hU0, _, _⟩ := hlast_pref
          have hne : pref ≠ [] := by rw [hU0]; simp
          rw [← htl, PS.linksT_append pref (kd, v :: R) [] hne]
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with h0 | h1k
          · simp [h0, linksT]
          · simp [h1k, linksT]
        have hnew_d_le_x : d + (5 - R.length) ≤ x := by
          have h1 : holesT 7 (pref ++ [(kd, v :: R)]) + holesT 7 rest' = x := by
            rw [← PS.holesT_append, hpref_next_eq, hLholes]
          omega
        have hnew_t_le_s : t + kd ≤ s := by
          have h1 := congrArg linksT hpref_next_eq
          rw [hLlinks] at h1
          have hle := KS.linksT_le_right (pref ++ [(kd, v :: R)]) rest'
          omega
        have hnew_r_lt : r + 1 < 250 := by simp only [List.length_cons] at hLlen; omega
        have hjs_bit : ∀ mk : UInt32, (mk.toNat >>> R.length) % 2 = 1 →
            ((if js && baGetU16 buildS7K16Tabs.ciBA (UInt32.ofNat (encB 7 v)).toUSize == UInt32.ofNat cqN
              then mk &&& 1 else mk).toNat >>> R.length) % 2 = 1 := by
          intro mk hmkb
          by_cases hj : (js && baGetU16 buildS7K16Tabs.ciBA (UInt32.ofNat (encB 7 v)).toUSize == UInt32.ofNat cqN) = true
          · rw [if_pos hj]
            simp only [Bool.and_eq_true, beq_iff_eq] at hj
            have hRnil : R = [] := by
              by_contra hRne
              apply hjs1 hj.1 hRne
              have hus : (UInt32.ofNat (encB 7 v)).toUSize = USize.ofNat (encB 7 v) := by
                apply USize.toNat_inj.mp; rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := encB_lt hv; omega), usize_ofNat_toNat (by have := encB_lt hv; omega)]
              have hci := congrArg UInt32.toNat hj.2
              rw [hus, tabs_ciBA_get hv, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hci
              simp only [cqN, hj.1, ite_true] at hci
              have hnxt := (PS.encB_enc 7 (by omega) (by omega)).nxt_eq last (tau2 7 last) hlast rfl
              rw [hnxt] at hci
              exact (PS.encB_enc 7 (by omega) (by omega)).ci_inj v (tau2 7 last) hv (permW_tau2 (by omega) hlast) hci
            subst hRnil
            simp only [List.length_nil, Nat.shiftRight_zero, UInt32.toNat_and, UInt32.toNat_one, Nat.and_one_is_mod] at hmkb ⊢
            omega
          · rw [if_neg hj]; exact hmkb
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
        · -- Case kd = 0 (weight-3 link)
          have hc_ne3 : (getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) != 3) = true := by
            rw [hcode_u32]; simp only [bne_iff_ne, ne_eq]
            intro h; have := congrArg UInt32.toNat h
            rw [UInt32.toNat_ofNat', show (3 : UInt32).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by unfold codeF; split_ifs <;> omega)] at this
            rcases hcode_ne with h1 | h1 <;> omega
          have hmN_eq : (if Int32.ofInt (potN a b h t r d) < Int32.ofInt m then Int32.ofInt (potN a b h t r d) else Int32.ofInt m) =
              Int32.ofInt (min m (potN a b h t r d)) := by
            by_cases hlt : potN a b h t r d < m
            · rw [if_pos (by rw [int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_right (le_of_lt hlt)]
            · rw [if_neg (by rw [int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_left (by omega)]
          have hMN_eq : (if Int32.ofInt (potN a b h t r d) > Int32.ofInt M then Int32.ofInt (potN a b h t r d) else Int32.ofInt M) =
              Int32.ofInt (max M (potN a b h t r d)) := by
            by_cases hgt' : M < potN a b h t r d
            · rw [if_pos (by rw [gt_iff_lt, int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hgt'),
                max_eq_right (le_of_lt hgt')]
            · rw [if_neg (by rw [gt_iff_lt, int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hgt'),
                max_eq_left (by omega)]
          have hcut_u : checkCut ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
              (Int32.ofInt (min m (potN a b h t r d))) (Int32.ofInt (max M (potN a b h t r d))) = true :=
            hvc.hcut t r d _ _ ht (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simpa [fK] using hcut)
          have hmk_bit := hvc.hmask t (r + 1) d R.length ht (by omega) (by omega) hR_lt6 (by simpa using hnext)
          set mkN := getMask ctx (UInt32.ofNat t) (UInt32.ofNat (r + 1)) (UInt32.ofNat d)
          have hmkN_lt : mkN.toNat < 64 := hvc.hmask_lt t (r + 1) d ht (by omega) (by omega)
          have hmkN_ne : (mkN == 0) = false := by
            simp only [beq_eq_false_iff_ne]; intro h0; rw [h0] at hmk_bit; simp at hmk_bit
          have hnw3_eq : (if UInt32.ofNat w3 < 2 then UInt32.ofNat w3 + 1 else 2) = UInt32.ofNat (if w3 < 2 then w3 + 1 else 2) := by
            have hw3_le := htail.1
            match w3, hw3_le with | 0, _ | 1, _ | 2, _ => rfl
          set nw3 := if w3 < 2 then w3 + 1 else 2
          obtain ⟨t3, ht3, hv_step⟩ := w3Step_complete hlast hv (hlink.1 rfl) hrot_ne
          have hbase_eq : ((UInt32.ofNat d).toUInt64 <<< 13) ||| ((UInt32.ofNat (r + 1)).toUInt64 <<< 21) |||
              ((UInt32.ofNat t).toUInt64 <<< 29) ||| ((UInt32.ofNat nw3).toUInt64 <<< 33) |||
              ((UInt32.ofNat s1).toUInt64 <<< 35) ||| ((UInt32.ofNat s2).toUInt64 <<< 38) =
              mkBaseSt d (r + 1) t nw3 s1 s2 0 := by
            unfold mkBaseSt
            apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
            simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
            rw [u64_field_getLsbD (val := 0) (sh := (46 : UInt64)) (w := 3) (by omega) (by omega) (by decide) (by decide) j hj,
              Nat.zero_testBit, Bool.and_false, Bool.or_false]
          have hlArg_eq : ((5 : UInt64) <<< 5) ||| (mkN.toUInt64 <<< 10) ||| ((UInt32.ofNat cqN).toUInt64 <<< 16) =
              mkLArg 5 mkN.toNat cqN false := by
            unfold mkLArg
            have hmk_eq : UInt32.ofNat mkN.toNat = mkN := UInt32.ofNat_toNat
            rw [hmk_eq, if_neg (by decide)]
            apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
            simp [UInt64.toBitVec_or, BitVec.getLsbD_or]
          have hB1_zero : (loopSucc ctx (UInt32.ofNat fuel) (mkBaseSt d (r + 1) t nw3 s1 s2 0)
              (packMM (Int32.ofInt (min m (potN a b h t r d))) (Int32.ofInt (max M (potN a b h t r d))))
              (mkLArg 5 mkN.toNat cqN false) ((UInt32.ofNat (encB 7 last)).toUSize * 5) 5 B).size = 0 := by
            apply loopSucc_complete rfl (UInt32.ofNat fuel) _ _ _ _ 5 mkN.toNat cqN false
              (by omega) hmkN_lt hcq_lt rfl t3 ht3
              (fun B' => MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!) B' used)
              (fun B' B hs hB => hB.sub hs) ?_ 5 (by omega) (by omega) B hBsz hM
            intro B' hB'sz hB'inv
            have hsBase_add : (UInt32.ofNat (encB 7 last)).toUSize * 5 + USize.ofNat t3 =
                USize.ofNat (encB 7 last * 5 + t3) := by
              have hlast_u : (UInt32.ofNat (encB 7 last)).toNat = encB 7 last := by
                rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
              have h5 : (5 : USize).toNat = 5 := by change (USize.ofNat 5).toNat = 5; exact usize_ofNat_toNat (by omega)
              apply USize.toNat_inj.mp
              rw [USize.toNat_add, USize.toNat_mul, UInt32.toNat_toUSize, hlast_u, h5,
                usize_ofNat_toNat (by omega : t3 < 2 ^ 32),
                Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 last * 5 < 2 ^ 32)),
                Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 last * 5 + t3 < 2 ^ 32)),
                usize_ofNat_toNat (by omega)]
            have hD_eq : baGetU16 ctx.s3BA ((UInt32.ofNat (encB 7 last)).toUSize * 5 + USize.ofNat t3) =
                UInt32.ofNat (encB 7 v) := by
              apply UInt32.toNat_inj.mp
              rw [hvc.hs3BA, hsBase_add, tabs_s3BA_get hlast ht3, ← hv_step, UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := encB_lt hv; omega)]
            have hwBase_eq : mkBaseSt d (r + 1) t nw3 s1 s2 0 ||| ((UInt32.ofNat t3).toUInt64 <<< 46) =
                mkBaseSt d (r + 1) t nw3 s1 s2 t3 := by
              unfold mkBaseSt
              apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
              simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
              rw [u64_field_getLsbD (val := 0) (sh := (46 : UInt64)) (w := 3) (by omega) (by omega) (by decide) (by decide) j hj,
                Nat.zero_testBit, Bool.and_false, Bool.or_false]
            have hmk_eq : UInt32.ofNat mkN.toNat = mkN := UInt32.ofNat_toNat
            simp only [Bool.false_eq_true, ite_false, Bool.false_and, hD_eq, hmk_eq, hvc.hjs, hvc.hciBA, hwBase_eq]
            have hemk_bit := hjs_bit mkN hmk_bit
            have hnw3_lt : nw3 < 4 := by dsimp [nw3]; split_ifs <;> omega
            refine ⟨fun h0 => by rw [h0] at hemk_bit; simp at hemk_bit, ?_⟩
            apply walkGo_complete rfl hvc.hciBA hvc.hnxtBA (UInt32.ofNat fuel)
              (mkBaseSt d (r + 1) t nw3 s1 s2 t3) _ d (r + 1) t nw3 s1 s2 t3
              (by omega) (by omega) (by omega) hnw3_lt (by have := htail.2.1; omega)
              (by have := htail.2.2.1; omega) (by omega) rfl R 6 _ v B' used
              (by omega) hR_lt6 (by omega) hemk_bit hperm hdoor hB'sz hB'inv hused hnew hpw ?_ ?_
            · intro hnw3_2 huseM3
              have hw3_ge1 : 1 ≤ w3 := by dsimp [nw3] at hnw3_2; split_ifs at hnw3_2 <;> omega
              obtain ⟨U0, R0, R1, t0, h0ne, h1ne, hpref_eq, hR1k, ht0, hstep1, hs2_eq⟩ := htail.2.2.2.2 hw3_ge1
              obtain ⟨U1, R1', hU1, h1ne', hlast_eq⟩ := hlast_pref
              have hR1_eq : R1' = R1 := by
                have h1 : U1 ++ [R1'] = (U0 ++ [R0]) ++ [R1] := by rw [← hU1, hpref_eq]; simp
                exact (List.append_inj_right' h1 rfl |> List.cons.inj).1
              subst R1'
              have hns3_eq : s2 * 30 + t3 * 6 + (5 - (6 - 1 - R.length)) =
                  ((R0.2.length - 1) * 30 + t0 * 6 + (R1.2.length - 1)) * 30 + t3 * 6 + ((0, v :: R).2.length - 1) := by
                simp only [hs2_eq, List.length_cons]; omega
              have hm3_match : matchesM3Idx R0 R1 (0, v :: R) (s2 * 30 + t3 * 6 + (5 - (6 - 1 - R.length))) :=
                ⟨hR1k, rfl, t0, t3, h0ne, h1ne, List.cons_ne_nil v R, ht0, ht3, hstep1,
                  by simpa [hlast_eq] using hv_step, hns3_eq⟩
              have hL_split : pref ++ (0, v :: R) :: rest' = U0 ++ [R0, R1, (0, v :: R)] ++ rest' := by
                rw [hpref_eq]; simp
              have hm3_ne0 : buildM3Allow.get! (s2 * 30 + t3 * 6 + (5 - (6 - 1 - R.length))) ≠ 0 :=
                hnoM3 (by rw [← hvc.hM3]; exact huseM3) U0 R0 R1 (0, v :: R) rest' _ hL_split hm3_match
              have hns3_lt : s2 * 30 + t3 * 6 + (5 - (6 - 1 - R.length)) < 5400 := by
                have := htail.2.2.1; omega
              refine ⟨?_, ?_⟩
              · rw [hvc.hm3BA (by rw [← hvc.hM3]; exact huseM3)]
                have hba_sz : buildM3Allow.size = 5400 := by
                  have hfold_sz : ∀ (l : List (ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ))) (b : ByteArray),
                      (l.foldl (fun ba (l0, t0, l1, t1, l2, _) =>
                        ba.set! (((l0 - 1) * 30 + t0 * 6 + (l1 - 1)) * 30 + t1 * 6 + (l2 - 1)) 0) b).size = b.size := by
                    intro l; induction l with
                    | nil => intro _; rfl
                    | cons _ tl iht => intro b; simp only [List.foldl_cons]; rw [iht, ByteArray.size_set!]
                  rw [buildM3Allow, hfold_sz]; simp [ByteArray.size]
                rw [baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hba_sz]; exact hns3_lt),
                  usize_ofNat_toNat (by omega)]
                simp [hm3_ne0]
              · intro htS
                rw [hvc.hS, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at htS
                rw [hvc.hC, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
                refine ⟨by omega, ?_⟩
                rw [hvc.hu3BA (by rw [← hvc.hM3]; exact huseM3)]
                have hw3_rest : ∀ y ∈ rest', y.1 = 0 := by
                  have hlk_all := hLlinks
                  rw [← hpref_next_eq] at hlk_all
                  cases rest' with
                  | nil => simp
                  | cons y0 ys =>
                    have h1 := PS.linksT_append (pref ++ [(0, v :: R)]) y0 ys (by simp)
                    rw [hpref_links, htS, Nat.add_zero] at h1
                    have hy0_0 : y0.1 = 0 := by
                      by_contra hne; simp [hne] at h1; omega
                    have hys_0 : linksT (y0 :: ys) = 0 := by simp [hy0_0] at h1; omega
                    simp only [linksT, List.tail_cons, List.countP_eq_zero] at hys_0
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hys
                    · exact hy0_0
                    · have := hys_0 y hys; simp at this; exact this
                have htail_seq : IsSeq 7 (R0 :: R1 :: (0, v :: R) :: rest') :=
                  hLseq.infix ⟨U0, [], by rw [hL_split]; simp⟩
                have htail_M3 : NoM3 (R0 :: R1 :: (0, v :: R) :: rest') :=
                  fun U' A B C W' idx heq hm => hnoM3 (by rw [← hvc.hM3]; exact huseM3) (U0 ++ U') A B C W' idx
                    (by rw [hL_split]; simpa [List.append_assoc] using congrArg (U0 ++ ·) heq) hm
                have htail_JS : js = true → NoJS 7 (R0 :: R1 :: (0, v :: R) :: rest') :=
                  fun hj U' A B W' heq hbad => hnoJS hj (U0 ++ U') A B W'
                    (by rw [hL_split]; simpa [List.append_assoc] using congrArg (U0 ++ ·) heq) hbad
                have hrest_holes : holesT 7 rest' = x - (d + (6 - 1 - R.length)) := by
                  have h1 : holesT 7 (pref ++ [(0, v :: R)]) + holesT 7 rest' = x := by
                    rw [← PS.holesT_append, hpref_next_eq, hLholes]
                  rw [hpref_holes] at h1; omega
                have hrest_len_lt : rest'.length ≤ L_len - 1 := by
                  simp only [List.length_cons] at hLlen; omega
                exact u3MinR_lt_nr (maxLen := L_len - 1) (lo := lo) (hi := hi)
                  (nd := d + (6 - 1 - R.length)) (nr := r + 1)
                  (ns3 := s2 * 30 + t3 * 6 + (5 - (6 - 1 - R.length))) (x := x)
                  hhi (by omega) hlo_x hx_hi (by omega) hns3_lt
                  (fun r' hr' h1 h2 h3 y hy_hi hy => hcap0 r' (by omega) h1 h2 h3 y hy_hi hy)
                  hrest_len_lt htail_seq htail_M3 htail_JS hw3_rest hrest_holes hm3_match
                  (by simp only [List.length_cons] at hLlen; omega)
            · intro B'' hB''sz hB''inv
              have hnw3_ne0 : nw3 ≠ 0 := by
                have hdef : nw3 = if w3 < 2 then w3 + 1 else 2 := rfl
                rw [hdef]; split_ifs <;> omega
              have hns1_eq : 5 - (6 - 1 - R.length) = (0, v :: R).2.length - 1 := by simp; omega
              simp only [hnw3_ne0, ite_false, hns1_eq]
              have htail' : TailInv (pref ++ [(0, v :: R)]) nw3 ((0, v :: R).2.length - 1)
                  (s1 * 30 + t3 * 6 + ((0, v :: R).2.length - 1)) := by
                obtain ⟨U0, R1, hU0, h1ne, hlast_eq⟩ := hlast_pref
                exact tailInv_w3 htail ⟨U0, hU0⟩ h1ne (List.cons_ne_nil v R) (by simp; omega) rfl ht3
                  (by simpa [hlast_eq] using hv_step)
              have hnext_d : d + (6 - 1 - R.length) = d + (5 - R.length) := rfl
              rw [hnext_d]
              exact ih (pref ++ [(0, v :: R)]) rest' t (r + 1) (d + (5 - R.length)) nw3
                ((0, v :: R).2.length - 1) (s1 * 30 + t3 * 6 + ((0, v :: R).2.length - 1))
                (min m (potN a b h t r d)) (max M (potN a b h t r d)) B''
                ((v :: R).getLast (List.cons_ne_nil v R)) (used ++ v :: R)
                (by omega) (by simp at hLlen ⊢; omega) (by simp [hpr]) hnew_r_lt
                (by simpa using hpref_links) ht hpref_holes hnew_d_le_x
                (by rw [hpref_next_eq]; exact hLlinks) (by rw [hpref_next_eq]; exact hLholes) hLgt
                (by rw [hpref_next_eq]; exact hLseq)
                (fun hm => by rw [hpref_next_eq]; exact hnoM3 hm)
                (fun hw => by rw [hpref_next_eq]; exact hnoW4 hw)
                (fun hj => by rw [hpref_next_eq]; exact hnoJS hj)
                htail' ⟨pref, (0, v :: R), rfl, List.cons_ne_nil v R, rfl⟩
                (by omega) (by omega) (by omega) (by omega)
                (hperm _ (List.getLast_mem _)) hused' hB''sz hB''inv hcont'
                (by simpa [fK] using halong') hjs2
          have hmkN_def : getMask ctx (UInt32.ofNat t) (UInt32.ofNat (r + 1)) (UInt32.ofNat d) = mkN := rfl
          simp only [hc_ne3, ite_true, hmN_eq, hMN_eq, hcut_u, hnr_eq, hmkN_def, hmkN_ne, Bool.false_eq_true,
            ite_false, hnw3_eq, hbase_eq, hlArg_eq]
          rw [if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hB1_zero)]
          exact hB1_zero
        · -- Case kd = 1 (weight-4 link)
          have hbind0 : ∀ {B1 : ByteArray} (f : ByteArray → ByteArray),
              SubSz (PS.permCodes 7 7).length B1 B →
              (∀ B1', B1'.size = (PS.permCodes 7 7).length → Sub B1' B → (f B1').size = 0) →
              (if (B1.usize == 0) = true then B1 else f B1).size = 0 := by
            intro B1 f hsub helse
            by_cases hz : (B1.usize == 0) = true
            · rw [if_pos hz]
              exact (ba_usize_eq_zero_iff (by rcases hsub.1 with h | h <;> omega)).mp hz
            · rw [if_neg hz]
              have hne : B1.size ≠ 0 := fun h0 =>
                hz ((ba_usize_eq_zero_iff (by rcases hsub.1 with h | h <;> omega)).mpr h0)
              exact helse B1 (hsub.1.resolve_left hne) hsub.2
          have hsub_ite : ∀ {c : Prop} [Decidable c] {X Y : ByteArray},
              SubSz (PS.permCodes 7 7).length X B → SubSz (PS.permCodes 7 7).length Y B →
              SubSz (PS.permCodes 7 7).length (if c then X else Y) B := by
            intro c _ X Y hX hY; by_cases hc : c <;> simp [hc, hX, hY]
          apply hbind0 (fun B1 =>
            if (getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) != 2) = true then
              let g := Int32.ofInt (potN a b h t r d) - Int32.ofInt h
              let mS := if g < Int32.ofInt m then g else Int32.ofInt m
              let MS := if g > Int32.ofInt M then g else Int32.ofInt M
              if checkCut ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) mS MS = true then
                let nt1 := UInt32.ofNat t + 1
                let nr := UInt32.ofNat r + 1
                let mk := getMask ctx nt1 nr (UInt32.ofNat d)
                if (mk == 0) = true then B1
                else
                  let baseSt := ((UInt32.ofNat d).toUInt64 <<< 13) ||| (nr.toUInt64 <<< 21) |||
                    (nt1.toUInt64 <<< 29) ||| ((UInt32.ofNat s1).toUInt64 <<< 35)
                  let lArg := ((23 : UInt64) <<< 5) ||| (mk.toUInt64 <<< 10) |||
                    ((UInt32.ofNat cqN).toUInt64 <<< 16) ||| ((1 : UInt64) <<< 29)
                  loopSucc ctx (UInt32.ofNat fuel) baseSt (packMM mS MS) lArg
                    ((UInt32.ofNat (encB 7 last)).toUSize * 23) 23 B1
              else B1
            else B1)
          · apply hsub_ite _ (subSz_refl hBsz)
            apply hsub_ite _ (subSz_refl hBsz)
            apply hsub_ite (subSz_refl hBsz)
            exact (fastK16_subSz ctx (PS.permCodes 7 7).length hsz_u32).2.1 (UInt32.ofNat fuel) _ _ _ _ 5 B hBsz
          · intro B1 hB1_sz' hB1_sub'
            dsimp only
            have hc_ne2 : (getCode ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) != 2) = true := by
              rw [hcode_u32]; simp only [bne_iff_ne, ne_eq]
              intro h; have := congrArg UInt32.toNat h
              rw [UInt32.toNat_ofNat', show (2 : UInt32).toNat = 2 from rfl,
                Nat.mod_eq_of_lt (by unfold codeF; split_ifs <;> omega)] at this
              rcases hcode_ne with h1 | h1 <;> omega
            have hg_eq : Int32.ofInt (potN a b h t r d) - Int32.ofInt h = Int32.ofInt (potS a b h t r d) := by
              rw [int32_ofInt_sub (by omega) (by omega) (by omega) (by omega)]; rfl
            have hmS_eq : (if Int32.ofInt (potS a b h t r d) < Int32.ofInt m then Int32.ofInt (potS a b h t r d) else Int32.ofInt m) =
                Int32.ofInt (min m (potS a b h t r d)) := by
              by_cases hlt : potS a b h t r d < m
              · rw [if_pos (by rw [int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hlt),
                  min_eq_right (le_of_lt hlt)]
              · rw [if_neg (by rw [int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hlt),
                  min_eq_left (by omega)]
            have hMS_eq : (if Int32.ofInt (potS a b h t r d) > Int32.ofInt M then Int32.ofInt (potS a b h t r d) else Int32.ofInt M) =
                Int32.ofInt (max M (potS a b h t r d)) := by
              by_cases hgt' : M < potS a b h t r d
              · rw [if_pos (by rw [gt_iff_lt, int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hgt'),
                  max_eq_right (le_of_lt hgt')]
              · rw [if_neg (by rw [gt_iff_lt, int32_lt_iff_toInt, int32_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt (by omega) (by omega)]; exact hgt'),
                  max_eq_left (by omega)]
            have hcut_u : checkCut ctx (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
                (Int32.ofInt (min m (potS a b h t r d))) (Int32.ofInt (max M (potS a b h t r d))) = true :=
              hvc.hcut t r d _ _ ht (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simpa [fK] using hcut)
            have hmk_bit := hvc.hmask (t + 1) (r + 1) d R.length hnew_t_le_s (by omega) (by omega) hR_lt6 (by simpa using hnext)
            let mkS := getMask ctx (UInt32.ofNat (t + 1)) (UInt32.ofNat (r + 1)) (UInt32.ofNat d)
            have hmkS_def : getMask ctx (UInt32.ofNat (t + 1)) (UInt32.ofNat (r + 1)) (UInt32.ofNat d) = mkS := rfl
            have hmkS_lt : mkS.toNat < 64 := hvc.hmask_lt (t + 1) (r + 1) d hnew_t_le_s (by omega) (by omega)
            have hmkS_ne : (mkS == 0) = false := by
              simp only [beq_eq_false_iff_ne]; intro h0; change (mkS.toNat >>> R.length) % 2 = 1 at hmk_bit; rw [h0] at hmk_bit; simp at hmk_bit
            obtain ⟨t4, ht4, hv_step⟩ := w4Step_complete hlast hv (hlink.2 rfl) hrot_ne
            have hbase_eq : ((UInt32.ofNat d).toUInt64 <<< 13) ||| ((UInt32.ofNat (r + 1)).toUInt64 <<< 21) |||
                ((UInt32.ofNat (t + 1)).toUInt64 <<< 29) ||| ((UInt32.ofNat s1).toUInt64 <<< 35) =
                mkBaseSt d (r + 1) (t + 1) 0 s1 0 0 := by
              unfold mkBaseSt
              apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
              simp only [UInt64.toBitVec_or, BitVec.getLsbD_or,
                u64_field_getLsbD (val := 0) (sh := (33 : UInt64)) (w := 2) (by omega) (by omega) (by decide) (by decide) j hj,
                u64_field_getLsbD (val := 0) (sh := (38 : UInt64)) (w := 8) (by omega) (by omega) (by decide) (by decide) j hj,
                u64_field_getLsbD (val := 0) (sh := (46 : UInt64)) (w := 3) (by omega) (by omega) (by decide) (by decide) j hj,
                Nat.zero_testBit, Bool.and_false, Bool.or_false, Bool.false_or]
            have hlArg_eq : ((23 : UInt64) <<< 5) ||| (mkS.toUInt64 <<< 10) |||
                ((UInt32.ofNat cqN).toUInt64 <<< 16) ||| ((1 : UInt64) <<< 29) =
                mkLArg 23 mkS.toNat cqN true := by
              unfold mkLArg
              have hmk_eq : UInt32.ofNat mkS.toNat = mkS := UInt32.ofNat_toNat
              rw [hmk_eq, if_pos rfl]; rfl
            simp only [hc_ne2, ite_true, hg_eq, hmS_eq, hMS_eq, hcut_u, hnt_eq, hnr_eq, hmkS_def, hmkS_ne,
              Bool.false_eq_true, ite_false, hbase_eq, hlArg_eq]
            apply loopSucc_complete rfl (UInt32.ofNat fuel) _ _ _ _ 23 mkS.toNat cqN true
              (by omega) hmkS_lt hcq_lt rfl t4 ht4
              (fun B' => MInv (encB 7) (fun i => (ciTab 7 (PS.permCodes 7 7))[i]!) B' used)
              (fun B' B hs hB => hB.sub hs) ?_ 23 (by omega) (by omega) B1 hB1_sz' (hM.sub hB1_sub')
            intro B' hB'sz hB'inv
            have hsBase_add : (UInt32.ofNat (encB 7 last)).toUSize * 23 + USize.ofNat t4 =
                USize.ofNat (encB 7 last * 23 + t4) := by
              have hlast_u : (UInt32.ofNat (encB 7 last)).toNat = encB 7 last := by
                rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
              have h23 : (23 : USize).toNat = 23 := by change (USize.ofNat 23).toNat = 23; exact usize_ofNat_toNat (by omega)
              apply USize.toNat_inj.mp
              rw [USize.toNat_add, USize.toNat_mul, UInt32.toNat_toUSize, hlast_u, h23,
                usize_ofNat_toNat (by omega : t4 < 2 ^ 32),
                Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 last * 23 < 2 ^ 32)),
                Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 last * 23 + t4 < 2 ^ 32)),
                usize_ofNat_toNat (by omega)]
            have hD_eq : baGetU16 ctx.s4BA ((UInt32.ofNat (encB 7 last)).toUSize * 23 + USize.ofNat t4) =
                UInt32.ofNat (encB 7 v) := by
              apply UInt32.toNat_inj.mp
              rw [hvc.hs4BA, hsBase_add, tabs_s4BA_get hlast ht4, ← hv_step, UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by have := encB_lt hv; omega)]
            have hmk_eq : UInt32.ofNat mkS.toNat = mkS := UInt32.ofNat_toNat
            simp only [ite_true, Bool.true_and, hD_eq, hmk_eq, hvc.hjs, hvc.hciBA]
            have hemk0_bit := hjs_bit mkS hmk_bit
            have hemk_bit : ((if ctx.useW4 = true then
                (if js && baGetU16 buildS7K16Tabs.ciBA (UInt32.ofNat (encB 7 v)).toUSize == UInt32.ofNat cqN
                  then mkS &&& 1 else mkS) &&&
                  (baGetU8 ctx.w4AllowBA (((mkBaseSt d (r + 1) (t + 1) 0 s1 0 0 >>> 35) &&& 7).toUInt32 * 23 + UInt32.ofNat t4).toUSize).toUInt32
                else if js && baGetU16 buildS7K16Tabs.ciBA (UInt32.ofNat (encB 7 v)).toUSize == UInt32.ofNat cqN
                  then mkS &&& 1 else mkS).toNat >>> R.length) % 2 = 1 := by
              by_cases hw4 : ctx.useW4 = true
              · rw [if_pos hw4]
                obtain ⟨_, _, _, _, ub_s1, _, _⟩ := mkBaseSt_unpack (by omega : d < 256) (by omega : r + 1 < 256)
                  (by omega : t + 1 < 16) (by omega : 0 < 4) (by have := htail.2.1; omega : s1 < 8) (by omega : 0 < 256) (by omega : 0 < 8)
                rw [ub_s1, hvc.hw4BA (by rw [← hvc.hW4]; exact hw4)]
                have hidx_w4 : (UInt32.ofNat s1 * 23 + UInt32.ofNat t4).toUSize = USize.ofNat (s1 * 23 + t4) := by
                  have hs1_u : (UInt32.ofNat s1).toNat = s1 := by
                    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by have := htail.2.1; omega)]
                  have ht4_u : (UInt32.ofNat t4).toNat = t4 := by
                    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
                  apply USize.toNat_inj.mp
                  rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, hs1_u, ht4_u,
                    show (23 : UInt32).toNat = 23 from rfl,
                    Nat.mod_eq_of_lt (by have := htail.2.1; omega : s1 * 23 < 2 ^ 32),
                    Nat.mod_eq_of_lt (by have := htail.2.1; omega : s1 * 23 + t4 < 2 ^ 32),
                    usize_ofNat_toNat (by have := htail.2.1; omega)]
                rw [hidx_w4]
                have hw4_sz : buildW4Allow.size = 138 := by
                  have hfold_sz : ∀ (l : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))) (b : ByteArray),
                      (l.foldl (fun ba (l1, t4, l2, _) =>
                        let j := (l1 - 1) * 23 + t4
                        ba.set! j (ba.get! j &&& UInt8.ofNat (63 - (1 <<< (l2 - 1))))) b).size = b.size := by
                    intro l; induction l with
                    | nil => intro _; rfl
                    | cons _ tl iht => intro b; simp only [List.foldl_cons]; rw [iht, ByteArray.size_set!]
                  rw [buildW4Allow, hfold_sz]; simp [ByteArray.size]
                have hidx_lt : s1 * 23 + t4 < 138 := by have := htail.2.1; omega
                rw [baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hw4_sz]; exact hidx_lt),
                  usize_ofNat_toNat (by omega)]
                obtain ⟨U0, R1, hU0, h1ne, hlast_eq⟩ := hlast_pref
                obtain ⟨_, _, _, ⟨U1, R1', hU1, hR1'_len⟩, _⟩ := htail
                have hR1_eq : R1' = R1 := by
                  have h1 := hU1.symm.trans hU0
                  exact (List.append_inj_right' h1 rfl |> List.cons.inj).1
                subst R1'
                have hL_split : pref ++ (1, v :: R) :: rest' = U0 ++ [R1, (1, v :: R)] ++ rest' := by
                  rw [hU0]; simp
                have hw4_bit := hnoW4 (by rw [← hvc.hW4]; exact hw4) U0 R1 (1, v :: R) rest' (s1 + 1) t4 (R.length + 1)
                  hL_split ⟨rfl, hR1'_len, rfl, ht4, h1ne, List.cons_ne_nil v R, by simpa [hlast_eq] using hv_step⟩
                simp only [Nat.add_sub_cancel] at hw4_bit
                rw [UInt32.toNat_and, UInt8.toNat_toUInt32]
                have hand_bit : ∀ a b k : ℕ, ((a &&& b) >>> k) % 2 = ((a >>> k) % 2) * ((b >>> k) % 2) := by
                  intro a b k
                  have ht : ∀ n : ℕ, (n >>> k) % 2 = if n.testBit k then 1 else 0 := by
                    intro n; rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
                    have h2 : (n >>> k) % 2 < 2 := Nat.mod_lt _ (by omega)
                    match h : (n >>> k) % 2, h2 with | 0, _ => rfl | 1, _ => rfl
                  rw [ht, ht, ht, Nat.testBit_and]
                  cases a.testBit k <;> cases b.testBit k <;> rfl
                rw [hand_bit, hemk0_bit, hw4_bit]
              · rw [if_neg hw4]; exact hemk0_bit
            refine ⟨fun h0 => by rw [h0] at hemk_bit; simp at hemk_bit, ?_⟩
            apply walkGo_complete rfl hvc.hciBA hvc.hnxtBA (UInt32.ofNat fuel)
              (mkBaseSt d (r + 1) (t + 1) 0 s1 0 0) _ d (r + 1) (t + 1) 0 s1 0 0
              (by omega) (by omega) (by omega) (by omega) (by have := htail.2.1; omega)
              (by omega) (by omega) rfl R 6 _ v B' used
              (by omega) hR_lt6 (by omega) hemk_bit hperm hdoor hB'sz hB'inv hused hnew hpw
              (fun h0 => by omega) ?_
            intro B'' hB''sz hB''inv
            simp only [ite_true]
            have hns1_eq : 5 - (6 - 1 - R.length) = (1, v :: R).2.length - 1 := by simp; omega
            rw [hns1_eq]
            exact ih (pref ++ [(1, v :: R)]) rest' (t + 1) (r + 1) (d + (5 - R.length)) 0
              ((1, v :: R).2.length - 1) 0
              (min m (potS a b h t r d)) (max M (potS a b h t r d)) B''
              ((v :: R).getLast (List.cons_ne_nil v R)) (used ++ v :: R)
              (by omega) (by simp at hLlen ⊢; omega) (by simp [hpr]) hnew_r_lt
              (by simpa using hpref_links) hnew_t_le_s hpref_holes hnew_d_le_x
              (by rw [hpref_next_eq]; exact hLlinks) (by rw [hpref_next_eq]; exact hLholes) hLgt
              (by rw [hpref_next_eq]; exact hLseq)
              (fun hm => by rw [hpref_next_eq]; exact hnoM3 hm)
              (fun hw => by rw [hpref_next_eq]; exact hnoW4 hw)
              (fun hj => by rw [hpref_next_eq]; exact hnoJS hj)
              (tailInv_w4 pref (1, v :: R) (List.cons_ne_nil v R) (by simp; omega))
              ⟨pref, (1, v :: R), rfl, List.cons_ne_nil v R, rfl⟩
              (by omega) (by omega) (by omega) (by omega)
              (hperm _ (List.getLast_mem _)) hused' hB''sz hB''inv hcont'
              (by simpa [fK] using halong') hjs2

/-! ### `NoJS` Preservation Under `relabSeq` & Top-Level `seqCap_of_fastK16` -/

theorem noJS_relab {e : List ℕ} (he : PermW 7 e) {L : List TRow} (hL : IsSeq 7 L)
    (hno : NoJS 7 L) : NoJS 7 (relabSeq e L) := by
  intro U' R1' R2' W' heq hbad
  have hlenU : U'.length + 2 ≤ L.length := by
    have := congrArg List.length heq; simp [relabSeq] at this; omega
  set U := L.take U'.length
  set R1 := L[U'.length]'(by omega)
  set R2 := L[U'.length + 1]'(by omega)
  set W := L.drop (U'.length + 2)
  have hL_split : L = U ++ R1 :: R2 :: W := by
    have h1 := List.take_append_drop U'.length L
    have h2 : L.drop U'.length = R1 :: R2 :: W := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [h2] at h1; exact h1.symm
  have hmap_eq : relabSeq e U ++ (relabSeq e [R1, R2]) ++ relabSeq e W = U' ++ R1' :: R2' :: W' := by
    rw [← heq, hL_split]; simp [relabSeq]
  have hU_eq : relabSeq e U = U' := by
    have h1 : (relabSeq e U).length = U'.length := by simp [relabSeq, U]; omega
    exact (List.append_inj (by simpa [List.append_assoc] using hmap_eq) h1).1
  have htail_eq : relabSeq e [R1, R2] ++ relabSeq e W = R1' :: R2' :: W' := by
    have h1 : (relabSeq e U).length = U'.length := by simp [relabSeq, U]; omega
    exact (List.append_inj (by simpa [List.append_assoc] using hmap_eq) h1).2
  simp only [relabSeq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at htail_eq
  obtain ⟨hR1_eq, hR2_eq, _⟩ := htail_eq
  subst R1'; subst R2'
  obtain ⟨h1ne', v', f', F', hR2'_eq, hrot'⟩ := hbad
  have h1ne : R1.2 ≠ [] := hL.pieces_ne R1 (by rw [hL_split]; simp)
  have h2_ge2 : 2 ≤ R2.2.length := by
    have := congrArg List.length hR2'_eq; simp at this; omega
  obtain ⟨v, f, F, hR2_cons⟩ : ∃ v f F, R2.2 = v :: f :: F := by
    match h : R2.2, h2_ge2 with | v :: f :: F, _ => exact ⟨v, f, F, rfl⟩
  have hv_eq : v.map (S.relab e) = v' := by
    rw [hR2_cons] at hR2'_eq; simp at hR2'_eq; exact hR2'_eq.1
  have hlast_eq : (R1.2.map (List.map (S.relab e))).getLast h1ne' = (R1.2.getLast h1ne).map (S.relab e) :=
    List.getLast_map _
  rw [← hv_eq, hlast_eq, K16.tau2_map (by omega) _ (hL.words R1 (by rw [hL_split]; simp) _ (List.getLast_mem h1ne)).2.1] at hrot'
  have hrot : v ~r tau2 7 (R1.2.getLast h1ne) := by
    by_contra hnr
    exact S.not_isRotated_map_relab he (hL.words R2 (by rw [hL_split]; simp) v (by rw [hR2_cons]; simp))
      (permW_tau2 (by omega) (hL.words R1 (by rw [hL_split]; simp) _ (List.getLast_mem h1ne))) hnr hrot'
  exact hno U R1 R2 W hL_split ⟨h1ne, v, f, F, hR2_cons, hrot⟩

/-- **Main Soundness Theorem for `FastK16.seqSearch`:**
If all parts `tp < nt` return `false`, then `PS.SeqCapLt 7 s (PS.capF caps s) (hi + 1)`! -/
theorem seqCap_of_fastK16 {caps : List (List ℕ)} {s lo hi a b h : ℕ} {js useM3 useW4 : Bool}
    {fuel ds nt : ℕ}
    (hs : s < 15) (hhi : hi < 200) (hR : rowsR caps s hi < 250) (hfuel : fuel < 250)
    (habh : a ≤ 100 ∧ b ≤ 100 ∧ h ≤ 100) (hnt : 0 < nt ∧ nt < 65536)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200)
    (hlow : ∀ j, j < s → SeqCapLt 7 j (capF caps j) (hi + 1))
    (hprev : SeqCapLt 7 s (capF caps s) lo)
    (hM3 : useM3 = true → ∀ x, lo ≤ x → x ≤ hi → ∀ y, y < x → capF caps s y + x ≤ capF caps s x + y)
    (hW4 : useW4 = true → 1 ≤ s ∧ SeqCapLt 7 (s - 1) (capF caps (s - 1)) (hi + 7) ∧
      ∀ x, lo ≤ x → x ≤ hi → ∀ y, y ≤ x + 6 → capF caps (s - 1) y + x + 5 ≤ capF caps s x + y)
    (hparts_res : ∀ tp, tp < nt → ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      seqSearch caps s lo hi a b h js useM3 useW4 fuel ds nt pa pb = false) :
    SeqCapLt 7 s (capF caps s) (hi + 1) := by
  suffices hmain : ∀ n : ℕ, ∀ L : List TRow, L.length = n → IsSeq 7 L → (∀ x ∈ L, x.1 ≤ 1) →
      linksT L = s → holesT 7 L < hi + 1 → L.length ≤ capF caps s (holesT 7 L) from
    fun L h1 h2 h3 h4 => hmain L.length L rfl h1 h2 h3 h4
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hlen hL htag hlinks hholes
    by_cases hlo : holesT 7 L < lo
    · exact hprev L hL htag hlinks hlo
    by_cases hne : L = []
    · subst hne; simp
    by_contra hnb
    have hn_lt : n < 250 := by
      have hL_snoc : L = L.dropLast ++ [L.getLast hne] := (List.dropLast_append_getLast hne).symm
      set init := L.dropLast
      set lastRow := L.getLast hne
      have hinit_seq : IsSeq 7 init := hL.infix ⟨[], [lastRow], by simp [hL_snoc]⟩
      have hinit_tag : ∀ y ∈ init, y.1 ≤ 1 := fun y hy => htag y (by rw [hL_snoc]; simp [hy])
      have hinit_holes : holesT 7 init ≤ holesT 7 L := by rw [hL_snoc, PS.holesT_append]; omega
      have hinit_links : linksT init ≤ s := by
        rw [← hlinks, hL_snoc]; exact KS.linksT_le_right init [lastRow]
      have hinit_cap : init.length ≤ capF caps (linksT init) (holesT 7 init) := by
        by_cases hlt : linksT init < s
        · exact hlow _ hlt init hinit_seq hinit_tag rfl (by omega)
        · have heq : linksT init = s := by omega
          rw [heq]
          by_cases hlo' : holesT 7 init < lo
          · exact hprev init hinit_seq hinit_tag heq hlo'
          · exact ih init.length (by rw [← hlen, hL_snoc]; simp) init rfl hinit_seq hinit_tag heq (by omega)
      have hcap_le := capF_le_of_all hcaps (linksT init) (holesT 7 init)
      have hlen_snoc : n = init.length + 1 := by rw [← hlen, hL_snoc]; simp
      omega
    have hparts : ∀ L' : List TRow, L'.length = n → IsSeq 7 L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT 7 L' < hi + 1 → ∀ U X W, L' = U ++ X ++ W → X ≠ [] →
        X.length < L'.length → X.length ≤ capF caps (linksT X) (holesT 7 X) := by
      intro L' hlen' hL' htag' hlinks' hholes' U X W hUXW _ hXlen
      have hX : IsSeq 7 X := hL'.infix ⟨U, W, hUXW.symm⟩
      have hXtag : ∀ y ∈ X, y.1 ≤ 1 := fun y hy => htag' y (by rw [hUXW]; simp [hy])
      have hXholes : holesT 7 X ≤ holesT 7 L' := by rw [hUXW, PS.holesT_append, PS.holesT_append]; omega
      have hXlinks : linksT X ≤ s := by
        rw [← hlinks', hUXW]
        exact le_trans (KS.linksT_le_left U X) (KS.linksT_le_right (U ++ X) W)
      by_cases hsX : linksT X < s
      · exact hlow _ hsX X hX hXtag rfl (by omega)
      · have hs' : linksT X = s := by omega
        rw [hs']
        by_cases hloX : holesT 7 X < lo
        · exact hprev X hX hXtag hs' hloX
        · exact ih X.length (by omega) X rfl hX hXtag hs' (by omega)
    have hcap0 : ∀ rest' : List TRow, rest'.length < n → IsSeq 7 rest' → (∀ w ∈ rest', w.1 ≤ 1) →
        linksT rest' = 0 → ∀ y, holesT 7 rest' = y → y ≤ hi → rest'.length ≤ capF caps 0 y := by
      intro rest' hrlen hseq' htag' hlk' y hy hyhi
      by_cases hs0 : 0 < s
      · rw [← hy]; exact hlow 0 hs0 rest' hseq' htag' hlk' (by omega)
      · have hs_eq : s = 0 := by omega
        subst hs_eq; rw [← hy]
        by_cases hlo' : holesT 7 rest' < lo
        · exact hprev rest' hseq' htag' hlk' hlo'
        · exact ih rest'.length hrlen rest' rfl hseq' htag' hlk' (by omega)
    have hrev : ∀ L' : List TRow, L'.length = n → IsSeq 7 L' → (∀ x ∈ L', x.1 ≤ 1) →
        linksT L' = s → holesT 7 L' = holesT 7 L → Good 7 a b h L' → False := by
      suffices hmeas : ∀ D : ℕ, ∀ L' : List TRow, 6 * n * n - K16.psi L' = D →
          L'.length = n → IsSeq 7 L' → (∀ x ∈ L', x.1 ≤ 1) → linksT L' = s →
          holesT 7 L' = holesT 7 L → Good 7 a b h L' → False from
        fun L' h1 h2 h3 h4 h5 h6 => hmeas _ L' rfl h1 h2 h3 h4 h5 h6
      intro D
      induction D using Nat.strong_induction_on with
      | h D ihD =>
        intro L' hD hlen' hL' htag' hlinks' hholes' hgood
        by_cases hno : js = true → NoJS 7 L'
        · have hne' : L' ≠ [] := by
            intro h0; rw [h0] at hlen'; rw [← hlen] at hlen'
            exact hne (List.length_eq_zero_iff.mp hlen'.symm)
          obtain ⟨x0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne'
          have hrule := KS.ruleK_of_good (P := capF caps) (s := s) (lo := lo) (hi := hi) (a := a)
            (b := b) (h := h) htag' hlinks' (by rw [hholes']; omega) (by rw [hholes']; omega)
            (by rw [hholes', hlen', ← hlen]; omega)
            (hparts _ hlen' hL' htag' hlinks' (by omega)) hgood rest [x0] 0 0 rfl (by simp)
            ⟨[], [x0], rfl, by simp, KS.phiAt_nil a b h _⟩
            (by
              intro A1 A2 hA12 hA2
              have hA1 : A1 = [] := by
                have hl := congrArg List.length hA12
                rw [List.length_append] at hl
                have : 0 < A2.length := List.length_pos_iff.mpr hA2
                simp only [List.length_cons, List.length_nil] at hl
                exact List.length_eq_zero_iff.mp (by omega)
              rw [hA1, KS.phiAt_nil])
          have e1 : linksT [x0] = 0 := rfl
          have e2 : ([x0] : List TRow).length = 1 := rfl
          have e3 : holesT 7 [x0] = 6 - x0.2.length := by simp [holesT]
          rw [e1, e2, e3] at hrule
          obtain ⟨kd0, Q0⟩ := x0
          have hQ0 : Q0 ≠ [] := hL'.pieces_ne (kd0, Q0) List.mem_cons_self
          obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
          have hv0 : PermW 7 v0 := hL'.words _ List.mem_cons_self v0 List.mem_cons_self
          have hL1 := hL'.relabel hv0
          have hrule1 := KS.ruleK_relab v0 rest _ _ _ _ _ hrule
          have hjsA0 : js = true → NoJSAlong 7 ((v0 :: R0).getLast (List.cons_ne_nil _ _)) rest :=
            fun h => noJSAlong_of_noJS rest (kd0, v0 :: R0) (List.cons_ne_nil _ _)
              (fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)) (hno h)
          have hg : v0.map (S.relab v0) = List.range' 1 7 := by
            rw [S.map_relab_self hv0.1, hv0.2.1]
          have hjsR : js = true → NoJSAlong 7
              ((List.range' 1 7 :: R0.map (List.map (S.relab v0))).getLast (List.cons_ne_nil _ _))
              (relabSeq v0 rest) := by
            intro h
            rw [← hg, K16.getLast_map_cons]
            exact noJSAlong_relab (by omega) hv0 rest _
              (hL'.words _ List.mem_cons_self _ (List.getLast_mem _))
              (fun y hy => hL'.words y (List.mem_cons_of_mem _ hy)) (hjsA0 h)
          have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest) =
              (kd0, List.range' 1 7 :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest := by
            simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
          have hL1_len : (relabSeq v0 ((kd0, v0 :: R0) :: rest)).length = n := by
            rw [relabSeq_length]; exact hlen'
          have hL1_tag : ∀ x ∈ relabSeq v0 ((kd0, v0 :: R0) :: rest), x.1 ≤ 1 :=
            relabSeq_tags v0 _ htag'
          have hL1_links : linksT (relabSeq v0 ((kd0, v0 :: R0) :: rest)) = s := by
            rw [relabSeq_linksT]; exact hlinks'
          have hL1_holes : holesT 7 (relabSeq v0 ((kd0, v0 :: R0) :: rest)) = holesT 7 L := by
            rw [relabSeq_holesT]; exact hholes'
          have hL1_M3 : useM3 = true → NoM3 (relabSeq v0 ((kd0, v0 :: R0) :: rest)) := fun hm =>
            noM3_of_min_rows (hM3 hm)
              (fun M hMlen hMseq hMtag hMlk hMhl => by
                by_cases hloM : holesT 7 M < lo
                · exact hprev M hMseq hMtag hMlk hloM
                · exact ih M.length (by omega) M rfl hMseq hMtag hMlk hMhl)
              hL1 hL1_tag hL1_links (by omega) (by omega) (by rw [hL1_holes, hL1_len]; omega)
          have hL1_W4 : useW4 = true → NoW4 (relabSeq v0 ((kd0, v0 :: R0) :: rest)) := fun hw =>
            let ⟨hs1, hlowW4, hmonoW4⟩ := hW4 hw
            noW4_of_hlow hs1 hmonoW4 hlowW4 hL1 hL1_tag hL1_links (by omega) (by omega)
              (by rw [hL1_holes, hL1_len]; omega)
          have hL1_JS : js = true → NoJS 7 (relabSeq v0 ((kd0, v0 :: R0) :: rest)) :=
            fun hj => noJS_relab hv0 hL' (hno hj)
          rw [hshape] at hL1 hL1_len hL1_tag hL1_links hL1_holes hL1_M3 hL1_W4 hL1_JS
          have elen : 6 - (kd0, v0 :: R0).2.length = 5 - (R0.map (List.map (S.relab v0))).length := by
            simp only [List.length_cons, List.length_map]; omega
          rw [elen] at hrule1
          set R1 := R0.map (List.map (S.relab v0))
          set rest1 := relabSeq v0 rest
          have hperm1 : ∀ w ∈ List.range' 1 7 :: R1, PermW 7 w :=
            hL1.words (kd0, List.range' 1 7 :: R1) List.mem_cons_self
          have hcl1 : List.Pairwise (fun a b => ¬ a ~r b)
              ((List.range' 1 7 :: R1) ++ (rest1.map Prod.snd).flatten) := by
            have := hL1.classes; simp only [List.map_cons, List.flatten_cons] at this; exact this
          have hcl1' := List.pairwise_append.mp hcl1
          have hR1_lt : R1.length < 6 := by
            have := hL1.size_le (kd0, List.range' 1 7 :: R1) List.mem_cons_self
            simp only [List.length_cons] at this; omega
          have hdoor1 := S.door_chain (by omega) _ hperm1
            (hL1.doors (kd0, List.range' 1 7 :: R1) List.mem_cons_self) hcl1'.1
          have hcont1 := PS.pcont_of_seq (by omega) rest1 (kd0, List.range' 1 7 :: R1)
            (List.range' 1 7 :: R1) (List.cons_ne_nil _ _) hL1 hcl1'.2.2
          have hne1 : ∀ y ∈ rest1, y.2 ≠ [] := fun y hy => hL1.pieces_ne y (List.mem_cons_of_mem _ hy)
          obtain ⟨tp, htp, hP⟩ := KS.kalong_gate (enc := encB 7) (fg := fuel - ds) hnt.1 fuel rest1
            0 1 (5 - R1.length) 0 0 _ (KS.kalong_of_rule (enc := encB 7) (fuel - ds) rest1 fuel 0 1
              (5 - R1.length) 0 0 ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) hne1 hrule1)
          obtain ⟨pa, pb, hpa, hpb, hsr⟩ := hparts_res tp htp
          have hvc0 := buildProblem_valid (caps := caps) (s := s) (lo := lo) (hi := hi) (a := a)
            (b := b) (h := h) (js := js) (useM3 := useM3) (useW4 := useW4) (fuel := fuel)
            (ds := ds) (nt := nt) (tp := tp) hs hhi hR habh hcaps
          have hst_eq0 : (buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt).2.1 =
              UInt32.ofNat (encB 7 (List.range' 1 7)) := by
            change UInt32.ofNat ((PS.permCodes 7 7).idxOf (PS.idcF 7)) = _
            rw [(PS.encB_enc 7 (by omega) (by omega)).st_eq]
          have hsz_eq0 : (buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt).2.2 =
              (PS.permCodes 7 7).length := rfl
          have hfull_eq0 : (buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt).1.fullMk =
              UInt32.ofNat (maskG (fun _ _ _ => 1) 0 0 0 6) := rfl
          unfold seqSearch at hsr
          generalize hbp : buildProblem caps s lo hi a b h js useM3 useW4 fuel ds nt = bp at hsr hvc0 hst_eq0 hsz_eq0 hfull_eq0
          rcases bp with ⟨ctx0, st0, sz0⟩
          dsimp only at hsr hvc0 hst_eq0 hsz_eq0 hfull_eq0
          have hrun_f : runPart ctx0 st0 sz0 fuel tp = false := by
            split_ifs at hsr with h1
            · have h1' : pb = pa + 1 := beq_iff_eq.mp h1
              have htp_eq : tp = pa := by omega
              rwa [htp_eq]
            · exact KS.par_false hsr tp hpa hpb
          set ctx : FastK16Ctx := { ctx0 with tp := UInt32.ofNat tp }
          have hfull_bit : (ctx.fullMk.toNat >>> R1.length) % 2 = 1 := by
            have hlt32 : maskG (fun _ _ _ => 1) 0 0 0 6 < 2 ^ 32 := by decide
            change (ctx0.fullMk.toNat >>> R1.length) % 2 = 1
            rw [hfull_eq0, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32, Nat.shiftRight_eq_div_pow]
            exact KS.maskG_bit (fun _ _ _ => 1) 0 0 0 6 R1.length hR1_lt (by simp)
          have hbase0 : ((1 : UInt64) <<< 21) = mkBaseSt 0 1 0 0 0 0 0 := by decide
          have hsz_init : (ByteArray.mk (Array.replicate (PS.permCodes 7 7).length 0)).size =
              (PS.permCodes 7 7).length := Array.size_replicate
          have hw0 : (walkGo ctx (UInt32.ofNat fuel) ((1 : UInt64) <<< 21) 0 6 ctx.fullMk
              (UInt32.ofNat (encB 7 (List.range' 1 7)))
              (ByteArray.mk (Array.replicate (PS.permCodes 7 7).length 0))).size = 0 := by
            rw [hbase0]
            apply walkGo_complete rfl hvc0.hciBA hvc0.hnxtBA (UInt32.ofNat fuel)
              (mkBaseSt 0 1 0 0 0 0 0) 0 0 1 0 0 0 0 0
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl
              R1 6 ctx.fullMk (List.range' 1 7) _ [] (by omega) hR1_lt (by omega) hfull_bit
              hperm1 hdoor1 hsz_init (PS.minv_marks0 _ _ _) (by simp) (by simp)
              hcl1'.1 (fun h0 => by omega) ?_
            intro B' hB'sz hB'inv
            simp only [ite_true]
            rw [Nat.zero_add]
            have hns1 : 5 - (6 - 1 - R1.length) = (kd0, List.range' 1 7 :: R1).2.length - 1 := by simp; omega
            rw [hns1]
            have h0m : (0 : UInt64) = packMM (Int32.ofInt 0) (Int32.ofInt 0) := by decide
            rw [h0m]
            have hpref_d : holesT 7 [(kd0, List.range' 1 7 :: R1)] = 5 - R1.length := by simp [holesT]
            have hd_le_x : 5 - R1.length ≤ holesT 7 L := by
              have h1 : holesT 7 [(kd0, List.range' 1 7 :: R1)] + holesT 7 rest1 = holesT 7 L := by
                rw [← PS.holesT_append]; exact hL1_holes
              omega
            have hd5 : 6 - 1 - R1.length = 5 - R1.length := rfl
            rw [hd5]
            exact go_complete (L_len := n) (x := holesT 7 L) hvc0 hs hhi hR (by omega) habh hnt
              (by omega) (by omega) hn_lt
              (fun r' hr' h1 h2 h3 y hy_hi hy => hcap0 r' hr' h1 h2 h3 y hy hy_hi)
              fuel [(kd0, List.range' 1 7 :: R1)] rest1 0 1 (5 - R1.length) 0
              ((kd0, List.range' 1 7 :: R1).2.length - 1) 0 0 0 B'
              ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 7 :: R1)
              (by omega) (by simp only [List.length_cons, List.length_nil] at hL1_len ⊢; omega) rfl (by omega) rfl (by omega) hpref_d hd_le_x
              hL1_links hL1_holes (by omega) hL1 hL1_M3 hL1_W4 hL1_JS
              (tailInv_single _ (List.cons_ne_nil _ _) (by simp; omega))
              ⟨[], (kd0, List.range' 1 7 :: R1), rfl, List.cons_ne_nil _ _, rfl⟩
              (by omega) (by omega) (by omega) (by omega)
              (hperm1 _ (List.getLast_mem _)) hperm1 hB'sz (by simpa using hB'inv) hcont1 hP hjsR
          have hrun_t : runPart ctx0 st0 sz0 fuel tp = true := by
            unfold runPart
            rw [hst_eq0, hsz_eq0]
            exact (ba_usize_eq_zero_iff (by rw [hw0]; omega)).mpr hw0
          rw [hrun_f] at hrun_t
          exact Bool.false_ne_true hrun_t
        · have hno' : js = true ∧ ¬ NoJS 7 L' := by
            by_cases hj : js = true
            · exact ⟨hj, fun h' => hno (fun _ => h')⟩
            · exact absurd (fun h' => absurd h' hj) hno
          obtain ⟨N, hN, htagN, hlenN, hlinksN, hholesN, hpsiN, hgoodN⟩ :=
            shift_of_not_noJS (by omega) hL' htag' hno'.2
          have hb := psi_le N (fun x hx => hN.size_le x hx)
          rw [hlenN, hlen', show (7 - 1) * n * n = 6 * n * n from rfl] at hb
          exact ihD _ (by omega) N rfl (by omega) hN htagN (by omega) (by omega) (hgoodN a b h hgood)
    rcases KS.good_or_rev (k := 7) a b h hne htag with hg | hg
    · exact hrev L hlen hL htag hlinks rfl hg
    · exact hrev (KS.revA 7 0 L) (by rw [KS.length_revA, hlen]) (KS.isSeq_revA (by omega) 0 hL)
        (KS.kinds_revA (Nat.zero_le 1) htag) (by rw [KS.linksT_revA, hlinks])
        (KS.holesT_revA 0 L) hg

end FastK16Sound
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.FastK16Sound.seqCap_of_fastK16
