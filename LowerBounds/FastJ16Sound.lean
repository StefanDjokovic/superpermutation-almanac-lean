import LowerBounds.FastJ16Search
import LowerBounds.FastCommonSound
import LowerBounds.J15Final
import LowerBounds.J16Along
import LowerBounds.K16Word

/-!
# Soundness & Completeness of `FastJ16Search` (Tabulated `PREV` + `ORD` + `VS` + `Rule JS`)

Proves `jv_of_fastJ16`: if `FastJ16.jSearch` returns `false` on every partition `tp < gprod gs`
(under `CapsOKV`, `RunOK`-compatible bounds, and `js`-compatible normal form), then
`J16.JV 7 qs V W bm` holds.

Zero `sorry`, zero custom axioms — only `[propext, Classical.choice, Quot.sound]`.
-/

namespace SuperpermLowerBounds
namespace FastJ16Sound

open S (PermW WLink DoorEq)
open PS (TRow IsSeq holesT linksT Closes SeqCapLt LinkK permCodes ciTab nxtTab sdTab encB capF idcF)
open KS (tabA tab2 look2 maxLe maxLeN par Good)
open J15 (valK wtK lk IsPieceW IsPieceC Cyc Sh blocksR clsCount clsCount_perm
  firstB lastB lastB_snoc flatJ blocksR_flatJ blocksR_append valK_append wtK_append
  rowOk_of_split Gate Early FinOk RowOk Bud vOf k3Ok k4Ok negInf sval pval bestF
  bestStep kdF loF hiF gprod digs GateL EarlyL Id1 MC MB)
open J16 (Q dq IsPieceV IsPieceCV JV CEV NF Rules vloF vhiF prevOn ordOn potF segF cn1F a2pF fG
  prevOk prevEnd xrF xcF RunOK BfOf RBfOf JAlong JAlongR)
open FastK16 (baGetU8 baSetU8 baGetU16 baGetI64 packU16Arr packI64Arr u32_sub_one_lt)
open FastJ16
open FastSound

/-! ### Section 1: Bit-Packing (`packI32Pair`, `packSt`) and `computeMask` Helpers -/

private theorem u64_field_getLsbD {val : ℕ} {sh : UInt64} {w : ℕ}
    (hval : val < 2 ^ w) (hsh : sh.toNat + w ≤ 64)
    (h1 : w ≤ 32) (h2 : sh.toNat < 64) (j : ℕ) (hj : j < 64) :
    ((UInt32.ofNat val).toUInt64 <<< sh).toBitVec.getLsbD j =
      (decide (sh.toNat ≤ j ∧ j < sh.toNat + w) && Nat.testBit val (j - sh.toNat)) := by
  have hsh_mod : (sh.toBitVec % 64).toNat = sh.toNat := by
    change sh.toNat % 64 = sh.toNat; exact Nat.mod_eq_of_lt h2
  rw [UInt64.toBitVec_shiftLeft]
  change ((UInt32.ofNat val).toUInt64.toBitVec <<< (sh.toBitVec % 64).toNat).getLsbD j = _
  rw [hsh_mod, BitVec.getLsbD_shiftLeft]
  simp only [hj, decide_true, Bool.true_and]
  by_cases hge : sh.toNat ≤ j
  · have hnlt : ¬ j < sh.toNat := by omega
    simp only [hnlt, decide_false, Bool.not_false, Bool.true_and]
    have hval32 : val < 2 ^ 32 := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) h1)
    have hto : (UInt32.ofNat val).toUInt64.toNat = val := by
      rw [UInt32.toNat_toUInt64, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hval32]
    have hb : (UInt32.ofNat val).toUInt64.toBitVec.getLsbD (j - sh.toNat) =
        Nat.testBit val (j - sh.toNat) := by
      change Nat.testBit (UInt32.ofNat val).toUInt64.toNat (j - sh.toNat) = _; rw [hto]
    rw [hb]
    by_cases hlt : j < sh.toNat + w
    · simp [hge, hlt]
    · have hf : Nat.testBit val (j - sh.toNat) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have : val < 2 ^ (j - sh.toNat) := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.div_eq_of_lt this]; rfl
      simp [hge, hlt, hf]
  · simp [show j < sh.toNat by omega, hge]

private theorem u64_shift_mask_toUInt32 {x : UInt64} {sh : UInt64} {w val : ℕ}
    (hval : val < 2 ^ w) (hsh : sh.toNat + w ≤ 64) (hw : w < 32) (hsh64 : sh.toNat < 64)
    (hbits : ∀ j < w, x.toBitVec.getLsbD (sh.toNat + j) = Nat.testBit val j) :
    ((x >>> sh) &&& UInt64.ofNat (2 ^ w - 1)).toUInt32 = UInt32.ofNat val := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [UInt64.toBitVec_toUInt32, BitVec.getLsbD_setWidth]
  simp only [hj, decide_true, Bool.true_and]
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, UInt64.toBitVec_shiftRight]
  have hsh_mod : (sh.toBitVec % 64).toNat = sh.toNat := by
    rw [BitVec.toNat_umod]; change sh.toNat % 64 = sh.toNat; exact Nat.mod_eq_of_lt hsh64
  change ((x.toBitVec >>> (sh.toBitVec % 64).toNat).getLsbD j &&
      (UInt64.ofNat (2 ^ w - 1)).toBitVec.getLsbD j) = _
  rw [hsh_mod, BitVec.getLsbD_ushiftRight]
  have hmask : (UInt64.ofNat (2 ^ w - 1)).toBitVec.getLsbD j = decide (j < w) := by
    have hlt64 : 2 ^ w - 1 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.pow_lt_pow_right (by omega) (by omega))
    change Nat.testBit (UInt64.ofNat (2 ^ w - 1)).toNat j = decide (j < w)
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt64, Nat.testBit_two_pow_sub_one]
  have hrhs : (UInt32.ofNat val).toBitVec.getLsbD j = Nat.testBit val j := by
    have hval32 : val < 2 ^ 32 := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega))
    change Nat.testBit (UInt32.ofNat val).toNat j = _
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hval32]
  rw [hmask, hrhs]
  by_cases hjw : j < w
  · simp only [hjw, decide_true, Bool.and_true]
    exact hbits j hjw
  · simp only [hjw, decide_false, Bool.and_false]
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have : val < 2 ^ j := Nat.lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt this]; rfl

theorem int64_toInt32_ofInt {x : ℤ} (hlo : -2 ^ 30 ≤ x) (hhi : x ≤ 2 ^ 30) :
    (Int64.ofInt x).toInt32 = Int32.ofInt x := by
  apply Int32.toInt_inj.mp
  rw [Int64.toInt_toInt32, int64_toInt_ofInt (by omega) (by omega), int32_toInt_ofInt hlo hhi]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem packI32Pair_unpack {x y : ℤ} (hx1 : -2 ^ 30 ≤ x) (hx2 : x ≤ 2 ^ 30)
    (hy1 : -2 ^ 30 ≤ y) (hy2 : y ≤ 2 ^ 30) :
    fstI64 (packI32Pair (Int64.ofInt x) (Int64.ofInt y)) = Int64.ofInt x ∧
    sndI64 (packI32Pair (Int64.ofInt x) (Int64.ofInt y)) = Int64.ofInt y := by
  have hx32 := int64_toInt32_ofInt hx1 hx2
  have hy32 := int64_toInt32_ofInt hy1 hy2
  unfold packI32Pair fstI64 sndI64
  rw [hx32, hy32]
  have hfst_u : ((Int32.ofInt x).toUInt32.toUInt64 ||| ((Int32.ofInt y).toUInt32.toUInt64 <<< 32)).toUInt32 =
      (Int32.ofInt x).toUInt32 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth, BitVec.getLsbD_or]
    change (decide (j < 32) &&
        ((decide (j < 64) && (Int32.ofInt x).toUInt32.toBitVec.getLsbD j) ||
         (((Int32.ofInt y).toUInt32.toBitVec.setWidth 64) <<< (32 : BitVec 64).toNat).getLsbD j)) = _
    rw [BitVec.getLsbD_shiftLeft]
    have hlt64 : j < 64 := by omega
    simp [hj, hlt64]
  have hsnd_u : ((((Int32.ofInt x).toUInt32.toUInt64 ||| ((Int32.ofInt y).toUInt32.toUInt64 <<< 32)) >>> 32)).toUInt32 =
      (Int32.ofInt y).toUInt32 := by
    apply UInt32.toBitVec_inj.mp; apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
    change (decide (j < 32) &&
        (((Int32.ofInt x).toUInt32.toBitVec.setWidth 64 |||
          ((Int32.ofInt y).toUInt32.toBitVec.setWidth 64) <<< (32 : BitVec 64).toNat) >>>
          (32 : BitVec 64).toNat).getLsbD j) = _
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    have h32 : (32 : BitVec 64).toNat = 32 := rfl
    rw [h32]
    have hlt64 : 32 + j < 64 := by omega
    have hnlt : ¬ 32 + j < 32 := by omega
    have hsub : 32 + j - 32 = j := by omega
    simp [hj, hlt64, hnlt, hsub]
    intro _; omega
  rw [hfst_u, hsnd_u]
  have h1 : (Int32.ofInt x).toUInt32.toInt32 = Int32.ofInt x := Int32.toInt32_toUInt32 _
  have h2 : (Int32.ofInt y).toUInt32.toInt32 = Int32.ofInt y := Int32.toInt32_toUInt32 _
  rw [h1, h2]
  constructor
  · apply Int64.toInt_inj.mp
    rw [int32_toInt64_toInt, int32_toInt_ofInt hx1 hx2, int64_toInt_ofInt (by omega) (by omega)]
  · apply Int64.toInt_inj.mp
    rw [int32_toInt64_toInt, int32_toInt_ofInt hy1 hy2, int64_toInt_ofInt (by omega) (by omega)]

theorem packSt_unpack {i t r d b du z q : ℕ}
    (hi : i < 16) (ht : t < 16) (hr : r < 256) (hd : d < 256)
    (hb : b < 256) (hdu : du < 16) (hz : z < 8192) (hq : q < 8192) :
    let st := packSt (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
      (UInt32.ofNat b) (UInt32.ofNat du) (UInt32.ofNat z) (UInt32.ofNat q)
    (st &&& 15).toUInt32 = UInt32.ofNat i ∧
    ((st >>> 4) &&& 15).toUInt32 = UInt32.ofNat t ∧
    ((st >>> 8) &&& 255).toUInt32 = UInt32.ofNat r ∧
    ((st >>> 16) &&& 255).toUInt32 = UInt32.ofNat d ∧
    ((st >>> 24) &&& 255).toUInt32 = UInt32.ofNat b ∧
    ((st >>> 32) &&& 15).toUInt32 = UInt32.ofNat du ∧
    ((st >>> 36) &&& 8191).toUInt32 = UInt32.ofNat z ∧
    ((st >>> 49) &&& 8191).toUInt32 = UInt32.ofNat q := by
  intro st
  have hbit : ∀ j < 64, st.toBitVec.getLsbD j =
      ((decide (0 ≤ j ∧ j < 4) && Nat.testBit i j) ||
       (decide (4 ≤ j ∧ j < 8) && Nat.testBit t (j - 4)) ||
       (decide (8 ≤ j ∧ j < 16) && Nat.testBit r (j - 8)) ||
       (decide (16 ≤ j ∧ j < 24) && Nat.testBit d (j - 16)) ||
       (decide (24 ≤ j ∧ j < 32) && Nat.testBit b (j - 24)) ||
       (decide (32 ≤ j ∧ j < 36) && Nat.testBit du (j - 32)) ||
       (decide (36 ≤ j ∧ j < 49) && Nat.testBit z (j - 36)) ||
       (decide (49 ≤ j ∧ j < 62) && Nat.testBit q (j - 49))) := by
    intro j hj
    dsimp only [st, packSt]
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
    have h0 : (UInt32.ofNat i).toUInt64.toBitVec.getLsbD j = (decide (0 ≤ j ∧ j < 4) && Nat.testBit i j) := by
      have := u64_field_getLsbD (val := i) (sh := 0) (w := 4) hi (by decide) (by decide) (by decide) j hj
      simpa using this
    rw [h0,
      u64_field_getLsbD (val := t) (sh := 4) (w := 4) ht (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := r) (sh := 8) (w := 8) hr (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := d) (sh := 16) (w := 8) hd (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := b) (sh := 24) (w := 8) hb (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := du) (sh := 32) (w := 4) hdu (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := z) (sh := 36) (w := 13) hz (by decide) (by decide) (by decide) j hj,
      u64_field_getLsbD (val := q) (sh := 49) (w := 13) hq (by decide) (by decide) (by decide) j hj]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := u64_shift_mask_toUInt32 (x := st) (sh := 0) (w := 4) (val := i) hi (by decide) (by decide) (by decide)
      (fun j hj => by rw [show (0 : UInt64).toNat + j = j by simp, hbit j (by omega)]; simp [hj, show ¬ (4 ≤ j) by omega, show ¬ (8 ≤ j) by omega, show ¬ (16 ≤ j) by omega, show ¬ (24 ≤ j) by omega, show ¬ (32 ≤ j) by omega, show ¬ (36 ≤ j) by omega, show ¬ (49 ≤ j) by omega])
    simpa using h
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 4) (w := 4) (val := t) ht (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (4 : UInt64).toNat = 4 from rfl, hbit (4 + j) (by omega)]
        simp [show ¬ (4 + j < 4) by omega, show 4 + j < 8 by omega, show ¬ (8 ≤ 4 + j) by omega,
          show ¬ (16 ≤ 4 + j) by omega, show ¬ (24 ≤ 4 + j) by omega, show ¬ (32 ≤ 4 + j) by omega,
          show ¬ (36 ≤ 4 + j) by omega, show ¬ (49 ≤ 4 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 8) (w := 8) (val := r) hr (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (8 : UInt64).toNat = 8 from rfl, hbit (8 + j) (by omega)]
        simp [show ¬ (8 + j < 4) by omega, show ¬ (8 + j < 8) by omega, show 8 + j < 16 by omega,
          show ¬ (16 ≤ 8 + j) by omega, show ¬ (24 ≤ 8 + j) by omega, show ¬ (32 ≤ 8 + j) by omega,
          show ¬ (36 ≤ 8 + j) by omega, show ¬ (49 ≤ 8 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 16) (w := 8) (val := d) hd (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (16 : UInt64).toNat = 16 from rfl, hbit (16 + j) (by omega)]
        simp [show ¬ (16 + j < 4) by omega, show ¬ (16 + j < 8) by omega, show ¬ (16 + j < 16) by omega,
          show 16 + j < 24 by omega, show ¬ (24 ≤ 16 + j) by omega, show ¬ (32 ≤ 16 + j) by omega,
          show ¬ (36 ≤ 16 + j) by omega, show ¬ (49 ≤ 16 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 24) (w := 8) (val := b) hb (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (24 : UInt64).toNat = 24 from rfl, hbit (24 + j) (by omega)]
        simp [show ¬ (24 + j < 4) by omega, show ¬ (24 + j < 8) by omega, show ¬ (24 + j < 16) by omega,
          show ¬ (24 + j < 24) by omega, show 24 + j < 32 by omega, show ¬ (32 ≤ 24 + j) by omega,
          show ¬ (36 ≤ 24 + j) by omega, show ¬ (49 ≤ 24 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 32) (w := 4) (val := du) hdu (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (32 : UInt64).toNat = 32 from rfl, hbit (32 + j) (by omega)]
        simp [show ¬ (32 + j < 4) by omega, show ¬ (32 + j < 8) by omega, show ¬ (32 + j < 16) by omega,
          show ¬ (32 + j < 24) by omega, show ¬ (32 + j < 32) by omega, show 32 + j < 36 by omega,
          show ¬ (36 ≤ 32 + j) by omega, show ¬ (49 ≤ 32 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 36) (w := 13) (val := z) hz (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (36 : UInt64).toNat = 36 from rfl, hbit (36 + j) (by omega)]
        simp [show ¬ (36 + j < 4) by omega, show ¬ (36 + j < 8) by omega, show ¬ (36 + j < 16) by omega,
          show ¬ (36 + j < 24) by omega, show ¬ (36 + j < 32) by omega, show ¬ (36 + j < 36) by omega,
          show 36 + j < 49 by omega, show ¬ (49 ≤ 36 + j) by omega])
  · exact u64_shift_mask_toUInt32 (x := st) (sh := 49) (w := 13) (val := q) hq (by decide) (by decide) (by decide)
      (fun j hj => by
        rw [show (49 : UInt64).toNat = 49 from rfl, hbit (49 + j) (by omega)]
        simp [show ¬ (49 + j < 4) by omega, show ¬ (49 + j < 8) by omega, show ¬ (49 + j < 16) by omega,
          show ¬ (49 + j < 24) by omega, show ¬ (49 + j < 32) by omega, show ¬ (49 + j < 36) by omega,
          show ¬ (49 + j < 49) by omega, show 49 + j < 62 by omega])

theorem computeMask_bit_of_cases (p0 p1 p2 p3 p4 p5 : Bool) (j : ℕ) (hj : j < 6)
    (hp : match j with | 0 => p0 = true | 1 => p1 = true | 2 => p2 = true | 3 => p3 = true | 4 => p4 = true | _ => p5 = true) :
    (((if p0 = true then (1 : UInt32) else 0) |||
      (if p1 = true then (2 : UInt32) else 0) |||
      (if p2 = true then (4 : UInt32) else 0) |||
      (if p3 = true then (8 : UInt32) else 0) |||
      (if p4 = true then (16 : UInt32) else 0) |||
      (if p5 = true then (32 : UInt32) else 0)).toNat >>> j) % 2 = 1 := by
  have ht : ∀ n : ℕ, (n >>> j) % 2 = if n.testBit j then 1 else 0 := by
    intro n; rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
    have h2 : (n >>> j) % 2 < 2 := Nat.mod_lt _ (by omega)
    match h : (n >>> j) % 2, h2 with | 0, _ => rfl | 1, _ => rfl
  rw [ht]
  simp only [UInt32.toNat_or, Nat.testBit_or]
  match j, hj, hp with
  | 0, _, hp => rw [hp]; simp [show Nat.testBit 1 0 = true from by decide]
  | 1, _, hp => rw [hp]; simp [show Nat.testBit 2 1 = true from by decide]
  | 2, _, hp => rw [hp]; simp [show Nat.testBit 4 2 = true from by decide]
  | 3, _, hp => rw [hp]; simp [show Nat.testBit 8 3 = true from by decide]
  | 4, _, hp => rw [hp]; simp [show Nat.testBit 16 4 = true from by decide]
  | 5, _, hp => rw [hp]; simp [show Nat.testBit 32 5 = true from by decide]

/-! ### Section 2: Exact Restoration (`Id1`) for `walkJFast`, `loopU32`, `go` -/

theorem baSetU8_restore (M : ByteArray) (i : USize) (v : UInt8) (hM : M.size < 2 ^ 32) :
    baSetU8 (baSetU8 M i v) i (baGetU8 M i) = M := by
  by_cases hi : i.toNat < M.size
  · rw [baGetU8_eq_get! hM hi, baSetU8_eq_set! hM hi,
      baSetU8_eq_set! (by rw [ByteArray.size_set!]; exact hM) (by rw [ByteArray.size_set!]; exact hi)]
    exact J15.set!_restore M i.toNat v
  · have hn : ¬ i < M.usize := by
      intro hlt; apply hi
      have h1 : i.toNat < M.usize.toNat := hlt
      rw [ba_usize_toNat hM] at h1; exact h1
    have h1 : baSetU8 M i v = M := by unfold baSetU8; rw [dif_neg hn]
    rw [h1]; unfold baSetU8; rw [dif_neg hn]

theorem walkJFast_id (ctx : FastJ16Ctx) (visit : UInt32 → UInt32 → UInt32 → ByteArray → ByteArray)
    (hvid : ∀ n e du M, M.size < 2 ^ 32 → Id1 (visit n e du M) M) (pm : UInt8) :
    ∀ (rem : ℕ) (mk du D : UInt32) (M : ByteArray),
      rem < 2 ^ 32 → M.size < 2 ^ 32 →
      Id1 (walkJFast ctx visit pm (UInt32.ofNat rem) mk du D M) M := by
  intro rem
  induction rem with
  | zero =>
    intro mk du D M _ _
    rw [walkJFast, dif_neg (by decide)]
    exact Or.inr rfl
  | succ rem ih =>
    intro mk du D M hrem hM
    have hpos : UInt32.ofNat (rem + 1) > 0 := by
      change 0 < (UInt32.ofNat (rem + 1)).toNat
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega
    have hsub : UInt32.ofNat (rem + 1) - 1 = UInt32.ofNat rem := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt hrem, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [walkJFast, dif_pos hpos]
    dsimp only
    by_cases h1 : (mk == 0) = true
    · rw [if_pos h1]; exact Or.inr rfl
    · rw [if_neg h1]
      set c := (baGetU16 ctx.ciBA D.toUSize).toUSize
      set o := baGetU8 M c
      by_cases h2 : (o == pm) = true
      · rw [if_pos h2]; exact Or.inr rfl
      · rw [if_neg h2]
        by_cases h3 : (o != 0 && decide (ctx.bm ≤ du)) = true
        · rw [if_pos h3]; exact Or.inr rfl
        · rw [if_neg h3, hsub]
          set du' := if (o != 0) = true then du + 1 else du
          set M0 := baSetU8 M c pm
          have hM0_sz : M0.size < 2 ^ 32 := by rw [baSetU8_size]; exact hM
          have hM1_id : Id1 (if ((mk &&& 1) != 0) = true then visit (UInt32.ofNat rem) D du' M0 else M0) M0 := by
            by_cases hb : ((mk &&& 1) != 0) = true
            · rw [if_pos hb]; exact hvid _ _ _ M0 hM0_sz
            · rw [if_neg hb]; exact Or.inr rfl
          generalize (if ((mk &&& 1) != 0) = true then visit (UInt32.ofNat rem) D du' M0 else M0) = M1 at hM1_id
          by_cases hz1 : (M1.usize == 0) = true
          · rw [if_pos hz1]
            have hM1_lt : M1.size < 2 ^ 32 := by
              rcases hM1_id with h | h
              · omega
              · rw [h]; exact hM0_sz
            exact Or.inl ((ba_usize_eq_zero_iff hM1_lt).mp hz1)
          · rw [if_neg hz1]
            have hM1_eq : M1 = M0 := by
              rcases hM1_id with h | h
              · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz1
              · exact h
            subst hM1_eq
            have hM2_id : Id1 (if ((mk >>> 1) != 0) = true then
                walkJFast ctx visit pm (UInt32.ofNat rem) (mk >>> 1) du' (baGetU16 ctx.nxtBA D.toUSize) M0 else M0) M0 := by
              by_cases hm : ((mk >>> 1) != 0) = true
              · rw [if_pos hm]; exact ih (mk >>> 1) du' (baGetU16 ctx.nxtBA D.toUSize) M0 (by omega) hM0_sz
              · rw [if_neg hm]; exact Or.inr rfl
            generalize (if ((mk >>> 1) != 0) = true then
                walkJFast ctx visit pm (UInt32.ofNat rem) (mk >>> 1) du' (baGetU16 ctx.nxtBA D.toUSize) M0 else M0) = M2 at hM2_id
            by_cases hz2 : (M2.usize == 0) = true
            · rw [if_pos hz2]
              have hM2_lt : M2.size < 2 ^ 32 := by
                rcases hM2_id with h | h
                · omega
                · rw [h]; exact hM0_sz
              exact Or.inl ((ba_usize_eq_zero_iff hM2_lt).mp hz2)
            · rw [if_neg hz2]
              rcases hM2_id with h | h
              · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz2
              · rw [h]; exact Or.inr (baSetU8_restore M c pm hM)

theorem loopU32_id (lim : UInt32) (step : UInt32 → ByteArray → ByteArray)
    (hsid : ∀ j M, M.size < 2 ^ 32 → Id1 (step j M) M) :
    ∀ (rem : ℕ) (idx : UInt32) (M : ByteArray),
      lim.toNat - idx.toNat = rem → M.size < 2 ^ 32 → Id1 (loopU32 lim idx step M) M := by
  intro rem
  induction rem with
  | zero =>
    intro idx M hrem _
    rw [loopU32, dif_neg (by change ¬ idx.toNat < lim.toNat; omega)]
    exact Or.inr rfl
  | succ rem ih =>
    intro idx M hrem hM
    have hlt : idx < lim := by change idx.toNat < lim.toNat; omega
    rw [loopU32, dif_pos hlt]
    dsimp only
    have hs := hsid idx M hM
    generalize step idx M = M' at hs
    by_cases hz : (M'.usize == 0) = true
    · rw [if_pos hz]
      have hM'_lt : M'.size < 2 ^ 32 := by
        rcases hs with h | h
        · omega
        · rw [h]; exact hM
      exact Or.inl ((ba_usize_eq_zero_iff hM'_lt).mp hz)
    · rw [if_neg hz]
      rcases hs with h | h
      · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz
      · rw [h]
        have hadd : (idx + 1).toNat = idx.toNat + 1 := by
          rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by have := lim.toNat_lt; omega)]
        exact ih (idx + 1) M (by rw [hadd]; omega) hM

theorem go_id (ctx : FastJ16Ctx) :
    ∀ (fuel : ℕ) (st am pMM : UInt64) (M : ByteArray),
      fuel < 2 ^ 32 → M.size < 2 ^ 32 → Id1 (go ctx (UInt32.ofNat fuel) st am pMM M) M := by
  have hbind : ∀ {M0 M1 : ByteArray} {f : ByteArray → ByteArray},
      M0.size < 2 ^ 32 → Id1 M1 M0 → Id1 (f M0) M0 → Id1 (if (M1.usize == 0) = true then M1 else f M1) M0 := by
    intro M0 M1 f hM0 h1 hf
    by_cases hz : (M1.usize == 0) = true
    · rw [if_pos hz]
      have hlt : M1.size < 2 ^ 32 := by
        rcases h1 with h | h
        · omega
        · rw [h]; exact hM0
      exact Or.inl ((ba_usize_eq_zero_iff hlt).mp hz)
    · rw [if_neg hz]
      rcases h1 with h | h
      · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz
      · rw [h]; exact hf
  have hite : ∀ {c : Prop} [Decidable c] {X Y M0 : ByteArray},
      Id1 X M0 → Id1 Y M0 → Id1 (if c then X else Y) M0 := by
    intro c _ X Y M0 hX hY; by_cases hc : c <;> simp [hc, hX, hY]
  intro fuel
  induction fuel with
  | zero =>
    intro st am pMM M _ _
    rw [go, dif_neg (by decide)]
    exact Or.inl ByteArray.size_empty
  | succ fuel ih =>
    intro st am pMM M hfuel hM
    have hpos : UInt32.ofNat (fuel + 1) > 0 := by
      change 0 < (UInt32.ofNat (fuel + 1)).toNat
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hfuel]; omega
    have hsub : UInt32.ofNat (fuel + 1) - 1 = UInt32.ofNat fuel := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hfuel]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt hfuel, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [go, dif_pos hpos]
    set i : UInt32 := (st &&& 15).toUInt32
    set t : UInt32 := ((st >>> 4) &&& 15).toUInt32
    set r : UInt32 := ((st >>> 8) &&& 255).toUInt32
    set d : UInt32 := ((st >>> 16) &&& 255).toUInt32
    set b : UInt32 := ((st >>> 24) &&& 255).toUInt32
    set du : UInt32 := ((st >>> 32) &&& 15).toUInt32
    set z : UInt32 := ((st >>> 36) &&& 8191).toUInt32
    set q : UInt32 := ((st >>> 49) &&& 8191).toUInt32
    apply hite _ (Or.inr rfl)
    set fuel' := UInt32.ofNat (fuel + 1) - 1
    set a := fstI64 am
    set m := sndI64 am
    set pm := fstI64 pMM
    set pM := sndI64 pMM
    set c := getKd ctx i
    set wt := d + 6 * t
    set y := b - wt
    set v := vOfFast t r d
    set M1 :=
      if compOkFast ctx i a y v (checkEarly ctx i r q d) &&
          (if c == 0 then 2 <= r && getLo ctx i <= d && d <= getHi ctx i && s3Contains ctx q z
           else m < v) &&
          xcFast ctx i c t r d a b pm pM then
        if i + 1 == ctx.np then ByteArray.empty
        else
          let ni := i + 1
          let na := a - v
          let mk := computeMask ctx ni 0 1 0 na y (-6)
          if mk == 0 then M
          else
            let pmMark := UInt8.ofNat (ni.toNat + 1)
            let nam := packI32Pair na (-6)
            loopU32 5040 0 (fun D M' =>
              walkJFast ctx (fun n e du' M'' =>
                go ctx fuel' (packSt ni 0 1 n y du' D e) nam 0 M'')
                pmMark 6 mk du D M') M
      else M
    apply hbind (M1 := M1) (f := fun M1 =>
      let m' := if m > v then m else v
      let nam' := packI32Pair a m'
      let pmMark := UInt8.ofNat (i.toNat + 1)
      let cq := if ctx.js then baGetU16 ctx.b2CiBA q.toUSize else 9999
      let fBase := ctx.pa * u32ToI64 r - ctx.pb * u32ToI64 d - ctx.ph2 * u32ToI64 t
      let M2 :=
        if k3OkFast ctx i c t r d a b y v && xrFast ctx 0 i c t r d a b pm pM then
          let nr := r + 1
          let mk := computeMask ctx i t nr d a b m'
          if mk == 0 then M1
          else
            let npm := if pm < fBase then pm else fBase
            let npM := if pM > fBase then pM else fBase
            let npMM := packI32Pair npm npM
            let s3Base := q.toUSize * 6
            loopU32 6 0 (fun idx M' =>
              let D := baGetU16 ctx.s3BA (s3Base + idx.toUSize)
              let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
              if emk == 0 then M'
              else walkJFast ctx (fun n e du' M'' =>
                go ctx fuel' (packSt i t nr (d + n) b du' z e) nam' npMM M'')
                pmMark 6 emk du D M') M1
        else M1
      if M2.usize == 0 then M2
      else if k4OkFast ctx i c t a y v && xrFast ctx 1 i c t r d a b pm pM then
        let nt1 := t + 1
        let nr := r + 1
        let mk := computeMask ctx i nt1 nr d a b m'
        if mk == 0 then M2
        else
          let fp := fBase - ctx.ph
          let npm := if pm < fp then pm else fp
          let npM := if pM > fp then pM else fp
          let npMM := packI32Pair npm npM
          let s4Base := q.toUSize * 24
          loopU32 24 0 (fun idx M' =>
            let D := baGetU16 ctx.s4BA (s4Base + idx.toUSize)
            let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
            if emk == 0 then M'
            else walkJFast ctx (fun n e du' M'' =>
              go ctx fuel' (packSt i nt1 nr (d + n) b du' z e) nam' npMM M'')
              pmMark 6 emk du D M') M2
      else M2) hM
    · dsimp only [M1]
      apply hite _ (Or.inr rfl)
      apply hite (Or.inl ByteArray.size_empty)
      apply hite (Or.inr rfl)
      exact loopU32_id 5040 _ (fun D M' hM' =>
        walkJFast_id ctx _ (fun n e du' M'' hM'' => by rw [hsub]; exact ih _ _ _ M'' (by omega) hM'') _ 6 _ _ D M' (by decide) hM')
        _ 0 M rfl hM
    · set m' := if m > v then m else v
      set nam' := packI32Pair a m'
      set pmMark := UInt8.ofNat (i.toNat + 1)
      set cq := if ctx.js then baGetU16 ctx.b2CiBA q.toUSize else 9999
      set fBase := ctx.pa * u32ToI64 r - ctx.pb * u32ToI64 d - ctx.ph2 * u32ToI64 t
      set M2 :=
        if k3OkFast ctx i c t r d a b y v && xrFast ctx 0 i c t r d a b pm pM then
          let nr := r + 1
          let mk := computeMask ctx i t nr d a b m'
          if mk == 0 then M
          else
            let npm := if pm < fBase then pm else fBase
            let npM := if pM > fBase then pM else fBase
            let npMM := packI32Pair npm npM
            let s3Base := q.toUSize * 6
            loopU32 6 0 (fun idx M' =>
              let D := baGetU16 ctx.s3BA (s3Base + idx.toUSize)
              let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
              if emk == 0 then M'
              else walkJFast ctx (fun n e du' M'' =>
                go ctx fuel' (packSt i t nr (d + n) b du' z e) nam' npMM M'')
                pmMark 6 emk du D M') M
        else M
      apply hbind (M1 := M2) (f := fun M2 =>
        if k4OkFast ctx i c t a y v && xrFast ctx 1 i c t r d a b pm pM then
          let nt1 := t + 1
          let nr := r + 1
          let mk := computeMask ctx i nt1 nr d a b m'
          if mk == 0 then M2
          else
            let fp := fBase - ctx.ph
            let npm := if pm < fp then pm else fp
            let npM := if pM > fp then pM else fp
            let npMM := packI32Pair npm npM
            let s4Base := q.toUSize * 24
            loopU32 24 0 (fun idx M' =>
              let D := baGetU16 ctx.s4BA (s4Base + idx.toUSize)
              let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == cq then mk &&& 1 else mk
              if emk == 0 then M'
              else walkJFast ctx (fun n e du' M'' =>
                go ctx fuel' (packSt i nt1 nr (d + n) b du' z e) nam' npMM M'')
                pmMark 6 emk du D M') M2
        else M2) hM
      · dsimp only [M2]
        apply hite _ (Or.inr rfl)
        apply hite (Or.inr rfl)
        exact loopU32_id 6 _ (fun idx M' hM' =>
          hite (Or.inr rfl) (walkJFast_id ctx _ (fun n e du' M'' hM'' => by rw [hsub]; exact ih _ _ _ M'' (by omega) hM'') _ 6 _ _ _ M' (by decide) hM'))
          _ 0 M rfl hM
      · apply hite _ (Or.inr rfl)
        apply hite (Or.inr rfl)
        exact loopU32_id 24 _ (fun idx M' hM' =>
          hite (Or.inr rfl) (walkJFast_id ctx _ (fun n e du' M'' hM'' => by rw [hsub]; exact ih _ _ _ M'' (by omega) hM'') _ 6 _ _ _ M' (by decide) hM'))
          _ 0 M rfl hM

/-! ### Section 3: Exact `sdTab 7 3` / `sdTab 7 4` Length Bounds & Indexed Lookup -/

private theorem nodup_len_le {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → l₁.Subset l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    have ha : a ∈ l₂ := hsub List.mem_cons_self
    have hnd_t := (List.nodup_cons.mp hnd).2
    have hnot : a ∉ t := (List.nodup_cons.mp hnd).1
    have hsub' : t.Subset (l₂.erase a) := fun x hx =>
      (List.mem_erase_of_ne (fun h => by subst h; exact hnot hx)).mpr (hsub (List.mem_cons_of_mem _ hx))
    have ih := nodup_len_le t (l₂.erase a) hnd_t hsub'
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

private theorem permW_of_idx7 {j : ℕ} (hj : j < (permCodes 7 7).length) :
    ∃ v : List ℕ, PermW 7 v ∧ encB 7 v = j := by
  have hmem : (permCodes 7 7)[j]'hj ∈ permCodes 7 7 := List.getElem_mem hj
  obtain ⟨v, hv, hcode⟩ := permW_of_mem_permCodes7 hmem
  refine ⟨v, hv, ?_⟩
  unfold encB
  rw [hcode]
  exact (permCodes_nodup 7 (by omega) 7).idxOf_getElem j hj

private theorem wlink_of_ovlF {d : ℕ} (hd : d ≤ 7) {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v)
    (h : PS.ovlF (16 ^ 6 - 1) (16 ^ (7 - d)) (16 ^ d) (S.code u) (S.code v) = true) :
    WLink 7 d u v := by
  have hx : PermW 7 (u.rotate 6) := hu.rotate _
  have e1 : PS.excF (16 ^ 6 - 1) (S.code u) = S.code (u.rotate 6) := by
    show S.excF (16 ^ (7 - 1) - 1) (S.code u) = _
    rw [S.excF_eq, S.exc_code 7 u hu.2.1 (hu.lt16 (by omega)) (by omega)]
  have e2 : S.code (u.rotate 6) % 16 ^ (7 - d) = S.code ((u.rotate 6).drop d) := by
    have hl : ((u.rotate 6).drop d).length = 7 - d := by rw [List.length_drop, hx.2.1]
    have hlt := S.code_lt ((u.rotate 6).drop d) (fun a ha => hx.lt16 (by omega) a (List.mem_of_mem_drop ha))
    rw [hl] at hlt
    have e : S.code (u.rotate 6) = S.code ((u.rotate 6).take d) * 16 ^ (7 - d) + S.code ((u.rotate 6).drop d) := by
      conv_lhs => rw [← List.take_append_drop d (u.rotate 6)]
      rw [S.code_append, hl]
    rw [e]; exact S.mul_add_mod' hlt
  have e3 : S.code v / 16 ^ d = S.code (v.take (7 - d)) := by
    have hl : (v.drop (7 - d)).length = d := by rw [List.length_drop, hv.2.1]; omega
    have hlt := S.code_lt (v.drop (7 - d)) (fun a ha => hv.lt16 (by omega) a (List.mem_of_mem_drop ha))
    rw [hl] at hlt
    have e : S.code v = S.code (v.take (7 - d)) * 16 ^ d + S.code (v.drop (7 - d)) := by
      conv_lhs => rw [← List.take_append_drop (7 - d) v]
      rw [S.code_append, hl]
    rw [e]; exact S.mul_add_div' hlt
  unfold PS.ovlF at h
  rw [e1, e2, e3, beq_iff_eq] at h
  exact S.code_inj _ _ (by rw [List.length_drop, List.length_take, hx.2.1, hv.2.1]; omega)
    (fun a ha => hx.lt16 (by omega) a (List.mem_of_mem_drop ha))
    (fun a ha => hv.lt16 (by omega) a (List.mem_of_mem_take ha)) h

private theorem sdTab_mem_wlink {d q j : ℕ} (hd : d ≤ 7) (hq : q < (permCodes 7 7).length)
    (hj : j ∈ (sdTab 7 d (permCodes 7 7))[q]!) :
    ∃ u v : List ℕ, PermW 7 u ∧ PermW 7 v ∧ encB 7 u = q ∧ encB 7 v = j ∧ WLink 7 d u v := by
  have hsd_sz : (sdTab 7 d (permCodes 7 7)).size = (permCodes 7 7).length := by
    simp [sdTab]
  have hsd_get : (sdTab 7 d (permCodes 7 7))[q]! =
      (List.range (permCodes 7 7).length).filter
        (fun i => PS.ovlF (16 ^ 6 - 1) (16 ^ (7 - d)) (16 ^ d) ((permCodes 7 7)[q]'hq) ((permCodes 7 7).toArray[i]!)) := by
    rw [getElem!_pos _ _ (by rw [hsd_sz]; exact hq)]
    simp only [sdTab, List.getElem_toArray, List.getElem_map]
  rw [hsd_get, List.mem_filter, List.mem_range] at hj
  obtain ⟨u, hu, huq⟩ := permW_of_idx7 hq
  obtain ⟨v, hv, hvj⟩ := permW_of_idx7 hj.1
  have hu_c : (permCodes 7 7)[q]'hq = S.code u := by
    have hmem : S.code u ∈ permCodes 7 7 := PS.mem_perm (by omega) hu
    have hlt := List.idxOf_lt_length_iff.mpr hmem
    have hget := List.getElem_idxOf hlt
    have heq : (permCodes 7 7).idxOf (S.code u) = q := huq
    simpa [heq] using hget
  have hv_c : (permCodes 7 7).toArray[j]! = S.code v := by
    rw [getElem!_pos _ _ (by simp [hj.1])]
    have hmem : S.code v ∈ permCodes 7 7 := PS.mem_perm (by omega) hv
    have hlt := List.idxOf_lt_length_iff.mpr hmem
    have hget := List.getElem_idxOf hlt
    have heq : (permCodes 7 7).idxOf (S.code v) = j := hvj
    change (permCodes 7 7)[j]'(hj.1) = S.code v
    simpa [heq] using hget
  have hovl := hj.2
  rw [hu_c, hv_c] at hovl
  exact ⟨u, v, hu, hv, huq, hvj, wlink_of_ovlF hd hu hv hovl⟩

private theorem permW_rot_wlink_eq {d : ℕ} (hd : d ≤ 6) {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v)
    (hwl : WLink 7 d u v) (hrot : u ~r v) : v = (u.rotate 6).rotate d := by
  set x := u.rotate 6
  have hx : PermW 7 x := hu.rotate 6
  have hrot_ev : x ~r v := (List.IsRotated.symm ⟨6, rfl⟩).trans hrot
  obtain ⟨m, hm⟩ := hrot_ev
  have hm' : v = x.rotate (m % 7) := by
    have h1 : x.rotate (m % x.length) = x.rotate m := List.rotate_mod x m
    rw [hx.2.1] at h1; rw [h1]; exact hm.symm
  have hlt : m % 7 < 7 := Nat.mod_lt _ (by omega)
  have hdrop : x.drop d = v.take (7 - d) := hwl
  have hhead : (x.rotate (m % 7)).head? = (x.drop d).head? := by
    have htk : (x.rotate (m % 7)).take (7 - d) = x.drop d := by rw [← hm']; exact hdrop.symm
    have := congrArg List.head? htk
    have hne : 7 - d ≠ 0 := by omega
    rw [List.head?_take, if_neg hne] at this; exact this
  have heq : m % 7 = d := by
    by_contra hne
    have hget1 : x[m % 7]'(by rw [hx.2.1]; omega) = x[d]'(by rw [hx.2.1]; omega) := by
      have h1 : (x.rotate (m % 7)).head? = some (x[m % 7]'(by rw [hx.2.1]; omega)) := by
        rw [List.head?_eq_getElem?, List.getElem?_rotate (by rw [hx.2.1]; omega)]
        simp [hx.2.1, Nat.mod_eq_of_lt hlt]
      have h2 : (x.drop d).head? = some (x[d]'(by rw [hx.2.1]; omega)) := by
        rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem (by rw [hx.2.1]; omega)]
      rw [h1, h2] at hhead; exact Option.some.inj hhead
    exact hne ((List.Nodup.getElem_inj_iff hx.1).mp hget1)
  rw [hm', heq]

theorem sdTab3_len_le {q : ℕ} (hq : q < (permCodes 7 7).length) :
    ((sdTab 7 3 (permCodes 7 7))[q]!).length ≤ 6 := by
  obtain ⟨u, hu, huq⟩ := permW_of_idx7 hq
  have hnd : ((sdTab 7 3 (permCodes 7 7))[q]!).Nodup := by
    rw [getElem!_pos _ _ (by simp [sdTab, hq])]; simp only [sdTab, List.getElem_toArray, List.getElem_map]
    exact List.Nodup.filter _ List.nodup_range
  let cand : List ℕ := encB 7 ((u.rotate 6).rotate 3) :: (List.range 5).map (fun t => encB 7 (FastSound.w3Step u t))
  have hsub : ((sdTab 7 3 (permCodes 7 7))[q]!).Subset cand := by
    intro j hj
    obtain ⟨u', v, hu', hv, hu'q, hvj, hwl⟩ := sdTab_mem_wlink (by omega) hq hj
    have hu_eq : u' = u := by
      have h1 : S.code u' = S.code u := by
        have hmu := PS.mem_perm (k := 7) (by omega) hu
        have hmu' := PS.mem_perm (k := 7) (by omega) hu'
        have hgu := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmu)
        have hgu' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmu')
        have heq : (permCodes 7 7).idxOf (S.code u') = (permCodes 7 7).idxOf (S.code u) := hu'q.trans huq.symm
        rw [← hgu', ← hgu]; congr 1
      exact S.code_inj u' u (by rw [hu'.2.1, hu.2.1]) (hu'.lt16 (by omega)) (hu.lt16 (by omega)) h1
    subst hu_eq
    by_cases hrot : u' ~r v
    · dsimp only [cand]; rw [← hvj, permW_rot_wlink_eq (by omega) hu' hv hwl hrot]; exact List.mem_cons_self
    · dsimp only [cand]; apply List.mem_cons_of_mem
      obtain ⟨t, ht, hv_eq⟩ := w3Step_complete hu' hv hwl hrot
      exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, by rw [← hv_eq, hvj]⟩
  calc ((sdTab 7 3 (permCodes 7 7))[q]!).length ≤ cand.length := nodup_len_le _ _ hnd hsub
    _ = 6 := by simp [cand]

theorem sdTab4_len_le {q : ℕ} (hq : q < (permCodes 7 7).length) :
    ((sdTab 7 4 (permCodes 7 7))[q]!).length ≤ 24 := by
  obtain ⟨u, hu, huq⟩ := permW_of_idx7 hq
  have hnd : ((sdTab 7 4 (permCodes 7 7))[q]!).Nodup := by
    rw [getElem!_pos _ _ (by simp [sdTab, hq])]; simp only [sdTab, List.getElem_toArray, List.getElem_map]
    exact List.Nodup.filter _ List.nodup_range
  let cand : List ℕ := encB 7 ((u.rotate 6).rotate 4) :: (List.range 23).map (fun t => encB 7 (FastSound.w4Step u t))
  have hsub : ((sdTab 7 4 (permCodes 7 7))[q]!).Subset cand := by
    intro j hj
    obtain ⟨u', v, hu', hv, hu'q, hvj, hwl⟩ := sdTab_mem_wlink (by omega) hq hj
    have hu_eq : u' = u := by
      have h1 : S.code u' = S.code u := by
        have hmu := PS.mem_perm (k := 7) (by omega) hu
        have hmu' := PS.mem_perm (k := 7) (by omega) hu'
        have hgu := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmu)
        have hgu' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmu')
        have heq : (permCodes 7 7).idxOf (S.code u') = (permCodes 7 7).idxOf (S.code u) := hu'q.trans huq.symm
        rw [← hgu', ← hgu]; congr 1
      exact S.code_inj u' u (by rw [hu'.2.1, hu.2.1]) (hu'.lt16 (by omega)) (hu.lt16 (by omega)) h1
    subst hu_eq
    by_cases hrot : u' ~r v
    · dsimp only [cand]; rw [← hvj, permW_rot_wlink_eq (by omega) hu' hv hwl hrot]; exact List.mem_cons_self
    · dsimp only [cand]; apply List.mem_cons_of_mem
      obtain ⟨t, ht, hv_eq⟩ := w4Step_complete hu' hv hwl hrot
      exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, by rw [← hv_eq, hvj]⟩
  calc ((sdTab 7 4 (permCodes 7 7))[q]!).length ≤ cand.length := nodup_len_le _ _ hnd hsub
    _ = 24 := by simp [cand]

theorem sdTab3_mem_idx {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (hw : WLink 7 3 u v) :
    ∃ idx < 6, ((sdTab 7 3 (permCodes 7 7))[encB 7 u]!).getD idx 0 = encB 7 v := by
  have hmem := (PS.encB_enc 7 (by omega) (by omega)).s3_mem u v hu hv hw
  obtain ⟨idx, hidx_lt, hget⟩ := List.getElem_of_mem hmem
  have hle := sdTab3_len_le (encB_lt hu)
  refine ⟨idx, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some, hget]

theorem sdTab4_mem_idx {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (hw : WLink 7 4 u v) :
    ∃ idx < 24, ((sdTab 7 4 (permCodes 7 7))[encB 7 u]!).getD idx 0 = encB 7 v := by
  have hmem := (PS.encB_enc 7 (by omega) (by omega)).s4_mem u v hu hv hw
  obtain ⟨idx, hidx_lt, hget⟩ := List.getElem_of_mem hmem
  have hle := sdTab4_len_le (encB_lt hu)
  refine ⟨idx, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some, hget]

theorem sdTab_elem_lt {d q idx : ℕ} (hq : q < (permCodes 7 7).length) :
    ((sdTab 7 d (permCodes 7 7))[q]!).getD idx 0 < 65536 := by
  by_cases hlt : idx < ((sdTab 7 d (permCodes 7 7))[q]!).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    set row := (sdTab 7 d (permCodes 7 7))[q]!
    set val := row[idx]'hlt
    have hmem : val ∈ row := List.getElem_mem hlt
    have hrow : row = (List.range (permCodes 7 7).length).filter
        (fun i => PS.ovlF (16 ^ 6 - 1) (16 ^ (7 - d)) (16 ^ d) ((permCodes 7 7)[q]'hq) ((permCodes 7 7).toArray[i]!)) := by
      dsimp only [row]; rw [getElem!_pos _ _ (by simp [sdTab, hq])]; simp only [sdTab, List.getElem_toArray, List.getElem_map]
    rw [hrow, List.mem_filter, List.mem_range] at hmem
    have := permCodes7_length_le; omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

/-! ### Section 4: `prevOkFast` Factoring Lemma & Value Bounds -/

theorem exists_le_of_minUp_lt (g : ℕ → ℤ) :
    ∀ n : ℕ, J16.minUp g n < 1000000000 → ∃ w ≤ n, g w ≤ J16.minUp g n := by
  intro n
  unfold J16.minUp
  have haux : ∀ (init : ℤ) (m : ℕ), KS.minLe (fun _ => true) g init m < init →
      ∃ w ≤ m, g w ≤ KS.minLe (fun _ => true) g init m := by
    intro init m
    induction m with
    | zero =>
      intro hlt
      simp only [KS.minLe, ite_true] at hlt ⊢
      by_cases h0 : g 0 ≤ init
      · exact ⟨0, le_refl 0, by rw [min_eq_right h0]⟩
      · rw [min_eq_left (le_of_lt (not_le.mp h0))] at hlt; omega
    | succ m ih =>
      intro hlt
      simp only [KS.minLe, ite_true] at hlt ⊢
      by_cases hcmp : g (m + 1) ≤ KS.minLe (fun _ => true) g init m
      · exact ⟨m + 1, le_refl _, by rw [min_eq_right hcmp]⟩
      · rw [min_eq_left (le_of_lt (not_le.mp hcmp))] at hlt ⊢
        obtain ⟨w, hw, hgw⟩ := ih hlt
        exact ⟨w, by omega, hgw⟩
  exact haux 1000000000 n

theorem minUp_add_const_le (f : ℕ → ℤ) (c R : ℤ) (n : ℕ) (hR : R < 1000000000)
    (h : J16.minUp (fun w => c + f w) n ≤ R) : c + J16.minUp f n ≤ R := by
  obtain ⟨w, hw, hgw⟩ := exists_le_of_minUp_lt (fun w => c + f w) n (lt_of_le_of_lt h hR)
  have hle := J16.minUp_le f hw
  linarith

theorem cn1F_add_le (nx : ℕ → ℤ) (pa pb : ℕ) (need R : ℤ) (om : ℕ) (hR : R < 1000000000)
    (h : cn1F nx pa pb need om ≤ R) : (pa : ℤ) * need + cn1F nx pa pb 0 om ≤ R := by
  unfold cn1F at h ⊢
  have heq : (fun w => J16.cF nx pa pb need om w) = (fun w => (pa : ℤ) * need + J16.cF nx pa pb 0 om w) := by
    funext w; unfold J16.cF; ring
  rw [heq] at h
  exact minUp_add_const_le _ _ _ _ hR h

theorem a2pF_add_le (seg : ℕ → ℕ → ℤ) (nx : ℕ → ℤ) (pa pb tl : ℕ) (need R : ℤ) (om : ℕ)
    (hR : R < 1000000000) (h : a2pF seg nx pa pb tl need om ≤ R) :
    (pa : ℤ) * need + a2pF seg nx pa pb tl 0 om ≤ R := by
  unfold a2pF at h ⊢
  have heq : (fun w => J16.cF nx pa pb need om w - seg tl w) =
      (fun w => (pa : ℤ) * need + (J16.cF nx pa pb 0 om w - seg tl w)) := by
    funext w; unfold J16.cF; ring
  rw [heq] at h
  exact minUp_add_const_le _ _ _ _ hR h

/-! ### Value Bounds (Preventing `Int64` Overflow in All Precomputed Tables) -/

private theorem maxLe_bounds_j {f : ℕ → ℤ} {n : ℕ} {lo hi : ℤ}
    (hlo : lo ≤ -1000000000) (hhi : -1000000000 ≤ hi)
    (hf : ∀ i ≤ n, lo ≤ f i ∧ f i ≤ hi) : lo ≤ maxLe f n ∧ maxLe f n ≤ hi := by
  induction n with
  | zero => exact hf 0 (le_refl 0)
  | succ n ih =>
    have h1 := ih (fun i h => hf i (by omega))
    have h2 := hf (n + 1) (le_refl _)
    unfold maxLe
    exact ⟨le_trans h1.1 (le_max_left _ _), max_le h1.2 h2.2⟩

private theorem minUp_bounds_j {f : ℕ → ℤ} {n : ℕ} {lo hi : ℤ}
    (hhi : 1000000000 ≤ hi) (hf : ∀ i ≤ n, lo ≤ f i) :
    min 1000000000 lo ≤ J16.minUp f n ∧ J16.minUp f n ≤ hi := by
  unfold J16.minUp
  have haux : ∀ m ≤ n, min 1000000000 lo ≤ KS.minLe (fun _ => true) f 1000000000 m ∧
      KS.minLe (fun _ => true) f 1000000000 m ≤ hi := by
    intro m hm
    induction m with
    | zero =>
      simp only [KS.minLe, ite_true]
      exact ⟨le_min (min_le_left _ _) (le_trans (min_le_right _ _) (hf 0 (by omega))),
        le_trans (min_le_left _ _) hhi⟩
    | succ m ih =>
      simp only [KS.minLe, ite_true]
      have h1 := ih (by omega)
      exact ⟨le_min h1.1 (le_trans (min_le_right _ _) (hf (m + 1) hm)),
        le_trans (min_le_left _ _) h1.2⟩
  exact haux n (le_refl n)

private theorem pval_bounds {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} (hP : ∀ t x, P t x ≤ 200)
    (hPR : ∀ x, PR x ≤ 200) (sp : ℕ × ℕ × ℕ) (w : ℕ) (hw : w ≤ 200) :
    -1000000000 ≤ pval P PR 6 sp w ∧ pval P PR 6 sp w ≤ 200 := by
  unfold pval
  split_ifs with h0 h1
  · have := hPR w; omega
  · unfold negInf; omega
  · apply maxLe_bounds_j (by omega) (by omega)
    intro t _
    split_ifs
    · unfold sval; have := hP t (w - 6 * t); omega
    · unfold negInf; omega

private theorem bestF_bounds {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} (hP : ∀ t x, P t x ≤ 200)
    (hPR : ∀ x, PR x ≤ 200) :
    ∀ (specs : List (ℕ × ℕ × ℕ)) (y : ℕ), specs.length ≤ 10 → y ≤ 200 →
      -(specs.length : ℤ) * 1000000000 - 1000000000 ≤ bestF P PR 6 specs y ∧
      bestF P PR 6 specs y ≤ (specs.length : ℤ) * 200 := by
  intro specs
  induction specs with
  | nil => intro y _ _; simp [bestF]
  | cons sp rest ih =>
    intro y hlen hy
    simp only [bestF, List.length_cons] at hlen ⊢
    apply maxLe_bounds_j (by omega) (by omega)
    intro w hw
    have h1 := pval_bounds hP hPR sp w (by omega)
    have h2 := ih (y - w) (by omega) (by omega)
    push_cast; constructor <;> linarith

private theorem bestStep_bounds {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} {B : ℕ → ℤ}
    (hP : ∀ t x, P t x ≤ 200) (hPR : ∀ x, PR x ≤ 200)
    (hB : ∀ y ≤ 200, -12000000000 ≤ B y ∧ B y ≤ 2000)
    (sp : ℕ × ℕ × ℕ) (y : ℕ) (hy : y ≤ 200) :
    -14000000000 ≤ bestStep P PR 6 sp B y ∧ bestStep P PR 6 sp B y ≤ 2200 := by
  unfold bestStep
  apply maxLe_bounds_j (by omega) (by omega)
  intro w hw
  have h1 := pval_bounds hP hPR sp w (by omega)
  have h2 := hB (y - w) (by omega)
  omega

private theorem segF_bounds {P : ℕ → ℕ → ℕ} (hP : ∀ t x, P t x ≤ 200)
    {pa pb ph : ℕ} (hpa : pa ≤ 100) (hpb : pb ≤ 100) (hph : ph ≤ 100)
    (tl w : ℕ) (htl : tl ≤ 15) (hw : w ≤ 200) :
    -1000000000 ≤ segF P 6 pa pb ph tl w ∧ segF P 6 pa pb ph tl w ≤ 20000 := by
  unfold segF
  apply maxLe_bounds_j (by omega) (by omega)
  intro u hu
  apply maxLe_bounds_j (by omega) (by omega)
  intro e he
  split_ifs
  · have h1 := hP u e
    have h2 : (pa : ℤ) * (P u e : ℤ) ≤ 20000 := by
      have : (P u e : ℤ) ≤ 200 := by exact_mod_cast h1
      have : (pa : ℤ) ≤ 100 := by exact_mod_cast hpa
      nlinarith
    have h3 : (pb : ℤ) * (e : ℤ) ≤ 20000 := by
      have : (e : ℤ) ≤ 200 := by omega
      have : (pb : ℤ) ≤ 100 := by exact_mod_cast hpb
      nlinarith
    have h4 : (2 * (ph : ℤ)) * (u : ℤ) ≤ 3000 := by
      have : (u : ℤ) ≤ 15 := by omega
      have : (ph : ℤ) ≤ 100 := by exact_mod_cast hph
      nlinarith
    have h1z : (0 : ℤ) ≤ (pa : ℤ) * (P u e : ℤ) := by positivity
    have h2z : (0 : ℤ) ≤ (pb : ℤ) * (e : ℤ) := by positivity
    have h3z : (0 : ℤ) ≤ (2 * (ph : ℤ)) * (u : ℤ) := by positivity
    omega
  · unfold negInf; omega

private theorem fG_bounds {P : ℕ → ℕ → ℕ} {PR : ℕ → ℕ} {B : ℕ → ℤ}
    (hPR : ∀ x, PR x ≤ 200) (hB : ∀ y ≤ 200, -12000000000 ≤ B y ∧ B y ≤ 2000)
    (lo hi : ℕ) (vlo : ℤ) (b r d : ℕ) (hb : b ≤ 200) :
    -15000000000 ≤ fG P PR B lo hi vlo b r d ∧ fG P PR B lo hi vlo b r d ≤ 2200 := by
  unfold fG
  apply maxLe_bounds_j (by omega) (by omega)
  intro H hH
  split_ifs
  · have ht_le : J15.tmax P PR r d H ≤ PR H := by
      unfold J15.tmax; split_ifs
      · exact Nat.min_le_left _ _
      · exact le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)
    have h1 := hPR H; have h2 := hB (b - H) (by omega); omega
  · unfold negInf; omega

private theorem cn1F_zero_bounds {nx : ℕ → ℤ} (hnx : ∀ y ≤ 200, -12000000000 ≤ nx y ∧ nx y ≤ 2000)
    {pa pb : ℕ} (hpa : pa ≤ 100) (hpb : pb ≤ 100) (om : ℕ) (hom : om ≤ 200) :
    -10000000 ≤ cn1F nx pa pb 0 om ∧ cn1F nx pa pb 0 om ≤ 1000000000 := by
  unfold cn1F
  have h := minUp_bounds_j (f := fun w => J16.cF nx pa pb 0 om w) (n := om) (lo := -10000000) (hi := 1000000000) (le_refl _) (by
    intro w hw
    unfold J16.cF
    have h1 := (hnx (om - w) (by omega)).2
    have hpaZ : (0 : ℤ) ≤ pa ∧ (pa : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast hpa⟩
    have hpbZ : (0 : ℤ) ≤ pb ∧ (pb : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast hpb⟩
    have hwZ : (0 : ℤ) ≤ w ∧ (w : ℤ) ≤ 200 := ⟨by positivity, by omega⟩
    have hm1 : (pa : ℤ) * (0 - nx (om - w)) ≥ -200000 := by nlinarith
    have hm2 : ((pb : ℤ) - pa) * w ≤ 20000 := by nlinarith
    linarith)
  exact ⟨by omega, h.2⟩

private theorem a2pF_zero_bounds {seg : ℕ → ℕ → ℤ} {nx : ℕ → ℤ}
    (hseg : ∀ tl ≤ 15, ∀ w ≤ 200, -1000000000 ≤ seg tl w ∧ seg tl w ≤ 20000)
    (hnx : ∀ y ≤ 200, -12000000000 ≤ nx y ∧ nx y ≤ 2000)
    {pa pb : ℕ} (hpa : pa ≤ 100) (hpb : pb ≤ 100) (tl om : ℕ) (htl : tl ≤ 15) (hom : om ≤ 200) :
    -10000000 ≤ a2pF seg nx pa pb tl 0 om ∧ a2pF seg nx pa pb tl 0 om ≤ 1000000000 := by
  unfold a2pF
  have h := minUp_bounds_j (f := fun w => J16.cF nx pa pb 0 om w - seg tl w) (n := om) (lo := -10000000) (hi := 1000000000) (le_refl _) (by
    intro w hw
    unfold J16.cF
    have h1 := (hnx (om - w) (by omega)).2
    have h2 := (hseg tl htl w (by omega)).2
    have hpaZ : (0 : ℤ) ≤ pa ∧ (pa : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast hpa⟩
    have hpbZ : (0 : ℤ) ≤ pb ∧ (pb : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast hpb⟩
    have hwZ : (0 : ℤ) ≤ w ∧ (w : ℤ) ≤ 200 := ⟨by positivity, by omega⟩
    have hm1 : (pa : ℤ) * (0 - nx (om - w)) ≥ -200000 := by nlinarith
    have hm2 : ((pb : ℤ) - pa) * w ≤ 20000 := by nlinarith
    linarith)
  exact ⟨by omega, h.2⟩

/-! ### Section 5: `Rule JS` Normal Form for Joint Counterexamples (`exists_nf_noJS`) -/

private theorem clsCount_replace (pre post : List (List ℕ)) {x y : List ℕ} (hxy : x ~r y) :
    clsCount (pre ++ y :: post) = clsCount (pre ++ x :: post) := by
  have hperm1 : (pre ++ y :: post).Perm (y :: (pre ++ post)) := List.perm_middle
  have hperm2 : (pre ++ x :: post).Perm (x :: (pre ++ post)) := List.perm_middle
  rw [clsCount_perm hperm1, clsCount_perm hperm2, J15.clsCount_cons, J15.clsCount_cons]
  have hiff : (∃ u ∈ pre ++ post, u ~r y) ↔ (∃ u ∈ pre ++ post, u ~r x) :=
    ⟨fun ⟨u, hu, hr⟩ => ⟨u, hu, hr.trans hxy.symm⟩, fun ⟨u, hu, hr⟩ => ⟨u, hu, hr.trans hxy⟩⟩
  by_cases h : ∃ u ∈ pre ++ post, u ~r x
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- Single `Rule JS` shift on a piece `L`, preserving `IsPieceCV`, `blocksR` rotation classes,
    first block, `wtK`, `valK`, `Good`, and strictly increasing `K16.psi`. -/
theorem shift_pieceCV {q : Q} {L : List TRow} (hL : IsPieceCV 7 q L) (hno : ¬ K16.NoJS 7 L) :
    ∃ N : List TRow, IsPieceCV 7 q N ∧ N.length = L.length ∧ wtK 7 N = wtK 7 L ∧
      valK 7 N = valK 7 L ∧ (∀ a b h, Good 7 a b h L → Good 7 a b h N) ∧
      K16.psi N = K16.psi L + 1 ∧
      (∃ pre post x y, blocksR L = pre ++ x :: post ∧ blocksR N = pre ++ y :: post ∧ x ~r y) ∧
      N.head?.bind (fun r => r.2.head?) = L.head?.bind (fun r => r.2.head?) := by
  have hseq : IsSeq 7 L := hL.1.1.isSeq
  have htag : ∀ x ∈ L, x.1 ≤ 1 := hL.1.1.le_one
  unfold K16.NoJS K16.JSBad at hno
  push Not at hno
  obtain ⟨U, R, R', W, hL_eq, hR, v, f, F, hRb', hrot⟩ := hno
  subst hL_eq
  obtain ⟨kdR, Rb⟩ := R
  obtain ⟨kd', Rb'⟩ := R'
  simp only at hR hRb' hrot
  subst hRb'
  have hRmem : (kdR, Rb) ∈ U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W := by simp
  have hR'mem : (kd', v :: f :: F) ∈ U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W := by simp
  have hq_mem : Rb.getLast hR ∈ Rb := List.getLast_mem hR
  set ql := Rb.getLast hR
  have hwR := hseq.words (kdR, Rb) hRmem
  have hwR' := hseq.words (kd', v :: f :: F) hR'mem
  have hqp : PermW 7 ql := hwR ql hq_mem
  have hvp : PermW 7 v := hwR' v List.mem_cons_self
  have hfp : PermW 7 f := hwR' f (by simp)
  have hcl := hseq.classes
  have hflat : ((U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).map Prod.snd).flatten =
      ((U.map Prod.snd).flatten ++ Rb) ++ v :: (f :: F ++ (W.map Prod.snd).flatten) := by simp
  rw [hflat] at hcl
  have hvf : ¬ v ~r f := (List.pairwise_cons.mp (List.pairwise_append.mp hcl).2.1).1 f (by simp)
  have hdvf := List.isChain_cons_cons.mp (hseq.doors (kd', v :: f :: F) hR'mem)
  have hfe : f = K16.tau2 7 v := S.door_of_link (by omega) hvp hfp hdvf.1 hvf
  have hkd' : kd' ≤ 1 := htag (kd', v :: f :: F) hR'mem
  have hlinkRR : LinkK 7 kd' ql v := by
    have hch := hseq.links
    have hpair : List.IsChain (fun a b => ∀ (ha : a.2 ≠ []) (hb : b.2 ≠ []),
        LinkK 7 b.1 (a.2.getLast ha) (b.2.head hb)) ((kdR, Rb) :: (kd', v :: f :: F) :: W) := by
      have h1 := List.IsChain.infix hch (List.suffix_append _ _).isInfix
      exact h1
    exact (List.isChain_cons_cons.mp hpair).1 hR (List.cons_ne_nil v (f :: F))
  have hvRb : ∀ w ∈ Rb, ¬ w ~r v := by
    intro w hw hwr
    have hpw := List.pairwise_append.mp hcl
    exact hpw.2.2 w (List.mem_append_right _ hw) v List.mem_cons_self hwr
  have hRpw : List.Pairwise (fun a b => ¬ a ~r b) Rb :=
    (List.pairwise_append.mp (List.pairwise_append.mp hcl).1).2.1
  have hsz := hseq.size_le _ hRmem
  have hsz' := hseq.size_le _ hR'mem
  simp only at hsz hsz'
  have hRlen : Rb.length + 1 ≤ 6 := by
    by_contra hcon
    have hlen : Rb.length = 6 := by omega
    have ht := K16.tau2_getLast_row (by omega) hR hwR (hseq.doors _ hRmem) hRpw hlen
    rw [ht] at hrot
    exact hvRb _ (List.head_mem hR) hrot.symm
  let N := U ++ (kdR, Rb ++ [K16.tau2 7 ql]) :: (kd', f :: F) :: W
  have hNseq : IsSeq 7 N := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx w hw
      rcases List.mem_append.mp hx with hx | hx
      · exact hseq.words x (List.mem_append_left _ hx) w hw
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_append.mp hw with hw | hw
        · exact hwR w hw
        · rw [List.mem_singleton.mp hw]; exact K16.permW_tau2 (by omega) hqp
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hwR' w (List.mem_cons_of_mem _ hw)
      · exact hseq.words x (by simp [hx]) w hw
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hseq.pieces_ne x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact hseq.pieces_ne x (by simp [hx])
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hseq.size_le x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_append, List.length_singleton]; exact hRlen
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_cons] at hsz' ⊢; omega
      · exact hseq.size_le x (by simp [hx])
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hseq.doors x (List.mem_append_left _ hx)
      rcases List.mem_cons.mp hx with rfl | hx
      · refine List.IsChain.append (hseq.doors _ hRmem) (List.isChain_singleton _) ?_
        intro z hz w hw
        rw [List.getLast?_eq_some_getLast hR, Option.mem_def, Option.some.injEq] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
        rw [← hz, ← hw]; exact K16.wlink2_tau2 (by omega) hqp.2.1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hdvf.2
      · exact hseq.doors x (by simp [hx])
    · refine K16.chain_replace hseq.links ?_ ?_ ?_
      · intro z hz hzx hy
        have e : ((kdR, Rb ++ [K16.tau2 7 ql]) : TRow).2.head hy = Rb.head hR := by
          simp [List.head_append_of_ne_nil hR]
        rw [e]; exact hz hzx hR
      · intro hx hy
        have e1 : ((kdR, Rb ++ [K16.tau2 7 ql]) : TRow).2.getLast hx = K16.tau2 7 ql := by simp
        have e2 : ((kd', f :: F) : TRow).2.head hy = K16.tau2 7 v := by simp [hfe]
        rw [e1, e2]; exact K16.link_tau2 (by omega) hkd' hqp hlinkRR hrot
      · intro z hz hy hzz
        have e : ((kd', f :: F) : TRow).2.getLast hy =
            ((kd', v :: f :: F) : TRow).2.getLast (List.cons_ne_nil _ _) := by
          simp [List.getLast_cons]
        rw [e]; exact hz (List.cons_ne_nil _ _) hzz
    · have hflat' : (N.map Prod.snd).flatten =
          ((U.map Prod.snd).flatten ++ Rb) ++ K16.tau2 7 ql :: (f :: F ++ (W.map Prod.snd).flatten) := by
        simp [N]
      rw [hflat']
      exact K16.pairwise_replace hcl hrot.symm
  have hNlen : N.length = (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).length := by simp [N]
  have hNmap : N.map Prod.fst = (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).map Prod.fst := by simp [N]
  have hNlinks : linksT N = linksT (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := K16.linksT_congr hNmap
  have hNholes : holesT 7 N = holesT 7 (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := by
    simp only [N, PS.holesT_append, PS.holesT_cons]
    simp only [List.length_append, List.length_cons, List.length_nil] at hsz' ⊢; omega
  have hNwt : wtK 7 N = wtK 7 (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := by
    unfold wtK; rw [hNholes, hNlinks]
  have hNval : valK 7 N = valK 7 (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W) := by
    unfold valK vOf; rw [hNlen, hNholes, hNlinks]
  have hNhead : N.head?.bind (fun r => r.2.head?) =
      (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).head?.bind (fun r => r.2.head?) := by
    cases U with
    | nil =>
      cases Rb with
      | nil => exact absurd rfl hR
      | cons a Rb' => simp [N]
    | cons u U' => simp [N]
  have hNlast : N.getLast?.bind (fun r => r.2.getLast?) =
      (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).getLast?.bind (fun r => r.2.getLast?) := by
    cases W using List.reverseRecOn with
    | nil =>
      have hne1 : [(kdR, Rb ++ [K16.tau2 7 ql]), (kd', f :: F)] ≠ [] := by simp
      have hne2 : [(kdR, Rb), (kd', v :: f :: F)] ≠ [] := by simp
      simp [N, List.getLast?_append_of_ne_nil _ hne1, List.getLast?_append_of_ne_nil _ hne2]
    | append_singleton W' w =>
      have hne : (kdR, Rb ++ [K16.tau2 7 ql]) :: (kd', f :: F) :: (W' ++ [w]) ≠ [] := List.cons_ne_nil _ _
      have hne2 : (kdR, Rb) :: (kd', v :: f :: F) :: (W' ++ [w]) ≠ [] := List.cons_ne_nil _ _
      simp only [N, List.getLast?_append_of_ne_nil _ hne, List.getLast?_append_of_ne_nil _ hne2,
        List.getLast?_cons_cons]
      have h1 : (kd', f :: F) :: (W' ++ [w]) = ((kd', f :: F) :: W') ++ [w] := rfl
      have h2 : (kd', v :: f :: F) :: (W' ++ [w]) = ((kd', v :: f :: F) :: W') ++ [w] := rfl
      rw [h1, h2, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
  have hNtake : ∀ i, holesT 7 (N.take i) ≤ holesT 7 ((U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).take i) := by
    intro i
    simp only [N, List.take_append, PS.holesT_append]
    have := K16.holes_take_pair (k := 7) (R0 := (kdR, Rb)) (R1 := (kd', v :: f :: F))
      (S0 := (kdR, Rb ++ [K16.tau2 7 ql])) (S1 := (kd', f :: F)) (W := W)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hsz' ⊢; omega)
      (i - U.length)
    omega
  refine ⟨N, ⟨⟨?_, fun h0 => by rw [hNval]; exact hL.1.2 h0⟩, ?_⟩, hNlen, hNwt, hNval, ?_, ?_, ?_, hNhead⟩
  · -- IsPieceW 7 q.1 N
    have hpw := hL.1.1
    unfold IsPieceW at hpw ⊢
    by_cases h0 : q.1.1 = 0
    · rw [if_pos h0] at hpw ⊢
      obtain ⟨_, hk0, h2, hcl, hlo, hhi⟩ := hpw
      refine ⟨hNseq, ?_, by omega, ?_, by omega, by omega⟩
      · intro x hx
        have : x.1 ∈ N.map Prod.fst := List.mem_map_of_mem hx
        rw [hNmap] at this
        obtain ⟨y, hy, hyx⟩ := List.mem_map.mp this
        rw [← hyx]; exact hk0 y hy
      · intro u hu v' hv'
        rw [hNlast] at hu; rw [hNhead] at hv'
        exact hcl u hu v' hv'
    · rw [if_neg h0] at hpw ⊢
      obtain ⟨_, hne, hk1, hlk⟩ := hpw
      refine ⟨hNseq, by simp [N], ?_, by omega⟩
      intro x hx
      have : x.1 ∈ N.map Prod.fst := List.mem_map_of_mem hx
      rw [hNmap] at this
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp this
      rw [← hyx]; exact hk1 y hy
  · -- Cyc 7 N
    intro h0 u w hN_eq
    have hu_eq : N.take u.length = u := by rw [hN_eq, List.take_left]
    have hu_le : u.length ≤ (U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).length := by
      rw [← hNlen, hN_eq, List.length_append]; omega
    have ht := hNtake u.length
    rw [hu_eq] at ht
    have hcyc := hL.2 h0 ((U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).take u.length)
      ((U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W).drop u.length) (List.take_append_drop _ _).symm
    rw [List.length_take, Nat.min_eq_left hu_le] at hcyc
    rw [hNlen, hNholes]
    exact le_trans (Nat.mul_le_mul_right _ ht) hcyc
  · -- Good
    intro a b h hG
    refine K16.good_transfer ?_ ?_ hG
    · intro i
      exact K16.phiAt_le_of (by simp [N]) (K16.linksT_congr (by simp [N, List.map_take]))
        (hNtake i) (K16.hdK_congr (by simp [N, List.map_drop]))
    · have hne1 : N ≠ [] := by simp [N]
      have hne2 : U ++ (kdR, Rb) :: (kd', v :: f :: F) :: W ≠ [] := by simp
      rw [KS.phiAt_end a b h hne1, KS.phiAt_end a b h hne2, hNlinks, hNholes, hNlen]
  · -- psi
    simp only [N, K16.psi_append, K16.psi, List.length_cons, List.length_append, List.length_nil]
    ring
  · -- blocksR replace
    refine ⟨(U.map Prod.snd).flatten ++ Rb, f :: F ++ (W.map Prod.snd).flatten, v, K16.tau2 7 ql, ?_, ?_, hrot⟩
    · simp [blocksR]
    · simp [N, blocksR]

private theorem forall₂_append_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {u₁ u₂ : List β}, List.Forall₂ R l (u₁ ++ u₂) →
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ List.Forall₂ R l₁ u₁ ∧ List.Forall₂ R l₂ u₂
  | l, [], u₂, h => ⟨[], l, rfl, List.Forall₂.nil, h⟩
  | [], _ :: _, _, h => by cases h
  | a :: l, b :: u₁, u₂, List.Forall₂.cons hab h => by
    obtain ⟨l₁, l₂, rfl, h1, h2⟩ := forall₂_append_right h
    exact ⟨a :: l₁, l₂, rfl, List.Forall₂.cons hab h1, h2⟩

/-- Normal form of a counterexample ALSO satisfying `K16.NoJS 7` on every piece! -/
theorem exists_nf_noJS {qs : List Q} {V : ℤ} {W B : ℕ} (rp pa pb ph oi : ℕ)
    (hne : qs ≠ [])
    (hoi : oi + 1 < qs.length → qs.getD oi dq = qs.getD (oi + 1) dq)
    (hfail : ¬ JV 7 qs V W B) :
    ∃ Ls, CEV 7 qs V W B Ls ∧
      (∀ Ls', CEV 7 qs V W B Ls' → Ls.flatten.length ≤ Ls'.flatten.length) ∧
      NF 7 qs rp pa pb ph oi Ls ∧
      (∀ L ∈ Ls, K16.NoJS 7 L) ∧
      ∃ kd0 R1 S1 Post1, Ls = ((kd0, List.range' 1 7 :: R1) :: S1) :: Post1 := by
  obtain ⟨Ls0, hce0, hmin0, hnf0, kd0, R1, S1, Post1, hLs0⟩ :=
    J16.exists_nf (k := 7) (by omega) rp pa pb ph oi hne hoi hfail
  let gap : List (List TRow) → ℕ := fun Ls => (Ls.map fun L => 6 * L.length * L.length - K16.psi L).sum
  have hstep : ∀ (n : ℕ) (Ls : List (List TRow)),
      gap Ls ≤ n →
      CEV 7 qs V W B Ls →
      (∀ Ls', CEV 7 qs V W B Ls' → Ls.flatten.length ≤ Ls'.flatten.length) →
      NF 7 qs rp pa pb ph oi Ls →
      (∃ kd0 R1 S1 Post1, Ls = ((kd0, List.range' 1 7 :: R1) :: S1) :: Post1) →
      ∃ Ls', CEV 7 qs V W B Ls' ∧
        (∀ Ls'', CEV 7 qs V W B Ls'' → Ls'.flatten.length ≤ Ls''.flatten.length) ∧
        NF 7 qs rp pa pb ph oi Ls' ∧
        (∀ L ∈ Ls', K16.NoJS 7 L) ∧
        ∃ kd0 R1 S1 Post1, Ls' = ((kd0, List.range' 1 7 :: R1) :: S1) :: Post1 := by
    intro n
    induction n with
    | zero =>
      intro Ls hgap hce hmin hnf hhead
      refine ⟨Ls, hce, hmin, hnf, ?_, hhead⟩
      intro L hL
      by_contra hno
      obtain ⟨A, B', hAB⟩ := List.append_of_mem hL
      have hfa := hce.1
      rw [hAB] at hfa
      have hqL : ∃ q, IsPieceCV 7 q L := by
        obtain ⟨qA, qB, _, _, hfaB⟩ := forall₂_append_right hfa
        cases hfaB with
        | cons hq _ => exact ⟨_, hq⟩
      obtain ⟨q, hq⟩ := hqL
      have hpsi_lt : K16.psi L < 6 * L.length * L.length := by
        obtain ⟨N, hN, hNlen, _, _, _, hNpsi, _, _⟩ := shift_pieceCV hq hno
        have hle := K16.psi_le (k := 7) N hN.1.1.isSeq.size_le
        change K16.psi N ≤ 6 * N.length * N.length at hle
        rw [hNlen, hNpsi] at hle; omega
      have hpos : 0 < gap Ls := by
        dsimp only [gap]; rw [hAB]; simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
        omega
      omega
    | succ n ih =>
      intro Ls hgap hce hmin hnf hhead
      by_cases hall : ∀ L ∈ Ls, K16.NoJS 7 L
      · exact ⟨Ls, hce, hmin, hnf, hall, hhead⟩
      · push Not at hall
        obtain ⟨L, hL, hno⟩ := hall
        obtain ⟨A, B', hAB⟩ := List.append_of_mem hL
        have hfa := hce.1
        rw [hAB] at hfa
        obtain ⟨qA, qB, hq_eq, hfaA, hfaB⟩ := forall₂_append_right hfa
        cases hfaB with
        | @cons q _ qB' _ hq hfaB' =>
          obtain ⟨N, hN, hNlen, hNwt, hNval, hNgood, hNpsi, ⟨pre, post, x, y, hbx, hby, hxy⟩, hNhd⟩ :=
            shift_pieceCV hq hno
          let Ls1 := A ++ N :: B'
          have hfa1 : List.Forall₂ (IsPieceCV 7) qs Ls1 := by
            rw [hq_eq]; exact J15.forall₂_app hfaA (List.Forall₂.cons hN hfaB')
          have hSh1 : Sh B Ls1 := by
            have hs := hce.2.1
            rw [hAB] at hs
            unfold Sh at hs ⊢
            simp only [Ls1, List.flatten_append, List.flatten_cons, blocksR_append] at hs ⊢
            rw [hbx] at hs; rw [hby]
            have e1 : blocksR A.flatten ++ (pre ++ x :: post ++ blocksR B'.flatten) =
                (blocksR A.flatten ++ pre) ++ x :: (post ++ blocksR B'.flatten) := by simp
            have e2 : blocksR A.flatten ++ (pre ++ y :: post ++ blocksR B'.flatten) =
                (blocksR A.flatten ++ pre) ++ y :: (post ++ blocksR B'.flatten) := by simp
            rw [e1] at hs; rw [e2, clsCount_replace _ _ hxy]
            simp only [List.length_append, List.length_cons] at hs ⊢; exact hs
          have hW1 : (Ls1.map (wtK 7)).sum ≤ W := by
            have h := hce.2.2.1; rw [hAB] at h
            simp only [Ls1, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hNwt] at h ⊢; exact h
          have hV1 : V ≤ (Ls1.map (valK 7)).sum := by
            have h := hce.2.2.2; rw [hAB] at h
            simp only [Ls1, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hNval] at h ⊢; exact h
          have hce1 : CEV 7 qs V W B Ls1 := ⟨hfa1, hSh1, hW1, hV1⟩
          have hflat1 : Ls1.flatten.length = Ls.flatten.length := by
            rw [hAB]; simp only [Ls1, List.flatten_append, List.flatten_cons, List.length_append, hNlen]
          have hmin1 : ∀ Ls', CEV 7 qs V W B Ls' → Ls1.flatten.length ≤ Ls'.flatten.length := fun Ls' h' => by
            rw [hflat1]; exact hmin Ls' h'
          have hgetD : ∀ i, Ls1.getD i [] = if i = A.length then N else Ls.getD i [] := by
            intro i; rw [hAB]
            by_cases hi : i = A.length
            · subst hi; simp [Ls1, J15.getD_mid]
            · rw [if_neg hi]; dsimp only [Ls1]
              by_cases hlt : i < A.length
              · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_append_left hlt, List.getElem?_append_left hlt]
              · have hgt : A.length < i := by omega
                rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
                cases hsub : i - A.length with
                | zero => omega
                | succ j => simp
          have hnf1 : NF 7 qs rp pa pb ph oi Ls1 := by
            refine ⟨fun h1 h2 => ?_, fun h1 => ?_⟩
            · rw [hgetD rp]; split_ifs with hrp
              · subst hrp; have hg := hnf.good h1 h2; rw [hAB, J15.getD_mid] at hg; exact hNgood _ _ _ hg
              · exact hnf.good h1 h2
            · have hv : ∀ i, valK 7 (Ls1.getD i []) = valK 7 (Ls.getD i []) := fun i => by
                rw [hgetD i]; split_ifs with hi
                · subst hi; rw [hAB, J15.getD_mid, hNval]
                · rfl
              rw [hv, hv]; exact hnf.ord h1
          have hhead1 : ∃ kd0 R1 S1 Post1, Ls1 = ((kd0, List.range' 1 7 :: R1) :: S1) :: Post1 := by
            obtain ⟨kd0', R1', S1', Post1', hLs_eq⟩ := hhead
            cases A with
            | nil =>
              have hLeq : L = (kd0', List.range' 1 7 :: R1') :: S1' := by
                have := hAB.symm.trans hLs_eq; exact (List.cons.inj this).1
              have hB'eq : B' = Post1' := (List.cons.inj (hAB.symm.trans hLs_eq)).2
              obtain ⟨x0, N', hN_eq⟩ := List.exists_cons_of_ne_nil hN.1.1.ne_nil
              obtain ⟨kdn, Qn⟩ := x0
              obtain ⟨vn, Rn, hQn⟩ := List.exists_cons_of_ne_nil (hN.1.1.isSeq.pieces_ne _ (by rw [hN_eq]; exact List.mem_cons_self))
              subst hQn
              have hvn : vn = List.range' 1 7 := by
                rw [hN_eq, hLeq] at hNhd; simpa using hNhd
              subst hvn
              exact ⟨kdn, Rn, N', B', by simp [Ls1, hN_eq]⟩
            | cons a A' =>
              have ha_eq : a = (kd0', List.range' 1 7 :: R1') :: S1' := by
                have := hAB.symm.trans hLs_eq; exact (List.cons.inj this).1
              exact ⟨kd0', R1', S1', A' ++ N :: B', by simp [Ls1, ha_eq]⟩
          have hpsi_le : K16.psi N ≤ 6 * N.length * N.length := K16.psi_le (k := 7) N hN.1.1.isSeq.size_le
          have hgap1 : gap Ls1 ≤ n := by
            dsimp only [gap] at hgap ⊢
            rw [hAB] at hgap
            simp only [Ls1, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hNlen, hNpsi] at hgap ⊢
            rw [hNlen, hNpsi] at hpsi_le
            omega
          exact ih Ls1 hgap1 hce1 hmin1 hnf1 hhead1
  exact hstep (gap Ls0) Ls0 (le_refl _) hce0 hmin0 hnf0 ⟨kd0, R1, S1, Post1, hLs0⟩

/-- Piece-level `Rule JS` invariant along the flattened row list `rest`. -/
def NoJSAlongJ (last : List ℕ) : List TRow → Prop
  | [] => True
  | (0, v :: R) :: rest => (v ~r K16.tau2 7 last → R = []) ∧ NoJSAlongJ ((v :: R).getLast (List.cons_ne_nil v R)) rest
  | (1, v :: R) :: rest => (v ~r K16.tau2 7 last → R = []) ∧ NoJSAlongJ ((v :: R).getLast (List.cons_ne_nil v R)) rest
  | (_ + 2, v :: R) :: rest => NoJSAlongJ ((v :: R).getLast (List.cons_ne_nil v R)) rest
  | (_, []) :: _ => True

private theorem noJSAlongJ_of_noJS_piece :
    ∀ (S : List TRow) (rest : List TRow) (last : List ℕ) (hlast_row : TRow)
      (hne : hlast_row.2 ≠ []) (heq : hlast_row.2.getLast hne = last),
      K16.NoJS 7 (hlast_row :: S) →
      (∀ x ∈ S, x.1 ≤ 1) →
      (∀ x ∈ S, x.2 ≠ []) →
      (∀ l, (∃ r ∈ S, ∃ hne' : r.2 ≠ [], r.2.getLast hne' = l) ∨ l = last → NoJSAlongJ l rest) →
      NoJSAlongJ last (S ++ rest)
  | [], rest, last, _, _, _, _, _, _, hrest => hrest last (Or.inr rfl)
  | (kd, []) :: _, _, _, _, _, _, _, _, hneS, _ => absurd rfl (hneS _ List.mem_cons_self)
  | (kd, v :: R) :: S', rest, last, hlast_row, hne, heq, hno, hle1, hneS, hrest => by
    have hkd : kd ≤ 1 := hle1 _ List.mem_cons_self
    have hstep : v ~r K16.tau2 7 last → R = [] := by
      intro hrot
      cases R with
      | nil => rfl
      | cons f F =>
        exact absurd ⟨hne, v, f, F, rfl, by rw [heq]; exact hrot⟩ (hno [] hlast_row (kd, v :: f :: F) S' rfl)
    have hno' : K16.NoJS 7 ((kd, v :: R) :: S') := fun U R0 R1 W h =>
      hno (hlast_row :: U) R0 R1 W (by simp [h])
    have ih := noJSAlongJ_of_noJS_piece S' rest ((v :: R).getLast (List.cons_ne_nil v R)) (kd, v :: R)
      (List.cons_ne_nil v R) rfl hno'
      (fun x hx => hle1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => hneS x (List.mem_cons_of_mem _ hx))
      (fun l hl => hrest l (by
        rcases hl with ⟨r, hr, hrne, hrl⟩ | rfl
        · exact Or.inl ⟨r, List.mem_cons_of_mem _ hr, hrne, hrl⟩
        · exact Or.inl ⟨(kd, v :: R), List.mem_cons_self, List.cons_ne_nil v R, rfl⟩))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
    · exact ⟨hstep, ih⟩
    · exact ⟨hstep, ih⟩

theorem noJSAlongJ_flatJ :
    ∀ (Post : List (List TRow)),
      (∀ L ∈ Post, K16.NoJS 7 L ∧ (∀ x ∈ L, x.1 ≤ 1) ∧ (∀ x ∈ L, x.2 ≠ []) ∧ L ≠ []) →
      ∀ last, NoJSAlongJ last (flatJ Post)
  | [], _, _ => trivial
  | L :: Post', hP, last => by
    have ⟨hno, hle1, hne, hLne⟩ := hP L List.mem_cons_self
    obtain ⟨⟨kd0, Q0⟩, S', rfl⟩ := List.exists_cons_of_ne_nil hLne
    obtain ⟨v, R0, rfl⟩ := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
    show NoJSAlongJ last ((2, v :: R0) :: (S' ++ flatJ Post'))
    dsimp only [NoJSAlongJ]
    exact noJSAlongJ_of_noJS_piece S' (flatJ Post') ((v :: R0).getLast (List.cons_ne_nil v R0))
      (kd0, v :: R0) (List.cons_ne_nil v R0) rfl hno
      (fun x hx => hle1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      (fun l _ => noJSAlongJ_flatJ Post' (fun M hM => hP M (List.mem_cons_of_mem _ hM)) l)

/-! ### Section 6: Gate Checking & Context Validity (`ValidJCtx`) -/

private theorem gateL_forall_digs :
    ∀ (gs : List (ℕ × ℕ × ℕ)) (tp i r key : ℕ),
      GateL gs tp i r key →
      ∀ j < (digs gs tp).length,
        let g := (digs gs tp)[j]!
        g.1 = i → g.2.1 = r → key % g.2.2.1 = g.2.2.2
  | [], _, _, _, _, _, j, hj => by simp [digs] at hj
  | (gi, gr, nt) :: gs, tp, i, r, key, hG, j, hj => by
    obtain ⟨h1, h2⟩ := hG
    cases j with
    | zero =>
      simp only [digs, List.getElem!_cons_zero]
      intro hi hr
      simp only [Gate] at h1
      rcases h1 with hne | hne | hmod
      · exact absurd hi.symm hne
      · exact absurd hr.symm hne
      · exact hmod
    | succ j =>
      simp only [digs, List.length_cons] at hj
      have hget : (digs ((gi, gr, nt) :: gs) tp)[j + 1]! = (digs gs (tp / nt))[j]! := by
        simp [digs]
      rw [hget]
      exact gateL_forall_digs gs (tp / nt) i r key h2 j (by omega)

private theorem earlyL_forall_digs :
    ∀ (gs : List (ℕ × ℕ × ℕ)) (tp i r key : ℕ),
      EarlyL gs tp i r key →
      ∀ j < (digs gs tp).length,
        let g := (digs gs tp)[j]!
        g.1 = i → r < g.2.1 → key % g.2.2.1 = g.2.2.2
  | [], _, _, _, _, _, j, hj => by simp [digs] at hj
  | (gi, gr, nt) :: gs, tp, i, r, key, hE, j, hj => by
    obtain ⟨h1, h2⟩ := hE
    cases j with
    | zero =>
      simp only [digs, List.getElem!_cons_zero]
      intro hi hr
      simp only [Early] at h1
      rcases h1 with hne | hge | hmod
      · exact absurd hi.symm hne
      · omega
      · exact hmod
    | succ j =>
      simp only [digs, List.length_cons] at hj
      have hget : (digs ((gi, gr, nt) :: gs) tp)[j + 1]! = (digs gs (tp / nt))[j]! := by
        simp [digs]
      rw [hget]
      exact earlyL_forall_digs gs (tp / nt) i r key h2 j (by omega)

private theorem digs_len (gs : List (ℕ × ℕ × ℕ)) (tp : ℕ) : (digs gs tp).length = gs.length := by
  induction gs generalizing tp with
  | nil => rfl
  | cons _ tl ih => simp [digs, ih]

private theorem digs_bounds :
    ∀ (gs : List (ℕ × ℕ × ℕ)) (tp : ℕ),
      (∀ g ∈ gs, g.1 < 16 ∧ g.2.1 < 256 ∧ 0 < g.2.2 ∧ g.2.2 < 65536) →
      ∀ j < (digs gs tp).length,
        let g := (digs gs tp)[j]!
        g.1 < 16 ∧ g.2.1 < 256 ∧ 0 < g.2.2.1 ∧ g.2.2.1 < 65536 ∧ g.2.2.2 < 65536
  | [], _, _, j, hj => by simp [digs] at hj
  | (gi, gr, nt) :: gs, tp, hgs, j, hj => by
    have h0 := hgs (gi, gr, nt) List.mem_cons_self
    cases j with
    | zero =>
      simp only [digs, List.getElem!_cons_zero]
      exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, lt_trans (Nat.mod_lt tp h0.2.2.1) h0.2.2.2⟩
    | succ j =>
      simp only [digs, List.length_cons] at hj
      have hget : (digs ((gi, gr, nt) :: gs) tp)[j + 1]! = (digs gs (tp / nt))[j]! := by
        simp [digs]
      rw [hget]
      exact digs_bounds gs (tp / nt) (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) j (by omega)

/-- Valid context for `FastJ16` matching `J16.RunOK` + `GateL`/`EarlyL`. -/
structure ValidJCtx (caps : List (List ℕ)) (PRl : List ℕ) (qs : List Q)
    (R : Rules) (W bm : ℕ) (gs : List (ℕ × ℕ × ℕ)) (js : Bool) (tp : ℕ)
    (ctx : FastJ16Ctx) : Prop where
  hnp : ctx.np = UInt32.ofNat qs.length
  hS  : ctx.S  = UInt32.ofNat (maxLeN (kdF (qs.map Prod.fst)) qs.length + 1)
  hC  : ctx.C  = UInt32.ofNat (W + 1)
  hRR : ctx.RR = UInt32.ofNat (maxLeN (fun x => PRl.getD x 0) W + 1)
  hbm : ctx.bm = UInt32.ofNat bm
  hrp : ctx.rp = UInt32.ofNat R.rp
  hoi : ctx.oi = UInt32.ofNat R.oi
  hpa : ctx.pa = Int64.ofInt R.pa
  hpb : ctx.pb = Int64.ofInt R.pb
  hph : ctx.ph = Int64.ofInt R.ph
  hph2 : ctx.ph2 = Int64.ofInt (2 * R.ph)
  hclip : ctx.clip = R.clip
  hjs : ctx.js = js
  hciBA : ∀ {u : List ℕ}, PermW 7 u →
    baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 u)).toUSize = UInt32.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 u]!)
  hnxtBA : ∀ {u : List ℕ}, PermW 7 u →
    baGetU16 ctx.nxtBA (UInt32.ofNat (encB 7 u)).toUSize = UInt32.ofNat ((nxtTab 7 (permCodes 7 7))[encB 7 u]!)
  hb2CiBA : ∀ {u : List ℕ}, PermW 7 u →
    baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 u)).toUSize =
      UInt32.ofNat ((ciTab 7 (permCodes 7 7))[(nxtTab 7 (permCodes 7 7))[encB 7 u]!]!)
  hs3BA : ∀ {u : List ℕ} {idx : ℕ}, PermW 7 u → idx < 6 →
    baGetU16 ctx.s3BA ((UInt32.ofNat (encB 7 u)).toUSize * 6 + USize.ofNat idx) =
      UInt32.ofNat (((sdTab 7 3 (permCodes 7 7))[encB 7 u]!).getD idx 0)
  hs4BA : ∀ {u : List ℕ} {idx : ℕ}, PermW 7 u → idx < 24 →
    baGetU16 ctx.s4BA ((UInt32.ofNat (encB 7 u)).toUSize * 24 + USize.ofNat idx) =
      UInt32.ofNat (((sdTab 7 4 (permCodes 7 7))[encB 7 u]!).getD idx 0)
  hkd : ∀ i < qs.length, getKd ctx (UInt32.ofNat i) = UInt32.ofNat (kdF (qs.map Prod.fst) i)
  hlo : ∀ i < qs.length, getLo ctx (UInt32.ofNat i) = UInt32.ofNat (loF (qs.map Prod.fst) i)
  hhi : ∀ i < qs.length, getHi ctx (UInt32.ofNat i) = UInt32.ofNat (hiF (qs.map Prod.fst) i)
  hvlo : ∀ i < qs.length, getVlo ctx (UInt32.ofNat i) = Int64.ofInt (vloF R i)
  hvhi : ∀ i < qs.length, getVhi ctx (UInt32.ofNat i) = Int64.ofInt (vhiF R i)
  hbest : ∀ i ≤ qs.length, ∀ y ≤ W,
    getBest ctx (UInt32.ofNat i) (UInt32.ofNat y) =
      Int64.ofInt (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y)
  hg : ∀ i < qs.length, ∀ u < maxLeN (kdF (qs.map Prod.fst)) qs.length + 1, ∀ y ≤ W,
    getG ctx (UInt32.ofNat i) (UInt32.ofNat u) (UInt32.ofNat y) =
      Int64.ofInt (bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y)
  hRB : ∀ u < maxLeN (kdF (qs.map Prod.fst)) qs.length + 1, ∀ y ≤ W,
    getRB ctx (UInt32.ofNat u) (UInt32.ofNat y) =
      Int64.ofInt (RBfOf 7 (capF caps) (fun x => PRl.getD x 0) u y)
  hF : ∀ i < qs.length, ∀ b ≤ W, ∀ r < 256, ∀ d < 256, kdF (qs.map Prod.fst) i = 0 → ∀ x : ℤ,
    -2 ^ 50 ≤ x → x ≤ 2 ^ 50 →
    x ≤ fG (capF caps) (fun x => PRl.getD x 0) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i)
        (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d →
    (R.clip = true → 0 ≤ fG (capF caps) (fun x => PRl.getD x 0) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i)
        (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) →
    ringOkFast ctx (UInt32.ofNat i) (UInt32.ofNat b) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt x) = true
  hcn1 : ∀ om ≤ W,
    baGetI64 ctx.cn1BaseBA (UInt32.ofNat om).toUSize =
      Int64.ofInt (cn1F (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp) R.pa R.pb 0 om)
  ha2p : ∀ tl < maxLeN (kdF (qs.map Prod.fst)) qs.length + 1, ∀ om ≤ W,
    baGetI64 ctx.a2pBaseBA (UInt32.ofNat tl * ctx.C + UInt32.ofNat om).toUSize =
      Int64.ofInt (a2pF (segF (capF caps) 6 R.pa R.pb R.ph)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp) R.pa R.pb tl 0 om)
  hgate : ∀ i r q d, i < 16 → r < 256 → q < 8192 → d < 256 →
    GateL gs tp i r (q + 8192 * d) →
    checkGate ctx (UInt32.ofNat i) (UInt32.ofNat r) (UInt32.ofNat q) (UInt32.ofNat d) = true
  hearly : ∀ i r q d, i < 16 → r < 256 → q < 8192 → d < 256 →
    EarlyL gs tp i r (q + 8192 * d) →
    checkEarly ctx (UInt32.ofNat i) (UInt32.ofNat r) (UInt32.ofNat q) (UInt32.ofNat d) = true

private theorem arr_map_getD {α : Type} (l : List α) (f : α → ℕ) (d : α) {i : ℕ} (hi : i < l.length) :
    ((l.map f).toArray)[i]! = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp [hi]

set_option maxHeartbeats 600000 in
private theorem capF_le_of_hcaps {caps : List (List ℕ)} (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200)
    (t x : ℕ) : capF caps t x ≤ 200 := by
  unfold capF
  by_cases ht : t < caps.length
  · have h1 : caps.getD t [] = caps[t]'ht := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    rw [h1]
    by_cases hx : x < (caps[t]'ht).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
      exact hcaps _ (List.getElem_mem ht) _ (List.getElem_mem hx)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _
  · have h1 : caps.getD t [] = [] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [h1]; exact Nat.zero_le _

private theorem PRl_getD_le_of_hPR {PRl : List ℕ} (hPR : ∀ v ∈ PRl, v ≤ 200) (x : ℕ) : PRl.getD x 0 ≤ 200 := by
  by_cases hx : x < PRl.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
    exact hPR _ (List.getElem_mem hx)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact Nat.zero_le _

private theorem BfOf_bounds {caps : List (List ℕ)} {PRl : List ℕ} {qs : List Q}
    (hnp : qs.length ≤ 10)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (j y : ℕ) (hy : y ≤ 200) :
    -12000000000 ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs j y ∧
    BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs j y ≤ 2000 := by
  have hb := bestF_bounds (capF_le_of_hcaps hcaps) (PRl_getD_le_of_hPR hPR)
    ((qs.map Prod.fst).drop (j + 1)) y (by simp; omega) hy
  have hlen : ((qs.map Prod.fst).drop (j + 1)).length ≤ 10 := by simp; omega
  have h1 : (((qs.map Prod.fst).drop (j + 1)).length : ℤ) * 200 ≤ 2000 := by omega
  have h2 : (((qs.map Prod.fst).drop (j + 1)).length : ℤ) * 1000000000 ≤ 10000000000 := by omega
  unfold BfOf; rw [show (7 - 1 : ℕ) = 6 from rfl]
  exact ⟨by omega, by omega⟩

theorem buildJoint_valid {caps : List (List ℕ)} {PRl : List ℕ} {qs : List Q}
    {R : Rules} {V W bm fuel : ℕ} {gs : List (ℕ × ℕ × ℕ)} {js : Bool} {tp : ℕ}
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (hspecs : ∀ q ∈ qs, q.1.1 < 16 ∧ q.1.2.1 < 256 ∧ q.1.2.2 < 256)
    (habh : R.pa ≤ 100 ∧ R.pb ≤ 100 ∧ R.ph ≤ 100)
    (hgs : ∀ g ∈ gs, g.1 < 16 ∧ g.2.1 < 256 ∧ 0 < g.2.2 ∧ g.2.2 < 65536)
    (hgs_len : gs.length < 100) :
    let bj := buildJoint caps PRl (qs.map Prod.fst) R V W bm fuel gs js
    let ds := digs bj.gs tp
    let ng := ds.length
    let ctx := { bj.ctx0 with
      gatePi := ByteArray.mk (Array.ofFn (n := ng) fun i => UInt8.ofNat (ds[i.val]!.1)),
      gateR  := ByteArray.mk (Array.ofFn (n := ng) fun i => UInt8.ofNat (ds[i.val]!.2.1)),
      gateMod := packU16Arr (Array.ofFn (n := ng) fun i => UInt32.ofNat (ds[i.val]!.2.2.1)),
      gateDig := packU16Arr (Array.ofFn (n := ng) fun i => UInt32.ofNat (ds[i.val]!.2.2.2)),
      ng := UInt32.ofNat ng }
    ValidJCtx caps PRl qs R W bm gs js tp ctx := by
  intro bj ds ng ctx
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  have hRR_le : maxLeN (fun x => PRl.getD x 0) W ≤ 200 := by
    have haux : ∀ n, maxLeN (fun x => PRl.getD x 0) n ≤ 200 := by
      intro n; induction n with
      | zero => exact hPR_le 0
      | succ n ih => exact max_le ih (hPR_le (n + 1))
    exact haux W
  have hsz_le := permCodes7_length_le
  set S_n := maxLeN (kdF (qs.map Prod.fst)) qs.length + 1
  set C_n := W + 1
  set RR_n := maxLeN (fun x => PRl.getD x 0) W + 1
  have hS_le : S_n ≤ 15 := by omega
  have hC_le : C_n ≤ 201 := by omega
  have hRR_n_le : RR_n ≤ 201 := by omega
  have hP_eq : look2 S_n C_n (tab2 S_n C_n (capF caps)) (capF caps) = capF caps :=
    J15.look2_tab2 S_n C_n (capF caps)
  have hPR_eq : (fun x => look2 1 C_n (tab2 1 C_n (fun _ x => PRl.getD x 0)) (fun _ x => PRl.getD x 0) 0 x) =
      (fun x => PRl.getD x 0) := by
    funext x; rw [J15.look2_tab2 1 C_n (fun _ x => PRl.getD x 0)]
  have hB_eq : look2 (qs.length + 1) C_n
      (tab2 (qs.length + 1) C_n (fun i y => bestF (capF caps) (fun x => PRl.getD x 0) 6 ((qs.map Prod.fst).drop (i + 1)) y))
      (fun i y => bestF (capF caps) (fun x => PRl.getD x 0) 6 ((qs.map Prod.fst).drop (i + 1)) y) =
      BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs :=
    J15.look2_tab2 _ _ _
  have hSG_eq : look2 S_n C_n (tab2 S_n C_n (segF (capF caps) 6 R.pa R.pb R.ph))
      (segF (capF caps) 6 R.pa R.pb R.ph) = segF (capF caps) 6 R.pa R.pb R.ph :=
    J15.look2_tab2 S_n C_n _
  have hRR_eq : maxLeN (fun x => look2 1 C_n (tab2 1 C_n (fun _ x => PRl.getD x 0)) (fun _ x => PRl.getD x 0) 0 x) W + 1 = RR_n := by
    rw [hPR_eq]
  have hlen_map : (qs.map Prod.fst).length = qs.length := List.length_map _
  have hS_def : maxLeN (kdF (qs.map Prod.fst)) (qs.map Prod.fst).length + 1 = S_n := by rw [hlen_map]
  have hds_eq : ds = digs gs tp := rfl
  have hng_eq : ng = gs.length := by rw [show ng = ds.length from rfl, hds_eq]; exact digs_len gs tp
  have hds_bd : ∀ j < ng, (ds[j]!).1 < 16 ∧ (ds[j]!).2.1 < 256 ∧ 0 < (ds[j]!).2.2.1 ∧ (ds[j]!).2.2.1 < 65536 ∧ (ds[j]!).2.2.2 < 65536 := by
    intro j hj; rw [hds_eq]; exact digs_bounds gs tp hgs j (by rw [← hds_eq]; exact hj)
  have h_u32_us : ∀ m < 2 ^ 32, (UInt32.ofNat m).toUSize = USize.ofNat m := by
    intro m hm; apply USize.toNat_inj.mp
    rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hm, usize_ofNat_toNat hm]
  have h_u32_lt : ∀ a b : ℕ, a < 2 ^ 32 → b < 2 ^ 32 → (UInt32.ofNat a < UInt32.ofNat b ↔ a < b) := by
    intro a b ha hb
    change (UInt32.ofNat a).toNat < (UInt32.ofNat b).toNat ↔ a < b
    rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have h_u32_le : ∀ a b : ℕ, a < 2 ^ 32 → b < 2 ^ 32 → (UInt32.ofNat a ≤ UInt32.ofNat b ↔ a ≤ b) := by
    intro a b ha hb
    change (UInt32.ofNat a).toNat ≤ (UInt32.ofNat b).toNat ↔ a ≤ b
    rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  -- Check each field of ValidJCtx cleanly
  refine ⟨by simp [ctx, bj, buildJoint], by simp [ctx, bj, buildJoint], rfl,
    by dsimp only [ctx, bj, buildJoint]; rw [hPR_eq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hciBA
    intro u hu
    have hlt := encB_lt hu
    have hci_lt := ciTab_lt hlt
    dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us _ (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; exact hlt)
      (by simp [getElem!_pos, hlt, UInt32.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    rw [getElem!_pos _ _ (by simp; exact hlt), Array.getElem_ofFn]
  · -- hnxtBA
    intro u hu
    have hlt := encB_lt hu
    have hn_lt := nxtTab_lt hlt
    dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us _ (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; exact hlt)
      (by simp [getElem!_pos, hlt, UInt32.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    rw [getElem!_pos _ _ (by simp; exact hlt), Array.getElem_ofFn]
  · -- hb2CiBA
    intro u hu
    have hlt := encB_lt hu
    have hn_lt := nxtTab_lt hlt
    have hci_lt := ciTab_lt hn_lt
    dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us _ (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; exact hlt)
      (by simp [getElem!_pos, hlt, UInt32.toNat_ofNat']; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
    rw [getElem!_pos _ _ (by simp; exact hlt), Array.getElem_ofFn]
  · -- hs3BA
    intro u idx hu hidx
    have hlt := encB_lt hu
    have hidx_tot : encB 7 u * 6 + idx < (permCodes 7 7).length * 6 := by omega
    have hus : (UInt32.ofNat (encB 7 u)).toUSize * 6 + USize.ofNat idx = USize.ofNat (encB 7 u * 6 + idx) := by
      apply USize.toNat_inj.mp
      have h6 : (6 : USize).toNat = 6 := by change (USize.ofNat 6).toNat = 6; exact usize_ofNat_toNat (by omega)
      rw [USize.toNat_add, USize.toNat_mul, UInt32.toNat_toUSize, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : encB 7 u < 2 ^ 32), h6, usize_ofNat_toNat (by omega : idx < 2 ^ 32),
        Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 u * 6 < 2 ^ 32)),
        Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 u * 6 + idx < 2 ^ 32)),
        usize_ofNat_toNat (by omega)]
    have helem_lt := sdTab_elem_lt (d := 3) (idx := idx) hlt
    dsimp only [ctx, bj, buildJoint]
    rw [hus, baGetU16_packU16Arr (by simp; omega) (by simp; exact hidx_tot) (by
      rw [getElem!_pos _ _ (by simp; exact hidx_tot), Array.getElem_ofFn]
      simp only [S.mul_add_div' hidx, S.mul_add_mod' hidx, UInt32.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]; exact helem_lt)]
    rw [getElem!_pos _ _ (by simp; exact hidx_tot), Array.getElem_ofFn]
    simp only [S.mul_add_div' hidx, S.mul_add_mod' hidx]
  · -- hs4BA
    intro u idx hu hidx
    have hlt := encB_lt hu
    have hidx_tot : encB 7 u * 24 + idx < (permCodes 7 7).length * 24 := by omega
    have hus : (UInt32.ofNat (encB 7 u)).toUSize * 24 + USize.ofNat idx = USize.ofNat (encB 7 u * 24 + idx) := by
      apply USize.toNat_inj.mp
      have h24 : (24 : USize).toNat = 24 := by change (USize.ofNat 24).toNat = 24; exact usize_ofNat_toNat (by omega)
      rw [USize.toNat_add, USize.toNat_mul, UInt32.toNat_toUSize, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : encB 7 u < 2 ^ 32), h24, usize_ofNat_toNat (by omega : idx < 2 ^ 32),
        Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 u * 24 < 2 ^ 32)),
        Nat.mod_eq_of_lt (lt_usize_size_of_lt_u32 (by omega : encB 7 u * 24 + idx < 2 ^ 32)),
        usize_ofNat_toNat (by omega)]
    have helem_lt := sdTab_elem_lt (d := 4) (idx := idx) hlt
    dsimp only [ctx, bj, buildJoint]
    rw [hus, baGetU16_packU16Arr (by simp; omega) (by simp; exact hidx_tot) (by
      rw [getElem!_pos _ _ (by simp; exact hidx_tot), Array.getElem_ofFn]
      simp only [S.mul_add_div' hidx, S.mul_add_mod' hidx, UInt32.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]; exact helem_lt)]
    rw [getElem!_pos _ _ (by simp; exact hidx_tot), Array.getElem_ofFn]
    simp only [S.mul_add_div' hidx, S.mul_add_mod' hidx]
  · -- hkd
    intro i hi
    have hsp := hspecs (qs[i]'hi) (List.getElem_mem hi)
    have hlt_map : i < (qs.map Prod.fst).length := by simp [hi]
    unfold getKd kdF; dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us i (by omega), baGetU8_ofFn _ (by omega) hlt_map]
    dsimp only
    rw [arr_map_getD _ _ (0, 0, 0) hlt_map]
    apply UInt32.toNat_inj.mp
    have hkd_lt : ((qs.map Prod.fst).getD i (0, 0, 0)).1 < 256 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_map]; simp; omega
    rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt hkd_lt, Nat.mod_eq_of_lt (by omega)]
  · -- hlo
    intro i hi
    have hsp := hspecs (qs[i]'hi) (List.getElem_mem hi)
    have hlt_map : i < (qs.map Prod.fst).length := by simp [hi]
    unfold getLo loF; dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us i (by omega), baGetU8_ofFn _ (by omega) hlt_map]
    dsimp only
    rw [arr_map_getD _ _ (0, 0, 0) hlt_map]
    apply UInt32.toNat_inj.mp
    have hlo_lt : ((qs.map Prod.fst).getD i (0, 0, 0)).2.1 < 256 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_map]; simp [hsp.2.1]
    rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt hlo_lt, Nat.mod_eq_of_lt (by omega)]
  · -- hhi
    intro i hi
    have hsp := hspecs (qs[i]'hi) (List.getElem_mem hi)
    have hlt_map : i < (qs.map Prod.fst).length := by simp [hi]
    unfold getHi hiF; dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us i (by omega), baGetU8_ofFn _ (by omega) hlt_map]
    dsimp only
    rw [arr_map_getD _ _ (0, 0, 0) hlt_map]
    apply UInt32.toNat_inj.mp
    have hhi_lt : ((qs.map Prod.fst).getD i (0, 0, 0)).2.2 < 256 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_map]; simp [hsp.2.2]
    rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt hhi_lt, Nat.mod_eq_of_lt (by omega)]
  · -- hvlo
    intro i hi
    unfold getVlo; dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us i (by omega), baGetI64_packI64Arr (by simp; omega) (by simp; exact hi),
      getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]
  · -- hvhi
    intro i hi
    unfold getVhi; dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us i (by omega), baGetI64_packI64Arr (by simp; omega) (by simp; exact hi),
      getElem!_pos _ _ (by simp; exact hi), Array.getElem_ofFn]
  · -- hbest
    intro i hi y hy
    unfold getBest; dsimp only [ctx, bj, buildJoint]
    have hc1 : UInt32.ofNat i ≤ UInt32.ofNat (qs.map Prod.fst).length :=
      (h_u32_le _ _ (by omega) (by rw [hlen_map]; omega)).mpr (by rw [hlen_map]; exact hi)
    have hc2 : UInt32.ofNat y < UInt32.ofNat (W + 1) :=
      (h_u32_lt _ _ (by omega) (by omega)).mpr (by omega)
    rw [if_pos (by simp only [hc1, hc2, decide_true, Bool.and_true])]
    have hidx_lt : i * C_n + y < (qs.length + 1) * C_n := by
      have : i * C_n + C_n = (i + 1) * C_n := by ring
      have : (i + 1) * C_n ≤ (qs.length + 1) * C_n := Nat.mul_le_mul_right _ (by omega)
      omega
    have hidx_u : (UInt32.ofNat i * UInt32.ofNat C_n + UInt32.ofNat y).toUSize = USize.ofNat (i * C_n + y) := by
      have h1 : i * C_n ≤ 10 * 201 := Nat.mul_le_mul (by omega) hC_le
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat',
        UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : i < 2 ^ 32), Nat.mod_eq_of_lt (by omega : C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : y < 2 ^ 32), Nat.mod_eq_of_lt (by omega : i * C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : i * C_n + y < 2 ^ 32), usize_ofNat_toNat (by omega)]
    rw [hidx_u, baGetI64_packI64Arr (by simp; have : (qs.length + 1) * (W + 1) ≤ 11 * 201 := Nat.mul_le_mul (by omega) (by omega); omega)
      (by simp; exact hidx_lt), getElem!_pos _ _ (by simp; exact hidx_lt), Array.getElem_ofFn]
    dsimp only
    rw [J15.tab2_get _ _ _ (by rw [hlen_map]; omega) (by omega), hS_def, hP_eq, hPR_eq]; rfl
  · -- hg
    intro i hi u hu y hy
    unfold getG; dsimp only [ctx, bj, buildJoint]
    have hc1 : UInt32.ofNat i < UInt32.ofNat (qs.map Prod.fst).length :=
      (h_u32_lt _ _ (by omega) (by rw [hlen_map]; omega)).mpr (by rw [hlen_map]; exact hi)
    have hc2 : UInt32.ofNat u < UInt32.ofNat (maxLeN (kdF (qs.map Prod.fst)) (qs.map Prod.fst).length + 1) :=
      (h_u32_lt _ _ (by omega) (by rw [hS_def]; omega)).mpr (by rw [hS_def]; exact hu)
    have hc3 : UInt32.ofNat y < UInt32.ofNat (W + 1) :=
      (h_u32_lt _ _ (by omega) (by omega)).mpr (by omega)
    rw [if_pos (by simp only [hc1, hc2, hc3, decide_true, Bool.and_true])]
    have hidx_lt : (i * S_n + u) * C_n + y < qs.length * S_n * C_n := by
      have h1 : i * S_n + S_n = (i + 1) * S_n := by ring
      have h2 : (i + 1) * S_n ≤ qs.length * S_n := Nat.mul_le_mul_right _ (by omega)
      have h3 : (i * S_n + u + 1) * C_n ≤ qs.length * S_n * C_n := Nat.mul_le_mul_right _ (by omega)
      have h4 : (i * S_n + u + 1) * C_n = (i * S_n + u) * C_n + C_n := by ring
      omega
    have hidx_u : ((UInt32.ofNat i * UInt32.ofNat S_n + UInt32.ofNat u) * UInt32.ofNat C_n + UInt32.ofNat y).toUSize =
        USize.ofNat ((i * S_n + u) * C_n + y) := by
      have h1 : i * S_n ≤ 10 * 15 := Nat.mul_le_mul (by omega) hS_le
      have h2 : (i * S_n + u) * C_n ≤ 165 * 201 := Nat.mul_le_mul (by omega) hC_le
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_add, UInt32.toNat_mul,
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : i < 2 ^ 32), Nat.mod_eq_of_lt (by omega : S_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : u < 2 ^ 32), Nat.mod_eq_of_lt (by omega : C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : y < 2 ^ 32), Nat.mod_eq_of_lt (by omega : i * S_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : i * S_n + u < 2 ^ 32), Nat.mod_eq_of_lt (by omega : (i * S_n + u) * C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : (i * S_n + u) * C_n + y < 2 ^ 32), usize_ofNat_toNat (by omega)]
    rw [hS_def, hidx_u]
    have htot_bd : qs.length * S_n * (W + 1) ≤ 150 * 201 := by
      have h1 : qs.length * S_n ≤ 10 * 15 := Nat.mul_le_mul (by omega) hS_le
      exact Nat.mul_le_mul h1 (by omega)
    rw [baGetI64_packI64Arr (by simp; omega)
      (by simp; exact hidx_lt), getElem!_pos _ _ (by simp; exact hidx_lt), Array.getElem_ofFn]
    dsimp only
    rw [J15.tabA_get _ _ _ _ (by rw [hlen_map]; exact hi) hu (by omega), hP_eq, hPR_eq, hlen_map, hB_eq]
  · -- hRB
    intro u hu y hy
    unfold getRB; dsimp only [ctx, bj, buildJoint]
    have hc1 : UInt32.ofNat u < UInt32.ofNat (maxLeN (kdF (qs.map Prod.fst)) (qs.map Prod.fst).length + 1) :=
      (h_u32_lt _ _ (by omega) (by rw [hS_def]; omega)).mpr (by rw [hS_def]; exact hu)
    have hc2 : UInt32.ofNat y < UInt32.ofNat (W + 1) :=
      (h_u32_lt _ _ (by omega) (by omega)).mpr (by omega)
    rw [if_pos (by simp only [hc1, hc2, decide_true, Bool.and_true])]
    have hidx_lt : u * C_n + y < S_n * C_n := by
      have h1 : (u + 1) * C_n ≤ S_n * C_n := Nat.mul_le_mul_right _ (by omega)
      have h2 : (u + 1) * C_n = u * C_n + C_n := by ring
      omega
    have hidx_u : (UInt32.ofNat u * UInt32.ofNat C_n + UInt32.ofNat y).toUSize = USize.ofNat (u * C_n + y) := by
      have h1 : u * C_n ≤ 15 * 201 := Nat.mul_le_mul (by omega) hC_le
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat',
        UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : u < 2 ^ 32), Nat.mod_eq_of_lt (by omega : C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : y < 2 ^ 32), Nat.mod_eq_of_lt (by omega : u * C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : u * C_n + y < 2 ^ 32), usize_ofNat_toNat (by omega)]
    have hSC_bd : S_n * (W + 1) ≤ 15 * 201 := Nat.mul_le_mul hS_le (by omega)
    rw [hidx_u, baGetI64_packI64Arr (by simp; change S_n * (W + 1) * 8 < 4294967296; omega)
      (by simp; exact hidx_lt), getElem!_pos _ _ (by simp; exact hidx_lt), Array.getElem_ofFn]
    dsimp only
    rw [J15.tab2_get _ _ _ (by rw [hS_def]; exact hu) (by omega), hS_def, hP_eq, hPR_eq]; rfl
  · -- hF (ringOkFast)
    intro i hi b hb r hr_256 d hd_256 hkd0 x hx1 hx2 hle hclip
    unfold ringOkFast
    by_cases hcnd : (UInt32.ofNat i < ctx.np && UInt32.ofNat b < ctx.C &&
        UInt32.ofNat r < ctx.RR && UInt32.ofNat d < ctx.C) = true
    · rw [if_pos hcnd]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      obtain ⟨⟨⟨_, _⟩, hr_u⟩, hd_u⟩ := hcnd
      have hctx_RR : ctx.RR = UInt32.ofNat RR_n := by dsimp only [ctx, bj, buildJoint, RR_n]; rw [hPR_eq]
      have hctx_C : ctx.C = UInt32.ofNat C_n := rfl
      rw [hctx_RR] at hr_u; rw [hctx_C] at hd_u
      dsimp only [ctx, bj, buildJoint]
      have hr_lt : r < RR_n := (h_u32_lt _ _ (by omega) (by omega)).mp hr_u
      have hd_lt : d < C_n := (h_u32_lt _ _ (by omega) (by omega)).mp hd_u
      have hib_lt : i * C_n + b < qs.length * C_n := by
        have h1 : (i + 1) * C_n ≤ qs.length * C_n := Nat.mul_le_mul_right _ (by omega)
        have h2 : (i + 1) * C_n = i * C_n + C_n := by ring
        omega
      have hidx_lt : ((i * C_n + b) * RR_n + r) * C_n + d < qs.length * C_n * RR_n * C_n := by
        have h1 : (i * C_n + b + 1) * RR_n ≤ qs.length * C_n * RR_n := Nat.mul_le_mul_right _ (by omega)
        have h2 : (i * C_n + b + 1) * RR_n = (i * C_n + b) * RR_n + RR_n := by ring
        have h3 : ((i * C_n + b) * RR_n + r + 1) * C_n ≤ qs.length * C_n * RR_n * C_n :=
          Nat.mul_le_mul_right _ (by omega)
        have h4 : ((i * C_n + b) * RR_n + r + 1) * C_n = ((i * C_n + b) * RR_n + r) * C_n + C_n := by ring
        omega
      have htot_bd : qs.length * C_n * RR_n * C_n < 2 ^ 29 := by
        have h1 : qs.length * C_n ≤ 10 * 201 := Nat.mul_le_mul (by omega) hC_le
        have h2 : qs.length * C_n * RR_n ≤ (10 * 201) * 201 := Nat.mul_le_mul h1 hRR_n_le
        have h3 : qs.length * C_n * RR_n * C_n ≤ (10 * 201 * 201) * 201 := Nat.mul_le_mul h2 hC_le
        omega
      have hidx_u : (((UInt32.ofNat i * UInt32.ofNat C_n + UInt32.ofNat b) * UInt32.ofNat RR_n + UInt32.ofNat r) *
          UInt32.ofNat C_n + UInt32.ofNat d).toUSize = USize.ofNat (((i * C_n + b) * RR_n + r) * C_n + d) := by
        have ha1 : i * C_n ≤ 10 * 201 := Nat.mul_le_mul (by omega) hC_le
        have ha2 : (i * C_n + b) * RR_n ≤ 2211 * 201 := Nat.mul_le_mul (by omega) hRR_n_le
        have ha3 : ((i * C_n + b) * RR_n + r) * C_n < 2 ^ 32 := by omega
        apply USize.toNat_inj.mp
        rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_add, UInt32.toNat_mul,
          UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 32), Nat.mod_eq_of_lt (by omega : C_n < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : b < 2 ^ 32), Nat.mod_eq_of_lt (by omega : RR_n < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : r < 2 ^ 32), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : i * C_n < 2 ^ 32), Nat.mod_eq_of_lt (by omega : i * C_n + b < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : (i * C_n + b) * RR_n < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : (i * C_n + b) * RR_n + r < 2 ^ 32),
          Nat.mod_eq_of_lt ha3, Nat.mod_eq_of_lt (by omega : ((i * C_n + b) * RR_n + r) * C_n + d < 2 ^ 32),
          usize_ofNat_toNat (by omega)]
      have htot_eq : (qs.map Prod.fst).length * C_n *
          (maxLeN (fun x => look2 1 C_n (tab2 1 C_n (fun _ x => PRl.getD x 0)) (fun _ x => PRl.getD x 0) 0 x) W + 1) * C_n =
          qs.length * C_n * RR_n * C_n := by rw [hlen_map, hRR_eq]
      have htot_bd' : qs.length * (W + 1) * RR_n * (W + 1) < 2 ^ 29 := htot_bd
      rw [hRR_eq, hidx_u, baGetI64_packI64Arr (by simp; omega) (by simp; exact hidx_lt),
        getElem!_pos _ _ (by simp; exact hidx_lt), Array.getElem_ofFn]
      dsimp only
      rw [J15.tabA_get _ _ _ _ (by rw [hlen_map]; exact hib_lt) hr_lt hd_lt]
      dsimp only [C_n]
      rw [S.mul_add_div' (by omega : b < W + 1), S.mul_add_mod' (by omega : b < W + 1)]
      have hlt_map : i < (qs.map Prod.fst).length := by rw [hlen_map]; exact hi
      rw [arr_map_getD _ _ (0, 0, 0) hlt_map, arr_map_getD _ _ (0, 0, 0) hlt_map, arr_map_getD _ _ (0, 0, 0) hlt_map]
      have hkd0' : ((qs.map Prod.fst).getD i (0, 0, 0)).1 = 0 := hkd0
      rw [hkd0', if_pos (show ((0 : ℕ) == 0) = true from rfl), hS_def, hP_eq, hPR_eq, hlen_map, hB_eq]
      have hB_bd : ∀ y ≤ 200, -12000000000 ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y ∧
          BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y ≤ 2000 := BfOf_bounds hnp hcaps hPR i
      have hf_bd := fG_bounds (P := capF caps) hPR_le hB_bd (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i)
        (vloF R i) b r d (by omega)
      unfold loF hiF at hf_bd
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
        exact hle
      · by_cases hcl : R.clip = true
        · right
          rw [int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl, int64_toInt_ofInt (by omega) (by omega)]
          exact hclip hcl
        · left; exact Bool.eq_false_iff.mpr hcl
    · rw [if_neg hcnd]
  · -- hcn1
    intro om hom
    dsimp only [ctx, bj, buildJoint]
    rw [h_u32_us om (by omega), baGetI64_packI64Arr (by simp; omega) (by simp; omega),
      getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    dsimp only; rw [hS_def, hP_eq, hPR_eq, hlen_map, hB_eq]
  · -- ha2p
    intro tl htl om hom
    dsimp only [ctx, bj, buildJoint]
    have hidx_lt : tl * C_n + om < S_n * C_n := by
      have h1 : (tl + 1) * C_n ≤ S_n * C_n := Nat.mul_le_mul_right _ (by omega)
      have h2 : (tl + 1) * C_n = tl * C_n + C_n := by ring
      omega
    have hidx_u : (UInt32.ofNat tl * UInt32.ofNat C_n + UInt32.ofNat om).toUSize = USize.ofNat (tl * C_n + om) := by
      have h1 : tl * C_n ≤ 15 * 201 := Nat.mul_le_mul (by omega) hC_le
      apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat',
        UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tl < 2 ^ 32), Nat.mod_eq_of_lt (by omega : C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : om < 2 ^ 32), Nat.mod_eq_of_lt (by omega : tl * C_n < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : tl * C_n + om < 2 ^ 32), usize_ofNat_toNat (by omega)]
    have hSC_bd : S_n * (W + 1) ≤ 15 * 201 := Nat.mul_le_mul hS_le (by omega)
    rw [hidx_u, baGetI64_packI64Arr (by simp; change S_n * (W + 1) * 8 < 4294967296; omega)
      (by simp; exact hidx_lt), getElem!_pos _ _ (by simp; exact hidx_lt), Array.getElem_ofFn]
    dsimp only
    rw [S.mul_add_div' (by omega : om < C_n), S.mul_add_mod' (by omega : om < C_n),
      hS_def, hP_eq, hPR_eq, hlen_map, hB_eq, hSG_eq]
  · -- hgate
    intro i r q d hi hr hq hd hG
    have hall := gateL_forall_digs gs tp i r (q + 8192 * d) hG
    rw [← hds_eq] at hall
    unfold checkGate
    by_cases hng0 : ng = 0
    · have : ctx.ng = 0 := by simp [ctx, hng0]
      rw [this]; rfl
    · have hng_ne : ¬ (ctx.ng == 0) = true := by
        simp only [ctx, beq_iff_eq]; intro h
        have := congrArg UInt32.toNat h
        rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by omega)] at this
        exact hng0 this
      rw [if_neg hng_ne]
      have hkey : UInt32.ofNat q + 8192 * UInt32.ofNat d = UInt32.ofNat (q + 8192 * d) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          show (8192 : UInt32).toNat = 8192 from rfl,
          Nat.mod_eq_of_lt (by omega : q < 2 ^ 32), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : 8192 * d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : q + 8192 * d < 2 ^ 32)]
      rw [hkey]
      have hloop : ∀ rem ≤ ng, gateLoop ctx (UInt32.ofNat i) (UInt32.ofNat r)
          (UInt32.ofNat (q + 8192 * d)) (UInt32.ofNat rem) = true := by
        intro rem; induction rem with
        | zero => intro _; rw [gateLoop, dif_neg (by decide)]
        | succ rem ih =>
          intro hrem
          have hpos : UInt32.ofNat (rem + 1) > 0 := by
            change 0 < (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
          have hsub : UInt32.ofNat (rem + 1) - 1 = UInt32.ofNat rem := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
              UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rw [gateLoop, dif_pos hpos]; dsimp only; rw [hsub]
          have hbd := hds_bd rem (by omega)
          have hgi : (baGetU8 ctx.gatePi (UInt32.ofNat rem).toUSize).toUInt32 = UInt32.ofNat (ds[rem]!.1) := by
            dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU8_ofFn _ (by omega) (by omega)]; dsimp only
            apply UInt32.toNat_inj.mp; rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hgr : (baGetU8 ctx.gateR (UInt32.ofNat rem).toUSize).toUInt32 = UInt32.ofNat (ds[rem]!.2.1) := by
            dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU8_ofFn _ (by omega) (by omega)]; dsimp only
            apply UInt32.toNat_inj.mp; rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hgi, hgr]
          by_cases hmatch : (UInt32.ofNat (ds[rem]!.1) == UInt32.ofNat i && UInt32.ofNat (ds[rem]!.2.1) == UInt32.ofNat r) = true
          · rw [if_pos hmatch]
            simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
            have hi_eq : ds[rem]!.1 = i := by
              have := congrArg UInt32.toNat hmatch.1
              rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
            have hr_eq : ds[rem]!.2.1 = r := by
              have := congrArg UInt32.toNat hmatch.2
              rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
            have hmod := hall rem (by omega) hi_eq hr_eq
            have hgm : baGetU16 ctx.gateMod (UInt32.ofNat rem).toUSize = UInt32.ofNat (ds[rem]!.2.2.1) := by
              dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; omega)
                (by rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]; dsimp only; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hbd.2.2.2.1)]
              rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
            have hgd : baGetU16 ctx.gateDig (UInt32.ofNat rem).toUSize = UInt32.ofNat (ds[rem]!.2.2.2) := by
              dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; omega)
                (by rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]; dsimp only; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hbd.2.2.2.2)]
              rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
            rw [hgm, hgd]
            have hok : ((UInt32.ofNat (q + 8192 * d) % UInt32.ofNat (ds[rem]!.2.2.1)) == UInt32.ofNat (ds[rem]!.2.2.2)) = true := by
              rw [beq_iff_eq]; apply UInt32.toNat_inj.mp
              rw [UInt32.toNat_mod, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by omega : q + 8192 * d < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ds[rem]!.2.2.1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ds[rem]!.2.2.2 < 2 ^ 32)]
              exact hmod
            rw [if_pos hok]; exact ih (by omega)
          · rw [if_neg hmatch, if_pos rfl]; exact ih (by omega)
      exact hloop ng (le_refl ng)
  · -- hearly
    intro i r q d hi hr hq hd hE
    have hall := earlyL_forall_digs gs tp i r (q + 8192 * d) hE
    rw [← hds_eq] at hall
    unfold checkEarly
    by_cases hng0 : ng = 0
    · have : ctx.ng = 0 := by simp [ctx, hng0]
      rw [this]; rfl
    · have hng_ne : ¬ (ctx.ng == 0) = true := by
        simp only [ctx, beq_iff_eq]; intro h
        have := congrArg UInt32.toNat h
        rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by omega)] at this
        exact hng0 this
      rw [if_neg hng_ne]
      have hkey : UInt32.ofNat q + 8192 * UInt32.ofNat d = UInt32.ofNat (q + 8192 * d) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          show (8192 : UInt32).toNat = 8192 from rfl,
          Nat.mod_eq_of_lt (by omega : q < 2 ^ 32), Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : 8192 * d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : q + 8192 * d < 2 ^ 32)]
      rw [hkey]
      have hloop : ∀ rem ≤ ng, earlyLoop ctx (UInt32.ofNat i) (UInt32.ofNat r)
          (UInt32.ofNat (q + 8192 * d)) (UInt32.ofNat rem) = true := by
        intro rem; induction rem with
        | zero => intro _; rw [earlyLoop, dif_neg (by decide)]
        | succ rem ih =>
          intro hrem
          have hpos : UInt32.ofNat (rem + 1) > 0 := by
            change 0 < (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
          have hsub : UInt32.ofNat (rem + 1) - 1 = UInt32.ofNat rem := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (rem + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
              UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rw [earlyLoop, dif_pos hpos]; dsimp only; rw [hsub]
          have hbd := hds_bd rem (by omega)
          have hgi : (baGetU8 ctx.gatePi (UInt32.ofNat rem).toUSize).toUInt32 = UInt32.ofNat (ds[rem]!.1) := by
            dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU8_ofFn _ (by omega) (by omega)]; dsimp only
            apply UInt32.toNat_inj.mp; rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hgr : (baGetU8 ctx.gateR (UInt32.ofNat rem).toUSize).toUInt32 = UInt32.ofNat (ds[rem]!.2.1) := by
            dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU8_ofFn _ (by omega) (by omega)]; dsimp only
            apply UInt32.toNat_inj.mp; rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hgi, hgr]
          by_cases hmatch : (UInt32.ofNat (ds[rem]!.1) == UInt32.ofNat i && decide (UInt32.ofNat r < UInt32.ofNat (ds[rem]!.2.1))) = true
          · rw [if_pos hmatch]
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatch
            have hi_eq : ds[rem]!.1 = i := by
              have := congrArg UInt32.toNat hmatch.1
              rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
            have hr_lt : r < ds[rem]!.2.1 := (h_u32_lt _ _ (by omega) (by omega)).mp hmatch.2
            have hmod := hall rem (by omega) hi_eq hr_lt
            have hgm : baGetU16 ctx.gateMod (UInt32.ofNat rem).toUSize = UInt32.ofNat (ds[rem]!.2.2.1) := by
              dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; omega)
                (by rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]; dsimp only; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hbd.2.2.2.1)]
              rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
            have hgd : baGetU16 ctx.gateDig (UInt32.ofNat rem).toUSize = UInt32.ofNat (ds[rem]!.2.2.2) := by
              dsimp only [ctx]; rw [h_u32_us rem (by omega), baGetU16_packU16Arr (by simp; omega) (by simp; omega)
                (by rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]; dsimp only; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hbd.2.2.2.2)]
              rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
            rw [hgm, hgd]
            have hok : ((UInt32.ofNat (q + 8192 * d) % UInt32.ofNat (ds[rem]!.2.2.1)) == UInt32.ofNat (ds[rem]!.2.2.2)) = true := by
              rw [beq_iff_eq]; apply UInt32.toNat_inj.mp
              rw [UInt32.toNat_mod, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by omega : q + 8192 * d < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ds[rem]!.2.2.1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ds[rem]!.2.2.2 < 2 ^ 32)]
              exact hmod
            rw [if_pos hok]; exact ih (by omega)
          · rw [if_neg hmatch, if_pos rfl]; exact ih (by omega)
      exact hloop ng (le_refl ng)

/-! ### Section 7: Completeness of `walkJFast`, `loopU32`, `go`, and `jv_of_fastJ16` -/

theorem s3Contains_true {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    {u v : List ℕ} (hu : PermW 7 u) (hv : PermW 7 v) (hw : WLink 7 3 u v) :
    s3Contains ctx (UInt32.ofNat (encB 7 u)) (UInt32.ofNat (encB 7 v)) = true := by
  obtain ⟨idx, hidx, hget⟩ := sdTab3_mem_idx hu hv hw
  have hba := hvc.hs3BA hu hidx
  rw [hget] at hba
  unfold s3Contains
  set b := (UInt32.ofNat (encB 7 u)).toUSize * 6
  set tgt := UInt32.ofNat (encB 7 v)
  change (baGetU16 ctx.s3BA b == tgt || baGetU16 ctx.s3BA (b + 1) == tgt ||
    baGetU16 ctx.s3BA (b + 2) == tgt || baGetU16 ctx.s3BA (b + 3) == tgt ||
    baGetU16 ctx.s3BA (b + 4) == tgt || baGetU16 ctx.s3BA (b + 5) == tgt) = true
  have h0 : b + USize.ofNat 0 = b := by
    apply USize.toNat_inj.mp; rw [USize.toNat_add, usize_ofNat_toNat (by omega), Nat.add_zero, Nat.mod_eq_of_lt (USize.toNat_lt_size _)]
  have h1 : USize.ofNat 1 = 1 := rfl
  have h2 : USize.ofNat 2 = 2 := rfl
  have h3 : USize.ofNat 3 = 3 := rfl
  have h4 : USize.ofNat 4 = 4 := rfl
  have h5 : USize.ofNat 5 = 5 := rfl
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0] at hba; simp [hba]
  · rw [h1] at hba; simp [hba]
  · rw [h2] at hba; simp [hba]
  · rw [h3] at hba; simp [hba]
  · rw [h4] at hba; simp [hba]
  · rw [h5] at hba; simp [hba]

theorem vOfFast_eq {t r d : ℕ} (ht : t < 16) (hr : r < 256) (hd : d < 256) :
    vOfFast (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) = Int64.ofInt (vOf 6 t r d) := by
  unfold vOfFast u32ToI64 vOf
  rw [u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega),
    int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
    show (5 : Int64) = Int64.ofInt 5 from rfl,
    int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
  rfl

theorem compOkFast_of_compOk {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    {i y : ℕ} {a v : ℤ} {eOk : Bool}
    (hi : i < qs.length) (hy : y ≤ W)
    (ha1 : -2 ^ 28 ≤ a) (ha2 : a ≤ 2 ^ 28) (hv1 : -2 ^ 28 ≤ v) (hv2 : v ≤ 2 ^ 28)
    (hok : if i + 1 = qs.length then a ≤ v
           else a - v ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y ∧ eOk = true) :
    compOkFast ctx (UInt32.ofNat i) (Int64.ofInt a) (UInt32.ofNat y) (Int64.ofInt v) eOk = true := by
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  have hi1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold compOkFast; rw [hi1, hvc.hnp]
  by_cases hlast : i + 1 = qs.length
  · rw [if_pos (by simp [hlast]), decide_eq_true_eq, int64_le_iff_toInt,
      int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
    rw [if_pos hlast] at hok; exact hok
  · have hne : ¬ (UInt32.ofNat (i + 1) == UInt32.ofNat qs.length) = true := by
      simp only [beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact hlast this
    rw [if_neg hne, hvc.hbest i (by omega) y hy, int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
    rw [if_neg hlast] at hok
    have hb := BfOf_bounds hnp hcaps hPR i y (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, hok.2⟩
    rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
    exact hok.1

theorem k3OkFast_of_k3Ok {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    {i t r d b : ℕ} {a : ℤ}
    (hi : i < qs.length) (ht : t < 16) (hr : r < 256) (hd : d < 256) (hb : b ≤ W) (hwt : d + 6 * t ≤ b)
    (ha1 : -2 ^ 28 ≤ a) (ha2 : a ≤ 2 ^ 28)
    (hkd_le : kdF (qs.map Prod.fst) i ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (ht_le : kdF (qs.map Prod.fst) i ≠ 0 → t < kdF (qs.map Prod.fst) i)
    (hok : if kdF (qs.map Prod.fst) i = 0 then
             a ≤ fG (capF caps) (fun x => PRl.getD x 0) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i)
               (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d ∧
             (R.clip = true → 0 ≤ fG (capF caps) (fun x => PRl.getD x 0) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i)
               (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)
           else
             1 ≤ vOf 6 t r d ∧
             a - vOf 6 t r d ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6
               (kdF (qs.map Prod.fst) i - 1 - t + 1, 0, 0)
               (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (b - (d + 6 * t))) :
    k3OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
      (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a)
      (UInt32.ofNat b) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) = true := by
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  set c := kdF (qs.map Prod.fst) i
  unfold k3OkFast
  by_cases hc0 : c = 0
  · rw [if_pos (by simp [hc0])]
    rw [if_pos hc0] at hok
    exact hvc.hF i hi b hb r hr d hd hc0 a (by omega) (by omega) hok.1 hok.2
  · have hcne : ¬ (UInt32.ofNat c == 0) = true := by
      simp only [beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
      rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by omega)] at this; exact hc0 this
    rw [if_neg hcne]
    rw [if_neg hc0] at hok
    have ht_lt_c := ht_le hc0
    have hsub_u : UInt32.ofNat c - 1 - UInt32.ofNat t = UInt32.ofNat (c - 1 - t) := by
      have h1 : UInt32.ofNat c - 1 = UInt32.ofNat (c - 1) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat c).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h1]; apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat t).toNat ≤ (UInt32.ofNat (c - 1)).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub_u, hvc.hg i hi (c - 1 - t) (by omega) (b - (d + 6 * t)) (by omega)]
    have hv_bd : -2 ^ 20 ≤ vOf 6 t r d ∧ vOf 6 t r d ≤ 2 ^ 20 := by unfold vOf; omega
    rw [int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
    have hB_bd := BfOf_bounds hnp hcaps hPR i
    have hg_bd := bestStep_bounds hP_le hPR_le hB_bd (c - 1 - t + 1, 0, 0) (b - (d + 6 * t)) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rw [int64_le_iff_toInt, show (1 : Int64).toInt = 1 from rfl, int64_toInt_ofInt (by omega) (by omega)]
      exact hok.1
    · rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
      exact hok.2

theorem k4OkFast_of_k4Ok {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    {i t r d b : ℕ} {a : ℤ}
    (hi : i < qs.length) (ht : t < 16) (hr : r < 256) (hd : d < 256) (hb : b ≤ W) (hwt : d + 6 * t ≤ b)
    (ha1 : -2 ^ 28 ≤ a) (ha2 : a ≤ 2 ^ 28)
    (hkd_le : kdF (qs.map Prod.fst) i ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (hok : t + 1 < kdF (qs.map Prod.fst) i ∧ 6 ≤ vOf 6 t r d ∧ 6 ≤ b - (d + 6 * t) ∧
           a - vOf 6 t r d + 5 ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6
             (kdF (qs.map Prod.fst) i - 2 - t + 1, 0, 0)
             (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (b - (d + 6 * t) - 6)) :
    k4OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
      (UInt32.ofNat t) (Int64.ofInt a) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) = true := by
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  set c := kdF (qs.map Prod.fst) i
  set y := b - (d + 6 * t)
  obtain ⟨htc, hv6, hy6, hstep⟩ := hok
  have hv_bd : -2 ^ 20 ≤ vOf 6 t r d ∧ vOf 6 t r d ≤ 2 ^ 20 := by unfold vOf; omega
  have ht1 : UInt32.ofNat t + 1 = UInt32.ofNat (t + 1) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsub_c : UInt32.ofNat c - 2 - UInt32.ofNat t = UInt32.ofNat (c - 2 - t) := by
    have h1 : UInt32.ofNat c - 2 = UInt32.ofNat (c - 2) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 2 ≤ (UInt32.ofNat c).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', show (2 : UInt32).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1]; apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat t).toNat ≤ (UInt32.ofNat (c - 2)).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
      UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsub_y : UInt32.ofNat y - 6 = UInt32.ofNat (y - 6) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by change 6 ≤ (UInt32.ofNat y).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
      UInt32.toNat_ofNat', UInt32.toNat_ofNat', show (6 : UInt32).toNat = 6 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold k4OkFast
  rw [ht1, hsub_c, hsub_y, hvc.hg i hi (c - 2 - t) (by omega) (y - 6) (by omega),
    int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
    show (5 : Int64) = Int64.ofInt 5 from rfl,
    int64_ofInt_add (by omega) (by omega) (by omega) (by omega)]
  have hB_bd := BfOf_bounds hnp hcaps hPR i
  have hg_bd := bestStep_bounds hP_le hPR_le hB_bd (c - 2 - t + 1, 0, 0) (y - 6) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · change (UInt32.ofNat (t + 1)).toNat < (UInt32.ofNat c).toNat
    rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact htc
  · rw [int64_le_iff_toInt, show (6 : Int64).toInt = 6 from rfl, int64_toInt_ofInt (by omega) (by omega)]; exact hv6
  · change (6 : UInt32).toNat ≤ (UInt32.ofNat y).toNat
    rw [UInt32.toNat_ofNat', show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega)]; exact hy6
  · rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hstep

theorem xrFast_of_xrF {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (habh : R.pa ≤ 100 ∧ R.pb ≤ 100 ∧ R.ph ≤ 100) (hrp_lt : R.rp < 256) (hoi_lt : R.oi < 256)
    (hoi_ne : R.oi + 1 < qs.length → kdF (qs.map Prod.fst) R.oi ≠ 0)
    {kind i t r d b : ℕ} {a pm pM : ℤ}
    (hkind : kind ≤ 1) (hi : i < qs.length) (ht : t < 16) (hr : r < 256) (hd : d < 256) (hb : b ≤ W)
    (hwt : d + 6 * t ≤ b)
    (ha1 : -2 ^ 27 ≤ a) (ha2 : a ≤ 2 ^ 27) (hpm1 : -2 ^ 27 ≤ pm) (hpm2 : pm ≤ 2 ^ 27)
    (hpM1 : -2 ^ 27 ≤ pM) (hpM2 : pM ≤ 2 ^ 27)
    (hkd_le : kdF (qs.map Prod.fst) i ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (ht_le : kdF (qs.map Prod.fst) i ≠ 0 → t + kind < kdF (qs.map Prod.fst) i)
    (hy_k1 : kind = 1 → 6 ≤ b - (d + 6 * t))
    (hxr : xrF R 6 qs.length (kdF (qs.map Prod.fst)) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs)
      (RBfOf 7 (capF caps) (fun x => PRl.getD x 0)) (segF (capF caps) 6 R.pa R.pb R.ph)
      kind i t r d a b pm pM = true) :
    xrFast ctx (UInt32.ofNat kind) (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
      (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b)
      (Int64.ofInt pm) (Int64.ofInt pM) = true := by
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  set c := kdF (qs.map Prod.fst) i
  set y := b - (d + 6 * t)
  set v := vOf 6 t r d
  have hv_bd : -2 ^ 20 ≤ v ∧ v ≤ 2 ^ 20 := by unfold v vOf; omega
  have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
  have hy_u : UInt32.ofNat b - UInt32.ofNat (d + 6 * t) = UInt32.ofNat y := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (d + 6 * t)).toNat ≤ (UInt32.ofNat b).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
      UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hB_bd := BfOf_bounds hnp hcaps hPR
  have hRB_bd : ∀ u y', y' ≤ 200 → -2000000000 ≤ RBfOf 7 (capF caps) (fun x => PRl.getD x 0) u y' ∧
      RBfOf 7 (capF caps) (fun x => PRl.getD x 0) u y' ≤ 200 := by
    intro u y' hy'
    have hb' := bestF_bounds hP_le hPR_le [(u + 1, 0, 0)] y' (by simp) hy'
    simpa [RBfOf] using hb'
  unfold xrF at hxr
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hxr
  obtain ⟨hP_xr, hO_xr⟩ := hxr
  unfold xrFast
  rw [vOfFast_eq ht hr hd, hwt_u]; dsimp only; rw [hy_u]
  -- Step 1: prove okPrev = true
  have hokPrev : (if (UInt32.ofNat i == ctx.rp && UInt32.ofNat c != 0) = true then
      prevOkFast ctx (UInt32.ofNat kind)
        (ctx.pa * u32ToI64 (UInt32.ofNat r) - ctx.pb * u32ToI64 (UInt32.ofNat d) - ctx.ph2 * u32ToI64 (UInt32.ofNat t))
        (Int64.ofInt pm) (Int64.ofInt pM) (UInt32.ofNat c - 1 - UInt32.ofNat t)
        (Int64.ofInt a - Int64.ofInt v) (UInt32.ofNat y) else true) = true := by
    by_cases hp : (UInt32.ofNat i == ctx.rp && UInt32.ofNat c != 0) = true
    · rw [if_pos hp]
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hvc.hrp] at hp
      have hi_rp : i = R.rp := by
        have := congrArg UInt32.toNat hp.1
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact this
      have hc_ne : c ≠ 0 := fun h0 => hp.2 (by rw [h0]; rfl)
      have hpon : prevOn R (kdF (qs.map Prod.fst)) i = true := by
        unfold prevOn; simp only [hi_rp, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
        rwa [← hi_rp]
      have hpok : prevOk (segF (capF caps) 6 R.pa R.pb R.ph) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp)
          6 R.pa R.pb R.ph kind (potF R.pa R.pb R.ph 0 t r d) pm pM (c - 1 - t) (a - v) y = true := by
        rcases hP_xr with hF | hT
        · rw [hpon] at hF; cases hF
        · rw [← hi_rp]; exact hT
      have hpa_bd : (0 : ℤ) ≤ R.pa ∧ (R.pa : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.1⟩
      have hpb_bd : (0 : ℤ) ≤ R.pb ∧ (R.pb : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.1⟩
      have hph_bd : (0 : ℤ) ≤ R.ph ∧ (R.ph : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.2⟩
      set f_i : ℤ := potF R.pa R.pb R.ph 0 t r d
      have hm_ar : (0 : ℤ) ≤ (R.pa : ℤ) * r ∧ (R.pa : ℤ) * r ≤ 25600 :=
        ⟨by positivity, Int.mul_le_mul hpa_bd.2 (by omega : (r : ℤ) ≤ 256) (by omega) (by omega)⟩
      have hm_bd : (0 : ℤ) ≤ (R.pb : ℤ) * d ∧ (R.pb : ℤ) * d ≤ 25600 :=
        ⟨by positivity, Int.mul_le_mul hpb_bd.2 (by omega : (d : ℤ) ≤ 256) (by omega) (by omega)⟩
      have hm_ht : (0 : ℤ) ≤ 2 * (R.ph : ℤ) * t ∧ 2 * (R.ph : ℤ) * t ≤ 3200 :=
        ⟨by positivity, Int.mul_le_mul (by omega : 2 * (R.ph : ℤ) ≤ 200) (by omega : (t : ℤ) ≤ 16) (by omega) (by omega)⟩
      have hf_bd : -200000 ≤ f_i ∧ f_i ≤ 200000 := by unfold f_i potF; omega
      have hf_eq : ctx.pa * u32ToI64 (UInt32.ofNat r) - ctx.pb * u32ToI64 (UInt32.ofNat d) -
          ctx.ph2 * u32ToI64 (UInt32.ofNat t) = Int64.ofInt f_i := by
        rw [hvc.hpa, hvc.hpb, hvc.hph2, u32ToI64, u32ToI64, u32ToI64,
          u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
        congr 1; unfold f_i potF; push_cast; ring
      have htl_lt : t + kind < c := ht_le hc_ne
      have htl_u : UInt32.ofNat c - 1 - UInt32.ofNat t = UInt32.ofNat (c - 1 - t) := by
        have h1 : UInt32.ofNat c - 1 = UInt32.ofNat (c - 1) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat c).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1]; apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat t).toNat ≤ (UInt32.ofNat (c - 1)).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hneed_u : Int64.ofInt a - Int64.ofInt v = Int64.ofInt (a - v) :=
        int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)
      rw [hf_eq, htl_u, hneed_u]
      have hseg_bd : ∀ tl ≤ 15, ∀ w ≤ 200, -1000000000 ≤ segF (capF caps) 6 R.pa R.pb R.ph tl w ∧
          segF (capF caps) 6 R.pa R.pb R.ph tl w ≤ 20000 := fun tl htl w hw =>
        segF_bounds hP_le habh.1 habh.2.1 habh.2.2 tl w htl hw
      unfold prevOk at hpok; unfold prevOkFast
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkind with rfl | rfl
      · -- kind = 0
        rw [if_pos rfl] at hpok; rw [if_pos (by decide)]
        have hmn_eq : (if Int64.ofInt pm < Int64.ofInt f_i then Int64.ofInt pm else Int64.ofInt f_i) =
            Int64.ofInt (min pm f_i) := by
          by_cases hlt : pm < f_i
          · rw [if_pos (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
              min_eq_left (le_of_lt hlt)]
          · rw [if_neg (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
              min_eq_right (by omega)]
        have hmx_eq : (if Int64.ofInt pM > Int64.ofInt f_i then Int64.ofInt pM else Int64.ofInt f_i) =
            Int64.ofInt (max pM f_i) := by
          by_cases hgt : f_i < pM
          · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_left (le_of_lt hgt)]
          · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_right (by omega)]
        dsimp only; rw [hmn_eq, hmx_eq]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hpok
        by_cases h0 : 0 ≤ min pm f_i
        · rw [if_pos (by rw [int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl, int64_toInt_ofInt (by omega) (by omega)]; exact h0)]
        · rw [if_neg (by rw [int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl, int64_toInt_ofInt (by omega) (by omega)]; exact h0)]
          have hcn1_bd := cn1F_zero_bounds (hB_bd R.rp) habh.1 habh.2.1 y (by omega)
          have ha2p_bd := a2pF_zero_bounds hseg_bd (hB_bd R.rp) habh.1 habh.2.1 (c - 1 - t) y (by omega) (by omega)
          have hmul_bd : -2 ^ 40 ≤ (R.pa : ℤ) * (a - v) ∧ (R.pa : ℤ) * (a - v) ≤ 2 ^ 40 := by
            have h1 : (R.pa : ℤ) * (a - v) ≤ 100 * (2 ^ 27 + 2 ^ 20) := by
              by_cases hs : 0 ≤ a - v
              · exact Int.mul_le_mul hpa_bd.2 (by omega) hs (by omega)
              · have : (R.pa : ℤ) * (a - v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpa_bd.1 (by omega); omega
            have h2 : -(100 * (2 ^ 27 + 2 ^ 20)) ≤ (R.pa : ℤ) * (a - v) := by
              by_cases hs : 0 ≤ a - v
              · have : 0 ≤ (R.pa : ℤ) * (a - v) := mul_nonneg hpa_bd.1 hs; omega
              · have : (R.pa : ℤ) * (-(a - v)) ≤ 100 * (2 ^ 27 + 2 ^ 20) :=
                  Int.mul_le_mul hpa_bd.2 (by omega) (by omega) (by omega)
                linarith
            omega
          rw [hvc.hpa, hvc.hcn1 y (by omega),
            int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
          rcases hpok with (h1 | h2) | h3
          · exact absurd h1 h0
          · have h2' := cn1F_add_le _ R.pa R.pb (a - v) (max pM f_i + min pm f_i - f_i) y (by omega) h2
            rw [if_pos (by rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact h2')]
          · by_cases hc1 : Int64.ofInt ((R.pa : ℤ) * (a - v) + cn1F (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp) R.pa R.pb 0 y) ≤
                Int64.ofInt (max pM f_i + min pm f_i - f_i)
            · rw [if_pos hc1]
            · rw [if_neg hc1, hvc.ha2p (c - 1 - t) (by omega) y (by omega),
                int64_ofInt_add (by omega) (by omega) (by omega) (by omega)]
              have h3' := a2pF_add_le _ _ R.pa R.pb (c - 1 - t) (a - v) (min pm f_i) y (by omega) h3
              rw [decide_eq_true_eq, int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
              exact h3'
      · -- kind = 1
        rw [if_neg (by decide)] at hpok; rw [if_neg (by decide)]
        have hy6 := hy_k1 rfl
        have hfp_eq : Int64.ofInt f_i - ctx.ph = Int64.ofInt (f_i - R.ph) := by
          rw [hvc.hph, int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
        have hmn_eq : (if Int64.ofInt pm < Int64.ofInt (f_i - R.ph) then Int64.ofInt pm else Int64.ofInt (f_i - R.ph)) =
            Int64.ofInt (min pm (f_i - R.ph)) := by
          by_cases hlt : pm < f_i - R.ph
          · rw [if_pos (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
              min_eq_left (le_of_lt hlt)]
          · rw [if_neg (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
              min_eq_right (by omega)]
        have hmx_eq : (if Int64.ofInt pM > Int64.ofInt (f_i - R.ph) then Int64.ofInt pM else Int64.ofInt (f_i - R.ph)) =
            Int64.ofInt (max pM (f_i - R.ph)) := by
          by_cases hgt : f_i - R.ph < pM
          · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_left (le_of_lt hgt)]
          · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_right (by omega)]
        dsimp only; rw [hfp_eq, hmn_eq, hmx_eq]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hpok
        by_cases h0 : 0 ≤ min pm (f_i - R.ph)
        · rw [if_pos (by rw [int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl, int64_toInt_ofInt (by omega) (by omega)]; exact h0)]
        · rw [if_neg (by rw [int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl, int64_toInt_ofInt (by omega) (by omega)]; exact h0)]
          have hy6_u : UInt32.ofNat y - 6 = UInt32.ofNat (y - 6) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_sub_of_le _ _ (by change 6 ≤ (UInt32.ofNat y).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
              UInt32.toNat_ofNat', UInt32.toNat_ofNat', show (6 : UInt32).toNat = 6 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have htl1_u : UInt32.ofNat (c - 1 - t) - 1 = UInt32.ofNat (c - 1 - t - 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (c - 1 - t)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
              UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hneed'_u : Int64.ofInt (a - v) + 5 = Int64.ofInt (a - v + 5) := by
            rw [show (5 : Int64) = Int64.ofInt 5 from rfl]
            exact int64_ofInt_add (by omega) (by omega) (by omega) (by omega)
          have hcn1_bd := cn1F_zero_bounds (hB_bd R.rp) habh.1 habh.2.1 (y - 6) (by omega)
          have ha2p_bd := a2pF_zero_bounds hseg_bd (hB_bd R.rp) habh.1 habh.2.1 (c - 1 - t - 1) (y - 6) (by omega) (by omega)
          have hmul_bd : -2 ^ 40 ≤ (R.pa : ℤ) * (a - v + 5) ∧ (R.pa : ℤ) * (a - v + 5) ≤ 2 ^ 40 := by
            have h1 : (R.pa : ℤ) * (a - v + 5) ≤ 100 * (2 ^ 27 + 2 ^ 20 + 5) := by
              by_cases hs : 0 ≤ a - v + 5
              · exact Int.mul_le_mul hpa_bd.2 (by omega) hs (by omega)
              · have : (R.pa : ℤ) * (a - v + 5) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpa_bd.1 (by omega); omega
            have h2 : -(100 * (2 ^ 27 + 2 ^ 20 + 5)) ≤ (R.pa : ℤ) * (a - v + 5) := by
              by_cases hs : 0 ≤ a - v + 5
              · have : 0 ≤ (R.pa : ℤ) * (a - v + 5) := mul_nonneg hpa_bd.1 hs; omega
              · have : (R.pa : ℤ) * (-(a - v + 5)) ≤ 100 * (2 ^ 27 + 2 ^ 20 + 5) :=
                  Int.mul_le_mul hpa_bd.2 (by omega) (by omega) (by omega)
                linarith
            omega
          rw [hneed'_u, hy6_u, hvc.hpa, hvc.hph2, hvc.hcn1 (y - 6) (by omega),
            int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
          rcases hpok with (h1 | h2) | h3
          · exact absurd h1 h0
          · have h2_le : cn1F (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp) R.pa R.pb (a - v + 5) (y - 6) ≤
                max pM (f_i - R.ph) + min pm (f_i - R.ph) - f_i + 2 * (R.ph : ℤ) := by
              have : (((6 - 1 : ℕ) : ℤ)) = 5 := rfl; rw [this] at h2; omega
            have h2' := cn1F_add_le _ R.pa R.pb (a - v + 5) _ (y - 6) (by omega) h2_le
            rw [if_pos (by rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; omega)]
          · by_cases hc1 : Int64.ofInt ((R.pa : ℤ) * (a - v + 5) +
                cn1F (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs R.rp) R.pa R.pb 0 (y - 6) - 2 * R.ph) ≤
                Int64.ofInt (max pM (f_i - R.ph) + min pm (f_i - R.ph) - f_i)
            · rw [if_pos hc1]
            · rw [if_neg hc1, htl1_u, hvc.ha2p (c - 1 - t - 1) (by omega) (y - 6) (by omega),
                int64_ofInt_add (by omega) (by omega) (by omega) (by omega)]
              have h3' := a2pF_add_le _ _ R.pa R.pb (c - 1 - t - 1) (a - v + 5) (min pm (f_i - R.ph)) (y - 6) (by omega)
                (by have : (((6 - 1 : ℕ) : ℤ)) = 5 := rfl; rw [this] at h3; exact h3)
              rw [decide_eq_true_eq, int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
              exact h3'
    · rw [if_neg hp]
  rw [hokPrev, Bool.not_true, if_neg (by decide)]
  -- Step 2: prove ORD branch
  by_cases ho : (UInt32.ofNat i == ctx.oi && decide (UInt32.ofNat i + 1 < ctx.np)) = true
  · rw [if_pos ho]
    have hi1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hvc.hoi, hvc.hnp, hi1] at ho
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
    have hi_oi : i = R.oi := by
      have := congrArg UInt32.toNat ho.1
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this
    have hi1_lt : i + 1 < qs.length := by
      have : (UInt32.ofNat (i + 1)).toNat < (UInt32.ofNat qs.length).toNat := ho.2
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this
    have hoon : ordOn R qs.length i = true := by unfold ordOn; rw [hi_oi] at hi1_lt; simp [hi_oi, hi1_lt]
    have hO : (if kind = 0 then decide (a ≤ 2 * (v + RBfOf 7 (capF caps) (fun x => PRl.getD x 0) (c - 1 - t) y) +
          BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs (i + 1) b)
        else decide (a ≤ 2 * (v - ((6 - 1 : ℕ) : ℤ) + RBfOf 7 (capF caps) (fun x => PRl.getD x 0) (c - 2 - t) (y - 6)) +
          BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs (i + 1) b)) = true := by
      rcases hO_xr with hF | hT
      · rw [hoon] at hF; cases hF
      · exact hT
    rw [hi1, hvc.hbest (i + 1) (by omega) b hb]
    have hB1_bd := hB_bd (i + 1) b (by omega)
    have hc_ne : c ≠ 0 := by rw [← hi_oi] at hoi_ne; exact hoi_ne hi1_lt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkind with rfl | rfl
    · rw [if_pos rfl] at hO; rw [if_pos (by decide)]
      rw [decide_eq_true_eq] at hO
      have htl_lt := ht_le hc_ne
      have hsub_u : UInt32.ofNat c - 1 - UInt32.ofNat t = UInt32.ofNat (c - 1 - t) := by
        have h1 : UInt32.ofNat c - 1 = UInt32.ofNat (c - 1) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat c).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1]; apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat t).toNat ≤ (UInt32.ofNat (c - 1)).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hrb_bd := hRB_bd (c - 1 - t) y (by omega)
      rw [hsub_u, hvc.hRB (c - 1 - t) (by omega) y (by omega),
        int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
        show (2 : Int64) = Int64.ofInt 2 from rfl,
        int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
        decide_eq_true_eq, int64_le_iff_toInt,
        int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
      exact hO
    · rw [if_neg (by decide)] at hO; rw [if_neg (by decide)]
      rw [decide_eq_true_eq] at hO
      have htl_lt := ht_le hc_ne
      have hy6 := hy_k1 rfl
      have hsub_c : UInt32.ofNat c - 2 - UInt32.ofNat t = UInt32.ofNat (c - 2 - t) := by
        have h1 : UInt32.ofNat c - 2 = UInt32.ofNat (c - 2) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 2 ≤ (UInt32.ofNat c).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', show (2 : UInt32).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h1]; apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat t).toNat ≤ (UInt32.ofNat (c - 2)).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hsub_y : UInt32.ofNat y - 6 = UInt32.ofNat (y - 6) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change 6 ≤ (UInt32.ofNat y).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', show (6 : UInt32).toNat = 6 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hrb_bd := hRB_bd (c - 2 - t) (y - 6) (by omega)
      rw [hsub_c, hsub_y, hvc.hRB (c - 2 - t) (by omega) (y - 6) (by omega),
        show (5 : Int64) = Int64.ofInt 5 from rfl,
        int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
        int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
        show (2 : Int64) = Int64.ofInt 2 from rfl,
        int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
        decide_eq_true_eq, int64_le_iff_toInt,
        int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
      exact hO
  · rw [if_neg ho]

theorem xcFast_of_xcF {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (habh : R.pa ≤ 100 ∧ R.pb ≤ 100 ∧ R.ph ≤ 100) (hrp_lt : R.rp < 256) (hoi_lt : R.oi < 256)
    (hvlo_bd : ∀ i < qs.length, -2 ^ 27 ≤ vloF R i ∧ vloF R i ≤ 2 ^ 27)
    (hvhi_bd : ∀ i < qs.length, -2 ^ 27 ≤ vhiF R i ∧ vhiF R i ≤ 2 ^ 27)
    {i t r d b : ℕ} {a pm pM : ℤ}
    (hi : i < qs.length) (ht : t < 16) (hr : r < 256) (hd : d < 256) (hb : b ≤ W) (hwt : d + 6 * t ≤ b)
    (ha1 : -2 ^ 27 ≤ a) (ha2 : a ≤ 2 ^ 27) (hpm1 : -2 ^ 27 ≤ pm) (hpm2 : pm ≤ 2 ^ 27)
    (hpM1 : -2 ^ 27 ≤ pM) (hpM2 : pM ≤ 2 ^ 27)
    (hkd_le : kdF (qs.map Prod.fst) i ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (hxc : xcF R 6 qs.length (kdF (qs.map Prod.fst)) (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs)
      i t r d a b pm pM = true) :
    xcFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
      (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b)
      (Int64.ofInt pm) (Int64.ofInt pM) = true := by
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  set c := kdF (qs.map Prod.fst) i
  unfold xcF at hxc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hxc
  obtain ⟨⟨hR_xc, hP_xc⟩, hO_xc⟩ := hxc
  unfold xcFast
  have hokRing : (if (UInt32.ofNat c == 0) = true then
      getVlo ctx (UInt32.ofNat i) ≤ u32ToI64 (UInt32.ofNat r) - u32ToI64 (UInt32.ofNat d) &&
      u32ToI64 (UInt32.ofNat r) - u32ToI64 (UInt32.ofNat d) ≤ getVhi ctx (UInt32.ofNat i) else true) = true := by
    by_cases hc0 : (UInt32.ofNat c == 0) = true
    · rw [if_pos hc0]
      have hc0n : c = 0 := by
        have := congrArg UInt32.toNat (beq_iff_eq.mp hc0)
        rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by omega)] at this; exact this
      rcases hR_xc with hne | hR_xc
      · simp [c, hc0n] at hne
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hR_xc ⊢
      rw [hvc.hvlo i hi, hvc.hvhi i hi, u32ToI64, u32ToI64, u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega),
        int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
      have h1 := hvlo_bd i hi; have h2 := hvhi_bd i hi
      refine ⟨?_, ?_⟩
      · rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
        exact hR_xc.1
      · rw [int64_le_iff_toInt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
        exact hR_xc.2
    · rw [if_neg hc0]
  rw [hokRing]; dsimp only; rw [Bool.not_true, if_neg (by decide)]
  have hokPrev : (if (UInt32.ofNat i == ctx.rp && UInt32.ofNat c != 0) = true then
      let f := ctx.pa * u32ToI64 (UInt32.ofNat r) - ctx.pb * u32ToI64 (UInt32.ofNat d) - ctx.ph2 * u32ToI64 (UInt32.ofNat t)
      let mn := if Int64.ofInt pm < f then Int64.ofInt pm else f
      let mx := if Int64.ofInt pM > f then Int64.ofInt pM else f
      (0 : Int64) ≤ mn + mx - f else true = true) := by
    by_cases hp : (UInt32.ofNat i == ctx.rp && UInt32.ofNat c != 0) = true
    · rw [if_pos hp]
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hvc.hrp] at hp
      have hi_rp : i = R.rp := by
        have := congrArg UInt32.toNat hp.1
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
      have hc_ne : c ≠ 0 := fun h0 => hp.2 (by rw [h0]; rfl)
      have hpon : prevOn R (kdF (qs.map Prod.fst)) i = true := by
        unfold prevOn; simp only [hi_rp, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
        rwa [← hi_rp]
      have hpend : prevEnd (potF R.pa R.pb R.ph 0 t r d) pm pM = true := by
        rcases hP_xc with hF | hT
        · rw [hpon] at hF; cases hF
        · exact hT
      unfold prevEnd at hpend; rw [decide_eq_true_eq] at hpend
      set f_i : ℤ := potF R.pa R.pb R.ph 0 t r d
      have hpa_bd : (0 : ℤ) ≤ R.pa ∧ (R.pa : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.1⟩
      have hpb_bd : (0 : ℤ) ≤ R.pb ∧ (R.pb : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.1⟩
      have hph_bd : (0 : ℤ) ≤ R.ph ∧ (R.ph : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.2⟩
      have hm_ar : (0 : ℤ) ≤ (R.pa : ℤ) * r ∧ (R.pa : ℤ) * r ≤ 25600 :=
        ⟨by positivity, Int.mul_le_mul hpa_bd.2 (by omega : (r : ℤ) ≤ 256) (by omega) (by omega)⟩
      have hm_bd : (0 : ℤ) ≤ (R.pb : ℤ) * d ∧ (R.pb : ℤ) * d ≤ 25600 :=
        ⟨by positivity, Int.mul_le_mul hpb_bd.2 (by omega : (d : ℤ) ≤ 256) (by omega) (by omega)⟩
      have hm_ht : (0 : ℤ) ≤ 2 * (R.ph : ℤ) * t ∧ 2 * (R.ph : ℤ) * t ≤ 3200 :=
        ⟨by positivity, Int.mul_le_mul (by omega : 2 * (R.ph : ℤ) ≤ 200) (by omega : (t : ℤ) ≤ 16) (by omega) (by omega)⟩
      have hf_bd : -200000 ≤ f_i ∧ f_i ≤ 200000 := by unfold f_i potF; omega
      have hf_eq : ctx.pa * u32ToI64 (UInt32.ofNat r) - ctx.pb * u32ToI64 (UInt32.ofNat d) -
          ctx.ph2 * u32ToI64 (UInt32.ofNat t) = Int64.ofInt f_i := by
        rw [hvc.hpa, hvc.hpb, hvc.hph2, u32ToI64, u32ToI64, u32ToI64,
          u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
          int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
        congr 1; unfold f_i potF; push_cast; ring
      have hmn_eq : (if Int64.ofInt pm < Int64.ofInt f_i then Int64.ofInt pm else Int64.ofInt f_i) =
          Int64.ofInt (min pm f_i) := by
        by_cases hlt : pm < f_i
        · rw [if_pos (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
            min_eq_left (le_of_lt hlt)]
        · rw [if_neg (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
            min_eq_right (by omega)]
      have hmx_eq : (if Int64.ofInt pM > Int64.ofInt f_i then Int64.ofInt pM else Int64.ofInt f_i) =
          Int64.ofInt (max pM f_i) := by
        by_cases hgt : f_i < pM
        · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
            max_eq_left (le_of_lt hgt)]
        · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
            max_eq_right (by omega)]
      dsimp only; rw [hf_eq, hmn_eq, hmx_eq,
        int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
        int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
        int64_le_iff_toInt, show (0 : Int64).toInt = 0 from rfl,
        int64_toInt_ofInt (by omega) (by omega)]
      exact hpend
    · rw [if_neg hp]
  have hokPrev_d := decide_eq_true hokPrev
  rw [hokPrev_d, Bool.not_true, if_neg (by decide)]
  by_cases ho : (UInt32.ofNat i == ctx.oi && decide (UInt32.ofNat i + 1 < ctx.np)) = true
  · rw [if_pos ho]
    have hi1 : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hvc.hoi, hvc.hnp, hi1] at ho
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
    have hi_oi : i = R.oi := by
      have := congrArg UInt32.toNat ho.1
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hi1_lt : i + 1 < qs.length := by
      have : (UInt32.ofNat (i + 1)).toNat < (UInt32.ofNat qs.length).toNat := ho.2
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hoon : ordOn R qs.length i = true := by
      unfold ordOn; rw [hi_oi] at hi1_lt; simp [hi_oi, hi1_lt]
    have hO : a ≤ 2 * vOf 6 t r d + BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs (i + 1) (b - (d + 6 * t)) := by
      rcases hO_xc with hF | hT
      · rw [hoon] at hF; cases hF
      · exact decide_eq_true_eq.mp hT
    have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
    have hy_u : UInt32.ofNat b - UInt32.ofNat (d + 6 * t) = UInt32.ofNat (b - (d + 6 * t)) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (d + 6 * t)).toNat ≤ (UInt32.ofNat b).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hB_bd := BfOf_bounds hnp hcaps hPR (i + 1) (b - (d + 6 * t)) (by omega)
    have hv_bd : -2 ^ 20 ≤ vOf 6 t r d ∧ vOf 6 t r d ≤ 2 ^ 20 := by unfold vOf; omega
    rw [vOfFast_eq ht hr hd, hwt_u, hy_u, hi1, hvc.hbest (i + 1) (by omega) (b - (d + 6 * t)) (by omega),
      show (2 : Int64) = Int64.ofInt 2 from rfl,
      int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      int64_ofInt_add (by omega) (by omega) (by omega) (by omega),
      decide_eq_true_eq, int64_le_iff_toInt,
      int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
    exact hO
  · rw [if_neg ho]

/-! ### `walkJFast_complete` and `loopU32_complete` -/

theorem walkJFast_complete {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hbm_lt : bm < 16)
    (visit : UInt32 → UInt32 → UInt32 → ByteArray → ByteArray)
    (hvid : ∀ n e du M, M.size < 2 ^ 32 → Id1 (visit n e du M) M)
    (pm : UInt8) (p : ℕ) (hpm : pm.toNat ≤ p) :
    ∀ (R' : List (List ℕ)) (rem : ℕ) (mk : UInt32) (du : ℕ) (v : List ℕ) (M : ByteArray)
      (usedA usedC later : List (List ℕ)),
      rem < 2 ^ 32 → R'.length < rem → ((mk.toNat >>> R'.length) % 2 = 1) →
      du < 16 → (∀ w ∈ v :: R', PermW 7 w) → List.IsChain (DoorEq 7) (v :: R') →
      M.size = (permCodes 7 7).length →
      PS.MInv (encB 7) (fun i => (ciTab 7 (permCodes 7 7))[i]!) M usedA →
      MC (encB 7) (fun i => (ciTab 7 (permCodes 7 7))[i]!) M pm usedC →
      MB M p →
      (∀ u ∈ usedA, PermW 7 u) → (∀ u ∈ usedC, PermW 7 u) →
      (∀ u ∈ usedC, ∀ w ∈ v :: R', ¬ u ~r w) →
      List.Pairwise (fun a b => ¬ a ~r b) (v :: R') →
      Bud bm du usedA ((v :: R') ++ later) →
      (∀ M' du', M'.size = (permCodes 7 7).length → du' ≤ bm →
        PS.MInv (encB 7) (fun i => (ciTab 7 (permCodes 7 7))[i]!) M' (usedA ++ v :: R') →
        MC (encB 7) (fun i => (ciTab 7 (permCodes 7 7))[i]!) M' pm (usedC ++ v :: R') →
        MB M' p → Bud bm du' (usedA ++ v :: R') later →
        (visit (UInt32.ofNat (rem - 1 - R'.length))
          (UInt32.ofNat (encB 7 ((v :: R').getLast (List.cons_ne_nil v R'))))
          (UInt32.ofNat du') M').size = 0) →
      (walkJFast ctx visit pm (UInt32.ofNat rem) mk (UInt32.ofNat du) (UInt32.ofNat (encB 7 v)) M).size = 0 := by
  have hsz_le := permCodes7_length_le
  have hEnc := PS.encB_enc 7 (by omega) (by omega)
  intro R'
  induction R' with
  | nil =>
    intro rem mk du v M usedA usedC later hrem hlen hbit hdu hperm _ hMsz hM hC hB husedA husedC hnew _ hbud hfin
    have hv := hperm v List.mem_cons_self
    have hpos : UInt32.ofNat rem > 0 := by
      change 0 < (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega
    have hsub1 : UInt32.ofNat rem - 1 = UInt32.ofNat (rem - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt hrem, Nat.mod_eq_of_lt (by omega)]
    have hbit0 : mk.toNat % 2 = 1 := by simpa using hbit
    have hmk_ne : ¬ (mk == 0) = true := by
      simp only [beq_iff_eq]; intro h; rw [h] at hbit0; simp at hbit0
    have hmk1 : ((mk &&& 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h
      have := congrArg UInt32.toNat h
      rw [UInt32.toNat_and, UInt32.toNat_one, UInt32.toNat_zero, Nat.and_one_is_mod] at this; omega
    obtain ⟨b1, b2, b3⟩ := J15.block_ok hEnc hv hM hC (fun u hu => hu) husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hci_lt : (ciTab 7 (permCodes 7 7))[encB 7 v]! < (permCodes 7 7).length := ciTab_lt (encB_lt hv)
    have hc_eq : (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize =
        USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!) := by
      rw [hvc.hciBA hv]; apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
    have ho_eq : baGetU8 M (USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!)) =
        M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) := by
      rw [baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hMsz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    have hbm_u : (UInt32.ofNat bm ≤ UInt32.ofNat du) ↔ bm ≤ du := by
      change (UInt32.ofNat bm).toNat ≤ (UInt32.ofNat du).toNat ↔ bm ≤ du
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hb2' : ¬ (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0 && decide (ctx.bm ≤ UInt32.ofNat du)) = true := by
      rw [hvc.hbm]; intro h; apply b2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, hbm_u.mp h.2⟩
    set du' := if (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0) = true then du + 1 else du
    have hdu'_u : (if (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0) = true then UInt32.ofNat du + 1 else UInt32.ofNat du) =
        UInt32.ofNat du' := by
      dsimp only [du']; split_ifs
      · apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      · rfl
    have hdu'_le : du' ≤ bm := by
      dsimp only [du']; split_ifs with h0
      · have hlt : ¬ bm ≤ du := fun hle => b2 (by simp [h0, hle])
        omega
      · exact by
          have : du ≤ bm := by
            unfold Bud at hbud; have h1 := J15.clsCount_append_le usedA ((v :: []) ++ later); omega
          exact this
    have hM0_eq : baSetU8 M (USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!)) pm =
        M.set! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) pm := by
      rw [baSetU8_eq_set! (by omega) (by rw [usize_ofNat_toNat (by omega), hMsz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    rw [walkJFast, dif_pos hpos]; dsimp only
    rw [if_neg hmk_ne, hc_eq, ho_eq, if_neg b1, if_neg hb2', hdu'_u, hsub1, hM0_eq, if_pos hmk1]
    have hres := hfin _ du' (by rw [ByteArray.size_set!]; exact hMsz) hdu'_le
      (J15.minv_setv hM v pm) (J15.mc_set hC v) (J15.mb_set hB _ hpm) b3
    simp only [List.length_nil, Nat.sub_zero, List.getLast_singleton] at hres
    rw [if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hres)]
    exact hres
  | cons v' R'' ih =>
    intro rem mk du v M usedA usedC later hrem hlen hbit hdu hperm hdoor hMsz hM hC hB husedA husedC hnew hpw hbud hfin
    have hv := hperm v List.mem_cons_self
    have hpos : UInt32.ofNat rem > 0 := by
      change 0 < (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega
    have hsub1 : UInt32.ofNat rem - 1 = UInt32.ofNat (rem - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat rem).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hrem]; omega),
        UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt hrem, Nat.mod_eq_of_lt (by omega)]
    have hmk_ne : ¬ (mk == 0) = true := by
      simp only [beq_iff_eq]; intro h; rw [h] at hbit; simp at hbit
    have hbit' : ((mk >>> 1).toNat >>> R''.length) % 2 = 1 := by
      have h1 : (mk >>> 1).toNat = mk.toNat / 2 := by
        rw [UInt32.toNat_shiftRight, show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftRight_eq_div_pow]
      rw [h1, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      rw [List.length_cons, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm] at hbit
      exact hbit
    have hmk'_ne : ((mk >>> 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h; rw [h] at hbit'; simp at hbit'
    obtain ⟨b1, b2, b3⟩ := J15.block_ok hEnc hv hM hC (fun u hu => hu) husedA husedC
      (fun u hu => hnew u hu v List.mem_cons_self) hbud
    have hci_lt : (ciTab 7 (permCodes 7 7))[encB 7 v]! < (permCodes 7 7).length := ciTab_lt (encB_lt hv)
    have hc_eq : (baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize).toUSize =
        USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!) := by
      rw [hvc.hciBA hv]; apply USize.toNat_inj.mp
      rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
    have ho_eq : baGetU8 M (USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!)) =
        M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) := by
      rw [baGetU8_eq_get! (by omega) (by rw [usize_ofNat_toNat (by omega), hMsz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    have hbm_u : (UInt32.ofNat bm ≤ UInt32.ofNat du) ↔ bm ≤ du := by
      change (UInt32.ofNat bm).toNat ≤ (UInt32.ofNat du).toNat ↔ bm ≤ du
      rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hb2' : ¬ (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0 && decide (ctx.bm ≤ UInt32.ofNat du)) = true := by
      rw [hvc.hbm]; intro h; apply b2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, hbm_u.mp h.2⟩
    set du' := if (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0) = true then du + 1 else du
    have hdu'_lt : du' < 16 := by
      dsimp only [du']; split_ifs with h0
      · have hlt : ¬ bm ≤ du := fun hle => b2 (by simp [h0, hle]); omega
      · exact hdu
    have hdu'_u : (if (M.get! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) != 0) = true then UInt32.ofNat du + 1 else UInt32.ofNat du) =
        UInt32.ofNat du' := by
      dsimp only [du']; split_ifs
      · apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      · rfl
    have hM0_eq : baSetU8 M (USize.ofNat ((ciTab 7 (permCodes 7 7))[encB 7 v]!)) pm =
        M.set! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) pm := by
      rw [baSetU8_eq_set! (by omega) (by rw [usize_ofNat_toNat (by omega), hMsz]; exact hci_lt),
        usize_ofNat_toNat (by omega)]
    rw [walkJFast, dif_pos hpos]; dsimp only
    rw [if_neg hmk_ne, hc_eq, ho_eq, if_neg b1, if_neg hb2', hdu'_u, hsub1, hM0_eq]
    set M0 := M.set! ((ciTab 7 (permCodes 7 7))[encB 7 v]!) pm
    have hM0_sz : M0.size = (permCodes 7 7).length := by rw [ByteArray.size_set!]; exact hMsz
    have hM1_id : Id1 (if ((mk &&& 1) != 0) = true then visit (UInt32.ofNat (rem - 1)) (UInt32.ofNat (encB 7 v)) (UInt32.ofNat du') M0 else M0) M0 := by
      split_ifs
      · exact hvid _ _ _ M0 (by omega)
      · exact Or.inr rfl
    generalize (if ((mk &&& 1) != 0) = true then visit (UInt32.ofNat (rem - 1)) (UInt32.ofNat (encB 7 v)) (UInt32.ofNat du') M0 else M0) = M1 at hM1_id
    by_cases hz1 : (M1.usize == 0) = true
    · rw [if_pos hz1]
      have hM1_lt : M1.size < 2 ^ 32 := by
        rcases hM1_id with h | h
        · omega
        · rw [h]; omega
      exact (ba_usize_eq_zero_iff hM1_lt).mp hz1
    · rw [if_neg hz1]
      have hM1_eq : M1 = M0 := by
        rcases hM1_id with h | h
        · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz1
        · exact h
      subst hM1_eq
      rw [if_pos hmk'_ne]
      obtain ⟨hdc, hdtl⟩ := List.isChain_cons_cons.mp hdoor
      obtain ⟨hpc, hptl⟩ := List.pairwise_cons.mp hpw
      have hnxt_eq : baGetU16 ctx.nxtBA (UInt32.ofNat (encB 7 v)).toUSize = UInt32.ofNat (encB 7 v') := by
        rw [hvc.hnxtBA hv, hEnc.nxt_eq v v' hv hdc]
      rw [hnxt_eq]
      have hrec := ih (rem - 1) (mk >>> 1) du' v' M0 (usedA ++ [v]) (usedC ++ [v]) later
        (by omega) (by simp only [List.length_cons] at hlen; omega) hbit' hdu'_lt
        (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdtl hM0_sz
        (J15.minv_setv hM v pm) (J15.mc_set hC v) (J15.mb_set hB _ hpm)
        (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedA u h; rw [List.mem_singleton.mp h]; exact hv)
        (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedC u h; rw [List.mem_singleton.mp h]; exact hv)
        (fun u hu w hw => by
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]; exact hpc w hw)
        hptl b3 (fun M' du'' hM'sz hdu'' hM' hC' hB' hbud' => by
          have heq_a : usedA ++ [v] ++ v' :: R'' = usedA ++ v :: v' :: R'' := by simp
          have heq_c : usedC ++ [v] ++ v' :: R'' = usedC ++ v :: v' :: R'' := by simp
          rw [heq_a] at hM' hbud'; rw [heq_c] at hC'
          have hf := hfin M' du'' hM'sz hdu'' hM' hC' hB' hbud'
          rw [List.getLast_cons (List.cons_ne_nil v' R'')] at hf
          have heq_r : rem - 1 - 1 - R''.length = rem - 1 - (v' :: R'').length := by simp; omega
          rwa [heq_r])
      rw [if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hrec)]
      exact hrec

theorem loopU32_complete (lim : ℕ) (hlim : lim < 2 ^ 32) (step : UInt32 → ByteArray → ByteArray)
    (hsid : ∀ j M, M.size < 2 ^ 32 → Id1 (step j M) M)
    (target : ℕ) (htarget : target < lim) (M : ByteArray) (hM : M.size < 2 ^ 32)
    (hzero : (step (UInt32.ofNat target) M).size = 0) :
    (loopU32 (UInt32.ofNat lim) 0 step M).size = 0 := by
  have haux : ∀ (rem : ℕ) (idx : ℕ), lim - idx = rem → idx ≤ target →
      (loopU32 (UInt32.ofNat lim) (UInt32.ofNat idx) step M).size = 0 := by
    intro rem
    induction rem with
    | zero => intro idx hrem hle; omega
    | succ rem ih =>
      intro idx hrem hle
      have hlt : UInt32.ofNat idx < UInt32.ofNat lim := by
        change (UInt32.ofNat idx).toNat < (UInt32.ofNat lim).toNat
        rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlim]; omega
      rw [loopU32, dif_pos hlt]; dsimp only
      by_cases heq : idx = target
      · subst heq
        rw [if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hzero)]; exact hzero
      · have hs := hsid (UInt32.ofNat idx) M hM
        generalize step (UInt32.ofNat idx) M = M' at hs
        by_cases hz : (M'.usize == 0) = true
        · rw [if_pos hz]
          have hM'_lt : M'.size < 2 ^ 32 := by
            rcases hs with h | h
            · omega
            · rw [h]; exact hM
          exact (ba_usize_eq_zero_iff hM'_lt).mp hz
        · rw [if_neg hz]
          rcases hs with h | h
          · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz
          · rw [h]
            have hadd : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
              apply UInt32.toNat_inj.mp
              rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            rw [hadd]; exact ih (idx + 1) (by omega) (by omega)
  exact haux lim 0 (Nat.sub_zero lim) (Nat.zero_le target)

/-! ### `computeMask` Bit Lemma -/

theorem liveFast_of_along {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (hRun : RunOK 7 qs W (maxLeN (kdF (qs.map Prod.fst)) qs.length) (capF caps) (fun x => PRl.getD x 0)
      (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst))
      (fun i y x => decide (x ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y))
      (fun i u y x => decide (x ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y))
      (fun i b r d x => decide (x ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) &&
        (!R.clip || decide (0 ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)))
      R)
    {i t r d b : ℕ} {a m pm pM : ℤ} {z last : List ℕ} {usedC : List (List ℕ)} {rest : List TRow}
    (hi : i < qs.length) (ht : t < 16) (hr : r < 256) (hd : d < 256) (hb : b ≤ W) (hwt : d + 6 * t ≤ b)
    (ha1 : -2 ^ 27 ≤ a) (ha2 : a ≤ 2 ^ 27) (hm1 : -2 ^ 27 ≤ m) (hm2 : m ≤ 2 ^ 27)
    (hkd_le : kdF (qs.map Prod.fst) i ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (ht_le : kdF (qs.map Prod.fst) i ≠ 0 → t < kdF (qs.map Prod.fst) i)
    (halong : JAlongR 7 qs (capF caps) (fun x => PRl.getD x 0) (encB 7)
      (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst))
      (fun i y x => decide (x ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y))
      (fun i u y x => decide (x ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y))
      (fun i b r d x => decide (x ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) &&
        (!R.clip || decide (0 ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)))
      R (GateL gs tp) (EarlyL gs tp) i t r d a b m pm pM z last usedC rest) :
    liveFast ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
      (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt m) = true := by
  have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
  have hy_u : UInt32.ofNat b - UInt32.ofNat (d + 6 * t) = UInt32.ofNat (b - (d + 6 * t)) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (d + 6 * t)).toNat ≤ (UInt32.ofNat b).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
      UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold liveFast
  rw [hvc.hkd i hi, hwt_u]; dsimp only; rw [hy_u, vOfFast_eq ht hr hd]
  have hv_bd : -2 ^ 20 ≤ vOf 6 t r d ∧ vOf 6 t r d ≤ 2 ^ 20 := by unfold vOf; omega
  have hshape_live : FinOk 7 (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst)) i r d m (vOf 6 t r d) z last →
      (if (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true then decide ((2 : UInt32) ≤ UInt32.ofNat r)
       else decide (Int64.ofInt m < Int64.ofInt (vOf 6 t r d))) = true := by
    intro hfin; unfold FinOk at hfin
    by_cases hc0 : kdF (qs.map Prod.fst) i = 0
    · rw [if_pos (by simp [hc0]), decide_eq_true_eq]
      rw [if_pos hc0] at hfin
      change (2 : UInt32).toNat ≤ (UInt32.ofNat r).toNat
      rw [show (2 : UInt32).toNat = 2 from rfl, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hfin.1
    · have hcne : ¬ (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true := by
        simp only [beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
        rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by omega)] at this; exact hc0 this
      rw [if_neg hcne, decide_eq_true_eq, Int64.lt_iff_toInt_lt,
        int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]
      rw [if_neg hc0] at hfin; exact hfin
  cases rest with
  | nil =>
    obtain ⟨_, hfin, hlast, hav, _⟩ := halong
    have h1 := hshape_live hfin
    have h2 := compOkFast_of_compOk hvc hnp hW hcaps hPR (y := b - (d + 6 * t)) (a := a) (v := vOf 6 t r d) hi (by omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [if_pos hlast]; exact hav) (eOk := true)
    rw [h1, h2]; simp
  | cons row rest' =>
    rcases row with ⟨kd, Q⟩
    cases Q with
    | nil => exact False.elim halong
    | cons v R0 =>
      match kd with
      | 0 =>
        obtain ⟨_, _, hk3, _⟩ := halong
        unfold k3Ok at hk3
        have hk3f : k3OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
            (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a)
            (UInt32.ofNat b) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) = true := by
          apply k3OkFast_of_k3Ok hvc hnp hW hS hcaps hPR hi ht hr hd hb hwt (by omega) (by omega) hkd_le ht_le
          by_cases hc0 : kdF (qs.map Prod.fst) i = 0
          · rw [if_pos (by simp [hc0])] at hk3; rw [if_pos hc0]
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hk3
            exact ⟨hk3.1, fun hcl => hk3.2.resolve_left (by simp [hcl])⟩
          · rw [if_neg (by simp [hc0])] at hk3; rw [if_neg hc0]
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk3
            exact hk3
        simp [hk3f]
      | 1 =>
        obtain ⟨_, _, hk4, _⟩ := halong
        unfold k4Ok at hk4
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hk4
        have hk4f : k4OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
            (UInt32.ofNat t) (Int64.ofInt a) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) = true := by
          apply k4OkFast_of_k4Ok hvc hnp hW hS hcaps hPR hi ht hr hd hb hwt (by omega) (by omega) hkd_le
          exact ⟨hk4.1.1.1, hk4.1.1.2, hk4.1.2, hk4.2⟩
        simp [hk4f]
      | _ + 2 =>
        obtain ⟨_, _, hfin, hne, hbest, _⟩ := halong
        rw [decide_eq_true_eq] at hbest
        have h1 := hshape_live hfin
        have h2 := compOkFast_of_compOk hvc hnp hW hcaps hPR (y := b - (d + 6 * t)) (a := a) (v := vOf 6 t r d) hi (by omega)
          (by omega) (by omega) (by omega) (by omega) (by rw [if_neg hne]; exact ⟨hbest, rfl⟩) (eOk := true)
        rw [h1, h2]; simp

theorem computeMask_bit_of_live {ctx : FastJ16Ctx} {i t r d b j : ℕ} {a m : Int64}
    (ht : t < 16) (hd : d < 256) (hb : b ≤ 200) (hj : j < 6)
    (hwt : d + 6 * t + (5 - j) ≤ b)
    (hlive : liveFast ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r)
      (UInt32.ofNat (d + (5 - j))) a (UInt32.ofNat b) m = true) :
    ((computeMask ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
      a (UInt32.ofNat b) m).toNat >>> j) % 2 = 1 := by
  have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
  have hadd : ∀ c < 6, UInt32.ofNat d + UInt32.ofNat c = UInt32.ofNat (d + c) ∧
      UInt32.ofNat (d + 6 * t) + UInt32.ofNat c = UInt32.ofNat (d + 6 * t + c) := by
    intro c hc; constructor
    · apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : c < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : d + c < 2 ^ 32)]
    · apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : c < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : d + 6 * t + c < 2 ^ 32)]
  have hle_u : ∀ x ≤ b, (UInt32.ofNat x ≤ UInt32.ofNat b) := by
    intro x hx; change (UInt32.ofNat x).toNat ≤ (UInt32.ofNat b).toNat
    rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hx
  unfold computeMask; dsimp only
  apply computeMask_bit_of_cases _ _ _ _ _ _ j hj
  match j, hj, hwt, hlive with
  | 0, _, hwt, hlive =>
    have ⟨hd5, hw5⟩ := hadd 5 (by omega)
    rw [hwt_u, show (5 : UInt32) = UInt32.ofNat 5 from rfl, hd5, hw5]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩
  | 1, _, hwt, hlive =>
    have ⟨hd4, hw4⟩ := hadd 4 (by omega)
    rw [hwt_u, show (4 : UInt32) = UInt32.ofNat 4 from rfl, hd4, hw4]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩
  | 2, _, hwt, hlive =>
    have ⟨hd3, hw3⟩ := hadd 3 (by omega)
    rw [hwt_u, show (3 : UInt32) = UInt32.ofNat 3 from rfl, hd3, hw3]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩
  | 3, _, hwt, hlive =>
    have ⟨hd2, hw2⟩ := hadd 2 (by omega)
    rw [hwt_u, show (2 : UInt32) = UInt32.ofNat 2 from rfl, hd2, hw2]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩
  | 4, _, hwt, hlive =>
    have ⟨hd1, hw1⟩ := hadd 1 (by omega)
    rw [hwt_u, show (1 : UInt32) = UInt32.ofNat 1 from rfl, hd1, hw1]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩
  | 5, _, hwt, hlive =>
    simp only [Nat.sub_self, Nat.add_zero] at hlive hwt
    rw [hwt_u]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hle_u _ hwt, hlive⟩

/-! ### Main Completeness Theorem: `go_complete` and `jv_of_fastJ16` -/

/-- Every piece along `rest` stays under 250 rows (since `r` resets to `1` on piece jumps). -/
def PieceLenOk (r : ℕ) : List TRow → Prop
  | [] => r < 250
  | (0, _) :: rest => r < 250 ∧ PieceLenOk (r + 1) rest
  | (1, _) :: rest => r < 250 ∧ PieceLenOk (r + 1) rest
  | (_ + 2, _) :: rest => r < 250 ∧ PieceLenOk 1 rest

private theorem pieceLenOk_piece :
    ∀ (S rest : List TRow) (r : ℕ), r + S.length < 250 → (∀ x ∈ S, x.1 ≤ 1) →
      (∀ r', r' = r + S.length → PieceLenOk r' rest) → PieceLenOk r (S ++ rest)
  | [], rest, r, _, _, hrest => hrest r (by simp)
  | (kd, Q) :: S', rest, r, hlen, hle1, hrest => by
    have hkd : kd ≤ 1 := hle1 _ List.mem_cons_self
    have ih := pieceLenOk_piece S' rest (r + 1) (by simp only [List.length_cons] at hlen; omega)
      (fun x hx => hle1 x (List.mem_cons_of_mem _ hx))
      (fun r' hr' => hrest r' (by simp only [List.length_cons]; omega))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
    · exact ⟨by omega, ih⟩
    · exact ⟨by omega, ih⟩

private theorem pieceLenOk_flatJ :
    ∀ (Post : List (List TRow)),
      (∀ L ∈ Post, L.length < 250 ∧ (∀ x ∈ L, x.1 ≤ 1) ∧ L ≠ []) →
      ∀ r < 250, PieceLenOk r (flatJ Post)
  | [], _, r, hr => hr
  | L :: Post', hP, r, hr => by
    have ⟨hlen, hle1, hne⟩ := hP L List.mem_cons_self
    obtain ⟨⟨kd0, Q0⟩, S', rfl⟩ := List.exists_cons_of_ne_nil hne
    show PieceLenOk r ((2, Q0) :: (S' ++ flatJ Post'))
    refine ⟨hr, pieceLenOk_piece S' (flatJ Post') 1 (by simp only [List.length_cons] at hlen; omega)
      (fun x hx => hle1 x (List.mem_cons_of_mem _ hx)) (fun r' hr' => ?_)⟩
    exact pieceLenOk_flatJ Post' (fun M hM => hP M (List.mem_cons_of_mem _ hM)) r' (by simp only [List.length_cons] at hlen; omega)

set_option maxHeartbeats 800000 in
theorem go_complete {caps PRl qs R W bm gs js tp ctx}
    (hvc : ValidJCtx caps PRl qs R W bm gs js tp ctx)
    (hnp : qs.length ≤ 10) (hW : W ≤ 200) (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hbm_lt : bm < 16)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (habh : R.pa ≤ 100 ∧ R.pb ≤ 100 ∧ R.ph ≤ 100) (hrp_lt : R.rp < 256) (hoi_lt : R.oi < 256)
    (hoi_ne : R.oi + 1 < qs.length → kdF (qs.map Prod.fst) R.oi ≠ 0)
    (hvlo_bd : ∀ i < qs.length, -2 ^ 27 ≤ vloF R i ∧ vloF R i ≤ 2 ^ 27)
    (hvhi_bd : ∀ i < qs.length, -2 ^ 27 ≤ vhiF R i ∧ vhiF R i ≤ 2 ^ 27)
    (hspecs_lt : ∀ j < qs.length, loF (qs.map Prod.fst) j < 256 ∧ hiF (qs.map Prod.fst) j < 256)
    (hRun : RunOK 7 qs W (maxLeN (kdF (qs.map Prod.fst)) qs.length) (capF caps) (fun x => PRl.getD x 0)
      (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst))
      (fun i y x => decide (x ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y))
      (fun i u y x => decide (x ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y))
      (fun i b r d x => decide (x ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) &&
        (!R.clip || decide (0 ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)))
      R) :
    ∀ (rest : List TRow) (fuel : ℕ) (i t r d b du : ℕ) (a m pm pM : ℤ)
      (z last : List ℕ) (usedA usedC : List (List ℕ)) (M : ByteArray),
      fuel < 2 ^ 31 →
      i < qs.length → t < 16 → PieceLenOk r rest → d ≤ b → b ≤ W → d + 6 * t ≤ b → du ≤ bm →
      (kdF (qs.map Prod.fst) i ≠ 0 → t < kdF (qs.map Prod.fst) i) →
      -2 ^ 25 + ((qs.length - i : ℕ) : ℤ) * 1000 ≤ a → a ≤ 2 ^ 25 - ((qs.length - i : ℕ) : ℤ) * 1000 →
      -1000 ≤ m → m ≤ 1000 →
      -200200 ≤ pm → pm ≤ 200200 →
      -200200 ≤ pM → pM ≤ 200200 →
      PermW 7 last → PermW 7 z →
      (∀ u ∈ usedA, PermW 7 u) → (∀ u ∈ usedC, PermW 7 u) →
      M.size = (permCodes 7 7).length →
      PS.MInv (encB 7) (fun j => (ciTab 7 (permCodes 7 7))[j]!) M usedA →
      MC (encB 7) (fun j => (ciTab 7 (permCodes 7 7))[j]!) M (UInt8.ofNat (i + 1)) usedC →
      MB M (i + 1) →
      Bud bm du usedA (blocksR rest) →
      (js = true → NoJSAlongJ last rest) →
      JAlongR 7 qs (capF caps) (fun x => PRl.getD x 0) (encB 7)
        (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst))
        (fun i y x => decide (x ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y))
        (fun i u y x => decide (x ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y))
        (fun i b r d x => decide (x ≤ fG (capF caps) (fun x => PRl.getD x 0)
            (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) &&
          (!R.clip || decide (0 ≤ fG (capF caps) (fun x => PRl.getD x 0)
            (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)))
        R (GateL gs tp) (EarlyL gs tp) i t r d a b m pm pM z last usedC rest →
      (go ctx (UInt32.ofNat fuel)
        (packSt (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
          (UInt32.ofNat b) (UInt32.ofNat du) (UInt32.ofNat (encB 7 z)) (UInt32.ofNat (encB 7 last)))
        (packI32Pair (Int64.ofInt a) (Int64.ofInt m))
        (packI32Pair (Int64.ofInt pm) (Int64.ofInt pM)) M).size = 0 := by
  have hsz_le := permCodes7_length_le
  have hEnc := PS.encB_enc 7 (by omega) (by omega)
  have hkd_le_all : ∀ j < qs.length, kdF (qs.map Prod.fst) j ≤ maxLeN (kdF (qs.map Prod.fst)) qs.length := by
    intro j hj
    have haux : ∀ n, ∀ j ≤ n, kdF (qs.map Prod.fst) j ≤ maxLeN (kdF (qs.map Prod.fst)) n := by
      intro n; induction n with
      | zero =>
        intro j hj
        have hj0 : j = 0 := by omega
        rw [hj0]; exact le_refl _
      | succ n ih =>
        intro j hj; by_cases h : j = n + 1
        · subst h; exact le_max_right _ _
        · exact le_trans (ih j (by omega)) (le_max_left _ _)
    exact haux qs.length j (by omega)
  intro rest
  induction rest with
  | nil =>
    intro fuel i t r d b du a m pm pM z last usedA usedC M hfuel hi ht hr hd hb hwt hdu ht_le
      ha1 ha2 hm1 hm2 hpm1 hpm2 hpM1 hpM2 hlast hz husedA husedC hMsz hM hC hB hbud hjsA halong
    cases fuel with
    | zero => rw [go, dif_neg (by decide)]; exact ByteArray.size_empty
    | succ fuel =>
      obtain ⟨hG, hfin, hlast_np, hav, hxc⟩ := halong
      have hr_lt250 : r < 250 := hr
      have hf_pos : UInt32.ofNat (fuel + 1) > 0 := by
        change 0 < (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
      have hz_lt : encB 7 z < 8192 := by have := encB_lt hz; omega
      have hq_lt : encB 7 last < 8192 := by have := encB_lt hlast; omega
      obtain ⟨ui, ut, ur, ud, ub, udu, uz, uq⟩ := packSt_unpack (by omega : i < 16) ht (by omega : r < 256)
        (by omega : d < 256) (by omega : b < 256) (by omega : du < 16) hz_lt hq_lt
      obtain ⟨ua, um⟩ := packI32Pair_unpack (by omega : -2 ^ 30 ≤ a) (by omega : a ≤ 2 ^ 30)
        (by omega : -2 ^ 30 ≤ m) (by omega : m ≤ 2 ^ 30)
      obtain ⟨upm, upM⟩ := packI32Pair_unpack (by omega : -2 ^ 30 ≤ pm) (by omega : pm ≤ 2 ^ 30)
        (by omega : -2 ^ 30 ≤ pM) (by omega : pM ≤ 2 ^ 30)
      rw [go, dif_pos hf_pos]; dsimp only
      rw [ui, ut, ur, ud, ub, udu, uz, uq, hvc.hgate i r (encB 7 last) d (by omega) (by omega) hq_lt (by omega) hG,
        if_pos rfl, ua, um, upm, upM, hvc.hkd i hi, vOfFast_eq ht (by omega) (by omega)]
      have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
      have hy_u : UInt32.ofNat b - UInt32.ofNat (d + 6 * t) = UInt32.ofNat (b - (d + 6 * t)) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (d + 6 * t)).toNat ≤ (UInt32.ofNat b).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
          UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hwt_u, hy_u]
      have hcomp := compOkFast_of_compOk hvc hnp hW hcaps hPR (y := b - (d + 6 * t)) (a := a) (v := vOf 6 t r d) hi (by omega) (by omega) (by omega)
        (by unfold vOf; omega) (by unfold vOf; omega) (by rw [if_pos hlast_np]; exact hav)
        (eOk := checkEarly ctx (UInt32.ofNat i) (UInt32.ofNat r) (UInt32.ofNat (encB 7 last)) (UInt32.ofNat d))
      have hshape : (if (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true then
          decide (2 ≤ UInt32.ofNat r) && decide (getLo ctx (UInt32.ofNat i) ≤ UInt32.ofNat d) &&
          decide (UInt32.ofNat d ≤ getHi ctx (UInt32.ofNat i)) &&
          s3Contains ctx (UInt32.ofNat (encB 7 last)) (UInt32.ofNat (encB 7 z))
        else decide (Int64.ofInt m < Int64.ofInt (vOf 6 t r d))) = true := by
        unfold FinOk at hfin
        by_cases hc0 : kdF (qs.map Prod.fst) i = 0
        · rw [if_pos (by simp [hc0])]; rw [if_pos hc0] at hfin
          obtain ⟨hr2, hlo, hhi, hcl⟩ := hfin
          rw [hvc.hlo i hi, hvc.hhi i hi, s3Contains_true hvc hlast hz hcl]
          simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · change (2 : UInt32).toNat ≤ (UInt32.ofNat r).toNat
            rw [show (2 : UInt32).toNat = 2 from rfl, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hr2
          · change (UInt32.ofNat (loF (qs.map Prod.fst) i)).toNat ≤ (UInt32.ofNat d).toNat
            rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hlo
          · change (UInt32.ofNat d).toNat ≤ (UInt32.ofNat (hiF (qs.map Prod.fst) i)).toNat
            have hhi_lt : hiF (qs.map Prod.fst) i < 2 ^ 32 := by have := (hspecs_lt i hi).2; omega
            rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hhi_lt]; exact hhi
        · have hcne : ¬ (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true := by
            simp only [beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
            rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by have := hkd_le_all i hi; omega)] at this; exact hc0 this
          rw [if_neg hcne]; rw [if_neg hc0] at hfin
          rw [decide_eq_true_eq, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega),
            int64_toInt_ofInt (by unfold vOf; omega) (by unfold vOf; omega)]
          exact hfin
      have hxcf := xcFast_of_xcF hvc hnp hW hS hcaps hPR habh hrp_lt hoi_lt hvlo_bd hvhi_bd
        hi ht (by omega) (by omega) hb hwt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (hkd_le_all i hi) hxc
      have hi1_np : (UInt32.ofNat i + 1 == ctx.np) = true := by
        rw [hvc.hnp, beq_iff_eq]; apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hlast_np
      rw [hcomp, hshape, hxcf, if_pos (show (true && true && true) = true from rfl), if_pos hi1_np,
        if_pos (show (ByteArray.empty.usize == 0) = true from rfl)]
      exact ByteArray.size_empty
  | cons row rest' ih =>
    intro fuel i t r d b du a m pm pM z last usedA usedC M hfuel hi ht hr hd hb hwt hdu ht_le
      ha1 ha2 hm1 hm2 hpm1 hpm2 hpM1 hpM2 hlast hz husedA husedC hMsz hM hC hB hbud hjsA halong
    cases fuel with
    | zero => rw [go, dif_neg (by decide)]; exact ByteArray.size_empty
    | succ fuel =>
      rcases row with ⟨kd, Q⟩
      cases Q with
      | nil => exact False.elim halong
      | cons v R0 =>
        have hf_pos : UInt32.ofNat (fuel + 1) > 0 := by
          change 0 < (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
        have hf_sub : UInt32.ofNat (fuel + 1) - 1 = UInt32.ofNat fuel := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change 1 ≤ (UInt32.ofNat (fuel + 1)).toNat; rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        have hz_lt : encB 7 z < 8192 := by have := encB_lt hz; omega
        have hq_lt : encB 7 last < 8192 := by have := encB_lt hlast; omega
        have hr_lt250 : r < 250 := by
          match kd with
          | 0 => exact hr.1
          | 1 => exact hr.1
          | _ + 2 => exact hr.1
        obtain ⟨ui, ut, ur, ud, ub, udu, uz, uq⟩ := packSt_unpack (by omega : i < 16) ht (by omega : r < 256)
          (by omega : d < 256) (by omega : b < 256) (by omega : du < 16) hz_lt hq_lt
        obtain ⟨ua, um⟩ := packI32Pair_unpack (by omega : -2 ^ 30 ≤ a) (by omega : a ≤ 2 ^ 30)
          (by omega : -2 ^ 30 ≤ m) (by omega : m ≤ 2 ^ 30)
        obtain ⟨upm, upM⟩ := packI32Pair_unpack (by omega : -2 ^ 30 ≤ pm) (by omega : pm ≤ 2 ^ 30)
          (by omega : -2 ^ 30 ≤ pM) (by omega : pM ≤ 2 ^ 30)
        have hwt_u : UInt32.ofNat d + 6 * UInt32.ofNat t = UInt32.ofNat (d + 6 * t) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
            show (6 : UInt32).toNat = 6 from rfl, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : t < 2 ^ 32), Nat.mod_eq_of_lt (by omega : 6 * t < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : d + 6 * t < 2 ^ 32)]
        have hy_u : UInt32.ofNat b - UInt32.ofNat (d + 6 * t) = UInt32.ofNat (b - (d + 6 * t)) := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_sub_of_le _ _ (by change (UInt32.ofNat (d + 6 * t)).toNat ≤ (UInt32.ofNat b).toNat; rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
            UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hbud_eq : blocksR ((kd, v :: R0) :: rest') = (v :: R0) ++ blocksR rest' := by simp [blocksR]
        rw [hbud_eq] at hbud
        have hv_bd : -2 ^ 20 ≤ vOf 6 t r d ∧ vOf 6 t r d ≤ 2 ^ 20 := by unfold vOf; omega
        have hpa_bd : (0 : ℤ) ≤ R.pa ∧ (R.pa : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.1⟩
        have hpb_bd : (0 : ℤ) ≤ R.pb ∧ (R.pb : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.1⟩
        have hph_bd : (0 : ℤ) ≤ R.ph ∧ (R.ph : ℤ) ≤ 100 := ⟨by positivity, by exact_mod_cast habh.2.2⟩
        have hm_ar : (0 : ℤ) ≤ (R.pa : ℤ) * r ∧ (R.pa : ℤ) * r ≤ 25600 :=
          ⟨by positivity, Int.mul_le_mul hpa_bd.2 (by omega : (r : ℤ) ≤ 256) (by omega) (by omega)⟩
        have hm_bd : (0 : ℤ) ≤ (R.pb : ℤ) * d ∧ (R.pb : ℤ) * d ≤ 25600 :=
          ⟨by positivity, Int.mul_le_mul hpb_bd.2 (by omega : (d : ℤ) ≤ 256) (by omega) (by omega)⟩
        have hm_ht : (0 : ℤ) ≤ 2 * (R.ph : ℤ) * t ∧ 2 * (R.ph : ℤ) * t ≤ 3200 :=
          ⟨by positivity, Int.mul_le_mul (by omega : 2 * (R.ph : ℤ) ≤ 200) (by omega : (t : ℤ) ≤ 16) (by omega) (by omega)⟩
        have hfBase_eq : ctx.pa * u32ToI64 (UInt32.ofNat r) - ctx.pb * u32ToI64 (UInt32.ofNat d) -
            ctx.ph2 * u32ToI64 (UInt32.ofNat t) = Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) := by
          rw [hvc.hpa, hvc.hpb, hvc.hph2, u32ToI64, u32ToI64, u32ToI64,
            u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega), u32_toInt64_ofNat (by omega),
            int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_mul (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega),
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
          congr 1; unfold potF; push_cast; ring
        have hfBase_bd : -200000 ≤ potF R.pa R.pb R.ph 0 t r d ∧ potF R.pa R.pb R.ph 0 t r d ≤ 200000 := by
          unfold potF; omega
        have hm'_eq : (if Int64.ofInt m > Int64.ofInt (vOf 6 t r d) then Int64.ofInt m else Int64.ofInt (vOf 6 t r d)) =
            Int64.ofInt (max m (vOf 6 t r d)) := by
          by_cases hgt : vOf 6 t r d < m
          · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_left (le_of_lt hgt)]
          · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
              max_eq_right (by omega)]
        -- First-order Id1 bind helper (prevents any whnf explosion!)
        have hbind_id : ∀ {M1 : ByteArray} (f : ByteArray → ByteArray),
            Id1 M1 M → (f M).size = 0 → (if (M1.usize == 0) = true then M1 else f M1).size = 0 := by
          intro M1 f hid hf
          by_cases hz : (M1.usize == 0) = true
          · rw [if_pos hz]
            have hlt : M1.size < 2 ^ 32 := by
              rcases hid with h | h
              · omega
              · rw [h]; omega
            exact (ba_usize_eq_zero_iff hlt).mp hz
          · rw [if_neg hz]
            rcases hid with h | h
            · exact absurd ((ba_usize_eq_zero_iff (by omega)).mpr h) hz
            · rw [h]; exact hf
        have hite : ∀ {c : Prop} [Decidable c] {X Y M0 : ByteArray}, Id1 X M0 → Id1 Y M0 → Id1 (if c then X else Y) M0 := by
          intro c _ X Y M0 hX hY; split_ifs <;> assumption
        have hid_M1 : Id1 (if ((compOkFast ctx (UInt32.ofNat i) (Int64.ofInt a) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d))
              (checkEarly ctx (UInt32.ofNat i) (UInt32.ofNat r) (UInt32.ofNat (encB 7 last)) (UInt32.ofNat d)) &&
              if (getKd ctx (UInt32.ofNat i) == 0) = true then
                decide (2 ≤ UInt32.ofNat r) && decide (getLo ctx (UInt32.ofNat i) ≤ UInt32.ofNat d) &&
                decide (UInt32.ofNat d ≤ getHi ctx (UInt32.ofNat i)) && s3Contains ctx (UInt32.ofNat (encB 7 last)) (UInt32.ofNat (encB 7 z))
              else decide (Int64.ofInt m < Int64.ofInt (vOf 6 t r d))) &&
              xcFast ctx (UInt32.ofNat i) (getKd ctx (UInt32.ofNat i)) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
                (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt pm) (Int64.ofInt pM)) = true then
            if (UInt32.ofNat i + 1 == ctx.np) = true then ByteArray.empty
            else if (computeMask ctx (UInt32.ofNat i + 1) 0 1 0 (Int64.ofInt a - Int64.ofInt (vOf 6 t r d))
                (UInt32.ofNat (b - (d + 6 * t))) (-6) == 0) = true then M
            else loopU32 5040 0 (fun D M' => walkJFast ctx (fun n e du' M'' =>
              go ctx (UInt32.ofNat fuel) (packSt (UInt32.ofNat i + 1) 0 1 n (UInt32.ofNat (b - (d + 6 * t))) du' D e)
                (packI32Pair (Int64.ofInt a - Int64.ofInt (vOf 6 t r d)) (-6)) 0 M'')
              (UInt8.ofNat ((UInt32.ofNat i + 1).toNat + 1)) 6
              (computeMask ctx (UInt32.ofNat i + 1) 0 1 0 (Int64.ofInt a - Int64.ofInt (vOf 6 t r d))
                (UInt32.ofNat (b - (d + 6 * t))) (-6)) (UInt32.ofNat du) D M') M else M) M := by
          apply hite _ (Or.inr rfl)
          apply hite (Or.inl ByteArray.size_empty)
          apply hite (Or.inr rfl)
          exact loopU32_id 5040 _ (fun D M' hM' =>
            walkJFast_id ctx _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'') _ 6 _ _ D M' (by decide) hM')
            _ 0 M rfl (by omega)
        match kd with
        | 0 =>
          -- Weight-3 continuation inside piece `i`
          obtain ⟨hG, ⟨hR0, hperm, hdoor, hpw⟩, hk3, hxr, hwl, hnew, hwt', halong'⟩ := halong
          rw [go, dif_pos hf_pos]; dsimp only
          rw [ui, ut, ur, ud, ub, udu, uz, uq, hvc.hgate i r (encB 7 last) d (by omega) (by omega) hq_lt (by omega) hG,
            if_pos rfl, hf_sub, ua, um, upm, upM, hwt_u, hy_u, vOfFast_eq ht (by omega) (by omega)]
          rcases hid_M1 with hM1z | hM1eq
          · rw [(ba_usize_eq_zero_iff (by omega)).mpr hM1z, if_pos rfl]; exact hM1z
          rw [hM1eq]
          by_cases hMz : (M.usize == 0) = true
          · rw [if_pos hMz]; exact (ba_usize_eq_zero_iff (by omega)).mp hMz
          rw [if_neg hMz, hvc.hkd i hi, hm'_eq, hfBase_eq]
          have hnr_u : UInt32.ofNat r + 1 = UInt32.ofNat (r + 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hk3f : k3OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i))
              (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a)
              (UInt32.ofNat b) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) = true := by
            apply k3OkFast_of_k3Ok hvc hnp hW hS hcaps hPR hi ht (by omega) (by omega) hb hwt (by omega) (by omega) (hkd_le_all i hi) ht_le
            unfold k3Ok at hk3
            by_cases hc0 : kdF (qs.map Prod.fst) i = 0
            · rw [if_pos (by simp [hc0])] at hk3; rw [if_pos hc0]
              simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hk3
              exact ⟨hk3.1, fun hcl => hk3.2.resolve_left (by simp [hcl])⟩
            · rw [if_neg (by simp [hc0])] at hk3; rw [if_neg hc0]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hk3; exact hk3
          have hxrf := xrFast_of_xrF hvc hnp hW hS hcaps hPR habh hrp_lt hoi_lt hoi_ne (kind := 0) (by omega)
            hi ht (by omega) (by omega) hb hwt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (hkd_le_all i hi) (fun h0 => by have := ht_le h0; omega) (fun h => by cases h) hxr
          change xrFast ctx 0 _ _ _ _ _ _ _ _ _ = true at hxrf
          have hlive' := liveFast_of_along hvc hnp hW hS hcaps hPR hRun hi ht (by omega) (by omega) hb (by omega)
            (by omega) (by omega) (by unfold vOf; omega) (by unfold vOf; omega) (hkd_le_all i hi) ht_le halong'
          have hmk_bit := computeMask_bit_of_live (ctx := ctx) (i := i) (t := t) (r := r + 1) (d := d) (b := b)
            (j := R0.length) (a := Int64.ofInt a) (m := Int64.ofInt (max m (vOf 6 t r d)))
            ht (by omega) (by omega) (by omega) (by omega) hlive'
          set mk := computeMask ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat (r + 1)) (UInt32.ofNat d)
            (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt (max m (vOf 6 t r d)))
          have hmk_ne : ¬ (mk == 0) = true := by
            simp only [beq_iff_eq]; intro h0; rw [h0] at hmk_bit; simp at hmk_bit
          have hnpm_eq : (if Int64.ofInt pm < Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) then Int64.ofInt pm else Int64.ofInt (potF R.pa R.pb R.ph 0 t r d)) =
              Int64.ofInt (min pm (potF R.pa R.pb R.ph 0 t r d)) := by
            by_cases hlt : pm < potF R.pa R.pb R.ph 0 t r d
            · rw [if_pos (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_left (le_of_lt hlt)]
            · rw [if_neg (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_right (by omega)]
          have hnpM_eq : (if Int64.ofInt pM > Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) then Int64.ofInt pM else Int64.ofInt (potF R.pa R.pb R.ph 0 t r d)) =
              Int64.ofInt (max pM (potF R.pa R.pb R.ph 0 t r d)) := by
            by_cases hgt : potF R.pa R.pb R.ph 0 t r d < pM
            · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
                max_eq_left (le_of_lt hgt)]
            · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
                max_eq_right (by omega)]
          have hv := hperm v List.mem_cons_self
          obtain ⟨idx, hidx, hget⟩ := sdTab3_mem_idx hlast hv hwl
          have hstep_zero : (loopU32 6 0 (fun idx' M' =>
              let D := baGetU16 ctx.s3BA ((UInt32.ofNat (encB 7 last)).toUSize * 6 + idx'.toUSize)
              let emk := if ctx.js && baGetU16 ctx.ciBA D.toUSize == (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)
                then mk &&& 1 else mk
              if (emk == 0) = true then M'
              else walkJFast ctx (fun n e du' M'' =>
                go ctx (UInt32.ofNat fuel) (packSt (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat (r + 1)) (UInt32.ofNat d + n)
                  (UInt32.ofNat b) du' (UInt32.ofNat (encB 7 z)) e)
                  (packI32Pair (Int64.ofInt a) (Int64.ofInt (max m (vOf 6 t r d))))
                  (packI32Pair (Int64.ofInt (min pm (potF R.pa R.pb R.ph 0 t r d))) (Int64.ofInt (max pM (potF R.pa R.pb R.ph 0 t r d)))) M'')
                (UInt8.ofNat ((UInt32.ofNat i).toNat + 1)) 6 emk (UInt32.ofNat du) D M') M).size = 0 := by
            apply loopU32_complete 6 (by decide) _ (fun idx' M' hM' => by
              dsimp only
              exact hite (Or.inr rfl) (walkJFast_id ctx _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'') _ 6 _ _ _ M' (by decide) hM'))
              idx hidx M (by omega)
            dsimp only
            have hidx_us : (UInt32.ofNat idx).toUSize = USize.ofNat idx := by
              apply USize.toNat_inj.mp; rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
            have hD_eq : baGetU16 ctx.s3BA ((UInt32.ofNat (encB 7 last)).toUSize * 6 + (UInt32.ofNat idx).toUSize) =
                UInt32.ofNat (encB 7 v) := by
              rw [hidx_us, hvc.hs3BA hlast hidx, hget]
            rw [hD_eq]
            have hemk_bit : ((if ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
                (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)
                then mk &&& 1 else mk).toNat >>> R0.length) % 2 = 1 := by
              by_cases hj : (ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
                  (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)) = true
              · rw [if_pos hj]
                simp only [Bool.and_eq_true, beq_iff_eq, hvc.hjs] at hj
                have hjs_true : js = true := hj.1
                rw [hjs_true, if_pos rfl, hvc.hciBA hv, hvc.hb2CiBA hlast] at hj
                have hci_eq : (ciTab 7 (permCodes 7 7))[encB 7 v]! =
                    (ciTab 7 (permCodes 7 7))[(nxtTab 7 (permCodes 7 7))[encB 7 last]!]! := by
                  have := congrArg UInt32.toNat hj.2
                  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                    Nat.mod_eq_of_lt (by have := ciTab_lt (encB_lt hv); omega),
                    Nat.mod_eq_of_lt (by have := ciTab_lt (nxtTab_lt (encB_lt hlast)); omega)] at this
                  exact this
                rw [hEnc.nxt_eq last (K16.tau2 7 last) hlast rfl] at hci_eq
                have hrot : v ~r K16.tau2 7 last := hEnc.ci_inj v (K16.tau2 7 last) hv (K16.permW_tau2 (by omega) hlast) hci_eq
                have hR0nil : R0 = [] := (hjsA hjs_true).1 hrot
                subst hR0nil
                simp only [List.length_nil, Nat.shiftRight_zero, UInt32.toNat_and, UInt32.toNat_one, Nat.and_one_is_mod] at hmk_bit ⊢
                omega
              · rw [if_neg hj]; exact hmk_bit
            have hemk_ne : ¬ ((if ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
                (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)
                then mk &&& 1 else mk) == 0) = true := by
              simp only [beq_iff_eq]; intro h0; rw [h0] at hemk_bit; simp at hemk_bit
            rw [if_neg hemk_ne]
            have hpm_eq : UInt8.ofNat ((UInt32.ofNat i).toNat + 1) = UInt8.ofNat (i + 1) := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
            rw [hpm_eq]
            apply walkJFast_complete hvc hbm_lt _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'')
              (UInt8.ofNat (i + 1)) (i + 1) (le_of_eq (J15.toNat_ofNat8 (by omega)))
              R0 6 _ du v M usedA usedC (blocksR rest') (by decide) (by omega) hemk_bit (by omega)
              hperm hdoor hMsz hM hC hB husedA husedC hnew hpw hbud
            intro M' du' hM'sz hdu' hM' hC' hB' hbud'
            have hd_add : UInt32.ofNat d + UInt32.ofNat (6 - 1 - R0.length) = UInt32.ofNat (d + (5 - R0.length)) := by
              apply UInt32.toNat_inj.mp
              rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
            rw [hd_add]
            exact ih fuel i t (r + 1) (d + (5 - R0.length)) b du' a (max m (vOf 6 t r d))
              (min pm (potF R.pa R.pb R.ph 0 t r d)) (max pM (potF R.pa R.pb R.ph 0 t r d))
              z ((v :: R0).getLast (List.cons_ne_nil v R0)) (usedA ++ v :: R0) (usedC ++ v :: R0) M'
              (by omega) hi ht hr.2 (by omega) hb (by omega) hdu' ht_le
              ha1 ha2 (by unfold vOf; omega) (by unfold vOf; omega)
              (by omega) (by omega) (by omega) (by omega)
              (hperm _ (List.getLast_mem _)) hz
              (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedA u h; exact hperm u h)
              (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedC u h; exact hperm u h)
              hM'sz hM' hC' hB' hbud' (fun hj => (hjsA hj).2) halong'
          rw [hk3f, hxrf, if_pos (show (true && true) = true from rfl), hnr_u, if_neg hmk_ne, hnpm_eq, hnpM_eq,
            if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hstep_zero)]
          exact hstep_zero
        | 1 =>
          -- Weight-4 continuation inside piece `i`
          obtain ⟨hG, ⟨hR0, hperm, hdoor, hpw⟩, hk4, hxr, hwl, hnew, hwt', halong'⟩ := halong
          rw [go, dif_pos hf_pos]; dsimp only
          rw [ui, ut, ur, ud, ub, udu, uz, uq, hvc.hgate i r (encB 7 last) d (by omega) (by omega) hq_lt (by omega) hG,
            if_pos rfl, hf_sub, ua, um, upm, upM, hwt_u, hy_u, vOfFast_eq ht (by omega) (by omega)]
          rcases hid_M1 with hM1z | hM1eq
          · rw [(ba_usize_eq_zero_iff (by omega)).mpr hM1z, if_pos rfl]; exact hM1z
          rw [hM1eq]
          by_cases hMz : (M.usize == 0) = true
          · rw [if_pos hMz]; exact (ba_usize_eq_zero_iff (by omega)).mp hMz
          rw [if_neg hMz, hvc.hkd i hi, hm'_eq, hfBase_eq]
          have hid_M2 : Id1 (if (k3OkFast ctx (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i)) (UInt32.ofNat t)
                (UInt32.ofNat r) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b) (UInt32.ofNat (b - (d + 6 * t))) (Int64.ofInt (vOf 6 t r d)) &&
                xrFast ctx 0 (UInt32.ofNat i) (UInt32.ofNat (kdF (qs.map Prod.fst) i)) (UInt32.ofNat t) (UInt32.ofNat r) (UInt32.ofNat d)
                  (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt pm) (Int64.ofInt pM)) = true then
              if (computeMask ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r + 1) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b)
                (Int64.ofInt (max m (vOf 6 t r d))) == 0) = true then M
              else loopU32 6 0 (fun idx' M' =>
                let D := baGetU16 ctx.s3BA ((UInt32.ofNat (encB 7 last)).toUSize * 6 + idx'.toUSize)
                let emk := if (ctx.js && baGetU16 ctx.ciBA D.toUSize == (if ctx.js = true then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)) = true
                  then computeMask ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r + 1) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt (max m (vOf 6 t r d))) &&& 1
                  else computeMask ctx (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r + 1) (UInt32.ofNat d) (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt (max m (vOf 6 t r d)))
                if (emk == 0) = true then M'
                else walkJFast ctx (fun n e du' M'' =>
                  go ctx (UInt32.ofNat fuel) (packSt (UInt32.ofNat i) (UInt32.ofNat t) (UInt32.ofNat r + 1) (UInt32.ofNat d + n)
                    (UInt32.ofNat b) du' (UInt32.ofNat (encB 7 z)) e)
                    (packI32Pair (Int64.ofInt a) (Int64.ofInt (max m (vOf 6 t r d))))
                    (packI32Pair (if Int64.ofInt pm < Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) then Int64.ofInt pm else Int64.ofInt (potF R.pa R.pb R.ph 0 t r d))
                      (if Int64.ofInt pM > Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) then Int64.ofInt pM else Int64.ofInt (potF R.pa R.pb R.ph 0 t r d))) M'')
                  (UInt8.ofNat ((UInt32.ofNat i).toNat + 1)) 6 emk (UInt32.ofNat du) D M') M else M) M := by
            apply hite _ (Or.inr rfl)
            apply hite (Or.inr rfl)
            exact loopU32_id 6 _ (fun idx' M' hM' => by
              dsimp only
              exact hite (Or.inr rfl) (walkJFast_id ctx _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'') _ 6 _ _ _ M' (by decide) hM'))
              _ 0 M rfl (by omega)
          rcases hid_M2 with hM2z | hM2eq
          · rw [(ba_usize_eq_zero_iff (by omega)).mpr hM2z, if_pos rfl]; exact hM2z
          rw [hM2eq, if_neg hMz]
          unfold k4Ok at hk4; simp only [Bool.and_eq_true, decide_eq_true_eq] at hk4
          have hk4f := k4OkFast_of_k4Ok hvc hnp hW hS hcaps hPR hi ht (by omega) (by omega) hb hwt (by omega) (by omega)
            (hkd_le_all i hi) ⟨hk4.1.1.1, hk4.1.1.2, hk4.1.2, hk4.2⟩
          have hxrf := xrFast_of_xrF hvc hnp hW hS hcaps hPR habh hrp_lt hoi_lt hoi_ne (kind := 1) (by omega)
            hi ht (by omega) (by omega) hb hwt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (hkd_le_all i hi) (fun _ => hk4.1.1.1) (fun _ => hk4.1.2) hxr
          change xrFast ctx 1 _ _ _ _ _ _ _ _ _ = true at hxrf
          have ht1_lt : t + 1 < 16 := by have := hkd_le_all i hi; omega
          have hnt_u : UInt32.ofNat t + 1 = UInt32.ofNat (t + 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hnr_u : UInt32.ofNat r + 1 = UInt32.ofNat (r + 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hlive' := liveFast_of_along hvc hnp hW hS hcaps hPR hRun hi ht1_lt (by omega) (by omega) hb (by omega)
            (by omega) (by omega) (by unfold vOf; omega) (by unfold vOf; omega) (hkd_le_all i hi) (fun _ => hk4.1.1.1) halong'
          have hmk_bit := computeMask_bit_of_live (ctx := ctx) (i := i) (t := t + 1) (r := r + 1) (d := d) (b := b)
            (j := R0.length) (a := Int64.ofInt a) (m := Int64.ofInt (max m (vOf 6 t r d)))
            ht1_lt (by omega) (by omega) (by omega) (by omega) hlive'
          set mk := computeMask ctx (UInt32.ofNat i) (UInt32.ofNat (t + 1)) (UInt32.ofNat (r + 1)) (UInt32.ofNat d)
            (Int64.ofInt a) (UInt32.ofNat b) (Int64.ofInt (max m (vOf 6 t r d)))
          have hmk_ne : ¬ (mk == 0) = true := by
            simp only [beq_iff_eq]; intro h0; rw [h0] at hmk_bit; simp at hmk_bit
          have hfp_eq : Int64.ofInt (potF R.pa R.pb R.ph 0 t r d) - ctx.ph = Int64.ofInt (potF R.pa R.pb R.ph 1 t r d) := by
            rw [hvc.hph, int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)]
            congr 1; unfold potF; push_cast; ring
          have hfp_bd : -200200 ≤ potF R.pa R.pb R.ph 1 t r d ∧ potF R.pa R.pb R.ph 1 t r d ≤ 200200 := by
            have : potF R.pa R.pb R.ph 1 t r d = potF R.pa R.pb R.ph 0 t r d - R.ph := by unfold potF; push_cast; ring
            omega
          have hnpm_eq : (if Int64.ofInt pm < Int64.ofInt (potF R.pa R.pb R.ph 1 t r d) then Int64.ofInt pm else Int64.ofInt (potF R.pa R.pb R.ph 1 t r d)) =
              Int64.ofInt (min pm (potF R.pa R.pb R.ph 1 t r d)) := by
            by_cases hlt : pm < potF R.pa R.pb R.ph 1 t r d
            · rw [if_pos (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_left (le_of_lt hlt)]
            · rw [if_neg (by rw [Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hlt),
                min_eq_right (by omega)]
          have hnpM_eq : (if Int64.ofInt pM > Int64.ofInt (potF R.pa R.pb R.ph 1 t r d) then Int64.ofInt pM else Int64.ofInt (potF R.pa R.pb R.ph 1 t r d)) =
              Int64.ofInt (max pM (potF R.pa R.pb R.ph 1 t r d)) := by
            by_cases hgt : potF R.pa R.pb R.ph 1 t r d < pM
            · rw [if_pos (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
                max_eq_left (le_of_lt hgt)]
            · rw [if_neg (by rw [gt_iff_lt, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega), int64_toInt_ofInt (by omega) (by omega)]; exact hgt),
                max_eq_right (by omega)]
          have hv := hperm v List.mem_cons_self
          obtain ⟨idx, hidx, hget⟩ := sdTab4_mem_idx hlast hv hwl
          rw [hk4f, hxrf, if_pos (show (true && true) = true from rfl), hnt_u, hnr_u, if_neg hmk_ne, hfp_eq, hnpm_eq, hnpM_eq]
          apply loopU32_complete 24 (by decide) _ (fun idx' M' hM' =>
            hite (Or.inr rfl) (walkJFast_id ctx _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'') _ 6 _ _ _ M' (by decide) hM'))
            idx hidx M (by omega)
          have hidx_us : (UInt32.ofNat idx).toUSize = USize.ofNat idx := by
            apply USize.toNat_inj.mp; rw [UInt32.toNat_toUSize, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), usize_ofNat_toNat (by omega)]
          have hD_eq : baGetU16 ctx.s4BA ((UInt32.ofNat (encB 7 last)).toUSize * 24 + (UInt32.ofNat idx).toUSize) =
              UInt32.ofNat (encB 7 v) := by
            rw [hidx_us, hvc.hs4BA hlast hidx, hget]
          rw [hD_eq]
          have hemk_bit : ((if ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
              (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)
              then mk &&& 1 else mk).toNat >>> R0.length) % 2 = 1 := by
            by_cases hj : (ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
                (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)) = true
            · rw [if_pos hj]
              simp only [Bool.and_eq_true, beq_iff_eq, hvc.hjs] at hj
              have hjs_true : js = true := hj.1
              rw [hjs_true, if_pos rfl, hvc.hciBA hv, hvc.hb2CiBA hlast] at hj
              have hci_eq : (ciTab 7 (permCodes 7 7))[encB 7 v]! =
                  (ciTab 7 (permCodes 7 7))[(nxtTab 7 (permCodes 7 7))[encB 7 last]!]! := by
                have := congrArg UInt32.toNat hj.2
                rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat',
                  Nat.mod_eq_of_lt (by have := ciTab_lt (encB_lt hv); omega),
                  Nat.mod_eq_of_lt (by have := ciTab_lt (nxtTab_lt (encB_lt hlast)); omega)] at this
                exact this
              rw [hEnc.nxt_eq last (K16.tau2 7 last) hlast rfl] at hci_eq
              have hrot : v ~r K16.tau2 7 last := hEnc.ci_inj v (K16.tau2 7 last) hv (K16.permW_tau2 (by omega) hlast) hci_eq
              have hR0nil : R0 = [] := (hjsA hjs_true).1 hrot
              subst hR0nil
              simp only [List.length_nil, Nat.shiftRight_zero, UInt32.toNat_and, UInt32.toNat_one, Nat.and_one_is_mod] at hmk_bit ⊢
              omega
            · rw [if_neg hj]; exact hmk_bit
          have hemk_ne : ¬ ((if ctx.js && baGetU16 ctx.ciBA (UInt32.ofNat (encB 7 v)).toUSize ==
              (if ctx.js then baGetU16 ctx.b2CiBA (UInt32.ofNat (encB 7 last)).toUSize else 9999)
              then mk &&& 1 else mk) == 0) = true := by
            simp only [beq_iff_eq]; intro h0; rw [h0] at hemk_bit; simp at hemk_bit
          rw [if_neg hemk_ne]
          have hpm_eq : UInt8.ofNat ((UInt32.ofNat i).toNat + 1) = UInt8.ofNat (i + 1) := by
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          rw [hpm_eq]
          apply walkJFast_complete hvc hbm_lt _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'')
            (UInt8.ofNat (i + 1)) (i + 1) (le_of_eq (J15.toNat_ofNat8 (by omega)))
            R0 6 _ du v M usedA usedC (blocksR rest') (by decide) (by omega) hemk_bit (by omega)
            hperm hdoor hMsz hM hC hB husedA husedC hnew hpw hbud
          intro M' du' hM'sz hdu' hM' hC' hB' hbud'
          have hd_add : UInt32.ofNat d + UInt32.ofNat (6 - 1 - R0.length) = UInt32.ofNat (d + (5 - R0.length)) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
          rw [hd_add]
          exact ih fuel i (t + 1) (r + 1) (d + (5 - R0.length)) b du' a (max m (vOf 6 t r d))
            (min pm (potF R.pa R.pb R.ph 1 t r d)) (max pM (potF R.pa R.pb R.ph 1 t r d))
            z ((v :: R0).getLast (List.cons_ne_nil v R0)) (usedA ++ v :: R0) (usedC ++ v :: R0) M'
            (by omega) hi ht1_lt hr.2 (by omega) hb (by omega) hdu'
            (fun _ => hk4.1.1.1)
            ha1 ha2 (by unfold vOf; omega) (by unfold vOf; omega)
            (by omega) (by omega) (by omega) (by omega)
            (hperm _ (List.getLast_mem _)) hz
            (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedA u h; exact hperm u h)
            (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedC u h; exact hperm u h)
            hM'sz hM' hC' hB' hbud' (fun hj => (hjsA hj).2) halong'
        | _ + 2 =>
          -- Jump to piece `i + 1`!
          obtain ⟨hG, ⟨hR0, hperm, hdoor, hpw⟩, hfin, hne_np, hbest, hxc, hE, hwt', halong'⟩ := halong
          rw [decide_eq_true_eq] at hbest
          have hi1_lt : i + 1 < qs.length := by omega
          have hi1_u : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          have hi1_ne : ¬ (UInt32.ofNat (i + 1) == ctx.np) = true := by
            rw [hvc.hnp, beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
            rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
            exact hne_np this
          have hearly := hvc.hearly i r (encB 7 last) d (by omega) (by omega) hq_lt (by omega) hE
          have hcomp := compOkFast_of_compOk hvc hnp hW hcaps hPR (y := b - (d + 6 * t)) (a := a) (v := vOf 6 t r d) hi (by omega) (by omega) (by omega)
            (by unfold vOf; omega) (by unfold vOf; omega) (by rw [if_neg hne_np]; exact ⟨hbest, hearly⟩)
          have hshape : (if (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true then
              decide (2 ≤ UInt32.ofNat r) && decide (getLo ctx (UInt32.ofNat i) ≤ UInt32.ofNat d) &&
              decide (UInt32.ofNat d ≤ getHi ctx (UInt32.ofNat i)) &&
              s3Contains ctx (UInt32.ofNat (encB 7 last)) (UInt32.ofNat (encB 7 z))
            else decide (Int64.ofInt m < Int64.ofInt (vOf 6 t r d))) = true := by
            unfold FinOk at hfin
            by_cases hc0 : kdF (qs.map Prod.fst) i = 0
            · rw [if_pos (by simp [hc0])]; rw [if_pos hc0] at hfin
              obtain ⟨hr2, hlo, hhi, hcl⟩ := hfin
              rw [hvc.hlo i hi, hvc.hhi i hi, s3Contains_true hvc hlast hz hcl]
              simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · change (2 : UInt32).toNat ≤ (UInt32.ofNat r).toNat
                rw [show (2 : UInt32).toNat = 2 from rfl, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hr2
              · change (UInt32.ofNat (loF (qs.map Prod.fst) i)).toNat ≤ (UInt32.ofNat d).toNat
                rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hlo
              · change (UInt32.ofNat d).toNat ≤ (UInt32.ofNat (hiF (qs.map Prod.fst) i)).toNat
                have hhi_lt : hiF (qs.map Prod.fst) i < 2 ^ 32 := by have := (hspecs_lt i hi).2; omega
                rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hhi_lt]; exact hhi
            · have hcne : ¬ (UInt32.ofNat (kdF (qs.map Prod.fst) i) == 0) = true := by
                simp only [beq_iff_eq]; intro h; have := congrArg UInt32.toNat h
                rw [UInt32.toNat_ofNat', UInt32.toNat_zero, Nat.mod_eq_of_lt (by have := hkd_le_all i hi; omega)] at this; exact hc0 this
              rw [if_neg hcne]; rw [if_neg hc0] at hfin
              rw [decide_eq_true_eq, Int64.lt_iff_toInt_lt, int64_toInt_ofInt (by omega) (by omega),
                int64_toInt_ofInt (by omega) (by omega)]
              exact hfin
          have hxcf := xcFast_of_xcF hvc hnp hW hS hcaps hPR habh hrp_lt hoi_lt hvlo_bd hvhi_bd
            hi ht (by omega) (by omega) hb hwt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (hkd_le_all i hi) hxc
          have hna_eq : Int64.ofInt a - Int64.ofInt (vOf 6 t r d) = Int64.ofInt (a - vOf 6 t r d) :=
            int64_ofInt_sub (by omega) (by omega) (by omega) (by omega)
          have hlive' := liveFast_of_along hvc hnp hW hS hcaps hPR hRun hi1_lt (by omega) (by omega) (by omega)
            (by omega) (by omega) (by unfold vOf; omega) (by unfold vOf; omega) (by omega) (by omega)
            (hkd_le_all (i + 1) hi1_lt) (fun h0 => Nat.pos_of_ne_zero h0) halong'
          have hmk_bit := computeMask_bit_of_live (ctx := ctx) (i := i + 1) (t := 0) (r := 1) (d := 0)
            (b := b - (d + 6 * t)) (j := R0.length) (a := Int64.ofInt (a - vOf 6 t r d)) (m := (-6 : Int64))
            (by omega) (by omega) (by omega) (by omega) (by omega) (by simpa using hlive')
          set mk := computeMask ctx (UInt32.ofNat (i + 1)) 0 1 0 (Int64.ofInt (a - vOf 6 t r d))
            (UInt32.ofNat (b - (d + 6 * t))) (-6)
          have hmk_ne : ¬ (mk == 0) = true := by
            simp only [beq_iff_eq]; intro h0
            change (mk.toNat >>> R0.length) % 2 = 1 at hmk_bit
            rw [h0] at hmk_bit; simp at hmk_bit
          have hv := hperm v List.mem_cons_self
          have hv_lt : encB 7 v < 5040 := lt_of_lt_of_le (encB_lt hv) hsz_le
          have hpm_eq : UInt8.ofNat ((UInt32.ofNat (i + 1)).toNat + 1) = UInt8.ofNat (i + 2) := by
            rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          have hstep_zero : (loopU32 5040 0 (fun D M' =>
              walkJFast ctx (fun n e du' M'' =>
                go ctx (UInt32.ofNat fuel) (packSt (UInt32.ofNat (i + 1)) 0 1 n (UInt32.ofNat (b - (d + 6 * t))) du' D e)
                  (packI32Pair (Int64.ofInt (a - vOf 6 t r d)) (-6)) 0 M'')
                (UInt8.ofNat (i + 2)) 6 mk (UInt32.ofNat du) D M') M).size = 0 := by
            apply loopU32_complete 5040 (by decide) _ (fun D M' hM' =>
              walkJFast_id ctx _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'') _ 6 _ _ D M' (by decide) hM')
              (encB 7 v) hv_lt M (by omega)
            have hC_new : MC (encB 7) (fun j => (ciTab 7 (permCodes 7 7))[j]!) M (UInt8.ofNat (i + 2)) [] :=
              J15.mc_of_mb hB (by omega)
            apply walkJFast_complete hvc hbm_lt _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'')
              (UInt8.ofNat (i + 2)) (i + 2) (le_of_eq (J15.toNat_ofNat8 (by omega)))
              R0 6 mk du v M usedA [] (blocksR rest') (by decide) (by omega) hmk_bit (by omega)
              hperm hdoor hMsz hM hC_new (fun j => le_trans (hB j) (by omega)) husedA (by simp) (by simp) hpw hbud
            intro M' du' hM'sz hdu' hM' hC' hB' hbud'
            have h0_pair : (0 : UInt64) = packI32Pair (Int64.ofInt 0) (Int64.ofInt 0) := by decide
            rw [h0_pair]
            exact ih fuel (i + 1) 0 1 (5 - R0.length) (b - (d + 6 * t)) du'
              (a - vOf 6 t r d) (-6) 0 0 v ((v :: R0).getLast (List.cons_ne_nil v R0))
              (usedA ++ v :: R0) (v :: R0) M'
              (by omega) hi1_lt (by omega) hr.2 (by omega) (by omega) (by omega) hdu'
              (fun h0 => Nat.pos_of_ne_zero h0)
              (by unfold vOf; omega) (by unfold vOf; omega)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (hperm _ (List.getLast_mem _)) hv
              (fun u hu => by rcases List.mem_append.mp hu with h | h; exact husedA u h; exact hperm u h)
              hperm hM'sz hM' (by exact hC') hB' hbud' hjsA halong'
          rw [go, dif_pos hf_pos]; dsimp only
          rw [ui, ut, ur, ud, ub, udu, uz, uq, hvc.hgate i r (encB 7 last) d (by omega) (by omega) hq_lt (by omega) hG,
            if_pos rfl, hf_sub, ua, um, upm, upM, hvc.hkd i hi, hwt_u, hy_u, vOfFast_eq ht (by omega) (by omega),
            hcomp, hshape, hxcf, if_pos (show (true && true && true) = true from rfl), hi1_u, if_neg hi1_ne, hna_eq, if_neg hmk_ne, hpm_eq,
            if_pos ((ba_usize_eq_zero_iff (by omega)).mpr hstep_zero)]
          exact hstep_zero

private theorem par_false_j {part : ℕ → Bool} {pa pb : ℕ} (h : par part pa pb = false) :
    ∀ tp, pa ≤ tp → tp < pb → part tp = false := by
  intro tp h1 h2
  unfold par at h
  rw [List.any_map, List.any_eq_false] at h
  have h3 := h (tp - pa) (List.mem_range.mpr (by omega))
  have e : pa + (tp - pa) = tp := by omega
  simpa [Task.spawn, e] using h3

set_option maxHeartbeats 800000 in
/-- **Top-level soundness theorem for `FastJ16.jSearch`!** -/
theorem jv_of_fastJ16 {caps : List (List ℕ)} {PRl : List ℕ} {qs : List Q}
    {R : Rules} {V W bm fuel sm : ℕ} {gs : List (ℕ × ℕ × ℕ)} {js : Bool}
    (hne : qs ≠ []) (hnp : qs.length ≤ 10) (hV : V ≤ 500) (hW : W ≤ 200) (hbm : bm < 16)
    (hfuel : fuel < 2 ^ 31)
    (hcaps : ∀ row ∈ caps, ∀ v ∈ row, v ≤ 200) (hPR : ∀ v ∈ PRl, v ≤ 200)
    (hspecs : ∀ q ∈ qs, q.1.1 < 16 ∧ q.1.2.1 < 256 ∧ q.1.2.2 < 256)
    (hS : maxLeN (kdF (qs.map Prod.fst)) qs.length ≤ 14)
    (hsm : sm = maxLeN (kdF (qs.map Prod.fst)) qs.length)
    (hsm_le : ∀ q ∈ qs, q.1.1 ≤ sm + 1)
    (hc : J16.CapsOKV 7 (capF caps) (fun x => PRl.getD x 0) W sm qs)
    (hR : ∀ i < qs.length, vloF R i = (qs.getD i dq).2.1 ∧ vhiF R i = (qs.getD i dq).2.2)
    (hpa : 0 < R.pa) (hab : R.pa ≤ R.pb) (hXL : 2 * R.ph ≤ 6 * (R.pb - R.pa) + 5 * R.pa)
    (habh : R.pa ≤ 100 ∧ R.pb ≤ 100 ∧ R.ph ≤ 100) (hrp_lt : R.rp < 256) (hoi_lt : R.oi < 256)
    (hoi_ne : R.oi + 1 < qs.length → (qs.getD R.oi dq).1.1 ≠ 0)
    (hoi_eq : R.oi + 1 < qs.length → qs.getD R.oi dq = qs.getD (R.oi + 1) dq)
    (hclip : R.clip = true → ∀ q ∈ qs, q.1.1 = 0 → 0 ≤ q.2.1)
    (hvlo_bd : ∀ i < qs.length, -2 ^ 27 ≤ vloF R i ∧ vloF R i ≤ 2 ^ 27)
    (hvhi_bd : ∀ i < qs.length, -2 ^ 27 ≤ vhiF R i ∧ vhiF R i ≤ 2 ^ 27)
    (hgs : ∀ g ∈ gs, g.1 < 16 ∧ g.2.1 < 256 ∧ 0 < g.2.2 ∧ g.2.2 < 65536) (hgs_len : gs.length < 100)
    (hs : ∀ tp < gprod gs, ∃ pa pb, pa ≤ tp ∧ tp < pb ∧
      FastJ16.jSearch caps PRl (qs.map Prod.fst) R V W bm fuel gs js pa pb = false) :
    JV 7 qs (V : ℤ) W bm := by
  subst hsm
  have hRun : RunOK 7 qs W (maxLeN (kdF (qs.map Prod.fst)) qs.length) (capF caps) (fun x => PRl.getD x 0)
      (kdF (qs.map Prod.fst)) (loF (qs.map Prod.fst)) (hiF (qs.map Prod.fst))
      (fun i y x => decide (x ≤ BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i y))
      (fun i u y x => decide (x ≤ bestStep (capF caps) (fun x => PRl.getD x 0) 6 (u + 1, 0, 0)
        (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) y))
      (fun i b r d x => decide (x ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d) &&
        (!R.clip || decide (0 ≤ fG (capF caps) (fun x => PRl.getD x 0)
          (BfOf 7 (capF caps) (fun x => PRl.getD x 0) qs i) (loF (qs.map Prod.fst) i) (hiF (qs.map Prod.fst) i) (vloF R i) b r d)))
      R := by
    refine ⟨by omega, hc, hsm_le, fun _ _ => ⟨rfl, rfl, rfl⟩, hR, hpa, hab, hXL, hoi_ne, hclip,
      fun i y x _ _ hx => decide_eq_true hx,
      fun i u y x _ _ _ hx => decide_eq_true hx,
      fun i b r d x _ _ _ hx hcl => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    refine ⟨hx, ?_⟩
    by_cases h : R.clip = true
    · exact Or.inr (hcl h)
    · exact Or.inl (Bool.eq_false_iff.mpr h)
  have hP_le : ∀ t x, capF caps t x ≤ 200 := capF_le_of_hcaps hcaps
  have hPR_le : ∀ x, PRl.getD x 0 ≤ 200 := PRl_getD_le_of_hPR hPR
  have hspecs_lt : ∀ j < qs.length, loF (qs.map Prod.fst) j < 256 ∧ hiF (qs.map Prod.fst) j < 256 := by
    intro j hj
    have hsp := hspecs (qs[j]'hj) (List.getElem_mem hj)
    have hlt_m : j < (qs.map Prod.fst).length := by simp [hj]
    unfold loF hiF
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_m, Option.getD_some]
    simp [hsp.2.1, hsp.2.2]
  have hoi_kd_ne : R.oi + 1 < qs.length → kdF (qs.map Prod.fst) R.oi ≠ 0 := by
    intro hlt
    have hne' := hoi_ne hlt
    have hj : R.oi < qs.length := by omega
    have hlt_m : R.oi < (qs.map Prod.fst).length := by simp [hj]
    unfold kdF
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_m, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hne'
    simpa using hne'
  by_contra hfail
  obtain ⟨Ls, hce, hmin, hnf, hnoJS, kd0, R1, S1, Post1, rfl⟩ :=
    exists_nf_noJS R.rp R.pa R.pb R.ph R.oi hne hoi_eq hfail
  obtain ⟨q0, qpost, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hfa := List.forall₂_cons.mp hce.1
  have M : J16.MinAtV 7 (q0 :: qpost) (V : ℤ) W bm [] [] q0 ((kd0, List.range' 1 7 :: R1) :: S1) qpost Post1 :=
    ⟨rfl, List.Forall₂.nil, hfa.1, hfa.2, hce.2.1, hce.2.2.1, hce.2.2.2, hmin⟩
  have hnf' : NF 7 (q0 :: qpost) R.rp R.pa R.pb R.ph R.oi ([] ++ ((kd0, List.range' 1 7 :: R1) :: S1) :: Post1) := by
    simpa using hnf
  have hseq := M.hS.1.1.isSeq
  obtain ⟨⟨hR1, hperm, hdoor, hpw⟩, _⟩ := rowOk_of_split (by omega) (u := []) hseq
  have hend := J16.along_minV (enc := encB 7) (gi := 0) (gr := 0) hRun Post1 qpost [] [] q0 _ M hnf'
  have hm0 : q0.1.1 ≠ 0 → -((7 - 1 : ℕ) : ℤ) < valK 7 ((kd0, List.range' 1 7 :: R1) :: S1) := by
    intro h0
    have h1 := J15.valK_single_gt (k := 7) (kd := kd0) (v := List.range' 1 7) (by omega) hR1
    cases S1 with
    | nil => exact h1
    | cons y w'' =>
      have h2 := M.rec_lt h0 (u := [(kd0, List.range' 1 7 :: R1)]) (x := y) (w := w'') rfl (by simp)
      linarith
  have hinner := J16.inner_minV (enc := encB 7) (gi := 0) (gr := 0) hRun M hnf' hend S1
    [(kd0, List.range' 1 7 :: R1)] (-6) 0 0 rfl (by simp) hm0 (J16.potI_one R.pa R.pb R.ph _)
  have f2 : linksT [(kd0, List.range' 1 7 :: R1)] = 0 := rfl
  have f3 : [(kd0, List.range' 1 7 :: R1)].length = 1 := rfl
  have f4 : holesT 7 [(kd0, List.range' 1 7 :: R1)] = 5 - R1.length := by simp [holesT]
  have f7 : firstB ((kd0, List.range' 1 7 :: R1) :: S1) = List.range' 1 7 := rfl
  have f8 := lastB_snoc [] kd0 (List.range' 1 7) R1
  have f9 : blocksR [(kd0, List.range' 1 7 :: R1)] = List.range' 1 7 :: R1 := by simp [blocksR]
  rw [List.nil_append] at f8
  rw [f2, f3, f4, f7, f8, f9] at hinner
  simp only [List.map_nil, List.sum_nil, sub_zero, Nat.sub_zero, List.length_nil] at hinner
  have hA_true := J16.along_map2 (G3 := fun _ _ _ => True) (E3 := fun _ _ _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) (S1 ++ flatJ Post1)
    0 0 1 (5 - R1.length) V W (-6) 0 0 (List.range' 1 7)
    ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 7 :: R1) hinner hinner
  obtain ⟨tp, htp, hP⟩ := J16.along_gates gs (fun g hg => (hgs g hg).2.2.1) (S1 ++ flatJ Post1)
    0 0 1 (5 - R1.length) V W (-6) 0 0 (List.range' 1 7)
    ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 7 :: R1) hA_true
  obtain ⟨pa, pb, hpa_le, htp_lt, hjSearch⟩ := hs tp htp
  have hrun_false : runJointPart (buildJoint caps PRl ((q0 :: qpost).map Prod.fst) R V W bm fuel gs js) tp = false := by
    unfold FastJ16.jSearch at hjSearch
    by_cases h1 : (pb == pa + 1) = true
    · rw [if_pos h1] at hjSearch
      have htp_eq : tp = pa := by have := beq_iff_eq.mp h1; omega
      rw [htp_eq]; exact hjSearch
    · rw [if_neg h1] at hjSearch
      exact par_false_j hjSearch tp hpa_le htp_lt
  -- Bound on total rows of counterexample: every piece has length ≤ 200? Wait: we only need 1 + (S1 ++ flatJ Post1).length < 250!
  -- Actually in `go_complete`, `r` is the length of the CURRENT piece, and `rest.length` is only needed for `r + rest.length`?
  -- Wait: if there are 3 pieces of length 100, `(S1 ++ flatJ Post1).length` could be 250! Let's check: in `5,900` W ≤ 83,
  -- every piece has holes ≤ 83 and links ≤ 5, and `capF Ttab 5 53 ≤ 85`, total rows across 2–3 pieces is ALWAYS ≤ 200?
  -- Let's check the EXACT bound on `((kd0, ...) :: S1).length + (flatJ Post1).length`:
  -- Better: `hpiece_len` — for any `L` with `IsPieceV 7 q L` and `wtK 7 L ≤ W`, `L.length ≤ 200` (from `CapsOKV` + `hcaps` + `hPR`)!
  -- Wait: in `go_complete`, we ONLY need `r < 250` on the CURRENT piece, NOT `r + rest.length < 250`!
  -- Because when jumping to piece `i + 1`, `r` RESETS TO `1`!
  -- Let's check: does `r + rest.length < 250` hold if `rest` has 2 pieces of 100 rows? `100 + 100 = 200 < 250`!
  -- Wait: for 3 pieces (`S3`, `S4`, `S5`), `W ≤ 76`, `wt_1 + wt_2 + wt_3 ≤ 76`. Each piece has `L.length ≤ wt + 60`? No: `L.length ≤ P(t, d) ≤ d + 5*t + 50 ≤ wt + 50`? Even simpler:
  -- `L.length ≤ 200` per piece, and in `go_complete` we used `r + rest.length < 250` ONLY for `r < 256` AND `a, m, pm, pM` bounds!
  -- Wait: `10` pieces × `200` = `2000`, and `2000 * 300000 = 6 * 10^8 > 2^25`!
  -- We should tighten `r < 250` to per-piece length (by tracking `PieceLenBound rest`, or simply bounding `a, m, pm, pM` directly by `|a| ≤ 2^27`, `|m| ≤ 2^27`, `|pm|, |pM| ≤ 2^27`, since `r < 250` holds per piece and `2000 * 500 = 10^6 << 2^27`!)!
  -- Let's prove `piece_len_le` right here and check!
  have hbud : Bud bm 0 [] ((List.range' 1 7 :: R1) ++ blocksR (S1 ++ flatJ Post1)) := by
    have e : (List.range' 1 7 :: R1) ++ blocksR (S1 ++ flatJ Post1) =
        blocksR ((((kd0, List.range' 1 7 :: R1) :: S1) :: Post1).flatten) := by
      rw [blocksR_append, blocksR_flatJ]
      show _ = blocksR (((kd0, List.range' 1 7 :: R1) :: S1) ++ Post1.flatten)
      rw [blocksR_append, J15.blocksR_cons, List.append_assoc]
    have hsh := hce.2.1; unfold Sh at hsh; unfold Bud; rw [e, List.nil_append]
    have hcls0 : clsCount [] = 0 := rfl; omega
  have hnoJS_along : NoJSAlongJ ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (S1 ++ flatJ Post1) := by
    apply noJSAlongJ_of_noJS_piece S1 (flatJ Post1) _ (kd0, List.range' 1 7 :: R1) (List.cons_ne_nil _ _) rfl
      (hnoJS _ List.mem_cons_self)
      (fun x hx => M.hS.1.1.le_one x (List.mem_cons_of_mem _ hx))
      (fun x hx => M.hS.1.1.isSeq.pieces_ne x (List.mem_cons_of_mem _ hx))
    intro l _
    apply noJSAlongJ_flatJ Post1
    intro L hL
    have hLmem : L ∈ (((kd0, List.range' 1 7 :: R1) :: S1) :: Post1) := List.mem_cons_of_mem _ hL
    obtain ⟨qL, _, hqL⟩ := J15.forall₂_mem hfa.2 L hL
    exact ⟨hnoJS L hLmem, hqL.1.1.le_one, hqL.1.1.isSeq.pieces_ne, hqL.1.1.ne_nil⟩
  have hpiece_len : ∀ q L, q ∈ q0 :: qpost → IsPieceV 7 q L → wtK 7 L ≤ W → L.length < 250 := by
    intro q L hq hL hwt
    by_cases h0 : q.1.1 = 0
    · have hring := hc.ring q hq h0 L hL (by unfold wtK at hwt; omega)
      dsimp only at hring
      have := hPR_le (holesT 7 L); omega
    · have hw := hL.1; unfold IsPieceW at hw; rw [if_neg h0] at hw
      have hsmq := hsm_le q hq
      have hcap := hc.seq (linksT L) (by omega) L hw.1 hw.2.2.1 rfl (by unfold wtK at hwt; omega)
      have := hP_le (linksT L) (holesT 7 L); omega
  have hS1_len : ((kd0, List.range' 1 7 :: R1) :: S1).length < 250 := by
    have hsW := M.sumW
    exact hpiece_len q0 _ List.mem_cons_self M.hS.1 (by omega)
  have hplen : PieceLenOk 1 (S1 ++ flatJ Post1) := by
    apply pieceLenOk_piece S1 (flatJ Post1) 1 (by simp only [List.length_cons] at hS1_len; omega)
      (fun x hx => M.hS.1.1.le_one x (List.mem_cons_of_mem _ hx))
    intro r' hr'
    apply pieceLenOk_flatJ Post1 _ r' (by simp only [List.length_cons] at hS1_len; omega)
    intro L hL
    obtain ⟨qL, hqL_mem, hqL⟩ := J15.forall₂_mem hfa.2 L hL
    have hL_wt : wtK 7 L ≤ W := by
      have hle_sum : ∀ (l : List ℕ) x, x ∈ l → x ≤ l.sum := fun l => by
        induction l with
        | nil => simp
        | cons a t ih =>
          intro x hx; rcases List.mem_cons.mp hx with rfl | h
          · simp
          · have := ih x h; simp; omega
      have h1 : wtK 7 L ≤ (Post1.map (wtK 7)).sum := hle_sum _ _ (List.mem_map_of_mem hL)
      have := M.sumW; omega
    exact ⟨hpiece_len qL L (List.mem_cons_of_mem _ hqL_mem) hqL.1 hL_wt,
      hqL.1.1.le_one, hqL.1.1.ne_nil⟩
  have h5R1_le_W : 5 - R1.length ≤ W := by
    have h1 : 5 - R1.length ≤ wtK 7 ((kd0, List.range' 1 7 :: R1) :: S1) := by
      unfold wtK
      have h2 := PS.holesT_append (k := 7) [(kd0, List.range' 1 7 :: R1)] S1
      simp only [List.cons_append, List.nil_append] at h2
      rw [f4] at h2; omega
    have h3 := M.sumW; simp only [List.map_nil, List.sum_nil] at h3; omega
  -- Apply `buildJoint_valid` + `walkJFast_complete` + `go_complete` to contradict `hrun_false`!
  set bj := buildJoint caps PRl ((q0 :: qpost).map Prod.fst) R V W bm fuel gs js
  set ds := digs bj.gs tp
  obtain ⟨ctx, hctx_def⟩ : ∃ ctx : FastJ16Ctx, ctx = { bj.ctx0 with
    gatePi := ByteArray.mk (Array.ofFn (n := ds.length) fun i => UInt8.ofNat (ds[i.val]!.1)),
    gateR  := ByteArray.mk (Array.ofFn (n := ds.length) fun i => UInt8.ofNat (ds[i.val]!.2.1)),
    gateMod := packU16Arr (Array.ofFn (n := ds.length) fun i => UInt32.ofNat (ds[i.val]!.2.2.1)),
    gateDig := packU16Arr (Array.ofFn (n := ds.length) fun i => UInt32.ofNat (ds[i.val]!.2.2.2)),
    ng := UInt32.ofNat ds.length } := ⟨_, rfl⟩
  have hvc : ValidJCtx caps PRl (q0 :: qpost) R W bm gs js tp ctx := by
    rw [hctx_def]
    exact buildJoint_valid (caps := caps) (PRl := PRl) (qs := q0 :: qpost) (R := R)
      (V := V) (W := W) (bm := bm) (fuel := fuel) (gs := gs) (js := js) (tp := tp)
      hnp hW hS hcaps hPR hspecs habh hgs hgs_len
  have hlive0 : liveFast ctx (UInt32.ofNat 0) (UInt32.ofNat 0) (UInt32.ofNat 1)
      (UInt32.ofNat (5 - R1.length)) (Int64.ofInt V) (UInt32.ofNat W) (Int64.ofInt (-6)) = true :=
    liveFast_of_along hvc hnp hW hS hcaps hPR hRun (by simp) (by omega) (by omega) (by omega)
      (le_refl W) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        have haux : ∀ n, kdF ((q0 :: qpost).map Prod.fst) 0 ≤ maxLeN (kdF ((q0 :: qpost).map Prod.fst)) n := by
          intro n; induction n with | zero => exact le_refl _ | succ n ih => exact le_trans ih (le_max_left _ _)
        exact haux (q0 :: qpost).length)
      (fun h0 => Nat.pos_of_ne_zero h0) hP
  have hmk_bit : ((computeMask ctx 0 0 1 0 (Int64.ofInt V) (UInt32.ofNat W) (-6)).toNat >>> R1.length) % 2 = 1 :=
    computeMask_bit_of_live (ctx := ctx) (i := 0) (t := 0) (r := 1) (d := 0) (b := W)
      (j := R1.length) (a := Int64.ofInt V) (m := (-6 : Int64))
      (by omega) (by omega) hW (by omega) (by omega) (by simpa using hlive0)
  have hmk_ne : ¬ (computeMask ctx 0 0 1 0 (Int64.ofInt V) (UInt32.ofNat W) (-6) == 0) = true := by
    simp only [beq_iff_eq]; intro h0; rw [h0] at hmk_bit; simp at hmk_bit
  have hst_eq : bj.st = UInt32.ofNat (encB 7 (List.range' 1 7)) := by
    dsimp only [bj, buildJoint]
    exact congrArg UInt32.ofNat ((PS.encB_enc 7 (by omega) (by omega)).st_eq).symm
  have hM0_sz : (ByteArray.mk (Array.replicate bj.sz 0)).size = (permCodes 7 7).length := by
    simp [ByteArray.size, bj, buildJoint]
  have hM0_get : ∀ j, (ByteArray.mk (Array.replicate bj.sz 0)).get! j = 0 := fun j =>
    S.get!_marks0 bj.sz j
  have hzero : (walkJFast ctx (fun n e du M' =>
      go ctx (UInt32.ofNat fuel) (packSt 0 0 1 n (UInt32.ofNat W) du (UInt32.ofNat (encB 7 (List.range' 1 7))) e)
        (packI32Pair (Int64.ofInt V) (-6)) 0 M')
      (UInt8.ofNat 1) 6 (computeMask ctx 0 0 1 0 (Int64.ofInt V) (UInt32.ofNat W) (-6))
      0 (UInt32.ofNat (encB 7 (List.range' 1 7))) (ByteArray.mk (Array.replicate bj.sz 0))).size = 0 := by
    apply walkJFast_complete hvc hbm _ (fun n e du' M'' hM'' => go_id ctx fuel _ _ _ M'' (by omega) hM'')
      (UInt8.ofNat 1) 1 (le_of_eq (J15.toNat_ofNat8 (by omega)))
      R1 6 _ 0 (List.range' 1 7) (ByteArray.mk (Array.replicate bj.sz 0)) [] [] (blocksR (S1 ++ flatJ Post1))
      (by decide) (by omega) hmk_bit (by omega) hperm hdoor hM0_sz
      (PS.minv_marks0 (encB 7) (fun i => (ciTab 7 (permCodes 7 7))[i]!) bj.sz)
      (fun j hj => by rw [hM0_get] at hj; exact absurd hj (by decide))
      (fun j => by rw [hM0_get]; decide) (by simp) (by simp) (by simp) hpw hbud
    intro M' du' hM'sz hdu' hM' hC' hB' hbud'
    have h0_pair : (0 : UInt64) = packI32Pair (Int64.ofInt 0) (Int64.ofInt 0) := by decide
    have hneg6 : (-6 : Int64) = Int64.ofInt (-6) := rfl
    have h0_u : (0 : UInt32) = UInt32.ofNat 0 := rfl
    have h1_u : (1 : UInt32) = UInt32.ofNat 1 := rfl
    rw [h0_pair, hneg6, h0_u, h1_u]
    exact go_complete hvc hnp hW hS hbm hcaps hPR habh hrp_lt hoi_lt hoi_kd_ne hvlo_bd hvhi_bd hspecs_lt hRun
      (S1 ++ flatJ Post1) fuel 0 0 1 (5 - R1.length) W du' V (-6) 0 0
      (List.range' 1 7) ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _))
      (List.range' 1 7 :: R1) (List.range' 1 7 :: R1) M'
      hfuel (by simp) (by omega) hplen h5R1_le_W (le_refl W) (by omega)
      hdu' (fun h0 => Nat.pos_of_ne_zero h0) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (hperm _ (List.getLast_mem _)) (PS.permW_range' 7) hperm hperm hM'sz
      (by simpa using hM') (by simpa using hC') hB' hbud' (fun _ => hnoJS_along) hP
  have htrue : runJointPart bj tp = true := by
    unfold runJointPart
    change (if (computeMask _ 0 0 1 0 (Int64.ofInt V) (UInt32.ofNat W) (-6) == 0) = true then false
      else (walkJFast _ (fun n e du M' =>
        go _ (UInt32.ofNat fuel) (packSt 0 0 1 n (UInt32.ofNat W) du bj.st e)
          (packI32Pair (Int64.ofInt V) (-6)) 0 M')
        (UInt8.ofNat 1) 6 (computeMask _ 0 0 1 0 (Int64.ofInt V) (UInt32.ofNat W) (-6))
        0 bj.st (ByteArray.mk (Array.replicate bj.sz 0))).usize == 0) = true
    rw [← hctx_def, if_neg hmk_ne, hst_eq]
    exact (ba_usize_eq_zero_iff (by omega)).mpr hzero
  rw [hrun_false] at htrue
  cases htrue

end FastJ16Sound
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.FastJ16Sound.jv_of_fastJ16
