/-
  Proofs of the Crc32 statements in `Spec.lean`, under the same names.

  The main fact is that the table-driven `Crc32.update` agrees with the
  bit-at-a-time `Spec.crcByte`. `step` is linear over xor, so `step8` is
  too; eight steps of a value whose low byte is zero just shift it right
  by eight; hence `step8 x = step8 (x &&& 0xFF) ^^^ (x >>> 8)`, and
  `table[i]! = step8 i` for `i < 256`.
-/

import Codec
import Spec.Defs

open Codec

namespace Codec.Proofs.Crc32
open Codec.Crc32

theorem and_one_cases (a : UInt32) : a &&& 1 = 0 ∨ a &&& 1 = 1 := by
  have h : (a &&& 1).toNat = a.toNat % 2 := by simp
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h' | h'
  · left; apply UInt32.toNat_inj.1; simp [h, h']
  · right; apply UInt32.toNat_inj.1; simp [h, h']

theorem xor_and_one (a b : UInt32) : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := by
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> simp

theorem xor_cancel (x y p : UInt32) : x ^^^ y = x ^^^ p ^^^ (y ^^^ p) := by
  rw [UInt32.xor_assoc, ← UInt32.xor_assoc p, UInt32.xor_comm p y, UInt32.xor_assoc y,
    UInt32.xor_self, UInt32.xor_zero]

theorem step_xor (a b : UInt32) : step (a ^^^ b) = step a ^^^ step b := by
  unfold step
  rw [xor_and_one, UInt32.shiftRight_xor]
  rcases and_one_cases a with ha | ha <;> rcases and_one_cases b with hb | hb <;>
    simp only [ha, hb] <;> simp
  · rw [UInt32.xor_assoc]
  · rw [UInt32.xor_assoc, UInt32.xor_comm (b >>> 1), ← UInt32.xor_assoc]
  · exact xor_cancel _ _ _

theorem step8_xor (a b : UInt32) : step8 (a ^^^ b) = step8 a ^^^ step8 b := by
  simp only [step8, step_xor]

theorem toNat_shr1 (y : UInt32) : (y >>> 1).toNat = y.toNat / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem step_of_even (y : UInt32) (h : y.toNat % 2 = 0) : step y = y >>> 1 := by
  unfold step
  have : y &&& 1 ≠ 1 := by
    intro h1
    have := congrArg UInt32.toNat h1
    simp at this
    omega
  simp [this]

theorem step8_high (y : UInt32) (h : y.toNat % 256 = 0) : step8 y = y >>> 8 := by
  have e1 := toNat_shr1 y
  have e2 := toNat_shr1 (y >>> 1)
  have e3 := toNat_shr1 (y >>> 1 >>> 1)
  have e4 := toNat_shr1 (y >>> 1 >>> 1 >>> 1)
  have e5 := toNat_shr1 (y >>> 1 >>> 1 >>> 1 >>> 1)
  have e6 := toNat_shr1 (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
  have e7 := toNat_shr1 (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
  have e8 := toNat_shr1 (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
  unfold step8
  rw [step_of_even y (by omega), step_of_even (y >>> 1) (by omega),
    step_of_even (y >>> 1 >>> 1) (by omega), step_of_even (y >>> 1 >>> 1 >>> 1) (by omega),
    step_of_even (y >>> 1 >>> 1 >>> 1 >>> 1) (by omega),
    step_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) (by omega),
    step_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) (by omega),
    step_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) (by omega)]
  apply UInt32.toNat_inj.1
  have e9 : (y >>> 8).toNat = y.toNat / 256 := by simp [Nat.shiftRight_eq_div_pow]
  omega


theorem and_xor_distrib (x a b : UInt32) : (x &&& a) ^^^ (x &&& b) = x &&& (a ^^^ b) := by
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.toBitVec.getLsbD i <;> cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> simp

theorem and_255_toNat (x : UInt32) : (x &&& 255).toNat = x.toNat % 256 := by
  simp only [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8

theorem split_byte (x : UInt32) : x = (x &&& 0xFF) ^^^ (x &&& 0xFFFFFF00) := by
  rw [and_xor_distrib]
  have : (0xFF ^^^ 0xFFFFFF00 : UInt32) = 0xFFFFFFFF := by decide
  rw [this]
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_and]
  have := x.toNat_lt
  have h2 : (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 := by decide
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt this).symm

theorem high_shr (x : UInt32) : (x &&& 0xFFFFFF00) >>> 8 = x >>> 8 := by
  rw [UInt32.shiftRight_and]
  have : (0xFFFFFF00 : UInt32) >>> 8 = 0xFFFFFF := by decide
  rw [this]
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_and]
  have h2 : (0xFFFFFF : UInt32).toNat = 2 ^ 24 - 1 := by decide
  rw [h2, Nat.and_two_pow_sub_one_eq_mod]
  have := x.toNat_lt
  have e : (x >>> 8).toNat = x.toNat / 256 := by simp [Nat.shiftRight_eq_div_pow]
  rw [e]
  apply Nat.mod_eq_of_lt
  have : x.toNat < 2 ^ 32 := this
  omega

theorem high_low (x : UInt32) : (x &&& 0xFFFFFF00).toNat % 256 = 0 := by
  rw [← and_255_toNat, UInt32.and_assoc]
  have : (0xFFFFFF00 &&& 255 : UInt32) = 0 := by decide
  rw [this, UInt32.and_zero]
  rfl

theorem step8_split (x : UInt32) : step8 x = step8 (x &&& 0xFF) ^^^ (x >>> 8) := by
  conv => lhs; rw [split_byte x]
  rw [step8_xor, step8_high _ (high_low x), high_shr]

theorem table_get (i : Nat) (h : i < 256) : table[i]! = step8 i.toUInt32 := by
  simp [table, h]


theorem crcBit_eq : Spec.crcBit = step := by
  funext c
  unfold Spec.crcBit step
  have h1 : c / (2 : UInt32) = c >>> (1 : UInt32) := by
    apply UInt32.toNat_inj.1
    simp [Nat.shiftRight_eq_div_pow]
  have h2 : (c % (2 : UInt32) = 1) ↔ (c &&& (1 : UInt32) = 1) := by
    constructor
    · intro h; apply UInt32.toNat_inj.1; have := congrArg UInt32.toNat h; simp at this ⊢; omega
    · intro h; apply UInt32.toNat_inj.1; have := congrArg UInt32.toNat h; simp at this ⊢; omega
  rw [h1]
  by_cases h : c &&& 1 = 1
  · have h' : c % (2 : UInt32) = 1 := h2.2 h
    simp only [h, h', ite_true]
  · have h' : ¬ (c % (2 : UInt32) = 1) := fun h' => h (h2.1 h')
    simp only [h, h', ite_false]

theorem crcByte_eq (c : UInt32) (b : UInt8) : Spec.crcByte c b = step8 (c ^^^ b.toUInt32) := by
  unfold Spec.crcByte
  rw [crcBit_eq]
  rfl

theorem update_eq (c : UInt32) (b : UInt8) : update c b = step8 (c ^^^ b.toUInt32) := by
  unfold update
  have hlt : ((c ^^^ b.toUInt32) &&& 0xFF).toNat < 256 := by
    rw [and_255_toNat]; exact Nat.mod_lt _ (by decide)
  rw [table_get _ hlt]
  have e1 : ((c ^^^ b.toUInt32) &&& 0xFF).toNat.toUInt32 = (c ^^^ b.toUInt32) &&& 0xFF := by
    simp
  have e2 : c >>> 8 = (c ^^^ b.toUInt32) >>> 8 := by
    rw [UInt32.shiftRight_xor]
    have : b.toUInt32 >>> 8 = 0 := by
      apply UInt32.toNat_inj.1
      have := b.toNat_lt
      simp [Nat.shiftRight_eq_div_pow]
      omega
    rw [this, UInt32.xor_zero]
  rw [e1, e2, ← step8_split]

theorem le32_eq (x : UInt32) : le32 x = Spec.le32 x := by
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  unfold le32 Spec.le32
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.1 <;>
    simp [Nat.shiftRight_eq_div_pow] <;> omega

theorem le32_length (x : UInt32) : (le32 x).length = 4 := rfl

end Codec.Proofs.Crc32

open Codec.Proofs.Crc32 in
/-- The table-driven code computes the CRC-32 defined above. -/
theorem Spec.crc32_eq (bs : List UInt8) : Crc32.crc32 bs = Spec.crc32 bs := by
  unfold Crc32.crc32 Spec.crc32
  have : Crc32.update = Spec.crcByte := by
    funext c b; rw [update_eq, crcByte_eq]
  rw [this]

/-- The code gives the standard check value. -/
theorem Spec.crc32_check : Crc32.crc32 (Spec.ascii "123456789") = 0xCBF43926 := by
  rw [Spec.crc32_eq]
  decide +kernel

open Codec.Proofs.Crc32 in
/-- A frame is the message followed by its CRC-32, low byte first. -/
theorem Spec.frame_layout (bs : List UInt8) :
    Crc32.frame bs = bs ++ Spec.le32 (Spec.crc32 bs) := by
  rw [Crc32.frame, Spec.crc32_eq, le32_eq]

open Codec.Proofs.Crc32 in
/-- Unframing a frame gives back the message. -/
theorem Spec.unframe_frame (bs : List UInt8) :
    Crc32.unframe (Crc32.frame bs) = some bs := by
  unfold Crc32.unframe Crc32.frame
  simp [le32_length]

/-- Unframing accepts nothing else: whatever it accepts is a frame. -/
theorem Spec.frame_unframe (fr bs : List UInt8) :
    Crc32.unframe fr = some bs → Crc32.frame bs = fr := by
  unfold Crc32.unframe
  intro h
  split at h
  · exact absurd h (by simp)
  · simp only at h
    split at h
    · rename_i heq
      cases h
      unfold Crc32.frame
      rw [← heq, List.take_append_drop]
    · exact absurd h (by simp)
