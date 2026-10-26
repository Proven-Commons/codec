/-
  Proofs of the Base32 round trip.

  The statement proved here is the Base32 version of the round trip
  statements in `Spec.lean` for the other codecs. A matching statement
  for Base32 still has to be added to `Spec.lean` by a reviewer, so
  this file is a draft that builds on its own.

  The helper lemmas live in `Codec.Proofs.Base32`.
-/

import Codec
import Spec.Defs

open Codec

namespace Codec.Proofs.Base32

set_option maxRecDepth 10000 in
theorem value_tbl : ∀ n : Fin 32, Base32.value (Base32.char n.val) = some n.val := by
  decide +kernel

theorem value_char {n : Nat} (h : n < 32) : Base32.value (Base32.char n) = some n :=
  value_tbl ⟨n, h⟩

theorem char_ne_pad {n : Nat} (h : n < 32) : Base32.char n ≠ '=' := by
  intro e
  have hv := value_char h
  have hpad : Base32.value '=' = none := by decide
  rw [e, hpad] at hv
  cases hv

theorem toNat_toUInt8 {k : Nat} (h : k < 256) : k.toUInt8.toNat = k := by
  simp; omega

end Codec.Proofs.Base32

open Codec.Proofs.Base32

/-- Decoding gives back what was encoded. -/
theorem Spec.base32_decode_encode (bs : List UInt8) :
    Base32.decode (Base32.encode bs) = some bs := by
  induction bs using Base32.encode.induct with
  | case1 a b c d e rest ih =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have hd := d.toNat_lt
    have he := e.toNat_lt
    rw [Base32.encode.eq_1,
      Base32.decode.eq_6 _ _ _ _ _ _ _ _ _
        (fun h _ _ _ _ _ _ => char_ne_pad (by omega) h)
        (fun h _ _ _ _ => char_ne_pad (by omega) h)
        (fun h _ _ _ => char_ne_pad (by omega) h)
        (fun h _ => char_ne_pad (by omega) h),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega), value_char (by omega), ih]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case2 a b c d =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    have hd := d.toNat_lt
    rw [Base32.encode.eq_2,
      Base32.decode.eq_5 _ _ _ _ _ _ _
        (fun h _ _ _ _ => char_ne_pad (by omega) h)
        (fun h _ _ => char_ne_pad (by omega) h)
        (fun h _ => char_ne_pad (by omega) h),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case3 a b c =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    rw [Base32.encode.eq_3,
      Base32.decode.eq_4 _ _ _ _ _
        (fun h _ _ => char_ne_pad (by omega) h)
        (fun h => char_ne_pad (by omega) h),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega), value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case4 a b =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    rw [Base32.encode.eq_4,
      Base32.decode.eq_3 _ _ _ _
        (fun h _ => char_ne_pad (by omega) h),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      rw [toNat_toUInt8 (by omega)] <;> omega
  | case5 a =>
    have ha := a.toNat_lt
    rw [Base32.encode.eq_5, Base32.decode.eq_2, value_char (by omega),
      value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp; rw [toNat_toUInt8 (by omega)]; omega
  | case6 => rfl

/-- The test vectors of RFC 4648, section 10. -/
theorem Spec.base32_rfc4648_vectors :
    Base32.encode (Spec.ascii "") = "".toList ∧
    Base32.encode (Spec.ascii "f") = "MY======".toList ∧
    Base32.encode (Spec.ascii "fo") = "MZXQ====".toList ∧
    Base32.encode (Spec.ascii "foo") = "MZXW6===".toList ∧
    Base32.encode (Spec.ascii "foob") = "MZXW6YQ=".toList ∧
    Base32.encode (Spec.ascii "fooba") = "MZXW6YTB".toList ∧
    Base32.encode (Spec.ascii "foobar") = "MZXW6YTBOI======".toList := by
  decide +kernel
