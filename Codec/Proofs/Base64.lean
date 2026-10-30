/-
  Proofs of the Base64 statements in `Codec/Spec.lean`, under the same names.
-/

import Codec
import Codec.Spec.Defs

open Codec

namespace Codec.Proofs.Base64

theorem charLe (a c : Char) : a ≤ c ↔ a.toNat ≤ c.toNat := by
  simp [Char.le_def, UInt32.le_iff_toNat_le]

set_option maxRecDepth 10000 in
theorem char_tbl : ∀ n : Fin 64, Base64.char n.val = Codec.Spec.base64Char n.val := by decide +kernel
set_option maxRecDepth 10000 in
theorem value_tbl : ∀ n : Fin 64, Base64.value (Base64.char n.val) = some n.val := by
  decide +kernel

theorem char_eq {n : Nat} (h : n < 64) : Base64.char n = Codec.Spec.base64Char n :=
  char_tbl ⟨n, h⟩

theorem value_char {n : Nat} (h : n < 64) : Base64.value (Base64.char n) = some n :=
  value_tbl ⟨n, h⟩

theorem char_ne_pad {n : Nat} (h : n < 64) : Base64.char n ≠ '=' := by
  intro e
  have := value_char h
  have hv : Base64.value '=' = none := by decide
  rw [e, hv] at this
  cases this

set_option maxRecDepth 10000 in
theorem upper_tbl : ∀ k : Fin 26, (Base64.char k.val).toNat = k.val + 65 := by decide +kernel
set_option maxRecDepth 10000 in
theorem lower_tbl : ∀ k : Fin 26, (Base64.char (k.val + 26)).toNat = k.val + 97 := by decide +kernel
set_option maxRecDepth 10000 in
theorem digit_tbl : ∀ k : Fin 10, (Base64.char (k.val + 52)).toNat = k.val + 48 := by decide +kernel
theorem char62 : Base64.char 62 = '+' := by decide +kernel
theorem char63 : Base64.char 63 = '/' := by decide +kernel

theorem value_some {c : Char} {v : Nat} (h : Base64.value c = some v) :
    v < 64 ∧ Base64.char v = c := by
  unfold Base64.value at h
  simp only [charLe] at h
  have hA : 'A'.toNat = 65 := rfl
  have hZ : 'Z'.toNat = 90 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hz : 'z'.toNat = 122 := rfl
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  rw [hA, hZ, ha, hz, h0, h9] at h
  split at h
  · rename_i hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have := upper_tbl ⟨c.toNat - 65, by omega⟩
    simp only at this
    rw [this]; omega
  split at h
  · rename_i _ hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have := lower_tbl ⟨c.toNat - 97, by omega⟩
    simp only at this
    have e : c.toNat - 97 + 26 = c.toNat - 71 := by omega
    rw [e] at this
    rw [this]; omega
  split at h
  · rename_i _ _ hc
    cases h
    refine ⟨by omega, ?_⟩
    apply Char.toNat_inj.mp
    have := digit_tbl ⟨c.toNat - 48, by omega⟩
    simp only at this
    have e : c.toNat - 48 + 52 = c.toNat + 4 := by omega
    rw [e] at this
    rw [this]; omega
  split at h
  · rename_i hc
    cases h; subst hc; exact ⟨by omega, char62⟩
  split at h
  · rename_i hc
    cases h; subst hc; exact ⟨by omega, char63⟩
  · cases h

theorem toNat_toUInt8 {k : Nat} (h : k < 256) : k.toUInt8.toNat = k := by
  simp; omega

end Codec.Proofs.Base64

open Codec.Proofs.Base64

theorem Codec.Spec.base64_encode_nil : Base64.encode [] = [] := by
  simp [Base64.encode]

/-- Three bytes, the first in the high bits, form one group. -/
theorem Codec.Spec.base64_encode_three (a b c : UInt8) (rest : List UInt8) :
    Base64.encode (a :: b :: c :: rest) =
      Codec.Spec.base64Group (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) ++
        Base64.encode rest := by
  rw [Base64.encode.eq_1]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  simp only [Codec.Spec.base64Group, List.cons_append, List.nil_append]
  have e1 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) / 2 ^ 18 % 64 =
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 := by omega
  have e2 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) / 2 ^ 12 % 64 =
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 := by omega
  have e3 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) / 2 ^ 6 % 64 =
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 := by omega
  have e4 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) % 64 =
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 := by omega
  rw [e1, e2, e3, e4, char_eq (by omega), char_eq (by omega), char_eq (by omega),
    char_eq (by omega)]

/-- Two final bytes: zero bits fill the group, which is cut to three
    characters and padded with one `=`. -/
theorem Codec.Spec.base64_encode_two (a b : UInt8) :
    Base64.encode [a, b] =
      (Codec.Spec.base64Group (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8)).take 3 ++ ['='] := by
  rw [Base64.encode.eq_2]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [Codec.Spec.base64Group, List.take, List.cons_append, List.nil_append]
  have e1 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 18 % 64 =
      (a.toNat * 65536 + b.toNat * 256) / 262144 := by omega
  have e2 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 12 % 64 =
      (a.toNat * 65536 + b.toNat * 256) / 4096 % 64 := by omega
  have e3 : (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8) / 2 ^ 6 % 64 =
      (a.toNat * 65536 + b.toNat * 256) / 64 % 64 := by omega
  rw [e1, e2, e3, char_eq (by omega), char_eq (by omega), char_eq (by omega)]

/-- One final byte: the group is cut to two characters and padded with
    `==`. -/
theorem Codec.Spec.base64_encode_one (a : UInt8) :
    Base64.encode [a] = (Codec.Spec.base64Group (a.toNat * 2 ^ 16)).take 2 ++ ['=', '='] := by
  rw [Base64.encode.eq_3]
  have ha := a.toNat_lt
  simp only [Codec.Spec.base64Group, List.take, List.cons_append, List.nil_append]
  have e1 : (a.toNat * 2 ^ 16) / 2 ^ 18 % 64 = (a.toNat * 65536) / 262144 := by omega
  have e2 : (a.toNat * 2 ^ 16) / 2 ^ 12 % 64 = (a.toNat * 65536) / 4096 % 64 := by omega
  rw [e1, e2, char_eq (by omega), char_eq (by omega)]

/-- Decoding gives back what was encoded. -/
theorem Codec.Spec.base64_decode_encode (bs : List UInt8) :
    Base64.decode (Base64.encode bs) = some bs := by
  induction bs using Base64.encode.induct with
  | case1 a b c rest ih =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    rw [Base64.encode.eq_1,
      Base64.decode.eq_4 _ _ _ _ _ (fun _ h _ => char_ne_pad (by omega) h)
        (fun h _ => char_ne_pad (by omega) h),
      value_char (by omega), value_char (by omega), value_char (by omega),
      value_char (by omega), ih]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> rw [toNat_toUInt8 (by omega)] <;> omega
  | case2 a b =>
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    rw [Base64.encode.eq_2, Base64.decode.eq_3 _ _ _ (char_ne_pad (by omega)),
      value_char (by omega), value_char (by omega), value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> rw [toNat_toUInt8 (by omega)] <;> omega
  | case3 a =>
    have ha := a.toNat_lt
    rw [Base64.encode.eq_3, Base64.decode.eq_2, value_char (by omega), value_char (by omega)]
    simp only
    rw [ite_eq_left (by omega)]
    simp only [Option.some.injEq, List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp; rw [toNat_toUInt8 (by omega)]; omega
  | case4 => rfl

/-- Decoding is strict: whatever it accepts is exactly an encoding. -/
theorem Codec.Spec.base64_encode_decode (cs : List Char) (bs : List UInt8) :
    Base64.decode cs = some bs → Base64.encode bs = cs := by
  induction cs using Base64.decode.induct generalizing bs with
  | case1 =>
    intro h
    rw [Base64.decode.eq_1, Option.some.injEq] at h
    subst h; rfl
  | case2 c0 c1 v0 v1 h1 h0 hm =>
    intro h
    rw [Base64.decode.eq_2, h0, h1] at h
    simp only [ite_eq_left hm, Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    rw [Base64.encode.eq_3, toNat_toUInt8 (by omega)]
    have e1 : (v0 * 4 + v1 / 16) * 65536 / 262144 = v0 := by omega
    have e2 : (v0 * 4 + v1 / 16) * 65536 / 4096 % 64 = v1 := by omega
    rw [e1, e2, ch0, ch1]
  | case3 c0 c1 v0 v1 h1 h0 hm =>
    intro h
    rw [Base64.decode.eq_2, h0, h1] at h
    simp only [ite_eq_right hm] at h
    cases h
  | case4 c0 c1 hn =>
    intro h
    rw [Base64.decode.eq_2] at h
    split at h
    · exact (hn _ _ ‹_› ‹_›).elim
    · cases h
  | case5 c0 c1 c2 hne v0 v1 v2 h2 h1 h0 hm =>
    intro h
    rw [Base64.decode.eq_3 _ _ _ hne, h0, h1, h2] at h
    simp only [ite_eq_left hm, Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    obtain ⟨lt2, ch2⟩ := value_some h2
    rw [Base64.encode.eq_2, toNat_toUInt8 (by omega), toNat_toUInt8 (by omega)]
    have e1 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 262144 = v0 := by
      omega
    have e2 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 4096 % 64 = v1 := by
      omega
    have e3 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256) / 64 % 64 = v2 := by
      omega
    rw [e1, e2, e3, ch0, ch1, ch2]
  | case6 c0 c1 c2 hne v0 v1 v2 h2 h1 h0 hm =>
    intro h
    rw [Base64.decode.eq_3 _ _ _ hne, h0, h1, h2] at h
    simp only [ite_eq_right hm] at h
    cases h
  | case7 c0 c1 c2 hne hn =>
    intro h
    rw [Base64.decode.eq_3 _ _ _ hne] at h
    split at h
    · exact (hn _ _ _ ‹_› ‹_› ‹_›).elim
    · cases h
  | case8 c0 c1 c2 c3 rest hne1 hne2 v0 v1 v2 v3 tail hrest h3 h2 h1 h0 ih =>
    intro h
    rw [Base64.decode.eq_4 _ _ _ _ _ hne1 hne2, h0, h1, h2, h3, hrest] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨lt0, ch0⟩ := value_some h0
    obtain ⟨lt1, ch1⟩ := value_some h1
    obtain ⟨lt2, ch2⟩ := value_some h2
    obtain ⟨lt3, ch3⟩ := value_some h3
    rw [Base64.encode.eq_1, toNat_toUInt8 (by omega), toNat_toUInt8 (by omega),
      toNat_toUInt8 (by omega), ih tail hrest]
    have e1 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 262144 = v0 := by omega
    have e2 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 4096 % 64 = v1 := by omega
    have e3 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) / 64 % 64 = v2 := by omega
    have e4 : ((v0 * 4 + v1 / 16) * 65536 + (v1 % 16 * 16 + v2 / 4) * 256 +
        (v2 % 4 * 64 + v3)) % 64 = v3 := by omega
    rw [e1, e2, e3, e4, ch0, ch1, ch2, ch3]
  | case9 c0 c1 c2 c3 rest hne1 hne2 hn ih =>
    intro h
    rw [Base64.decode.eq_4 _ _ _ _ _ hne1 hne2] at h
    split at h
    · exact (hn _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›).elim
    · cases h
  | case10 t h0 h1 h2 h3 =>
    intro h
    rw [Base64.decode.eq_5 _ h0 h1 h2 h3] at h
    cases h

/-- The test vectors of RFC 4648, section 10. -/
theorem Codec.Spec.base64_rfc4648_vectors :
    Base64.encode (Codec.Spec.ascii "") = "".toList ∧
    Base64.encode (Codec.Spec.ascii "f") = "Zg==".toList ∧
    Base64.encode (Codec.Spec.ascii "fo") = "Zm8=".toList ∧
    Base64.encode (Codec.Spec.ascii "foo") = "Zm9v".toList ∧
    Base64.encode (Codec.Spec.ascii "foob") = "Zm9vYg==".toList ∧
    Base64.encode (Codec.Spec.ascii "fooba") = "Zm9vYmE=".toList ∧
    Base64.encode (Codec.Spec.ascii "foobar") = "Zm9vYmFy".toList := by
  decide +kernel
