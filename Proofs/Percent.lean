/-
  Proofs of the percent-encoding statements in `Spec.lean`, under the
  same names. The helper lemmas live in `Codec.Proofs.Percent`.
-/

import Codec
import Spec.Defs
import Proofs.Hex

open Codec

namespace Codec.Proofs.Percent

open Codec.Proofs.Hex

/-- `Percent.unreserved` picks out exactly the characters of
    `Spec.unreservedChars`. -/
theorem unreserved_fin : ∀ b : Fin 256,
    Percent.unreserved b.val.toUInt8 = true ↔ Char.ofNat b.val ∈ Spec.unreservedChars := by
  decide +kernel

/-- An unreserved byte is an ASCII character other than `%`, whose code is the byte. -/
theorem unreserved_char_fin : ∀ b : Fin 256, Percent.unreserved b.val.toUInt8 = true →
    Char.ofNat b.val ≠ '%' ∧ (Char.ofNat b.val).toNat < 0x80 ∧
      (Char.ofNat b.val).toNat.toUInt8 = b.val.toUInt8 := by
  decide +kernel

theorem upper_fin : ∀ n : Fin 16, Percent.upper n.val = Spec.upperHexDigits.getD n.val '?' := by
  decide

theorem lower_upper_fin : ∀ n : Fin 16, Spec.asciiLower (Percent.upper n.val) = Spec.hexDigit n.val := by
  decide

theorem unreserved_iff (b : UInt8) :
    Percent.unreserved b = true ↔ Char.ofNat b.toNat ∈ Spec.unreservedChars := by
  have := unreserved_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using this

theorem unreserved_char (b : UInt8) (h : Percent.unreserved b = true) :
    Char.ofNat b.toNat ≠ '%' ∧ (Char.ofNat b.toNat).toNat < 0x80 ∧
      (Char.ofNat b.toNat).toNat.toUInt8 = b := by
  have := unreserved_char_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [Nat.toUInt8_eq, UInt8.ofNat_toNat] at this
  simpa using this h

theorem upper_eq (n : Nat) (h : n < 16) : Percent.upper n = Spec.upperHexDigits.getD n '?' :=
  upper_fin ⟨n, h⟩

theorem lower_upper (n : Nat) (h : n < 16) : Spec.asciiLower (Percent.upper n) = Spec.hexDigit n :=
  lower_upper_fin ⟨n, h⟩

theorem encode_cons (b : UInt8) (bs : List UInt8) :
    Percent.encode (b :: bs) = Spec.pctByte b ++ Percent.encode bs := by
  have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
  have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [Percent.encode, Spec.pctByte]
  by_cases hu : Percent.unreserved b = true
  · rw [ite_eq_left hu, ite_eq_left ((unreserved_iff b).mp hu)]
    rfl
  · rw [ite_eq_right hu, ite_eq_right (fun h => hu ((unreserved_iff b).mpr h)), upper_eq _ h1, upper_eq _ h2]
    rfl

theorem decode_reads (cs : List Char) (bs : List UInt8) :
    Percent.decode cs = some bs → Spec.PctReads cs bs := by
  induction cs using Percent.decode.induct generalizing bs with
  | case1 =>
    intro hd
    rw [Percent.decode.eq_1] at hd
    cases hd
    exact Spec.PctReads.nil
  | case2 hi lo rest h l tail hrest hl hh ih =>
    intro hd
    rw [Percent.decode.eq_2, hh, hl, hrest] at hd
    injection hd with hd
    subst hd
    obtain ⟨h16, eh⟩ := value_some hi h hh
    obtain ⟨l16, el⟩ := value_some lo l hl
    have e1 : (h * 16 + l).toUInt8.toNat / 16 = h := by
      rw [byte_toNat h l h16 l16]; omega
    have e2 : (h * 16 + l).toUInt8.toNat % 16 = l := by
      rw [byte_toNat h l h16 l16]; omega
    refine Spec.PctReads.escape ?_ ?_ (ih tail hrest)
    · rw [e1, eh, digit_hexDigit h h16]
    · rw [e2, el, digit_hexDigit l l16]
  | case3 hi lo rest hne ih =>
    intro hd
    rw [Percent.decode.eq_2] at hd
    split at hd
    next h l tail hh hl hr => exact (hne h l tail hh hl hr).elim
    next => cases hd
  | case4 tail hne =>
    intro hd
    rw [Percent.decode.eq_3 tail hne] at hd
    cases hd
  | case5 c rest hne1 hne2 hlt ih =>
    intro hd
    rw [Percent.decode.eq_4 c rest hne1 hne2, ite_eq_left hlt] at hd
    cases hr : Percent.decode rest with
    | none => rw [hr] at hd; cases hd
    | some tail =>
      rw [hr] at hd
      injection hd with hd
      subst hd
      exact Spec.PctReads.char hne2 hlt (ih tail hr)
  | case6 c rest hne1 hne2 hlt =>
    intro hd
    rw [Percent.decode.eq_4 c rest hne1 hne2, ite_eq_right hlt] at hd
    cases hd

theorem reads_decode (cs : List Char) (bs : List UInt8) (h : Spec.PctReads cs bs) :
    Percent.decode cs = some bs := by
  induction h with
  | nil => rw [Percent.decode.eq_1]
  | @escape hi lo b rest bs ehi elo _ ih =>
    have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
    have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have v1 : Hex.value hi = some (b.toNat / 16) := by
      rw [← value_lower, ehi, ← digit_hexDigit _ h1, value_digit _ h1]
    have v2 : Hex.value lo = some (b.toNat % 16) := by
      rw [← value_lower, elo, ← digit_hexDigit _ h2, value_digit _ h2]
    rw [Percent.decode.eq_2, v1, v2, ih]
    simp only [byte_split]
  | @char c rest bs hne hlt _ ih =>
    rw [Percent.decode.eq_4 c rest (fun _ _ _ h _ => hne h) hne, ite_eq_left hlt, ih]
    rfl

theorem encode_reads (bs : List UInt8) : Spec.PctReads (Percent.encode bs) bs := by
  induction bs with
  | nil => exact Spec.PctReads.nil
  | cons b bs ih =>
    rw [Percent.encode]
    by_cases hu : Percent.unreserved b = true
    · rw [ite_eq_left hu]
      obtain ⟨hne, hlt, hb⟩ := unreserved_char b hu
      have := Spec.PctReads.char hne hlt ih
      rwa [hb] at this
    · rw [ite_eq_right hu]
      have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
      have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      exact Spec.PctReads.escape (lower_upper _ h1) (lower_upper _ h2) ih

end Codec.Proofs.Percent

open Codec.Proofs.Percent

theorem Spec.percent_encode_eq (bs : List UInt8) :
    Percent.encode bs = Spec.pctEncode bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [encode_cons, ih, Spec.pctEncode, Spec.pctEncode, List.map_cons, List.flatten_cons]

theorem Spec.percent_decode_iff (cs : List Char) (bs : List UInt8) :
    Percent.decode cs = some bs ↔ Spec.PctReads cs bs :=
  ⟨decode_reads cs bs, reads_decode cs bs⟩

theorem Spec.percent_decode_encode (bs : List UInt8) :
    Percent.decode (Percent.encode bs) = some bs :=
  reads_decode _ _ (encode_reads bs)

theorem Spec.percent_vectors :
    Percent.encode [0x20] = "%20".toList ∧
    Percent.encode (Spec.ascii "A") = "A".toList ∧
    Percent.encode [0xC3, 0x80] = "%C3%80".toList ∧
    Percent.encode [0xE3, 0x82, 0xA2] = "%E3%82%A2".toList ∧
    Percent.encode (Spec.ascii "-._~") = "-._~".toList ∧
    Percent.encode (Spec.ascii "Laguna Beach") = "Laguna%20Beach".toList ∧
    Percent.encode (Spec.ascii "%:/?#[]@!$&'()*+,;=") =
      "%25%3A%2F%3F%23%5B%5D%40%21%24%26%27%28%29%2A%2B%2C%3B%3D".toList ∧
    Percent.decode "%C3%80".toList = some [0xC3, 0x80] ∧
    Percent.decode "%e3%82%a2".toList = some [0xE3, 0x82, 0xA2] ∧
    Percent.decode "%7E".toList = some (Spec.ascii "~") ∧
    Percent.decode "%63/%7bfoo%7d".toList = some (Spec.ascii "c/{foo}") ∧
    Percent.decode "%3a".toList = some (Spec.ascii ":") ∧
    Percent.decode "%3A".toList = some (Spec.ascii ":") ∧
    Percent.decode "a+b c".toList = some (Spec.ascii "a+b c") ∧
    Percent.decode "%252E".toList = some (Spec.ascii "%2E") ∧
    Percent.decode "%".toList = none ∧
    Percent.decode "%2".toList = none ∧
    Percent.decode "%zz".toList = none ∧
    Percent.decode "%%41".toList = none ∧
    Percent.decode "café".toList = none := by
  decide
