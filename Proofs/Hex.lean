/-
  Proofs of the Hex statements in `Spec.lean`, under the same names.

  The helper lemmas live in `Codec.Proofs.Hex`. The facts about single
  characters are checked by `decide` over the ASCII range (code points
  below 128); above it, `Hex.value` gives `none` and `Spec.asciiLower`
  changes nothing.
-/

import Codec
import Spec.Defs

open Codec

namespace Codec.Proofs.Hex

/-- `Hex.digit` and `Spec.hexDigit` agree below 16 (they differ only in the
    default for out-of-range values). -/
theorem digit_eq_hexDigit : ∀ n : Fin 16, Hex.digit n.val = Spec.hexDigit n.val := by decide

theorem value_digit_fin : ∀ n : Fin 16, Hex.value (Hex.digit n.val) = some n.val := by decide

/-- Every ASCII character with a hex value lowercases to that value's digit. -/
theorem value_small : ∀ n : Fin 128,
    Hex.value (Char.ofNat n.val) = none ∨
    ∃ h : Fin 16, Hex.value (Char.ofNat n.val) = some h.val ∧
      Spec.asciiLower (Char.ofNat n.val) = Hex.digit h.val := by decide

/-- On ASCII characters, lowercasing does not change the hex value. -/
theorem value_lower_small : ∀ n : Fin 128,
    Hex.value (Spec.asciiLower (Char.ofNat n.val)) = Hex.value (Char.ofNat n.val) := by decide

theorem value_big (c : Char) (h : 128 ≤ c.toNat) : Hex.value c = none := by
  simp only [Hex.value, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]
  simp only [Char.reduceToNat]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · rfl

theorem lower_big (c : Char) (h : 128 ≤ c.toNat) : Spec.asciiLower c = c := by
  simp only [Spec.asciiLower, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]
  simp only [Char.reduceToNat]
  split
  · omega
  · rfl

theorem value_lower (c : Char) : Hex.value (Spec.asciiLower c) = Hex.value c := by
  by_cases h : c.toNat < 128
  · have := value_lower_small ⟨c.toNat, h⟩
    simpa only [Char.ofNat_toNat] using this
  · rw [lower_big c (by omega)]

theorem value_some (c : Char) (h : Nat) (hv : Hex.value c = some h) :
    h < 16 ∧ Spec.asciiLower c = Hex.digit h := by
  by_cases hc : c.toNat < 128
  · rcases value_small ⟨c.toNat, hc⟩ with h1 | ⟨k, h1, h2⟩
    · simp only [Char.ofNat_toNat] at h1
      rw [hv] at h1
      cases h1
    · simp only [Char.ofNat_toNat] at h1 h2
      rw [hv] at h1
      cases h1
      exact ⟨k.isLt, h2⟩
  · rw [value_big c (by omega)] at hv
    cases hv

theorem digit_hexDigit (n : Nat) (h : n < 16) : Hex.digit n = Spec.hexDigit n :=
  digit_eq_hexDigit ⟨n, h⟩

theorem value_digit (n : Nat) (h : n < 16) : Hex.value (Hex.digit n) = some n :=
  value_digit_fin ⟨n, h⟩

theorem byte_split (b : UInt8) : (b.toNat / 16 * 16 + b.toNat % 16).toUInt8 = b := by
  have : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
  rw [this]
  simp

theorem byte_toNat (h l : Nat) (hh : h < 16) (hl : l < 16) :
    (h * 16 + l).toUInt8.toNat = h * 16 + l := by
  simp
  omega

end Codec.Proofs.Hex

open Codec.Proofs.Hex

theorem Spec.hex_encode_nil : Hex.encode [] = [] := rfl

/-- Each byte is two digits, high half first. -/
theorem Spec.hex_encode_cons (b : UInt8) (bs : List UInt8) :
    Hex.encode (b :: bs) =
      Spec.hexDigit (b.toNat / 16) :: Spec.hexDigit (b.toNat % 16) :: Hex.encode bs := by
  have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
  have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [Hex.encode, digit_hexDigit _ h1, digit_hexDigit _ h2]

/-- Decoding gives back what was encoded. -/
theorem Spec.hex_decode_encode (bs : List UInt8) :
    Hex.decode (Hex.encode bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
    have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    rw [Hex.encode, Hex.decode, value_digit _ h1, value_digit _ h2, ih]
    simp only [byte_split]

/-- Decoding accepts any mix of upper and lower case. -/
theorem Spec.hex_decode_any_case (cs : List Char) (bs : List UInt8) :
    cs.map Spec.asciiLower = Hex.encode bs → Hex.decode cs = some bs := by
  induction bs generalizing cs with
  | nil =>
    intro h
    rw [Hex.encode, List.map_eq_nil_iff] at h
    subst h
    rfl
  | cons b bs ih =>
    intro h
    match cs, h with
    | c1 :: c2 :: rest, h =>
      rw [Hex.encode, List.map_cons, List.map_cons] at h
      injection h with e1 h
      injection h with e2 h
      have h1 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
      have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      have v1 : Hex.value c1 = some (b.toNat / 16) := by
        rw [← value_lower, e1, value_digit _ h1]
      have v2 : Hex.value c2 = some (b.toNat % 16) := by
        rw [← value_lower, e2, value_digit _ h2]
      rw [Hex.decode, v1, v2, ih rest h]
      simp only [byte_split]
    | [c], h =>
      rw [Hex.encode, List.map_cons, List.map_nil] at h
      injection h with _ h
      cases h

/-- Decoding accepts nothing else: whatever it accepts is an encoding,
    up to case. -/
theorem Spec.hex_encode_decode (cs : List Char) (bs : List UInt8) :
    Hex.decode cs = some bs → Hex.encode bs = cs.map Spec.asciiLower := by
  induction cs using Hex.decode.induct generalizing bs with
  | case1 =>
    intro h
    rw [Hex.decode] at h
    cases h
    rfl
  | case2 c =>
    intro h
    rw [Hex.decode] at h
    cases h
  | case3 hi lo rest h l tail hrest hl hh ih =>
    intro hd
    rw [Hex.decode, hh, hl, hrest] at hd
    injection hd with hd
    subst hd
    obtain ⟨h16, eh⟩ := value_some hi h hh
    obtain ⟨l16, el⟩ := value_some lo l hl
    have e1 : (h * 16 + l).toUInt8.toNat / 16 = h := by
      rw [byte_toNat h l h16 l16]; omega
    have e2 : (h * 16 + l).toUInt8.toNat % 16 = l := by
      rw [byte_toNat h l h16 l16]; omega
    rw [Hex.encode, e1, e2, ih tail hrest, List.map_cons, List.map_cons, eh, el]
  | case4 hi lo rest hne ih =>
    intro hd
    rw [Hex.decode] at hd
    split at hd
    next h l tail hh hl hr => exact (hne h l tail hh hl hr).elim
    next => cases hd

/-- The test vectors of RFC 4648, section 10. The RFC writes them in
    uppercase: encoding gives them in lowercase, and decoding reads them
    as the RFC writes them. -/
theorem Spec.hex_rfc4648_vectors :
    Hex.encode (Spec.ascii "") = "".toList ∧
    Hex.encode (Spec.ascii "f") = "66".toList ∧
    Hex.encode (Spec.ascii "fo") = "666f".toList ∧
    Hex.encode (Spec.ascii "foo") = "666f6f".toList ∧
    Hex.encode (Spec.ascii "foob") = "666f6f62".toList ∧
    Hex.encode (Spec.ascii "fooba") = "666f6f6261".toList ∧
    Hex.encode (Spec.ascii "foobar") = "666f6f626172".toList ∧
    Hex.decode "".toList = some (Spec.ascii "") ∧
    Hex.decode "66".toList = some (Spec.ascii "f") ∧
    Hex.decode "666F".toList = some (Spec.ascii "fo") ∧
    Hex.decode "666F6F".toList = some (Spec.ascii "foo") ∧
    Hex.decode "666F6F62".toList = some (Spec.ascii "foob") ∧
    Hex.decode "666F6F6261".toList = some (Spec.ascii "fooba") ∧
    Hex.decode "666F6F626172".toList = some (Spec.ascii "foobar") := by
  decide +kernel
