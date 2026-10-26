/-
  Proofs of the Iban statements in `Spec.lean`, under the same names. The
  helper lemmas live in `Codec.Proofs.Iban`.
-/

import Codec
import Spec.Defs

open Codec

namespace Codec.Proofs.Iban

end Codec.Proofs.Iban

theorem Spec.iban_valid_iff (s : List Char) : Iban.valid s = true ↔ Spec.IbanValid s := sorry

theorem Spec.iban_checkDigits_iff (country bban ck : List Char) :
    Iban.checkDigits country bban = some ck ↔
      ck.length = 2 ∧ (∀ c ∈ ck, Spec.ibanDigit c) ∧
        2 ≤ Spec.ibanNumber ck ∧ Spec.ibanNumber ck ≤ 98 ∧
          Spec.IbanValid (country ++ ck ++ bban) := sorry

theorem Spec.iban_substitution (l r : List Char) (a b : Char)
    (h : Iban.valid (l ++ a :: r) = true) (hab : a ≠ b)
    (hkind : (Spec.ibanDigit a ∧ Spec.ibanDigit b) ∨ (Spec.ibanLetter a ∧ Spec.ibanLetter b)) :
    Iban.valid (l ++ b :: r) = false := sorry

theorem Spec.iban_adjacent_swap (l r : List Char) (a b : Char)
    (h : Iban.valid (l ++ a :: b :: r) = true) (hab : a ≠ b)
    (hkind : (Spec.ibanDigit a ∧ Spec.ibanDigit b) ∨ (Spec.ibanLetter a ∧ Spec.ibanLetter b)) :
    Iban.valid (l ++ b :: a :: r) = false := sorry

theorem Spec.iban_vectors :
    Iban.valid "GB29NWBK60161331926819".toList = true ∧
    Iban.valid "DE89370400440532013000".toList = true ∧
    Iban.valid "FR1420041010050500013M02606".toList = true ∧
    Iban.valid "NO9386011117947".toList = true ∧
    Iban.checkDigits "GB".toList "NWBK60161331926819".toList = some "29".toList ∧
    Iban.checkDigits "NO".toList "86011117947".toList = some "93".toList ∧
    Iban.valid "GB29NWBK60161331926818".toList = false ∧
    Iban.valid "gb29NWBK60161331926819".toList = false ∧
    Iban.valid "FR2130006000010001234B15697".toList = true ∧
    Iban.valid "FR21300060000100012341B5697".toList = true := by
  and_intros <;> decide +kernel
