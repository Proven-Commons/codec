/-
  The Luhn check digit (ISO/IEC 7812-1, Annex B; US patent 2,950,048).

  Counting from the right, starting with the check digit, every second
  digit is doubled, and 9 is taken off a doubled value above 9. A number
  is valid when the sum is a multiple of 10. Digits are numbers 0 to 9,
  most significant first.
-/

namespace Codec.Luhn

/-- A digit's share of the sum: as it is, or doubled with 9 taken off a
    result above 9. -/
def weigh (double : Bool) (d : Nat) : Nat :=
  if double then (if 2 * d > 9 then 2 * d - 9 else 2 * d) else d

/-- The sum of digits given right to left, the first not doubled. -/
def sumFromRight : Bool → List Nat → Nat
  | _, [] => 0
  | double, d :: rest => weigh double d + sumFromRight (!double) rest

/-- The Luhn sum of a number. -/
def sum (ds : List Nat) : Nat := sumFromRight false ds.reverse

/-- Every digit is 0 to 9 and the Luhn sum is a multiple of 10. -/
def valid (ds : List Nat) : Bool :=
  ds.all (· ≤ 9) && sum ds % 10 == 0

/-- The digit to put after a payload so that the whole is valid. -/
def checkDigit (ds : List Nat) : Nat :=
  (10 - sum (ds ++ [0]) % 10) % 10

end Codec.Luhn
