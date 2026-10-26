/-
  IBAN check digits (ISO 13616), by ISO 7064 MOD 97-10.

  An IBAN in its electronic form is a country code of two letters, two
  check digits, and a BBAN of 1 to 30 letters and digits, letters in
  upper case. It passes the check when, with the first four characters
  moved to the end and each letter written as 10 (A) to 35 (Z), the
  digits read as a number are 1 more than a multiple of 97.
-/

namespace Codec.Iban

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- A digit as its value, a letter as 10 to 35. -/
def value (c : Char) : Nat :=
  if isDigit c then c.toNat - 48 else c.toNat - 55

/-- The remainder mod 97 of the number the characters write, each digit
    as one decimal digit and each letter as two, computed one character
    at a time so that the numbers stay small. -/
def mod97 (cs : List Char) : Nat :=
  cs.foldl (fun r c => if isDigit c then (r * 10 + value c) % 97 else (r * 100 + value c) % 97) 0

/-- Two letters, two digits, then 1 to 30 letters or digits. -/
def wellShaped (s : List Char) : Bool :=
  match s with
  | c0 :: c1 :: k0 :: k1 :: bban =>
    isUpper c0 && isUpper c1 && isDigit k0 && isDigit k1 &&
      1 ≤ bban.length && bban.length ≤ 30 && bban.all (fun c => isDigit c || isUpper c)
  | _ => false

/-- The IBAN passes the check. -/
def valid (s : List Char) : Bool :=
  wellShaped s && mod97 (s.drop 4 ++ s.take 4) == 1

/-- The check digits, 02 to 98, for a country code and a BBAN: 98 less
    the remainder of the BBAN, the country code and `00`. `none` when the
    country code is not two letters or the BBAN has the wrong shape. -/
def checkDigits (country bban : List Char) : Option (List Char) :=
  if country.length = 2 ∧ wellShaped (country ++ ['0', '0'] ++ bban) then
    let c := 98 - mod97 (bban ++ country ++ ['0', '0'])
    some [Char.ofNat (48 + c / 10), Char.ofNat (48 + c % 10)]
  else none

end Codec.Iban
