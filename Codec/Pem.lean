/-
  PEM, the textual encoding of RFC 7468, in its strict form (Figure 3):

    -----BEGIN label-----
    the base 64 of the data, in lines of 64 characters, the last at most 64
    -----END label-----

  `encode` writes each line ending in LF, and fails on a label that the
  `label` rule of section 3 does not allow. `decode` reads exactly one
  message in this form, with each line ending in LF, CR, or CR LF. It
  fails on anything else: a different label on the END line, blanks,
  headers, text before or after the message, a short line before the
  last, and base 64 that `Base64.decode` refuses. Empty data has no line
  of base 64.
-/

import Codec.Base64

namespace Codec.Pem

/-- `labelchar`: a printable US-ASCII character other than `-`. -/
def isLabelChar (c : Char) : Bool :=
  let n := c.toNat
  (0x21 ≤ n && n ≤ 0x2C) || (0x2E ≤ n && n ≤ 0x7E)

/-- After the first character of a label: label characters, each of
    which may follow one `-` or space. -/
def labelRest : List Char → Bool
  | [] => true
  | c :: rest =>
    if isLabelChar c then labelRest rest
    else if c = '-' ∨ c = ' ' then
      match rest with
      | d :: rest' => isLabelChar d && labelRest rest'
      | [] => false
    else false

/-- A label: empty, or a label character and then `labelRest`. -/
def validLabel : List Char → Bool
  | [] => true
  | c :: rest => isLabelChar c && labelRest rest

/-- Cut text into lines of 64 characters, the last one at most 64. `fuel`
    equal to the text's length is enough. -/
def lines64 : Nat → List Char → List (List Char)
  | _, [] => []
  | 0, _ :: _ => []
  | fuel + 1, cs => cs.take 64 :: lines64 fuel (cs.drop 64)

def beginLine (label : List Char) : List Char := "-----BEGIN ".toList ++ label ++ "-----".toList

def endLine (label : List Char) : List Char := "-----END ".toList ++ label ++ "-----".toList

/-- The lines of a message: BEGIN, the base 64, END. -/
def lines (label : List Char) (data : List UInt8) : List (List Char) :=
  let b64 := Base64.encode data
  beginLine label :: lines64 b64.length b64 ++ [endLine label]

/-- Encode data under a label, each line ending in LF. -/
def encode (label : List Char) (data : List UInt8) : Option (List Char) :=
  if validLabel label then some ((lines label data).flatMap (· ++ ['\n'])) else none

/-- The first line of `text` and the text after its line end (LF, CR,
    or CR LF), or `none` when no line end follows. -/
def takeLine : List Char → Option (List Char × List Char)
  | [] => none
  | '\r' :: '\n' :: rest => some ([], rest)
  | '\r' :: rest => some ([], rest)
  | '\n' :: rest => some ([], rest)
  | c :: rest => (takeLine rest).map fun (l, r) => (c :: l, r)

/-- Split text into lines, each of which must end in a line end. `fuel`
    equal to the text's length is enough. -/
def splitLines : Nat → List Char → Option (List (List Char))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, text => do
    let (l, rest) ← takeLine text
    let ls ← splitLines fuel rest
    pure (l :: ls)

/-- The label of a BEGIN line, or of an END line. -/
def labelOf (pre : List Char) (line : List Char) : Option (List Char) :=
  if pre.isPrefixOf line ∧ "-----".toList.isSuffixOf line ∧ pre.length + 5 ≤ line.length then
    some ((line.drop pre.length).take (line.length - pre.length - 5))
  else none

/-- Decode one message in the strict form: its label and its data. -/
def decode (text : List Char) : Option (List Char × List UInt8) := do
  let ls ← splitLines text.length text
  match ls with
  | first :: rest =>
    match rest.getLast? with
    | some last =>
      let body := rest.dropLast
      let label ← labelOf "-----BEGIN ".toList first
      let label' ← labelOf "-----END ".toList last
      let data ← Base64.decode body.flatten
      if label = label' ∧ validLabel label ∧ body = lines64 body.flatten.length body.flatten then
        some (label, data)
      else none
    | none => none
  | [] => none

end Codec.Pem
