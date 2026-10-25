/-
  Command line front end, used by the differential tests.

  Reads one request per line and prints one answer per line. Each
  request is an operation and its input as comma-separated decimal
  numbers: bytes, or for the decoders, character codes.

    hexenc 1,171,255      prints  01abff
    hexdec 48,49,97,66    prints  ok:1,171   (or none)
    b64enc 102,111        prints  Zm8=
    b64dec 90,103,61,61   prints  ok:102     (or none)
    b32enc 102,111        prints  MZXQ====
    b32dec 77,90,88,81,61,61,61,61   prints  ok:102,111     (or none)
    crc 49,50,51          prints  the CRC-32 as a decimal number
    frame 1,2             prints  the framed bytes
    unframe 1,2,3,4,5     prints  ok:... (or none)

  A request is an operation, then optionally one space and its numbers;
  with no numbers after the space, the input is empty. A malformed
  request prints `error`: any other line, an unknown operation, a number
  that is not plain decimal digits, a byte above 255, or a character
  code that is not a Unicode scalar value. A line may end in LF or
  CR LF; nothing else around a request is ignored.

  Every operation calls the proved function in `Codec/` directly. The
  parsing and printing here are covered by the tests, not by a proof.
-/

import Codec

open Codec

/-- A number in plain decimal digits. Longer numbers than any byte or
    character code are refused before they are converted, since that
    takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

def toBytes (ns : List Nat) : Option (List UInt8) :=
  ns.mapM fun n => if n < 256 then some n.toUInt8 else none

def toChars (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none

def showBytes (bs : List UInt8) : String :=
  ",".intercalate (bs.map fun b => toString b.toNat)

/-- The answer to one request, or `none` when the request is malformed. -/
def answer (op : String) (ns : List Nat) : Option String := do
  let result : Option (List UInt8) → String
    | some bs => "ok:" ++ showBytes bs
    | none => "none"
  match op with
  | "hexenc" => return String.ofList (Hex.encode (← toBytes ns))
  | "hexdec" => return result (Hex.decode (← toChars ns))
  | "b64enc" => return String.ofList (Base64.encode (← toBytes ns))
  | "b64dec" => return result (Base64.decode (← toChars ns))
  | "b32enc" => return String.ofList (Base32.encode (← toBytes ns))
  | "b32dec" => return result (Base32.decode (← toChars ns))
  | "crc" => return toString (Crc32.crc32 (← toBytes ns)).toNat
  | "frame" => return showBytes (Crc32.frame (← toBytes ns))
  | "unframe" => return result (Crc32.unframe (← toBytes ns))
  | _ => none

/-- The answer to one line: an operation, then optionally one space and
    its numbers. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op []
  | [op, arg] => numbers arg >>= answer op
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")
