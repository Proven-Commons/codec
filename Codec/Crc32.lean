/-
  CRC-32, the checksum of zip, gzip, and PNG, computed a byte at a time
  from a table. `frame` appends it to a message, as gzip does, and
  `unframe` checks and removes it.
-/

namespace Codec.Crc32

/-- One step of the shift register: shift toward the low end, and xor in
    the reflected polynomial 0xEDB88320 when a one bit falls out. -/
def step (c : UInt32) : UInt32 :=
  if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1

/-- Eight steps: one byte's worth. -/
def step8 (c : UInt32) : UInt32 :=
  step (step (step (step (step (step (step (step c)))))))

/-- `table[i]` is eight steps from `i`. -/
def table : Array UInt32 :=
  (Array.range 256).map fun i => step8 i.toUInt32

/-- Feed one byte into the register. -/
def update (c : UInt32) (b : UInt8) : UInt32 :=
  table[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)

/-- The CRC-32 of a message. -/
def crc32 (bs : List UInt8) : UInt32 :=
  bs.foldl update 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-- Four bytes, low byte first. -/
def le32 (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- A message followed by its CRC-32. -/
def frame (bs : List UInt8) : List UInt8 :=
  bs ++ le32 (crc32 bs)

/-- The message in a frame, if its last four bytes are its CRC-32. -/
def unframe (fr : List UInt8) : Option (List UInt8) :=
  if fr.length < 4 then none
  else
    let msg := fr.take (fr.length - 4)
    if fr.drop (fr.length - 4) = le32 (crc32 msg) then some msg else none

end Codec.Crc32
