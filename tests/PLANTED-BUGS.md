# Planted bugs

Written by `python3 tests/planted_bugs.py`. Each row is one small change to the
code, made in a copy. The tests ran on 30,000 inputs from their recorded seed
against the changed tool. A bug is caught when they report failures.

| Bug | File | Failures |
|-----|------|----------|
| m01_bytes_mod_512 | `Main.lean` | 7 |
| m02_underscores | `Main.lean` | 1 |
| m03_invalid_cp_to_fffd | `Main.lean` | 6 |
| m04_drop_last_number | `Main.lean` | 22414 |
| m05_trailing_comma | `Main.lean` | 1 |
| m06_case_insensitive_op | `Main.lean` | 2 |
| m07_tab_separator | `Main.lean` | 1 |
| m08_uint64_parser_nocap | `Main.lean` | 5 |
| m08b_uint64_parser_cap | `Main.lean` | 0, equivalent: The cap leaves at most seven digits after the leading zeros. So the value is below 10,000,000, and a UInt64 cannot overflow. |
| m09_cp_mod_256 | `Main.lean` | 796 |
| m10_cp_mod_65536 | `Main.lean` | 334 |
| m11a_cp_via_uint32_cap | `Main.lean` | 0, equivalent: The cap keeps every value below 10,000,000, which is below 2^32. So the trip through UInt32 changes nothing. |
| m11b_cp_via_uint32_nocap | `Main.lean` | 4 |
| m12_hexenc_unchecked | `Main.lean` | 3 |
| m13_b64enc_unchecked | `Main.lean` | 1 |
| m14_crc_unchecked | `Main.lean` | 1 |
| m15_frame_unchecked | `Main.lean` | 1 |
| m16_unframe_unchecked | `Main.lean` | 1 |
| m17_blank_line_ends_run | `Main.lean` | 29995 |
| m18_throw_on_malformed | `Main.lean` | 30006 |
| m19_chomp_all_trailing_crs | `Main.lean` | 1 |
| m20_chomp_any_trailing_ws | `Main.lean` | 5 |
| m20b_chomp_trailing_ctrl_ws | `Main.lean` | 4 |
| m20c_trim_both_ends | `Main.lean` | 8 |
| m21_chomp_strips_mid_cr | `Main.lean` | 4 |
| m22_cap_counts_leading_zeros | `Main.lean` | 3 |
| m22b_cap_32_chars_with_zeros | `Main.lean` | 1 |
| m23_cap_6 | `Main.lean` | 144 |
| m24_no_cap | `Main.lean` | 0, equivalent: Without the cap, a long number is converted, which only takes longer. It is above 255 and above 0x10FFFF, so the answer is still `error`. |
| m25_accept_surrogates | `Main.lean` | 4 |
| m26_accept_0x110000 | `Main.lean` | 1 |
| m27_accept_trailing_space | `Main.lean` | 3 |
| m28r_reject_empty_arg | `Main.lean` | 2401 |
| m29_swap_hexenc_b64enc | `Main.lean` | 3028 |
| m29b_swap_frame_unframe | `Main.lean` | 5130 |
| m30_hexenc_uppercase | `Main.lean` | 1390 |
| m31_trim_each_number | `Main.lean` | 4 |
| m32_crlf_output | `Main.lean` | 30006 |
| m33_cr_only_output | `Main.lean` | 30007 |
| m34_reject_nul_code_point | `Main.lean` | 188 |
| m34b_nul_as_invalid_sentinel | `Main.lean` | 188 |
| m35_no_eof_check | `Main.lean` | 3157781 |
| m36_no_arg_form_refused | `Main.lean` | 1 |
| m37_chars_below_256_only | `Main.lean` | 1065 |
| m38_strip_cr_before_lf | `Main.lean` | 3 |
| m39_showbytes_comma_space | `Main.lean` | 13076 |
| m40_swap_hexdec_b64dec | `Main.lean` | 5207 |
| m41_unchecked_chars_b64dec | `Main.lean` | 1 |
| m42_unchecked_chars_hexdec | `Main.lean` | 4 |
| m43_cr_as_separator | `Main.lean` | 1 |
| m44_parse_after_zero_strip | `Main.lean` | 2066 |
| m45_toInt_nonneg | `Main.lean` | 3 |
| m45b_toInt_nonneg_cap | `Main.lean` | 3 |
| m45c_minus_sign_then_nonneg | `Main.lean` | 2 |
| n01_chomp_cr_at_eof | `Main.lean` | 1 |
| n02_lfcr_leading_cr_dropped | `Main.lean` | 1 |
| n03_lfcr_lone_cr_at_eof_dropped | `Main.lean` | 1 |
| n04_chomp_nel_before_lf | `Main.lean` | 1 |
| n05_chomp_ls_ps_before_lf | `Main.lean` | 2 |
| n06_unicode_eol_at_eof | `Main.lean` | 1 |
| n07_ls_splits_requests | `Main.lean` | 26033 |
| n08_chomp_ff_fs_gs_rs_before_lf | `Main.lean` | 2 |
| n09_chomp_filter_all_lf | `Main.lean` | 0, equivalent: A line from getLine holds at most one LF, at its end. So removing every LF removes just that one. |
| n10_leading_bom_dropped | `Main.lean` | 2 |
| n11_chomp_drops_last_char_always | `Main.lean` | 3 |
| n12_eof_blank_fragment_dropped | `Main.lean` | 2 |
| n13_lone_comma_is_empty | `Main.lean` | 1 |
| n14_leading_empty_number_dropped | `Main.lean` | 1 |
| n15_two_trailing_spaces_empty | `Main.lean` | 1 |
| n16_comma_after_op_as_separator | `Main.lean` | 1 |
| n17_plus_on_first_number | `Main.lean` | 1 |
| n18_plus_each_cap_counts_sign | `Main.lean` | 2 |
| n19_signed_zero_any_position | `Main.lean` | 2 |
| n20_nfkc_digits_fullwidth_sub | `Main.lean` | 2 |
| n21_unicode_nd_digits | `Main.lean` | 2 |
| n22_no_digit_check_toNat | `Main.lean` | 1 |
| n23_cap_8 | `Main.lean` | 0, equivalent: A number with eight digits after its leading zeros is at least 10,000,000. That is above 255 and above 0x10FFFF, so the answer is still `error`. |
| n24_cap_ignores_all_zeros | `Main.lean` | 0, equivalent: A number this lets past the cap still has eight or more digits after its leading zeros. So it is at least 10,000,000, and the range checks still refuse it. |
| n25_cap_takewhile_zeros | `Main.lean` | 2 |
| n26_zero_refused | `Main.lean` | 2066 |
| n27_bytes_le_256 | `Main.lean` | 5 |
| n28_bytes_via_uint16 | `Main.lean` | 1 |
| n29_bytes_via_uint32 | `Main.lean` | 0, equivalent: The cap keeps every value below 10,000,000, which is below 2^32. So the value never wraps. |
| n30_cp_lt_10ffff | `Main.lean` | 7 |
| n31_cp_mask_21_bits | `Main.lean` | 1 |
| n32_cp_mask_24_bits | `Main.lean` | 0, equivalent: The cap keeps every value below 10,000,000, which is below 2^24. So the mask changes nothing. |
| n33_surrogate_D800_accepted | `Main.lean` | 2 |
| n34_surrogate_DFFF_accepted | `Main.lean` | 1 |
| n35_D7FF_refused | `Main.lean` | 6 |
| n36_E000_refused | `Main.lean` | 6 |
| n37_surrogate_pairs_combined | `Main.lean` | 1 |
| n38_c0_controls_refused | `Main.lean` | 175 |
| n39_noncharacters_refused | `Main.lean` | 13 |
| n40_no_lf_on_last_answer | `Main.lean` | 7 |
| n41_bom_before_output | `Main.lean` | 7 |
| n42_trailing_space_every_answer | `Main.lean` | 30006 |
| n43_trailing_space_on_error | `Main.lean` | 76 |
| n44_blank_line_after_last | `Main.lean` | 7 |
| n45_stderr_note | `Main.lean` | 0, equivalent: It only adds a note on stderr. The tool prints the same on stdout, and the tests and SPEC.md cover stdout only. |
| n46_exit_status_1 | `Main.lean` | 7 |
| n47_bom_on_error_lines | `Main.lean` | 76 |
| n48_minus_on_first_number | `Main.lean` | 1 |
| n49_bom_on_first_line_only | `Main.lean` | 1 |
| p01_lowercase_digits | `Codec/Percent.lean` | 1479 |
| p02_tilde_encoded | `Codec/Percent.lean` | 206 |
| p03_asterisk_kept | `Codec/Percent.lean` | 216 |
| p04_non_ascii_low_byte | `Codec/Percent.lean` | 499 |
| p05_bad_escape_passed_through | `Codec/Percent.lean` | 205 |
| p06_digits_low_half_first | `Codec/Percent.lean` | 5284 |
| p07_space_refused | `Codec/Percent.lean` | 84 |

## The changes

**m01_bytes_mod_512** in `Main.lean`:

```
-   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
+   ns.mapM fun n => if n < 512 then some n.toUInt8 else none
```

**m02_underscores** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all (fun c => c.isDigit || c = '_') || (ds.dropWhile (· = '0')).length > 7 then none
```

**m03_invalid_cp_to_fffd** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else some '\uFFFD'
```

**m04_drop_last_number** in `Main.lean`:

```
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+   if s.isEmpty then some [] else (s.splitOn ",").dropLast.mapM number
```

**m05_trailing_comma** in `Main.lean`:

```
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+   if s.isEmpty then some [] else (let ps := s.splitOn ","; if ps.length > 1 && ps.getLast? = some "" then ps.dropLast else ps).mapM number
```

**m06_case_insensitive_op** in `Main.lean`:

```
-   match op with
+   match op.toLower with
```

**m07_tab_separator** in `Main.lean`:

```
-   match line.splitOn " " with
+   match (line.map fun c => if c = '\t' then ' ' else c).splitOn " " with
```

**m08_uint64_parser_nocap** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   if ds.isEmpty || !ds.all Char.isDigit then none
+   else some (ds.foldl (fun (acc : UInt64) c => acc * 10 + (c.toNat - 48).toUInt64) 0).toNat
```

**m08b_uint64_parser_cap** in `Main.lean`:

```
-   else t.toNat?
+   else some (ds.foldl (fun (acc : UInt64) c => acc * 10 + (c.toNat - 48).toUInt64) 0).toNat
```

**m09_cp_mod_256** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar then some (Char.ofNat (n % 256)) else none
```

**m10_cp_mod_65536** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar then some (Char.ofNat (n % 65536)) else none
```

**m11a_cp_via_uint32_cap** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.toUInt32.toNat.isValidChar then some (Char.ofNat n.toUInt32.toNat) else none
```

**m11b_cp_via_uint32_nocap** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
- 
- /-- The comma-separated numbers in `s`. -/
- def numbers (s : String) : Option (List Nat) :=
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
- 
- def toBytes (ns : List Nat) : Option (List UInt8) :=
-   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
- 
- def toChars (ns : List Nat) : Option (List Char) :=
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   if ds.isEmpty || !ds.all Char.isDigit then none
+   else t.toNat?
+ 
+ /-- The comma-separated numbers in `s`. -/
+ def numbers (s : String) : Option (List Nat) :=
+   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+ 
+ def toBytes (ns : List Nat) : Option (List UInt8) :=
+   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
+ 
+ def toChars (ns : List Nat) : Option (List Char) :=
+   ns.mapM fun n => if n.toUInt32.toNat.isValidChar then some (Char.ofNat n.toUInt32.toNat) else none
```

**m12_hexenc_unchecked** in `Main.lean`:

```
-   | "hexenc" => return String.ofList (Hex.encode (← toBytes ns))
+   | "hexenc" => return String.ofList (Hex.encode (ns.map Nat.toUInt8))
```

**m13_b64enc_unchecked** in `Main.lean`:

```
-   | "b64enc" => return String.ofList (Base64.encode (← toBytes ns))
+   | "b64enc" => return String.ofList (Base64.encode (ns.map Nat.toUInt8))
```

**m14_crc_unchecked** in `Main.lean`:

```
-   | "crc" => return toString (Crc32.crc32 (← toBytes ns)).toNat
+   | "crc" => return toString (Crc32.crc32 (ns.map Nat.toUInt8)).toNat
```

**m15_frame_unchecked** in `Main.lean`:

```
-   | "frame" => return showBytes (Crc32.frame (← toBytes ns))
+   | "frame" => return showBytes (Crc32.frame (ns.map Nat.toUInt8))
```

**m16_unframe_unchecked** in `Main.lean`:

```
-   | "unframe" => return result (Crc32.unframe (← toBytes ns))
+   | "unframe" => return result (Crc32.unframe (ns.map Nat.toUInt8))
```

**m17_blank_line_ends_run** in `Main.lean`:

```
-     if line.isEmpty then break
+     if line.isEmpty || line == "\n" then break
```

**m18_throw_on_malformed** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     match request line with
+     | some s => stdout.putStrLn s
+     | none => throw (IO.userError "malformed request")
```

**m19_chomp_all_trailing_crs** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList ((cs.reverse.dropWhile (· = '\r')).reverse)
```

**m20_chomp_any_trailing_ws** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList ((cs.reverse.dropWhile Char.isWhitespace).reverse)
```

**m20b_chomp_trailing_ctrl_ws** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList ((cs.reverse.dropWhile (fun c => c = '\r' || c = '\t' || c = '\x0b' || c = '\x0c')).reverse)
```

**m20c_trim_both_ends** in `Main.lean`:

```
-     let line := chomp line
+     let line := (chomp line).trimAscii.toString
```

**m21_chomp_strips_mid_cr** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList (cs.filter (· ≠ '\r'))
```

**m22_cap_counts_leading_zeros** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || ds.length > 7 then none
```

**m22b_cap_32_chars_with_zeros** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || ds.length > 32 then none
```

**m23_cap_6** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 6 then none
```

**m24_no_cap** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit then none
```

**m25_accept_surrogates** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n < 0x110000 then some (Char.ofNat n) else none
```

**m26_accept_0x110000** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar || n = 0x110000 then some (Char.ofNat n) else none
```

**m27_accept_trailing_space** in `Main.lean`:

```
-   | [op, arg] => numbers arg >>= answer op
+   | [op, arg] | [op, arg, ""] => numbers arg >>= answer op
```

**m28r_reject_empty_arg** in `Main.lean`:

```
-   | [op, arg] => numbers arg >>= answer op
+   | [op, arg] => if arg.isEmpty then none else numbers arg >>= answer op
```

**m29_swap_hexenc_b64enc** in `Main.lean`:

```
-   | "hexenc" => return String.ofList (Hex.encode (← toBytes ns))
-   | "hexdec" => return result (Hex.decode (← toChars ns))
-   | "b64enc" => return String.ofList (Base64.encode (← toBytes ns))
+   | "b64enc" => return String.ofList (Hex.encode (← toBytes ns))
+   | "hexdec" => return result (Hex.decode (← toChars ns))
+   | "hexenc" => return String.ofList (Base64.encode (← toBytes ns))
```

**m29b_swap_frame_unframe** in `Main.lean`:

```
-   | "frame" => return showBytes (Crc32.frame (← toBytes ns))
-   | "unframe" => return result (Crc32.unframe (← toBytes ns))
+   | "unframe" => return showBytes (Crc32.frame (← toBytes ns))
+   | "frame" => return result (Crc32.unframe (← toBytes ns))
```

**m30_hexenc_uppercase** in `Main.lean`:

```
-   | "hexenc" => return String.ofList (Hex.encode (← toBytes ns))
+   | "hexenc" => return (String.ofList (Hex.encode (← toBytes ns))).toUpper
```

**m31_trim_each_number** in `Main.lean`:

```
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+   if s.isEmpty then some [] else (s.splitOn ",").mapM fun t => number t.trimAscii.toString
```

**m32_crlf_output** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStr ((request line).getD "error" ++ "\r\n")
```

**m33_cr_only_output** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStr ((request line).getD "error" ++ "\r")
```

**m34_reject_nul_code_point** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar && n ≠ 0 then some (Char.ofNat n) else none
```

**m34b_nul_as_invalid_sentinel** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => let c := Char.ofNat n; if c ≠ '\x00' then some c else none
```

**m35_no_eof_check** in `Main.lean`:

```
-     if line.isEmpty then break
+     if line.length > 1000000000 then break
```

**m36_no_arg_form_refused** in `Main.lean`:

```
-   | [op] => answer op []
+   | [op] => none
```

**m37_chars_below_256_only** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar && n < 256 then some (Char.ofNat n) else none
```

**m38_strip_cr_before_lf** in `Main.lean`:

```
-   if cs.getLast? = some '\n' then
-     let cs := cs.dropLast
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
-   else line
+   let cs := if cs.getLast? = some '\r' then cs.dropLast else cs
+   String.ofList (if cs.getLast? = some '\n' then cs.dropLast else cs)
```

**m39_showbytes_comma_space** in `Main.lean`:

```
-   ",".intercalate (bs.map fun b => toString b.toNat)
+   ", ".intercalate (bs.map fun b => toString b.toNat)
```

**m40_swap_hexdec_b64dec** in `Main.lean`:

```
-   | "hexdec" => return result (Hex.decode (← toChars ns))
-   | "b64enc" => return String.ofList (Base64.encode (← toBytes ns))
-   | "b64dec" => return result (Base64.decode (← toChars ns))
+   | "b64dec" => return result (Hex.decode (← toChars ns))
+   | "b64enc" => return String.ofList (Base64.encode (← toBytes ns))
+   | "hexdec" => return result (Base64.decode (← toChars ns))
```

**m41_unchecked_chars_b64dec** in `Main.lean`:

```
-   | "b64dec" => return result (Base64.decode (← toChars ns))
+   | "b64dec" => return result (Base64.decode (ns.map Char.ofNat))
```

**m42_unchecked_chars_hexdec** in `Main.lean`:

```
-   | "hexdec" => return result (Hex.decode (← toChars ns))
+   | "hexdec" => return result (Hex.decode (ns.map Char.ofNat))
```

**m43_cr_as_separator** in `Main.lean`:

```
-   match line.splitOn " " with
+   match (line.map fun c => if c = '\r' then ' ' else c).splitOn " " with
```

**m44_parse_after_zero_strip** in `Main.lean`:

```
-   else t.toNat?
+   else (String.ofList (ds.dropWhile (· = '0'))).toNat?
```

**m45_toInt_nonneg** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   match t.toInt? with
+   | some i => if i < 0 then none else some i.toNat
+   | none => none
```

**m45b_toInt_nonneg_cap** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   if ds.isEmpty || (ds.dropWhile (· = '0')).length > 7 then none
+   else match t.toInt? with
+   | some i => if i < 0 then none else some i.toNat
+   | none => none
```

**m45c_minus_sign_then_nonneg** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   let body := if ds.head? = some '-' then ds.tail else ds
+   if body.isEmpty || !body.all Char.isDigit || (body.dropWhile (· = '0')).length > 7 then none
+   else match t.toInt? with
+   | some i => if i < 0 then none else some i.toNat
+   | none => none
```

**n01_chomp_cr_at_eof** in `Main.lean`:

```
-   else line
+   else String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
```

**n02_lfcr_leading_cr_dropped** in `Main.lean`:

```
-   let cs := line.toList
+   let cs := line.toList
+   let cs := if cs.head? = some '\r' then cs.tail else cs
+   let line := String.ofList cs
```

**n03_lfcr_lone_cr_at_eof_dropped** in `Main.lean`:

```
-     if line.isEmpty then break
+     if line.isEmpty || line == "\r" then break
```

**n04_chomp_nel_before_lf** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList (if cs.getLast? = some '\r' || cs.getLast? = some '\u0085' then cs.dropLast else cs)
```

**n05_chomp_ls_ps_before_lf** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList (if cs.getLast? = some '\r' || cs.getLast? = some '\u2028' || cs.getLast? = some '\u2029' then cs.dropLast else cs)
```

**n06_unicode_eol_at_eof** in `Main.lean`:

```
-   else line
+   else String.ofList (if cs.getLast? = some '\u0085' || cs.getLast? = some '\u2028' || cs.getLast? = some '\u2029' then cs.dropLast else cs)
```

**n07_ls_splits_requests** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     for part in line.splitOn "\u2028" do
+       stdout.putStrLn ((request part).getD "error")
```

**n08_chomp_ff_fs_gs_rs_before_lf** in `Main.lean`:

```
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
+     String.ofList (if cs.getLast? = some '\r' || cs.getLast? = some '\x0c' || cs.getLast? = some '\x1c' || cs.getLast? = some '\x1d' || cs.getLast? = some '\x1e' then cs.dropLast else cs)
```

**n09_chomp_filter_all_lf** in `Main.lean`:

```
-     let cs := cs.dropLast
+     let cs := cs.filter (· ≠ '\n')
```

**n10_leading_bom_dropped** in `Main.lean`:

```
-   let cs := line.toList
+   let cs := line.toList
+   let cs := if cs.head? = some '\uFEFF' then cs.tail else cs
+   let line := String.ofList cs
```

**n11_chomp_drops_last_char_always** in `Main.lean`:

```
-   let cs := line.toList
-   if cs.getLast? = some '\n' then
-     let cs := cs.dropLast
-     String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
-   else line
+   let cs := line.toList.dropLast
+   String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
```

**n12_eof_blank_fragment_dropped** in `Main.lean`:

```
-     if line.isEmpty then break
+     if line.isEmpty || (!line.endsWith "\n" && line.all Char.isWhitespace) then break
```

**n13_lone_comma_is_empty** in `Main.lean`:

```
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+   if s.isEmpty || s = "," then some [] else (s.splitOn ",").mapM number
```

**n14_leading_empty_number_dropped** in `Main.lean`:

```
-   if s.isEmpty then some [] else (s.splitOn ",").mapM number
+   if s.isEmpty then some [] else (match s.splitOn "," with | "" :: rest@(_ :: _) => rest | ps => ps).mapM number
```

**n15_two_trailing_spaces_empty** in `Main.lean`:

```
-   | [op, arg] => numbers arg >>= answer op
+   | [op, arg] => numbers arg >>= answer op
+   | [op, "", ""] => answer op []
```

**n16_comma_after_op_as_separator** in `Main.lean`:

```
-   match line.splitOn " " with
+   match (match line.splitOn " " with | [w] => (match w.splitOn "," with | o :: r@(_ :: _) => [o, ",".intercalate r] | _ => [w]) | ps => ps) with
```

**n17_plus_on_first_number** in `Main.lean`:

```
-   | [op, arg] => numbers arg >>= answer op
+   | [op, arg] => numbers (if arg.startsWith "+" then String.ofList (arg.toList.drop 1) else arg) >>= answer op
```

**n18_plus_each_cap_counts_sign** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   let body := if ds.head? = some '+' then ds.tail else ds
+   if body.isEmpty || !body.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   else (String.ofList body).toNat?
```

**n19_signed_zero_any_position** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   let body := if ds.head? = some '-' || ds.head? = some '+' then ds.tail else ds
+   if body.isEmpty || !body.all Char.isDigit || (body.dropWhile (· = '0')).length > 7 then none
+   else if body.length < ds.length && !body.all (· = '0') then none
+   else (String.ofList body).toNat?
```

**n20_nfkc_digits_fullwidth_sub** in `Main.lean`:

```
-   let ds := t.toList
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   let ds := t.toList.map fun c =>
+     if false then c
+     else if 0xFF10 ≤ c.toNat && c.toNat ≤ 0xFF19 then Char.ofNat (c.toNat - 0xFF10 + 48)
+     else if 0x2080 ≤ c.toNat && c.toNat ≤ 0x2089 then Char.ofNat (c.toNat - 0x2080 + 48)
+     else c
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   else (String.ofList ds).toNat?
```

**n21_unicode_nd_digits** in `Main.lean`:

```
-   let ds := t.toList
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
-   else t.toNat?
+   let ds := t.toList.map fun c =>
+     if false then c
+     else if 0x660 ≤ c.toNat && c.toNat ≤ 0x669 then Char.ofNat (c.toNat - 0x660 + 48)
+     else if 0x6F0 ≤ c.toNat && c.toNat ≤ 0x6F9 then Char.ofNat (c.toNat - 0x6F0 + 48)
+     else if 0x966 ≤ c.toNat && c.toNat ≤ 0x96F then Char.ofNat (c.toNat - 0x966 + 48)
+     else if 0xFF10 ≤ c.toNat && c.toNat ≤ 0xFF19 then Char.ofNat (c.toNat - 0xFF10 + 48)
+     else c
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   else (String.ofList ds).toNat?
```

**n22_no_digit_check_toNat** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || (ds.dropWhile (· = '0')).length > 7 then none
```

**n23_cap_8** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 8 then none
```

**n24_cap_ignores_all_zeros** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.filter (· ≠ '0')).length > 7 then none
```

**n25_cap_takewhile_zeros** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || !ds.all Char.isDigit || (ds.takeWhile (· = '0')).length > 7 then none
```

**n26_zero_refused** in `Main.lean`:

```
-   if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
+   if ds.isEmpty || (ds.dropWhile (· = '0')).isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
```

**n27_bytes_le_256** in `Main.lean`:

```
-   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
+   ns.mapM fun n => if n ≤ 256 then some n.toUInt8 else none
```

**n28_bytes_via_uint16** in `Main.lean`:

```
-   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
+   ns.mapM fun n => if n.toUInt16.toNat < 256 then some n.toUInt8 else none
```

**n29_bytes_via_uint32** in `Main.lean`:

```
-   ns.mapM fun n => if n < 256 then some n.toUInt8 else none
+   ns.mapM fun n => if n.toUInt32.toNat < 256 then some n.toUInt8 else none
```

**n30_cp_lt_10ffff** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar && n < 0x10FFFF then some (Char.ofNat n) else none
```

**n31_cp_mask_21_bits** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => let m := n % 0x200000; if m.isValidChar then some (Char.ofNat m) else none
```

**n32_cp_mask_24_bits** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => let m := n % 0x1000000; if m.isValidChar then some (Char.ofNat m) else none
```

**n33_surrogate_D800_accepted** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n ≤ 0xD800 || (0xDFFF < n && n < 0x110000) then some (Char.ofNat n) else none
```

**n34_surrogate_DFFF_accepted** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n < 0xD800 || (0xDFFF ≤ n && n < 0x110000) then some (Char.ofNat n) else none
```

**n35_D7FF_refused** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n < 0xD7FF || (0xDFFF < n && n < 0x110000) then some (Char.ofNat n) else none
```

**n36_E000_refused** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n < 0xD800 || (0xE000 < n && n < 0x110000) then some (Char.ofNat n) else none
```

**n37_surrogate_pairs_combined** in `Main.lean`:

```
- def toChars (ns : List Nat) : Option (List Char) :=
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+ def toChars : List Nat → Option (List Char)
+   | [] => some []
+   | h :: t@(l :: rest) =>
+     if 0xD800 ≤ h && h ≤ 0xDBFF && 0xDC00 ≤ l && l ≤ 0xDFFF then
+       (Char.ofNat (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)) :: ·) <$> toChars rest
+     else if h.isValidChar then (Char.ofNat h :: ·) <$> toChars t else none
+   | [h] => if h.isValidChar then some [Char.ofNat h] else none
```

**n38_c0_controls_refused** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar && (n ≥ 32 || n = 0) then some (Char.ofNat n) else none
```

**n39_noncharacters_refused** in `Main.lean`:

```
-   ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none
+   ns.mapM fun n => if n.isValidChar && n % 0x10000 < 0xFFFE && !(0xFDD0 ≤ n && n ≤ 0xFDEF) then some (Char.ofNat n) else none
```

**n40_no_lf_on_last_answer** in `Main.lean`:

```
-   repeat
-     let line ← stdin.getLine
-     if line.isEmpty then break
-     let line := chomp line
-     stdout.putStrLn ((request line).getD "error")
+   let mut first := true
+   repeat
+     let line ← stdin.getLine
+     if line.isEmpty then break
+     let line := chomp line
+     if !first then stdout.putStr "\n"
+     first := false
+     stdout.putStr ((request line).getD "error")
```

**n41_bom_before_output** in `Main.lean`:

```
-   let stdout ← IO.getStdout
+   let stdout ← IO.getStdout
+   stdout.putStr "\uFEFF"
```

**n42_trailing_space_every_answer** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStrLn ((request line).getD "error" ++ " ")
```

**n43_trailing_space_on_error** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStrLn ((request line).getD "error ")
```

**n44_blank_line_after_last** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStrLn ((request line).getD "error")
+   stdout.putStrLn ""
```

**n45_stderr_note** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     match request line with
+     | some s => stdout.putStrLn s
+     | none => do stdout.putStrLn "error"; IO.eprintln s!"malformed: {line}"
```

**n46_exit_status_1** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStrLn ((request line).getD "error")
+   IO.Process.exit 1
```

**n47_bom_on_error_lines** in `Main.lean`:

```
-     stdout.putStrLn ((request line).getD "error")
+     stdout.putStrLn ((request line).getD "\uFEFFerror")
```

**n48_minus_on_first_number** in `Main.lean`:

```
-   | [op, arg] => numbers arg >>= answer op
+   | [op, arg] => numbers (if arg.startsWith "-" then String.ofList (arg.toList.drop 1) else arg) >>= answer op
```

**n49_bom_on_first_line_only** in `Main.lean`:

```
-   repeat
-     let line ← stdin.getLine
-     if line.isEmpty then break
-     let line := chomp line
+   let mut first := true
+   repeat
+     let line ← stdin.getLine
+     if line.isEmpty then break
+     let line := chomp (if first then String.ofList (match line.toList with | '\uFEFF' :: r => r | cs => cs) else line)
+     first := false
```

**p01_lowercase_digits** in `Codec/Percent.lean`:

```
- "0123456789ABCDEF"
+ "0123456789abcdef"
```

**p02_tilde_encoded** in `Codec/Percent.lean`:

```
-  || n == 0x7E
+ 
```

**p03_asterisk_kept** in `Codec/Percent.lean`:

```
- n == 0x2D || n == 0x2E
+ n == 0x2D || n == 0x2E || n == 0x2A
```

**p04_non_ascii_low_byte** in `Codec/Percent.lean`:

```
- if c.toNat < 0x80 then (decode rest).map (c.toNat.toUInt8 :: ·) else none
+ (decode rest).map (c.toNat.toUInt8 :: ·)
```

**p05_bad_escape_passed_through** in `Codec/Percent.lean`:

```
-   | '%' :: _ => none
+   | '%' :: rest => (decode rest).map (0x25 :: ·)
```

**p06_digits_low_half_first** in `Codec/Percent.lean`:

```
- | some h, some l, some tail => some ((h * 16 + l).toUInt8 :: tail)
+ | some h, some l, some tail => some ((l * 16 + h).toUInt8 :: tail)
```

**p07_space_refused** in `Codec/Percent.lean`:

```
- if c.toNat < 0x80 then
+ if c.toNat < 0x80 ∧ c ≠ ' ' then
```
