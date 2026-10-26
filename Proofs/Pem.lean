/-
  Proofs of the PEM statements in `Spec.lean`, under the same names, from
  the lemmas in `Proofs/Pem/` and the base 64 statements. The vectors are
  checked by evaluation in the kernel.
-/

import Codec
import Spec.Defs
import Proofs.Base64
import Proofs.Pem.Lines
import Proofs.Pem.Parts

open Codec

namespace Codec.Proofs.Pem

theorem pm_text_eq (label : List Char) (data : List UInt8) :
    (Pem.lines label data).flatMap (· ++ ['\n']) = Spec.pemText label data := by
  rw [lines_eq, Spec.pemText, List.flatMap_def]

theorem pm_mem_lines64 {s l : List Char} {c : Char} (hl : l ∈ Spec.lines64 s) (hc : c ∈ l) :
    c ∈ s := by
  unfold Spec.lines64 at hl
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
  exact List.mem_of_mem_drop (List.mem_of_mem_take hc)

theorem pm_char_ok (n : Nat) : Base64.char n ≠ '\r' ∧ Base64.char n ≠ '\n' := by
  unfold Base64.char
  rw [List.getD_eq_getElem?_getD]
  cases h : Base64.alphabet[n]? with
  | none => decide
  | some x =>
    have hx : x ∈ Base64.alphabet := List.mem_of_getElem? h
    have hall : ∀ y ∈ Base64.alphabet, y ≠ '\r' ∧ y ≠ '\n' := by decide
    exact hall x hx

theorem pm_encode_ok (bs : List UInt8) : ∀ c ∈ Base64.encode bs, c ≠ '\r' ∧ c ≠ '\n' := by
  induction bs using Base64.encode.induct with
  | case1 a b c rest ih =>
    rw [Base64.encode.eq_1]
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    all_goals first | exact pm_char_ok _ | exact ih x hx
  | case2 a b =>
    rw [Base64.encode.eq_2]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals first | exact pm_char_ok _ | decide
  | case3 a =>
    rw [Base64.encode.eq_3]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals first | exact pm_char_ok _ | decide
  | case4 =>
    rw [Base64.encode.eq_4]
    intro x hx
    cases hx

theorem pm_labelChar_ok {c : Char} (h : Spec.labelChar c) : c ≠ '\r' ∧ c ≠ '\n' := by
  unfold Spec.labelChar at h
  constructor <;> rintro rfl <;> revert h <;> decide

theorem pm_labelTail_ok {l : List Char} (h : Spec.LabelTail l) :
    ∀ c ∈ l, c ≠ '\r' ∧ c ≠ '\n' := by
  induction h with
  | nil => intro x hx; cases hx
  | char hc _ ih =>
    intro x hx
    cases hx with
    | head => exact pm_labelChar_ok hc
    | tail _ hx => exact ih x hx
  | sep hs hc _ ih =>
    intro x hx
    cases hx with
    | head => rcases hs with rfl | rfl <;> decide
    | tail _ hx =>
      cases hx with
      | head => exact pm_labelChar_ok hc
      | tail _ hx => exact ih x hx

theorem pm_label_ok {l : List Char} (h : Spec.Label l) : ∀ c ∈ l, c ≠ '\r' ∧ c ≠ '\n' := by
  rcases h with rfl | ⟨c, rest, rfl, hc, ht⟩
  · intro x hx; cases hx
  · intro x hx
    cases hx with
    | head => exact pm_labelChar_ok hc
    | tail _ hx => exact pm_labelTail_ok ht x hx

theorem pm_pemLines_ok (label : List Char) (data : List UInt8) (hl : Spec.Label label) :
    ∀ l ∈ Spec.pemLines label data, '\r' ∉ l ∧ '\n' ∉ l := by
  have key : ∀ l ∈ Spec.pemLines label data, ∀ c ∈ l, c ≠ '\r' ∧ c ≠ '\n' := by
    intro l hl' c hc
    simp only [Spec.pemLines, List.mem_append, List.mem_singleton] at hl'
    rcases hl' with (rfl | hl') | rfl
    · simp only [List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · revert c; decide
      · exact pm_label_ok hl c hc
      · revert c; decide
    · exact pm_encode_ok data c (pm_mem_lines64 hl' hc)
    · simp only [List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · revert c; decide
      · exact pm_label_ok hl c hc
      · revert c; decide
  intro l hl'
  exact ⟨fun h => (key l hl' _ h).1 rfl, fun h => (key l hl' _ h).2 rfl⟩

theorem pm_pemLines_ne_nil (label : List Char) (data : List UInt8) :
    ∀ l ∈ Spec.pemLines label data, l ≠ [] := by
  intro l hl'
  simp only [Spec.pemLines, List.mem_append, List.mem_singleton] at hl'
  rcases hl' with (rfl | hl') | rfl
  · simp
  · exact lines64_ne_nil _ l hl'
  · simp

theorem pm_linesEol_lf (ls : List (List Char)) (h : ∀ l ∈ ls, '\r' ∉ l ∧ '\n' ∉ l) :
    Spec.LinesEol ((ls.map (· ++ ['\n'])).flatten) ls := by
  induction ls with
  | nil => exact Spec.LinesEol.nil
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have := Spec.LinesEol.cons (e := ['\n']) hl.1 hl.2 (Or.inr (Or.inr rfl))
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    simpa only [List.map_cons, List.flatten_cons, List.append_assoc] using this

end Codec.Proofs.Pem

open Codec.Proofs.Pem

theorem Spec.pem_encode_iff (label : List Char) (data : List UInt8) (text : List Char) :
    Pem.encode label data = some text ↔ Spec.Label label ∧ text = Spec.pemText label data := by
  unfold Pem.encode
  rw [← validLabel_iff, pm_text_eq]
  constructor
  · intro h
    split at h
    · rename_i hv
      cases h
      exact ⟨hv, rfl⟩
    · cases h
  · rintro ⟨hv, rfl⟩
    simp [hv]

theorem Spec.pem_decode_iff (text label : List Char) (data : List UInt8) :
    Pem.decode text = some (label, data) ↔ Spec.StrictPem text label data := by
  constructor
  · intro h
    cases hs : Pem.splitLines text.length text with
    | none =>
      unfold Pem.decode at h
      rw [hs] at h
      cases h
    | some ls =>
      have hle := splitLines_sound _ _ _ hs
      unfold Pem.decode at h
      rw [hs] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      match ls, h with
      | first :: rest, h =>
        simp only at h
        cases hlast : rest.getLast? with
        | none => rw [hlast] at h; cases h
        | some last =>
          rw [hlast] at h
          simp only at h
          obtain ⟨body, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
          simp only [List.dropLast_concat] at h
          cases hb : Pem.labelOf "-----BEGIN ".toList first with
          | none => rw [hb] at h; cases h
          | some lb =>
            cases he : Pem.labelOf "-----END ".toList last with
            | none => rw [hb, he] at h; cases h
            | some le =>
              cases hd : Base64.decode body.flatten with
              | none => rw [hb, he, hd] at h; cases h
              | some d =>
                rw [hb, he, hd] at h
                simp only [Option.bind_some] at h
                split at h
                · rename_i hc
                  obtain ⟨rfl, hv, hbody⟩ := hc
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hflat := Spec.base64_encode_decode _ _ hd
                  rw [lines64_eq, ← hflat] at hbody
                  rw [labelOf_some _ _ _ hb, labelOf_some _ _ _ he, hbody] at hle
                  exact ⟨(validLabel_iff _).mp hv, hle⟩
                · cases h
  · rintro ⟨hl, hle⟩
    have hs := splitLines_complete text.length text _ (Nat.le_refl _) hle
      (pm_pemLines_ne_nil label data)
    unfold Pem.decode
    rw [hs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    simp only [Spec.pemLines, List.cons_append, List.nil_append, List.getLast?_concat,
      List.dropLast_concat, labelOf_append, Option.bind_some, flatten_lines64,
      Spec.base64_decode_encode, lines64_eq]
    simp only [(validLabel_iff label).mpr hl, and_self, ite_true]

theorem Spec.pem_decode_encode (label : List Char) (data : List UInt8) (text : List Char) :
    Pem.encode label data = some text → Pem.decode text = some (label, data) := by
  intro h
  obtain ⟨hl, rfl⟩ := (Spec.pem_encode_iff label data text).mp h
  exact (Spec.pem_decode_iff _ _ _).mpr ⟨hl, pm_linesEol_lf _ (pm_pemLines_ok label data hl)⟩

theorem Spec.pem_vectors :
    Pem.encode "PUBLIC KEY".toList Spec.figure15 = some
      ("-----BEGIN PUBLIC KEY-----\nMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAEn1LlwLN/KBYQRVH6HfIMTzfEqJOVztLe\n".toList ++
       "kLchp2hi78cCaMY81FBlYs8J9l7krc+M4aBeCGYFjba+hiXttJWPL7ydlE+5UG4U\nNkn3Eos8EiZByi9DVsyfy9eejh+8AXgp\n-----END PUBLIC KEY-----\n".toList) ∧
    Pem.decode ("-----BEGIN PUBLIC KEY-----\r\nMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAEn1LlwLN/KBYQRVH6HfIMTzfEqJOVztLe\r\n".toList ++
       "kLchp2hi78cCaMY81FBlYs8J9l7krc+M4aBeCGYFjba+hiXttJWPL7ydlE+5UG4U\r\nNkn3Eos8EiZByi9DVsyfy9eejh+8AXgp\r\n-----END PUBLIC KEY-----\r\n".toList) =
      some ("PUBLIC KEY".toList, Spec.figure15) ∧
    Pem.encode "X".toList [] = some "-----BEGIN X-----\n-----END X-----\n".toList ∧
    Pem.decode "-----BEGIN X-----\n-----END X-----\n".toList = some ("X".toList, []) ∧
    Pem.decode "-----BEGIN -----\rAA==\r-----END -----\r".toList = some ([], [0]) ∧
    Pem.encode "RSA PRIVATE KEY".toList [0] =
      some "-----BEGIN RSA PRIVATE KEY-----\nAA==\n-----END RSA PRIVATE KEY-----\n".toList ∧
    Pem.encode "A,B".toList [] = some "-----BEGIN A,B-----\n-----END A,B-----\n".toList ∧
    Pem.encode "A--B".toList [] = none ∧
    Pem.encode "A  B".toList [] = none ∧
    Pem.encode " A".toList [] = none ∧
    Pem.encode "A-".toList [] = none ∧
    Pem.encode "\u00c9".toList [] = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END Y-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END X-----".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA== \n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X----- \nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\n\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nProc-Type: 4,ENCRYPTED\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "text\n-----BEGIN X-----\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END X-----\n\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAB==\n-----END X-----\n".toList = none ∧
    Pem.decode ("-----BEGIN X-----\nAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\nAAAAAAAA\n".toList ++
      "-----END X-----\n".toList) = none := by
  and_intros <;> decide +kernel
