/-
  The parts of a PEM message: labels, lines of 64 characters, and the
  BEGIN and END lines, in the code against the spec.
-/

import Codec
import Codec.Spec.Defs

open Codec

namespace Codec.Proofs.Pem

theorem pt_isLabelChar_iff (c : Char) : Pem.isLabelChar c = true ↔ Codec.Spec.labelChar c := by
  simp [Pem.isLabelChar, Codec.Spec.labelChar]

private theorem pt_labelRest_cons (c : Char) (rest : List Char) :
    Pem.labelRest (c :: rest) =
      if Pem.isLabelChar c = true then Pem.labelRest rest
      else if c = '-' ∨ c = ' ' then
        (match rest with
        | d :: rest' => Pem.isLabelChar d && Pem.labelRest rest'
        | [] => false)
      else false := by
  rw [Pem.labelRest.eq_def]; rfl

theorem pt_labelRest_iff : ∀ (r : List Char), Pem.labelRest r = true ↔ Codec.Spec.LabelTail r
  | [] => by simp [Pem.labelRest, Codec.Spec.LabelTail.nil]
  | c :: rest => by
    have ih := pt_labelRest_iff rest
    rw [pt_labelRest_cons]
    by_cases hc : Pem.isLabelChar c = true
    · rw [ite_eq_left hc, ih]
      constructor
      · intro h; exact Codec.Spec.LabelTail.char ((pt_isLabelChar_iff c).1 hc) h
      · intro h
        cases h with
        | char _ h => exact h
        | sep hs _ _ =>
          rcases hs with hs | hs <;> subst hs <;> simp [Pem.isLabelChar] at hc
    · rw [ite_eq_right hc]
      by_cases hs : c = '-' ∨ c = ' '
      · rw [ite_eq_left hs]
        cases rest with
        | nil =>
          simp only [Bool.false_eq_true, false_iff]
          intro h
          cases h with
          | char h _ => exact hc ((pt_isLabelChar_iff c).2 h)
        | cons d rest' =>
          have ih' := pt_labelRest_iff rest'
          simp only [Bool.and_eq_true]
          rw [ih', pt_isLabelChar_iff]
          constructor
          · rintro ⟨h1, h2⟩; exact Codec.Spec.LabelTail.sep hs h1 h2
          · intro h
            cases h with
            | char h _ => exact absurd ((pt_isLabelChar_iff c).2 h) hc
            | sep _ h1 h2 => exact ⟨h1, h2⟩
      · rw [ite_eq_right hs]
        simp only [Bool.false_eq_true, false_iff]
        intro h
        cases h with
        | char h _ => exact hc ((pt_isLabelChar_iff c).2 h)
        | sep h _ _ => exact hs h

theorem validLabel_iff (l : List Char) : Pem.validLabel l = true ↔ Codec.Spec.Label l := by
  cases l with
  | nil => simp [Pem.validLabel, Codec.Spec.Label]
  | cons c rest =>
    simp only [Pem.validLabel, Bool.and_eq_true, pt_isLabelChar_iff, pt_labelRest_iff, Codec.Spec.Label]
    constructor
    · intro h; exact Or.inr ⟨c, rest, rfl, h⟩
    · rintro (h | ⟨c', rest', h, h1, h2⟩)
      · cases h
      · cases h; exact ⟨h1, h2⟩

theorem pt_spec_lines64_nil : Codec.Spec.lines64 [] = [] := by
  simp [Codec.Spec.lines64]

theorem pt_spec_lines64_cons (s : List Char) (h : s ≠ []) :
    Codec.Spec.lines64 s = s.take 64 :: Codec.Spec.lines64 (s.drop 64) := by
  have hlen : 0 < s.length := List.length_pos_iff.2 h
  have hk : (s.length + 63) / 64 = ((s.drop 64).length + 63) / 64 + 1 := by
    rw [List.length_drop]; omega
  unfold Codec.Spec.lines64
  rw [hk, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.mul_zero, List.drop_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, List.drop_drop, Nat.succ_eq_add_one]
  congr 2
  omega

theorem pt_lines64_fuel : ∀ (fuel : Nat) (s : List Char), s.length ≤ fuel →
    Pem.lines64 fuel s = Codec.Spec.lines64 s
  | _, [], _ => by simp [Pem.lines64, pt_spec_lines64_nil]
  | 0, _ :: _, h => by simp at h
  | fuel + 1, c :: cs, h => by
    rw [Pem.lines64, pt_spec_lines64_cons _ (List.cons_ne_nil c cs)]
    · rw [pt_lines64_fuel fuel _ (by simp at h ⊢; omega)]
    · exact List.cons_ne_nil c cs

theorem lines64_eq (s : List Char) : Pem.lines64 s.length s = Codec.Spec.lines64 s :=
  pt_lines64_fuel _ _ (Nat.le_refl _)

theorem pt_lines64_fuel_props : ∀ (fuel : Nat) (s : List Char), s.length ≤ fuel →
    (Codec.Spec.lines64 s).flatten = s ∧ ∀ l ∈ Codec.Spec.lines64 s, l ≠ []
  | _, [], _ => by simp [pt_spec_lines64_nil]
  | 0, _ :: _, h => by simp at h
  | fuel + 1, c :: cs, h => by
    rw [pt_spec_lines64_cons _ (List.cons_ne_nil c cs)]
    have ih := pt_lines64_fuel_props fuel ((c :: cs).drop 64) (by simp at h ⊢; omega)
    refine ⟨?_, ?_⟩
    · rw [List.flatten_cons, ih.1, List.take_append_drop]
    · intro l hl
      rcases List.mem_cons.1 hl with hl | hl
      · subst hl; simp
      · exact ih.2 l hl

theorem flatten_lines64 (s : List Char) : (Codec.Spec.lines64 s).flatten = s :=
  (pt_lines64_fuel_props s.length s (Nat.le_refl _)).1

theorem lines64_ne_nil (s : List Char) : ∀ l ∈ Codec.Spec.lines64 s, l ≠ [] :=
  (pt_lines64_fuel_props s.length s (Nat.le_refl _)).2

theorem lines_eq (label : List Char) (data : List UInt8) :
    Pem.lines label data = Codec.Spec.pemLines label data := by
  unfold Pem.lines Pem.beginLine Pem.endLine Codec.Spec.pemLines
  dsimp only
  rw [lines64_eq]
  rfl

theorem labelOf_append (pre l : List Char) :
    Pem.labelOf pre (pre ++ l ++ "-----".toList) = some l := by
  unfold Pem.labelOf
  have h1 : pre.isPrefixOf (pre ++ l ++ "-----".toList) = true := by
    rw [List.isPrefixOf_iff_prefix, List.append_assoc]; exact List.prefix_append _ _
  have h2 : "-----".toList.isSuffixOf (pre ++ l ++ "-----".toList) = true := by
    rw [List.isSuffixOf_iff_suffix]; exact List.suffix_append _ _
  have h5 : "-----".toList.length = 5 := rfl
  have h3 : pre.length + 5 ≤ (pre ++ l ++ "-----".toList).length := by
    simp only [List.length_append, h5]; omega
  rw [ite_eq_left ⟨h1, h2, h3⟩]
  congr 1
  rw [List.append_assoc, List.drop_left]
  have : (pre ++ (l ++ "-----".toList)).length - pre.length - 5 = l.length := by
    simp only [List.length_append, h5]; omega
  rw [this, List.take_left]

theorem labelOf_some (pre line l : List Char) (h : Pem.labelOf pre line = some l) :
    line = pre ++ l ++ "-----".toList := by
  unfold Pem.labelOf at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases h
    rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take] at h1
    rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop] at h2
    have h5 : "-----".toList.length = 5 := rfl
    rw [h5] at h2
    have e1 := List.take_append_drop pre.length line
    have e2 := List.take_append_drop (line.length - pre.length - 5) (line.drop pre.length)
    rw [List.drop_drop] at e2
    have : pre.length + (line.length - pre.length - 5) = line.length - 5 := by omega
    rw [this, ← h2] at e2
    rw [List.append_assoc, e2]
    exact e1.symm.trans (by rw [← h1])
  · cases h

end Codec.Proofs.Pem
