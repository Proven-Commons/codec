/-
  Splitting text into lines: `Pem.splitLines` against `Codec.Spec.LinesEol`.

  `eol` allows CR LF, CR, or LF, so "a" CR LF "b" LF also reads as the
  lines "a", "", "b". `splitLines` takes CR LF as one line end, which is
  the only reading with no empty line, and no line of a PEM message is
  empty.
-/

import Codec
import Codec.Spec.Defs

open Codec

namespace Codec.Proofs.Pem

theorem ln_takeLine_sound (text l rest : List Char) (h : Pem.takeLine text = some (l, rest)) :
    ∃ e, Codec.Spec.Eol e ∧ text = l ++ e ++ rest ∧ '\r' ∉ l ∧ '\n' ∉ l ∧ rest.length < text.length := by
  induction text using Pem.takeLine.induct generalizing l rest with
  | case1 => simp [Pem.takeLine] at h
  | case2 t =>
    rw [Pem.takeLine.eq_2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨['\r', '\n'], Or.inl rfl, by simp, by simp, by simp, by simp only [List.length_cons]; omega⟩
  | case3 t ht =>
    rw [Pem.takeLine.eq_3 _ ht] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨['\r'], Or.inr (Or.inl rfl), by simp, by simp, by simp, by simp only [List.length_cons]; omega⟩
  | case4 t =>
    rw [Pem.takeLine.eq_4] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨['\n'], Or.inr (Or.inr rfl), by simp, by simp, by simp, by simp only [List.length_cons]; omega⟩
  | case5 c t h1 h2 h3 ih =>
    rw [Pem.takeLine.eq_5 _ _ h1 h2 h3] at h
    cases ht : Pem.takeLine t with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨l', r'⟩ := p
      simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, he, rfl, h4, h5, h6⟩ := ih l' r' ht
      refine ⟨e, he, by simp, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, not_or]; exact ⟨fun h => h2 h.symm, h4⟩
      · simp only [List.mem_cons, not_or]; exact ⟨fun h => h3 h.symm, h5⟩
      · simp only [List.length_cons] at h6 ⊢; omega

theorem splitLines_sound (fuel : Nat) (text : List Char) (ls : List (List Char))
    (h : Pem.splitLines fuel text = some ls) : Codec.Spec.LinesEol text ls := by
  induction fuel generalizing text ls with
  | zero =>
    cases text with
    | nil => simp [Pem.splitLines] at h; subst h; exact Codec.Spec.LinesEol.nil
    | cons c t => simp [Pem.splitLines] at h
  | succ f ih =>
    cases text with
    | nil => simp [Pem.splitLines] at h; subst h; exact Codec.Spec.LinesEol.nil
    | cons c t =>
      rw [Pem.splitLines.eq_3 _ _ (by simp)] at h
      cases ht : Pem.takeLine (c :: t) with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨l, r⟩ := p
        cases hs : Pem.splitLines f r with
        | none => simp [ht, hs] at h
        | some ls' =>
          simp only [ht, hs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          obtain ⟨e, he, heq, h1, h2, _⟩ := ln_takeLine_sound _ _ _ ht
          rw [heq]
          exact Codec.Spec.LinesEol.cons h1 h2 he (ih r ls' hs)

theorem ln_takeLine_complete (l e rest : List Char) (h1 : '\r' ∉ l) (h2 : '\n' ∉ l)
    (he : Codec.Spec.Eol e) (hcr : e = ['\r'] → rest.head? ≠ some '\n') :
    Pem.takeLine (l ++ e ++ rest) = some (l, rest) := by
  induction l with
  | nil =>
    rcases he with rfl | rfl | rfl
    · exact Pem.takeLine.eq_2 rest
    · apply Pem.takeLine.eq_3
      intro r hr
      subst hr
      exact hcr rfl rfl
    · exact Pem.takeLine.eq_4 rest
  | cons c l' ih =>
    simp only [List.mem_cons, not_or] at h1 h2
    have hc1 : c ≠ '\r' := fun h => h1.1 h.symm
    have hc2 : c ≠ '\n' := fun h => h2.1 h.symm
    show Pem.takeLine (c :: (l' ++ e ++ rest)) = _
    rw [Pem.takeLine.eq_5 _ _ (fun _ h _ => hc1 h) hc1 hc2, ih h1.2 h2.2]
    rfl

theorem ln_linesEol_head (rest : List Char) (ls : List (List Char)) (h : Codec.Spec.LinesEol rest ls)
    (hne : ∀ l ∈ ls, l ≠ []) : rest.head? ≠ some '\n' := by
  cases h with
  | nil => simp
  | @cons l e r ls' h1 h2 he _ =>
    have hl : l ≠ [] := hne l (by simp)
    cases l with
    | nil => exact absurd rfl hl
    | cons c l' =>
      simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
      intro hc
      subst hc
      exact h2 (by simp)

theorem splitLines_complete (fuel : Nat) (text : List Char) (ls : List (List Char))
    (hfuel : text.length ≤ fuel) (h : Codec.Spec.LinesEol text ls) (hne : ∀ l ∈ ls, l ≠ []) :
    Pem.splitLines fuel text = some ls := by
  induction h generalizing fuel with
  | nil => cases fuel <;> simp [Pem.splitLines]
  | @cons l e rest ls h1 h2 he hrest ih =>
    have helen : e.length ≥ 1 := by rcases he with rfl | rfl | rfl <;> simp
    simp only [List.length_append] at hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hne' : ∀ l ∈ ls, l ≠ [] := fun l' hl' => hne l' (List.mem_cons_of_mem _ hl')
    have htext : l ++ e ++ rest ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp only [List.length_append, List.length_nil] at this
      omega
    rw [Pem.splitLines.eq_3 _ _ htext]
    have ht : Pem.takeLine (l ++ e ++ rest) = some (l, rest) :=
      ln_takeLine_complete l e rest h1 h2 he (fun _ => ln_linesEol_head rest ls hrest hne')
    rw [ht]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih f (by omega) hne']
    rfl

end Codec.Proofs.Pem
