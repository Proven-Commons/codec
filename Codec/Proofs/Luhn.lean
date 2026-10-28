/-
  Proofs of the Luhn statements in `Codec/Spec.lean`, under the same names. The
  helper lemmas live in `Codec.Proofs.Luhn`.
-/

import Codec
import Codec.Spec.Defs

open Codec

namespace Codec.Proofs.Luhn

/-! Facts about single digits, checked by `decide` over `Fin 10` and both
    parities, then lifted to `Nat`. -/

theorem weigh_zero (p : Bool) : Luhn.weigh p 0 = 0 := by cases p <;> rfl

theorem weigh_nine (p : Bool) : Luhn.weigh p 9 = 9 := by cases p <;> rfl

theorem weigh_false (d : Nat) : Luhn.weigh false d = d := rfl

theorem weigh_le_fin : ∀ p : Bool, ∀ a : Fin 10, Luhn.weigh p a.val ≤ 9 := by decide

theorem weigh_inj_fin : ∀ p : Bool, ∀ a b : Fin 10,
    Luhn.weigh p a.val = Luhn.weigh p b.val → a.val = b.val := by decide

/-- Swapping two neighbouring digits leaves the sum unchanged modulo 10
    only when they are equal, or 0 and 9. -/
theorem swap_fin : ∀ p q : Bool, p ≠ q → ∀ a b : Fin 10,
    (Luhn.weigh q a.val + Luhn.weigh p b.val) % 10 =
      (Luhn.weigh q b.val + Luhn.weigh p a.val) % 10 →
    a.val = b.val ∨ (a.val = 0 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 0) := by decide

theorem weigh_le (p : Bool) (a : Nat) (ha : a ≤ 9) : Luhn.weigh p a ≤ 9 :=
  weigh_le_fin p ⟨a, by omega⟩

theorem weigh_inj (p : Bool) (a b : Nat) (ha : a ≤ 9) (hb : b ≤ 9)
    (h : Luhn.weigh p a = Luhn.weigh p b) : a = b :=
  weigh_inj_fin p ⟨a, by omega⟩ ⟨b, by omega⟩ h

theorem swap_digits (p q : Bool) (hpq : p ≠ q) (a b : Nat) (ha : a ≤ 9) (hb : b ≤ 9)
    (h : (Luhn.weigh q a + Luhn.weigh p b) % 10 = (Luhn.weigh q b + Luhn.weigh p a) % 10) :
    a = b ∨ (a = 0 ∧ b = 9) ∨ (a = 9 ∧ b = 0) :=
  swap_fin p q hpq ⟨a, by omega⟩ ⟨b, by omega⟩ h

/-! Parities. -/

theorem not_parity (k : Nat) : (!decide (k % 2 = 1)) = decide ((k + 1) % 2 = 1) := by
  by_cases h : k % 2 = 1 <;> simp [h] <;> omega

theorem parity_succ_ne (k : Nat) : decide (k % 2 = 1) ≠ decide ((k + 1) % 2 = 1) := by
  rw [← not_parity]
  cases decide (k % 2 = 1) <;> decide

/-! The sum, place by place. -/

/-- `sumFromRight` from a place of parity `k`, written as the sum over the
    places. -/
theorem sumFromRight_range (k : Nat) (L : List Nat) :
    Luhn.sumFromRight (decide (k % 2 = 1)) L =
      ((List.range L.length).map fun i => Luhn.weigh (decide ((k + i) % 2 = 1)) (L.getD i 0)).sum := by
  induction L generalizing k with
  | nil => rfl
  | cons y L ih =>
    rw [Luhn.sumFromRight, not_parity, ih (k + 1), List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.sum_cons]
    have hf : ((fun i => Luhn.weigh (decide ((k + i) % 2 = 1)) ((y :: L).getD i 0)) ∘ Nat.succ) =
        (fun i => Luhn.weigh (decide ((k + 1 + i) % 2 = 1)) (L.getD i 0)) := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one, List.getD_cons_succ]
      rw [show k + (i + 1) = k + 1 + i by omega]
    rw [hf]
    simp only [Nat.add_zero, List.getD_cons_zero]

theorem sum_eq_luhnSum (ds : List Nat) : Luhn.sum ds = Codec.Spec.luhnSum ds := by
  have h := sumFromRight_range 0 ds.reverse
  simp only [Nat.zero_mod, Nat.zero_add, List.length_reverse] at h
  rw [Luhn.sum, Codec.Spec.luhnSum]
  refine Eq.trans h ?_
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Codec.Spec.luhnShare, Luhn.weigh]

/-- Changing one digit, at place `k` from the start of the list, changes
    its share only. -/
theorem sumFromRight_mid (k : Nat) (r l : List Nat) (x : Nat) :
    Luhn.sumFromRight (decide (k % 2 = 1)) (r ++ x :: l) =
      Luhn.sumFromRight (decide (k % 2 = 1)) (r ++ 0 :: l) +
        Luhn.weigh (decide ((k + r.length) % 2 = 1)) x := by
  induction r generalizing k with
  | nil =>
    simp only [List.nil_append, Luhn.sumFromRight, weigh_zero, List.length_nil, Nat.add_zero]
    omega
  | cons y r ih =>
    simp only [List.cons_append, Luhn.sumFromRight]
    rw [not_parity, ih (k + 1), List.length_cons, show k + (r.length + 1) = k + 1 + r.length by omega]
    omega

/-- The normal form: the digit `x` adds its share at place `r.length`. -/
theorem sum_mid (l r : List Nat) (x : Nat) :
    Luhn.sum (l ++ x :: r) =
      Luhn.sum (l ++ 0 :: r) + Luhn.weigh (decide (r.length % 2 = 1)) x := by
  have h := sumFromRight_mid 0 r.reverse l.reverse x
  simp only [Nat.zero_mod, Nat.zero_add, List.length_reverse] at h
  simp only [Luhn.sum, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.singleton_append]
  exact h

theorem sum_pair (l r : List Nat) (a b : Nat) :
    Luhn.sum (l ++ a :: b :: r) =
      Luhn.sum (l ++ 0 :: 0 :: r) + Luhn.weigh (decide ((r.length + 1) % 2 = 1)) a +
        Luhn.weigh (decide (r.length % 2 = 1)) b := by
  have h1 := sum_mid (l ++ [a]) r b
  have h2 := sum_mid l (0 :: r) a
  simp only [List.append_assoc, List.singleton_append, List.length_cons] at h1 h2
  omega

theorem valid_eq (ds : List Nat) :
    Luhn.valid ds = true ↔ (∀ d ∈ ds, d ≤ 9) ∧ Luhn.sum ds % 10 = 0 := by
  simp [Luhn.valid, List.all_eq_true]

end Codec.Proofs.Luhn

open Codec.Proofs.Luhn

theorem Codec.Spec.luhn_valid_iff (ds : List Nat) :
    Luhn.valid ds = true ↔ (∀ d ∈ ds, d ≤ 9) ∧ Codec.Spec.luhnSum ds % 10 = 0 := by
  rw [valid_eq, sum_eq_luhnSum]

theorem Codec.Spec.luhn_checkDigit (ds : List Nat) (h : ∀ d ∈ ds, d ≤ 9) :
    Luhn.checkDigit ds ≤ 9 ∧
      ∀ c, c ≤ 9 → (Luhn.valid (ds ++ [c]) = true ↔ c = Luhn.checkDigit ds) := by
  constructor
  · unfold Luhn.checkDigit
    omega
  · intro c hc
    have hs := sum_mid ds [] c
    simp only [List.length_nil, Nat.zero_mod] at hs
    rw [valid_eq, hs]
    have hall : ∀ d ∈ ds ++ [c], d ≤ 9 := by
      intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact h d hd
      · omega
    unfold Luhn.checkDigit
    simp only [weigh_false, Nat.zero_ne_one, decide_false]
    constructor
    · intro ⟨_, h2⟩
      omega
    · intro h2
      exact ⟨hall, by omega⟩

theorem Codec.Spec.luhn_single_error (l r : List Nat) (a b : Nat)
    (h : Luhn.valid (l ++ a :: r) = true) (hb : b ≤ 9) (hab : a ≠ b) :
    Luhn.valid (l ++ b :: r) = false := by
  rw [valid_eq] at h
  obtain ⟨hall, hs⟩ := h
  have ha : a ≤ 9 := hall a (by simp)
  cases hv : Luhn.valid (l ++ b :: r) with
  | false => rfl
  | true =>
    rw [valid_eq] at hv
    obtain ⟨_, hs'⟩ := hv
    rw [sum_mid] at hs hs'
    have := weigh_le (decide (r.length % 2 = 1)) a ha
    have := weigh_le (decide (r.length % 2 = 1)) b hb
    have := weigh_inj (decide (r.length % 2 = 1)) a b ha hb
    omega

theorem Codec.Spec.luhn_adjacent_swap (l r : List Nat) (a b : Nat)
    (h : Luhn.valid (l ++ a :: b :: r) = true) (hab : a ≠ b)
    (h09 : ¬ (a = 0 ∧ b = 9)) (h90 : ¬ (a = 9 ∧ b = 0)) :
    Luhn.valid (l ++ b :: a :: r) = false := by
  rw [valid_eq] at h
  obtain ⟨hall, hs⟩ := h
  have ha : a ≤ 9 := hall a (by simp)
  have hb : b ≤ 9 := hall b (by simp)
  cases hv : Luhn.valid (l ++ b :: a :: r) with
  | false => rfl
  | true =>
    rw [valid_eq] at hv
    obtain ⟨_, hs'⟩ := hv
    rw [sum_pair] at hs hs'
    have hm := swap_digits _ _ (parity_succ_ne r.length) a b ha hb (by omega)
    omega

theorem Codec.Spec.luhn_swap_09 (l r : List Nat) :
    Luhn.valid (l ++ 0 :: 9 :: r) = Luhn.valid (l ++ 9 :: 0 :: r) := by
  have hs : Luhn.sum (l ++ 0 :: 9 :: r) = Luhn.sum (l ++ 9 :: 0 :: r) := by
    rw [sum_pair, sum_pair l r 9 0, weigh_zero, weigh_zero, weigh_nine, weigh_nine]
  simp [Luhn.valid, hs]

theorem Codec.Spec.luhn_vectors :
    Luhn.valid [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3] = true ∧
    Luhn.checkDigit [7, 9, 9, 2, 7, 3, 9, 8, 7, 1] = 3 ∧
    Luhn.valid [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 4] = false ∧
    Luhn.valid [4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true ∧
    Luhn.valid [1, 0] = false := by
  and_intros <;> decide +kernel
