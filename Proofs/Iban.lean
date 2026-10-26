/-
  Proofs of the Iban statements in `Spec.lean`, under the same names. The
  helper lemmas live in `Codec.Proofs.Iban`.
-/

import Codec
import Spec.Defs

open Codec

namespace Codec.Proofs.Iban

/-! ### Characters, through their code points -/

theorem isDigit_iff (c : Char) : Iban.isDigit c = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [Iban.isDigit, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]

theorem isUpper_iff (c : Char) : Iban.isUpper c = true ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp [Iban.isUpper, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]

theorem ibanDigit_iff (c : Char) : Spec.ibanDigit c ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [Spec.ibanDigit, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]

theorem ibanLetter_iff (c : Char) : Spec.ibanLetter c ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp [Spec.ibanLetter, Char.le_def, UInt32.le_iff_toNat_le, Char.toNat_val]

theorem isDigit_digit (c : Char) : Iban.isDigit c = true ↔ Spec.ibanDigit c := by
  rw [isDigit_iff, ibanDigit_iff]

theorem isUpper_letter (c : Char) : Iban.isUpper c = true ↔ Spec.ibanLetter c := by
  rw [isUpper_iff, ibanLetter_iff]

theorem ibanValue_eq (c : Char) : Spec.ibanValue c = Iban.value c := by
  simp [Spec.ibanValue, Iban.value, Iban.isDigit]

theorem not_digit_of_upper (c : Char) (h : Iban.isUpper c = true) : Iban.isDigit c = false := by
  have := (isUpper_iff c).mp h
  cases hd : Iban.isDigit c
  · rfl
  · have := (isDigit_iff c).mp hd; omega

theorem value_of_digit (c : Char) (h : Iban.isDigit c = true) : Iban.value c = c.toNat - 48 := by
  simp [Iban.value, h]

theorem value_of_not_digit (c : Char) (h : Iban.isDigit c = false) :
    Iban.value c = c.toNat - 55 := by
  simp [Iban.value, h]

/-! ### The number a string writes, one character at a time -/

/-- The factor a character shifts the number by: 10 for a digit, 100 otherwise. -/
def pw (c : Char) : Nat := if Iban.isDigit c then 10 else 100

def step (n : Nat) (c : Char) : Nat := n * pw c + Iban.value c

def num (cs : List Char) : Nat := cs.foldl step 0

def pws : List Char → Nat
  | [] => 1
  | c :: cs => pw c * pws cs

theorem foldl_step (n : Nat) (cs : List Char) : cs.foldl step n = n * pws cs + num cs := by
  induction cs generalizing n with
  | nil => simp [num, pws]
  | cons c cs ih =>
    simp only [num, List.foldl_cons]
    rw [ih, ih (step 0 c)]
    simp only [step, pws, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem num_append (xs ys : List Char) : num (xs ++ ys) = num xs * pws ys + num ys := by
  rw [num, List.foldl_append, foldl_step]
  rfl

theorem num_snoc (xs : List Char) (c : Char) : num (xs ++ [c]) = num xs * pw c + Iban.value c := by
  rw [num_append]
  simp [num, pws, step]

theorem num_cons (c : Char) (cs : List Char) : num (c :: cs) = Iban.value c * pws cs + num cs := by
  rw [show c :: cs = [c] ++ cs from rfl, num_append]
  simp [num, step]

theorem num_mid (L R : List Char) (c : Char) :
    num (L ++ c :: R) = (num L * pw c + Iban.value c) * pws R + num R := by
  rw [show L ++ c :: R = (L ++ [c]) ++ R by simp, num_append, num_snoc]

theorem num_mid2 (L R : List Char) (c d : Char) :
    num (L ++ c :: d :: R) = ((num L * pw c + Iban.value c) * pw d + Iban.value d) * pws R + num R := by
  rw [show L ++ c :: d :: R = (L ++ [c]) ++ d :: R by simp, num_mid, num_snoc]

theorem mod97_eq (cs : List Char) : Iban.mod97 cs = num cs % 97 := by
  have key : ∀ (n : Nat) (cs : List Char),
      cs.foldl (fun r c => if Iban.isDigit c then (r * 10 + Iban.value c) % 97
        else (r * 100 + Iban.value c) % 97) (n % 97) = cs.foldl step n % 97 := by
    intro n cs
    induction cs generalizing n with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [← ih]
      congr 1
      simp only [step, pw]
      split <;> omega
  have := key 0 cs
  simpa [Iban.mod97, num] using this

theorem pw_of_digit (c : Char) (h : Iban.isDigit c = true) : pw c = 10 := by
  simp [pw, h]

theorem pw_of_not_digit (c : Char) (h : Iban.isDigit c = false) : pw c = 100 := by
  simp [pw, h]

theorem pws_append (xs ys : List Char) : pws (xs ++ ys) = pws xs * pws ys := by
  induction xs with
  | nil => simp [pws]
  | cons c xs ih => simp only [List.cons_append, pws, ih, Nat.mul_assoc]

theorem pws_pow (cs : List Char) : ∃ k, pws cs = 10 ^ k ∧ k ≤ 2 * cs.length := by
  induction cs with
  | nil => exact ⟨0, rfl, by simp⟩
  | cons c cs ih =>
    obtain ⟨k, hk, hl⟩ := ih
    simp only [pws, pw, hk, List.length_cons]
    split
    · exact ⟨k + 1, by rw [Nat.pow_succ, Nat.mul_comm], by omega⟩
    · exact ⟨k + 2, by rw [Nat.pow_add]; simp [Nat.mul_comm], by omega⟩

theorem cancel_pow (k : Nat) : ∀ x y : Nat, (x * 10 ^ k) % 97 = (y * 10 ^ k) % 97 → x % 97 = y % 97 := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x y h
    have e : ∀ z : Nat, z * 10 ^ (k + 1) = (z * 10) * 10 ^ k := by
      intro z
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, Nat.mul_assoc]
    rw [e, e] at h
    have := ih _ _ h
    omega

theorem cancel_pws (R : List Char) (x y : Nat) (h : (x * pws R) % 97 = (y * pws R) % 97) :
    x % 97 = y % 97 := by
  obtain ⟨k, hk, _⟩ := pws_pow R
  rw [hk] at h
  exact cancel_pow k x y h

/-- 10 has order 96 mod 97. -/
theorem pow_ten_ne : ∀ K : Fin 96, 0 < K.val → 10 ^ K.val % 97 ≠ 1 := by decide +kernel

/-- Two different digits swapped around a factor other than 1 change the remainder. -/
theorem swap_fin : ∀ u : Fin 97, u.val ≠ 1 → ∀ x y : Fin 10,
    (y.val * u.val + x.val) % 97 = (x.val * u.val + y.val) % 97 → x = y := by decide +kernel

theorem mul_mod_right (x y : Nat) : (x * y) % 97 = (x * (y % 97)) % 97 := by
  rw [Nat.mul_mod x (y % 97), Nat.mod_mod, ← Nat.mul_mod]

/-! ### Shape, rotation, validity -/

theorem wellShaped_cons4 (c0 c1 k0 k1 : Char) (bban : List Char) :
    Iban.wellShaped (c0 :: c1 :: k0 :: k1 :: bban) = true ↔
      Iban.isUpper c0 = true ∧ Iban.isUpper c1 = true ∧ Iban.isDigit k0 = true ∧
        Iban.isDigit k1 = true ∧ 1 ≤ bban.length ∧ bban.length ≤ 30 ∧
          ∀ c ∈ bban, Iban.isDigit c = true ∨ Iban.isUpper c = true := by
  simp only [Iban.wellShaped, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, and_assoc]

theorem shape_iff (s : List Char) : Iban.wellShaped s = true ↔ Spec.IbanShape s := by
  constructor
  · intro hs
    match s, hs with
    | c0 :: c1 :: k0 :: k1 :: bban, hs =>
      rw [wellShaped_cons4] at hs
      obtain ⟨u0, u1, d0, d1, l1, l2, hb⟩ := hs
      exact ⟨c0, c1, k0, k1, bban, rfl, (isUpper_letter c0).mp u0, (isUpper_letter c1).mp u1,
        (isDigit_digit k0).mp d0, (isDigit_digit k1).mp d1, l1, l2,
        fun c hc => (hb c hc).imp (isDigit_digit c).mp (isUpper_letter c).mp⟩
    | [], hs | [_], hs | [_, _], hs | [_, _, _], hs => simp [Iban.wellShaped] at hs
  · rintro ⟨c0, c1, k0, k1, bban, rfl, u0, u1, d0, d1, l1, l2, hb⟩
    rw [wellShaped_cons4]
    exact ⟨(isUpper_letter c0).mpr u0, (isUpper_letter c1).mpr u1,
      (isDigit_digit k0).mpr d0, (isDigit_digit k1).mpr d1, l1, l2,
      fun c hc => (hb c hc).imp (isDigit_digit c).mpr (isUpper_letter c).mpr⟩

theorem rot_ok (s : List Char) (hs : Iban.wellShaped s = true) :
    ∀ c ∈ s.drop 4 ++ s.take 4, Iban.isDigit c = true ∨ Iban.isUpper c = true := by
  match s, hs with
  | c0 :: c1 :: k0 :: k1 :: bban, hs =>
    rw [wellShaped_cons4] at hs
    obtain ⟨u0, u1, d0, d1, _, _, hb⟩ := hs
    intro c hc
    simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc | hc | hc
    · exact hb c hc
    · subst hc; exact Or.inr u0
    · subst hc; exact Or.inr u1
    · subst hc; exact Or.inl d0
    · subst hc; exact Or.inl d1
  | [], hs | [_], hs | [_, _], hs | [_, _, _], hs => simp [Iban.wellShaped] at hs

theorem digits_step (c : Char) (hc : Iban.isDigit c = true ∨ Iban.isUpper c = true) (n : Nat) :
    (Spec.ibanDigits c).foldl (fun n d => 10 * n + d) n = step n c := by
  simp only [Spec.ibanDigits, ibanValue_eq, step]
  rcases hc with hc | hc
  · have := (isDigit_iff c).mp hc
    rw [pw_of_digit c hc, value_of_digit c hc, ite_eq_left (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    omega
  · have := (isUpper_iff c).mp hc
    have hd := not_digit_of_upper c hc
    rw [pw_of_not_digit c hd, value_of_not_digit c hd, ite_eq_right (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    omega

theorem ibanNumber_eq (cs : List Char)
    (h : ∀ c ∈ cs, Iban.isDigit c = true ∨ Iban.isUpper c = true) :
    Spec.ibanNumber cs = num cs := by
  unfold Spec.ibanNumber Spec.decimal num
  rw [List.foldl_flatMap]
  suffices ∀ n, cs.foldl (fun acc x => (Spec.ibanDigits x).foldl (fun n d => 10 * n + d) acc) n =
      cs.foldl step n from this 0
  induction cs with
  | nil => intro n; rfl
  | cons c cs ih =>
    intro n
    simp only [List.foldl_cons]
    rw [digits_step c (h c (by simp)), ih (fun c hc => h c (by simp [hc]))]

theorem valid_iff_num (s : List Char) :
    Iban.valid s = true ↔ Iban.wellShaped s = true ∧ num (s.drop 4 ++ s.take 4) % 97 = 1 := by
  simp [Iban.valid, mod97_eq]

theorem valid_false (s : List Char) (h : num (s.drop 4 ++ s.take 4) % 97 ≠ 1) :
    Iban.valid s = false := by
  simp [Iban.valid, mod97_eq, h]

/-- Moving the first four characters to the end keeps a block that lies
    wholly before or wholly after the cut in one piece. -/
theorem rot_block (l m r : List Char) (h : l.length + m.length ≤ 4 ∨ 4 ≤ l.length) :
    ∃ L R : List Char, ∀ m' : List Char, m'.length = m.length →
      (l ++ (m' ++ r)).drop 4 ++ (l ++ (m' ++ r)).take 4 = L ++ (m' ++ R) := by
  rcases h with h | h
  · refine ⟨r.drop (4 - l.length - m.length) ++ l, r.take (4 - l.length - m.length), ?_⟩
    intro m' hm
    rw [← List.append_assoc, List.drop_append, List.take_append,
      List.drop_eq_nil_of_le (by simp; omega), List.take_of_length_le (by simp; omega)]
    simp [hm, Nat.sub_sub]
  · refine ⟨l.drop 4, r ++ l.take 4, ?_⟩
    intro m' _
    rw [List.drop_append_of_le_length h, List.take_append_of_le_length h]
    simp

/-- Characters of the same kind that differ: equal shift, different values. -/
theorem kind_cases (a b : Char) (hab : a ≠ b)
    (hkind : (Spec.ibanDigit a ∧ Spec.ibanDigit b) ∨ (Spec.ibanLetter a ∧ Spec.ibanLetter b)) :
    ((pw a = 10 ∧ pw b = 10 ∧ Iban.value a < 10 ∧ Iban.value b < 10) ∨
      (pw a = 100 ∧ pw b = 100)) ∧
      Iban.value a ≠ Iban.value b ∧ Iban.value a < 36 ∧ Iban.value b < 36 := by
  have hne : a.toNat ≠ b.toNat := fun h => hab (Char.toNat_inj.mp h)
  rcases hkind with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have da : Iban.isDigit a = true := (isDigit_digit a).mpr ha
    have db : Iban.isDigit b = true := (isDigit_digit b).mpr hb
    rw [ibanDigit_iff] at ha hb
    rw [pw_of_digit a da, pw_of_digit b db, value_of_digit a da, value_of_digit b db]
    omega
  · have da := not_digit_of_upper a ((isUpper_letter a).mpr ha)
    have db := not_digit_of_upper b ((isUpper_letter b).mpr hb)
    rw [ibanLetter_iff] at ha hb
    rw [pw_of_not_digit a da, pw_of_not_digit b db, value_of_not_digit a da,
      value_of_not_digit b db]
    omega

theorem valid_spec (s : List Char) : Iban.valid s = true ↔ Spec.IbanValid s := by
  rw [valid_iff_num]
  unfold Spec.IbanValid
  rw [← shape_iff]
  constructor
  · rintro ⟨hs, hm⟩
    exact ⟨hs, by rw [ibanNumber_eq _ (rot_ok s hs)]; exact hm⟩
  · rintro ⟨hs, hm⟩
    exact ⟨hs, by rw [ibanNumber_eq _ (rot_ok s hs)] at hm; exact hm⟩

/-- The digit characters, as `checkDigits` writes them. -/
theorem digitChar : ∀ d : Fin 10, Iban.isDigit (Char.ofNat (48 + d.val)) = true ∧
    (Char.ofNat (48 + d.val)).toNat = 48 + d.val := by decide

theorem digitChar' (d : Nat) (h : d < 10) : Iban.isDigit (Char.ofNat (48 + d)) = true ∧
    (Char.ofNat (48 + d)).toNat = 48 + d := digitChar ⟨d, h⟩

theorem num_two (d1 d2 : Char) (h1 : Iban.isDigit d1 = true) (h2 : Iban.isDigit d2 = true) :
    num [d1, d2] = Iban.value d1 * 10 + Iban.value d2 ∧ pws [d1, d2] = 100 := by
  simp [pws, num, step, pw_of_digit _ h1, pw_of_digit _ h2]

theorem zz_digit : Iban.isDigit '0' = true := by decide

/-- `Spec.iban_checkDigits_iff` for a country code of two characters. -/
theorem checkDigits_iff_of_length (country bban ck : List Char) (hc : country.length = 2) :
    Iban.checkDigits country bban = some ck ↔
      ck.length = 2 ∧ (∀ c ∈ ck, Spec.ibanDigit c) ∧
        2 ≤ Spec.ibanNumber ck ∧ Spec.ibanNumber ck ≤ 98 ∧
          Spec.IbanValid (country ++ ck ++ bban) := by
  match country, hc with
  | [c0, c1], _ =>
  have h00 : num (bban ++ [c0, c1] ++ ['0', '0']) = num (bban ++ [c0, c1]) * 100 := by
    rw [num_append, (num_two '0' '0' zz_digit zz_digit).2, (num_two '0' '0' zz_digit zz_digit).1]
    simp [value_of_digit _ zz_digit]
  have hrot : ∀ d1 d2 : Char, (c0 :: c1 :: d1 :: d2 :: bban).drop 4 ++
      (c0 :: c1 :: d1 :: d2 :: bban).take 4 = (bban ++ [c0, c1]) ++ [d1, d2] := by
    intro d1 d2; simp
  have hsh : ∀ d1 d2 : Char, Iban.isDigit d1 = true → Iban.isDigit d2 = true →
      Iban.wellShaped (c0 :: c1 :: d1 :: d2 :: bban) = Iban.wellShaped (c0 :: c1 :: '0' :: '0' :: bban) := by
    intro d1 d2 h1 h2
    apply Bool.eq_iff_iff.mpr
    rw [wellShaped_cons4, wellShaped_cons4]
    simp [h1, h2, zz_digit]
  unfold Iban.checkDigits
  rw [mod97_eq, h00]
  constructor
  · intro h
    split at h
    · rename_i hw'
      have hw := hw'.2
      injection h with h
      subst h
      have hq : (98 - num (bban ++ [c0, c1]) * 100 % 97) / 10 < 10 := by omega
      have ht : (98 - num (bban ++ [c0, c1]) * 100 % 97) % 10 < 10 := by omega
      obtain ⟨dq, tq⟩ := digitChar' _ hq
      obtain ⟨dt, tt⟩ := digitChar' _ ht
      have hok : ∀ c ∈ [Char.ofNat (48 + (98 - num (bban ++ [c0, c1]) * 100 % 97) / 10),
          Char.ofNat (48 + (98 - num (bban ++ [c0, c1]) * 100 % 97) % 10)],
          Iban.isDigit c = true := by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact dq
        · exact dt
      obtain ⟨n2, p2⟩ := num_two _ _ dq dt
      have hn : Spec.ibanNumber [Char.ofNat (48 + (98 - num (bban ++ [c0, c1]) * 100 % 97) / 10),
          Char.ofNat (48 + (98 - num (bban ++ [c0, c1]) * 100 % 97) % 10)] =
          98 - num (bban ++ [c0, c1]) * 100 % 97 := by
        rw [ibanNumber_eq _ (fun c hc => Or.inl (hok c hc)), n2, value_of_digit _ dq,
          value_of_digit _ dt, tq, tt]
        omega
      refine ⟨rfl, fun c hc => (isDigit_digit c).mp (hok c hc), by omega, by omega, ?_⟩
      rw [← valid_spec, valid_iff_num]
      refine ⟨?_, ?_⟩
      · rw [show [c0, c1] ++ _ ++ bban = c0 :: c1 :: _ :: _ :: bban from rfl, hsh _ _ dq dt]
        exact hw
      · rw [show [c0, c1] ++ _ ++ bban = c0 :: c1 :: _ :: _ :: bban from rfl, hrot,
          num_append, n2, p2, value_of_digit _ dq, value_of_digit _ dt, tq, tt]
        omega
    · cases h
  · rintro ⟨hl, hd, h2, h98, hv⟩
    match ck, hl with
    | [d1, d2], _ =>
    have e1 := (isDigit_digit d1).mpr (hd d1 (by simp))
    have e2 := (isDigit_digit d2).mpr (hd d2 (by simp))
    rw [← valid_spec, valid_iff_num,
      show [c0, c1] ++ [d1, d2] ++ bban = c0 :: c1 :: d1 :: d2 :: bban from rfl,
      hsh _ _ e1 e2, hrot, num_append] at hv
    obtain ⟨hw, hm⟩ := hv
    obtain ⟨n2, p2⟩ := num_two _ _ e1 e2
    rw [n2, p2] at hm
    rw [ibanNumber_eq _ (by simp [e1, e2]), n2] at h2 h98
    have v1 := value_of_digit _ e1
    have v2 := value_of_digit _ e2
    have b1 := (isDigit_iff d1).mp e1
    have b2 := (isDigit_iff d2).mp e2
    have hc : 98 - num (bban ++ [c0, c1]) * 100 % 97 = Iban.value d1 * 10 + Iban.value d2 := by
      omega
    rw [ite_eq_left (show [c0, c1].length = 2 ∧ Iban.wellShaped ([c0, c1] ++ ['0', '0'] ++ bban) = true
      from ⟨rfl, hw⟩), hc]
    have q1 : 48 + (Iban.value d1 * 10 + Iban.value d2) / 10 = d1.toNat := by omega
    have q2 : 48 + (Iban.value d1 * 10 + Iban.value d2) % 10 = d2.toNat := by omega
    simp only [q1, q2, Char.ofNat_toNat]

end Codec.Proofs.Iban

open Codec.Proofs.Iban

theorem Spec.iban_valid_iff (s : List Char) : Iban.valid s = true ↔ Spec.IbanValid s :=
  valid_spec s

theorem Spec.iban_checkDigits_iff (country bban ck : List Char) :
    Iban.checkDigits country bban = some ck ↔
      country.length = 2 ∧ ck.length = 2 ∧ (∀ c ∈ ck, Spec.ibanDigit c) ∧
        2 ≤ Spec.ibanNumber ck ∧ Spec.ibanNumber ck ≤ 98 ∧
          Spec.IbanValid (country ++ ck ++ bban) := by
  by_cases hc : country.length = 2
  · simp only [hc, true_and]
    exact checkDigits_iff_of_length country bban ck hc
  · simp only [hc, false_and, iff_false]
    unfold Iban.checkDigits
    simp [hc]

theorem Spec.iban_substitution (l r : List Char) (a b : Char)
    (h : Iban.valid (l ++ a :: r) = true) (hab : a ≠ b)
    (hkind : (Spec.ibanDigit a ∧ Spec.ibanDigit b) ∨ (Spec.ibanLetter a ∧ Spec.ibanLetter b)) :
    Iban.valid (l ++ b :: r) = false := by
  obtain ⟨_, h1⟩ := (valid_iff_num _).mp h
  obtain ⟨hp, hv, ha, hb⟩ := kind_cases a b hab hkind
  have hpw : pw b = pw a := by omega
  obtain ⟨L, R, hLR⟩ := rot_block l [a] r (by simp; omega)
  have e1 : (l ++ a :: r).drop 4 ++ (l ++ a :: r).take 4 = L ++ a :: R := hLR [a] rfl
  have e2 : (l ++ b :: r).drop 4 ++ (l ++ b :: r).take 4 = L ++ b :: R := hLR [b] rfl
  apply valid_false
  rw [e1, num_mid] at h1
  rw [e2, num_mid, hpw]
  intro h2
  have h3 : ((num L * pw a + Iban.value a) * pws R) % 97 =
      ((num L * pw a + Iban.value b) * pws R) % 97 := by omega
  have h4 := cancel_pws R _ _ h3
  omega

theorem Spec.iban_adjacent_swap (l r : List Char) (a b : Char)
    (h : Iban.valid (l ++ a :: b :: r) = true) (hab : a ≠ b)
    (hkind : (Spec.ibanDigit a ∧ Spec.ibanDigit b) ∨ (Spec.ibanLetter a ∧ Spec.ibanLetter b)) :
    Iban.valid (l ++ b :: a :: r) = false := by
  obtain ⟨hs, h1⟩ := (valid_iff_num _).mp h
  obtain ⟨hp, hv, ha, hb⟩ := kind_cases a b hab hkind
  apply valid_false
  intro h2
  by_cases hl : l.length = 3
  · -- the pair straddles the cut: the last check digit and the first BBAN character
    match l, hl with
    | [c0, c1, c2], _ =>
      rw [show [c0, c1, c2] ++ a :: b :: r = c0 :: c1 :: c2 :: a :: b :: r from rfl,
        wellShaped_cons4] at hs
      obtain ⟨_, _, _, da, _, hlen, _⟩ := hs
      have pa : pw a = 10 := pw_of_digit a da
      have hp' : pw b = 10 ∧ Iban.value a < 10 ∧ Iban.value b < 10 := by
        rcases hp with ⟨_, pb, va, vb⟩ | ⟨pa', _⟩
        · exact ⟨pb, va, vb⟩
        · omega
      obtain ⟨pb, va, vb⟩ := hp'
      have r1 : ([c0, c1, c2] ++ a :: b :: r).drop 4 ++ ([c0, c1, c2] ++ a :: b :: r).take 4 =
          b :: ((r ++ [c0, c1, c2]) ++ [a]) := by simp
      have r2 : ([c0, c1, c2] ++ b :: a :: r).drop 4 ++ ([c0, c1, c2] ++ b :: a :: r).take 4 =
          a :: ((r ++ [c0, c1, c2]) ++ [b]) := by simp
      rw [r1, num_cons, num_snoc, pws_append, pa] at h1
      rw [r2, num_cons, num_snoc, pws_append, pb] at h2
      obtain ⟨k, hk, hkl⟩ := pws_pow (r ++ [c0, c1, c2])
      simp only [List.length_append, List.length_cons, List.length_nil] at hkl hlen
      have p1 : pws [a] = 10 := by simp [pws, pa]
      have p2 : pws [b] = 10 := by simp [pws, pb]
      rw [p1] at h1
      rw [p2] at h2
      have hu : (pws (r ++ [c0, c1, c2]) * 10) % 97 ≠ 1 := by
        rw [hk, ← Nat.pow_succ]
        exact pow_ten_ne ⟨k + 1, by omega⟩ (by simp)
      have e1 := mul_mod_right (Iban.value b) (pws (r ++ [c0, c1, c2]) * 10)
      have e2 := mul_mod_right (Iban.value a) (pws (r ++ [c0, c1, c2]) * 10)
      have e3 : (Iban.value b * ((pws (r ++ [c0, c1, c2]) * 10) % 97) + Iban.value a) % 97 =
          (Iban.value a * ((pws (r ++ [c0, c1, c2]) * 10) % 97) + Iban.value b) % 97 := by
        omega
      have := swap_fin ⟨_, Nat.mod_lt _ (by decide)⟩ hu ⟨_, va⟩ ⟨_, vb⟩ e3
      simp only [Fin.mk.injEq] at this
      exact hv this
  · obtain ⟨L, R, hLR⟩ := rot_block l [a, b] r (by simp; omega)
    have e1 : (l ++ a :: b :: r).drop 4 ++ (l ++ a :: b :: r).take 4 = L ++ a :: b :: R :=
      hLR [a, b] rfl
    have e2 : (l ++ b :: a :: r).drop 4 ++ (l ++ b :: a :: r).take 4 = L ++ b :: a :: R :=
      hLR [b, a] rfl
    rw [e1, num_mid2] at h1
    rw [e2, num_mid2] at h2
    rcases hp with ⟨pa, pb, _, _⟩ | ⟨pa, pb⟩
    · rw [pa, pb] at h1 h2
      have h3 : (((num L * 10 + Iban.value a) * 10 + Iban.value b) * pws R) % 97 =
          (((num L * 10 + Iban.value b) * 10 + Iban.value a) * pws R) % 97 := by omega
      have h4 := cancel_pws R _ _ h3
      omega
    · rw [pa, pb] at h1 h2
      have h3 : (((num L * 100 + Iban.value a) * 100 + Iban.value b) * pws R) % 97 =
          (((num L * 100 + Iban.value b) * 100 + Iban.value a) * pws R) % 97 := by omega
      have h4 := cancel_pws R _ _ h3
      omega

theorem Spec.iban_vectors :
    Iban.valid "GB29NWBK60161331926819".toList = true ∧
    Iban.valid "DE89370400440532013000".toList = true ∧
    Iban.valid "FR1420041010050500013M02606".toList = true ∧
    Iban.valid "NO9386011117947".toList = true ∧
    Iban.checkDigits "GB".toList "NWBK60161331926819".toList = some "29".toList ∧
    Iban.checkDigits "NO".toList "86011117947".toList = some "93".toList ∧
    Iban.valid "GB29NWBK60161331926818".toList = false ∧
    Iban.valid "gb29NWBK60161331926819".toList = false ∧
    Iban.valid "FR2130006000010001234B15697".toList = true ∧
    Iban.valid "FR21300060000100012341B5697".toList = true := by
  and_intros <;> decide +kernel
