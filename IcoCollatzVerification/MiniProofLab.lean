import Mathlib

/-!
Mini Proof Lab (Phase 6). Twenty small theorems across five categories, used to
establish basic Lean/Mathlib competence before interpreting the target repository's
formalization. Every proof here must compile and be kernel-checked.
-/

namespace MiniProofLab

-- Arithmetic (5)
example : 2 + 2 = 4 := by norm_num
example : 7 * 6 = 42 := by norm_num
example (n : ℕ) : n + 0 = n := by simp
example (a b : ℕ) : a + b = b + a := by ring
example : (10 : ℤ) - 15 = -5 := by norm_num

-- Propositional logic (5)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (p q : Prop) (h : p ∨ q) (hp : p → q) : q := h.elim hp id
example (p : Prop) : p → p := id
example (p q : Prop) (h : p → q) (hnq : ¬q) : ¬p := fun hp => hnq (h hp)
example (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := fun hp => h2 (h1 hp)

-- Induction (5)
example (n : ℕ) : n < n + 1 := by omega
example : ∀ n : ℕ, 2 * n = n + n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => omega
example (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring
example (n : ℕ) : n ≤ n * n + n := by nlinarith
example (n : ℕ) (h : 0 < n) : 1 ≤ n := h

-- Finite / combinatorial (5)
example : (Finset.range 5).card = 5 := by simp
example : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
example (s : Finset ℕ) (h : s.card = 0) : s = ∅ := Finset.card_eq_zero.mp h
example : (Finset.range 4).sum id = 6 := by decide
example (n : ℕ) : (Finset.range n).card = n := Finset.card_range n

-- Mathlib-dependent (5)
example : Nat.Prime 2 := Nat.prime_two
example (a b : ℕ) (h : a ∣ b) (hb : b ≠ 0) : a ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h
example (n : ℕ) : Even (2 * n) := ⟨n, (two_mul n)⟩
example (n : ℕ) (h : Odd n) : ¬ Even n := by
  rw [Nat.odd_iff] at h
  rw [Nat.even_iff]
  omega
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := le_trans h1 h2

end MiniProofLab
