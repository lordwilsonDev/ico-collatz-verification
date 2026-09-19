import Mathlib

example : 1 + 1 = 2 := by
  norm_num

example (n : ℕ) : n + 0 = n := by
  simp
