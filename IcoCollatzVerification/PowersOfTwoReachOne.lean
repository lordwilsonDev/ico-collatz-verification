import Mathlib

/-!
A "soft" demonstration problem for the verifying-lean-proofs skill: every
power of two reaches 1 under the standard (uncompressed) Collatz map. This is
a genuinely easy induction, deliberately chosen to have a small dependency
closure so the full pipeline (kernel + independent checker) completes
end-to-end without hitting the large-closure exporter stall found while
auditing eliahou-collatz-bounds.
-/

/-- The standard (uncompressed) Collatz step: n/2 if even, 3n+1 if odd. -/
def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Every power of two reaches 1 in finitely many Collatz steps. -/
theorem powers_of_two_reach_one : ∀ k : ℕ, ∃ m : ℕ, (collatzStep^[m]) (2 ^ k) = 1 := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    have hstep : collatzStep (2 ^ (n + 1)) = 2 ^ n := by
      unfold collatzStep
      have heven : (2 : ℕ) ^ (n + 1) % 2 = 0 := by
        rw [pow_succ]; omega
      simp only [heven, ite_true]
      rw [pow_succ]
      omega
    rw [Function.iterate_succ, Function.comp_apply, hstep, hm]
