/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Damage

/-!
# The arithmetic core of the `D = 3` bound

Once the structural facts are in hand -- at most one big complement-cut block, at most one
`both` unit, and an outputs side that is a single block (or one block plus a singleton) --
the normalizer bound `4·cc ≤ (N-1)² + 8(N-1)` reduces to a single perfect square.

Writing `u` for the size of the one big block and `d = (N-1) - u` for what is left, the
main case is exactly

`4·cc = (N-1)² + 8(N-1) − (u − d)²`,

so the slack is a square and the bound is tight precisely at `u = d = (N-1)/2`: the
extremal `both` singleton / outputs arc / inputs arc.
-/

namespace IIT

open scoped Classical

section Arith

/-- **The main-case bound.**  One big inputs block of size `u`, one `both` singleton, and
one outputs block filling the remaining `N - u - 1` units.  The slack is `(u - d)²`. -/
theorem four_cc_main (N u : ℕ) (hN : 1 ≤ N) (hu : u ≤ N - 1) :
    4 * (u * (N - u) + (N - 1) + (N - u - 1)) ≤ (N - 1) * (N - 1) + 8 * (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hu
  obtain ⟨d, rfl⟩ : ∃ d, M = u + d := ⟨M - u, by omega⟩
  have h1 : u + d + 1 - u = d + 1 := by omega
  rw [h1]
  simp only [Nat.add_sub_cancel]
  zify
  nlinarith [sq_nonneg ((u : ℤ) - (d : ℤ))]

/-- **The split case.**  One big inputs block of size `u`, no `both` unit, one outputs
block and one outputs singleton. -/
theorem four_cc_split (N u : ℕ) (hN : 1 ≤ N) (hu : u ≤ N - 1) :
    4 * (u * (N - u) + 2 * (N - u - 1)) ≤ (N - 1) * (N - 1) + 8 * (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hu
  obtain ⟨d, rfl⟩ : ∃ d, M = u + d := ⟨M - u, by omega⟩
  have h1 : u + d + 1 - u = d + 1 := by omega
  rw [h1]
  simp only [Nat.add_sub_cancel]
  zify
  nlinarith [sq_nonneg ((u : ℤ) - (d : ℤ))]

/-- **The all-singletons case.**  Every complement-cut block is a singleton, so the
normalizer is at most `3(N-1)`, which clears the target once `N ≥ 5`. -/
theorem four_cc_allsingleton (N : ℕ) (hN : 5 ≤ N) :
    4 * (3 * (N - 1)) ≤ (N - 1) * (N - 1) + 8 * (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hM : 4 ≤ M := by omega
  nlinarith [hM]

end Arith

end IIT
