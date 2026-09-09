/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Arith

/-!
# The master arithmetic of the `D = 3` bound

The normalizer of a partition damaging three units decomposes exactly as

`cc = u(N-u) + m(N-1) + b·o + e`

with `u` the size of the unique big complement-cut block, `m` the number of complement-cut
singletons, `b` the size of the `both` region, `o` the size of the outputs region, and `e`
the outputs excess `o² - Σ|q|²`.

This file proves that the structural constraints force `4·cc ≤ (N-1)² + 8(N-1)`, which is
`4·f(N)`.  Two constraints do the real work, and a numerical experiment identified both:
a `both` region of size at least two forces the outputs region down to a single unit, and
a positive excess forces the `both` region to vanish.  They are mutually exclusive, and
that exclusion is what makes the bound hold.

Everything is phrased in the subtraction-free variables `u, m, o` with `N = u + m + o`, so
`N - u = m + o` and `S := N - 1` satisfies `u + m + o = S + 1`.
-/

namespace IIT

open scoped Classical

section Master

/-- No big block, no excess: at most three singletons and the interface term. -/
lemma d3_nobig_noexc (S m o b : ℕ) (hS : 7 ≤ S) (hm : m ≤ 3) (hsum : m + o = S + 1)
    (hb : b * o ≤ o) : 4 * (m * S + b * o) ≤ S * S + 8 * S := by
  zify at *
  nlinarith [hS, hm, hb, hsum, Nat.zero_le m, Nat.zero_le o]

/-- One big block, no singleton, no excess. -/
lemma d3_big_m0_noexc (S u o b : ℕ) (hS : 7 ≤ S) (hsum : u + o = S + 1)
    (hb : b * o ≤ o) : 4 * (u * o + b * o) ≤ S * S + 8 * S := by
  zify at *
  nlinarith [hS, hb, hsum, sq_nonneg ((u : ℤ) - o), Nat.zero_le u, Nat.zero_le o]

/-- One big block and one singleton, no excess: the extremal shape. -/
lemma d3_big_m1_noexc (S u o b : ℕ) (hS : 7 ≤ S) (hsum : u + 1 + o = S + 1)
    (hb : b * o ≤ o) : 4 * (u * (1 + o) + 1 * S + b * o) ≤ S * S + 8 * S := by
  zify at *
  nlinarith [hS, hb, hsum, sq_nonneg ((u : ℤ) - o), Nat.zero_le u, Nat.zero_le o]

/-- A `both` region of size at least two: the outputs region is a single unit. -/
lemma d3_bigb (S u m o b : ℕ) (hS : 7 ≤ S) (hm : m ≤ 1) (ho : o ≤ 1)
    (hsum : u + m + o = S + 1) (hble : b ≤ u + m) (hbo : b * o ≤ b) :
    4 * (u * (m + o) + m * S + b * o) ≤ S * S + 8 * S := by
  zify at *
  nlinarith [hS, hm, ho, hbo, hble, hsum, Nat.zero_le u, Nat.zero_le b]

/-- Positive excess, no big block: at most two singletons and the excess. -/
lemma d3_exc_nobig (S m o e : ℕ) (hS : 7 ≤ S) (hm : m ≤ 2) (hsum : m + o = S + 1)
    (hopos : 0 < o) (he : e ≤ 2 * (o - 1)) : 4 * (m * S + e) ≤ S * S + 8 * S := by
  have ho1 : o - 1 + 1 = o := by omega
  zify [show 1 ≤ o by omega] at *
  nlinarith [hS, hm, he, hsum, sq_nonneg ((S : ℤ) - 4), Nat.zero_le m]

/-- Positive excess with a big block: no singleton is affordable. -/
lemma d3_exc_big (S u o e : ℕ) (hS : 7 ≤ S) (hsum : u + o = S + 1)
    (hopos : 0 < o) (he : e ≤ 2 * (o - 1)) :
    4 * (u * o + e) ≤ S * S + 8 * S := by
  zify [show 1 ≤ o by omega] at *
  -- slack is `(2o - (S+3))² + (2S - 1)`
  nlinarith [hS, he, hsum, sq_nonneg (2 * (o : ℤ) - ((S : ℤ) + 3))]

/-- **The master bound.**  All five parameters, all six constraints, one conclusion. -/
theorem d3_master (N u m b o e : ℕ)
    (hN : 8 ≤ N)
    (hu : u = 0 ∨ 2 ≤ u)
    (hm : m ≤ 3)
    (hum : 2 ≤ u → m ≤ 1)
    (hsum : u + m + o = N)
    (hble : b ≤ u + m)
    (hb2 : 2 ≤ b → o ≤ 1 ∧ e = 0)
    (he : 0 < o → e ≤ 2 * (o - 1))
    (he2a : 0 < e → b = 0)
    (he2b : 0 < e → 2 ≤ u → m = 0)
    (he2c : 0 < e → u = 0 → m ≤ 2)
    (heo : 0 < e → 0 < o) :
    4 * (u * (N - u) + m * (N - 1) + b * o + e)
      ≤ (N - 1) * (N - 1) + 8 * (N - 1) := by
  obtain ⟨S, rfl⟩ : ∃ S, N = S + 1 := ⟨N - 1, by omega⟩
  have hS : 7 ≤ S := by omega
  have hNu : S + 1 - u = m + o := by omega
  have hS1 : S + 1 - 1 = S := by omega
  rw [hNu, hS1]
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · -- no excess
    rcases Nat.lt_or_ge b 2 with hb1 | hb2'
    · have hbo : b * o ≤ o := by
        rcases Nat.lt_or_ge b 1 with h | h
        · simp [show b = 0 by omega]
        · simpa [show b = 1 by omega] using le_refl o
      rcases hu with rfl | hu2
      · simpa using d3_nobig_noexc S m o b hS hm (by omega) hbo
      · have hm1 : m ≤ 1 := hum hu2
        interval_cases m
        · simpa using d3_big_m0_noexc S u o b hS (by omega) hbo
        · simpa using d3_big_m1_noexc S u o b hS (by omega) hbo
    · obtain ⟨ho1, -⟩ := hb2 hb2'
      have hbo : b * o ≤ b := by
        rcases Nat.eq_zero_or_pos o with rfl | hopos
        · simp
        · simpa [show o = 1 by omega] using le_refl b
      rcases hu with rfl | hu2
      · omega
      · exact d3_bigb S u m o b hS (hum hu2) ho1 (by omega) hble hbo
  · -- positive excess
    have hb0 := he2a hepos
    subst hb0
    have hopos : 0 < o := heo hepos
    have hee : e ≤ 2 * (o - 1) := he hopos
    rcases hu with rfl | hu2
    · simpa using d3_exc_nobig S m o e hS (he2c hepos rfl) (by omega) hopos hee
    · have hm0 : m = 0 := he2b hepos hu2
      have hsum' : u + o = S + 1 := by omega
      have hmain := d3_exc_big S u o e hS hsum' hopos hee
      rw [hm0]
      simpa using hmain

end Master

end IIT
