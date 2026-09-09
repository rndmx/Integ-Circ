/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantWitness

/-!
# `φ_s ≥ 3` for the window-3 circulant

The assembly.  The three-arc witness with `k = (N+1)/3` has damage at most four and a
quadratic normalizer, so its normalized ratio is below both `1/(N-1)` and `8/N²`.  By the
`D = 1` and `D = 2` classifications those are floors for every partition damaging at most
two units, so no such partition reaches the minimum information partition set, and the
`[IIT4, p.18]` tie rule returns at least three.

This is the whole-substrate half of `[IIT4, Eq 26]`'s exclusion, for every `N ≥ 7` with
`3 ∤ N`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Main

variable [NeZero N]

/-- **`φ_s ≥ 3` for the whole substrate**, for every `N ≥ 7` with `3 ∤ N`, in every
state. -/
theorem three_le_sysPhi_circNet (h3 : ¬ (3 ∣ N)) (hN : 7 ≤ N) (u s : State N) :
    3 ≤ sysPhi (circNet N) Finset.univ u s := by
  classical
  have hmod : N % 3 = 1 ∨ N % 3 = 2 := by
    have hz : N % 3 = 0 → False := fun hm => h3 (Nat.dvd_of_mod_eq_zero hm)
    omega
  -- the witness parameters
  have hk2 : 2 ≤ (N + 1) / 3 := by omega
  have hkN : 3 * ((N + 1) / 3) = N - 1 ∨ 3 * ((N + 1) / 3) = N + 1 := by omega
  have ha : 0 < N - 2 * ((N + 1) / 3) := by omega
  have hsum : (N - 2 * ((N + 1) / 3)) + (N + 1) / 3 + (N + 1) / 3 = N := by omega
  set k := (N + 1) / 3 with hkdef
  set a := N - 2 * k with hadef
  have hDw := damagedCount_threeArc_le (N := N) (a := a) (k := k) ha hk2 hsum
  have hccw := sysCutCount_threeArc (N := N) (a := a) (k := k) ha hk2 hsum
  -- the two arithmetic facts that starve `D ≤ 2` out of the argmin
  have hA : 4 * (N - 1) < sysCutCount (threeArc a k ha hk2 hsum) := by
    rw [hccw]
    rcases hkN with h | h
    · -- `N = 3k + 1`, `a = k + 1`
      have hak : a = k + 1 := by omega
      have hNk : N - k = 2 * k + 1 := by omega
      have hN1 : N - 1 = 3 * k := by omega
      rw [hak, hNk, hN1]
      have hkk : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk2
      nlinarith [hkk]
    · -- `N = 3k - 1` and `N ≥ 8` force `k ≥ 3`; substitute `k = j + 1`
      have hk3 : 3 ≤ k := by omega
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj2 : 2 ≤ j := by omega
      have hak : a = j := by omega
      have hNk : N - k = 2 * j + 1 := by omega
      have hN1 : N - 1 = 3 * j + 1 := by omega
      rw [hak, hNk, hN1, hj]
      have hjj : 2 * j ≤ j * j := Nat.mul_le_mul_right j hj2
      nlinarith [hjj]
  have hB : N * N < 2 * sysCutCount (threeArc a k ha hk2 hsum) := by
    rw [hccw]
    rcases hkN with h | h
    · have hak : a = k + 1 := by omega
      have hNk : N - k = 2 * k + 1 := by omega
      have hNe : N = 3 * k + 1 := by omega
      rw [hak, hNk, hNe]
      have hkk : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk2
      nlinarith [hkk]
    · have hk3 : 3 ≤ k := by omega
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj2 : 2 ≤ j := by omega
      have hak : a = j := by omega
      have hNk : N - k = 2 * j + 1 := by omega
      have hNe : N = 3 * j + 2 := by omega
      rw [hak, hNk, hNe, hj]
      have hjj : 2 * j ≤ j * j := Nat.mul_le_mul_right j hj2
      nlinarith [hjj]
  -- positivity, in `ℝ`
  have hccw_pos : 0 < sysCutCount (threeArc a k ha hk2 hsum) := by omega
  rw [sysPhi_circNet h3 (by omega : 3 ≤ N)]
  haveI hne : Nonempty (SysPartition N Finset.univ) := ⟨threeArc a k ha hk2 hsum⟩
  obtain ⟨θs, hθs⟩ := argminSet_nonempty
    (fun θ : SysPartition N Finset.univ => (damagedCount θ : ℝ) / (sysCutCount θ : ℝ))
  have hstar := (mem_argminSet.1 hθs) (threeArc a k ha hk2 hsum)
  -- the argmin damages at least three units
  have h3D : 3 ≤ damagedCount θs := by
    by_contra hlt
    have h1D := one_le_damagedCount θs
    have hccs_pos : 0 < sysCutCount θs := sysCutCount_pos θs
    have hccwR : (0 : ℝ) < (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) := by
      exact_mod_cast hccw_pos
    have hccsR : (0 : ℝ) < (sysCutCount θs : ℝ) := by exact_mod_cast hccs_pos
    -- the witness ratio is at most `4 / ccw`
    have hup : (damagedCount (threeArc a k ha hk2 hsum) : ℝ)
        / (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
        ≤ 4 / (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) := by
      gcongr
      exact_mod_cast hDw
    have hchain := hstar.trans hup
    have hDval : damagedCount θs = 1 ∨ damagedCount θs = 2 := by omega
    rcases hDval with hD | hD
    · -- `D = 1`
      have hcc1 := sysCutCount_eq_of_damagedCount_one (by omega : 3 ≤ N) θs hD
      rw [hD, hcc1] at hchain
      have hN1R : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
        ring
      rw [hN1R] at hchain
      have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      rw [div_le_div_iff₀ hN1pos hccwR] at hchain
      have : (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) ≤ 4 * ((N : ℝ) - 1) := by
        push_cast at hchain ⊢
        linarith
      have hcast : (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) ≤ ((4 * (N - 1) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
        linarith
      have := (Nat.cast_le (α := ℝ)).1 hcast
      omega
    · -- `D = 2`
      rcases sysCutCount_of_damagedCount_two (by omega : 3 ≤ N) θs hD with hcc | hcc
      · rw [hD, hcc] at hchain
        have h2N : ((2 * (N - 1) : ℕ) : ℝ) = 2 * ((N : ℝ) - 1) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
          ring
        rw [h2N] at hchain
        have hN1pos : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by
          have : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        rw [div_le_div_iff₀ hN1pos hccwR] at hchain
        have hcast : (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
            ≤ ((4 * (N - 1) : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at hchain ⊢
          linarith
        have := (Nat.cast_le (α := ℝ)).1 hcast
        omega
      · rw [hD] at hchain
        rw [div_le_div_iff₀ hccsR hccwR] at hchain
        push_cast at hchain
        -- `2 · ccw ≤ 4 · cc* ≤ N²`, contradicting `N² < 2 · ccw`
        have hchain' : 2 * (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
            ≤ 4 * (sysCutCount θs : ℝ) := by linarith
        have hcast : ((2 * sysCutCount (threeArc a k ha hk2 hsum) : ℕ) : ℝ)
            ≤ ((4 * sysCutCount θs : ℕ) : ℝ) := by push_cast; linarith
        have hle := (Nat.cast_le (α := ℝ)).1 hcast
        omega
  refine le_trans ?_ (le_sup'OrZero hθs)
  exact_mod_cast h3D

end Main

end IIT
