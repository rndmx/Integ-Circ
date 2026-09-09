/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.System
import IIT.Phi

/-!
# Substrate-independent support

A handful of definitions and lemmas used by the ring development that mention no
particular substrate: the all-ones state, the partition that severs a single unit from
its purview, and two facts about maximal cause purviews and about stated sets.

They are collected here so that the ring files depend on nothing but the core
formalization of IIT 4.0 (the `IIT` package) and this file.
-/

namespace IIT

variable {N : ℕ}

section Common

variable [NeZero N]

/-- The all-ones state. -/
def allOnes : State N := fun _ => true

@[simp] lemma allOnes_apply (i : Fin N) : (allOnes : State N) i = true := rfl

/-- A stated purview lies inside `Z_N` in state all-ones exactly when all its units are
in state `true`. -/
lemma stated_subset_allOnes_iff {Z : Finset (Fin N)} {z : State N} :
    stated Z z ⊆ stated Finset.univ allOnes ↔ ∀ k ∈ Z, z k = true := by
  constructor
  · intro h k hk
    have hmem : (k, z k) ∈ stated Z z := mem_stated.2 ⟨hk, rfl⟩
    exact (mem_stated.1 (h hmem)).2
  · intro h p hp
    rw [mem_stated] at hp ⊢
    exact ⟨Finset.mem_univ _, by rw [hp.2, h p.1 hp.1, allOnes_apply]⟩

/-- Inside `Z_N` in state all-ones, every unit of the purview is stated `true`. -/
lemma mem_stated_allOnes_of_subset {Z : Finset (Fin N)} {z : State N}
    (h : stated Z z ⊆ stated Finset.univ allOnes) {k : Fin N} (hk : k ∈ Z) :
    (k, true) ∈ stated Z z :=
  mem_stated.2 ⟨hk, (stated_subset_allOnes_iff.1 h k hk).symm⟩

/-- The partition severing one mechanism unit `k`: blocks `(M \ {k}, Z)` and `({k}, ∅)`. -/
noncomputable def severOne (M Z : Finset (Fin N)) {k : Fin N} (hk : k ∈ M) :
    Partition N M Z where
  blocks := {(M.erase k, Z), ({k}, ∅)}
  mech_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact Finset.erase_subset k M
    · exact Finset.singleton_subset_iff.2 hk
  purv_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact subset_rfl
    · exact Finset.empty_subset Z
  mech_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_singleton_right.2 (Finset.notMem_erase k M)
    · exact Finset.disjoint_singleton_left.2 (Finset.notMem_erase k M)
    · exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_empty_right Z
    · exact Finset.disjoint_empty_left Z
    · exact absurd rfl hne
  mech_cover := by
    intro i hi
    by_cases hik : i = k
    · exact ⟨({k}, ∅), Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        by rw [hik]; exact Finset.mem_singleton_self k⟩
    · exact ⟨(M.erase k, Z), Finset.mem_insert_self _ _, Finset.mem_erase.2 ⟨hik, hi⟩⟩
  purv_cover := fun j hj => ⟨(M.erase k, Z), Finset.mem_insert_self _ _, hj⟩
  proper := by
    intro b hb hbM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exfalso
      have hbM' : M.erase k = M := hbM
      have hmem : k ∈ M.erase k := by rw [hbM']; exact hk
      exact Finset.notMem_erase k M hmem
    · rfl

lemma severOne_causePart_of_ne (M Z : Finset (Fin N)) {k : Fin N} (hk : k ∈ M) {j : Fin N}
    (hj : j ∈ M) (hjk : j ≠ k) : (severOne M Z hk).causePart j = Z :=
  Partition.causePart_eq (severOne M Z hk) (Finset.mem_insert_self _ _)
    (Finset.mem_erase.2 ⟨hjk, hj⟩)

lemma severOne_causePart_self (M Z : Finset (Fin N)) {k : Fin N} (hk : k ∈ M) :
    (severOne M Z hk).causePart k = ∅ :=
  Partition.causePart_eq (severOne M Z hk)
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Finset.mem_singleton_self k)

lemma pos_logb_half_pow (m : ℕ) :
    pos (Real.logb 2 (1 / (1 / 2 : ℝ) ^ m)) = m := by
  rw [div_pow, one_pow, one_div_one_div, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos, max_eq_right (Nat.cast_nonneg m)]

/-- A maximizing cause purview of a mechanism with `φ_c(m) > 0` has positive `φ_c`. -/
theorem phiCat_pos_of_mem_maxCausePurviews (T : UnitTPM N) (M : Finset (Fin N)) (m : State N)
    (hpos : 0 < phiCmech T Finset.univ M m) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews T Finset.univ M m) : 0 < phiCat T p.1 p.2 M m := by
  obtain ⟨-, hmax⟩ := Finset.mem_filter.1 hp
  refine lt_of_lt_of_le hpos ?_
  rw [phiCmech]
  refine Finset.sup'_le _ _ fun W hW => ?_
  rw [phiCpurview]
  refine Finset.sup'_le _ _ fun w hw => ?_
  exact hmax (W, w) (Finset.mem_biUnion.2 ⟨W, hW, Finset.mem_image_of_mem _ hw⟩)
end Common

end IIT
