/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantExcl
import CircNet.Common

/-!
# The interval circulant: the system's cause--effect state at all-ones

The system-level counterpart of `CircNet/Circulant.lean`, specialised to the all-ones state.
For the whole substrate `S = Z_N` the window-3 interval circulant is deterministic, and
bijective when `3 ∤ N`, so its system-level effect and cause repertoires are point masses.
All of that is already proved in `CircNet/Circulant.lean` for an *arbitrary* system state
(`sysEffProb_circNet_eq`, `sysUncEff_circNet`, `sysCauseProb_circNet`,
`sysUncCause_circNet`, `sysIiE_circNet`, `sysIiC_circNet`, `sysMaxEffStates_circNet`,
`sysMaxCauseStates_circNet`); this file supplies the missing ingredient -- that all-ones
is a fixed point with itself as unique preimage (`circNext_allOnes`, `circPrev_allOnes`,
`circNext_eq_allOnes_iff`) -- and specialises everything to it.

The upshot is that the system's maximal cause and effect states at all-ones are both
`{allOnes}` (`sysMaxEffStates_circNet_allOnes`, `sysMaxCauseStates_circNet_allOnes`), so
congruence with the system's cause--effect state `[IIT4, Eq 48]` is the statement that
every unit of a stated purview is in state `true` (`congruent_circNet_of_subset`,
`subset_of_congruent_circNet`).

The purview-side lemmas `stated_subset_allOnes_iff` and `mem_stated_allOnes_of_subset`
mention no substrate at all; they live, with the all-ones state itself, in
`CircNet/Common.lean`.
-/

namespace IIT

variable {N : ℕ}

section CircAllOnes

variable [NeZero N]

/-! ## All-ones is a fixed point, and its own unique preimage -/

/-- All-ones is a fixed point of every unit: each window has three units, and the
exclusive-or of three `true`s is `true`. -/
lemma circVal_allOnes (i : Fin N) : circVal i (allOnes : State N) = true := by
  simp [circVal, allOnes]

/-- All-ones is a fixed point of the interval circulant. -/
lemma circNext_allOnes : circNext (allOnes : State N) = allOnes := by
  funext i; simp [circNext, circVal_allOnes]

/-- All-ones is its own preimage (`3 ∤ N`). -/
lemma circPrev_allOnes (h3 : ¬ (3 ∣ N)) : circPrev h3 (allOnes : State N) = allOnes := by
  have h := circPrev_circNext h3 (allOnes : State N)
  rwa [circNext_allOnes] at h

/-- All-ones is the *only* preimage of all-ones (`3 ∤ N`). -/
lemma circNext_eq_allOnes_iff (h3 : ¬ (3 ∣ N)) (t : State N) :
    circNext t = allOnes ↔ t = allOnes := by
  constructor
  · intro h
    exact circNext_injective h3 (h.trans circNext_allOnes.symm)
  · rintro rfl
    exact circNext_allOnes

/-! ## The effect side at all-ones -/

/-- The unpartitioned effect probability at all-ones is the indicator of all-ones. -/
lemma sysEffProb_circNet_allOnes (u t : State N) :
    sysEffProb (circNet N) Finset.univ u allOnes t = if t = allOnes then 1 else 0 := by
  rw [sysEffProb_circNet_eq, circNext_allOnes]

/-- All-ones reproduces itself with probability `1`. -/
lemma sysEffProb_circNet_allOnes_self (u : State N) :
    sysEffProb (circNet N) Finset.univ u allOnes allOnes = 1 := by
  simpa using sysEffProb_circNet_allOnes u (allOnes : State N)

/-- The unconstrained effect probability at all-ones is `1 / 2^N`. -/
lemma sysUncEff_circNet_allOnes (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysUncEff (circNet N) Finset.univ u (allOnes : State N) = 1 / 2 ^ N :=
  sysUncEff_circNet h3 u allOnes

/-! ## The cause side at all-ones -/

/-- The system cause probability at all-ones is the indicator of all-ones: it is the only
state producing all-ones. -/
lemma sysCauseProb_circNet_allOnes (h3 : ¬ (3 ∣ N)) (u t : State N) :
    sysCauseProb (circNet N) Finset.univ u allOnes t = if t = allOnes then 1 else 0 := by
  rw [sysCauseProb_circNet h3, circPrev_allOnes h3]

/-- The unconstrained cause probability at all-ones is `1 / 2^N`. -/
lemma sysUncCause_circNet_allOnes (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysUncCause (circNet N) Finset.univ u (allOnes : State N) = 1 / 2 ^ N :=
  sysUncCause_circNet h3 u allOnes

/-! ## Intrinsic information and the maximal states -/

/-- `ii_e` at all-ones is `N` bits on all-ones and `0` elsewhere. -/
lemma sysIiE_circNet_allOnes (h3 : ¬ (3 ∣ N)) (u t : State N) :
    sysIiE (circNet N) Finset.univ u allOnes t = if t = allOnes then (N : ℝ) else 0 := by
  rw [sysIiE_circNet h3, circNext_allOnes]

/-- `ii_c` at all-ones is `N` bits on all-ones and `0` elsewhere. -/
lemma sysIiC_circNet_allOnes (h3 : ¬ (3 ∣ N)) (u t : State N) :
    sysIiC (circNet N) Finset.univ u allOnes t = if t = allOnes then (N : ℝ) else 0 := by
  rw [sysIiC_circNet h3, circPrev_allOnes h3]

/-- **The system's maximal effect state at all-ones is all-ones.** -/
theorem sysMaxEffStates_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysMaxEffStates (circNet N) Finset.univ u allOnes = {allOnes} := by
  rw [sysMaxEffStates_circNet h3 hN, circNext_allOnes]

/-- **The system's maximal cause state at all-ones is all-ones.** -/
theorem sysMaxCauseStates_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysMaxCauseStates (circNet N) Finset.univ u allOnes = {allOnes} := by
  rw [sysMaxCauseStates_circNet h3 hN, circPrev_allOnes h3]

/-! ## Stated purviews and congruence -/

/-- The system's stated cause at all-ones is the single purview `Z_N` in state all-ones. -/
lemma sysStatedCause_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysStatedCause (circNet N) Finset.univ u allOnes = {stated Finset.univ allOnes} := by
  rw [sysStatedCause, sysMaxCauseStates_circNet_allOnes hN h3, Finset.image_singleton]

/-- The system's stated effect at all-ones is the single purview `Z_N` in state all-ones. -/
lemma sysStatedEffect_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) :
    sysStatedEffect (circNet N) Finset.univ u allOnes = {stated Finset.univ allOnes} := by
  rw [sysStatedEffect, sysMaxEffStates_circNet_allOnes hN h3, Finset.image_singleton]

/-- **Congruence at all-ones, sufficiency**: stated purviews inside `Z_N` in state
all-ones are congruent with the system's cause--effect state. -/
theorem congruent_circNet_of_subset (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    {zc ze : StatedPurview N} (hc : zc ⊆ stated Finset.univ allOnes)
    (he : ze ⊆ stated Finset.univ allOnes) :
    Congruent (circNet N) Finset.univ u allOnes zc ze := by
  refine ⟨⟨stated Finset.univ allOnes, ?_, hc⟩, ⟨stated Finset.univ allOnes, ?_, he⟩⟩
  · rw [sysStatedCause_circNet_allOnes hN h3]
    exact Finset.mem_singleton_self _
  · rw [sysStatedEffect_circNet_allOnes hN h3]
    exact Finset.mem_singleton_self _

/-- **Congruence at all-ones, necessity**: a congruent pair of stated purviews lies inside
`Z_N` in state all-ones on both sides. -/
theorem subset_of_congruent_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    {zc ze : StatedPurview N} (h : Congruent (circNet N) Finset.univ u allOnes zc ze) :
    zc ⊆ stated Finset.univ allOnes ∧ ze ⊆ stated Finset.univ allOnes := by
  obtain ⟨⟨c, hc, hzc⟩, ⟨e, he, hze⟩⟩ := h
  rw [sysStatedCause_circNet_allOnes hN h3, Finset.mem_singleton] at hc
  rw [sysStatedEffect_circNet_allOnes hN h3, Finset.mem_singleton] at he
  subst hc
  subst he
  exact ⟨hzc, hze⟩

end CircAllOnes

end IIT
