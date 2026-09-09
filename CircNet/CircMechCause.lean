/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CircSys
import CircNet.Common

/-!
# The interval circulant: the cause side of a mechanism at all-ones

The cause side of an arbitrary mechanism `M` of the window-3 interval circulant `circNet`
at the all-ones state, with cause purview the whole substrate, plus the **hull lemma** and
the description of the maximizing cause purviews.  The window is `inputs` of `CircNet/Circulant.lean`.

* **Whole-substrate purview.**  Conditioning on the whole substrate pins every unit, so
  `causeFwd` is an indicator, `uncCauseFwd` is `2^{-|M|}` (bijectivity, `3 ∤ N`), and
  `causeRep` is `2^{|M| - N}` on the fibre `{z | circVal k z = m k ∀ k ∈ M}` and `0` off
  it.  Every fibre state is a maximal cause state, and `iiC` there equals
  `2^{|M|-N} |M|`.
* **Partitions.**  For `θ : Partition N M univ` the partitioned cause repertoire at a fibre
  state is `(1/2)^L(θ)` with `L(θ)` the number of mechanism units whose window is not
  contained in their retained purview part; hence `φ_c(θ) = 2^{|M|-N} L(θ)`.
* **The hull lemma.**  Severing one mechanism unit `k` whose window is not inside the
  purview `Z` (`severOne`, from `CircNet/Common.lean`: it mentions no substrate) leaves the cause repertoire unchanged, so `φ_c` at that partition is `0`, so
  the MIP has `φ_c = 0`: a positive `φ_c` forces every window of `M` into `Z`.
* **Maximizing cause purviews.**  When the windows of `M` cover the substrate and
  `φ_c(m) > 0`, every maximizing cause purview is the whole substrate paired with a fibre
  state, and `(univ, allOnes)` is one of them.  In general -- covering or not -- a
  maximizing cause purview *contains the mechanism* (`mem_of_mem_maxCausePurviews`),
  since a unit lies in its own window; that is what puts a chosen unit of `M` into the
  support of the distinction.

The floor delivered here is `(1/2)^(N - |M|) ≤ φ_c(M)`, which is what the arc family uses.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

/-! ## The window as a `Finset`, and the effect repertoire of one unit -/

section Window

variable [NeZero N]

lemma mem_inputs {j k : Fin N} :
    k ∈ inputs j ↔ k = j ∨ k = shift j ∨ k = shift (shift j) := by
  unfold inputs
  simp

lemma self_mem_inputs (j : Fin N) : j ∈ inputs j := mem_inputs.2 (Or.inl rfl)

lemma shift_mem_inputs (j : Fin N) : shift j ∈ inputs j := mem_inputs.2 (Or.inr (Or.inl rfl))

lemma shift_shift_mem_inputs (j : Fin N) : shift (shift j) ∈ inputs j :=
  mem_inputs.2 (Or.inr (Or.inr rfl))

/-- Flipping the unit itself flips its next value: it occurs once in its own window. -/
lemma circVal_flipAt_self (hN : 3 ≤ N) (j : Fin N) (s : State N) :
    circVal j (flipAt j s) = !(circVal j s) := by
  rw [circVal, circVal, flipAt_apply_self,
    flipAt_apply_of_ne (shift_ne_self hN j) s,
    flipAt_apply_of_ne (shift_shift_ne_self hN j) s]
  cases s j <;> cases s (shift j) <;> cases s (shift (shift j)) <;> simp

/-- **Flipping any member of the window flips the unit's next value.** -/
lemma circVal_flipAt_window (hN : 3 ≤ N) {j k : Fin N} (hk : k ∈ inputs j) (s : State N) :
    circVal j (flipAt k s) = !(circVal j s) := by
  rcases mem_inputs.1 hk with h | h | h
  · rw [h]; exact circVal_flipAt_self hN j s
  · rw [h]; exact circVal_flipAt_shift hN j s
  · rw [h]; exact circVal_flipAt_shift_shift hN j s

/-- **A conditioning set containing the whole window determines the unit.** -/
theorem effUnit_circNet_of_inputs_subset (W : Finset (Fin N)) (m : State N) (j : Fin N)
    (b : Bool) (h : inputs j ⊆ W) :
    effUnit (circNet N) W m j b = if b = circVal j m then 1 else 0 :=
  effUnit_circNet_of_window_subset W m j b (h (self_mem_inputs j)) (h (shift_mem_inputs j))
    (h (shift_shift_mem_inputs j))

/-- **Omitting any window member halves `effUnit`.**  Flipping that member is an involution
of the marginalization fibre which flips the unit's next state, so exactly half the fibre
gives each value.  This strengthens `effUnit_circNet_of_not_mem`, which asks the omitted
unit to be a *live* input; here it may be the unit itself. -/
theorem effUnit_circNet_of_not_inputs_subset (hN : 3 ≤ N) (W : Finset (Fin N)) (m : State N)
    (j : Fin N) (b : Bool) (h : ¬ inputs j ⊆ W) :
    effUnit (circNet N) W m j b = 1 / 2 := by
  classical
  obtain ⟨k, hkI, hkW⟩ := Finset.not_subset.1 h
  have hbne : ∀ c : Bool, ¬ (c = !c) := by decide
  have hbnot : ∀ c d : Bool, ¬ (c = d) → c = !d := by decide
  have hmaps : ∀ s ∈ agree W m, flipAt k s ∈ agree W m := by
    intro s hs
    rw [mem_agree] at hs ⊢
    intro i hi
    rw [flipAt_apply_of_ne (by rintro rfl; exact hkW hi) s]
    exact hs i hi
  have hsum : ∑ s ∈ agree W m, (circNet N).prob j s b
      = ((((agree W m).filter fun s => b = circVal j s)).card : ℝ) := by
    rw [← Finset.sum_boole]
    rfl
  have hbij : (((agree W m).filter fun s => b = circVal j s)).card
      = (((agree W m).filter fun s => ¬ (b = circVal j s))).card := by
    refine Finset.card_nbij' (flipAt k) (flipAt k) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [circVal_flipAt_window hN hkI s, ← hs.2]
      exact hbne b
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [circVal_flipAt_window hN hkI s]
      exact hbnot _ _ hs.2
    · intro s _; exact flipAt_flipAt k s
    · intro s _; exact flipAt_flipAt k s
  have htot := Finset.card_filter_add_card_filter_not (s := agree W m)
    (fun s => b = circVal j s)
  have hcpos : 0 < (agree W m).card := Finset.card_pos.2 (agree_nonempty W m)
  have hc : (agree W m).card
      = 2 * (((agree W m).filter fun s => b = circVal j s)).card := by omega
  have h1 : (0 : ℝ) < ((((agree W m).filter fun s => b = circVal j s)).card : ℝ) := by
    have hp : 0 < (((agree W m).filter fun s => b = circVal j s)).card := by omega
    exact_mod_cast hp
  rw [effUnit, hsum, hc]
  push_cast
  field_simp

end Window

/-! ## The counting lemma

The image of the dynamics is uniform on every cylinder set: the states whose successor
agrees with `z` on `Z` are the preimage of `agree Z z` under a bijection. -/

section Counting

variable [NeZero N]

/-- **Uniformity of the image.** -/
theorem card_filter_circNext_agree (h3 : ¬ (3 ∣ N)) (Z : Finset (Fin N)) (z : State N) :
    (Finset.univ.filter fun s : State N => ∀ k ∈ Z, circNext s k = z k).card
      = 2 ^ (N - Z.card) := by
  classical
  have hbij : Function.Bijective (circNext : State N → State N) :=
    Finite.injective_iff_bijective.1 (circNext_injective h3)
  rw [← card_agree Z z]
  refine Finset.card_bij (fun s _ => circNext s) ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact mem_agree.2 hs.2
  · intro s₁ _ s₂ _ heq
    exact circNext_injective h3 heq
  · intro t ht
    obtain ⟨s, hs⟩ := hbij.surjective t
    refine ⟨s, ?_, hs⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hs]
    exact mem_agree.1 ht

/-- The same count as a real sum of indicators. -/
lemma sum_ite_circNext_agree (h3 : ¬ (3 ∣ N)) (Z : Finset (Fin N)) (z : State N) :
    ∑ s : State N, (if ∀ k ∈ Z, circNext s k = z k then (1 : ℝ) else 0)
      = (2 : ℝ) ^ (N - Z.card) := by
  rw [Finset.sum_boole, card_filter_circNext_agree h3 Z z]
  push_cast
  rfl

end Counting

/-! ## The cause side with the whole substrate as purview -/

section CauseUniv

variable [NeZero N]

/-- Conditioning on the whole substrate pins every unit. -/
lemma effUnit_circNet_univ (z : State N) (j : Fin N) (b : Bool) :
    effUnit (circNet N) Finset.univ z j b = if b = circVal j z then 1 else 0 :=
  effUnit_circNet_of_inputs_subset _ _ _ _ (Finset.subset_univ _)

/-- The forward cause probability from the whole substrate is an indicator. -/
theorem causeFwd_circNet_univ (M : Finset (Fin N)) (m z : State N) :
    causeFwd (circNet N) Finset.univ z M m
      = if (∀ k ∈ M, circVal k z = m k) then 1 else 0 := by
  rw [causeFwd_eq]
  by_cases h : ∀ k ∈ M, circVal k z = m k
  · rw [if_pos h]
    refine Finset.prod_eq_one fun k hk => ?_
    rw [effUnit_circNet_univ, if_pos (h k hk).symm]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨k, hk, hne⟩ := h
    refine Finset.prod_eq_zero hk ?_
    rw [effUnit_circNet_univ, if_neg (fun h' => hne h'.symm)]

/-- The unconstrained cause probability is `2^{-|M|}`: the dynamics is a bijection, so the
fibre over `m` on `M` has exactly `2^{N-|M|}` states. -/
theorem uncCauseFwd_circNet_univ (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N)) (m : State N) :
    uncCauseFwd (circNet N) Finset.univ M m = (1 / 2 : ℝ) ^ M.card := by
  have hMN : M.card ≤ N := by simpa using Finset.card_le_univ M
  rw [uncCauseFwd, avgOverStates,
    Finset.sum_congr rfl fun z _ => causeFwd_circNet_univ M m z]
  have hsum : (∑ z : State N, (if ∀ k ∈ M, circVal k z = m k then (1 : ℝ) else 0))
      = (2 : ℝ) ^ (N - M.card) :=
    sum_ite_circNext_agree h3 M m
  rw [hsum, div_pow, one_pow, div_eq_div_iff (by positivity) (by positivity), one_mul,
    ← pow_add, Nat.sub_add_cancel hMN]

/-- The Bayes cause repertoire from the whole substrate. -/
theorem causeRep_circNet_univ (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N)) (m z : State N) :
    causeRep (circNet N) Finset.univ z M m
      = (if (∀ k ∈ M, circVal k z = m k) then 1 else 0) * (1 / 2 : ℝ) ^ (N - M.card) := by
  have hMN : M.card ≤ N := by simpa using Finset.card_le_univ M
  rw [causeRep, causeFwd_circNet_univ, uncCauseFwd_circNet_univ h3, Finset.card_univ,
    Fintype.card_fin]
  have key : ((2 : ℝ) ^ N * (1 / 2 : ℝ) ^ M.card) = (2 : ℝ) ^ (N - M.card) := by
    rw [pow_sub₀ _ (by norm_num) hMN, div_pow, one_pow, one_div]
  rw [key, div_pow, one_pow, ← div_eq_mul_one_div]

/-- Intrinsic cause information from the whole substrate. -/
theorem iiC_circNet_univ (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N)) (m z : State N) :
    iiC (circNet N) M m Finset.univ z
      = if (∀ k ∈ M, circVal k z = m k) then (1 / 2 : ℝ) ^ (N - M.card) * M.card else 0 := by
  rw [iiC, causeRep_circNet_univ h3, causeFwd_circNet_univ, uncCauseFwd_circNet_univ h3]
  by_cases h : ∀ k ∈ M, circVal k z = m k
  · simp only [if_pos h]
    rw [one_mul]
    congr 1
    rw [div_pow, one_pow, one_div_one_div, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
      mul_one]
  · simp only [if_neg h]
    rw [zero_mul, zero_mul]

lemma circVal_allOnes_eq_allOnes (M : Finset (Fin N)) :
    ∀ k ∈ M, circVal k (allOnes : State N) = allOnes k :=
  fun k _ => by rw [circVal_allOnes, allOnes_apply]

lemma circVal_allOnes_eq_true (M : Finset (Fin N)) :
    ∀ k ∈ M, circVal k (allOnes : State N) = true :=
  fun k _ => circVal_allOnes k

/-- All-ones is a maximal cause state of every mechanism at all-ones. -/
theorem allOnes_mem_maxCauseStates_circNet_univ (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N)) :
    allOnes ∈ maxCauseStates (circNet N) M allOnes Finset.univ := by
  rw [maxCauseStates, mem_argmaxSet]
  intro z
  rw [iiC_circNet_univ h3, iiC_circNet_univ h3, if_pos (circVal_allOnes_eq_allOnes M)]
  split_ifs
  · exact le_rfl
  · positivity

/-- The maximal cause states of a nonempty mechanism at all-ones are exactly the fibre. -/
theorem mem_maxCauseStates_circNet_univ_iff (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    (hM : M.Nonempty) (z : State N) :
    z ∈ maxCauseStates (circNet N) M allOnes Finset.univ ↔ ∀ k ∈ M, circVal k z = true := by
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (N - M.card) * M.card := by
    have : (0 : ℝ) < M.card := by exact_mod_cast Finset.card_pos.2 hM
    positivity
  rw [maxCauseStates, mem_argmaxSet]
  constructor
  · intro h
    have h1 := h allOnes
    rw [iiC_circNet_univ h3, iiC_circNet_univ h3, if_pos (circVal_allOnes_eq_allOnes M)] at h1
    by_contra hz
    rw [if_neg (fun h' => hz (fun k hk => (h' k hk).trans (allOnes_apply k)))] at h1
    linarith
  · intro hz w
    rw [iiC_circNet_univ h3, iiC_circNet_univ h3,
      if_pos (fun k hk => (hz k hk).trans (allOnes_apply k).symm)]
    split_ifs
    · exact le_rfl
    · exact hpos.le

/-- The partitioned cause repertoire at a fibre state: one factor `1/2` per mechanism unit
whose window is not inside its retained purview part. -/
theorem partCauseFwd_circNet_univ (hN : 3 ≤ N) (M : Finset (Fin N))
    (θ : Partition N M Finset.univ) {z : State N} (hz : ∀ k ∈ M, circVal k z = true) :
    partCauseFwd (circNet N) Finset.univ z M allOnes θ
      = (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ θ.causePart k).card := by
  rw [partCauseFwd]
  have hterm : ∀ k ∈ M, effUnit (circNet N) (θ.causePart k) z k (allOnes k)
      = if inputs k ⊆ θ.causePart k then 1 else (1 / 2 : ℝ) := by
    intro k hk
    by_cases h : inputs k ⊆ θ.causePart k
    · rw [if_pos h, effUnit_circNet_of_inputs_subset _ _ _ _ h, allOnes_apply, hz k hk,
        if_pos rfl]
    · rw [if_neg h, effUnit_circNet_of_not_inputs_subset hN _ _ _ _ h]
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]

/-- `φ_c` at a partition, at all-ones with the whole substrate as purview. -/
theorem phiCofPartition_circNet_univ (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    (θ : Partition N M Finset.univ) :
    phiCofPartition (circNet N) Finset.univ allOnes M allOnes θ
      = (1 / 2 : ℝ) ^ (N - M.card)
          * ((M.filter fun k => ¬ inputs k ⊆ θ.causePart k).card : ℝ) := by
  rw [phiCofPartition, causeRep_circNet_univ h3, causeFwd_circNet_univ,
    if_pos (circVal_allOnes_eq_allOnes M), one_mul,
    partCauseFwd_circNet_univ hN M θ (circVal_allOnes_eq_true M), pos_logb_half_pow]

/-- If every partition loses some window, `φ_c ≥ 2^{|M| - N}`. -/
theorem le_phiCat_circNet_univ (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    (hM : M.Nonempty)
    (hlose : ∀ θ : Partition N M Finset.univ, ∃ k ∈ M, ¬ inputs k ⊆ θ.causePart k) :
    (1 / 2 : ℝ) ^ (N - M.card) ≤ phiCat (circNet N) Finset.univ allOnes M allOnes := by
  have : Fact M.Nonempty := ⟨hM⟩
  obtain ⟨θ₀, hθ₀⟩ :=
    argminSet_nonempty (normalizedPhiC (circNet N) Finset.univ allOnes M allOnes)
  rw [phiCat]
  refine le_trans ?_ (le_sup'OrZero hθ₀)
  rw [phiCofPartition_circNet_univ hN h3]
  obtain ⟨k, hk, hkθ⟩ := hlose θ₀
  have hcard : (1 : ℝ)
      ≤ ((M.filter fun k => ¬ inputs k ⊆ θ₀.causePart k).card : ℝ) := by
    have : 0 < (M.filter fun k => ¬ inputs k ⊆ θ₀.causePart k).card :=
      Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨hk, hkθ⟩⟩
    exact_mod_cast this
  calc (1 / 2 : ℝ) ^ (N - M.card) = (1 / 2 : ℝ) ^ (N - M.card) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

/-- `φ_c` is constant on the fibre of maximal cause states. -/
theorem phiCat_circNet_univ_eq_of_fibre (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    {z : State N} (hz : ∀ k ∈ M, circVal k z = true) :
    phiCat (circNet N) Finset.univ z M allOnes
      = phiCat (circNet N) Finset.univ allOnes M allOnes := by
  have hfwd : causeFwd (circNet N) Finset.univ z M allOnes
      = causeFwd (circNet N) Finset.univ allOnes M allOnes := by
    rw [causeFwd_circNet_univ, causeFwd_circNet_univ,
      if_pos (fun k hk => (hz k hk).trans (allOnes_apply k).symm),
      if_pos (circVal_allOnes_eq_allOnes M)]
  have hrep : causeRep (circNet N) Finset.univ z M allOnes
      = causeRep (circNet N) Finset.univ allOnes M allOnes := by
    rw [causeRep_circNet_univ h3, causeRep_circNet_univ h3,
      if_pos (fun k hk => (hz k hk).trans (allOnes_apply k).symm),
      if_pos (circVal_allOnes_eq_allOnes M)]
  have hpart : ∀ θ : Partition N M Finset.univ,
      partCauseFwd (circNet N) Finset.univ z M allOnes θ
        = partCauseFwd (circNet N) Finset.univ allOnes M allOnes θ := by
    intro θ
    rw [partCauseFwd_circNet_univ hN M θ hz,
      partCauseFwd_circNet_univ hN M θ (circVal_allOnes_eq_true M)]
  have hphi : ∀ θ : Partition N M Finset.univ,
      phiCofPartition (circNet N) Finset.univ z M allOnes θ
        = phiCofPartition (circNet N) Finset.univ allOnes M allOnes θ := by
    intro θ
    rw [phiCofPartition, phiCofPartition, hrep, hfwd, hpart]
  have hnorm : ∀ θ : Partition N M Finset.univ,
      normalizedPhiC (circNet N) Finset.univ z M allOnes θ
        = normalizedPhiC (circNet N) Finset.univ allOnes M allOnes θ := by
    intro θ
    rw [normalizedPhiC, normalizedPhiC, hphi]
  have hmip : mipSetC (circNet N) Finset.univ z M allOnes
      = mipSetC (circNet N) Finset.univ allOnes M allOnes := by
    ext θ
    simp only [mipSetC, mem_argminSet, hnorm]
  rw [phiCat, phiCat, hmip]
  exact sup'OrZero_congr hphi

/-- **The floor.**  If every partition loses some window, then
`φ_c(M) ≥ (1/2)^(N-|M|)`. -/
theorem le_phiCmech_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    (hM : M.Nonempty)
    (hlose : ∀ θ : Partition N M Finset.univ, ∃ k ∈ M, ¬ inputs k ⊆ θ.causePart k) :
    (1 / 2 : ℝ) ^ (N - M.card) ≤ phiCmech (circNet N) Finset.univ M allOnes := by
  refine (le_phiCat_circNet_univ hN h3 M hM hlose).trans ?_
  rw [phiCmech]
  refine le_trans ?_ (Finset.le_sup' (f := fun Z => phiCpurview (circNet N) M allOnes Z)
    (b := Finset.univ) (Finset.mem_powerset.2 subset_rfl))
  rw [phiCpurview]
  exact Finset.le_sup' (f := fun w => phiCat (circNet N) Finset.univ w M allOnes)
    (allOnes_mem_maxCauseStates_circNet_univ h3 M)

end CauseUniv

/-! ## The hull lemma

Severing a single mechanism unit whose window is not inside the purview does not change
the cause repertoire, so `φ_c` vanishes at that partition and hence at the MIP.  The
partition `severOne` and its two `causePart` lemmas mention no substrate at all and are
from `CircNet/Common.lean`. -/

section Hull

variable [NeZero N]

/-- Severing a unit whose window is not inside `Z` leaves the cause repertoire unchanged:
the severed unit is at `1/2` before and after. -/
theorem partCauseFwd_circNet_severOne (hN : 3 ≤ N) (M Z : Finset (Fin N)) (z m : State N)
    {k : Fin N} (hk : k ∈ M) (hkZ : ¬ inputs k ⊆ Z) :
    partCauseFwd (circNet N) Z z M m (severOne M Z hk) = causeFwd (circNet N) Z z M m := by
  rw [partCauseFwd, causeFwd_eq]
  refine Finset.prod_congr rfl fun j hj => ?_
  by_cases hjk : j = k
  · have hne : ¬ inputs k ⊆ (∅ : Finset (Fin N)) :=
      fun h => Finset.notMem_empty k (h (self_mem_inputs k))
    rw [hjk, severOne_causePart_self M Z hk,
      effUnit_circNet_of_not_inputs_subset hN _ _ _ _ hne,
      effUnit_circNet_of_not_inputs_subset hN _ _ _ _ hkZ]
  · rw [severOne_causePart_of_ne M Z hk hj hjk]

theorem phiCofPartition_circNet_severOne (hN : 3 ≤ N) (M Z : Finset (Fin N)) (z m : State N)
    {k : Fin N} (hk : k ∈ M) (hkZ : ¬ inputs k ⊆ Z) :
    phiCofPartition (circNet N) Z z M m (severOne M Z hk) = 0 := by
  rw [phiCofPartition, partCauseFwd_circNet_severOne hN M Z z m hk hkZ]
  rcases eq_or_ne (causeFwd (circNet N) Z z M m) 0 with h0 | h0
  · rw [h0, zero_div, Real.logb_zero]
    simp [pos]
  · rw [div_self h0, Real.logb_one]
    simp [pos]

/-- **The hull lemma.**  A positive `φ_c` forces every window of the mechanism into the
purview. -/
theorem circInputs_subset_of_phiCat_pos (hN : 3 ≤ N) {Z : Finset (Fin N)} {z : State N}
    {M : Finset (Fin N)} {m : State N} (hpos : 0 < phiCat (circNet N) Z z M m)
    {k : Fin N} (hk : k ∈ M) : inputs k ⊆ Z := by
  by_contra hkZ
  have hZ : Z.Nonempty := by
    rcases Z.eq_empty_or_nonempty with h | h
    · subst h
      rw [phiCat_empty_purview] at hpos
      exact absurd hpos (lt_irrefl _)
    · exact h
  have hnorm0 : normalizedPhiC (circNet N) Z z M m (severOne M Z hk) = 0 := by
    rw [normalizedPhiC, phiCofPartition_circNet_severOne hN M Z z m hk hkZ, zero_div]
  have hle : phiCat (circNet N) Z z M m ≤ 0 := by
    rw [phiCat]
    refine sup'OrZero_le le_rfl fun θ hθ => ?_
    rw [mipSetC, mem_argminSet] at hθ
    have h1 := hθ (severOne M Z hk)
    rw [hnorm0] at h1
    have hcut : (0 : ℝ) < (cutCount M Z θ : ℝ) := by exact_mod_cast cutCount_pos hZ θ
    rw [normalizedPhiC, div_le_iff₀ hcut, zero_mul] at h1
    exact h1
  exact absurd hpos (not_lt.2 hle)

end Hull

/-! ## Maximizing cause purviews -/

section MaxPurviews

variable [NeZero N]

/-- **The mechanism sits inside every maximizing cause purview.**  A maximizing cause
purview has positive `φ_c` (`phiCat_pos_of_mem_maxCausePurviews`, reused from
`CircNet/Common.lean`: it mentions no substrate), so by the hull lemma it contains the
window of every unit of `M`, and each unit lies in its own window.  This is what puts a
chosen unit of `M` into the support of the distinction. -/
theorem mem_of_mem_maxCausePurviews (hN : 3 ≤ N) (M : Finset (Fin N)) (m : State N)
    (hpos : 0 < phiCmech (circNet N) Finset.univ M m)
    {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews (circNet N) Finset.univ M m) : M ⊆ p.1 := by
  intro k hk
  exact circInputs_subset_of_phiCat_pos hN
    (phiCat_pos_of_mem_maxCausePurviews _ _ _ hpos hp) hk (self_mem_inputs k)

/-- **Maximizing cause purviews at all-ones.**  When the windows of `M` cover the substrate
and `φ_c(m) > 0`, every maximizing cause purview is the whole substrate paired with a
fibre state, and `(univ, allOnes)` is one of them. -/
theorem maxCausePurviews_circNet_univ (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M : Finset (Fin N))
    (hM : M.Nonempty) (hhull : ∀ x : Fin N, ∃ k ∈ M, x ∈ inputs k)
    (hpos : 0 < phiCmech (circNet N) Finset.univ M allOnes)
    {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews (circNet N) Finset.univ M allOnes) :
    p.1 = Finset.univ ∧ (∀ k ∈ M, circVal k p.2 = true) ∧
      (Finset.univ, allOnes) ∈ maxCausePurviews (circNet N) Finset.univ M allOnes := by
  have hpcat : 0 < phiCat (circNet N) p.1 p.2 M allOnes :=
    phiCat_pos_of_mem_maxCausePurviews _ _ _ hpos hp
  have hp1 : p.1 = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    obtain ⟨k, hk, hx⟩ := hhull x
    exact circInputs_subset_of_phiCat_pos hN hpcat hk hx
  obtain ⟨hcand, hmax⟩ := Finset.mem_filter.1 hp
  obtain ⟨Z, -, hz⟩ := Finset.mem_biUnion.1 hcand
  obtain ⟨w, hwmem, hweq⟩ := Finset.mem_image.1 hz
  have hZp : Z = p.1 := congrArg Prod.fst hweq
  have hwp : w = p.2 := congrArg Prod.snd hweq
  rw [hZp, hp1, hwp] at hwmem
  have hp2 : ∀ k ∈ M, circVal k p.2 = true :=
    (mem_maxCauseStates_circNet_univ_iff h3 M hM p.2).1 hwmem
  refine ⟨hp1, hp2, ?_⟩
  have hcand' : (Finset.univ, allOnes)
      ∈ causeCandidates (circNet N) Finset.univ M allOnes := by
    rw [causeCandidates, Finset.mem_biUnion]
    exact ⟨Finset.univ, Finset.mem_powerset.2 subset_rfl,
      Finset.mem_image_of_mem _ (allOnes_mem_maxCauseStates_circNet_univ h3 M)⟩
  refine Finset.mem_filter.2 ⟨hcand', fun q hq => ?_⟩
  refine (hmax q hq).trans (le_of_eq ?_)
  rw [hp1]
  exact phiCat_circNet_univ_eq_of_fibre hN h3 M hp2

/-- A maximizing cause purview congruent with the all-ones system state contains
`(k, true)` for every unit `k` of the mechanism. -/
theorem mem_stated_of_mem_maxCausePurviews (hN : 3 ≤ N) (M : Finset (Fin N)) (m : State N)
    (hpos : 0 < phiCmech (circNet N) Finset.univ M m)
    {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews (circNet N) Finset.univ M m)
    (hcong : stated p.1 p.2 ⊆ stated Finset.univ allOnes)
    {k : Fin N} (hk : k ∈ M) : (k, true) ∈ stated p.1 p.2 := by
  have hkp : k ∈ p.1 := mem_of_mem_maxCausePurviews hN M m hpos hp hk
  have h0 : (k, p.2 k) ∈ stated p.1 p.2 := mem_stated.2 ⟨hkp, rfl⟩
  have h1 := hcong h0
  rw [mem_stated] at h1
  exact mem_stated.2 ⟨hkp, h1.2.symm⟩

end MaxPurviews

end IIT
