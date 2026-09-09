/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CircSys

/-!
# The interval circulant: the effect side of an arbitrary mechanism at all-ones

The mechanism-level effect side for the interval window `{i, i+1, i+2}` (`3 ∤ N`)
to the interval window `{i, i+1, i+2}` (`3 ∤ N`).  For a mechanism `M` and an effect
purview `Z` of the interval circulant, split `Z` into the units whose whole window lies in
`M` (`circZdet M Z`, the *determined* units) and the rest (`circZund M Z`).  At the
all-ones state every determined unit is pinned to `true` and every undetermined unit sits
at one half, so

* the effect repertoire of a purview state `z` is `(1/2)^|Zund|` if `z` is `true` on
  `Zdet` and `0` otherwise (`effRep_circNet_allOnes_eq`);
* the unconstrained repertoire is `(1/2)^|Z|` when `3 ∤ N` (`uncEffRep_circNet`), by the
  uniformity of the image of the dynamics;
* hence `ii_e = (1/2)^|Zund| · |Zdet|` on the agreeing states and `0` elsewhere, so
  all-ones is a maximal effect state and every maximal effect state agrees with it on
  `Zdet`;
* on a fully determined purview every partition loses the windows it severs, `φ_e` at a
  partition is the number of purview units whose window is cut, and `φ_e ≥ 1` as soon as
  every partition cuts some window.

The last section swaps the all-ones state into any maximal effect purview
(`mem_maxEffPurviews_circNet_allOnes`).

The unit-level input `effUnit_circNet_of_not_mem` of `CircNet/Circulant.lean` only covers a
missing *live* input `{i+1, i+2}`; the first section upgrades it to the whole window
`inputs i = {i, i+1, i+2}` (`effUnit_circNet_of_not_subset`), which is what the mechanism
level needs.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

/-! ## The whole window as a conditioning set -/

section Window

variable [NeZero N]

lemma mem_inputs {j k : Fin N} :
    k ∈ inputs j ↔ k = j ∨ k = shift j ∨ k = shift (shift j) := by
  unfold inputs; simp

lemma self_mem_inputs (j : Fin N) : j ∈ inputs j := by simp [inputs]

lemma shift_mem_inputs (j : Fin N) : shift j ∈ inputs j := by simp [inputs]

lemma shift2_mem_inputs (j : Fin N) : shift (shift j) ∈ inputs j := by simp [inputs]

/-- Flipping a unit's own value flips its next value: it occurs once in its window. -/
lemma circVal_flipAt_self (hN : 3 ≤ N) (j : Fin N) (s : State N) :
    circVal j (flipAt j s) = !(circVal j s) := by
  rw [circVal, circVal, flipAt_apply_self,
    flipAt_apply_of_ne (shift_ne_self hN j) s,
    flipAt_apply_of_ne (shift_shift_ne_self hN j) s]
  cases s j <;> cases s (shift j) <;> cases s (shift (shift j)) <;> simp

/-- Flipping any window member flips the unit's next value. -/
lemma circVal_flipAt_inputs (hN : 3 ≤ N) {j k : Fin N} (hk : k ∈ inputs j) (s : State N) :
    circVal j (flipAt k s) = !(circVal j s) := by
  rcases mem_inputs.1 hk with rfl | rfl | rfl
  · exact circVal_flipAt_self hN _ s
  · exact circVal_flipAt_shift hN _ s
  · exact circVal_flipAt_shift_shift hN _ s

/-- **Omitting any window member halves `effUnit`.**  This is the window version of
`effUnit_circNet_of_not_mem`, which covers a missing live input. -/
theorem effUnit_circNet_of_not_subset (hN : 3 ≤ N) (W : Finset (Fin N)) (m : State N)
    (j : Fin N) (b : Bool) (h : ¬ inputs j ⊆ W) :
    effUnit (circNet N) W m j b = 1 / 2 := by
  classical
  obtain ⟨k, hkI, hk⟩ := Finset.not_subset.1 h
  have hbne : ∀ c : Bool, ¬ (c = !c) := by decide
  have hbnot : ∀ c d : Bool, ¬ (c = d) → c = !d := by decide
  have hmaps : ∀ s ∈ agree W m, flipAt k s ∈ agree W m := by
    intro s hs
    rw [mem_agree] at hs ⊢
    intro i hi
    rw [flipAt_apply_of_ne (by rintro rfl; exact hk hi) s]
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
      rw [circVal_flipAt_inputs hN hkI s, ← hs.2]
      exact hbne b
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [circVal_flipAt_inputs hN hkI s]
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

/-- A conditioning set containing the whole window pins the unit. -/
theorem effUnit_circNet_of_subset (W : Finset (Fin N)) (m : State N) (j : Fin N) (b : Bool)
    (h : inputs j ⊆ W) :
    effUnit (circNet N) W m j b = if b = circVal j m then 1 else 0 :=
  effUnit_circNet_of_window_subset W m j b (h (self_mem_inputs j)) (h (shift_mem_inputs j))
    (h (shift2_mem_inputs j))

/-- At the all-ones state the unit's effect probability of `true` is `1` when its window is
inside the conditioning set and `1/2` otherwise. -/
lemma effUnit_circNet_allOnes_eq (hN : 3 ≤ N) (W : Finset (Fin N)) (j : Fin N) :
    effUnit (circNet N) W allOnes j true = if inputs j ⊆ W then 1 else 1 / 2 := by
  by_cases h : inputs j ⊆ W
  · rw [if_pos h, effUnit_circNet_of_subset _ _ _ _ h, circVal_allOnes, if_pos rfl]
  · rw [if_neg h, effUnit_circNet_of_not_subset hN _ _ _ _ h]

end Window

/-! ## The counting lemma

The image of the dynamics is uniform on every cylinder set: the states whose successor
agrees with `z` on `Z` are the preimage of `agree Z z` under a bijection. -/

section Counting

variable [NeZero N]

/-- **Uniformity of the image** (`3 ∤ N`). -/
theorem card_filter_circNext_agree (h3 : ¬ (3 ∣ N)) (Z : Finset (Fin N)) (z : State N) :
    (Finset.univ.filter fun s : State N => ∀ k ∈ Z, circNext s k = z k).card
      = 2 ^ (N - Z.card) := by
  classical
  rw [← card_agree Z z]
  refine Finset.card_bij (fun s _ => circNext s) ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact mem_agree.2 hs.2
  · intro s₁ _ s₂ _ heq
    exact circNext_injective h3 heq
  · intro t ht
    obtain ⟨s, hs⟩ :=
      (Finite.injective_iff_bijective.1 (circNext_injective (N := N) h3)).surjective t
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

/-! ## Determined and undetermined purview units -/

section DetUnd

variable [NeZero N]

/-- The purview units whose whole window lies inside the mechanism. -/
noncomputable def circZdet (M Z : Finset (Fin N)) : Finset (Fin N) :=
  Z.filter fun k => inputs k ⊆ M

/-- The purview units missing at least one window member from the mechanism. -/
noncomputable def circZund (M Z : Finset (Fin N)) : Finset (Fin N) :=
  Z.filter fun k => ¬ inputs k ⊆ M

lemma mem_circZdet {M Z : Finset (Fin N)} {k : Fin N} :
    k ∈ circZdet M Z ↔ k ∈ Z ∧ inputs k ⊆ M := by
  unfold circZdet; simp

lemma mem_circZund {M Z : Finset (Fin N)} {k : Fin N} :
    k ∈ circZund M Z ↔ k ∈ Z ∧ ¬ inputs k ⊆ M := by
  unfold circZund; simp

lemma card_circZdet_add_circZund (M Z : Finset (Fin N)) :
    (circZdet M Z).card + (circZund M Z).card = Z.card :=
  Finset.card_filter_add_card_filter_not (s := Z) (fun k => inputs k ⊆ M)

lemma card_circZdet_le (M Z : Finset (Fin N)) : (circZdet M Z).card ≤ N := by
  simpa using Finset.card_le_univ (circZdet M Z)

/-- A product over the purview splits into the determined and undetermined parts. -/
lemma prod_circZdet_mul_prod_circZund (M Z : Finset (Fin N)) (f : Fin N → ℝ) :
    (∏ k ∈ circZdet M Z, f k) * ∏ k ∈ circZund M Z, f k = ∏ k ∈ Z, f k :=
  Finset.prod_filter_mul_prod_filter_not Z (fun k => inputs k ⊆ M) f

/-- All-ones trivially agrees with all-ones on the determined units. -/
lemma allOnes_agree_circ (M Z : Finset (Fin N)) :
    ∀ k ∈ Z, inputs k ⊆ M → (allOnes : State N) k = true :=
  fun _ _ _ => rfl

end DetUnd

/-- The power arithmetic behind `uncEffRep_circNet`:
`(1/2)^u · 2^(n-d) / 2^n = (1/2)^(d+u)` for `d ≤ n`. -/
lemma half_pow_arith_circ (u d n : ℕ) (hd : d ≤ n) :
    (1 / 2 : ℝ) ^ u * (2 : ℝ) ^ (n - d) / (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (d + u) := by
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - d) * 2 ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  have h1 : ((1 / 2 : ℝ) ^ d * 2 ^ d) = 1 := by rw [← mul_pow]; norm_num
  rw [div_eq_iff (by positivity), hpow, pow_add]
  calc (1 / 2 : ℝ) ^ u * 2 ^ (n - d)
      = (1 / 2) ^ u * 2 ^ (n - d) * ((1 / 2) ^ d * 2 ^ d) := by rw [h1, mul_one]
    _ = (1 / 2) ^ d * (1 / 2) ^ u * (2 ^ (n - d) * 2 ^ d) := by ring

/-! ## Effect repertoires -/

section EffRep

variable [NeZero N]

/-- The effect repertoire of a general mechanism state: the undetermined units contribute
one half each, the determined ones an indicator. -/
lemma effRep_circNet_eq_general (hN : 3 ≤ N) (M Z : Finset (Fin N)) (m z : State N) :
    effRep (circNet N) M m Z z =
      if (∀ k ∈ Z, inputs k ⊆ M → z k = circVal k m) then
        (1 / 2 : ℝ) ^ (circZund M Z).card else 0 := by
  rw [effRep, ← prod_circZdet_mul_prod_circZund M Z]
  have hund : ∏ k ∈ circZund M Z, effUnit (circNet N) M m k (z k)
      = (1 / 2 : ℝ) ^ (circZund M Z).card := by
    rw [Finset.prod_congr rfl (fun k hk =>
      effUnit_circNet_of_not_subset hN M m k (z k) (mem_circZund.1 hk).2), Finset.prod_const]
  rw [hund]
  by_cases h : ∀ k ∈ Z, inputs k ⊆ M → z k = circVal k m
  · rw [if_pos h]
    have hdet : ∏ k ∈ circZdet M Z, effUnit (circNet N) M m k (z k) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      obtain ⟨hkZ, hkM⟩ := mem_circZdet.1 hk
      rw [effUnit_circNet_of_subset M m k (z k) hkM, if_pos (h k hkZ hkM)]
    rw [hdet, one_mul]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨k, hkZ, hkM, hne⟩ := h
    have hdet : ∏ k ∈ circZdet M Z, effUnit (circNet N) M m k (z k) = 0 := by
      refine Finset.prod_eq_zero (mem_circZdet.2 ⟨hkZ, hkM⟩) ?_
      rw [effUnit_circNet_of_subset M m k (z k) hkM, if_neg hne]
    rw [hdet, zero_mul]

/-- The effect repertoire at the all-ones state. -/
lemma effRep_circNet_allOnes_eq (hN : 3 ≤ N) (M Z : Finset (Fin N)) (z : State N) :
    effRep (circNet N) M allOnes Z z =
      if (∀ k ∈ Z, inputs k ⊆ M → z k = true) then
        (1 / 2 : ℝ) ^ (circZund M Z).card else 0 := by
  rw [effRep_circNet_eq_general hN]
  have e : (∀ k ∈ Z, inputs k ⊆ M → z k = circVal k allOnes)
      ↔ (∀ k ∈ Z, inputs k ⊆ M → z k = true) := by
    simp only [circVal_allOnes]
  by_cases h : ∀ k ∈ Z, inputs k ⊆ M → z k = true
  · rw [if_pos h, if_pos (e.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]

lemma effRep_circNet_allOnes_allOnes (hN : 3 ≤ N) (M Z : Finset (Fin N)) :
    effRep (circNet N) M allOnes Z allOnes = (1 / 2 : ℝ) ^ (circZund M Z).card := by
  rw [effRep_circNet_allOnes_eq hN, if_pos (allOnes_agree_circ M Z)]

lemma circZund_eq_empty_of_det {M Z : Finset (Fin N)} (hZ : ∀ k ∈ Z, inputs k ⊆ M) :
    circZund M Z = ∅ := by
  rw [circZund, Finset.filter_eq_empty_iff]
  intro k hk h
  exact h (hZ k hk)

lemma effRep_circNet_allOnes_of_det (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (hZ : ∀ k ∈ Z, inputs k ⊆ M) :
    effRep (circNet N) M allOnes Z allOnes = 1 := by
  rw [effRep_circNet_allOnes_allOnes hN, circZund_eq_empty_of_det hZ, Finset.card_empty,
    pow_zero]

end EffRep

/-! ## The unconstrained repertoire and intrinsic information -/

section UncEff

variable [NeZero N]

/-- **The unconstrained effect repertoire is uniform** when `3 ∤ N`. -/
theorem uncEffRep_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (z : State N) :
    uncEffRep (circNet N) M Z z = (1 / 2 : ℝ) ^ Z.card := by
  rw [uncEffRep]
  have hterm : ∀ m : State N, effRep (circNet N) M m Z z
      = (1 / 2 : ℝ) ^ (circZund M Z).card
        * (if ∀ k ∈ circZdet M Z, circNext m k = z k then (1 : ℝ) else 0) := by
    intro m
    rw [effRep_circNet_eq_general hN]
    have e : (∀ k ∈ Z, inputs k ⊆ M → z k = circVal k m)
        ↔ (∀ k ∈ circZdet M Z, circNext m k = z k) := by
      constructor
      · intro h k hk
        obtain ⟨hkZ, hkM⟩ := mem_circZdet.1 hk
        exact (h k hkZ hkM).symm
      · intro h k hkZ hkM
        exact (h k (mem_circZdet.2 ⟨hkZ, hkM⟩)).symm
    by_cases h : ∀ k ∈ circZdet M Z, circNext m k = z k
    · rw [if_pos (e.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (e.1 h')), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.mul_sum,
    sum_ite_circNext_agree h3, card_state]
  have hd := card_circZdet_le M Z
  have hZ := card_circZdet_add_circZund M Z
  push_cast
  rw [← hZ]
  exact half_pow_arith_circ _ _ _ hd

/-- `log₂ ((1/2)^u / (1/2)^(d+u)) = d`. -/
lemma logb_half_pow_div_circ (u d : ℕ) :
    Real.logb 2 ((1 / 2 : ℝ) ^ u / (1 / 2 : ℝ) ^ (d + u)) = d := by
  have hu : (1 / 2 : ℝ) ^ u ≠ 0 := by positivity
  have hd : (1 / 2 : ℝ) ^ d ≠ 0 := by positivity
  have e : (1 / 2 : ℝ) ^ u / (1 / 2 : ℝ) ^ (d + u) = 1 / (1 / 2 : ℝ) ^ d := by
    rw [pow_add]
    field_simp
  rw [e, div_pow, one_pow, one_div_one_div, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one]

/-- **Intrinsic effect information at all-ones**: `(1/2)^|Zund| · |Zdet|` on the states
agreeing with all-ones on the determined units, `0` elsewhere. -/
theorem iiE_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (z : State N) :
    iiE (circNet N) M allOnes Z z =
      if (∀ k ∈ Z, inputs k ⊆ M → z k = true) then
        (1 / 2 : ℝ) ^ (circZund M Z).card * (circZdet M Z).card else 0 := by
  rw [iiE, effRep_circNet_allOnes_eq hN, uncEffRep_circNet hN h3]
  by_cases h : ∀ k ∈ Z, inputs k ⊆ M → z k = true
  · rw [if_pos h, if_pos h, ← card_circZdet_add_circZund M Z, logb_half_pow_div_circ]
  · rw [if_neg h, if_neg h, zero_mul]

/-- All-ones is a maximal effect state of every mechanism on every purview. -/
theorem allOnes_mem_maxEffStates_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N))
    (M Z : Finset (Fin N)) :
    allOnes ∈ maxEffStates (circNet N) M allOnes Z := by
  rw [maxEffStates, mem_argmaxSet]
  intro z
  rw [iiE_circNet_allOnes hN h3, iiE_circNet_allOnes hN h3,
    if_pos (allOnes_agree_circ M Z)]
  split_ifs
  · exact le_rfl
  · positivity

/-- When some purview unit is determined, the maximal effect states are exactly those
agreeing with all-ones on the determined units. -/
theorem mem_maxEffStates_circNet_iff (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (hd : (circZdet M Z).Nonempty) (z : State N) :
    z ∈ maxEffStates (circNet N) M allOnes Z ↔ ∀ k ∈ Z, inputs k ⊆ M → z k = true := by
  constructor
  · intro hz
    rw [maxEffStates, mem_argmaxSet] at hz
    have h1 := hz allOnes
    rw [iiE_circNet_allOnes hN h3, iiE_circNet_allOnes hN h3,
      if_pos (allOnes_agree_circ M Z)] at h1
    by_contra h
    rw [if_neg h] at h1
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (circZund M Z).card * (circZdet M Z).card := by
      have : (0 : ℝ) < (circZdet M Z).card := by exact_mod_cast Finset.card_pos.2 hd
      positivity
    linarith
  · intro h
    rw [maxEffStates, mem_argmaxSet]
    intro w
    rw [iiE_circNet_allOnes hN h3, iiE_circNet_allOnes hN h3, if_pos h]
    split_ifs
    · exact le_rfl
    · positivity

/-- Every maximal effect state agrees with all-ones on the determined units. -/
theorem agree_of_mem_maxEffStates_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N))
    (M Z : Finset (Fin N)) {z : State N}
    (hz : z ∈ maxEffStates (circNet N) M allOnes Z) :
    ∀ k ∈ Z, inputs k ⊆ M → z k = true := by
  rcases (circZdet M Z).eq_empty_or_nonempty with he | hne
  · intro k hk hkM
    have hmem := mem_circZdet.2 ⟨hk, hkM⟩
    rw [he] at hmem
    exact absurd hmem (Finset.notMem_empty k)
  · exact (mem_maxEffStates_circNet_iff hN h3 M Z hne z).1 hz

end UncEff

/-! ## Partitioned repertoires and `φ_e` -/

section PartEff

variable [NeZero N]

/-- **The partitioned effect repertoire at all-ones**: one half for every purview unit
whose window is cut by the partition. -/
theorem partEffRep_circNet_allOnes (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (θ : Partition N M Z) {z : State N}
    (hz : ∀ k ∈ Z, inputs k ⊆ M → z k = true) :
    partEffRep (circNet N) M allOnes Z z θ =
      (1 / 2 : ℝ) ^ (Z.filter fun k => ¬ inputs k ⊆ θ.effPart k).card := by
  rw [partEffRep,
    ← Finset.prod_filter_mul_prod_filter_not Z (fun k => inputs k ⊆ θ.effPart k)]
  have h1 : ∏ k ∈ Z.filter (fun k => inputs k ⊆ θ.effPart k),
      effUnit (circNet N) (θ.effPart k) allOnes k (z k) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    obtain ⟨hkZ, hkP⟩ := Finset.mem_filter.1 hk
    have hkM : inputs k ⊆ M := hkP.trans (θ.effPart_subset k)
    rw [hz k hkZ hkM, effUnit_circNet_allOnes_eq hN, if_pos hkP]
  have h2 : ∏ k ∈ Z.filter (fun k => ¬ inputs k ⊆ θ.effPart k),
      effUnit (circNet N) (θ.effPart k) allOnes k (z k)
      = (1 / 2 : ℝ) ^ (Z.filter fun k => ¬ inputs k ⊆ θ.effPart k).card := by
    rw [Finset.prod_congr rfl (fun k hk =>
      effUnit_circNet_of_not_subset hN _ _ _ _ (Finset.mem_filter.1 hk).2), Finset.prod_const]
  rw [h1, h2, one_mul]

lemma partEffRep_circNet_allOnes_pos (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (θ : Partition N M Z) {z : State N}
    (hz : ∀ k ∈ Z, inputs k ⊆ M → z k = true) :
    0 < partEffRep (circNet N) M allOnes Z z θ := by
  rw [partEffRep_circNet_allOnes hN M Z θ hz]
  positivity

lemma pos_logb_half_pow_circ (m : ℕ) :
    pos (Real.logb 2 (1 / (1 / 2 : ℝ) ^ m)) = m := by
  rw [div_pow, one_pow, one_div_one_div, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos, max_eq_right (Nat.cast_nonneg m)]

/-- **`φ_e` at a partition of a fully determined purview** is the number of purview units
whose window the partition cuts. -/
theorem phiEofPartition_circNet_allOnes (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (θ : Partition N M Z) (hZ : ∀ k ∈ Z, inputs k ⊆ M) :
    phiEofPartition (circNet N) M allOnes Z allOnes θ =
      ((Z.filter fun k => ¬ inputs k ⊆ θ.effPart k).card : ℝ) := by
  rw [phiEofPartition, effRep_circNet_allOnes_of_det hN M Z hZ,
    partEffRep_circNet_allOnes hN M Z θ (allOnes_agree_circ M Z), one_mul,
    pos_logb_half_pow_circ]

/-- **`φ_e ≥ 1`** on a fully determined purview once every partition cuts some window. -/
theorem one_le_phiEat_circNet (hN : 3 ≤ N) (M Z : Finset (Fin N)) (hM : M.Nonempty)
    (hZ : ∀ k ∈ Z, inputs k ⊆ M)
    (hlose : ∀ θ : Partition N M Z, ∃ k ∈ Z, ¬ inputs k ⊆ θ.effPart k) :
    1 ≤ phiEat (circNet N) M allOnes Z allOnes := by
  have : Fact M.Nonempty := ⟨hM⟩
  obtain ⟨θ₀, hθ₀⟩ := argminSet_nonempty (normalizedPhi (circNet N) M allOnes Z allOnes)
  have h1 : 1 ≤ phiEofPartition (circNet N) M allOnes Z allOnes θ₀ := by
    rw [phiEofPartition_circNet_allOnes hN M Z θ₀ hZ]
    obtain ⟨k, hkZ, hk⟩ := hlose θ₀
    have hpos : 0 < (Z.filter fun k => ¬ inputs k ⊆ θ₀.effPart k).card :=
      Finset.card_pos.2 ⟨k, Finset.mem_filter.2 ⟨hkZ, hk⟩⟩
    exact Nat.one_le_cast.2 hpos
  exact h1.trans (le_sup'OrZero hθ₀)

/-- `φ_e` at all-ones depends on the purview state only through its values on the
determined units. -/
theorem phiEat_circNet_allOnes_eq_of_agree (hN : 3 ≤ N) (M Z : Finset (Fin N))
    {z z' : State N}
    (hz : ∀ k ∈ Z, inputs k ⊆ M → z k = true)
    (hz' : ∀ k ∈ Z, inputs k ⊆ M → z' k = true) :
    phiEat (circNet N) M allOnes Z z = phiEat (circNet N) M allOnes Z z' := by
  have hrep : effRep (circNet N) M allOnes Z z = effRep (circNet N) M allOnes Z z' := by
    rw [effRep_circNet_allOnes_eq hN, effRep_circNet_allOnes_eq hN, if_pos hz, if_pos hz']
  have hphi : ∀ θ : Partition N M Z,
      phiEofPartition (circNet N) M allOnes Z z θ =
        phiEofPartition (circNet N) M allOnes Z z' θ := by
    intro θ
    rw [phiEofPartition, phiEofPartition, hrep, partEffRep_circNet_allOnes hN M Z θ hz,
      partEffRep_circNet_allOnes hN M Z θ hz']
  have hnorm : ∀ θ, normalizedPhi (circNet N) M allOnes Z z θ =
      normalizedPhi (circNet N) M allOnes Z z' θ := by
    intro θ; simp only [normalizedPhi, hphi]
  have hmip : mipSetE (circNet N) M allOnes Z z = mipSetE (circNet N) M allOnes Z z' := by
    ext θ
    simp [mipSetE, mem_argminSet, hnorm]
  simp only [phiEat, hmip]
  exact sup'OrZero_congr (fun θ => hphi θ)

end PartEff

/-! ## The mechanism level -/

section Mech

variable [NeZero N]

lemma one_le_phiEpurview_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (hM : M.Nonempty) (hZ : ∀ k ∈ Z, inputs k ⊆ M)
    (hlose : ∀ θ : Partition N M Z, ∃ k ∈ Z, ¬ inputs k ⊆ θ.effPart k) :
    1 ≤ phiEpurview (circNet N) M allOnes Z := by
  rw [phiEpurview]
  exact (one_le_phiEat_circNet hN M Z hM hZ hlose).trans
    (Finset.le_sup' (f := fun z => phiEat (circNet N) M allOnes Z z)
      (allOnes_mem_maxEffStates_circNet hN h3 M Z))

/-- **`φ_e(M) ≥ 1`** within the whole substrate. -/
theorem one_le_phiEmech_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (hM : M.Nonempty) (hZ : ∀ k ∈ Z, inputs k ⊆ M)
    (hlose : ∀ θ : Partition N M Z, ∃ k ∈ Z, ¬ inputs k ⊆ θ.effPart k) :
    1 ≤ phiEmech (circNet N) Finset.univ M allOnes := by
  rw [phiEmech]
  exact (one_le_phiEpurview_circNet hN h3 M Z hM hZ hlose).trans
    (Finset.le_sup' (f := fun Z => phiEpurview (circNet N) M allOnes Z)
      (Finset.mem_powerset.2 (Finset.subset_univ _)))

/-- **Swapping all-ones into a maximal effect purview.** -/
theorem mem_maxEffPurviews_circNet_allOnes (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N))
    (M : Finset (Fin N)) {p : Finset (Fin N) × State N}
    (hp : p ∈ maxEffPurviews (circNet N) Finset.univ M allOnes) :
    (p.1, allOnes) ∈ maxEffPurviews (circNet N) Finset.univ M allOnes := by
  obtain ⟨hcand, hmax⟩ := Finset.mem_filter.1 hp
  obtain ⟨Z, hZ, hz⟩ := Finset.mem_biUnion.1 hcand
  obtain ⟨z, hzmem, hzeq⟩ := Finset.mem_image.1 hz
  have hpZ : p = (Z, z) := hzeq.symm
  subst hpZ
  have hagree := agree_of_mem_maxEffStates_circNet hN h3 M Z hzmem
  have heq := phiEat_circNet_allOnes_eq_of_agree hN M Z hagree (allOnes_agree_circ M Z)
  have hcand' : (Z, allOnes) ∈ effCandidates (circNet N) Finset.univ M allOnes := by
    rw [effCandidates, Finset.mem_biUnion]
    exact ⟨Z, hZ, Finset.mem_image_of_mem _ (allOnes_mem_maxEffStates_circNet hN h3 M Z)⟩
  refine Finset.mem_filter.2 ⟨hcand', fun q hq => ?_⟩
  exact (hmax q hq).trans_eq heq

end Mech

end IIT
