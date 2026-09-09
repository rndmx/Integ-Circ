/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantMain

/-!
# The damage model for an arbitrary candidate system

`CircNet/Circulant.lean` reduces `φ_E` to a damage count for the *whole* substrate.  This file
does the same for an arbitrary `S ⊆ Fin N`, which is what the exclusion postulate needs:
`[IIT4, Eq 26]` compares the whole against every overlapping candidate.

Background conditioning does the work.  A cut set always lies inside `S`, so every unit
*outside* `S` is pinned at the background state, and a unit of `S` is undetermined exactly
when the cut reaches one of its live inputs **inside `S`**.  The halving lemmas of
`CircNet/Circulant.lean` are stated for an arbitrary conditioning set and apply verbatim.

The payoff is the bound `φ_s ≤ φ_E`, which is all the competitor analysis needs: no
cause-side law is required, because `φ_s` is a minimum of the two directions.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section SubDamage

variable [NeZero N]

/-- Unit `j` of `S` is damaged by `θ` when the cut reaches one of its live inputs that
lies inside `S`. -/
def DamagedOn (S : Finset (Fin N)) (θ : SysPartition N S) (j : Fin N) : Prop :=
  ∃ k ∈ liveInputs j, k ∈ θ.cutSet (θ.partOf j)

/-- The damaged units of a candidate system. -/
noncomputable def damagedOn (S : Finset (Fin N)) (θ : SysPartition N S) : Finset (Fin N) :=
  S.filter fun j => DamagedOn S θ j

noncomputable def damagedCountOn (S : Finset (Fin N)) (θ : SysPartition N S) : ℕ :=
  (damagedOn S θ).card

/-- A unit is never in its own block's cut set. -/
lemma notMem_cutSet_partOf_gen {S : Finset (Fin N)} (θ : SysPartition N S) {j : Fin N}
    (hj : j ∈ S) : j ∉ θ.cutSet (θ.partOf j) := by
  classical
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j hj
  rw [θ.partOf_eq hp hjp]
  intro hmem
  rw [SysPartition.cutSet] at hmem
  cases hd : θ.dir p with
  | inputs => rw [hd] at hmem; exact (Finset.mem_sdiff.1 hmem).2 hjp
  | both => rw [hd] at hmem; exact (Finset.mem_sdiff.1 hmem).2 hjp
  | outputs =>
      rw [hd] at hmem
      obtain ⟨q, hq, hjq⟩ := Finset.mem_sup.1 hmem
      obtain ⟨hqp, hqne, -⟩ := Finset.mem_filter.1 hq
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hqp p hp hqne) hjq hjp

/-- **A damaged unit contributes exactly one half.** -/
lemma effUnit_circNet_damagedOn (hN : 3 ≤ N) {S : Finset (Fin N)} (θ : SysPartition N S)
    (m : State N) {j : Fin N} (b : Bool) (h : DamagedOn S θ j) :
    effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ m j b = 1 / 2 := by
  obtain ⟨k, hlive, hk⟩ := h
  exact effUnit_circNet_of_not_mem hN _ _ _ k _ (by simpa using hk) hlive

/-- **An undamaged unit is pinned to the state the substrate produces.** -/
lemma effUnit_circNet_undamagedOn {S : Finset (Fin N)} (θ : SysPartition N S)
    (m : State N) {j : Fin N} (hj : j ∈ S) (h : ¬ DamagedOn S θ j) :
    effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ m j (circVal j m) = 1 := by
  have hjc : j ∈ (θ.cutSet (θ.partOf j))ᶜ := by
    simpa using notMem_cutSet_partOf_gen θ hj
  have hlive : ∀ k ∈ liveInputs j, k ∈ (θ.cutSet (θ.partOf j))ᶜ := by
    intro k hk
    simp only [Finset.mem_compl]
    intro hmem
    exact h ⟨k, hk, hmem⟩
  rw [effUnit_circNet_of_window_subset _ _ _ _ hjc
    (hlive _ (mem_liveInputs.2 (Or.inl rfl)))
    (hlive _ (mem_liveInputs.2 (Or.inr rfl))), if_pos rfl]

/-- The state the candidate system produces from its own units, with the background
pinned. -/
noncomputable def sysNext (S : Finset (Fin N)) (u s : State N) : State N :=
  fun j => circVal j (merge S s u)

/-- **The partitioned effect probability of the produced state is a half per damaged
unit.** -/
theorem sysPartEffProb_circNet_gen (hN : 3 ≤ N) {S : Finset (Fin N)}
    (θ : SysPartition N S) (u s : State N) :
    sysPartEffProb (circNet N) S u θ s (sysNext S u s)
      = (1 / 2 : ℝ) ^ damagedCountOn S θ := by
  classical
  rw [sysPartEffProb]
  have hterm : ∀ j ∈ S,
      effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ (merge S s u) j (sysNext S u s j)
        = if DamagedOn S θ j then (1 / 2 : ℝ) else 1 := by
    intro j hj
    by_cases h : DamagedOn S θ j
    · rw [if_pos h]
      exact effUnit_circNet_damagedOn hN θ (merge S s u) _ h
    · rw [if_neg h]
      exact effUnit_circNet_undamagedOn θ (merge S s u) hj h
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, damagedCountOn, damagedOn]

/-- The unpartitioned effect probability of the produced state is `1`. -/
theorem sysEffProb_circNet_gen {S : Finset (Fin N)} (u s : State N) :
    sysEffProb (circNet N) S u s (sysNext S u s) = 1 := by
  rw [sysEffProb]
  refine Finset.prod_eq_one fun j _ => ?_
  show (if sysNext S u s j = circVal j (merge S s u) then (1 : ℝ) else 0) = 1
  simp [sysNext]

/-- **`φ_E` is the damage count**, for an arbitrary candidate system, at the state the
substrate produces. -/
theorem sysPhiE_circNet_gen (hN : 3 ≤ N) {S : Finset (Fin N)} (θ : SysPartition N S)
    (u s : State N) :
    sysPhiE (circNet N) S u θ s (sysNext S u s) = (damagedCountOn S θ : ℝ) := by
  rw [sysPhiE, sysEffProb_circNet_gen, sysPartEffProb_circNet_gen hN, one_mul]
  have hinv : (((1 : ℝ) / 2) ^ damagedCountOn S θ)⁻¹ = (2 : ℝ) ^ damagedCountOn S θ := by
    rw [one_div, inv_pow, inv_inv]
  rw [div_eq_mul_inv, one_mul, hinv, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos,
    max_eq_right (by positivity)]

/-- At any other candidate effect state the effect probability vanishes, so `φ_E` does
too. -/
theorem sysPhiE_circNet_gen_of_ne (hN : 3 ≤ N) {S : Finset (Fin N)}
    (θ : SysPartition N S) (u s t : State N) (hne : ∃ j ∈ S, t j ≠ sysNext S u s j) :
    sysPhiE (circNet N) S u θ s t = 0 := by
  obtain ⟨j, hj, hjne⟩ := hne
  have hzero : sysEffProb (circNet N) S u s t = 0 := by
    rw [sysEffProb]
    refine Finset.prod_eq_zero hj ?_
    show (if t j = circVal j (merge S s u) then (1 : ℝ) else 0) = 0
    have : t j ≠ circVal j (merge S s u) := hjne
    rw [if_neg this]
  rw [sysPhiE, hzero, zero_mul]

/-- **`φ_E` never exceeds the damage count**, whatever the candidate effect state. -/
theorem sysPhiE_circNet_gen_le (hN : 3 ≤ N) {S : Finset (Fin N)} (θ : SysPartition N S)
    (u s t : State N) :
    sysPhiE (circNet N) S u θ s t ≤ (damagedCountOn S θ : ℝ) := by
  classical
  by_cases hall : ∀ j ∈ S, t j = sysNext S u s j
  · have heq : sysPhiE (circNet N) S u θ s t
        = sysPhiE (circNet N) S u θ s (sysNext S u s) := by
      unfold sysPhiE
      rw [sysEffProb_congr hall, sysPartEffProb_congr hall]
    rw [heq, sysPhiE_circNet_gen hN]
  · push_neg at hall
    obtain ⟨j, hj, hjne⟩ := hall
    rw [sysPhiE_circNet_gen_of_ne hN θ u s t ⟨j, hj, hjne⟩]
    exact Nat.cast_nonneg _

/-- **`φ_s` at a partition never exceeds the damage count.**  `φ_s` is a minimum of the
two directions, so the effect side alone bounds it -- no cause-side law is needed. -/
theorem sysPhiAt_circNet_gen_le (hN : 3 ≤ N) {S : Finset (Fin N)} (θ : SysPartition N S)
    (u s tc te : State N) :
    sysPhiAt (circNet N) S u θ s tc te ≤ (damagedCountOn S θ : ℝ) :=
  le_trans (min_le_right _ _) (sysPhiE_circNet_gen_le hN θ u s te)

end SubDamage

/-! ## The competitor bound

A cut set always avoids its own block, so the normalizer of any partition of `S` is at
most `|S|(|S|-1)`.  Against a witness partition whose damage is small and whose normalizer
is large, the minimum information partition is then forced to have small value -- with no
case analysis at all, because `φ_s ≤ φ_E = damage` is already available.
-/

section Crude

variable [NeZero N]

/-- A cut set lies inside `S` and avoids its own block. -/
lemma cutSet_subset_sdiff_gen {S : Finset (Fin N)} (θ : SysPartition N S)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) : θ.cutSet p ⊆ S \ p := by
  classical
  rw [SysPartition.cutSet]
  cases hd : θ.dir p with
  | inputs => exact subset_rfl
  | both => exact subset_rfl
  | outputs =>
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hqp, hqne, -⟩ := Finset.mem_filter.1 hq
      intro x hx
      refine Finset.mem_sdiff.2 ⟨θ.parts_subset q hqp hx, ?_⟩
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hqp p hp hqne) hx

/-- **The normalizer of a candidate system is at most `|S|(|S|-1)`.** -/
theorem sysCutCount_le_gen {S : Finset (Fin N)} (θ : SysPartition N S) :
    sysCutCount θ ≤ S.card * (S.card - 1) := by
  classical
  have hterm : ∀ p ∈ θ.parts, p.card * (θ.cutSet p).card ≤ p.card * (S.card - 1) := by
    intro p hp
    refine Nat.mul_le_mul_left _ ?_
    have h1 : (θ.cutSet p).card ≤ (S \ p).card :=
      Finset.card_le_card (cutSet_subset_sdiff_gen θ hp)
    have h2 : (S \ p).card = S.card - p.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 (θ.parts_subset p hp)]
    have h3 : 0 < p.card := Finset.card_pos.2 (θ.parts_nonempty p hp)
    omega
  have hsum : ∑ p ∈ θ.parts, p.card ≤ S.card := by
    classical
    have hdisj : Set.PairwiseDisjoint (↑θ.parts : Set (Finset (Fin N))) id :=
      fun p hp q hq hpq => θ.parts_disjoint p hp q hq hpq
    have hbi := Finset.card_biUnion (s := θ.parts) (t := fun p => p)
      (fun p hp q hq hpq => θ.parts_disjoint p hp q hq hpq)
    rw [← hbi]
    refine Finset.card_le_card fun x hx => ?_
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hx
    exact θ.parts_subset p hp hxp
  calc sysCutCount θ = ∑ p ∈ θ.parts, p.card * (θ.cutSet p).card := rfl
    _ ≤ ∑ p ∈ θ.parts, p.card * (S.card - 1) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ θ.parts, p.card) * (S.card - 1) := by rw [Finset.sum_mul]
    _ ≤ S.card * (S.card - 1) := Nat.mul_le_mul_right _ hsum

/-- **The competitor bound.**  A witness partition `θ₀` of `S` bounds `φ_s(S)` by
`|S|(|S|-1) · damage(θ₀) / cutCount(θ₀)`: at the minimum information partition the
normalized value cannot exceed the witness's, and `φ_s ≤ damage` supplies the numerator. -/
theorem sysPhi_circNet_gen_le (hN : 3 ≤ N) {S : Finset (Fin N)} (u s : State N)
    (θ₀ : SysPartition N S) :
    sysPhi (circNet N) S u s
      ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) * (damagedCountOn S θ₀ : ℝ)
          / (sysCutCount θ₀ : ℝ) := by
  classical
  have hcc₀ : (0 : ℝ) < (sysCutCount θ₀ : ℝ) := by
    exact_mod_cast sysCutCount_pos θ₀
  have hnn : (0 : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) * (damagedCountOn S θ₀ : ℝ)
      / (sysCutCount θ₀ : ℝ) := by positivity
  refine sup'OrZero_le hnn fun q _ => ?_
  refine sup'OrZero_le hnn fun θ hθ => ?_
  -- the argmin beats the witness
  have hmin := (mem_argminSet.1 hθ) θ₀
  have hccθ : (0 : ℝ) < (sysCutCount θ : ℝ) := by exact_mod_cast sysCutCount_pos θ
  rw [normalizedSysPhiAt, normalizedSysPhiAt] at hmin
  have hw : sysPhiAt (circNet N) S u θ₀ s q.1 q.2 ≤ (damagedCountOn S θ₀ : ℝ) :=
    sysPhiAt_circNet_gen_le hN θ₀ u s q.1 q.2
  have hstep : sysPhiAt (circNet N) S u θ s q.1 q.2 / (sysCutCount θ : ℝ)
      ≤ (damagedCountOn S θ₀ : ℝ) / (sysCutCount θ₀ : ℝ) :=
    hmin.trans (by gcongr)
  rw [div_le_div_iff₀ hccθ hcc₀] at hstep
  have hccle : (sysCutCount θ : ℝ) ≤ ((S.card * (S.card - 1) : ℕ) : ℝ) := by
    exact_mod_cast sysCutCount_le_gen θ
  rw [le_div_iff₀ hcc₀]
  calc sysPhiAt (circNet N) S u θ s q.1 q.2 * (sysCutCount θ₀ : ℝ)
      ≤ (damagedCountOn S θ₀ : ℝ) * (sysCutCount θ : ℝ) := hstep
    _ ≤ (damagedCountOn S θ₀ : ℝ) * ((S.card * (S.card - 1) : ℕ) : ℝ) := by
        gcongr
    _ = ((S.card * (S.card - 1) : ℕ) : ℝ) * (damagedCountOn S θ₀ : ℝ) := by ring

end Crude

end IIT
