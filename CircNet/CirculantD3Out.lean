/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Bound

/-!
# The outputs-side contribution

A block severing its outputs is cut from every *other* block that severs its outputs or
both directions.  So its cut set is `(B ∪ O) \ q`, where `O` is the union of all
outputs blocks and `B` the union of all `both` blocks.

This gives the closed form

`Σ_{outputs q} |q|·|cutSet q| = |B|·|O| + |O|² − Σ_q |q|²`,

which is the outputs half of the `D = 3` normalizer bound.  The `Σ|q|²` term is what makes
a *single* outputs block cheap (the `|O|²` cancels, leaving `|B|·|O|`) and a balanced split
expensive -- and the damage budget is what forbids the expensive splits.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section OutRegion

variable [NeZero N]

/-- The union of the blocks severing their outputs. -/
noncomputable def outRegion (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  (θ.parts.filter fun p => θ.dir p = Dir.outputs).sup id

/-- The union of the blocks severing both directions. -/
noncomputable def bothRegion (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  (θ.parts.filter fun p => θ.dir p = Dir.both).sup id

lemma mem_outRegion {θ : SysPartition N Finset.univ} {x : Fin N} :
    x ∈ outRegion θ ↔ ∃ p ∈ θ.parts, θ.dir p = Dir.outputs ∧ x ∈ p := by
  unfold outRegion
  rw [Finset.mem_sup]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨hpp, hpd⟩ := Finset.mem_filter.1 hp
    exact ⟨p, hpp, hpd, hx⟩
  · rintro ⟨p, hpp, hpd, hx⟩
    exact ⟨p, Finset.mem_filter.2 ⟨hpp, hpd⟩, hx⟩

lemma mem_bothRegion {θ : SysPartition N Finset.univ} {x : Fin N} :
    x ∈ bothRegion θ ↔ ∃ p ∈ θ.parts, θ.dir p = Dir.both ∧ x ∈ p := by
  unfold bothRegion
  rw [Finset.mem_sup]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨hpp, hpd⟩ := Finset.mem_filter.1 hp
    exact ⟨p, hpp, hpd, hx⟩
  · rintro ⟨p, hpp, hpd, hx⟩
    exact ⟨p, Finset.mem_filter.2 ⟨hpp, hpd⟩, hx⟩

/-- **The cut set of an outputs block** is everything that severs its outputs or both
directions, minus itself. -/
theorem cutSet_outputs_eq (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    θ.cutSet q = (bothRegion θ ∪ outRegion θ) \ q := by
  classical
  ext x
  rw [SysPartition.cutSet, hdq, Finset.mem_sup, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨r, hr, hxr⟩
    obtain ⟨hrp, hrq, hrd⟩ := Finset.mem_filter.1 hr
    refine ⟨?_, ?_⟩
    · rcases hrd with h | h
      · exact Or.inr (mem_outRegion.2 ⟨r, hrp, h, hxr⟩)
      · exact Or.inl (mem_bothRegion.2 ⟨r, hrp, h, hxr⟩)
    · intro hxq
      exact Finset.disjoint_left.1 (θ.parts_disjoint r hrp q hq hrq) hxr hxq
  · rintro ⟨hxbo, hxq⟩
    rcases hxbo with hb | ho
    · obtain ⟨r, hrp, hrd, hxr⟩ := mem_bothRegion.1 hb
      have hrq : r ≠ q := by
        rintro rfl
        rw [hdq] at hrd
        exact absurd hrd (by decide)
      exact ⟨r, Finset.mem_filter.2 ⟨hrp, hrq, Or.inr hrd⟩, hxr⟩
    · obtain ⟨r, hrp, hrd, hxr⟩ := mem_outRegion.1 ho
      have hrq : r ≠ q := by
        rintro rfl
        exact hxq hxr
      exact ⟨r, Finset.mem_filter.2 ⟨hrp, hrq, Or.inl hrd⟩, hxr⟩

/-- An outputs block sits inside the outputs region. -/
lemma subset_outRegion (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) : q ⊆ outRegion θ :=
  fun x hx => mem_outRegion.2 ⟨q, hq, hdq, hx⟩

/-- The `both` region and the outputs region are disjoint. -/
lemma bothRegion_disjoint_outRegion (θ : SysPartition N Finset.univ) :
    Disjoint (bothRegion θ) (outRegion θ) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxb hxo
  obtain ⟨r, hrp, hrd, hxr⟩ := mem_bothRegion.1 hxb
  obtain ⟨r', hr'p, hr'd, hxr'⟩ := mem_outRegion.1 hxo
  have hne : r ≠ r' := by
    rintro rfl
    rw [hrd] at hr'd
    exact absurd hr'd (by decide)
  exact Finset.disjoint_left.1 (θ.parts_disjoint r hrp r' hr'p hne) hxr hxr'

/-- **The size of an outputs block's cut set**: `|B| + |O| − |q|`. -/
theorem card_cutSet_outputs (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    (θ.cutSet q).card = (bothRegion θ).card + (outRegion θ).card - q.card := by
  classical
  have hsub : q ⊆ bothRegion θ ∪ outRegion θ :=
    fun x hx => Finset.mem_union_right _ (subset_outRegion θ hq hdq hx)
  rw [cutSet_outputs_eq θ hq hdq, Finset.card_sdiff, Finset.inter_eq_left.2 hsub,
    Finset.card_union_of_disjoint (bothRegion_disjoint_outRegion θ)]

/-- The blocks severing their outputs. -/
noncomputable def outBlocks (θ : SysPartition N Finset.univ) : Finset (Finset (Fin N)) :=
  θ.parts.filter fun p => θ.dir p = Dir.outputs

omit [NeZero N] in
lemma mem_outBlocks {θ : SysPartition N Finset.univ} {p : Finset (Fin N)} :
    p ∈ outBlocks θ ↔ p ∈ θ.parts ∧ θ.dir p = Dir.outputs := by
  unfold outBlocks
  rw [Finset.mem_filter]

omit [NeZero N] in
/-- Every block either severs its outputs or is complement-cut. -/
lemma parts_eq_union (θ : SysPartition N Finset.univ) :
    θ.parts = compCutBlocks θ ∪ outBlocks θ := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    by_cases hd : θ.dir p = Dir.outputs
    · exact Finset.mem_union_right _ (mem_outBlocks.2 ⟨hp, hd⟩)
    · exact Finset.mem_union_left _ (mem_compCutBlocks.2 ⟨hp, hd⟩)
  · intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact (mem_compCutBlocks.1 h).1
    · exact (mem_outBlocks.1 h).1

omit [NeZero N] in
lemma compCut_disjoint_outBlocks (θ : SysPartition N Finset.univ) :
    Disjoint (compCutBlocks θ) (outBlocks θ) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  exact (mem_compCutBlocks.1 hp).2 (mem_outBlocks.1 hp').2

/-- **The normalizer splits into its two halves.**  The complement-cut blocks contribute
`|p|(N-|p|)` each, and the outputs blocks contribute `|q|(|B| + |O| - |q|)` each. -/
theorem sysCutCount_split (θ : SysPartition N Finset.univ) :
    sysCutCount θ
      = (∑ p ∈ compCutBlocks θ, p.card * (N - p.card))
        + ∑ q ∈ outBlocks θ, q.card *
            ((bothRegion θ).card + (outRegion θ).card - q.card) := by
  classical
  rw [sysCutCount, parts_eq_union θ,
    Finset.sum_union (compCut_disjoint_outBlocks θ)]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    exact cutContribution_compCut θ (mem_compCutBlocks.1 hp).1 (mem_compCutBlocks.1 hp).2
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [card_cutSet_outputs θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2]

end OutRegion

end IIT
