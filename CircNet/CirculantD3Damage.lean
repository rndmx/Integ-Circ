/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Out

/-!
# Damage bookkeeping for outputs blocks

`CircNet/Circulant.lean` splits the damage of a *complement-cut* block into its exit points and
their predecessors.  This file does the same for a block severing its **outputs**, where
the cut set is `(B ∪ O) \ q` rather than `qᶜ`.

Three disjoint families of damaged units arise, distinguished by where the successor lands:

* `oExit`     — the successor is already in another outputs block;
* `oPreExit`  — the successor stays inside `q`, but the *second* successor leaves;
* `oCross`    — the successor lands in the complement-cut region, and the second successor
                lands in another outputs block, i.e. the walk **jumps a width-one gap**.

`oCross` is the formal counterpart of the observation that a gap of width one cannot
separate two outputs blocks: `shift²` steps straight over it.  A gap of width two or more
blocks both steps, but then that run of the complement-cut region is long, and long runs
are exactly what `preExitSet` charges for.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section OutDamage

variable [NeZero N]

/-- Units of `q` whose successor is already in another outputs block. -/
noncomputable def oExit (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) :=
  q.filter fun j => shift j ∈ outRegion θ \ q

/-- Units of `q` whose successor stays inside `q` but whose second successor leaves. -/
noncomputable def oPreExit (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) :=
  q.filter fun j => shift j ∈ q ∧ shift (shift j) ∈ outRegion θ \ q

/-- Units of `q` whose successor lands in the complement-cut region but whose second
successor lands in another outputs block: the width-one gap jump. -/
noncomputable def oCross (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) :=
  q.filter fun j => shift j ∉ outRegion θ ∧ shift (shift j) ∈ outRegion θ \ q

lemma mem_oExit {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oExit θ q ↔ j ∈ q ∧ shift j ∈ outRegion θ \ q := by
  unfold oExit; rw [Finset.mem_filter]

lemma mem_oPreExit {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oPreExit θ q ↔ j ∈ q ∧ shift j ∈ q ∧ shift (shift j) ∈ outRegion θ \ q := by
  unfold oPreExit; rw [Finset.mem_filter]

lemma mem_oCross {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oCross θ q ↔
      j ∈ q ∧ shift j ∉ outRegion θ ∧ shift (shift j) ∈ outRegion θ \ q := by
  unfold oCross; rw [Finset.mem_filter]

/-- Anything in the outputs region but outside `q` lies in `q`'s cut set. -/
lemma mem_cutSet_of_mem_outRegion_sdiff (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs)
    {x : Fin N} (hx : x ∈ outRegion θ \ q) : x ∈ θ.cutSet q := by
  rw [cutSet_outputs_eq θ hq hdq]
  obtain ⟨hxo, hxq⟩ := Finset.mem_sdiff.1 hx
  exact Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hxo, hxq⟩

/-- **All three families consist of damaged units.** -/
theorem oExit_subset_damaged (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    oExit θ q ⊆ damaged θ := by
  intro j hj
  obtain ⟨hjq, hsj⟩ := mem_oExit.1 hj
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨shift j, mem_liveInputs.2 (Or.inl rfl), ?_⟩⟩
  rw [θ.partOf_eq hq hjq]
  exact mem_cutSet_of_mem_outRegion_sdiff θ hq hdq hsj

theorem oPreExit_subset_damaged (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    oPreExit θ q ⊆ damaged θ := by
  intro j hj
  obtain ⟨hjq, -, hssj⟩ := mem_oPreExit.1 hj
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨shift (shift j), mem_liveInputs.2 (Or.inr rfl), ?_⟩⟩
  rw [θ.partOf_eq hq hjq]
  exact mem_cutSet_of_mem_outRegion_sdiff θ hq hdq hssj

theorem oCross_subset_damaged (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    oCross θ q ⊆ damaged θ := by
  intro j hj
  obtain ⟨hjq, -, hssj⟩ := mem_oCross.1 hj
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨shift (shift j), mem_liveInputs.2 (Or.inr rfl), ?_⟩⟩
  rw [θ.partOf_eq hq hjq]
  exact mem_cutSet_of_mem_outRegion_sdiff θ hq hdq hssj

/-- **The three families are pairwise disjoint**, separated by where the successor lands:
in another outputs block, inside `q`, or in the complement-cut region. -/
theorem oExit_disjoint_oPreExit (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Disjoint (oExit θ q) (oPreExit θ q) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact (Finset.mem_sdiff.1 (mem_oExit.1 hj).2).2 (mem_oPreExit.1 hj').2.1

theorem oExit_disjoint_oCross (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Disjoint (oExit θ q) (oCross θ q) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact (mem_oCross.1 hj').2.1 (Finset.mem_sdiff.1 (mem_oExit.1 hj).2).1

theorem oPreExit_disjoint_oCross (θ : SysPartition N Finset.univ) (q : Finset (Fin N))
    (hq : q ⊆ outRegion θ) : Disjoint (oPreExit θ q) (oCross θ q) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact (mem_oCross.1 hj').2.1 (hq (mem_oPreExit.1 hj).2.1)

/-- **The damage charged to an outputs block is at least the size of the three
families.** -/
theorem card_oFamilies_le (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    (oExit θ q).card + (oPreExit θ q).card + (oCross θ q).card
      ≤ (damaged θ ∩ q).card := by
  classical
  have hqO : q ⊆ outRegion θ := subset_outRegion θ hq hdq
  have hsub : oExit θ q ∪ oPreExit θ q ∪ oCross θ q ⊆ damaged θ ∩ q := by
    intro j hj
    have hjq : j ∈ q := by
      rcases Finset.mem_union.1 hj with h | h
      · rcases Finset.mem_union.1 h with h' | h'
        · exact (mem_oExit.1 h').1
        · exact (mem_oPreExit.1 h').1
      · exact (mem_oCross.1 h).1
    refine Finset.mem_inter.2 ⟨?_, hjq⟩
    rcases Finset.mem_union.1 hj with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · exact oExit_subset_damaged θ hq hdq h'
      · exact oPreExit_subset_damaged θ hq hdq h'
    · exact oCross_subset_damaged θ hq hdq h
  have hd1 : Disjoint (oExit θ q ∪ oPreExit θ q) (oCross θ q) :=
    Finset.disjoint_union_left.2
      ⟨oExit_disjoint_oCross θ q, oPreExit_disjoint_oCross θ q hqO⟩
  calc (oExit θ q).card + (oPreExit θ q).card + (oCross θ q).card
      = (oExit θ q ∪ oPreExit θ q).card + (oCross θ q).card := by
        rw [Finset.card_union_of_disjoint (oExit_disjoint_oPreExit θ q)]
    _ = (oExit θ q ∪ oPreExit θ q ∪ oCross θ q).card := by
        rw [Finset.card_union_of_disjoint hd1]
    _ ≤ (damaged θ ∩ q).card := Finset.card_le_card hsub

/-! ## The damage budget

The blocks partition the substrate, so the damaged units split across them.  Charging each
complement-cut block its exact damage and each outputs block its three families turns the
budget `damagedCount θ = 3` into a single arithmetic constraint.
-/

/-- The damaged units split across the blocks. -/
theorem damagedCount_eq_sum (θ : SysPartition N Finset.univ) :
    damagedCount θ = ∑ p ∈ θ.parts, (damaged θ ∩ p).card := by
  classical
  have hbi : damaged θ = θ.parts.biUnion fun p => damaged θ ∩ p := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hj
      obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
      exact ⟨p, hp, hj, hjp⟩
    · rintro ⟨p, -, hj, -⟩
      exact hj
  have hdisj : ∀ p ∈ θ.parts, ∀ q ∈ θ.parts, p ≠ q →
      Disjoint (damaged θ ∩ p) (damaged θ ∩ q) := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.1 (θ.parts_disjoint p hp q hq hpq)
      (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2
  rw [damagedCount]
  conv_lhs => rw [hbi]
  rw [Finset.card_biUnion hdisj]

/-- **The damage budget.**  Complement-cut blocks are charged exactly their exit and
pre-exit points; outputs blocks are charged their three families. -/
theorem damage_budget (θ : SysPartition N Finset.univ) :
    (∑ p ∈ compCutBlocks θ, ((exitSet p).card + (preExitSet p).card))
      + ∑ q ∈ outBlocks θ,
          ((oExit θ q).card + (oPreExit θ q).card + (oCross θ q).card)
      ≤ damagedCount θ := by
  classical
  rw [damagedCount_eq_sum θ, parts_eq_union θ,
    Finset.sum_union (compCut_disjoint_outBlocks θ)]
  refine Nat.add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun p hp => ?_
    have hpp := (mem_compCutBlocks.1 hp).1
    have hpd := (mem_compCutBlocks.1 hp).2
    exact le_of_eq (card_damaged_inter θ hpp (cutSet_compl_of_ne_outputs θ hpd)).symm
  · refine Finset.sum_le_sum fun q hq => ?_
    exact card_oFamilies_le θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2

/-! ## Why an extra outputs block must be a singleton

If a unit of `q` exits into another outputs block and its *predecessor* also lies in `q`,
that predecessor is charged too: its successor stays inside `q` but its second successor
leaves.  So a block that exits into another outputs block costs **two** unless the exit
happens at the very start of one of its runs -- which for a single-run block means the
block is a singleton.
-/

/-- **The propagation lemma.**  An exit whose predecessor is inside the block charges that
predecessor as well. -/
theorem pred_mem_oPreExit_of_mem_oExit (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} {j : Fin N} (hj : j ∈ oExit θ q) (hpj : pred j ∈ q) :
    pred j ∈ oPreExit θ q := by
  obtain ⟨hjq, hsj⟩ := mem_oExit.1 hj
  refine mem_oPreExit.2 ⟨hpj, ?_, ?_⟩
  · rw [shift_pred]; exact hjq
  · rw [shift_pred]; exact hsj

/-- A block that exits into another outputs block, at a point whose predecessor is inside
the block, is charged at least two. -/
theorem two_le_oDamage (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    {j : Fin N} (hj : j ∈ oExit θ q) (hpj : pred j ∈ q) :
    2 ≤ (oExit θ q).card + (oPreExit θ q).card := by
  classical
  have h1 : 1 ≤ (oExit θ q).card := Finset.card_pos.2 ⟨j, hj⟩
  have h2 : 1 ≤ (oPreExit θ q).card :=
    Finset.card_pos.2 ⟨pred j, pred_mem_oPreExit_of_mem_oExit θ hj hpj⟩
  omega

/-- A singleton outputs block has no pre-exit point: there is no room for one. -/
theorem oPreExit_singleton_eq_empty (θ : SysPartition N Finset.univ) (hN : 3 ≤ N)
    (a : Fin N) : oPreExit θ ({a} : Finset (Fin N)) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  obtain ⟨hjq, hsj, -⟩ := mem_oPreExit.1 hj
  rw [Finset.mem_singleton] at hjq hsj
  subst hjq
  exact shift_ne_self hN j hsj

/-! ## Counting the runs of the complement-cut region -/

/-- The complement-cut region. -/
noncomputable def compCutRegion (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  (compCutBlocks θ).sup id

lemma mem_compCutRegion {θ : SysPartition N Finset.univ} {x : Fin N} :
    x ∈ compCutRegion θ ↔ ∃ p ∈ compCutBlocks θ, x ∈ p := by
  unfold compCutRegion
  rw [Finset.mem_sup]
  simp only [id]

/-- **Every run of the complement-cut region is charged.**  A unit leaving the region
leaves its own block too, so the region's exit points inject into the blocks' exit
points. -/
theorem card_exitSet_compCutRegion_le (θ : SysPartition N Finset.univ) :
    (exitSet (compCutRegion θ)).card ≤ ∑ p ∈ compCutBlocks θ, (exitSet p).card := by
  classical
  have hsub : exitSet (compCutRegion θ)
      ⊆ (compCutBlocks θ).biUnion fun p => exitSet p := by
    intro j hj
    obtain ⟨hjC, hsj⟩ := mem_exitSet.1 hj
    obtain ⟨p, hp, hjp⟩ := mem_compCutRegion.1 hjC
    refine Finset.mem_biUnion.2 ⟨p, hp, mem_exitSet.2 ⟨hjp, ?_⟩⟩
    intro hcon
    exact hsj (mem_compCutRegion.2 ⟨p, hp, hcon⟩)
  calc (exitSet (compCutRegion θ)).card
      ≤ ((compCutBlocks θ).biUnion fun p => exitSet p).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ compCutBlocks θ, (exitSet p).card := Finset.card_biUnion_le

/-! ## Wide runs of the complement-cut region are charged twice

A run of the complement-cut region of width one is charged once: its last unit steps out.
A run of width two or more is charged **twice** -- its last unit steps out, and that unit's
predecessor is charged as well, because its *second* step leaves.

This is the formal price of a protecting gap.  A width-one gap is cheap but lets `shift²`
jump it (an `oCross`); a wider gap blocks `shift²` but pays for itself here.
-/

lemma pred_injective : Function.Injective (pred : Fin N → Fin N) := by
  intro x y h
  have := congrArg shift h
  rwa [shift_pred, shift_pred] at this

/-- The exit points of the complement-cut region whose run has width at least two. -/
noncomputable def wideExits (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  (exitSet (compCutRegion θ)).filter fun y => pred y ∈ compCutRegion θ

lemma mem_wideExits {θ : SysPartition N Finset.univ} {y : Fin N} :
    y ∈ wideExits θ ↔ y ∈ exitSet (compCutRegion θ) ∧ pred y ∈ compCutRegion θ := by
  unfold wideExits; rw [Finset.mem_filter]

/-- A unit of the complement-cut region whose successor leaves it is damaged. -/
lemma mem_damaged_of_mem_exitSet_compCutRegion (θ : SysPartition N Finset.univ)
    {y : Fin N} (hy : y ∈ exitSet (compCutRegion θ)) : y ∈ damaged θ := by
  obtain ⟨hyC, hsy⟩ := mem_exitSet.1 hy
  obtain ⟨p, hp, hyp⟩ := mem_compCutRegion.1 hyC
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨shift y, mem_liveInputs.2 (Or.inl rfl), ?_⟩⟩
  rw [θ.partOf_eq (mem_compCutBlocks.1 hp).1 hyp,
    cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hp).2, Finset.mem_compl]
  intro hcon
  exact hsy (mem_compCutRegion.2 ⟨p, hp, hcon⟩)

/-- The predecessor of a wide run's exit is damaged too: its second step leaves. -/
lemma pred_mem_damaged_of_mem_wideExits (θ : SysPartition N Finset.univ)
    {y : Fin N} (hy : y ∈ wideExits θ) : pred y ∈ damaged θ := by
  obtain ⟨hyE, hpC⟩ := mem_wideExits.1 hy
  obtain ⟨-, hsy⟩ := mem_exitSet.1 hyE
  obtain ⟨p, hp, hpp⟩ := mem_compCutRegion.1 hpC
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _,
    ⟨shift (shift (pred y)), mem_liveInputs.2 (Or.inr rfl), ?_⟩⟩
  rw [θ.partOf_eq (mem_compCutBlocks.1 hp).1 hpp,
    cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hp).2, Finset.mem_compl, shift_pred]
  intro hcon
  exact hsy (mem_compCutRegion.2 ⟨p, hp, hcon⟩)

/-- **Wide runs cost an extra unit of damage.**  The region's exit points and the
predecessors of its wide exits are disjoint families of damaged units inside the
region. -/
theorem card_exit_add_wide_le (θ : SysPartition N Finset.univ) :
    (exitSet (compCutRegion θ)).card + (wideExits θ).card
      ≤ (damaged θ ∩ compCutRegion θ).card := by
  classical
  have hinj : ((wideExits θ).image pred).card = (wideExits θ).card :=
    Finset.card_image_of_injective _ pred_injective
  have hdisj : Disjoint (exitSet (compCutRegion θ)) ((wideExits θ).image pred) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨-, hsz⟩ := mem_exitSet.1 hz
    rw [shift_pred] at hsz
    exact hsz (mem_exitSet.1 (mem_wideExits.1 hy).1).1
  have hsub : exitSet (compCutRegion θ) ∪ (wideExits θ).image pred
      ⊆ damaged θ ∩ compCutRegion θ := by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact Finset.mem_inter.2 ⟨mem_damaged_of_mem_exitSet_compCutRegion θ h,
        (mem_exitSet.1 h).1⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_inter.2 ⟨pred_mem_damaged_of_mem_wideExits θ hy,
        (mem_wideExits.1 hy).2⟩
  calc (exitSet (compCutRegion θ)).card + (wideExits θ).card
      = (exitSet (compCutRegion θ)).card + ((wideExits θ).image pred).card := by rw [hinj]
    _ = (exitSet (compCutRegion θ) ∪ (wideExits θ).image pred).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (damaged θ ∩ compCutRegion θ).card := Finset.card_le_card hsub

/-! ## Exit points propagate backwards

If a unit exits into another outputs block and its predecessor lies in the outputs region
but in a *different* block, then that predecessor exits too.  So exit points chain
backwards along the outputs region until they run out of room.

Together with `pred_mem_oPreExit_of_mem_oExit` this is a dichotomy with no third option:
walking back from an exit, each step either lands in the same block -- charging a
pre-exit -- or lands in a different one, charging another exit.  Either way the walk is
paid for, and a budget of three cannot pay for long.
-/

/-- The union of all outputs blocks is the outputs region. -/
lemma partOf_mem_outBlocks_of_mem_outRegion (θ : SysPartition N Finset.univ)
    {j : Fin N} (hj : j ∈ outRegion θ) : θ.partOf j ∈ outBlocks θ ∧ j ∈ θ.partOf j := by
  obtain ⟨p, hp, hdp, hjp⟩ := mem_outRegion.1 hj
  rw [θ.partOf_eq hp hjp]
  exact ⟨mem_outBlocks.2 ⟨hp, hdp⟩, hjp⟩

/-- **Backward propagation.**  If `j` lies in an outputs block and the predecessor of `j`
lies in the outputs region but outside that block, then the predecessor is itself an exit
point of its own block. -/
theorem pred_mem_oExit_of_mem_outBlock (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} {j : Fin N} (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs)
    (hjq : j ∈ q) (hpO : pred j ∈ outRegion θ) (hpq : pred j ∉ q) :
    pred j ∈ oExit θ (θ.partOf (pred j)) := by
  classical
  obtain ⟨-, hpp⟩ := partOf_mem_outBlocks_of_mem_outRegion θ hpO
  refine mem_oExit.2 ⟨hpp, ?_⟩
  rw [shift_pred]
  refine Finset.mem_sdiff.2 ⟨mem_outRegion.2 ⟨q, hq, hdq, hjq⟩, ?_⟩
  intro hcon
  have h1 : θ.partOf j = θ.partOf (pred j) :=
    θ.partOf_eq (partOf_mem_parts θ (pred j)) hcon
  have h2 : θ.partOf j = q := θ.partOf_eq hq hjq
  rw [h2] at h1
  rw [← h1] at hpp
  exact hpq hpp

/-- **The dichotomy.**  Walking back one step from a unit of an outputs block, either the
predecessor is charged a pre-exit (same block) or it is charged an exit (different block)
-- provided it is still in the outputs region.  There is no free step. -/
theorem pred_charged (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    {j : Fin N} (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs)
    (hj : j ∈ oExit θ q) (hpO : pred j ∈ outRegion θ) :
    pred j ∈ oPreExit θ q ∨ pred j ∈ oExit θ (θ.partOf (pred j)) := by
  classical
  by_cases hpq : pred j ∈ q
  · exact Or.inl (pred_mem_oPreExit_of_mem_oExit θ hj hpq)
  · exact Or.inr (pred_mem_oExit_of_mem_outBlock θ hq hdq (mem_oExit.1 hj).1 hpO hpq)

/-! ## The budget, in region form

Recasting `damage_budget` so the complement-cut side is charged by its *runs* rather than
block by block.  This is the form the structural argument uses: the number of runs of the
complement-cut region, plus the number of wide ones, plus everything charged on the
outputs side, all fit inside the budget.
-/

/-- The damaged units of the complement-cut region, block by block. -/
lemma sum_damaged_compCut (θ : SysPartition N Finset.univ) :
    ∑ p ∈ compCutBlocks θ, (damaged θ ∩ p).card
      = (damaged θ ∩ compCutRegion θ).card := by
  classical
  have hbi : damaged θ ∩ compCutRegion θ
      = (compCutBlocks θ).biUnion fun p => damaged θ ∩ p := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨hjd, hjC⟩
      obtain ⟨p, hp, hjp⟩ := mem_compCutRegion.1 hjC
      exact ⟨p, hp, hjd, hjp⟩
    · rintro ⟨p, hp, hjd, hjp⟩
      exact ⟨hjd, mem_compCutRegion.2 ⟨p, hp, hjp⟩⟩
  have hdisj : ∀ p ∈ compCutBlocks θ, ∀ q ∈ compCutBlocks θ, p ≠ q →
      Disjoint (damaged θ ∩ p) (damaged θ ∩ q) := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 q (mem_compCutBlocks.1 hq).1 hpq)
      (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2
  rw [hbi, Finset.card_biUnion hdisj]

/-- **The budget in region form.**  The runs of the complement-cut region, the wide ones
among them, and every family charged on the outputs side all fit inside the damage. -/
theorem damage_budget_region (θ : SysPartition N Finset.univ) :
    (exitSet (compCutRegion θ)).card + (wideExits θ).card
      + ∑ q ∈ outBlocks θ,
          ((oExit θ q).card + (oPreExit θ q).card + (oCross θ q).card)
      ≤ damagedCount θ := by
  classical
  rw [damagedCount_eq_sum θ, parts_eq_union θ,
    Finset.sum_union (compCut_disjoint_outBlocks θ), sum_damaged_compCut θ]
  refine Nat.add_le_add (card_exit_add_wide_le θ) ?_
  refine Finset.sum_le_sum fun q hq => ?_
  exact card_oFamilies_le θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2

/-- The complement-cut region is nonempty as soon as some block is not an outputs
block. -/
lemma compCutRegion_nonempty (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ) : (compCutRegion θ).Nonempty := by
  obtain ⟨x, hx⟩ := θ.parts_nonempty p (mem_compCutBlocks.1 hp).1
  exact ⟨x, mem_compCutRegion.2 ⟨p, hp, hx⟩⟩

/-- A nonempty set with no exit is shift-closed, hence everything. -/
lemma exitSet_nonempty_of_ne_univ {S : Finset (Fin N)} (hSne : S.Nonempty)
    (hne : S ≠ Finset.univ) : (exitSet S).Nonempty := by
  classical
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hcl : ∀ j ∈ S, shift j ∈ S := by
    intro j hj
    by_contra hcon
    have : j ∈ exitSet S := mem_exitSet.2 ⟨hj, hcon⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty j)
  exact hne (eq_univ_of_shift_closed hSne hcl)

/-- **At least one run.**  A nonempty proper region has an exit. -/
lemma one_le_card_exitSet_compCutRegion (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ)
    (hne : compCutRegion θ ≠ Finset.univ) :
    1 ≤ (exitSet (compCutRegion θ)).card := by
  classical
  obtain ⟨x, hx⟩ := exitSet_nonempty_of_ne_univ (compCutRegion_nonempty θ hp) hne
  exact Finset.card_pos.2 ⟨x, hx⟩

/-- **The key consequence.**  With a damage budget of three and at least one
complement-cut block, everything charged on the outputs side, together with the wide runs,
fits in two. -/
theorem out_charge_le_two (θ : SysPartition N Finset.univ) (hD : damagedCount θ = 3)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ)
    (hne : compCutRegion θ ≠ Finset.univ) :
    (wideExits θ).card
      + ∑ q ∈ outBlocks θ,
          ((oExit θ q).card + (oPreExit θ q).card + (oCross θ q).card)
      ≤ 2 := by
  have h1 := damage_budget_region θ
  have h2 := one_le_card_exitSet_compCutRegion θ hp hne
  omega

/-! ## The full four-way charge

The three families above miss a case: a unit whose successor lands directly in the `both`
region is damaged too, since `B` lies in every outputs block's cut set.  Classifying
instead by **where the successor lands** gives a genuine four-way partition of the charged
units of an outputs block `q`:

* `oA` -- the successor is in another outputs block;
* `oB` -- the successor is in the `both` region;
* `oC` -- the successor stays in `q`, and the second successor leaves into `O \ q` or `B`;
* `oD` -- the successor is in the inputs region, and the second successor leaves likewise.

Disjointness is immediate: `O \ q`, `B`, `q` and the inputs region are pairwise disjoint.
`oB` is what charges the interface between the `both` region and the outputs region, and
it is what forbids a large `both` region from sitting next to a large outputs region.
-/

/-- The inputs region: complement-cut units that are not in the `both` region. -/
noncomputable def inRegion (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  compCutRegion θ \ bothRegion θ

/-- Successor in another outputs block. -/
noncomputable def oA (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) := q.filter fun j => shift j ∈ outRegion θ \ q

/-- Successor in the `both` region: the interface charge. -/
noncomputable def oB (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) := q.filter fun j => shift j ∈ bothRegion θ

/-- Successor stays inside `q`, second successor leaves. -/
noncomputable def oC (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) :=
  q.filter fun j => shift j ∈ q ∧
    (shift (shift j) ∈ outRegion θ \ q ∨ shift (shift j) ∈ bothRegion θ)

/-- Successor in the inputs region, second successor leaves. -/
noncomputable def oD (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) :=
  q.filter fun j => shift j ∈ inRegion θ ∧
    (shift (shift j) ∈ outRegion θ \ q ∨ shift (shift j) ∈ bothRegion θ)

lemma mem_oA {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oA θ q ↔ j ∈ q ∧ shift j ∈ outRegion θ \ q := by
  unfold oA; rw [Finset.mem_filter]

lemma mem_oB {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oB θ q ↔ j ∈ q ∧ shift j ∈ bothRegion θ := by
  unfold oB; rw [Finset.mem_filter]

lemma mem_oC {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oC θ q ↔ j ∈ q ∧ shift j ∈ q ∧
      (shift (shift j) ∈ outRegion θ \ q ∨ shift (shift j) ∈ bothRegion θ) := by
  unfold oC; rw [Finset.mem_filter]

lemma mem_oD {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oD θ q ↔ j ∈ q ∧ shift j ∈ inRegion θ ∧
      (shift (shift j) ∈ outRegion θ \ q ∨ shift (shift j) ∈ bothRegion θ) := by
  unfold oD; rw [Finset.mem_filter]

/-- Anything in the `both` region lies in every outputs block's cut set. -/
lemma mem_cutSet_of_mem_bothRegion (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs)
    {x : Fin N} (hx : x ∈ bothRegion θ) : x ∈ θ.cutSet q := by
  rw [cutSet_outputs_eq θ hq hdq]
  refine Finset.mem_sdiff.2 ⟨Finset.mem_union_left _ hx, ?_⟩
  intro hxq
  exact Finset.disjoint_left.1 (bothRegion_disjoint_outRegion θ) hx
    (subset_outRegion θ hq hdq hxq)

/-- **All four families are damaged.** -/
theorem oFour_subset_damaged (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    oA θ q ∪ oB θ q ∪ oC θ q ∪ oD θ q ⊆ damaged θ := by
  classical
  have key : ∀ j ∈ q, ∀ x, (x = shift j ∨ x = shift (shift j)) →
      (x ∈ outRegion θ \ q ∨ x ∈ bothRegion θ) → j ∈ damaged θ := by
    intro j hjq x hx hxc
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨x, ?_, ?_⟩⟩
    · rcases hx with rfl | rfl
      · exact mem_liveInputs.2 (Or.inl rfl)
      · exact mem_liveInputs.2 (Or.inr rfl)
    · rw [θ.partOf_eq hq hjq]
      rcases hxc with h | h
      · exact mem_cutSet_of_mem_outRegion_sdiff θ hq hdq h
      · exact mem_cutSet_of_mem_bothRegion θ hq hdq h
  intro j hj
  rcases Finset.mem_union.1 hj with h | h
  · rcases Finset.mem_union.1 h with h' | h'
    · rcases Finset.mem_union.1 h' with h'' | h''
      · exact key j (mem_oA.1 h'').1 _ (Or.inl rfl) (Or.inl (mem_oA.1 h'').2)
      · exact key j (mem_oB.1 h'').1 _ (Or.inl rfl) (Or.inr (mem_oB.1 h'').2)
    · exact key j (mem_oC.1 h').1 _ (Or.inr rfl) (mem_oC.1 h').2.2
  · exact key j (mem_oD.1 h).1 _ (Or.inr rfl) (mem_oD.1 h).2.2

/-- The four regions the successor can land in are pairwise disjoint. -/
lemma outRegion_sdiff_disjoint_bothRegion (θ : SysPartition N Finset.univ)
    (q : Finset (Fin N)) : Disjoint (outRegion θ \ q) (bothRegion θ) := by
  rw [Finset.disjoint_left]
  intro x hx hxb
  exact Finset.disjoint_left.1 (bothRegion_disjoint_outRegion θ) hxb
    (Finset.mem_sdiff.1 hx).1

lemma inRegion_disjoint_outRegion (θ : SysPartition N Finset.univ) :
    Disjoint (inRegion θ) (outRegion θ) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hxo
  obtain ⟨hxC, -⟩ := Finset.mem_sdiff.1 hx
  obtain ⟨p, hp, hxp⟩ := mem_compCutRegion.1 hxC
  obtain ⟨p', hp', hd', hxp'⟩ := mem_outRegion.1 hxo
  have hne : p ≠ p' := by
    rintro rfl
    exact (mem_compCutBlocks.1 hp).2 hd'
  exact Finset.disjoint_left.1
    (θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 p' hp' hne) hxp hxp'

lemma inRegion_disjoint_bothRegion (θ : SysPartition N Finset.univ) :
    Disjoint (inRegion θ) (bothRegion θ) := by
  rw [Finset.disjoint_left]
  intro x hx hxb
  exact (Finset.mem_sdiff.1 hx).2 hxb

/-- **The four families are pairwise disjoint**, separated by where the successor
lands. -/
theorem oFour_card (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    (oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card
      ≤ (damaged θ ∩ q).card := by
  classical
  have hqO : q ⊆ outRegion θ := subset_outRegion θ hq hdq
  -- pairwise disjointness, all by the location of `shift j`
  have dAB : Disjoint (oA θ q) (oB θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact Finset.disjoint_left.1 (outRegion_sdiff_disjoint_bothRegion θ q)
      (mem_oA.1 h).2 (mem_oB.1 h').2
  have dAC : Disjoint (oA θ q) (oC θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact (Finset.mem_sdiff.1 (mem_oA.1 h).2).2 (mem_oC.1 h').2.1
  have dAD : Disjoint (oA θ q) (oD θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact Finset.disjoint_left.1 (inRegion_disjoint_outRegion θ)
      (mem_oD.1 h').2.1 (Finset.mem_sdiff.1 (mem_oA.1 h).2).1
  have dBC : Disjoint (oB θ q) (oC θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact Finset.disjoint_left.1 (bothRegion_disjoint_outRegion θ)
      (mem_oB.1 h).2 (hqO (mem_oC.1 h').2.1)
  have dBD : Disjoint (oB θ q) (oD θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact Finset.disjoint_left.1 (inRegion_disjoint_bothRegion θ)
      (mem_oD.1 h').2.1 (mem_oB.1 h).2
  have dCD : Disjoint (oC θ q) (oD θ q) := by
    rw [Finset.disjoint_left]; intro j h h'
    exact Finset.disjoint_left.1 (inRegion_disjoint_outRegion θ)
      (mem_oD.1 h').2.1 (hqO (mem_oC.1 h).2.1)
  have hsub : oA θ q ∪ oB θ q ∪ oC θ q ∪ oD θ q ⊆ damaged θ ∩ q := by
    intro j hj
    refine Finset.mem_inter.2 ⟨oFour_subset_damaged θ hq hdq hj, ?_⟩
    rcases Finset.mem_union.1 hj with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · rcases Finset.mem_union.1 h' with h'' | h''
        · exact (mem_oA.1 h'').1
        · exact (mem_oB.1 h'').1
      · exact (mem_oC.1 h').1
    · exact (mem_oD.1 h).1
  have d1 : Disjoint (oA θ q ∪ oB θ q) (oC θ q) :=
    Finset.disjoint_union_left.2 ⟨dAC, dBC⟩
  have d2 : Disjoint (oA θ q ∪ oB θ q ∪ oC θ q) (oD θ q) :=
    Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_left.2 ⟨dAD, dBD⟩, dCD⟩
  calc (oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card
      = (oA θ q ∪ oB θ q).card + (oC θ q).card + (oD θ q).card := by
        rw [Finset.card_union_of_disjoint dAB]
    _ = (oA θ q ∪ oB θ q ∪ oC θ q).card + (oD θ q).card := by
        rw [Finset.card_union_of_disjoint d1]
    _ = (oA θ q ∪ oB θ q ∪ oC θ q ∪ oD θ q).card := by
        rw [Finset.card_union_of_disjoint d2]
    _ ≤ (damaged θ ∩ q).card := Finset.card_le_card hsub

/-! ## Counting the outputs blocks -/

/-- Units of an outputs block whose successor leaves the outputs region entirely. -/
noncomputable def oOut (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Finset (Fin N) := q.filter fun j => shift j ∉ outRegion θ

lemma mem_oOut {θ : SysPartition N Finset.univ} {q : Finset (Fin N)} {j : Fin N} :
    j ∈ oOut θ q ↔ j ∈ q ∧ shift j ∉ outRegion θ := by
  unfold oOut; rw [Finset.mem_filter]

/-- **Exits split by destination.** -/
theorem exitSet_eq_oA_union_oOut (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} (hq : q ∈ θ.parts) (hdq : θ.dir q = Dir.outputs) :
    exitSet q = oA θ q ∪ oOut θ q := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨hjq, hsj⟩ := mem_exitSet.1 hj
    by_cases hmem : shift j ∈ outRegion θ
    · exact Finset.mem_union_left _ (mem_oA.2 ⟨hjq, Finset.mem_sdiff.2 ⟨hmem, hsj⟩⟩)
    · exact Finset.mem_union_right _ (mem_oOut.2 ⟨hjq, hmem⟩)
  · intro hj
    rcases Finset.mem_union.1 hj with h | h
    · obtain ⟨hjq, hsj⟩ := mem_oA.1 h
      exact mem_exitSet.2 ⟨hjq, (Finset.mem_sdiff.1 hsj).2⟩
    · obtain ⟨hjq, hsj⟩ := mem_oOut.1 h
      exact mem_exitSet.2 ⟨hjq, fun hc => hsj (subset_outRegion θ hq hdq hc)⟩

lemma oA_disjoint_oOut (θ : SysPartition N Finset.univ) (q : Finset (Fin N)) :
    Disjoint (oA θ q) (oOut θ q) := by
  rw [Finset.disjoint_left]
  intro j h h'
  exact (mem_oOut.1 h').2 (Finset.mem_sdiff.1 (mem_oA.1 h).2).1

/-- Each outputs block has at least one exit. -/
theorem card_outBlocks_le_sum_exit (θ : SysPartition N Finset.univ) :
    (outBlocks θ).card ≤ ∑ q ∈ outBlocks θ, (exitSet q).card := by
  classical
  calc (outBlocks θ).card = ∑ _q ∈ outBlocks θ, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ q ∈ outBlocks θ, (exitSet q).card := by
        refine Finset.sum_le_sum fun q hq => ?_
        refine Finset.card_pos.2 (exitSet_nonempty_of_ne_univ
          (θ.parts_nonempty q (mem_outBlocks.1 hq).1) ?_)
        intro hcon
        exact block_ne_univ θ (mem_outBlocks.1 hq).1 hcon

/-- **The block count bound.** -/
theorem card_outBlocks_le (θ : SysPartition N Finset.univ) :
    (outBlocks θ).card
      ≤ (∑ q ∈ outBlocks θ, (oA θ q).card) + ∑ q ∈ outBlocks θ, (oOut θ q).card := by
  classical
  refine le_trans (card_outBlocks_le_sum_exit θ) ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q hq => ?_
  rw [exitSet_eq_oA_union_oOut θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2,
    Finset.card_union_of_disjoint (oA_disjoint_oOut θ q)]

/-! ## The complete four-family region budget

Combining the wide-run charge on the complement-cut side with the four-family charge on
the outputs side gives a single inequality: the runs of the complement-cut region, the
wide ones among them, and every outputs charge together fit inside the damage.
-/

/-- The damaged units of the outputs region, block by block. -/
lemma sum_damaged_out (θ : SysPartition N Finset.univ) :
    ∑ q ∈ outBlocks θ, (damaged θ ∩ q).card = (damaged θ ∩ outRegion θ).card := by
  classical
  have hbi : damaged θ ∩ outRegion θ = (outBlocks θ).biUnion fun q => damaged θ ∩ q := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨hjd, hjo⟩
      obtain ⟨p, hp, hdp, hjp⟩ := mem_outRegion.1 hjo
      exact ⟨p, mem_outBlocks.2 ⟨hp, hdp⟩, hjd, hjp⟩
    · rintro ⟨q, hq, hjd, hjq⟩
      exact ⟨hjd, mem_outRegion.2 ⟨q, (mem_outBlocks.1 hq).1, (mem_outBlocks.1 hq).2, hjq⟩⟩
  have hdisj : ∀ p ∈ outBlocks θ, ∀ q ∈ outBlocks θ, p ≠ q →
      Disjoint (damaged θ ∩ p) (damaged θ ∩ q) := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_outBlocks.1 hp).1 q (mem_outBlocks.1 hq).1 hpq)
      (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2
  rw [hbi, Finset.card_biUnion hdisj]

/-- `damaged` splits across the two regions. -/
lemma damagedCount_eq_regions (θ : SysPartition N Finset.univ) :
    damagedCount θ = (damaged θ ∩ compCutRegion θ).card + (damaged θ ∩ outRegion θ).card := by
  classical
  have hdisj : Disjoint (damaged θ ∩ compCutRegion θ) (damaged θ ∩ outRegion θ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨p, hp, hxp⟩ := mem_compCutRegion.1 (Finset.mem_inter.1 hx).2
    obtain ⟨p', hp', hd', hxp'⟩ := mem_outRegion.1 (Finset.mem_inter.1 hx').2
    have hne : p ≠ p' := fun h => (mem_compCutBlocks.1 hp).2 (h ▸ hd')
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 p' hp' hne) hxp hxp'
  have hcover : damaged θ = (damaged θ ∩ compCutRegion θ) ∪ (damaged θ ∩ outRegion θ) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hj
      obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
      by_cases hd : θ.dir p = Dir.outputs
      · exact Or.inr ⟨hj, mem_outRegion.2 ⟨p, hp, hd, hjp⟩⟩
      · exact Or.inl ⟨hj, mem_compCutRegion.2 ⟨p, mem_compCutBlocks.2 ⟨hp, hd⟩, hjp⟩⟩
    · rintro (⟨hj, -⟩ | ⟨hj, -⟩) <;> exact hj
  rw [damagedCount]
  conv_lhs => rw [hcover]
  rw [Finset.card_union_of_disjoint hdisj]

/-- **The four-family region budget.** -/
theorem damage_budget_four (θ : SysPartition N Finset.univ) :
    (exitSet (compCutRegion θ)).card + (wideExits θ).card
      + ∑ q ∈ outBlocks θ,
          ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card)
      ≤ damagedCount θ := by
  classical
  rw [damagedCount_eq_regions θ]
  refine Nat.add_le_add (card_exit_add_wide_le θ) ?_
  have hle : ∀ q ∈ outBlocks θ,
      (oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card
        ≤ (damaged θ ∩ q).card :=
    fun q hq => oFour_card θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2
  calc ∑ q ∈ outBlocks θ,
          ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card)
      ≤ ∑ q ∈ outBlocks θ, (damaged θ ∩ q).card := Finset.sum_le_sum hle
    _ = (damaged θ ∩ outRegion θ).card := sum_damaged_out θ

/-- **The outputs side has a budget of two.** -/
theorem out_charge_four_le_two (θ : SysPartition N Finset.univ) (hD : damagedCount θ = 3)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ)
    (hne : compCutRegion θ ≠ Finset.univ) :
    (wideExits θ).card
      + ∑ q ∈ outBlocks θ,
          ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card)
      ≤ 2 := by
  have h1 := damage_budget_four θ
  have h2 := one_le_card_exitSet_compCutRegion θ hp hne
  omega

end OutDamage

end IIT
