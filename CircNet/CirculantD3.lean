/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD2c

/-!
# Structural facts for the `D = 3` classification

The building blocks for bounding the normalizer of a partition of the whole substrate that
damages exactly three units.  The eventual bound is
`sysCutCount θ ≤ 2(N-1) + ⌊(N-1)²/4⌋`, whose extremal shape is a `both` singleton, an
outputs arc, and an inputs arc.

This file isolates the reusable counting facts: a block severing its inputs or both
directions has its own complement as cut set and damages at least one of its own units
(at least two once it has two units), so a damage budget of three admits at most three
such blocks and at most one of size `≥ 2`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section D3Struct

variable [NeZero N]

/-- A block whose direction is not `outputs` has its complement as cut set. -/
lemma cutSet_compl_of_ne_outputs (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hd : θ.dir p ≠ Dir.outputs) : θ.cutSet p = pᶜ :=
  cutSet_eq_compl_of_dir θ (dir_io_of_ne_outputs θ hd)

/-- **At most three blocks sever their inputs or both directions.**  Each such block
damages a distinct unit, so a damage budget of three admits at most three of them. -/
theorem card_le_three_of_damagedCount_three (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) {B : Finset (Finset (Fin N))} (hBsub : B ⊆ θ.parts)
    (hBd : ∀ p ∈ B, θ.dir p ≠ Dir.outputs) : B.card ≤ 3 := by
  have hle := card_le_damagedCount_of_forall_compl θ hBsub
    (fun p hp => cutSet_compl_of_ne_outputs θ (hBd p hp))
  omega

/-- **At most one block of size `≥ 2` severs its inputs or both directions.**  Such a
block damages two of its own units, so two would exceed a budget of three. -/
theorem atMostOne_big_of_damagedCount_three (θ : SysPartition N Finset.univ)
    (hN : 3 ≤ N) (hD : damagedCount θ = 3) {p q : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hq : q ∈ θ.parts) (hpq : p ≠ q)
    (hdp : θ.dir p ≠ Dir.outputs) (hdq : θ.dir q ≠ Dir.outputs)
    (hcp : 2 ≤ p.card) (hcq : 2 ≤ q.card) : False := by
  classical
  obtain ⟨a, ha, a', ha', hne, hda, hda'⟩ :=
    two_le_damaged_of_cutSet_compl θ hp (cutSet_compl_of_ne_outputs θ hdp) hcp
  obtain ⟨b, hb, b', hb', hne', hdb, hdb'⟩ :=
    two_le_damaged_of_cutSet_compl θ hq (cutSet_compl_of_ne_outputs θ hdq) hcq
  have hdisj : Disjoint p q := θ.parts_disjoint p hp q hq hpq
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb)
  have hab' : a ≠ b' := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb')
  have ha'b : a' ≠ b := fun h => Finset.disjoint_left.1 hdisj ha' (h ▸ hb)
  have ha'b' : a' ≠ b' := fun h => Finset.disjoint_left.1 hdisj ha' (h ▸ hb')
  have hsub : ({a, a', b, b'} : Finset (Fin N)) ⊆ damaged θ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne, hab, hab']),
    Finset.card_insert_of_notMem (by simp [ha'b, ha'b']),
    Finset.card_insert_of_notMem (by simp [hne']),
    Finset.card_singleton] at hcard
  rw [damagedCount] at hD
  omega

/-- The complement-cut blocks of a partition. -/
noncomputable def compCutBlocks (θ : SysPartition N Finset.univ) : Finset (Finset (Fin N)) :=
  θ.parts.filter fun p => θ.dir p ≠ Dir.outputs

omit [NeZero N] in
lemma mem_compCutBlocks {θ : SysPartition N Finset.univ} {p : Finset (Fin N)} :
    p ∈ compCutBlocks θ ↔ p ∈ θ.parts ∧ θ.dir p ≠ Dir.outputs := by
  unfold compCutBlocks
  rw [Finset.mem_filter]

/-- The contribution of a single complement-cut block to the normalizer is
`|p|·(N - |p|)`. -/
lemma cutContribution_compCut (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hd : θ.dir p ≠ Dir.outputs) :
    p.card * (θ.cutSet p).card = p.card * (N - p.card) := by
  rw [cutSet_compl_of_ne_outputs θ hd, Finset.card_compl, Fintype.card_fin]

end D3Struct

end IIT
