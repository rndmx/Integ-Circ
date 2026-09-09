/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Crux
import CircNet.CirculantMain
import CircNet.CirculantCompetitor

/-!
# Exclusion for the window-3 circulant

The last structural facts of the `D = 3` classification, and the assembly.

**Charges.**  Every outputs block other than the whole outputs region is the *target* of a
charged unit: an `oA` point of another block whose successor lands in it, a wide exit of
the complement-cut region whose successor lands in it, or an `oB`/`oD` point of another
block whose second successor lands in it.  Walking back from the block, each step is
either inside the block, a narrow gap that rejoins it, or one of these three charges; so a
block with no charge is `pred`-closed together with its narrow gaps and is everything.
This drops the "outputs region undamaged" hypothesis of `card_outBlocks_le_wideExits`.

**Consequences at damage `≤ 3`.**  With the four-family budget, at most two outputs
blocks (`card_outBlocks_le_two`), and when there are two, the one not containing the
unique exit of the outputs region is a singleton (`exists_singleton_of_two_outBlocks`).

**Relabelling.**  Turning every `both` block into an `outputs` block can only shrink cut
sets, so the damage does not grow; the two consequences above applied to the relabelled
partition give the remaining facts about the `both` region.

**Assembly.**  `sysCutCount_of_damagedCount_three` becomes unconditional, the three-arc
witness starves `D ≤ 3` out of the argmin, `φ_s ≥ 4` for the whole substrate, and with
`sysPhi_circNet_lt_four` for every proper candidate this is `[IIT4, Eq 26]`:
the window-3 circulant is its own complex, for every `N ≥ 8` with `3 ∤ N`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Charges

variable [NeZero N]

/-- The charged units: the wide exits of the complement-cut region together with the
`oA`, `oB` and `oD` points of every outputs block. -/
noncomputable def charges (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  wideExits θ ∪ (outBlocks θ).biUnion fun q => oA θ q ∪ oB θ q ∪ oD θ q

/-- The block a charge is charged to. -/
noncomputable def target (θ : SysPartition N Finset.univ) (x : Fin N) : Finset (Fin N) :=
  if shift x ∈ outRegion θ then θ.partOf (shift x) else θ.partOf (shift (shift x))

lemma card_charges_le (θ : SysPartition N Finset.univ) :
    (charges θ).card ≤ (wideExits θ).card
      + ∑ q ∈ outBlocks θ, ((oA θ q).card + (oB θ q).card + (oD θ q).card) := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun q _ => ?_)
  exact le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- **Every outputs block other than the whole outputs region is the target of a
charge.** -/
theorem exists_charge_of_ne_outRegion (θ : SysPartition N Finset.univ)
    {q : Finset (Fin N)} (hq : q ∈ outBlocks θ) (hne : q ≠ outRegion θ) :
    ∃ x ∈ charges θ, target θ x = q := by
  classical
  by_contra hno
  push_neg at hno
  have hqp := (mem_outBlocks.1 hq).1
  have hqd := (mem_outBlocks.1 hq).2
  have hqsub : q ⊆ outRegion θ := subset_outRegion θ hqp hqd
  have hmemq : ∀ {j}, j ∈ q → θ.partOf j = q := fun {j} hj => θ.partOf_eq hqp hj
  -- the narrow gaps internal to `q`
  set G : Finset (Fin N) :=
    (compCutRegion θ).filter fun z => shift z ∈ q ∧ pred z ∈ q with hG
  set S : Finset (Fin N) := q ∪ G with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := θ.parts_nonempty q hqp
    exact ⟨x, Finset.mem_union_left _ hx⟩
  have hclosed : ∀ j ∈ S, pred j ∈ S := by
    intro j hj
    rcases Finset.mem_union.1 hj with hjq | hjG
    · by_cases hpq : pred j ∈ q
      · exact Finset.mem_union_left _ hpq
      have hjO : j ∈ outRegion θ := hqsub hjq
      by_cases hpO : pred j ∈ outRegion θ
      · -- `pred j` is an `oA` point of its own block, charged to `q`
        exfalso
        obtain ⟨hpb, hpp⟩ := partOf_mem_outBlocks_of_mem_outRegion θ hpO
        have hjnot : j ∉ θ.partOf (pred j) := by
          intro h
          have h1 : θ.partOf j = θ.partOf (pred j) :=
            θ.partOf_eq (partOf_mem_parts θ (pred j)) h
          rw [hmemq hjq] at h1
          rw [← h1] at hpp
          exact hpq hpp
        have hx : pred j ∈ oA θ (θ.partOf (pred j)) :=
          mem_oA.2 ⟨hpp, by rw [shift_pred]; exact Finset.mem_sdiff.2 ⟨hjO, hjnot⟩⟩
        have hxch : pred j ∈ charges θ :=
          Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨_, hpb, Finset.mem_union_left _ (Finset.mem_union_left _ hx)⟩)
        have ht : target θ (pred j) = q := by
          rw [target, if_pos (by rw [shift_pred]; exact hjO), shift_pred]
          exact hmemq hjq
        exact hno _ hxch ht
      · have hpC : pred j ∈ compCutRegion θ := by
          rw [compCutRegion_eq_compl, Finset.mem_compl]; exact hpO
        by_cases hppq : pred (pred j) ∈ q
        · exact Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hpC, by rw [shift_pred]; exact hjq, hppq⟩)
        by_cases hppO : pred (pred j) ∈ outRegion θ
        · -- `pred² j` is an `oB` or `oD` point of its own block, charged to `q`
          exfalso
          obtain ⟨hpb, hpp⟩ := partOf_mem_outBlocks_of_mem_outRegion θ hppO
          have hsx : shift (pred (pred j)) = pred j := shift_pred _
          have hssx : shift (shift (pred (pred j))) = j := by rw [hsx, shift_pred]
          have hjnot : j ∉ θ.partOf (pred (pred j)) := by
            intro h
            have h1 : θ.partOf j = θ.partOf (pred (pred j)) :=
              θ.partOf_eq (partOf_mem_parts θ _) h
            rw [hmemq hjq] at h1
            rw [← h1] at hpp
            exact hppq hpp
          have hxch : pred (pred j) ∈ charges θ := by
            refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hpb, ?_⟩)
            by_cases hB : shift (pred (pred j)) ∈ bothRegion θ
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_oB.2 ⟨hpp, hB⟩))
            · refine Finset.mem_union_right _ (mem_oD.2 ⟨hpp, ?_, Or.inl ?_⟩)
              · exact Finset.mem_sdiff.2 ⟨by rw [hsx]; exact hpC, hB⟩
              · rw [hssx]; exact Finset.mem_sdiff.2 ⟨hjO, hjnot⟩
          have ht : target θ (pred (pred j)) = q := by
            rw [target, if_neg (by rw [hsx]; exact hpO), hssx]
            exact hmemq hjq
          exact hno _ hxch ht
        · -- `pred j` is a wide exit, charged to `q`
          exfalso
          have hppC : pred (pred j) ∈ compCutRegion θ := by
            rw [compCutRegion_eq_compl, Finset.mem_compl]; exact hppO
          have hw : pred j ∈ wideExits θ :=
            mem_wideExits.2 ⟨mem_exitSet.2 ⟨hpC, by
              rw [shift_pred, compCutRegion_eq_compl, Finset.mem_compl, not_not]
              exact hjO⟩, hppC⟩
          have ht : target θ (pred j) = q := by
            rw [target, if_pos (by rw [shift_pred]; exact hjO), shift_pred]
            exact hmemq hjq
          exact hno _ (Finset.mem_union_left _ hw) ht
    · obtain ⟨-, -, hpq⟩ := Finset.mem_filter.1 hjG
      exact Finset.mem_union_left _ hpq
  have hSuniv : S = Finset.univ := eq_univ_pred_closed hSne hclosed
  refine hne (Finset.Subset.antisymm hqsub fun x hx => ?_)
  have hxS : x ∈ S := hSuniv ▸ Finset.mem_univ x
  rcases Finset.mem_union.1 hxS with hxq | hxG
  · exact hxq
  · exact absurd (Finset.mem_filter.1 hxG).1
      (by rw [compCutRegion_eq_compl, Finset.mem_compl, not_not]; exact hx)

/-- **The block count is at most the number of charges** once there are two blocks. -/
theorem card_outBlocks_le_charges (θ : SysPartition N Finset.univ)
    (hr : 2 ≤ (outBlocks θ).card) : (outBlocks θ).card ≤ (charges θ).card := by
  classical
  refine Finset.card_le_card_of_surjOn (target θ) ?_
  intro q hq
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  refine exists_charge_of_ne_outRegion θ hq ?_
  intro hqO
  obtain ⟨q', hq', hqq'⟩ : ∃ q' ∈ outBlocks θ, q' ≠ q := by
    by_contra hc
    push_neg at hc
    have : (outBlocks θ) ⊆ {q} := fun x hx => Finset.mem_singleton.2 (hc x hx)
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨x, hx⟩ := θ.parts_nonempty q' (mem_outBlocks.1 hq').1
  have hxO : x ∈ outRegion θ :=
    subset_outRegion θ (mem_outBlocks.1 hq').1 (mem_outBlocks.1 hq').2 hx
  have hxq : x ∈ q := hqO ▸ hxO
  exact Finset.disjoint_left.1
    (θ.parts_disjoint q' (mem_outBlocks.1 hq').1 q (mem_outBlocks.1 hq).1 hqq') hx hxq

end Charges

section AllOut

variable [NeZero N]

/-- The damage inside any family of blocks is bounded by the total. -/
lemma sum_damaged_inter_le (θ : SysPartition N Finset.univ) {B : Finset (Finset (Fin N))}
    (hB : B ⊆ θ.parts) : ∑ p ∈ B, (damaged θ ∩ p).card ≤ damagedCount θ := by
  rw [damagedCount_eq_sum θ]
  exact Finset.sum_le_sum_of_subset hB

lemma one_le_damaged_inter_of_compl (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) : 1 ≤ (damaged θ ∩ p).card := by
  obtain ⟨a, ha, hda⟩ := exists_damaged_of_cutSet_compl θ hp hcut
  exact Finset.card_pos.2
    ⟨a, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hda⟩, ha⟩⟩

lemma two_le_damaged_inter_of_compl (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) (hc : 2 ≤ p.card) :
    2 ≤ (damaged θ ∩ p).card := by
  classical
  obtain ⟨a, ha, a', ha', hne, hda, hda'⟩ := two_le_damaged_of_cutSet_compl θ hp hcut hc
  have hsub : ({a, a'} : Finset (Fin N)) ⊆ damaged θ ∩ p := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      exact Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩,
        by assumption⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at this

/-- **All-outputs partitions of damage at most three**: two blocks, one a singleton. -/
theorem all_outputs_structure (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) (hall : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs) :
    θ.parts.card = 2 ∧ ∃ p ∈ θ.parts, p.card = 1 := by
  classical
  have hcompl : ∀ p ∈ θ.parts, θ.cutSet p = pᶜ :=
    fun p hp => cutSet_eq_compl_of_all_outputs θ hall hp
  have hk := card_le_damagedCount_of_forall_compl θ (Finset.Subset.refl _) hcompl
  have h2 := θ.two_le
  have hsumN : ∑ p ∈ θ.parts, p.card = N := by
    have hob : outBlocks θ = θ.parts := Finset.filter_true_of_mem hall
    have h1 := sum_card_outBlocks θ
    have h2 := card_compCutRegion_add_outRegion θ
    have hC : compCutRegion θ = ∅ := by
      have hcb : compCutBlocks θ = ∅ :=
        Finset.filter_eq_empty_iff.2 fun p hp h => h (hall p hp)
      simp [compCutRegion, hcb]
    rw [hC, Finset.card_empty, zero_add] at h2
    rw [hob] at h1
    omega
  have hbig : ∀ p ∈ θ.parts, ∀ q ∈ θ.parts, p ≠ q → 2 ≤ p.card → 2 ≤ q.card → False := by
    intro p hp q hq hpq hcp hcq
    have hsub : ({p, q} : Finset (Finset (Fin N))) ⊆ θ.parts := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle := sum_damaged_inter_le θ hsub
    rw [Finset.sum_pair hpq] at hle
    have := two_le_damaged_inter_of_compl θ hp (hcompl p hp) hcp
    have := two_le_damaged_inter_of_compl θ hq (hcompl q hq) hcq
    omega
  rcases (show θ.parts.card = 2 ∨ θ.parts.card = 3 by omega) with h | h
  · refine ⟨h, ?_⟩
    obtain ⟨p, q, hpq, hpar⟩ := Finset.card_eq_two.1 h
    have hp : p ∈ θ.parts := by rw [hpar]; exact Finset.mem_insert_self _ _
    have hq : q ∈ θ.parts := by
      rw [hpar]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    have hp1 := Finset.card_pos.2 (θ.parts_nonempty p hp)
    have hq1 := Finset.card_pos.2 (θ.parts_nonempty q hq)
    by_cases hpc : p.card = 1
    · exact ⟨p, hp, hpc⟩
    · refine ⟨q, hq, ?_⟩
      by_contra hqc
      exact hbig p hp q hq hpq (by omega) (by omega)
  · exfalso
    have hsing : ∀ p ∈ θ.parts, p.card = 1 := by
      intro p hp
      by_contra hne
      have hpc : 2 ≤ p.card := by
        have := Finset.card_pos.2 (θ.parts_nonempty p hp); omega
      have hle := sum_damaged_inter_le θ (Finset.Subset.refl θ.parts)
      rw [← Finset.add_sum_erase _ _ hp] at hle
      have h2p := two_le_damaged_inter_of_compl θ hp (hcompl p hp) hpc
      have hrest : ∑ _q ∈ θ.parts.erase p, 1
          ≤ ∑ q ∈ θ.parts.erase p, (damaged θ ∩ q).card :=
        Finset.sum_le_sum fun q hq => one_le_damaged_inter_of_compl θ
          (Finset.mem_of_mem_erase hq) (hcompl q (Finset.mem_of_mem_erase hq))
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hp, h] at hrest
      omega
    rw [Finset.sum_congr rfl hsing, Finset.sum_const, smul_eq_mul, mul_one, h] at hsumN
    omega

lemma all_outputs_of_compCutBlocks_empty (θ : SysPartition N Finset.univ)
    (hC : compCutBlocks θ = ∅) : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs := by
  intro q hq
  by_contra hd
  have : q ∈ compCutBlocks θ := mem_compCutBlocks.2 ⟨hq, hd⟩
  rw [hC] at this
  exact Finset.notMem_empty _ this

lemma compCutRegion_ne_univ_of_outBlocks (θ : SysPartition N Finset.univ)
    (hr : 0 < (outBlocks θ).card) : compCutRegion θ ≠ Finset.univ := by
  intro h
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hr
  obtain ⟨x, hx⟩ := θ.parts_nonempty q (mem_outBlocks.1 hq).1
  have hxO := subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2 hx
  have hxC : x ∈ compCutRegion θ := h ▸ Finset.mem_univ x
  rw [compCutRegion_eq_compl, Finset.mem_compl] at hxC
  exact hxC hxO

end AllOut

section TwoBlocks

variable [NeZero N]

/-- **At most two outputs blocks** at damage at most three. -/
theorem card_outBlocks_le_two (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) : (outBlocks θ).card ≤ 2 := by
  classical
  by_contra hc
  have hr : 2 ≤ (outBlocks θ).card := by omega
  have hsur := card_outBlocks_le_charges θ hr
  have hch := card_charges_le θ
  have hbudget := damage_budget_four θ
  have hsum : ∑ q ∈ outBlocks θ, ((oA θ q).card + (oB θ q).card + (oD θ q).card)
      ≤ ∑ q ∈ outBlocks θ,
          ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card) :=
    Finset.sum_le_sum fun q _ => by omega
  rcases (compCutBlocks θ).eq_empty_or_nonempty with hC | ⟨p, hp⟩
  · have hall := all_outputs_of_compCutBlocks_empty θ hC
    have hob : outBlocks θ = θ.parts := Finset.filter_true_of_mem hall
    have := (all_outputs_structure hN θ hD hall).1
    rw [hob] at hc
    omega
  · have hne := compCutRegion_ne_univ_of_outBlocks θ (by omega)
    have h1 := one_le_card_exitSet_compCutRegion θ hp hne
    omega

/-- With no `oC` point, a block containing two consecutive units contains an exit of the
outputs region: the run continues until it leaves the region. -/
lemma exists_exit_mem_of_consec (θ : SysPartition N Finset.univ) {q : Finset (Fin N)}
    (hq : q ∈ outBlocks θ) (hoC : oC θ q = ∅) {j : Fin N} (hj : j ∈ q) (hsj : shift j ∈ q) :
    ∃ t ∈ q, t ∈ exitSet (outRegion θ) := by
  classical
  have hqp := (mem_outBlocks.1 hq).1
  obtain ⟨y, hy⟩ : ∃ y, y ∉ q := by
    by_contra h
    push_neg at h
    exact block_ne_univ θ hqp (Finset.eq_univ_of_forall h)
  obtain ⟨m, hm⟩ := exists_iterate_shift y j
  have hex : ∃ k, shift^[k] j ∉ q := ⟨m, hm ▸ hy⟩
  have hspec : shift^[Nat.find hex] j ∉ q := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, shift^[k] j ∈ q := fun k hk =>
    not_not.1 (Nat.find_min hex hk)
  have hk0 : Nat.find hex ≠ 0 := fun h => hspec (by rw [h]; simpa using hj)
  have hk1 : Nat.find hex ≠ 1 := fun h => hspec (by rw [h]; simpa using hsj)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
  have hxq : shift^[k] j ∈ q := hmin k (by omega)
  have hsx : shift (shift^[k] j) ∈ q := by
    have := hmin (k + 1) (by omega)
    rwa [Function.iterate_succ_apply'] at this
  have hssx : shift (shift (shift^[k] j)) ∉ q := by
    have := hspec
    rwa [hk, Function.iterate_succ_apply', Function.iterate_succ_apply'] at this
  refine ⟨shift (shift^[k] j), hsx,
    mem_exitSet.2 ⟨subset_outRegion θ hqp (mem_outBlocks.1 hq).2 hsx, ?_⟩⟩
  intro hO
  have : shift^[k] j ∈ oC θ q :=
    mem_oC.2 ⟨hxq, hsx, Or.inl (Finset.mem_sdiff.2 ⟨hO, hssx⟩)⟩
  rw [hoC] at this
  exact Finset.notMem_empty _ this

/-- **The core of the singleton lemma.**  With two outputs blocks, a unique exit `t` and a
unique entry `c` of the outputs region, no `oC` point in the block not containing `t`, and
at most two `oA` points overall, the block not containing `t` is a singleton. -/
lemma card_eq_one_of_not_mem_exit (θ : SysPartition N Finset.univ)
    {q₁ q₂ : Finset (Fin N)} (hq₁ : q₁ ∈ outBlocks θ) (hq₂ : q₂ ∈ outBlocks θ)
    (hne : q₁ ≠ q₂) (hob : outBlocks θ = {q₁, q₂}) {t c : Fin N}
    (hexit : exitSet (outRegion θ) = {t}) (hentry : entrySet (outRegion θ) = {c})
    (ht : t ∈ q₁) (hoC : oC θ q₂ = ∅)
    (hA : (oA θ q₁).card + (oA θ q₂).card ≤ 2) : q₂.card = 1 := by
  classical
  have hdisj := θ.parts_disjoint q₁ (mem_outBlocks.1 hq₁).1 q₂ (mem_outBlocks.1 hq₂).1 hne
  have hq₂O : q₂ ⊆ outRegion θ := subset_outRegion θ (mem_outBlocks.1 hq₂).1 (mem_outBlocks.1 hq₂).2
  have hnoconsec : ∀ y ∈ q₂, shift y ∉ q₂ := by
    intro y hy hsy
    obtain ⟨t', ht'q, ht'e⟩ := exists_exit_mem_of_consec θ hq₂ hoC hy hsy
    rw [hexit, Finset.mem_singleton] at ht'e
    subst ht'e
    exact Finset.disjoint_left.1 hdisj ht ht'q
  have hsub : q₂ ⊆ oA θ q₂ := by
    intro y hy
    refine mem_oA.2 ⟨hy, Finset.mem_sdiff.2 ⟨?_, hnoconsec y hy⟩⟩
    by_contra hsO
    have : y ∈ exitSet (outRegion θ) := mem_exitSet.2 ⟨hq₂O hy, hsO⟩
    rw [hexit, Finset.mem_singleton] at this
    subst this
    exact Finset.disjoint_left.1 hdisj ht hy
  have h1 : 1 ≤ q₂.card := Finset.card_pos.2 (θ.parts_nonempty q₂ (mem_outBlocks.1 hq₂).1)
  by_contra hc
  have h2 : 2 ≤ q₂.card := by omega
  have hA2 : 2 ≤ (oA θ q₂).card := le_trans h2 (Finset.card_le_card hsub)
  have hA1 : oA θ q₁ = ∅ := Finset.card_eq_zero.1 (by omega)
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < q₂.card) (shift c)
  have hyO : y ∈ outRegion θ := hq₂O hy
  have hpO : pred y ∈ outRegion θ := by
    by_contra hpO
    have : pred y ∈ entrySet (outRegion θ) :=
      mem_entrySet.2 ⟨hpO, by rw [shift_pred]; exact hyO⟩
    rw [hentry, Finset.mem_singleton] at this
    exact hyc (by rw [← this, shift_pred])
  have hpq₂ : pred y ∉ q₂ := fun h => hnoconsec _ h (by rw [shift_pred]; exact hy)
  have hpq₁ : pred y ∈ q₁ := by
    obtain ⟨hb, hpp⟩ := partOf_mem_outBlocks_of_mem_outRegion θ hpO
    rw [hob, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with h | h
    · rw [h] at hpp; exact hpp
    · rw [h] at hpp; exact absurd hpp hpq₂
  have : pred y ∈ oA θ q₁ := by
    refine mem_oA.2 ⟨hpq₁, Finset.mem_sdiff.2 ⟨by rw [shift_pred]; exact hyO, ?_⟩⟩
    rw [shift_pred]
    exact fun h => Finset.disjoint_left.1 hdisj h hy
  rw [hA1] at this
  exact Finset.notMem_empty _ this

/-- **Two outputs blocks force a singleton** at damage at most three. -/
theorem exists_singleton_of_two_outBlocks (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) (hr : (outBlocks θ).card = 2) :
    ∃ q ∈ outBlocks θ, q.card = 1 := by
  classical
  rcases (compCutBlocks θ).eq_empty_or_nonempty with hC | ⟨p, hp⟩
  · have hall := all_outputs_of_compCutBlocks_empty θ hC
    have hob : outBlocks θ = θ.parts := Finset.filter_true_of_mem hall
    rw [hob]
    exact (all_outputs_structure hN θ hD hall).2
  · have hne := compCutRegion_ne_univ_of_outBlocks θ (by omega)
    have hcc1 := one_le_card_exitSet_compCutRegion θ hp hne
    have hsur := card_outBlocks_le_charges θ (by omega)
    have hch := card_charges_le θ
    have hbudget := damage_budget_four θ
    have hsplit : ∑ q ∈ outBlocks θ,
          ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card)
        = ∑ q ∈ outBlocks θ, ((oA θ q).card + (oB θ q).card + (oD θ q).card)
          + ∑ q ∈ outBlocks θ, (oC θ q).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hoC0 : ∑ q ∈ outBlocks θ, (oC θ q).card = 0 := by omega
    have hoC : ∀ q ∈ outBlocks θ, oC θ q = ∅ := fun q hq =>
      Finset.card_eq_zero.1 ((Finset.sum_eq_zero_iff.1 hoC0) q hq)
    have hcc : (exitSet (compCutRegion θ)).card = 1 := by omega
    have hexitO : (exitSet (outRegion θ)).card = 1 := by
      rw [← card_exitSet_regions]; exact hcc
    have hentryO : (entrySet (outRegion θ)).card = 1 := by
      rw [← exitSet_compl, ← compCutRegion_eq_compl]; exact hcc
    obtain ⟨t, ht⟩ := Finset.card_eq_one.1 hexitO
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hentryO
    obtain ⟨q₁, q₂, hne12, hob⟩ := Finset.card_eq_two.1 hr
    have hq₁ : q₁ ∈ outBlocks θ := by rw [hob]; exact Finset.mem_insert_self _ _
    have hq₂ : q₂ ∈ outBlocks θ := by
      rw [hob]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hA : (oA θ q₁).card + (oA θ q₂).card ≤ 2 := by
      have h := hbudget
      rw [hob, Finset.sum_pair hne12] at h
      omega
    have htO : t ∈ outRegion θ :=
      (mem_exitSet.1 (by rw [ht]; exact Finset.mem_singleton_self t)).1
    obtain ⟨hb, htp⟩ := partOf_mem_outBlocks_of_mem_outRegion θ htO
    rw [hob, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with h | h
    · rw [h] at htp
      exact ⟨q₂, hq₂, card_eq_one_of_not_mem_exit θ hq₁ hq₂ hne12 hob ht hc htp
        (hoC q₂ hq₂) hA⟩
    · rw [h] at htp
      exact ⟨q₁, hq₁, card_eq_one_of_not_mem_exit θ hq₂ hq₁ hne12.symm
        (by rw [hob, Finset.pair_comm]) ht hc htp (hoC q₁ hq₁) (by omega)⟩

end TwoBlocks

section Relabel

variable [NeZero N]

/-- The partition with every `both` block relabelled `outputs`. -/
noncomputable def relabel (θ : SysPartition N Finset.univ) : SysPartition N Finset.univ :=
  { θ with dir := fun p => if θ.dir p = Dir.both then Dir.outputs else θ.dir p }

lemma relabel_parts (θ : SysPartition N Finset.univ) : (relabel θ).parts = θ.parts := rfl

lemma relabel_dir (θ : SysPartition N Finset.univ) (p : Finset (Fin N)) :
    (relabel θ).dir p = if θ.dir p = Dir.both then Dir.outputs else θ.dir p := rfl

lemma relabel_partOf (θ : SysPartition N Finset.univ) (j : Fin N) :
    (relabel θ).partOf j = θ.partOf j := rfl

/-- The blocks severing both directions. -/
noncomputable def bothBlocks (θ : SysPartition N Finset.univ) : Finset (Finset (Fin N)) :=
  θ.parts.filter fun p => θ.dir p = Dir.both

lemma mem_bothBlocks {θ : SysPartition N Finset.univ} {p : Finset (Fin N)} :
    p ∈ bothBlocks θ ↔ p ∈ θ.parts ∧ θ.dir p = Dir.both := by
  unfold bothBlocks; rw [Finset.mem_filter]

lemma bothRegion_eq_sup (θ : SysPartition N Finset.univ) :
    bothRegion θ = (bothBlocks θ).sup id := rfl

lemma outBlocks_relabel (θ : SysPartition N Finset.univ) :
    outBlocks (relabel θ) = outBlocks θ ∪ bothBlocks θ := by
  ext p
  rw [Finset.mem_union, mem_outBlocks, mem_outBlocks, mem_bothBlocks, relabel_parts,
    relabel_dir]
  constructor
  · rintro ⟨hp, hd⟩
    by_cases hb : θ.dir p = Dir.both
    · exact Or.inr ⟨hp, hb⟩
    · rw [if_neg hb] at hd; exact Or.inl ⟨hp, hd⟩
  · rintro (⟨hp, hd⟩ | ⟨hp, hd⟩)
    · exact ⟨hp, by simp [hd]⟩
    · exact ⟨hp, by rw [if_pos hd]⟩

lemma outBlocks_disjoint_bothBlocks (θ : SysPartition N Finset.univ) :
    Disjoint (outBlocks θ) (bothBlocks θ) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (mem_outBlocks.1 hp).2
  have h2 := (mem_bothBlocks.1 hp').2
  rw [h1] at h2
  exact absurd h2 (by decide)

lemma card_outBlocks_relabel (θ : SysPartition N Finset.univ) :
    (outBlocks (relabel θ)).card = (outBlocks θ).card + (bothBlocks θ).card := by
  rw [outBlocks_relabel, Finset.card_union_of_disjoint (outBlocks_disjoint_bothBlocks θ)]

lemma bothRegion_relabel (θ : SysPartition N Finset.univ) : bothRegion (relabel θ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨p, -, hd, -⟩ := mem_bothRegion.1 hx
  rw [relabel_dir] at hd
  by_cases hb : θ.dir p = Dir.both
  · rw [if_pos hb] at hd; exact absurd hd (by decide)
  · rw [if_neg hb] at hd; exact hb hd

lemma outRegion_relabel (θ : SysPartition N Finset.univ) :
    outRegion (relabel θ) = outRegion θ ∪ bothRegion θ := by
  ext x
  rw [Finset.mem_union, mem_outRegion, mem_outRegion, mem_bothRegion]
  simp only [relabel_parts, relabel_dir]
  constructor
  · rintro ⟨p, hp, hd, hx⟩
    by_cases hb : θ.dir p = Dir.both
    · exact Or.inr ⟨p, hp, hb, hx⟩
    · rw [if_neg hb] at hd; exact Or.inl ⟨p, hp, hd, hx⟩
  · rintro (⟨p, hp, hd, hx⟩ | ⟨p, hp, hd, hx⟩)
    · exact ⟨p, hp, by simp [hd], hx⟩
    · exact ⟨p, hp, by rw [if_pos hd], hx⟩

/-- Relabelling can only shrink cut sets. -/
lemma cutSet_relabel_subset (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) : (relabel θ).cutSet p ⊆ θ.cutSet p := by
  by_cases ho : θ.dir p = Dir.outputs
  · have ho' : (relabel θ).dir p = Dir.outputs := by rw [relabel_dir, ho]; simp
    rw [cutSet_outputs_eq (relabel θ) hp ho', cutSet_outputs_eq θ hp ho, bothRegion_relabel,
      outRegion_relabel, Finset.empty_union, Finset.union_comm]
  · rcases dir_io_of_ne_outputs θ ho with hi | hb
    · have hi' : (relabel θ).dir p = Dir.inputs := by
        rw [relabel_dir, if_neg (by rw [hi]; decide), hi]
      rw [cutSet_eq_compl_of_dir (relabel θ) (Or.inl hi'), cutSet_eq_compl_of_dir θ (Or.inl hi)]
    · have ho' : (relabel θ).dir p = Dir.outputs := by rw [relabel_dir, if_pos hb]
      rw [cutSet_outputs_eq (relabel θ) hp ho', cutSet_eq_compl_of_dir θ (Or.inr hb)]
      intro x hx
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.1 hx).2

lemma damaged_relabel_subset (θ : SysPartition N Finset.univ) :
    damaged (relabel θ) ⊆ damaged θ := by
  intro j hj
  obtain ⟨-, k, hk, hkc⟩ := Finset.mem_filter.1 hj
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hk, ?_⟩
  rw [relabel_partOf] at hkc
  exact cutSet_relabel_subset θ (partOf_mem_parts θ j) hkc

lemma damagedCount_relabel_le (θ : SysPartition N Finset.univ) :
    damagedCount (relabel θ) ≤ damagedCount θ :=
  Finset.card_le_card (damaged_relabel_subset θ)

end Relabel

section Facts

variable [NeZero N]

/-- **Fact 5a.**  A positive excess leaves no `both` region. -/
theorem bothRegion_card_eq_zero_of_excess (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) (he : 0 < outExcess θ) : (bothRegion θ).card = 0 := by
  have hr := two_le_card_outBlocks_of_outExcess_pos θ he
  have hr' := card_outBlocks_le_two hN (relabel θ) (le_trans (damagedCount_relabel_le θ) hD)
  rw [card_outBlocks_relabel] at hr'
  have hb : bothBlocks θ = ∅ := Finset.card_eq_zero.1 (by omega)
  simp [bothRegion_eq_sup, hb]

/-- **Fact 3.**  A `both` region of size at least two forces a single-unit outputs region
and no excess. -/
theorem outRegion_le_one_of_both (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) (hb : 2 ≤ (bothRegion θ).card) :
    (outRegion θ).card ≤ 1 ∧ outExcess θ = 0 := by
  classical
  have he : outExcess θ = 0 := by
    by_contra h
    have := bothRegion_card_eq_zero_of_excess hN θ hD (Nat.pos_of_ne_zero h)
    omega
  refine ⟨?_, he⟩
  by_contra ho
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < (outRegion θ).card)
  obtain ⟨hqb, -⟩ := partOf_mem_outBlocks_of_mem_outRegion θ hx
  have hr1 : 1 ≤ (outBlocks θ).card := Finset.card_pos.2 ⟨_, hqb⟩
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < (bothRegion θ).card)
  obtain ⟨pb, hpb, hdb, -⟩ := mem_bothRegion.1 hy
  have hb1 : 1 ≤ (bothBlocks θ).card := Finset.card_pos.2 ⟨pb, mem_bothBlocks.2 ⟨hpb, hdb⟩⟩
  have hD' := le_trans (damagedCount_relabel_le θ) hD
  have hr' := card_outBlocks_le_two hN (relabel θ) hD'
  rw [card_outBlocks_relabel] at hr'
  have hr2 : (outBlocks (relabel θ)).card = 2 := by rw [card_outBlocks_relabel]; omega
  obtain ⟨q, hq, hq1⟩ := exists_singleton_of_two_outBlocks hN (relabel θ) hD' hr2
  rw [outBlocks_relabel, Finset.mem_union] at hq
  rcases hq with hq | hq
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (show (outBlocks θ).card = 1 by omega)
    have hqa : q = a := by rw [ha, Finset.mem_singleton] at hq; exact hq
    have hsum := sum_card_outBlocks θ
    rw [ha, Finset.sum_singleton, ← hqa, hq1] at hsum
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (show (bothBlocks θ).card = 1 by omega)
    have hqa : q = a := by rw [ha, Finset.mem_singleton] at hq; exact hq
    have hreg : bothRegion θ = q := by
      rw [bothRegion_eq_sup, ha, Finset.sup_singleton, ← hqa]; rfl
    rw [hreg, hq1] at hb
    omega

/-- **Fact 4.**  The excess is at most `2(|O| - 1)`. -/
theorem outExcess_le (hN : 4 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ ≤ 3) (ho : 0 < (outRegion θ).card) :
    outExcess θ ≤ 2 * ((outRegion θ).card - 1) := by
  classical
  have hr := card_outBlocks_le_two hN θ hD
  rcases Nat.lt_or_ge (outBlocks θ).card 2 with h | h
  · rw [outExcess_eq_zero_of_card_le_one θ (by omega)]
    exact Nat.zero_le _
  · have hr2 : (outBlocks θ).card = 2 := by omega
    obtain ⟨q, hq, hq1⟩ := exists_singleton_of_two_outBlocks hN θ hD hr2
    obtain ⟨q₁, q₂, hne, hob⟩ := Finset.card_eq_two.1 hr2
    have hsum := sum_card_outBlocks θ
    rw [hob, Finset.sum_pair hne] at hsum
    rw [outExcess, hob, Finset.sum_pair hne]
    rw [hob, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [hq1] at hsum ⊢
      rw [← hsum]
      have hexp : (1 + q₂.card) * (1 + q₂.card) = (1 * 1 + q₂.card * q₂.card) + 2 * q₂.card := by
        ring
      rw [hexp, Nat.add_sub_cancel_left]
      omega
    · rw [hq1] at hsum ⊢
      rw [← hsum]
      have hexp : (q₁.card + 1) * (q₁.card + 1) = (q₁.card * q₁.card + 1 * 1) + 2 * q₁.card := by
        ring
      rw [hexp, Nat.add_sub_cancel_left]
      omega

/-- **The `D = 3` normalizer bound, unconditional.** -/
theorem sysCutCount_of_damagedCount_three' (hN : 8 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) :
    4 * sysCutCount θ ≤ (N - 1) * (N - 1) + 8 * (N - 1) :=
  sysCutCount_of_damagedCount_three θ hN hD
    (outRegion_le_one_of_both (by omega) θ hD.le)
    (outExcess_le (by omega) θ hD.le)
    (bothRegion_card_eq_zero_of_excess (by omega) θ hD.le)
    (fun he ⟨P, hP, hPc⟩ => card_compCutBlocks_le_one_of_excess_big θ hD he hP hPc)
    (card_compCutBlocks_le_two_of_excess θ hD)

end Facts

section Assembly

variable [NeZero N]

/-- **`φ_s ≥ 4` for the whole substrate**, for every `N ≥ 8` with `3 ∤ N`, in every
state. -/
theorem four_le_sysPhi_circNet (h3 : ¬ (3 ∣ N)) (hN : 8 ≤ N) (u s : State N) :
    4 ≤ sysPhi (circNet N) Finset.univ u s := by
  classical
  have hmod : N % 3 = 1 ∨ N % 3 = 2 := by
    have hz : N % 3 = 0 → False := fun hm => h3 (Nat.dvd_of_mod_eq_zero hm)
    omega
  have hk2 : 2 ≤ (N + 1) / 3 := by omega
  have hkN : 3 * ((N + 1) / 3) = N - 1 ∨ 3 * ((N + 1) / 3) = N + 1 := by omega
  have ha : 0 < N - 2 * ((N + 1) / 3) := by omega
  have hsum : (N - 2 * ((N + 1) / 3)) + (N + 1) / 3 + (N + 1) / 3 = N := by omega
  set k := (N + 1) / 3 with hkdef
  set a := N - 2 * k with hadef
  have hDw := damagedCount_threeArc_le (N := N) (a := a) (k := k) ha hk2 hsum
  have hccw := sysCutCount_threeArc (N := N) (a := a) (k := k) ha hk2 hsum
  have hA : 4 * (N - 1) < sysCutCount (threeArc a k ha hk2 hsum) := by
    rw [hccw]
    rcases hkN with h | h
    · have hak : a = k + 1 := by omega
      have hNk : N - k = 2 * k + 1 := by omega
      have hN1 : N - 1 = 3 * k := by omega
      rw [hak, hNk, hN1]
      have hkk : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk2
      nlinarith [hkk]
    · have hk3 : 3 ≤ k := by omega
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
  -- the `D = 3` floor is also beaten by the witness
  have hC : (N - 1) * (N - 1) + 8 * (N - 1) < 3 * sysCutCount (threeArc a k ha hk2 hsum) := by
    rw [hccw]
    rcases hkN with h | h
    · have hak : a = k + 1 := by omega
      have hNk : N - k = 2 * k + 1 := by omega
      have hN1 : N - 1 = 3 * k := by omega
      have hk3 : 3 ≤ k := by omega
      rw [hak, hNk, hN1]
      have hkk : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk3
      nlinarith [hkk]
    · have hk3 : 3 ≤ k := by omega
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj2 : 2 ≤ j := by omega
      have hak : a = j := by omega
      have hNk : N - k = 2 * j + 1 := by omega
      have hN1 : N - 1 = 3 * j + 1 := by omega
      rw [hak, hNk, hN1, hj]
      have hjj : 2 * j ≤ j * j := Nat.mul_le_mul_right j hj2
      nlinarith [hjj]
  have hccw_pos : 0 < sysCutCount (threeArc a k ha hk2 hsum) := by omega
  rw [sysPhi_circNet h3 (by omega : 3 ≤ N)]
  haveI hne : Nonempty (SysPartition N Finset.univ) := ⟨threeArc a k ha hk2 hsum⟩
  obtain ⟨θs, hθs⟩ := argminSet_nonempty
    (fun θ : SysPartition N Finset.univ => (damagedCount θ : ℝ) / (sysCutCount θ : ℝ))
  have hstar := (mem_argminSet.1 hθs) (threeArc a k ha hk2 hsum)
  have h4D : 4 ≤ damagedCount θs := by
    by_contra hlt
    have h1D := one_le_damagedCount θs
    have hccs_pos : 0 < sysCutCount θs := sysCutCount_pos θs
    have hccwR : (0 : ℝ) < (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) := by
      exact_mod_cast hccw_pos
    have hccsR : (0 : ℝ) < (sysCutCount θs : ℝ) := by exact_mod_cast hccs_pos
    have hup : (damagedCount (threeArc a k ha hk2 hsum) : ℝ)
        / (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
        ≤ 4 / (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) := by
      gcongr
      exact_mod_cast hDw
    have hchain := hstar.trans hup
    have hDval : damagedCount θs = 1 ∨ damagedCount θs = 2 ∨ damagedCount θs = 3 := by omega
    rcases hDval with hD | hD | hD
    · have hcc1 := sysCutCount_eq_of_damagedCount_one (by omega : 3 ≤ N) θs hD
      rw [hD, hcc1] at hchain
      have hN1R : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
        ring
      rw [hN1R] at hchain
      have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      rw [div_le_div_iff₀ hN1pos hccwR] at hchain
      have hcast : (sysCutCount (threeArc a k ha hk2 hsum) : ℝ) ≤ ((4 * (N - 1) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at hchain ⊢
        linarith
      have := (Nat.cast_le (α := ℝ)).1 hcast
      omega
    · rcases sysCutCount_of_damagedCount_two (by omega : 3 ≤ N) θs hD with hcc | hcc
      · rw [hD, hcc] at hchain
        have h2N : ((2 * (N - 1) : ℕ) : ℝ) = 2 * ((N : ℝ) - 1) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
          ring
        rw [h2N] at hchain
        have hN1pos : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by
          have : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
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
        have hchain' : 2 * (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
            ≤ 4 * (sysCutCount θs : ℝ) := by linarith
        have hcast : ((2 * sysCutCount (threeArc a k ha hk2 hsum) : ℕ) : ℝ)
            ≤ ((4 * sysCutCount θs : ℕ) : ℝ) := by push_cast; linarith
        have hle := (Nat.cast_le (α := ℝ)).1 hcast
        omega
    · have hcc3 := sysCutCount_of_damagedCount_three' hN θs hD
      rw [hD] at hchain
      rw [div_le_div_iff₀ hccsR hccwR] at hchain
      push_cast at hchain
      have hchain' : 3 * (sysCutCount (threeArc a k ha hk2 hsum) : ℝ)
          ≤ 4 * (sysCutCount θs : ℝ) := by linarith
      have hcast : ((3 * sysCutCount (threeArc a k ha hk2 hsum) : ℕ) : ℝ)
          ≤ ((4 * sysCutCount θs : ℕ) : ℝ) := by push_cast; linarith
      have hle := (Nat.cast_le (α := ℝ)).1 hcast
      omega
  refine le_trans ?_ (le_sup'OrZero hθs)
  exact_mod_cast h4D

/-- **The window-3 circulant is its own complex** `[IIT4, Eq 26]`, for every `N ≥ 8` with
`3 ∤ N`, in every state and against every background: the whole substrate has `φ_s ≥ 4`
and every proper candidate has `φ_s < 4`. -/
theorem isComplex_circNet_univ (h3 : ¬ (3 ∣ N)) (hN : 8 ≤ N) (u s : State N) :
    IsComplex (circNet N) u Finset.univ Finset.univ s := by
  rw [isComplex_univ_iff]
  intro S' hne hnem
  have h4 := four_le_sysPhi_circNet h3 hN u s
  by_cases hS2 : 2 ≤ S'.card
  · exact lt_of_lt_of_le (sysPhi_circNet_lt_four (by omega) hne hS2 u s) h4
  · rw [sysPhi_eq_zero_of_card_le_one _ u s (by omega)]
    linarith

end Assembly

end IIT
