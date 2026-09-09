/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Decomp

/-!
# The crux of the `D = 3` exclusion: two undamaged outputs blocks are impossible

If no unit of the outputs region is damaged, then a width-one gap between two outputs
runs always has the *same* block on both sides -- so a change of block forces a **wide**
gap.  This makes the map `wideExits → outBlocks`, `z ↦ block(shift z)`, surjective, hence
`|outBlocks| ≤ |wideExits|`.  With the damage budget this is incompatible with two
outputs blocks, which is exactly what every remaining structural fact needs.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Crux

variable [NeZero N]

/-- A set closed under `pred` and nonempty is everything. -/
lemma eq_univ_pred_closed {p : Finset (Fin N)} (hne : p.Nonempty)
    (hcl : ∀ j ∈ p, pred j ∈ p) : p = Finset.univ := by
  classical
  obtain ⟨e, he⟩ := hne
  refine Finset.eq_univ_of_forall fun a => ?_
  obtain ⟨m, hm⟩ := exists_iterate_pred a e
  have hiter : ∀ k, pred^[k] e ∈ p := by
    intro k
    induction k with
    | zero => simpa using he
    | succ t ih => rw [Function.iterate_succ_apply']; exact hcl _ ih
  rw [← hm]; exact hiter m

/-- Predecessor of a unit not in its own block, when the outputs region is undamaged,
lands in the complement-cut region. -/
lemma pred_mem_compCutRegion_of_undamaged (θ : SysPartition N Finset.univ)
    (hun : damaged θ ∩ outRegion θ = ∅) {q : Finset (Fin N)} (hq : q ∈ outBlocks θ)
    {j : Fin N} (hjq : j ∈ q) (hpj : pred j ∉ q) : pred j ∈ compCutRegion θ := by
  classical
  by_contra hpc
  -- pred j ∉ C, and pred j ≠ in q, so pred j ∈ O \ q, giving an oA damage at pred j
  rw [compCutRegion_eq_compl, Finset.mem_compl, not_not] at hpc
  have hpO : pred j ∈ outRegion θ := hpc
  have hjO : j ∈ outRegion θ := subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2 hjq
  -- pred j is damaged: its live input shift (pred j) = j lies in cutSet of its block
  have hne : θ.partOf (pred j) ≠ q := by
    intro h
    exact hpj (h ▸ mem_partOf θ (pred j))
  have hjcut : j ∈ θ.cutSet (θ.partOf (pred j)) := by
    obtain ⟨p', hp', hd', hpp'⟩ := mem_outRegion.1 hpO
    have hpeq : θ.partOf (pred j) = p' := θ.partOf_eq hp' hpp'
    rw [hpeq, cutSet_outputs_eq θ hp' hd']
    refine Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hjO, ?_⟩
    intro hjp'
    -- j ∈ p' = partOf(pred j) ≠ q, but j ∈ q: contradiction
    have : θ.partOf (pred j) = q := by rw [hpeq]; exact (θ.partOf_eq hp' hjp').symm ▸ (θ.partOf_eq (mem_outBlocks.1 hq).1 hjq)
    exact hne this
  have hdmg : pred j ∈ damaged θ := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨shift (pred j), ?_, ?_⟩⟩
    · exact mem_liveInputs.2 (Or.inl rfl)
    · rw [shift_pred]; exact hjcut
  have : pred j ∈ damaged θ ∩ outRegion θ := Finset.mem_inter.2 ⟨hdmg, hpO⟩
  rw [hun] at this
  exact absurd this (Finset.notMem_empty _)

/-- **Narrow gaps are within one block.**  If the outputs region is undamaged and `z` is a
width-one gap (in `C`, with both neighbours in `O`), its two neighbours share a block. -/
lemma narrow_within_block (θ : SysPartition N Finset.univ)
    (hun : damaged θ ∩ outRegion θ = ∅) {z : Fin N} (hzC : z ∈ compCutRegion θ)
    (hsz : shift z ∈ outRegion θ) (hpz : pred z ∈ outRegion θ) :
    θ.partOf (shift z) = θ.partOf (pred z) := by
  classical
  by_contra hne
  -- pred z is damaged: shift² (pred z) = shift z lies in cutSet of pred z's block
  obtain ⟨p', hp', hd', hpp'⟩ := mem_outRegion.1 hpz
  have hpeq : θ.partOf (pred z) = p' := θ.partOf_eq hp' hpp'
  have hszcut : shift z ∈ θ.cutSet (θ.partOf (pred z)) := by
    rw [hpeq, cutSet_outputs_eq θ hp' hd']
    refine Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ hsz, ?_⟩
    intro hszp'
    exact hne (by rw [hpeq]; exact (θ.partOf_eq hp' hszp'))
  have hdmg : pred z ∈ damaged θ := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨shift (shift (pred z)), ?_, ?_⟩⟩
    · exact mem_liveInputs.2 (Or.inr rfl)
    · rw [shift_pred]; exact hszcut
  have : pred z ∈ damaged θ ∩ outRegion θ := Finset.mem_inter.2 ⟨hdmg, hpz⟩
  rw [hun] at this
  exact absurd this (Finset.notMem_empty _)

/-- **A block with no wide exit is the whole outputs region.**  Walking back from the
block stays inside it (narrow gaps rejoin it), so it is `pred`-closed together with its
gaps and hence everything. -/
lemma eq_outRegion_of_no_wide (θ : SysPartition N Finset.univ)
    (hun : damaged θ ∩ outRegion θ = ∅) {q : Finset (Fin N)} (hq : q ∈ outBlocks θ)
    (hno : ∀ z ∈ wideExits θ, θ.partOf (shift z) ≠ q) : q = outRegion θ := by
  classical
  -- S = q together with the gaps whose forward neighbour is in q
  set G : Finset (Fin N) :=
    (compCutRegion θ).filter fun z => shift z ∈ outRegion θ ∧ θ.partOf (shift z) = q with hG
  have hqsub : q ⊆ outRegion θ := subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2
  have hmemq : ∀ {j}, j ∈ q → θ.partOf j = q := fun {j} hj =>
    θ.partOf_eq (mem_outBlocks.1 hq).1 hj
  -- every gap in G is narrow (its predecessor is in O)
  have hnarrow : ∀ z ∈ G, pred z ∈ outRegion θ := by
    intro z hz
    obtain ⟨hzC, hszO, hpart⟩ := Finset.mem_filter.1 hz
    by_contra hpO
    -- then z is a wide exit landing in q
    have hpC : pred z ∈ compCutRegion θ := by
      rw [compCutRegion_eq_compl, Finset.mem_compl]; exact hpO
    have hzw : z ∈ wideExits θ :=
      mem_wideExits.2 ⟨mem_exitSet.2 ⟨hzC, by
        rw [compCutRegion_eq_compl, Finset.mem_compl, not_not] at *; exact hszO⟩, hpC⟩
    exact hno z hzw hpart
  set S : Finset (Fin N) := q ∪ G with hS
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (mem_outBlocks.1 hq).1 |> θ.parts_nonempty q
    exact ⟨x, Finset.mem_union_left _ hx⟩
  have hclosed : ∀ j ∈ S, pred j ∈ S := by
    intro j hj
    rcases Finset.mem_union.1 hj with hjq | hjG
    · by_cases hpq : pred j ∈ q
      · exact Finset.mem_union_left _ hpq
      · have hjO : j ∈ outRegion θ := hqsub hjq
        have hpC : pred j ∈ compCutRegion θ :=
          pred_mem_compCutRegion_of_undamaged θ hun hq hjq hpq
        refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hpC, ?_, ?_⟩)
        · rw [shift_pred]; exact hjO
        · rw [shift_pred]; exact hmemq hjq
    · obtain ⟨hzC, hszO, hpart⟩ := Finset.mem_filter.1 hjG
      have hpO : pred j ∈ outRegion θ := hnarrow j hjG
      have hnw := narrow_within_block θ hun hzC hszO hpO
      rw [hpart] at hnw
      obtain ⟨p', hp', hd', hpp'⟩ := mem_outRegion.1 hpO
      have hpjq : pred j ∈ q := by
        have hpe : θ.partOf (pred j) = q := hnw.symm
        rw [θ.partOf_eq hp' hpp'] at hpe
        exact hpe ▸ hpp'
      exact Finset.mem_union_left _ hpjq
  have hSuniv : S = Finset.univ := eq_univ_pred_closed hSne hclosed
  -- but S ⊆ q ∪ C, so outRegion ⊆ q
  refine Finset.Subset.antisymm hqsub fun x hx => ?_
  have hxS : x ∈ S := hSuniv ▸ Finset.mem_univ x
  rcases Finset.mem_union.1 hxS with hxq | hxG
  · exact hxq
  · exact absurd (Finset.mem_filter.1 hxG).1
      (by rw [compCutRegion_eq_compl, Finset.mem_compl, not_not]; exact hx)

/-- **The block count is at most the number of wide gaps** when the outputs region is
undamaged. -/
theorem card_outBlocks_le_wideExits (θ : SysPartition N Finset.univ)
    (hun : damaged θ ∩ outRegion θ = ∅) (hr : 2 ≤ (outBlocks θ).card) :
    (outBlocks θ).card ≤ (wideExits θ).card := by
  classical
  -- surjection wideExits → outBlocks, z ↦ partOf (shift z)
  refine Finset.card_le_card_of_surjOn (fun z => θ.partOf (shift z)) ?_
  intro q hq
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  -- q has a wide exit, else q = outRegion and there is no second block
  by_contra hno
  push_neg at hno
  have hnowide : ∀ z ∈ wideExits θ, θ.partOf (shift z) ≠ q := by
    intro z hz he
    exact hno z hz he
  have hqO : q = outRegion θ := eq_outRegion_of_no_wide θ hun hq hnowide
  -- but there is a second block q' ⊆ outRegion = q, disjoint and nonempty: contradiction
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

/-- **The crux.**  At damage three, two outputs blocks cannot both be undamaged: some
outputs unit is always damaged when there are two or more outputs blocks. -/
theorem one_le_damaged_out_of_two_le_outBlocks (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) (hr : 2 ≤ (outBlocks θ).card) :
    1 ≤ (damaged θ ∩ outRegion θ).card := by
  classical
  by_contra hc
  have hun : damaged θ ∩ outRegion θ = ∅ := by
    rw [← Finset.card_eq_zero]; omega
  -- r ≤ w, and w ≤ cc, so cc + w ≥ 2r ≥ 4 > 3
  have hrw := card_outBlocks_le_wideExits θ hun hr
  have hwcc : (wideExits θ).card ≤ (exitSet (compCutRegion θ)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  -- the four-family sum is zero since all four families lie in damaged ∩ O = ∅
  have hbudget := damage_budget_four θ
  have hfour : ∑ q ∈ outBlocks θ,
      ((oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    have hsub : (oA θ q).card + (oB θ q).card + (oC θ q).card + (oD θ q).card
        ≤ (damaged θ ∩ q).card :=
      oFour_card θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2
    have hqO : q ⊆ outRegion θ :=
      subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2
    have : damaged θ ∩ q ⊆ damaged θ ∩ outRegion θ :=
      Finset.inter_subset_inter (le_refl _) hqO
    rw [hun] at this
    have : (damaged θ ∩ q).card = 0 := Finset.card_eq_zero.2 (Finset.subset_empty.1 this)
    omega
  rw [hfour, add_zero] at hbudget
  omega

/-! ## The excess facts, from the crux -/

/-- Every complement-cut block has a damaged unit (its exit). -/
lemma one_le_damaged_inter_compCut (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ) : 1 ≤ (damaged θ ∩ p).card := by
  have hd := card_damaged_inter θ (mem_compCutBlocks.1 hp).1
    (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hp).2)
  have := Finset.card_pos.2 (exitSet_nonempty θ (mem_compCutBlocks.1 hp).1)
  omega

/-- A big complement-cut block has two damaged units. -/
lemma two_le_damaged_inter_of_big (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ compCutBlocks θ) (hpc : 2 ≤ p.card) :
    2 ≤ (damaged θ ∩ p).card := by
  classical
  obtain ⟨a, ha, a', ha', hne, hda, hda'⟩ :=
    two_le_damaged_of_cutSet_compl θ (mem_compCutBlocks.1 hp).1
      (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hp).2) hpc
  have hsub : ({a, a'} : Finset (Fin N)) ⊆ damaged θ ∩ p := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      exact Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩,
        by assumption⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at this

/-- The number of complement-cut blocks is bounded by the damage inside the region. -/
lemma card_compCutBlocks_le_damaged (θ : SysPartition N Finset.univ) :
    (compCutBlocks θ).card ≤ (damaged θ ∩ compCutRegion θ).card := by
  classical
  calc (compCutBlocks θ).card = ∑ _p ∈ compCutBlocks θ, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ p ∈ compCutBlocks θ, (damaged θ ∩ p).card :=
        Finset.sum_le_sum fun p hp => one_le_damaged_inter_compCut θ hp
    _ = (damaged θ ∩ compCutRegion θ).card := sum_damaged_compCut θ

/-- **Fact 5c.**  A positive excess leaves at most two complement-cut blocks. -/
theorem card_compCutBlocks_le_two_of_excess (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) (he : 0 < outExcess θ) :
    (compCutBlocks θ).card ≤ 2 := by
  have hr := two_le_card_outBlocks_of_outExcess_pos θ he
  have hcrux := one_le_damaged_out_of_two_le_outBlocks θ hD hr
  have hreg := damagedCount_eq_regions θ
  have hcc := card_compCutBlocks_le_damaged θ
  omega

/-- **Fact 5b.**  A positive excess with a big block leaves exactly one complement-cut
block. -/
theorem card_compCutBlocks_le_one_of_excess_big (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) (he : 0 < outExcess θ)
    {P : Finset (Fin N)} (hP : P ∈ compCutBlocks θ) (hPc : 2 ≤ P.card) :
    (compCutBlocks θ).card ≤ 1 := by
  classical
  by_contra hc
  -- a second block P' ≠ P adds a disjoint damaged unit, exceeding the budget
  obtain ⟨P', hP', hPP'⟩ : ∃ P' ∈ compCutBlocks θ, P' ≠ P := by
    by_contra hcc
    push_neg at hcc
    have : (compCutBlocks θ) ⊆ {P} := fun x hx => Finset.mem_singleton.2 (hcc x hx)
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this; omega
  have hr := two_le_card_outBlocks_of_outExcess_pos θ he
  have hcrux := one_le_damaged_out_of_two_le_outBlocks θ hD hr
  have hreg := damagedCount_eq_regions θ
  have h2 := two_le_damaged_inter_of_big θ hP hPc
  have h1 := one_le_damaged_inter_compCut θ hP'
  -- damaged ∩ P and damaged ∩ P' are disjoint subsets of damaged ∩ C
  have hdisj : Disjoint (damaged θ ∩ P) (damaged θ ∩ P') := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint P (mem_compCutBlocks.1 hP).1 P' (mem_compCutBlocks.1 hP').1
        (Ne.symm hPP')) (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx').2
  have hsub : (damaged θ ∩ P) ∪ (damaged θ ∩ P') ⊆ damaged θ ∩ compCutRegion θ := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 h).1,
        mem_compCutRegion.2 ⟨P, hP, (Finset.mem_inter.1 h).2⟩⟩
    · exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 h).1,
        mem_compCutRegion.2 ⟨P', hP', (Finset.mem_inter.1 h).2⟩⟩
  have hun := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hun
  omega

end Crux

end IIT
