/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Master

/-!
# The normalizer decomposition

The normalizer of a partition splits into a complement-cut half and an outputs half.  This
file establishes the region bookkeeping that turns those two sums into the five numbers
`u, m, b, o, e` that `d3_master` consumes.

The outputs half is pure algebra: since every outputs block's cut set has size
`|B| + |O| - |q|`, summing gives `|B|·|O| + |O|² - Σ|q|²`, and the last two terms are the
*excess* that a single outputs block makes vanish.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Decomp

variable [NeZero N]

/-- The complement-cut blocks tile the complement-cut region. -/
theorem sum_card_compCutBlocks (θ : SysPartition N Finset.univ) :
    ∑ p ∈ compCutBlocks θ, p.card = (compCutRegion θ).card := by
  classical
  have hbi : compCutRegion θ = (compCutBlocks θ).biUnion id := by
    ext j
    simp only [Finset.mem_biUnion, id]
    exact mem_compCutRegion
  have hdisj : ∀ p ∈ compCutBlocks θ, ∀ q ∈ compCutBlocks θ, p ≠ q →
      Disjoint (id p) (id q) := by
    intro p hp q hq hpq
    exact θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 q (mem_compCutBlocks.1 hq).1 hpq
  rw [hbi, Finset.card_biUnion hdisj]
  simp only [id]

/-- The outputs blocks tile the outputs region. -/
theorem sum_card_outBlocks (θ : SysPartition N Finset.univ) :
    ∑ q ∈ outBlocks θ, q.card = (outRegion θ).card := by
  classical
  have hbi : outRegion θ = (outBlocks θ).biUnion id := by
    ext j
    simp only [Finset.mem_biUnion, id]
    constructor
    · intro hj
      obtain ⟨p, hp, hdp, hjp⟩ := mem_outRegion.1 hj
      exact ⟨p, mem_outBlocks.2 ⟨hp, hdp⟩, hjp⟩
    · rintro ⟨p, hp, hjp⟩
      exact mem_outRegion.2 ⟨p, (mem_outBlocks.1 hp).1, (mem_outBlocks.1 hp).2, hjp⟩
  have hdisj : ∀ p ∈ outBlocks θ, ∀ q ∈ outBlocks θ, p ≠ q → Disjoint (id p) (id q) := by
    intro p hp q hq hpq
    exact θ.parts_disjoint p (mem_outBlocks.1 hp).1 q (mem_outBlocks.1 hq).1 hpq
  rw [hbi, Finset.card_biUnion hdisj]
  simp only [id]

/-- The two regions partition the substrate. -/
theorem card_compCutRegion_add_outRegion (θ : SysPartition N Finset.univ) :
    (compCutRegion θ).card + (outRegion θ).card = N := by
  classical
  have hdisj : Disjoint (compCutRegion θ) (outRegion θ) := by
    rw [Finset.disjoint_left]
    intro x hx hxo
    obtain ⟨p, hp, hxp⟩ := mem_compCutRegion.1 hx
    obtain ⟨p', hp', hd', hxp'⟩ := mem_outRegion.1 hxo
    have hne : p ≠ p' := by
      rintro rfl
      exact (mem_compCutBlocks.1 hp).2 hd'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 p' hp' hne) hxp hxp'
  have huniv : compCutRegion θ ∪ outRegion θ = Finset.univ := by
    refine Finset.eq_univ_of_forall fun j => ?_
    obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
    by_cases hd : θ.dir p = Dir.outputs
    · exact Finset.mem_union_right _ (mem_outRegion.2 ⟨p, hp, hd, hjp⟩)
    · exact Finset.mem_union_left _ (mem_compCutRegion.2 ⟨p, mem_compCutBlocks.2 ⟨hp, hd⟩, hjp⟩)
  have := Finset.card_union_of_disjoint hdisj
  rw [huniv, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The `both` region sits inside the complement-cut region. -/
theorem bothRegion_subset_compCutRegion (θ : SysPartition N Finset.univ) :
    bothRegion θ ⊆ compCutRegion θ := by
  intro x hx
  obtain ⟨p, hp, hdp, hxp⟩ := mem_bothRegion.1 hx
  refine mem_compCutRegion.2 ⟨p, mem_compCutBlocks.2 ⟨hp, ?_⟩, hxp⟩
  rw [hdp]
  exact by decide

/-- **The outputs half.**  Written without subtraction: each block's contribution plus its
square is its size times the whole cut region. -/
theorem sum_out_add_sq (θ : SysPartition N Finset.univ) :
    (∑ q ∈ outBlocks θ, q.card * (θ.cutSet q).card)
      + ∑ q ∈ outBlocks θ, q.card * q.card
      = ((bothRegion θ).card + (outRegion θ).card) * (outRegion θ).card := by
  classical
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ q ∈ outBlocks θ,
      q.card * (θ.cutSet q).card + q.card * q.card
        = q.card * ((bothRegion θ).card + (outRegion θ).card) := by
    intro q hq
    rw [card_cutSet_outputs θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2,
      ← Nat.mul_add]
    congr 1
    have hqo : q.card ≤ (outRegion θ).card :=
      Finset.card_le_card (subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2)
    omega
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_card_outBlocks, Nat.mul_comm]

/-- The sum of squares of the outputs blocks never exceeds the square of the region. -/
theorem sum_sq_le (θ : SysPartition N Finset.univ) :
    ∑ q ∈ outBlocks θ, q.card * q.card ≤ (outRegion θ).card * (outRegion θ).card := by
  classical
  calc ∑ q ∈ outBlocks θ, q.card * q.card
      ≤ ∑ q ∈ outBlocks θ, q.card * (outRegion θ).card := by
        refine Finset.sum_le_sum fun q hq => Nat.mul_le_mul_left _ ?_
        exact Finset.card_le_card
          (subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2)
    _ = (outRegion θ).card * (outRegion θ).card := by
        rw [← Finset.sum_mul, sum_card_outBlocks]

/-- The outputs excess. -/
noncomputable def outExcess (θ : SysPartition N Finset.univ) : ℕ :=
  (outRegion θ).card * (outRegion θ).card - ∑ q ∈ outBlocks θ, q.card * q.card

/-- **The outputs half, in the form `d3_master` consumes.** -/
theorem sum_out_eq (θ : SysPartition N Finset.univ) :
    (∑ q ∈ outBlocks θ, q.card * (θ.cutSet q).card)
      = (bothRegion θ).card * (outRegion θ).card + outExcess θ := by
  have h1 := sum_out_add_sq θ
  have h2 := sum_sq_le θ
  rw [outExcess]
  have hexp : ((bothRegion θ).card + (outRegion θ).card) * (outRegion θ).card
      = (bothRegion θ).card * (outRegion θ).card
        + (outRegion θ).card * (outRegion θ).card := by ring
  omega

/-- **Fact (2).**  A big complement-cut block damages two of its own units and each
singleton damages one, so a budget of three admits at most one singleton beside it. -/
theorem m_le_one_of_big (θ : SysPartition N Finset.univ) (hN : 3 ≤ N)
    (hD : damagedCount θ = 3) {P q r : Finset (Fin N)}
    (hP : P ∈ compCutBlocks θ) (hq : q ∈ compCutBlocks θ) (hr : r ∈ compCutBlocks θ)
    (hPq : P ≠ q) (hPr : P ≠ r) (hqr : q ≠ r) (hPc : 2 ≤ P.card) : False := by
  classical
  obtain ⟨a, ha, a', ha', hne, hda, hda'⟩ :=
    two_le_damaged_of_cutSet_compl θ (mem_compCutBlocks.1 hP).1
      (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hP).2) hPc
  obtain ⟨b, hb, hdb⟩ :=
    exists_damaged_of_cutSet_compl θ (mem_compCutBlocks.1 hq).1
      (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hq).2)
  obtain ⟨c, hc, hdc⟩ :=
    exists_damaged_of_cutSet_compl θ (mem_compCutBlocks.1 hr).1
      (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hr).2)
  have dPq := θ.parts_disjoint P (mem_compCutBlocks.1 hP).1 q (mem_compCutBlocks.1 hq).1 hPq
  have dPr := θ.parts_disjoint P (mem_compCutBlocks.1 hP).1 r (mem_compCutBlocks.1 hr).1 hPr
  have dqr := θ.parts_disjoint q (mem_compCutBlocks.1 hq).1 r (mem_compCutBlocks.1 hr).1 hqr
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 dPq ha (h ▸ hb)
  have hac : a ≠ c := fun h => Finset.disjoint_left.1 dPr ha (h ▸ hc)
  have ha'b : a' ≠ b := fun h => Finset.disjoint_left.1 dPq ha' (h ▸ hb)
  have ha'c : a' ≠ c := fun h => Finset.disjoint_left.1 dPr ha' (h ▸ hc)
  have hbc : b ≠ c := fun h => Finset.disjoint_left.1 dqr hb (h ▸ hc)
  have hsub : ({a, a', b, c} : Finset (Fin N)) ⊆ damaged θ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne, hab, hac]),
    Finset.card_insert_of_notMem (by simp [ha'b, ha'c]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton] at hcard
  rw [damagedCount] at hD
  omega

/-- With a big complement-cut block present, there are at most two blocks in all. -/
theorem card_compCutBlocks_le_two_of_big (θ : SysPartition N Finset.univ) (hN : 3 ≤ N)
    (hD : damagedCount θ = 3) {P : Finset (Fin N)} (hP : P ∈ compCutBlocks θ)
    (hPc : 2 ≤ P.card) : (compCutBlocks θ).card ≤ 2 := by
  classical
  by_contra hc
  have h3 : 3 ≤ (compCutBlocks θ).card := by omega
  have herase : 2 ≤ ((compCutBlocks θ).erase P).card := by
    rw [Finset.card_erase_of_mem hP]
    omega
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.1 (by omega : 1 < ((compCutBlocks θ).erase P).card)
  exact m_le_one_of_big θ hN hD hP (Finset.mem_of_mem_erase hq) (Finset.mem_of_mem_erase hr)
    (Finset.ne_of_mem_erase hq).symm (Finset.ne_of_mem_erase hr).symm hqr hPc

/-! ## Cycle alternation

The complement-cut region is the complement of the outputs region, and on a cycle a set
has as many exits as its complement: `exitSet Sᶜ` is literally `entrySet S`, and a set has
as many entries as exits.  So the outputs region has exactly as many arcs as the
complement-cut region has runs.
-/

/-- The two regions are complementary. -/
theorem compCutRegion_eq_compl (θ : SysPartition N Finset.univ) :
    compCutRegion θ = (outRegion θ)ᶜ := by
  classical
  ext j
  rw [Finset.mem_compl]
  constructor
  · intro hj hjo
    obtain ⟨p, hp, hjp⟩ := mem_compCutRegion.1 hj
    obtain ⟨p', hp', hd', hjp'⟩ := mem_outRegion.1 hjo
    have hne : p ≠ p' := by
      rintro rfl
      exact (mem_compCutBlocks.1 hp).2 hd'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_compCutBlocks.1 hp).1 p' hp' hne) hjp hjp'
  · intro hj
    obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
    by_cases hd : θ.dir p = Dir.outputs
    · exact absurd (mem_outRegion.2 ⟨p, hp, hd, hjp⟩) hj
    · exact mem_compCutRegion.2 ⟨p, mem_compCutBlocks.2 ⟨hp, hd⟩, hjp⟩

/-- `exitSet` of a complement is `entrySet` of the set. -/
theorem exitSet_compl (S : Finset (Fin N)) : exitSet Sᶜ = entrySet S := by
  ext j
  rw [mem_exitSet, mem_entrySet, Finset.mem_compl, Finset.mem_compl, not_not]

/-- **Cycle alternation.**  The two regions have equally many runs. -/
theorem card_exitSet_regions (θ : SysPartition N Finset.univ) :
    (exitSet (compCutRegion θ)).card = (exitSet (outRegion θ)).card := by
  rw [compCutRegion_eq_compl, exitSet_compl, card_entrySet]

/-- The units leaving the outputs region are exactly its exit points. -/
theorem sum_oOut_eq (θ : SysPartition N Finset.univ) :
    ∑ q ∈ outBlocks θ, (oOut θ q).card = (exitSet (outRegion θ)).card := by
  classical
  have hbi : exitSet (outRegion θ) = (outBlocks θ).biUnion fun q => oOut θ q := by
    ext j
    simp only [Finset.mem_biUnion]
    constructor
    · intro hj
      obtain ⟨hjo, hsj⟩ := mem_exitSet.1 hj
      obtain ⟨p, hp, hdp, hjp⟩ := mem_outRegion.1 hjo
      exact ⟨p, mem_outBlocks.2 ⟨hp, hdp⟩, mem_oOut.2 ⟨hjp, hsj⟩⟩
    · rintro ⟨q, hq, hjq⟩
      obtain ⟨hjq', hsj⟩ := mem_oOut.1 hjq
      exact mem_exitSet.2
        ⟨subset_outRegion θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2 hjq', hsj⟩
  have hdisj : ∀ p ∈ outBlocks θ, ∀ q ∈ outBlocks θ, p ≠ q →
      Disjoint (oOut θ p) (oOut θ q) := by
    intro p hp q hq hpq
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.1
      (θ.parts_disjoint p (mem_outBlocks.1 hp).1 q (mem_outBlocks.1 hq).1 hpq)
      (mem_oOut.1 hx).1 (mem_oOut.1 hx').1
  rw [hbi, Finset.card_biUnion hdisj]

/-- **The block count, against the complement-cut runs.** -/
theorem card_outBlocks_le_arcs (θ : SysPartition N Finset.univ) :
    (outBlocks θ).card
      ≤ (∑ q ∈ outBlocks θ, (oA θ q).card) + (exitSet (compCutRegion θ)).card := by
  rw [card_exitSet_regions, ← sum_oOut_eq]
  exact card_outBlocks_le θ

/-! ## The complement-cut half

At most one complement-cut block has two or more units, so the region is one big block
plus some singletons.  Summing gives `u(N-u) + m(N-1)`.
-/

/-- Every complement-cut block is nonempty. -/
lemma one_le_card_compCutBlock (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ compCutBlocks θ) : 1 ≤ p.card :=
  Finset.card_pos.2 (θ.parts_nonempty p (mem_compCutBlocks.1 hp).1)

/-- **The complement-cut half.**  With the big block unique, the region splits as `u + m`
and the sum as `u(N-u) + m(N-1)`. -/
theorem compCut_decomp (θ : SysPartition N Finset.univ)
    (huniq : ∀ p ∈ compCutBlocks θ, ∀ q ∈ compCutBlocks θ,
      2 ≤ p.card → 2 ≤ q.card → p = q) :
    ∃ u m : ℕ, (u = 0 ∨ 2 ≤ u) ∧ m = (compCutBlocks θ).card - (if u = 0 then 0 else 1)
      ∧ (compCutRegion θ).card = u + m
      ∧ (2 ≤ u → ∃ P ∈ compCutBlocks θ, 2 ≤ P.card)
      ∧ ∑ p ∈ compCutBlocks θ, p.card * (N - p.card) = u * (N - u) + m * (N - 1) := by
  classical
  by_cases hbig : ∃ p ∈ compCutBlocks θ, 2 ≤ p.card
  · obtain ⟨P, hP, hPc⟩ := hbig
    have hsing : ∀ q ∈ (compCutBlocks θ).erase P, q.card = 1 := by
      intro q hq
      have hqmem := Finset.mem_of_mem_erase hq
      have hqne : q ≠ P := Finset.ne_of_mem_erase hq
      have h1 := one_le_card_compCutBlock θ hqmem
      by_contra hc
      exact hqne (huniq q hqmem P hP (by omega) hPc)
    refine ⟨P.card, (compCutBlocks θ).card - 1, Or.inr hPc, ?_, ?_, fun _ => ⟨P, hP, hPc⟩, ?_⟩
    · rw [if_neg (by omega)]
    · -- the region is the big block plus the singletons
      rw [← sum_card_compCutBlocks, ← Finset.add_sum_erase _ _ hP]
      congr 1
      rw [Finset.sum_congr rfl hsing, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem hP]
    · rw [← Finset.add_sum_erase _ _ hP]
      congr 1
      have hterm : ∀ q ∈ (compCutBlocks θ).erase P, q.card * (N - q.card) = N - 1 := by
        intro q hq
        rw [hsing q hq, Nat.one_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
        Finset.card_erase_of_mem hP]
  · push_neg at hbig
    have hsing : ∀ q ∈ compCutBlocks θ, q.card = 1 := by
      intro q hq
      have h1 := one_le_card_compCutBlock θ hq
      have h2 := hbig q hq
      omega
    refine ⟨0, (compCutBlocks θ).card, Or.inl rfl, by rw [if_pos rfl]; omega, ?_,
      fun h => absurd h (by omega), ?_⟩
    · rw [← sum_card_compCutBlocks, Finset.sum_congr rfl hsing, Finset.sum_const,
        smul_eq_mul, mul_one]
      omega
    · have hterm : ∀ q ∈ compCutBlocks θ, q.card * (N - q.card) = N - 1 := by
        intro q hq
        rw [hsing q hq, Nat.one_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
      omega

/-- The outputs half in the shape `sysCutCount_split` leaves it. -/
theorem sum_out_eq' (θ : SysPartition N Finset.univ) :
    (∑ q ∈ outBlocks θ,
        q.card * ((bothRegion θ).card + (outRegion θ).card - q.card))
      = (bothRegion θ).card * (outRegion θ).card + outExcess θ := by
  classical
  have hcong : ∀ q ∈ outBlocks θ,
      q.card * ((bothRegion θ).card + (outRegion θ).card - q.card)
        = q.card * (θ.cutSet q).card := by
    intro q hq
    rw [card_cutSet_outputs θ (mem_outBlocks.1 hq).1 (mem_outBlocks.1 hq).2]
  rw [Finset.sum_congr rfl hcong, sum_out_eq θ]

/-- **The full decomposition.**  The normalizer of a `D = 3` partition is exactly
`u(N-u) + m(N-1) + b·o + e`, with `u + m + o = N` and `b ≤ u + m`. -/
theorem sysCutCount_decomp (θ : SysPartition N Finset.univ) (hN : 3 ≤ N)
    (hD : damagedCount θ = 3) :
    ∃ u m : ℕ, (u = 0 ∨ 2 ≤ u) ∧ m ≤ 3 ∧ (2 ≤ u → m ≤ 1)
      ∧ u + m + (outRegion θ).card = N
      ∧ (bothRegion θ).card ≤ u + m
      ∧ sysCutCount θ
          = u * (N - u) + m * (N - 1)
            + (bothRegion θ).card * (outRegion θ).card + outExcess θ := by
  classical
  have huniq : ∀ p ∈ compCutBlocks θ, ∀ q ∈ compCutBlocks θ,
      2 ≤ p.card → 2 ≤ q.card → p = q := by
    intro p hp q hq hpc hqc
    by_contra hpq
    exact atMostOne_big_of_damagedCount_three θ hN hD
      (mem_compCutBlocks.1 hp).1 (mem_compCutBlocks.1 hq).1 hpq
      (mem_compCutBlocks.1 hp).2 (mem_compCutBlocks.1 hq).2 hpc hqc
  obtain ⟨u, m, hu, hmdef, hreg, hwit, hsum⟩ := compCut_decomp θ huniq
  have hcard3 : (compCutBlocks θ).card ≤ 3 :=
    card_le_three_of_damagedCount_three θ hD (Finset.filter_subset _ _)
      fun p hp => (mem_compCutBlocks.1 hp).2
  have hum : 2 ≤ u → m ≤ 1 := by
    intro hu2
    obtain ⟨P, hP, hPc⟩ := hwit hu2
    have := card_compCutBlocks_le_two_of_big θ hN hD hP hPc
    rw [hmdef, if_neg (by omega)]
    omega
  refine ⟨u, m, hu, by omega, hum, ?_, ?_, ?_⟩
  · have := card_compCutRegion_add_outRegion θ
    omega
  · have hb := Finset.card_le_card (bothRegion_subset_compCutRegion θ)
    omega
  · rw [sysCutCount_split θ, hsum, sum_out_eq' θ]
    ring

/-! ## Facts (2) and (6) -/

/-- **Fact (6).**  No outputs region means no outputs blocks, hence no excess. -/
theorem outExcess_eq_zero_of_outRegion_empty (θ : SysPartition N Finset.univ)
    (ho : (outRegion θ).card = 0) : outExcess θ = 0 := by
  classical
  have hle := sum_sq_le θ
  rw [outExcess, ho]
  omega

theorem outRegion_pos_of_outExcess_pos (θ : SysPartition N Finset.univ)
    (he : 0 < outExcess θ) : 0 < (outRegion θ).card := by
  by_contra hc
  have h0 : (outRegion θ).card = 0 := by omega
  rw [outExcess_eq_zero_of_outRegion_empty θ h0] at he
  exact absurd he (by omega)

/-- **The `D = 3` normalizer bound**, given the three outstanding structural facts.
Proved where `u` and `m` are still in scope, so nothing has to be unpacked. -/
theorem sysCutCount_of_damagedCount_three (θ : SysPartition N Finset.univ)
    (hN : 8 ≤ N) (hD : damagedCount θ = 3)
    (hfact3 : 2 ≤ (bothRegion θ).card →
      (outRegion θ).card ≤ 1 ∧ outExcess θ = 0)
    (hfact4 : 0 < (outRegion θ).card →
      outExcess θ ≤ 2 * ((outRegion θ).card - 1))
    (hfact5a : 0 < outExcess θ → (bothRegion θ).card = 0)
    (hfact5b : 0 < outExcess θ →
      (∃ P ∈ compCutBlocks θ, 2 ≤ P.card) → (compCutBlocks θ).card ≤ 1)
    (hfact5c : 0 < outExcess θ → (compCutBlocks θ).card ≤ 2) :
    4 * sysCutCount θ ≤ (N - 1) * (N - 1) + 8 * (N - 1) := by
  classical
  have huniq : ∀ p ∈ compCutBlocks θ, ∀ q ∈ compCutBlocks θ,
      2 ≤ p.card → 2 ≤ q.card → p = q := by
    intro p hp q hq hpc hqc
    by_contra hpq
    exact atMostOne_big_of_damagedCount_three θ (by omega) hD
      (mem_compCutBlocks.1 hp).1 (mem_compCutBlocks.1 hq).1 hpq
      (mem_compCutBlocks.1 hp).2 (mem_compCutBlocks.1 hq).2 hpc hqc
  obtain ⟨u, m, hu, hmdef, hreg, hwit, hsum⟩ := compCut_decomp θ huniq
  have hcard3 : (compCutBlocks θ).card ≤ 3 :=
    card_le_three_of_damagedCount_three θ hD (Finset.filter_subset _ _)
      fun p hp => (mem_compCutBlocks.1 hp).2
  have hum : 2 ≤ u → m ≤ 1 := by
    intro hu2
    obtain ⟨P, hP, hPc⟩ := hwit hu2
    have := card_compCutBlocks_le_two_of_big θ (by omega) hD hP hPc
    rw [hmdef, if_neg (by omega)]
    omega
  have htot : u + m + (outRegion θ).card = N := by
    have := card_compCutRegion_add_outRegion θ
    omega
  have hble : (bothRegion θ).card ≤ u + m := by
    have hb := Finset.card_le_card (bothRegion_subset_compCutRegion θ)
    omega
  have hcc : sysCutCount θ
      = u * (N - u) + m * (N - 1)
        + (bothRegion θ).card * (outRegion θ).card + outExcess θ := by
    rw [sysCutCount_split θ, hsum, sum_out_eq' θ]
    ring
  rw [hcc]
  refine d3_master N u m (bothRegion θ).card (outRegion θ).card (outExcess θ)
    hN hu (by omega) hum htot hble hfact3 hfact4 hfact5a ?_ ?_
    (fun he => outRegion_pos_of_outExcess_pos θ he)
  · -- with a big block, a positive excess leaves exactly one complement-cut block
    intro he hu2
    obtain ⟨P, hP, hPc⟩ := hwit hu2
    have h1 := hfact5b he ⟨P, hP, hPc⟩
    have hPpos : 1 ≤ (compCutBlocks θ).card := Finset.card_pos.2 ⟨P, hP⟩
    rw [hmdef, if_neg (by omega)]
    omega
  · -- with no big block, at most two singletons
    intro he hu0
    have h1 := hfact5c he
    rw [hmdef, if_pos hu0]
    omega

/-! ## Excess and the number of outputs blocks

The excess `|O|² − Σ|q|²` is positive exactly when the outputs region is split: a single
block contributes its whole square, and no block contributes more than its share.
-/

/-- With at most one outputs block, the sum of squares is the whole square. -/
theorem outExcess_eq_zero_of_card_le_one (θ : SysPartition N Finset.univ)
    (hr : (outBlocks θ).card ≤ 1) : outExcess θ = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (outBlocks θ).card with h0 | hpos
  · -- no outputs blocks: the region is empty
    have hemp : outBlocks θ = ∅ := Finset.card_eq_zero.1 h0
    have ho : (outRegion θ).card = 0 := by
      rw [← sum_card_outBlocks, hemp, Finset.sum_empty]
    exact outExcess_eq_zero_of_outRegion_empty θ ho
  · -- exactly one outputs block, which is the whole region
    obtain ⟨q, hq⟩ : ∃ q, outBlocks θ = {q} := Finset.card_eq_one.1 (by omega)
    have hsum : q.card = (outRegion θ).card := by
      rw [← sum_card_outBlocks, hq, Finset.sum_singleton]
    rw [outExcess, hq, Finset.sum_singleton, hsum]
    omega

/-- **A positive excess means the outputs region is genuinely split.** -/
theorem two_le_card_outBlocks_of_outExcess_pos (θ : SysPartition N Finset.univ)
    (he : 0 < outExcess θ) : 2 ≤ (outBlocks θ).card := by
  by_contra hc
  rw [outExcess_eq_zero_of_card_le_one θ (by omega)] at he
  exact absurd he (by omega)

/-- The complement-cut region is nonempty exactly when some block is not an outputs
block; otherwise every block severs its outputs. -/
theorem compCutBlocks_nonempty_of_ne_univ (θ : SysPartition N Finset.univ)
    (h : outRegion θ ≠ Finset.univ) : (compCutBlocks θ).Nonempty := by
  classical
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  refine h (Finset.eq_univ_of_forall fun j => ?_)
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
  by_cases hd : θ.dir p = Dir.outputs
  · exact mem_outRegion.2 ⟨p, hp, hd, hjp⟩
  · exact absurd (mem_compCutBlocks.2 ⟨hp, hd⟩) (by rw [hemp]; exact Finset.notMem_empty p)

end Decomp

end IIT
