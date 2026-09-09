/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3

/-!
# All-outputs partitions at `D = 3`

If every block severs its outputs and exactly three units are damaged, the partition is
either a singleton plus its complement (normalizer `2(N-1)`) or three singletons
(normalizer `3(N-1)`).
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section AllOut

variable [NeZero N]

theorem sysCutCount_all_outputs_three (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) (hall : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs) :
    sysCutCount θ = 2 * (N - 1) ∨ sysCutCount θ = 3 * (N - 1) := by
  classical
  have hcompl : ∀ p ∈ θ.parts, θ.cutSet p = pᶜ :=
    fun p hp => cutSet_eq_compl_of_all_outputs θ hall hp
  have hk : θ.parts.card ≤ 3 :=
    hD ▸ card_le_damagedCount_of_forall_compl θ (Finset.Subset.refl _) hcompl
  have hcard : θ.parts.card = 2 ∨ θ.parts.card = 3 := by
    have := θ.two_le
    omega
  rcases hcard with h2 | h3
  · obtain ⟨p, q, hpq, hpar⟩ := Finset.card_eq_two.1 h2
    have hp : p ∈ θ.parts := by rw [hpar]; exact Finset.mem_insert_self _ _
    have hq : q ∈ θ.parts := by
      rw [hpar]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    have hdisj : Disjoint p q := θ.parts_disjoint p hp q hq hpq
    have hunion : p ∪ q = Finset.univ := by
      refine Finset.eq_univ_of_forall fun x => ?_
      obtain ⟨r, hr, hxr⟩ := θ.parts_cover x (Finset.mem_univ x)
      rw [hpar] at hr
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · exact Finset.mem_union_left _ hxr
      · rw [Finset.mem_singleton] at hr'; subst hr'
        exact Finset.mem_union_right _ hxr
    have hsum : p.card + q.card = N := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hppos := Finset.card_pos.2 (θ.parts_nonempty p hp)
    have hqpos := Finset.card_pos.2 (θ.parts_nonempty q hq)
    have hnotboth : ¬ (2 ≤ p.card ∧ 2 ≤ q.card) := by
      intro ⟨hcp, hcq⟩
      obtain ⟨a, ha, a', ha', hne, hda, hda'⟩ :=
        two_le_damaged_of_cutSet_compl θ hp (hcompl p hp) hcp
      obtain ⟨b, hb, b', hb', hne', hdb, hdb'⟩ :=
        two_le_damaged_of_cutSet_compl θ hq (hcompl q hq) hcq
      have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb)
      have hab' : a ≠ b' := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb')
      have ha'b : a' ≠ b := fun h => Finset.disjoint_left.1 hdisj ha' (h ▸ hb)
      have ha'b' : a' ≠ b' := fun h => Finset.disjoint_left.1 hdisj ha' (h ▸ hb')
      have hsub : ({a, a', b, b'} : Finset (Fin N)) ⊆ damaged θ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hne, hab, hab']),
        Finset.card_insert_of_notMem (by simp [ha'b, ha'b']),
        Finset.card_insert_of_notMem (by simp [hne']),
        Finset.card_singleton] at hle
      have hDc : (damaged θ).card = 3 := hD
      exact absurd hle (by omega)
    have hsing : p.card = 1 ∨ q.card = 1 := by omega
    have hpq_mem : p ∉ ({q} : Finset (Finset (Fin N))) := by simpa using hpq
    rw [sysCutCount, hpar, Finset.sum_insert hpq_mem, Finset.sum_singleton,
      hcompl p hp, hcompl q hq, Finset.card_compl, Finset.card_compl, Fintype.card_fin]
    rcases hsing with hp1 | hq1
    · have hqN : q.card = N - 1 := by omega
      rw [hp1, hqN, show N - (N - 1) = 1 by omega]
      exact Or.inl (by omega)
    · have hpN : p.card = N - 1 := by omega
      rw [hq1, hpN, show N - (N - 1) = 1 by omega]
      exact Or.inl (by omega)
  · have hsing : ∀ p ∈ θ.parts, p.card = 1 := by
      intro p hp
      by_contra hne
      have h2 : 2 ≤ p.card := by
        have := Finset.card_pos.2 (θ.parts_nonempty p hp)
        omega
      have hrest : (θ.parts.erase p).card = 2 := by
        rw [Finset.card_erase_of_mem hp, h3]
      obtain ⟨q, r, hqr, hrest_eq⟩ := Finset.card_eq_two.1 hrest
      have hq_erase : q ∈ θ.parts.erase p := by
        rw [hrest_eq]; exact Finset.mem_insert_self _ _
      have hr_erase : r ∈ θ.parts.erase p := by
        rw [hrest_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hq : q ∈ θ.parts := Finset.mem_of_mem_erase hq_erase
      have hr : r ∈ θ.parts := Finset.mem_of_mem_erase hr_erase
      have hqp : p ≠ q := (Finset.ne_of_mem_erase hq_erase).symm
      have hrp : p ≠ r := (Finset.ne_of_mem_erase hr_erase).symm
      obtain ⟨a, ha, a', ha', hneaa', hda, hda'⟩ :=
        two_le_damaged_of_cutSet_compl θ hp (hcompl p hp) h2
      obtain ⟨b, hb, hdb⟩ := exists_damaged_of_cutSet_compl θ hq (hcompl q hq)
      obtain ⟨c, hc, hdc⟩ := exists_damaged_of_cutSet_compl θ hr (hcompl r hr)
      have hab : a ≠ b := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p hp q hq hqp) ha (h ▸ hb)
      have ha'b : a' ≠ b := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p hp q hq hqp) ha' (h ▸ hb)
      have hac : a ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p hp r hr hrp) ha (h ▸ hc)
      have ha'c : a' ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p hp r hr hrp) ha' (h ▸ hc)
      have hbc : b ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint q hq r hr hqr) hb (h ▸ hc)
      have hsub : ({a, a', b, c} : Finset (Fin N)) ⊆ damaged θ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;>
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hneaa', hab, hac]),
        Finset.card_insert_of_notMem (by simp [ha'b, ha'c]),
        Finset.card_insert_of_notMem (by simp [hbc]),
        Finset.card_singleton] at hle
      have hDc : (damaged θ).card = 3 := hD
      exact absurd hle (by omega)
    have hcontrib : ∀ p ∈ θ.parts, p.card * (θ.cutSet p).card = N - 1 := by
      intro p hp
      rw [hcompl p hp, Finset.card_compl, Fintype.card_fin, hsing p hp, Nat.one_mul]
    rw [sysCutCount, Finset.sum_congr rfl hcontrib, Finset.sum_const, h3, nsmul_eq_mul]
    exact Or.inr rfl

lemma sysCutCount_all_outputs_three_le (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) (hall : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs) :
    sysCutCount θ ≤ 3 * (N - 1) := by
  rcases sysCutCount_all_outputs_three hN θ hD hall with h | h <;> rw [h] <;> omega

/-- At most one complement-cut block of size `≥ 2`. -/
lemma card_big_compCut_le_one (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) :
    ((compCutBlocks θ).filter fun p => 2 ≤ p.card).card ≤ 1 := by
  classical
  let P : Finset (Fin N) → Prop := fun p => 2 ≤ p.card
  let B : Finset (Finset (Fin N)) := (compCutBlocks θ).filter P
  change B.card ≤ 1
  by_contra h
  have h2 : 2 ≤ B.card := by omega
  have hBne : B.Nonempty := Finset.one_le_card.mp (Nat.le_trans (by decide : 1 ≤ 2) h2)
  obtain ⟨p, hp⟩ := hBne
  have hpI : p ∈ compCutBlocks θ := (Finset.mem_filter.1 hp).1
  have hpc : 2 ≤ p.card := (Finset.mem_filter.1 hp).2
  have hpθ : p ∈ θ.parts := (mem_compCutBlocks.1 hpI).1
  have hpd : θ.dir p ≠ Dir.outputs := (mem_compCutBlocks.1 hpI).2
  have hrest : 0 < (B.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hrest
  have hqmem : q ∈ B := Finset.mem_of_mem_erase hq
  have hqI : q ∈ compCutBlocks θ := (Finset.mem_filter.1 hqmem).1
  have hqc : 2 ≤ q.card := (Finset.mem_filter.1 hqmem).2
  have hqθ : q ∈ θ.parts := (mem_compCutBlocks.1 hqI).1
  have hqd : θ.dir q ≠ Dir.outputs := (mem_compCutBlocks.1 hqI).2
  have hpq : p ≠ q := (Finset.ne_of_mem_erase hq).symm
  exact atMostOne_big_of_damagedCount_three θ hN hD hpθ hqθ hpq hpd hqd hpc hqc

/-- Complement-cut contribution: at most one AM-GM term `N²/4` and two singletons. -/
lemma four_mul_sum_compCut (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 3) :
    4 * ∑ p ∈ compCutBlocks θ, p.card * (θ.cutSet p).card ≤ N * N + 8 * (N - 1) := by
  classical
  have hsub : compCutBlocks θ ⊆ θ.parts := Finset.filter_subset _ _
  have hI : (compCutBlocks θ).card ≤ 3 :=
    card_le_three_of_damagedCount_three θ hD hsub fun p hp => (mem_compCutBlocks.1 hp).2
  have hcontrib : ∀ p ∈ compCutBlocks θ,
      p.card * (θ.cutSet p).card = p.card * (N - p.card) := by
    intro p hp
    exact cutContribution_compCut θ (mem_compCutBlocks.1 hp).1 (mem_compCutBlocks.1 hp).2
  rw [Finset.sum_congr rfl hcontrib]
  by_cases hB : ∃ p ∈ compCutBlocks θ, 2 ≤ p.card
  · obtain ⟨p0, hp0, hc0⟩ := hB
    have hp0θ := (mem_compCutBlocks.1 hp0).1
    have hsmall : ∀ q ∈ compCutBlocks θ, q ≠ p0 → q.card = 1 := by
      intro q hq hne
      have hqθ := (mem_compCutBlocks.1 hq).1
      have hqd := (mem_compCutBlocks.1 hq).2
      have hpd := (mem_compCutBlocks.1 hp0).2
      by_contra hne1
      have hq2 : 2 ≤ q.card := by
        have := Finset.card_pos.2 (θ.parts_nonempty q hqθ)
        omega
      exact atMostOne_big_of_damagedCount_three θ hN hD hp0θ hqθ hne.symm hpd hqd hc0 hq2
    have hsc : ((compCutBlocks θ).erase p0).card ≤ 1 := by
      by_contra hsc
      have h2e : 2 ≤ ((compCutBlocks θ).erase p0).card := by omega
      obtain ⟨q, r, hqr, hrest_eq⟩ := Finset.card_eq_two.1 (le_antisymm (by
        have := Finset.card_erase_of_mem hp0
        omega) h2e)
      have hq_erase : q ∈ (compCutBlocks θ).erase p0 := by
        rw [hrest_eq]; exact Finset.mem_insert_self _ _
      have hr_erase : r ∈ (compCutBlocks θ).erase p0 := by
        rw [hrest_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hqI := Finset.mem_of_mem_erase hq_erase
      have hrI := Finset.mem_of_mem_erase hr_erase
      have hqθ := (mem_compCutBlocks.1 hqI).1
      have hrθ := (mem_compCutBlocks.1 hrI).1
      have hqp : p0 ≠ q := (Finset.ne_of_mem_erase hq_erase).symm
      have hrp : p0 ≠ r := (Finset.ne_of_mem_erase hr_erase).symm
      obtain ⟨a, ha, a', ha', hneaa', hda, hda'⟩ :=
        two_le_damaged_of_cutSet_compl θ hp0θ
          (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hp0).2) hc0
      obtain ⟨b, hb, hdb⟩ :=
        exists_damaged_of_cutSet_compl θ hqθ
          (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hqI).2)
      obtain ⟨c, hc, hdc⟩ :=
        exists_damaged_of_cutSet_compl θ hrθ
          (cutSet_compl_of_ne_outputs θ (mem_compCutBlocks.1 hrI).2)
      have hab : a ≠ b := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p0 hp0θ q hqθ hqp) ha (h ▸ hb)
      have ha'b : a' ≠ b := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p0 hp0θ q hqθ hqp) ha' (h ▸ hb)
      have hac : a ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p0 hp0θ r hrθ hrp) ha (h ▸ hc)
      have ha'c : a' ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint p0 hp0θ r hrθ hrp) ha' (h ▸ hc)
      have hbc : b ≠ c := fun h =>
        Finset.disjoint_left.1 (θ.parts_disjoint q hqθ r hrθ hqr) hb (h ▸ hc)
      have hsub : ({a, a', b, c} : Finset (Fin N)) ⊆ damaged θ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;>
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hneaa', hab, hac]),
        Finset.card_insert_of_notMem (by simp [ha'b, ha'c]),
        Finset.card_insert_of_notMem (by simp [hbc]),
        Finset.card_singleton] at hle
      have hDc : (damaged θ).card = 3 := hD
      exact absurd hle (by omega)
    have hsum_small :
        ∑ q ∈ (compCutBlocks θ).erase p0, q.card * (N - q.card) ≤ 1 * (N - 1) := by
      have h1 : ∀ q ∈ (compCutBlocks θ).erase p0, q.card * (N - q.card) = N - 1 := by
        intro q hq
        have hqI := Finset.mem_of_mem_erase hq
        have hne := Finset.ne_of_mem_erase hq
        rw [hsmall q hqI hne, Nat.one_mul]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      have : ((compCutBlocks θ).erase p0).card * (N - 1) ≤ 1 * (N - 1) :=
        Nat.mul_le_mul_right _ hsc
      exact this
    have hp0_mem : p0 ∈ compCutBlocks θ := hp0
    rw [← Finset.add_sum_erase _ _ hp0_mem]
    have h4p : 4 * (p0.card * (N - p0.card)) ≤ N * N := by
      have := card_mul_compl_le p0
      rwa [Finset.card_compl, Fintype.card_fin] at this
    have h4s : 4 * ∑ q ∈ (compCutBlocks θ).erase p0, q.card * (N - q.card) ≤ 4 * (N - 1) := by
      have := Nat.mul_le_mul_left 4 hsum_small
      omega
    calc 4 * (p0.card * (N - p0.card) +
            ∑ q ∈ (compCutBlocks θ).erase p0, q.card * (N - q.card))
        = 4 * (p0.card * (N - p0.card)) +
            4 * ∑ q ∈ (compCutBlocks θ).erase p0, q.card * (N - q.card) := by
          ring
      _ ≤ N * N + 8 * (N - 1) :=
        Nat.add_le_add h4p (le_trans h4s (by omega : 4 * (N - 1) ≤ 8 * (N - 1)))
  · push_neg at hB
    have h1 : ∀ p ∈ compCutBlocks θ, p.card * (N - p.card) = N - 1 := by
      intro p hp
      have hpθ := (mem_compCutBlocks.1 hp).1
      have hpos := Finset.card_pos.2 (θ.parts_nonempty p hpθ)
      have : p.card = 1 := by
        have := hB p hp
        omega
      rw [this, Nat.one_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hle : (compCutBlocks θ).card * (N - 1) ≤ 3 * (N - 1) :=
      Nat.mul_le_mul_right _ hI
    have h4 : 4 * ((compCutBlocks θ).card * (N - 1)) ≤ 12 * (N - 1) := by
      have := Nat.mul_le_mul_left 4 hle
      calc 4 * ((compCutBlocks θ).card * (N - 1))
          ≤ 4 * (3 * (N - 1)) := this
        _ = 12 * (N - 1) := by ring
    have h12 : 12 * (N - 1) ≤ N * N + 8 * (N - 1) := by
      have h2 : 2 ≤ N := by omega
      obtain ⟨k, hk⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
      have h4N : 4 * (N - 1) ≤ N * N := by
        rw [hk]
        ring_nf
        omega
      omega
    exact le_trans h4 h12

end AllOut

end IIT
