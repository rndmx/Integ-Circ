/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import IIT.System

/-!
# Min-dependency

If a two-block split `{j}` / `S \ {j}` leaves the partitioned effect repertoire equal
to the intact one, then `φ_s(S) = 0`.  Instantiated for the circulant when some unit
of `S` has no live inputs in `S`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

lemma erase_ne_singleton {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) : ({j} : Finset (Fin N)) ≠ S.erase j := by
  intro h
  exact Finset.notMem_erase j S (h ▸ Finset.mem_singleton_self j)

/-- `{j}` severs inputs; `S \ {j}` severs outputs. Requires `|S| ≥ 2`. -/
noncomputable def splitAt {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) : SysPartition N S where
  parts := {{j}, S.erase j}
  dir p := if p = {j} then Dir.inputs else Dir.outputs
  parts_nonempty := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact ⟨j, Finset.mem_singleton_self j⟩
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact hrest
  parts_subset := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact Finset.singleton_subset_iff.2 hj
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact Finset.erase_subset j S
  parts_disjoint := by
    intro p hp q hq hpq
    rcases Finset.mem_insert.1 hp with hp1 | hp1 <;>
      rcases Finset.mem_insert.1 hq with hq1 | hq1
    · subst hp1; subst hq1; exact (hpq rfl).elim
    · subst hp1; rw [Finset.mem_singleton] at hq1; subst hq1
      exact Finset.disjoint_singleton_left.2 (Finset.notMem_erase j S)
    · subst hq1; rw [Finset.mem_singleton] at hp1; subst hp1
      exact Finset.disjoint_singleton_right.2 (Finset.notMem_erase j S)
    · rw [Finset.mem_singleton] at hp1 hq1; subst hp1; subst hq1; exact (hpq rfl).elim
  parts_cover := fun i hi =>
    if hij : i = j then
      ⟨{j}, Finset.mem_insert.2 (Or.inl rfl), hij ▸ Finset.mem_singleton.2 rfl⟩
    else
      ⟨S.erase j, Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 rfl)),
        Finset.mem_erase.2 ⟨hij, hi⟩⟩
  two_le := by
    have hne := erase_ne_singleton hj hrest
    have hnot : ({j} : Finset (Fin N)) ∉ ({S.erase j} : Finset (Finset (Fin N))) := by
      intro h; exact hne (Finset.eq_of_mem_singleton h)
    rw [Finset.card_insert_of_notMem hnot, Finset.card_singleton]

lemma splitAt_dir_j {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    (splitAt hj hrest).dir {j} = Dir.inputs := by
  simp [splitAt]

lemma splitAt_dir_rest {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    (splitAt hj hrest).dir (S.erase j) = Dir.outputs := by
  unfold splitAt
  dsimp
  rw [if_neg]
  exact Ne.symm (erase_ne_singleton hj hrest)

lemma splitAt_cut_j {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    (splitAt hj hrest).cutSet {j} = S.erase j := by
  rw [SysPartition.cutSet, splitAt_dir_j]
  ext x
  simp [Finset.mem_erase, Finset.mem_sdiff]
  exact and_comm

lemma splitAt_cut_rest {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    (splitAt hj hrest).cutSet (S.erase j) = ∅ := by
  have hne := (erase_ne_singleton hj hrest).symm
  ext x
  simp [SysPartition.cutSet, splitAt, hne]

lemma splitAt_partOf_j {S : Finset (Fin N)} {j : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) :
    (splitAt hj hrest).partOf j = {j} :=
  (splitAt hj hrest).partOf_eq (Finset.mem_insert_self _ _) (Finset.mem_singleton_self j)

lemma splitAt_partOf_rest {S : Finset (Fin N)} {j i : Fin N} (hj : j ∈ S)
    (hrest : (S.erase j).Nonempty) (hi : i ∈ S.erase j) :
    (splitAt hj hrest).partOf i = S.erase j :=
  (splitAt hj hrest).partOf_eq (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hi

lemma effUnit_univ_prob (T : UnitTPM N) (m : State N) (i : Fin N) (b : Bool) :
    effUnit T Finset.univ m i b = T.prob i m b := by
  have hconst : ∀ v ∈ agree Finset.univ m, T.prob i v b = T.prob i m b := by
    intro v hv
    have : v = m := funext fun k => mem_agree.1 hv k (Finset.mem_univ k)
    rw [this]
  rw [effUnit, Finset.sum_congr rfl fun v hv => hconst v hv, Finset.sum_const, nsmul_eq_mul]
  have : (0 : ℝ) < (agree Finset.univ m).card :=
    Nat.cast_pos.2 (Finset.card_pos.2 (agree_nonempty _ _))
  field_simp

/-- If `j`'s law is constant on the split fibre, the partitioned effect equals the intact one. -/
lemma sysPartEffProb_splitAt {T : UnitTPM N} {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) (s u t : State N)
    (hconst : ∀ v ∈ agree (S.erase j)ᶜ (merge S s u),
      T.prob j v (t j) = T.prob j (merge S s u) (t j)) :
    sysPartEffProb T S u (splitAt hj hrest) s t = sysEffProb T S u s t := by
  rw [sysPartEffProb, sysEffProb]
  refine Finset.prod_congr rfl fun i hi => ?_
  by_cases hij : i = j
  · rw [hij, splitAt_partOf_j, splitAt_cut_j]
    rw [effUnit, Finset.sum_congr rfl fun v hv => hconst v hv, Finset.sum_const, nsmul_eq_mul]
    have : (0 : ℝ) < (agree (S.erase j)ᶜ (merge S s u)).card :=
      Nat.cast_pos.2 (Finset.card_pos.2 (agree_nonempty _ _))
    field_simp
  · have hi' : i ∈ S.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
    rw [splitAt_partOf_rest hj hrest hi', splitAt_cut_rest, Finset.compl_empty,
      effUnit_univ_prob]

lemma sysPhiE_splitAt_zero {T : UnitTPM N} {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) (s u t : State N)
    (hconst : ∀ v ∈ agree (S.erase j)ᶜ (merge S s u),
      T.prob j v (t j) = T.prob j (merge S s u) (t j)) :
    sysPhiE T S u (splitAt hj hrest) s t = 0 := by
  rw [sysPhiE, sysPartEffProb_splitAt hj hrest s u t hconst]
  by_cases hp : sysEffProb T S u s t = 0
  · rw [hp, zero_mul]
  · rw [div_self hp, Real.logb_one, pos, max_eq_left le_rfl, mul_zero]

/-- **Min-dependency engine.**  A split that does not change the effect repertoire
forces `φ_s(S) = 0`. -/
theorem sysPhi_eq_zero_of_splitFibre {T : UnitTPM N} {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) (u s : State N)
    (hconst : ∀ (t v : State N), v ∈ agree (S.erase j)ᶜ (merge S s u) →
      T.prob j v (t j) = T.prob j (merge S s u) (t j)) :
    sysPhi T S u s = 0 := by
  haveI : Nonempty (SysPartition N S) := ⟨splitAt hj hrest⟩
  have h0 : ∀ tc te, sysPhiOfState T S u s tc te = 0 := by
    intro tc te
    have he : sysPhiE T S u (splitAt hj hrest) s te = 0 :=
      sysPhiE_splitAt_zero hj hrest s u te (fun v hv => hconst te v hv)
    have hphi : sysPhiAt T S u (splitAt hj hrest) s tc te = 0 := by
      simp only [sysPhiAt, he, min_eq_right (sysPhiC_nonneg T S u _ s tc)]
    have hns : normalizedSysPhiAt T S u (splitAt hj hrest) s tc te = 0 := by
      simp [normalizedSysPhiAt, hphi]
    obtain ⟨θ0, hθ0⟩ :=
      argminSet_nonempty (fun θ : SysPartition N S =>
        normalizedSysPhiAt T S u θ s tc te)
    have hz0 : normalizedSysPhiAt T S u θ0 s tc te = 0 := by
      apply le_antisymm
      · have := (mem_argminSet.1 hθ0) (splitAt hj hrest)
        simpa [hns] using this
      · exact div_nonneg (sysPhiAt_nonneg T S u θ0 s tc te) (Nat.cast_nonneg _)
    refine le_antisymm ?_ (sysPhiOfState_nonneg T S u s tc te)
    unfold sysPhiOfState sysMipSetAt
    refine sup'OrZero_le le_rfl fun θ hθ => ?_
    have hr : normalizedSysPhiAt T S u θ s tc te = 0 := by
      apply le_antisymm
      · have := (mem_argminSet.1 hθ) θ0
        simpa [hz0] using this
      · exact div_nonneg (sysPhiAt_nonneg T S u θ s tc te) (Nat.cast_nonneg _)
    have hcc : (sysCutCount θ : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (sysCutCount_pos θ).ne'
    rw [normalizedSysPhiAt] at hr
    exact le_of_eq ((div_eq_zero_iff.1 hr).resolve_right hcc)
  unfold sysPhi
  refine le_antisymm ?_ (sysPhi_nonneg T S u s)
  exact sup'OrZero_le le_rfl fun p _ => le_of_eq (h0 p.1 p.2)

end IIT
