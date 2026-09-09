/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantExcl

/-!
# The `D = 2` bound: supporting walks and counts

Two tools for the classification of partitions damaging exactly two units.

* `exists_exit_backward`: walking backwards from a point outside a nonempty set `A`, the
  first element of `A` one meets has its successor outside `A`, and its second successor
  outside `A` as well unless the walk had length one.  The same `Nat.find` trap as
  `exists_no_live_of_double_gap`.
* `card_entrySet`: a set has as many entry points as exit points -- `shift` is a
  bijection, so `|shift⁻¹(p)| = |p|` and both counts equal `|p| - |p ∩ shift⁻¹(p)|`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Walk

variable [NeZero N]

/-- **The backward-walk trap.**  For nonempty `A` and `x ∉ A`, the first element of `A`
met walking backwards from `x` has its successor outside `A`; its second successor is also
outside `A`, unless the walk had length one, in which case that successor is `x` itself. -/
theorem exists_exit_backward {A : Finset (Fin N)} (hA : A.Nonempty) {x : Fin N}
    (hx : x ∉ A) :
    ∃ j ∈ A, shift j ∉ A ∧ (shift (shift j) ∉ A ∨ shift j = x) := by
  classical
  have hex : ∃ t : ℕ, pred^[t] x ∈ A := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨t, ht⟩ := exists_iterate_pred a x
    exact ⟨t, ht ▸ ha⟩
  obtain ⟨t₀, hmem, hmin⟩ : ∃ t, pred^[t] x ∈ A ∧ ∀ r < t, pred^[r] x ∉ A :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  have ht0pos : 0 < t₀ := by
    rcases Nat.eq_zero_or_pos t₀ with h | h
    · rw [h] at hmem; simp at hmem; exact absurd hmem hx
    · exact h
  have hstep : ∀ r : ℕ, shift (pred^[r + 1] x) = pred^[r] x := by
    intro r
    rw [Function.iterate_succ_apply']
    exact shift_pred _
  have h1 : shift (pred^[t₀] x) = pred^[t₀ - 1] x := by
    obtain ⟨r, hr⟩ : ∃ r, t₀ = r + 1 := ⟨t₀ - 1, by omega⟩
    subst hr
    simpa using hstep r
  refine ⟨pred^[t₀] x, hmem, ?_, ?_⟩
  · rw [h1]
    exact hmin _ (by omega)
  · rcases Nat.lt_or_ge t₀ 2 with hlt | hge
    · refine Or.inr ?_
      rw [h1]
      have : t₀ - 1 = 0 := by omega
      rw [this]
      simp
    · refine Or.inl ?_
      rw [h1]
      have he : t₀ - 1 = (t₀ - 2) + 1 := by omega
      rw [he, hstep (t₀ - 2)]
      exact hmin _ (by omega)

end Walk

section EntryExit

variable [NeZero N]

/-- The units outside `p` whose successor lies in `p`: one per maximal run. -/
def entrySet (p : Finset (Fin N)) : Finset (Fin N) := pᶜ.filter fun j => shift j ∈ p

lemma mem_entrySet {p : Finset (Fin N)} {j : Fin N} :
    j ∈ entrySet p ↔ j ∉ p ∧ shift j ∈ p := by
  unfold entrySet
  simp

/-- **Entries equal exits**: `shift` is a bijection, so both count `|p| - |p ∩ shift⁻¹ p|`. -/
theorem card_entrySet (p : Finset (Fin N)) : (entrySet p).card = (exitSet p).card := by
  classical
  have hpre : (p.filter fun j => shift j ∈ p).card
      + (p.filter fun j => shift j ∉ p).card = p.card :=
    Finset.card_filter_add_card_filter_not (s := p) (fun j => shift j ∈ p)
  have himg : (Finset.univ.filter fun j => shift j ∈ p).card = p.card := by
    rw [← Finset.card_image_of_injective (Finset.univ.filter fun j => shift j ∈ p)
      shift_injective]
    congr 1
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hy
      obtain ⟨a, ha⟩ := exists_iterate_shift y (pred y)
      exact ⟨pred y, by rw [shift_pred]; exact hy, shift_pred y⟩
  have hsplit : (Finset.univ.filter fun j => shift j ∈ p).card
      = (p.filter fun j => shift j ∈ p).card + (entrySet p).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        entrySet, Finset.mem_compl]
      constructor
      · intro hj
        by_cases hjp : j ∈ p
        · exact Or.inl ⟨hjp, hj⟩
        · exact Or.inr ⟨hjp, hj⟩
      · rintro (⟨-, hj⟩ | ⟨-, hj⟩) <;> exact hj
    · rw [Finset.disjoint_left]
      intro j hj hj'
      rw [Finset.mem_filter] at hj
      rw [mem_entrySet] at hj'
      exact hj'.1 hj.1
  unfold exitSet
  omega

end EntryExit

section Helpers

variable [NeZero N]

/-- Three distinct damaged units bound the damage count below. -/
lemma three_le_damagedCount (θ : SysPartition N Finset.univ) {j₁ j₂ j₃ : Fin N}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃)
    (hd₁ : Damaged θ j₁) (hd₂ : Damaged θ j₂) (hd₃ : Damaged θ j₃) :
    3 ≤ damagedCount θ := by
  classical
  have hs : ({j₁, j₂, j₃} : Finset (Fin N)) ⊆ damaged θ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
  have := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
    Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton] at this
  rw [damagedCount]
  omega

/-- A singleton block severing its inputs always damages its own unit. -/
lemma singleton_damaged (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    {b : Fin N} (hp : ({b} : Finset (Fin N)) ∈ θ.parts)
    (hcut : θ.cutSet {b} = ({b} : Finset (Fin N))ᶜ) : Damaged θ b := by
  refine ⟨shift b, mem_liveInputs.2 (Or.inl rfl), ?_⟩
  rw [θ.partOf_eq hp (Finset.mem_singleton_self b), hcut]
  simp only [Finset.mem_compl, Finset.mem_singleton]
  exact shift_ne_self hN b

/-- **The zero-damage trap.**  An undamaged outputs block, in the presence of a second
outputs block, contains a unit whose next two steps leave it and avoid every other block
severing its outputs: those steps can only land in blocks severing their inputs. -/
lemma trap_of_zero_damage (θ : SysPartition N Finset.univ)
    {q₁ q₂ : Finset (Fin N)} (hq₁ : q₁ ∈ θ.parts) (hd₁ : θ.dir q₁ = Dir.outputs)
    (hzero : ∀ j ∈ q₁, ¬ Damaged θ j)
    (hq₂ : q₂ ∈ θ.parts) (hne : q₂ ≠ q₁) (hd₂ : θ.dir q₂ = Dir.outputs)
    {x : Fin N} (hx : x ∈ q₂) :
    ∃ j ∈ q₁, shift j ∉ q₁ ∧ shift (shift j) ∉ q₁ ∧
      (∀ r ∈ θ.parts, r ≠ q₁ → (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) →
        shift j ∉ r ∧ shift (shift j) ∉ r) := by
  classical
  have hxq₁ : x ∉ q₁ := fun h =>
    Finset.disjoint_left.1 (θ.parts_disjoint q₂ hq₂ q₁ hq₁ hne) hx h
  obtain ⟨j, hj, hout, hbr⟩ :=
    exists_exit_backward (θ.parts_nonempty q₁ hq₁) hxq₁
  have hnotdam := hzero j hj
  have hnotcut : ∀ k ∈ liveInputs j, k ∉ θ.cutSet q₁ := by
    intro k hk hkc
    exact hnotdam ⟨k, hk, by rwa [θ.partOf_eq hq₁ hj]⟩
  have havoid : ∀ r ∈ θ.parts, r ≠ q₁ → (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) →
      shift j ∉ r ∧ shift (shift j) ∉ r := by
    intro r hr hrq hdr
    constructor
    · intro hmem
      refine hnotcut (shift j) (mem_liveInputs.2 (Or.inl rfl)) ?_
      rcases hdr with h | h
      · exact mem_cutSet_of_mem_other θ hr hrq h hd₁ hmem
      · exact mem_cutSet_of_mem_both θ hr hrq h hd₁ hmem
    · intro hmem
      refine hnotcut (shift (shift j)) (mem_liveInputs.2 (Or.inr rfl)) ?_
      rcases hdr with h | h
      · exact mem_cutSet_of_mem_other θ hr hrq h hd₁ hmem
      · exact mem_cutSet_of_mem_both θ hr hrq h hd₁ hmem
  have hss : shift (shift j) ∉ q₁ := by
    rcases hbr with h | h
    · exact h
    · exfalso
      have := (havoid q₂ hq₂ hne (Or.inl hd₂)).1
      rw [h] at this
      exact this hx
  exact ⟨j, hj, hout, hss, havoid⟩

end Helpers

section Runs

variable [NeZero N]

/-- **No pre-exit points means all runs are singletons**: every unit of the block has its
successor outside it.  Walking forward to the first exit, a run of length two or more
would put the unit before the exit in `preExitSet`. -/
lemma shift_notMem_of_preExit_empty {p : Finset (Fin N)} (hne : p ≠ Finset.univ)
    (hpre : preExitSet p = ∅) : ∀ y ∈ p, shift y ∉ p := by
  classical
  intro y hy hsy
  obtain ⟨z, hz⟩ : ∃ z, z ∉ p := by
    by_contra hall
    push_neg at hall
    exact hne (Finset.eq_univ_of_forall hall)
  have hex : ∃ t : ℕ, shift^[t + 1] y ∉ p := by
    obtain ⟨m, hm⟩ := exists_iterate_shift z y
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm; simp at hm; exact absurd (hm ▸ hy) hz
      · exact h
    exact ⟨m - 1, by rw [show m - 1 + 1 = m by omega, hm]; exact hz⟩
  obtain ⟨t₁, hout, hmin⟩ : ∃ t, shift^[t + 1] y ∉ p ∧ ∀ r < t, shift^[r + 1] y ∈ p := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun r hr => ?_⟩
    by_contra hcon
    exact Nat.find_min hex hr hcon
  have hexit : shift^[t₁] y ∈ exitSet p := by
    refine mem_exitSet.2 ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t₁ with h | h
      · rw [h]; simpa using hy
      · have := hmin (t₁ - 1) (by omega)
        rwa [show t₁ - 1 + 1 = t₁ by omega] at this
    · rw [← Function.iterate_succ_apply' shift t₁ y]
      exact hout
  rcases Nat.eq_zero_or_pos t₁ with h | h
  · rw [h] at hexit
    simp only [Function.iterate_zero, id] at hexit
    exact (mem_exitSet.1 hexit).2 hsy
  · have hprev : shift^[t₁ - 1] y ∈ p := by
      rcases Nat.eq_zero_or_pos (t₁ - 1) with h' | h'
      · rw [h']; simpa using hy
      · have := hmin (t₁ - 1 - 1) (by omega)
        rwa [show t₁ - 1 - 1 + 1 = t₁ - 1 by omega] at this
    have hstep : shift (shift^[t₁ - 1] y) = shift^[t₁] y := by
      have := Function.iterate_succ_apply' shift (t₁ - 1) y
      rw [Nat.succ_eq_add_one, show t₁ - 1 + 1 = t₁ by omega] at this
      exact this.symm
    have : shift^[t₁ - 1] y ∈ preExitSet p :=
      mem_preExitSet.2 ⟨hprev, by rw [hstep]; exact hexit⟩
    rw [hpre] at this
    simp at this

end Runs

end IIT
