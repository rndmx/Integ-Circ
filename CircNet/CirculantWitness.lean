/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD2c

/-!
# The three-arc witness

The partition of `Fin N` into three arcs `[0,a) / [a,a+k) / [a+k,N)` with directions
outputs / inputs / both.  Its damage is confined to the four units at the ends of the
second and third arcs, and its normalizer is `a·k + 2·k·(N-k)`: quadratic, while the
damage stays bounded.  This is the partition that starves every `D ≤ 2` competitor out of
the minimum information partition set.

Only an upper bound on the damage is needed, which keeps the interval reasoning entirely
wrap-free: every unit that matters shifts forward inside `[0, N)`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Witness

variable [NeZero N]

/-- First arc `[0, a)`, direction outputs. -/
def arcA (a : ℕ) : Finset (Fin N) := Finset.univ.filter fun j => j.val < a

/-- Second arc `[a, a+k)`, direction inputs. -/
def arcB (a k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun j => a ≤ j.val ∧ j.val < a + k

/-- Third arc `[a+k, N)`, direction both. -/
def arcC (a k : ℕ) : Finset (Fin N) := Finset.univ.filter fun j => a + k ≤ j.val

lemma mem_arcA {a : ℕ} {j : Fin N} : j ∈ arcA a ↔ j.val < a := by
  unfold arcA
  simp

lemma mem_arcB {a k : ℕ} {j : Fin N} : j ∈ arcB a k ↔ a ≤ j.val ∧ j.val < a + k := by
  unfold arcB
  simp

lemma mem_arcC {a k : ℕ} {j : Fin N} : j ∈ arcC a k ↔ a + k ≤ j.val := by
  unfold arcC
  simp

/-- Counting an initial segment of `Fin N`. -/
lemma card_val_lt (x : ℕ) (hx : x ≤ N) :
    (Finset.univ.filter fun j : Fin N => j.val < x).card = x := by
  classical
  have hbij : (Finset.univ.filter fun j : Fin N => j.val < x).card
      = (Finset.range x).card := by
    apply Finset.card_nbij (fun j => j.val)
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      rw [Finset.mem_coe, Finset.mem_range]
      exact hj.2
    · intro j hj j' hj' he
      exact Fin.ext he
    · intro m hm
      rw [Finset.mem_coe, Finset.mem_range] at hm
      refine ⟨⟨m, by omega⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hm⟩
  rw [hbij, Finset.card_range]

lemma card_arcA {a : ℕ} (hx : a ≤ N) : (arcA a : Finset (Fin N)).card = a :=
  card_val_lt a hx

lemma card_arcB {a k : ℕ} (hx : a + k ≤ N) : (arcB a k : Finset (Fin N)).card = k := by
  have hsplit : (arcB a k : Finset (Fin N))
      = (Finset.univ.filter fun j : Fin N => j.val < a + k) \
        (Finset.univ.filter fun j : Fin N => j.val < a) := by
    ext j
    rw [mem_arcB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Finset.mem_univ _, h2⟩, fun hc => by omega⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      have : ¬ j.val < a := fun hc => h1 ⟨Finset.mem_univ _, hc⟩
      exact ⟨by omega, h2⟩
  rw [hsplit, Finset.card_sdiff]
  have hint : ((Finset.univ.filter fun j : Fin N => j.val < a) ∩
      (Finset.univ.filter fun j : Fin N => j.val < a + k))
      = Finset.univ.filter fun j : Fin N => j.val < a := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, -⟩
      exact h1
    · intro h1
      exact ⟨h1, by omega⟩
  rw [hint, card_val_lt (a + k) hx, card_val_lt a (by omega)]
  omega

lemma card_arcC {a k : ℕ} (hx : a + k ≤ N) :
    (arcC a k : Finset (Fin N)).card = N - (a + k) := by
  have hcompl : (arcC a k : Finset (Fin N))
      = (Finset.univ.filter fun j : Fin N => j.val < a + k)ᶜ := by
    ext j
    rw [mem_arcC, Finset.mem_compl, Finset.mem_filter]
    constructor
    · intro h hc
      omega
    · intro h
      by_contra hc
      exact h ⟨Finset.mem_univ _, by omega⟩
  rw [hcompl, Finset.card_compl, Fintype.card_fin, card_val_lt (a + k) hx]

lemma arcA_ne_arcB {a k : ℕ} (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcA a : Finset (Fin N)) ≠ arcB a k := by
  intro h
  have h0 : (⟨0, by omega⟩ : Fin N) ∈ (arcA a : Finset (Fin N)) := mem_arcA.2 ha
  rw [h, mem_arcB] at h0
  have h1 : a ≤ 0 := h0.1
  omega

lemma arcA_ne_arcC {a k : ℕ} (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcA a : Finset (Fin N)) ≠ arcC a k := by
  intro h
  have h0 : (⟨0, by omega⟩ : Fin N) ∈ (arcA a : Finset (Fin N)) := mem_arcA.2 ha
  rw [h, mem_arcC] at h0
  have h1 : a + k ≤ 0 := h0
  omega

lemma arcB_ne_arcC {a k : ℕ} (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcB a k : Finset (Fin N)) ≠ arcC a k := by
  intro h
  have h0 : (⟨a, by omega⟩ : Fin N) ∈ (arcB a k : Finset (Fin N)) :=
    mem_arcB.2 ⟨le_refl a, show a < a + k by omega⟩
  rw [h, mem_arcC] at h0
  have h1 : a + k ≤ a := h0
  omega

/-- **The three-arc partition**: outputs `[0,a)`, inputs `[a,a+k)`, both `[a+k,N)`. -/
noncomputable def threeArc (a k : ℕ) (ha : 0 < a) (hk : 2 ≤ k)
    (hsum : a + k + k = N) : SysPartition N Finset.univ where
  parts := {arcA a, arcB a k, arcC a k}
  dir p := if p = arcA a then Dir.outputs
    else if p = arcB a k then Dir.inputs else Dir.both
  parts_nonempty := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨⟨0, by omega⟩, mem_arcA.2 ha⟩
    · exact ⟨⟨a, by omega⟩, mem_arcB.2 ⟨le_refl a, show a < a + k by omega⟩⟩
    · exact ⟨⟨a + k, by omega⟩, mem_arcC.2 (le_refl _)⟩
  parts_subset := fun p _ => p.subset_univ
  parts_disjoint := by
    intro p hp q hq hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rw [Finset.disjoint_left]
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | (intro x hx hx'
           first
             | (rw [mem_arcA] at hx; rw [mem_arcB] at hx'; omega)
             | (rw [mem_arcA] at hx; rw [mem_arcC] at hx'; omega)
             | (rw [mem_arcB] at hx; rw [mem_arcA] at hx'; omega)
             | (rw [mem_arcB] at hx; rw [mem_arcC] at hx'; omega)
             | (rw [mem_arcC] at hx; rw [mem_arcA] at hx'; omega)
             | (rw [mem_arcC] at hx; rw [mem_arcB] at hx'; omega))
  parts_cover := by
    intro i _
    by_cases h1 : i.val < a
    · exact ⟨arcA a, by simp, mem_arcA.2 h1⟩
    by_cases h2 : i.val < a + k
    · exact ⟨arcB a k, by simp, mem_arcB.2 ⟨by omega, h2⟩⟩
    · exact ⟨arcC a k, by simp, mem_arcC.2 (by omega)⟩
  two_le := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨arcA_ne_arcB ha hk hsum, arcA_ne_arcC ha hk hsum⟩),
      Finset.card_insert_of_notMem (by
        simpa using arcB_ne_arcC ha hk hsum),
      Finset.card_singleton]
    omega

variable {a k : ℕ}

lemma threeArc_dir_A (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).dir (arcA a) = Dir.outputs := by
  unfold threeArc
  simp

lemma threeArc_dir_B (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).dir (arcB a k) = Dir.inputs := by
  unfold threeArc
  simp [Ne.symm (arcA_ne_arcB ha hk hsum)]

lemma threeArc_dir_C (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).dir (arcC a k) = Dir.both := by
  unfold threeArc
  simp [Ne.symm (arcA_ne_arcC ha hk hsum), Ne.symm (arcB_ne_arcC ha hk hsum)]

lemma threeArc_mem_parts_A (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcA a : Finset (Fin N)) ∈ (threeArc a k ha hk hsum).parts := by
  unfold threeArc
  simp

lemma threeArc_mem_parts_B (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcB a k : Finset (Fin N)) ∈ (threeArc a k ha hk hsum).parts := by
  unfold threeArc
  simp

lemma threeArc_mem_parts_C (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (arcC a k : Finset (Fin N)) ∈ (threeArc a k ha hk hsum).parts := by
  unfold threeArc
  simp

/-- The outputs arc is cut only from the `both` arc. -/
lemma threeArc_cutSet_A (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).cutSet (arcA a) = arcC a k := by
  rw [SysPartition.cutSet, threeArc_dir_A]
  have hfil : ((threeArc a k ha hk hsum).parts.filter
      fun r => r ≠ arcA a ∧
        ((threeArc a k ha hk hsum).dir r = Dir.outputs ∨
          (threeArc a k ha hk hsum).dir r = Dir.both))
      = {arcC a k} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hrA, hd⟩
      have hpts : (threeArc a k ha hk hsum).parts
          = {arcA a, arcB a k, arcC a k} := rfl
      rw [hpts] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact absurd rfl hrA
      · rw [threeArc_dir_B ha hk hsum] at hd
        rcases hd with h | h <;> exact absurd h (by decide)
      · rfl
    · rintro rfl
      exact ⟨threeArc_mem_parts_C ha hk hsum,
        Ne.symm (arcA_ne_arcC ha hk hsum),
        Or.inr (threeArc_dir_C ha hk hsum)⟩
  rw [hfil, Finset.sup_singleton, id]

lemma threeArc_cutSet_B (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).cutSet (arcB a k) = (arcB a k : Finset (Fin N))ᶜ :=
  cutSet_eq_compl_of_dir _ (Or.inl (threeArc_dir_B ha hk hsum))

lemma threeArc_cutSet_C (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    (threeArc a k ha hk hsum).cutSet (arcC a k) = (arcC a k : Finset (Fin N))ᶜ :=
  cutSet_eq_compl_of_dir _ (Or.inr (threeArc_dir_C ha hk hsum))

/-- Forward shifts that stay below `N` do not wrap. -/
lemma shift_val_of_lt {j : Fin N} (h : j.val + 1 < N) : (shift j).val = j.val + 1 := by
  rw [shift_val, Nat.mod_eq_of_lt h]

/-- **Damage is confined to the four end units.**  Every other unit shifts forward twice
without leaving its own safe zone, and no wrap-around ever occurs for them. -/
theorem damaged_threeArc_subset (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    damaged (threeArc a k ha hk hsum) ⊆
      ({⟨a + k - 2, by omega⟩, ⟨a + k - 1, by omega⟩,
        ⟨N - 2, by omega⟩, ⟨N - 1, by omega⟩} : Finset (Fin N)) := by
  intro j hj
  obtain ⟨-, hdam⟩ := Finset.mem_filter.1 hj
  obtain ⟨x, hxl, hxc⟩ := hdam
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : j.val < a
  · -- the outputs arc is never damaged
    exfalso
    have hpj : (threeArc a k ha hk hsum).partOf j = arcA a :=
      SysPartition.partOf_eq _ (threeArc_mem_parts_A ha hk hsum) (mem_arcA.2 h1)
    rw [hpj, threeArc_cutSet_A ha hk hsum, mem_arcC] at hxc
    have hs1 : (shift j).val = j.val + 1 := shift_val_of_lt (by omega)
    rcases mem_liveInputs.1 hxl with rfl | rfl
    · rw [hs1] at hxc
      omega
    · have hs2 : (shift (shift j)).val = j.val + 2 := by
        rw [shift_val_of_lt (by rw [hs1]; omega), hs1]
      rw [hs2] at hxc
      omega
  by_cases h2 : j.val < a + k
  · -- the inputs arc is damaged only at its last two units
    have hpj : (threeArc a k ha hk hsum).partOf j = arcB a k :=
      SysPartition.partOf_eq _ (threeArc_mem_parts_B ha hk hsum)
        (mem_arcB.2 ⟨by omega, h2⟩)
    rw [hpj, threeArc_cutSet_B ha hk hsum, Finset.mem_compl, mem_arcB] at hxc
    push_neg at hxc
    by_cases h3 : j.val + 2 < a + k
    · exfalso
      have hs1 : (shift j).val = j.val + 1 := shift_val_of_lt (by omega)
      rcases mem_liveInputs.1 hxl with rfl | rfl
      · rw [hs1] at hxc
        omega
      · have hs2 : (shift (shift j)).val = j.val + 2 := by
          rw [shift_val_of_lt (by rw [hs1]; omega), hs1]
        rw [hs2] at hxc
        omega
    · have hval : j.val = a + k - 2 ∨ j.val = a + k - 1 := by omega
      rcases hval with h | h
      · exact Or.inl (Fin.ext (by simpa using h))
      · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · -- the both arc is damaged only at its last two units
    have hpj : (threeArc a k ha hk hsum).partOf j = arcC a k :=
      SysPartition.partOf_eq _ (threeArc_mem_parts_C ha hk hsum)
        (mem_arcC.2 (by omega))
    rw [hpj, threeArc_cutSet_C ha hk hsum, Finset.mem_compl, mem_arcC] at hxc
    by_cases h3 : j.val + 2 < N
    · exfalso
      have hs1 : (shift j).val = j.val + 1 := shift_val_of_lt (by omega)
      rcases mem_liveInputs.1 hxl with rfl | rfl
      · rw [hs1] at hxc
        omega
      · have hs2 : (shift (shift j)).val = j.val + 2 := by
          rw [shift_val_of_lt (by rw [hs1]; omega), hs1]
        rw [hs2] at hxc
        omega
    · have hjlt := j.isLt
      have hval : j.val = N - 2 ∨ j.val = N - 1 := by omega
      rcases hval with h | h
      · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using h))))

/-- **The witness damages at most four units.** -/
theorem damagedCount_threeArc_le (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    damagedCount (threeArc a k ha hk hsum) ≤ 4 := by
  refine le_trans (Finset.card_le_card (damaged_threeArc_subset ha hk hsum)) ?_
  calc ({⟨a + k - 2, by omega⟩, ⟨a + k - 1, by omega⟩,
        ⟨N - 2, by omega⟩, ⟨N - 1, by omega⟩} : Finset (Fin N)).card
      ≤ ({⟨a + k - 1, by omega⟩, ⟨N - 2, by omega⟩,
          ⟨N - 1, by omega⟩} : Finset (Fin N)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({⟨N - 2, by omega⟩, ⟨N - 1, by omega⟩} : Finset (Fin N)).card + 1) + 1 := by
        have := Finset.card_insert_le (⟨a + k - 1, by omega⟩ : Fin N)
          ({⟨N - 2, by omega⟩, ⟨N - 1, by omega⟩} : Finset (Fin N))
        omega
    _ ≤ ((({⟨N - 1, by omega⟩} : Finset (Fin N)).card + 1) + 1) + 1 := by
        have := Finset.card_insert_le (⟨N - 2, by omega⟩ : Fin N)
          ({⟨N - 1, by omega⟩} : Finset (Fin N))
        omega
    _ = 4 := by rw [Finset.card_singleton]

/-- **The witness's normalizer, in closed form.** -/
theorem sysCutCount_threeArc (ha : 0 < a) (hk : 2 ≤ k) (hsum : a + k + k = N) :
    sysCutCount (threeArc a k ha hk hsum) = a * k + k * (N - k) + k * (N - k) := by
  have hAB : (arcA a : Finset (Fin N)) ∉
      ({arcB a k, arcC a k} : Finset (Finset (Fin N))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨arcA_ne_arcB ha hk hsum, arcA_ne_arcC ha hk hsum⟩
  have hBC : (arcB a k : Finset (Fin N)) ∉
      ({arcC a k} : Finset (Finset (Fin N))) := by
    simpa using arcB_ne_arcC ha hk hsum
  have hparts : (threeArc a k ha hk hsum).parts
      = {arcA a, arcB a k, arcC a k} := rfl
  rw [sysCutCount, hparts, Finset.sum_insert hAB, Finset.sum_insert hBC,
    Finset.sum_singleton, threeArc_cutSet_A ha hk hsum, threeArc_cutSet_B ha hk hsum,
    threeArc_cutSet_C ha hk hsum, Finset.card_compl, Finset.card_compl,
    Fintype.card_fin, card_arcA (by omega), card_arcB (by omega : a + k ≤ N),
    card_arcC (by omega : a + k ≤ N)]
  have h1 : N - (a + k) = k := by omega
  rw [h1]
  ring

end Witness

end IIT
