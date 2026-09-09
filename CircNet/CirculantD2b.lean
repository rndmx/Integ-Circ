/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD2

/-!
# The `D = 2` classification, case of two inputs blocks

A partition damaging exactly two units, with **two** blocks severing their inputs, is
forced into the same shape as the `D = 1` classification doubled: both blocks are
singletons, every other block severs its outputs and is undamaged, at most one such block
exists, and the normalizer is exactly `2(N-1)`.

The `both` direction is ruled out by a two-step backward chase: the predecessor of a
`both` singleton must lie in an outputs block (damaging it) or be the other singleton, and
in the latter case the predecessor of *that* is trapped on all sides.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section CaseTwo

variable [NeZero N]

/-- Blocks with distinct directions are distinct. -/
lemma ne_of_dir_ne (θ : SysPartition N Finset.univ) {p q : Finset (Fin N)}
    (h : θ.dir p ≠ θ.dir q) : p ≠ q := fun he => h (he ▸ rfl)

/-- A direction that is not `outputs` severs its inputs. -/
lemma dir_io_of_ne_outputs (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (h : θ.dir p ≠ Dir.outputs) : θ.dir p = Dir.inputs ∨ θ.dir p = Dir.both := by
  cases hd : θ.dir p
  · exact Or.inl rfl
  · exact absurd hd h
  · exact Or.inr rfl

/-- **A `both` singleton is impossible** beside a second inputs-severing singleton when
every outputs block is undamaged: walking back from it, the predecessor damages an
outputs block or is the other singleton, whose own predecessor is trapped on all sides. -/
private lemma both_singleton_impossible (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hzero : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs → ∀ j ∈ q, ¬ Damaged θ j)
    {a b : Fin N} (hpa : ({a} : Finset (Fin N)) ∈ θ.parts)
    (hpb : ({b} : Finset (Fin N)) ∈ θ.parts) (hab : a ≠ b)
    (hthird : ∀ r ∈ θ.parts, r ≠ ({a} : Finset (Fin N)) →
      r ≠ ({b} : Finset (Fin N)) → θ.dir r = Dir.outputs)
    (hda : θ.dir ({a} : Finset (Fin N)) = Dir.both) : False := by
  classical
  -- first step back from `a`
  have hu : shift (pred a) = a := shift_pred a
  obtain ⟨r, hr, hur⟩ := θ.parts_cover (pred a) (Finset.mem_univ (pred a))
  have hra : r ≠ ({a} : Finset (Fin N)) := by
    rintro rfl
    rw [Finset.mem_singleton] at hur
    rw [hur] at hu
    exact shift_ne_self hN a hu
  by_cases hrout : θ.dir r = Dir.outputs
  · exact hzero r hr hrout (pred a) hur
      ⟨shift (pred a), mem_liveInputs.2 (Or.inl rfl), by
        rw [θ.partOf_eq hr hur, hu]
        exact mem_cutSet_of_mem_both θ hpa (Ne.symm hra) hda hrout (Finset.mem_singleton_self a)⟩
  · -- `r` must be `{b}`, so `shift b = a`
    have hrb : r = ({b} : Finset (Fin N)) := by
      by_contra hrb
      exact hrout (hthird r hr hra hrb)
    subst hrb
    rw [Finset.mem_singleton] at hur
    have hba : shift b = a := by rw [← hur]; exact hu
    -- second step back, from `b`
    have hv : shift (pred b) = b := shift_pred b
    obtain ⟨r', hr', hvr'⟩ := θ.parts_cover (pred b) (Finset.mem_univ (pred b))
    have hr'b : r' ≠ ({b} : Finset (Fin N)) := by
      rintro rfl
      rw [Finset.mem_singleton] at hvr'
      rw [hvr'] at hv
      exact shift_ne_self hN b hv
    have hr'a : r' ≠ ({a} : Finset (Fin N)) := by
      rintro rfl
      rw [Finset.mem_singleton] at hvr'
      -- then `shift a = b` and `shift b = a`, so `shift (shift b) = b`
      have hab' : shift a = b := by rw [← hvr']; exact hv
      exact shift_shift_ne_self hN b (by rw [hba, hab'])
    by_cases hr'out : θ.dir r' = Dir.outputs
    · refine hzero r' hr' hr'out (pred b) hvr'
        ⟨shift (shift (pred b)), mem_liveInputs.2 (Or.inr rfl), ?_⟩
      rw [θ.partOf_eq hr' hvr', hv, hba]
      exact mem_cutSet_of_mem_both θ hpa (Ne.symm hr'a) hda hr'out (Finset.mem_singleton_self a)
    · exact hr'out (hthird r' hr' hr'a hr'b)

/-- **Case `|I| = 2` of the `D = 2` classification**: the normalizer is exactly
`2(N-1)`. -/
theorem sysCutCount_of_two_inputs (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 2) {p₀ p₁ : Finset (Fin N)}
    (hp₀ : p₀ ∈ θ.parts) (hp₁ : p₁ ∈ θ.parts) (hne : p₀ ≠ p₁)
    (hd₀ : θ.dir p₀ ≠ Dir.outputs) (hd₁ : θ.dir p₁ ≠ Dir.outputs) :
    sysCutCount θ = 2 * (N - 1) := by
  classical
  have hcut₀ : θ.cutSet p₀ = p₀ᶜ := cutSet_eq_compl_of_dir θ (dir_io_of_ne_outputs θ hd₀)
  have hcut₁ : θ.cutSet p₁ = p₁ᶜ := cutSet_eq_compl_of_dir θ (dir_io_of_ne_outputs θ hd₁)
  -- no third block severing its inputs
  have hthird : ∀ r ∈ θ.parts, r ≠ p₀ → r ≠ p₁ → θ.dir r = Dir.outputs := by
    intro r hr hr₀ hr₁
    by_contra hdr
    have hcutr : θ.cutSet r = rᶜ := cutSet_eq_compl_of_dir θ (dir_io_of_ne_outputs θ hdr)
    have hsub : ({p₀, p₁, r} : Finset (Finset (Fin N))) ⊆ θ.parts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hle := card_le_damagedCount_of_forall_compl θ hsub (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    rw [Finset.card_insert_of_notMem (by simp [hne, Ne.symm hr₀]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hr₁]),
      Finset.card_singleton, hD] at hle
    omega
  -- both blocks are singletons
  have hsingle : ∀ p ∈ θ.parts, θ.cutSet p = pᶜ →
      (∃ q, q ∈ θ.parts ∧ q ≠ p ∧ θ.cutSet q = qᶜ) → p.card = 1 := by
    rintro p hp hcp ⟨q, hq, hqp, hcq⟩
    by_contra hone
    have h2 : 2 ≤ p.card := by
      have := Finset.card_pos.2 (θ.parts_nonempty p hp)
      omega
    obtain ⟨j₁, hj₁, j₂, hj₂, hj12, hda1, hda2⟩ :=
      two_le_damaged_of_cutSet_compl θ hp hcp h2
    obtain ⟨j₃, hj₃, hda3⟩ := exists_damaged_of_cutSet_compl θ hq hcq
    have hdisj : Disjoint q p := θ.parts_disjoint q hq p hp hqp
    have h13 : j₁ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj hj₃ (h ▸ hj₁)
    have h23 : j₂ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj hj₃ (h ▸ hj₂)
    have := three_le_damagedCount θ hj12 h13 h23 hda1 hda2 hda3
    omega
  have hcard₀ : p₀.card = 1 := hsingle p₀ hp₀ hcut₀ ⟨p₁, hp₁, Ne.symm hne, hcut₁⟩
  have hcard₁ : p₁.card = 1 := hsingle p₁ hp₁ hcut₁ ⟨p₀, hp₀, hne, hcut₀⟩
  obtain ⟨b₀, hb₀⟩ := Finset.card_eq_one.1 hcard₀
  obtain ⟨b₁, hb₁⟩ := Finset.card_eq_one.1 hcard₁
  subst hb₀
  subst hb₁
  have hbne : b₀ ≠ b₁ := fun h => hne (by rw [h])
  have hdam₀ : Damaged θ b₀ := singleton_damaged hN θ hp₀ hcut₀
  have hdam₁ : Damaged θ b₁ := singleton_damaged hN θ hp₁ hcut₁
  -- blocks severing outputs are undamaged
  have hzero : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs → ∀ j ∈ q, ¬ Damaged θ j := by
    intro q hq hdq j hj hdam
    have hq₀ : q ≠ ({b₀} : Finset (Fin N)) :=
      ne_of_dir_ne θ (by rw [hdq]; exact fun h => hd₀ h.symm)
    have hq₁ : q ≠ ({b₁} : Finset (Fin N)) :=
      ne_of_dir_ne θ (by rw [hdq]; exact fun h => hd₁ h.symm)
    have hj₀ : b₀ ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hq _ hp₀ hq₀) hj
        (Finset.mem_singleton_self _)
    have hj₁ : b₁ ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hq _ hp₁ hq₁) hj
        (Finset.mem_singleton_self _)
    have := three_le_damagedCount θ hbne hj₀ hj₁ hdam₀ hdam₁ hdam
    omega
  -- both singletons sever their inputs
  have hdir₀ : θ.dir ({b₀} : Finset (Fin N)) = Dir.inputs := by
    rcases dir_io_of_ne_outputs θ hd₀ with h | h
    · exact h
    · exact absurd (both_singleton_impossible hN θ hzero hp₀ hp₁ hbne hthird h) id
  have hdir₁ : θ.dir ({b₁} : Finset (Fin N)) = Dir.inputs := by
    rcases dir_io_of_ne_outputs θ hd₁ with h | h
    · exact h
    · refine absurd (both_singleton_impossible hN θ hzero hp₁ hp₀ (Ne.symm hbne) ?_ h) id
      intro r hr hrb₁ hrb₀
      exact hthird r hr hrb₀ hrb₁
  -- a block severing outputs exists
  obtain ⟨q, hq, hdq⟩ : ∃ q, q ∈ θ.parts ∧ θ.dir q = Dir.outputs := by
    by_contra hc
    push_neg at hc
    have hsub : ∀ x : Fin N, x ∈ ({b₀} : Finset (Fin N)) ∪ {b₁} := by
      intro x
      obtain ⟨r, hr, hxr⟩ := θ.parts_cover x (Finset.mem_univ x)
      by_cases h0 : r = ({b₀} : Finset (Fin N))
      · subst h0; exact Finset.mem_union_left _ hxr
      by_cases h1 : r = ({b₁} : Finset (Fin N))
      · subst h1; exact Finset.mem_union_right _ hxr
      · exact absurd (hthird r hr h0 h1) (hc r hr)
    have hle : (Finset.univ : Finset (Fin N)).card ≤
        (({b₀} : Finset (Fin N)) ∪ {b₁}).card :=
      Finset.card_le_card fun x _ => hsub x
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have hcu := Finset.card_union_le ({b₀} : Finset (Fin N)) ({b₁} : Finset (Fin N))
    simp only [Finset.card_singleton] at hcu
    omega
  -- at most one block severing outputs
  have huniq : ∀ q' ∈ θ.parts, θ.dir q' = Dir.outputs → q' = q := by
    intro q₂ hq₂ hdq₂
    by_contra hq2q
    -- trap both ways
    obtain ⟨x, hx⟩ := θ.parts_nonempty q hq
    obtain ⟨x₂, hx₂⟩ := θ.parts_nonempty q₂ hq₂
    obtain ⟨j₁, hj₁, hj₁o, hj₁o2, hav₁⟩ :=
      trap_of_zero_damage θ hq₂ hdq₂ (hzero q₂ hq₂ hdq₂) hq (Ne.symm hq2q) hdq hx
    obtain ⟨j₂, hj₂, hj₂o, hj₂o2, hav₂⟩ :=
      trap_of_zero_damage θ hq hdq (hzero q hq hdq) hq₂ hq2q hdq₂ hx₂
    -- both steps of each trapped walk land in `{b₀, b₁}`
    have hland : ∀ y : Fin N, (∀ r ∈ θ.parts, r ≠ q₂ →
        (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) → y ∉ r) → y ∉ q₂ →
        y = b₀ ∨ y = b₁ := by
      intro y hy hyq
      obtain ⟨r, hr, hyr⟩ := θ.parts_cover y (Finset.mem_univ y)
      by_cases h0 : r = ({b₀} : Finset (Fin N))
      · subst h0; rw [Finset.mem_singleton] at hyr; exact Or.inl hyr
      by_cases h1 : r = ({b₁} : Finset (Fin N))
      · subst h1; rw [Finset.mem_singleton] at hyr; exact Or.inr hyr
      · have hrq₂ : r ≠ q₂ := by
          rintro rfl
          exact hyq hyr
        exact absurd hyr (hy r hr hrq₂ (Or.inl (hthird r hr h0 h1)))
    have hland2 : ∀ y : Fin N, (∀ r ∈ θ.parts, r ≠ q →
        (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) → y ∉ r) → y ∉ q →
        y = b₀ ∨ y = b₁ := by
      intro y hy hyq
      obtain ⟨r, hr, hyr⟩ := θ.parts_cover y (Finset.mem_univ y)
      by_cases h0 : r = ({b₀} : Finset (Fin N))
      · subst h0; rw [Finset.mem_singleton] at hyr; exact Or.inl hyr
      by_cases h1 : r = ({b₁} : Finset (Fin N))
      · subst h1; rw [Finset.mem_singleton] at hyr; exact Or.inr hyr
      · have hrq : r ≠ q := by
          rintro rfl
          exact hyq hyr
        exact absurd hyr (hy r hr hrq (Or.inl (hthird r hr h0 h1)))
    have hs₁ : shift j₁ = b₀ ∨ shift j₁ = b₁ :=
      hland _ (fun r hr hrq hd => (hav₁ r hr hrq hd).1) hj₁o
    have hs₁' : shift (shift j₁) = b₀ ∨ shift (shift j₁) = b₁ :=
      hland _ (fun r hr hrq hd => (hav₁ r hr hrq hd).2) hj₁o2
    have hs₂ : shift j₂ = b₀ ∨ shift j₂ = b₁ :=
      hland2 _ (fun r hr hrq hd => (hav₂ r hr hrq hd).1) hj₂o
    have hs₂' : shift (shift j₂) = b₀ ∨ shift (shift j₂) = b₁ :=
      hland2 _ (fun r hr hrq hd => (hav₂ r hr hrq hd).2) hj₂o2
    -- the two steps of one walk are distinct, and the first steps of the two walks are
    have hstep_ne : ∀ y : Fin N, shift y ≠ shift (shift y) := by
      intro y h
      exact shift_ne_self hN y (shift_injective h).symm
    have hj₁₂ : j₁ ≠ j₂ := by
      rintro rfl
      exact Finset.disjoint_left.1 (θ.parts_disjoint q₂ hq₂ q hq hq2q) hj₁ hj₂
    have hsj₁₂ : shift j₁ ≠ shift j₂ := fun h => hj₁₂ (shift_injective h)
    -- extract the two cyclic equations and contradict
    rcases hs₁ with h₁ | h₁
    · have h₁' : shift (shift j₁) = b₁ := by
        rcases hs₁' with h | h
        · exact absurd (h₁.trans h.symm) (hstep_ne j₁)
        · exact h
      have hba : shift b₀ = b₁ := by rw [← h₁]; exact h₁'
      have h₂ : shift j₂ = b₁ := by
        rcases hs₂ with h | h
        · exact absurd (h₁.trans h.symm) hsj₁₂
        · exact h
      have h₂' : shift (shift j₂) = b₀ := by
        rcases hs₂' with h | h
        · exact h
        · exact absurd (h₂.trans h.symm) (hstep_ne j₂)
      have hab : shift b₁ = b₀ := by rw [← h₂]; exact h₂'
      exact shift_shift_ne_self hN b₀ (by rw [hba, hab])
    · have h₁' : shift (shift j₁) = b₀ := by
        rcases hs₁' with h | h
        · exact h
        · exact absurd (h₁.trans h.symm) (hstep_ne j₁)
      have hab : shift b₁ = b₀ := by rw [← h₁]; exact h₁'
      have h₂ : shift j₂ = b₀ := by
        rcases hs₂ with h | h
        · exact h
        · exact absurd (h₁.trans h.symm) hsj₁₂
      have h₂' : shift (shift j₂) = b₁ := by
        rcases hs₂' with h | h
        · exact absurd (h₂.trans h.symm) (hstep_ne j₂)
        · exact h
      have hba : shift b₀ = b₁ := by rw [← h₂]; exact h₂'
      exact shift_shift_ne_self hN b₀ (by rw [hba, hab])
  -- the parts are exactly the two singletons and `q`
  have hqb₀ : q ≠ ({b₀} : Finset (Fin N)) :=
    ne_of_dir_ne θ (by rw [hdq]; exact fun h => hd₀ h.symm)
  have hqb₁ : q ≠ ({b₁} : Finset (Fin N)) :=
    ne_of_dir_ne θ (by rw [hdq]; exact fun h => hd₁ h.symm)
  have hparts : θ.parts = {({b₀} : Finset (Fin N)), {b₁}, q} := by
    apply Finset.Subset.antisymm
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : r = ({b₀} : Finset (Fin N))
      · exact Or.inl h0
      by_cases h1 : r = ({b₁} : Finset (Fin N))
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (huniq r hr (hthird r hr h0 h1)))
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> assumption
  -- the outputs block's cut set is empty
  have hcutq : θ.cutSet q = ∅ := by
    rw [SysPartition.cutSet, hdq]
    have hfil : (θ.parts.filter
        fun r => r ≠ q ∧ (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr
      rw [hparts] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rintro ⟨-, hd⟩
        rw [hdir₀] at hd
        rcases hd with h | h <;> exact absurd h (by decide)
      · rintro ⟨-, hd⟩
        rw [hdir₁] at hd
        rcases hd with h | h <;> exact absurd h (by decide)
      · rintro ⟨hne', -⟩
        exact hne' rfl
    rw [hfil]
    exact Finset.sup_empty
  -- assemble the normalizer
  have hb₀q : ({b₀} : Finset (Fin N)) ∉ ({({b₁} : Finset (Fin N)), q} : Finset (Finset (Fin N))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨by simpa using hbne, Ne.symm hqb₀⟩
  have hb₁q : ({b₁} : Finset (Fin N)) ∉ ({q} : Finset (Finset (Fin N))) := by
    simpa using Ne.symm hqb₁
  rw [sysCutCount, hparts, Finset.sum_insert hb₀q, Finset.sum_insert hb₁q,
    Finset.sum_singleton, hcutq, Finset.card_empty, hcut₀, hcut₁, Finset.card_compl,
    Finset.card_compl, Fintype.card_fin, Finset.card_singleton, Finset.card_singleton,
    mul_zero, add_zero]
  omega

end CaseTwo

end IIT
