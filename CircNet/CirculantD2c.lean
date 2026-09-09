/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD2b

/-!
# The `D = 2` classification, case of a unique inputs block

A partition damaging exactly two units whose **only** block severing its inputs is `p₀`
forces: `p₀` has at least two units and absorbs the whole damage budget, `p₀` severs its
inputs (not both directions), and exactly one outputs block exists, with empty cut set.
The normalizer is then `|p₀| · |p₀ᶜ|`, which `card_mul_compl_le` caps at `N²/4`.

The two-outputs case dies on the exact damage count: each trapped walk enters `p₀`
twice in a row, so either some unit of `p₀` keeps its successor inside `p₀` -- impossible
when `preExitSet p₀ = ∅` -- or `p₀` has a single entry point, which two disjoint walks
cannot share.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section CaseOne

variable [NeZero N]

/-- **Case `|I| = 1` of the `D = 2` classification**: the normalizer is exactly
`|p₀| · |p₀ᶜ|`. -/
theorem sysCutCount_of_unique_inputs (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 2) {p₀ : Finset (Fin N)}
    (hp₀ : p₀ ∈ θ.parts) (hd₀ : θ.dir p₀ ≠ Dir.outputs)
    (huni : ∀ r ∈ θ.parts, r ≠ p₀ → θ.dir r = Dir.outputs) :
    sysCutCount θ = p₀.card * p₀ᶜ.card := by
  classical
  have hcut₀ : θ.cutSet p₀ = p₀ᶜ := cutSet_eq_compl_of_dir θ (dir_io_of_ne_outputs θ hd₀)
  have hne_univ : p₀ ≠ Finset.univ := block_ne_univ θ hp₀
  -- an outputs block exists
  obtain ⟨q₀, hq₀, hq₀p, hdq₀⟩ : ∃ q, q ∈ θ.parts ∧ q ≠ p₀ ∧ θ.dir q = Dir.outputs := by
    obtain ⟨r, hr, hrp⟩ : ∃ r ∈ θ.parts, r ≠ p₀ := by
      by_contra hc
      push_neg at hc
      have hsub : θ.parts ⊆ {p₀} := fun x hx => Finset.mem_singleton.2 (hc x hx)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      have := θ.two_le
      omega
    exact ⟨r, hr, hrp, huni r hr hrp⟩
  -- `p₀` has at least two units
  have hcard₀ : 2 ≤ p₀.card := by
    by_contra hone
    have h1 : p₀.card = 1 := by
      have := Finset.card_pos.2 (θ.parts_nonempty p₀ hp₀)
      omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
    subst hb
    have hdamb : Damaged θ b := singleton_damaged hN θ hp₀ hcut₀
    -- both direction: the two-step backward chase damages two outputs units
    rcases dir_io_of_ne_outputs θ hd₀ with hin | hboth
    · -- inputs direction
      -- outputs damage: at most one damaged unit outside `{b}`
      -- if two outputs blocks exist, one is undamaged; trap it: both steps must land in
      -- `{b}`, which is impossible
      by_cases htwo : ∃ q₁, q₁ ∈ θ.parts ∧ q₁ ≠ ({b} : Finset (Fin N)) ∧ q₁ ≠ q₀
      · obtain ⟨q₁, hq₁, hq₁p, hq₁q₀⟩ := htwo
        have hdq₁ : θ.dir q₁ = Dir.outputs := huni q₁ hq₁ hq₁p
        -- at least one of `q₀, q₁` is undamaged
        have htrap : ∀ qa qb : Finset (Fin N), qa ∈ θ.parts → qb ∈ θ.parts →
            qa ≠ qb → θ.dir qa = Dir.outputs → θ.dir qb = Dir.outputs →
            (∀ j ∈ qa, ¬ Damaged θ j) → False := by
          intro qa qb hqa hqb hab hda hdb hzeroa
          obtain ⟨x, hx⟩ := θ.parts_nonempty qb hqb
          obtain ⟨j, hj, hjo, hjo2, hav⟩ :=
            trap_of_zero_damage θ hqa hda hzeroa hqb (Ne.symm hab) hdb hx
          have hland : ∀ y : Fin N, (∀ r ∈ θ.parts, r ≠ qa →
              (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) → y ∉ r) → y ∉ qa →
              y = b := by
            intro y hy hyq
            obtain ⟨r, hr, hyr⟩ := θ.parts_cover y (Finset.mem_univ y)
            by_cases h0 : r = ({b} : Finset (Fin N))
            · subst h0
              rw [Finset.mem_singleton] at hyr
              exact hyr
            · have hrq : r ≠ qa := by
                rintro rfl
                exact hyq hyr
              exact absurd hyr (hy r hr hrq (Or.inl (huni r hr h0)))
          have h1 : shift j = b :=
            hland _ (fun r hr hrq hd => (hav r hr hrq hd).1) hjo
          have h2 : shift (shift j) = b :=
            hland _ (fun r hr hrq hd => (hav r hr hrq hd).2) hjo2
          exact shift_ne_self hN j (shift_injective (h2.trans h1.symm))
        by_cases hz₀ : ∀ j ∈ q₀, ¬ Damaged θ j
        · exact htrap q₀ q₁ hq₀ hq₁ (Ne.symm hq₁q₀) hdq₀ hdq₁ hz₀
        · push_neg at hz₀
          obtain ⟨u, hu, hudam⟩ := hz₀
          have hz₁ : ∀ j ∈ q₁, ¬ Damaged θ j := by
            intro j hj hdam
            have hub : u ≠ b := by
              rintro rfl
              exact Finset.disjoint_left.1
                (θ.parts_disjoint q₀ hq₀ _ hp₀ hq₀p) hu (Finset.mem_singleton_self _)
            have hjb : j ≠ b := by
              rintro rfl
              exact Finset.disjoint_left.1
                (θ.parts_disjoint q₁ hq₁ _ hp₀ hq₁p) hj (Finset.mem_singleton_self _)
            have hju : j ≠ u := by
              rintro rfl
              exact Finset.disjoint_left.1
                (θ.parts_disjoint q₁ hq₁ q₀ hq₀ hq₁q₀) hj hu
            have := three_le_damagedCount θ (Ne.symm hub) (Ne.symm hjb) (Ne.symm hju)
              hdamb hudam hdam
            omega
          exact htrap q₁ q₀ hq₁ hq₀ hq₁q₀ hdq₁ hdq₀ hz₁
      · -- a single outputs block: its cut set is empty, so nothing else is damaged
        push_neg at htwo
        have hcutq : θ.cutSet q₀ = ∅ := by
          rw [SysPartition.cutSet, hdq₀]
          have hfil : (θ.parts.filter
              fun r => r ≠ q₀ ∧ (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both)) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro r hr
            rintro ⟨hrq, hd⟩
            by_cases h0 : r = ({b} : Finset (Fin N))
            · subst h0
              rw [hin] at hd
              rcases hd with h | h <;> exact absurd h (by decide)
            · exact hrq (htwo r hr h0)
          rw [hfil]
          exact Finset.sup_empty
        -- the damage count is then one, not two
        have hdameq : damaged θ = {b} := by
          apply Finset.Subset.antisymm
          · intro j hj
            obtain ⟨hju, hjdam⟩ := Finset.mem_filter.1 hj
            obtain ⟨r, hr, hjr⟩ := θ.parts_cover j (Finset.mem_univ j)
            by_cases h0 : r = ({b} : Finset (Fin N))
            · subst h0
              exact hjr
            · have hrq : r = q₀ := htwo r hr h0
              subst hrq
              obtain ⟨k, hk, hkc⟩ := hjdam
              rw [θ.partOf_eq hr hjr, hcutq] at hkc
              simp at hkc
          · intro j hj
            rw [Finset.mem_singleton] at hj
            subst hj
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hdamb⟩
        rw [damagedCount, hdameq, Finset.card_singleton] at hD
        omega
    · -- both direction: the backward chase gives three damaged units
      have hu : shift (pred b) = b := shift_pred b
      obtain ⟨r, hr, hur⟩ := θ.parts_cover (pred b) (Finset.mem_univ (pred b))
      have hrb : r ≠ ({b} : Finset (Fin N)) := by
        rintro rfl
        rw [Finset.mem_singleton] at hur
        rw [hur] at hu
        exact shift_ne_self hN b hu
      have hdr : θ.dir r = Dir.outputs := huni r hr hrb
      have hudam : Damaged θ (pred b) :=
        ⟨shift (pred b), mem_liveInputs.2 (Or.inl rfl), by
          rw [θ.partOf_eq hr hur, hu]
          exact mem_cutSet_of_mem_both θ hp₀ (Ne.symm hrb) hboth hdr
            (Finset.mem_singleton_self b)⟩
      have hv : shift (pred (pred b)) = pred b := shift_pred (pred b)
      obtain ⟨r', hr', hvr'⟩ := θ.parts_cover (pred (pred b)) (Finset.mem_univ _)
      have hr'b : r' ≠ ({b} : Finset (Fin N)) := by
        rintro rfl
        rw [Finset.mem_singleton] at hvr'
        rw [hvr'] at hv
        -- then `shift b = pred b`, and `shift (pred b) = b` gives `shift (shift b) = b`
        exact shift_shift_ne_self hN b (by rw [hv, hu])
      have hdr' : θ.dir r' = Dir.outputs := huni r' hr' hr'b
      have hwdam : Damaged θ (pred (pred b)) :=
        ⟨shift (shift (pred (pred b))), mem_liveInputs.2 (Or.inr rfl), by
          rw [θ.partOf_eq hr' hvr', hv, hu]
          exact mem_cutSet_of_mem_both θ hp₀ (Ne.symm hr'b) hboth hdr'
            (Finset.mem_singleton_self b)⟩
      have hub : pred b ≠ b := by
        intro h
        rw [h] at hu
        exact shift_ne_self hN b hu
      have hwb : pred (pred b) ≠ b := by
        intro h
        rw [h] at hv
        refine shift_shift_ne_self hN b ?_
        rw [hv]
        exact hu
      have hwu : pred (pred b) ≠ pred b := by
        intro h
        rw [h] at hv
        exact shift_ne_self hN (pred b) hv
      have := three_le_damagedCount θ (Ne.symm hub) (Ne.symm hwb) (Ne.symm hwu)
        hdamb hudam hwdam
      omega
  -- `p₀` absorbs the whole budget
  obtain ⟨j₁, hj₁, j₂, hj₂, hj12, hda1, hda2⟩ :=
    two_le_damaged_of_cutSet_compl θ hp₀ hcut₀ hcard₀
  have hzero : ∀ q ∈ θ.parts, q ≠ p₀ → ∀ j ∈ q, ¬ Damaged θ j := by
    intro q hq hqp j hj hdam
    have hj1 : j₁ ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hq p₀ hp₀ hqp) hj hj₁
    have hj2 : j₂ ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.1 (θ.parts_disjoint q hq p₀ hp₀ hqp) hj hj₂
    have := three_le_damagedCount θ hj12 hj1 hj2 hda1 hda2 hdam
    omega
  -- `p₀` severs its inputs, not both directions
  have hdir₀ : θ.dir p₀ = Dir.inputs := by
    rcases dir_io_of_ne_outputs θ hd₀ with h | h
    · exact h
    · exfalso
      -- any outputs block would be shift-closed, hence everything
      have hcl : ∀ j ∈ q₀, shift j ∈ q₀ := by
        intro j hj
        by_contra hout
        obtain ⟨r, hr, hjr⟩ := θ.parts_cover (shift j) (Finset.mem_univ (shift j))
        have hnotdam := hzero q₀ hq₀ hq₀p j hj
        by_cases h0 : r = p₀
        · subst h0
          exact hnotdam ⟨shift j, mem_liveInputs.2 (Or.inl rfl), by
            rw [θ.partOf_eq hq₀ hj]
            exact mem_cutSet_of_mem_both θ hp₀ (Ne.symm hq₀p) h hdq₀ hjr⟩
        · have hrq : r ≠ q₀ := by
            rintro rfl
            exact hout hjr
          exact hnotdam ⟨shift j, mem_liveInputs.2 (Or.inl rfl), by
            rw [θ.partOf_eq hq₀ hj]
            exact mem_cutSet_of_mem_other θ hr hrq (huni r hr h0) hdq₀ hjr⟩
      exact block_ne_univ θ hq₀ (eq_univ_of_shift_closed (θ.parts_nonempty q₀ hq₀) hcl)
  -- at most one outputs block
  have huniq : ∀ q' ∈ θ.parts, q' ≠ p₀ → q' = q₀ := by
    intro q₁ hq₁ hq₁p
    by_contra hq₁q₀
    have hdq₁ : θ.dir q₁ = Dir.outputs := huni q₁ hq₁ hq₁p
    -- trap both walks; each enters `p₀` twice in a row
    have henter : ∀ qa qb : Finset (Fin N), qa ∈ θ.parts → qb ∈ θ.parts →
        qa ≠ p₀ → qb ≠ p₀ → qa ≠ qb → θ.dir qa = Dir.outputs → θ.dir qb = Dir.outputs →
        ∃ j ∈ qa, shift j ∈ p₀ ∧ shift (shift j) ∈ p₀ := by
      intro qa qb hqa hqb hqap hqbp hab hda hdb
      obtain ⟨x, hx⟩ := θ.parts_nonempty qb hqb
      obtain ⟨j, hj, hjo, hjo2, hav⟩ :=
        trap_of_zero_damage θ hqa hda (hzero qa hqa hqap) hqb (Ne.symm hab) hdb hx
      have hland : ∀ y : Fin N, (∀ r ∈ θ.parts, r ≠ qa →
          (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both) → y ∉ r) → y ∉ qa →
          y ∈ p₀ := by
        intro y hy hyq
        obtain ⟨r, hr, hyr⟩ := θ.parts_cover y (Finset.mem_univ y)
        by_cases h0 : r = p₀
        · subst h0
          exact hyr
        · have hrq : r ≠ qa := by
            rintro rfl
            exact hyq hyr
          exact absurd hyr (hy r hr hrq (Or.inl (huni r hr h0)))
      exact ⟨j, hj,
        hland _ (fun r hr hrq hd => (hav r hr hrq hd).1) hjo,
        hland _ (fun r hr hrq hd => (hav r hr hrq hd).2) hjo2⟩
    obtain ⟨ja, hja, hsja, hsja2⟩ :=
      henter q₀ q₁ hq₀ hq₁ hq₀p hq₁p (Ne.symm hq₁q₀) hdq₀ hdq₁
    obtain ⟨jb, hjb, hsjb, hsjb2⟩ :=
      henter q₁ q₀ hq₁ hq₀ hq₁p hq₀p hq₁q₀ hdq₁ hdq₀
    -- the damage of `p₀` is the whole budget
    have hdamin : damaged θ ∩ p₀ = damaged θ := by
      apply Finset.inter_eq_left.2
      intro j hj
      obtain ⟨hju, hjdam⟩ := Finset.mem_filter.1 hj
      obtain ⟨r, hr, hjr⟩ := θ.parts_cover j (Finset.mem_univ j)
      by_cases h0 : r = p₀
      · subst h0; exact hjr
      · exact absurd hjdam (hzero r hr h0 j hjr)
    have hsum : (exitSet p₀).card + (preExitSet p₀).card = 2 := by
      have hci := card_damaged_inter θ hp₀ hcut₀
      rw [hdamin] at hci
      rw [damagedCount] at hD
      omega
    by_cases hpre : preExitSet p₀ = ∅
    · -- all runs are singletons, yet `shift ja` stays inside
      have := shift_notMem_of_preExit_empty hne_univ hpre (shift ja) hsja
      exact this hsja2
    · -- a single entry point shared by two disjoint walks
      have hexit1 : (exitSet p₀).card = 1 := by
        have h1 : 1 ≤ (exitSet p₀).card :=
          Finset.card_pos.2 (exitSet_nonempty θ hp₀)
        have h2 : 1 ≤ (preExitSet p₀).card :=
          Finset.card_pos.2 (Finset.nonempty_of_ne_empty hpre)
        omega
      have hja_in : ja ∈ entrySet p₀ := by
        refine mem_entrySet.2 ⟨?_, hsja⟩
        intro hmem
        exact Finset.disjoint_left.1 (θ.parts_disjoint q₀ hq₀ p₀ hp₀ hq₀p) hja hmem
      have hjb_in : jb ∈ entrySet p₀ := by
        refine mem_entrySet.2 ⟨?_, hsjb⟩
        intro hmem
        exact Finset.disjoint_left.1 (θ.parts_disjoint q₁ hq₁ p₀ hp₀ hq₁p) hjb hmem
      have hjab : ja ≠ jb := by
        rintro rfl
        exact Finset.disjoint_left.1 (θ.parts_disjoint q₀ hq₀ q₁ hq₁ (Ne.symm hq₁q₀))
          hja hjb
      have h2le : 2 ≤ (entrySet p₀).card := by
        have hsub : ({ja, jb} : Finset (Fin N)) ⊆ entrySet p₀ := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx'
          · exact hja_in
          · rw [Finset.mem_singleton] at hx'
            subst hx'
            exact hjb_in
        have := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_notMem (by simpa using hjab),
          Finset.card_singleton] at this
      rw [card_entrySet, hexit1] at h2le
      omega
  -- the parts are exactly `p₀` and `q₀`, and `q₀`'s cut set is empty
  have hparts : θ.parts = {p₀, q₀} := by
    apply Finset.Subset.antisymm
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : r = p₀
      · exact Or.inl h0
      · exact Or.inr (huniq r hr h0)
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl <;> assumption
  have hcutq : θ.cutSet q₀ = ∅ := by
    rw [SysPartition.cutSet, hdq₀]
    have hfil : (θ.parts.filter
        fun r => r ≠ q₀ ∧ (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr
      rw [hparts] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · rintro ⟨-, hd⟩
        rw [hdir₀] at hd
        rcases hd with h | h <;> exact absurd h (by decide)
      · rintro ⟨hne', -⟩
        exact hne' rfl
    rw [hfil]
    exact Finset.sup_empty
  have hp₀q : p₀ ∉ ({q₀} : Finset (Finset (Fin N))) := by
    simpa using Ne.symm hq₀p
  rw [sysCutCount, hparts, Finset.sum_insert hp₀q, Finset.sum_singleton, hcutq,
    Finset.card_empty, mul_zero, add_zero, hcut₀]

end CaseOne


section Master

variable [NeZero N]

/-- **The `D = 2` bound.**  A partition damaging exactly two units has normalizer either
exactly `2(N-1)` (two singleton inputs blocks) or at most `N²/4` (one inputs block and
its complement).  Stated multiplicatively to stay in `ℕ`. -/
theorem sysCutCount_of_damagedCount_two (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 2) :
    sysCutCount θ = 2 * (N - 1) ∨ 4 * sysCutCount θ ≤ N * N := by
  classical
  have hnotall := not_all_outputs_of_damagedCount_two hN θ hD
  push_neg at hnotall
  obtain ⟨p₀, hp₀, hd₀⟩ := hnotall
  by_cases hsecond : ∃ p₁, p₁ ∈ θ.parts ∧ p₁ ≠ p₀ ∧ θ.dir p₁ ≠ Dir.outputs
  · obtain ⟨p₁, hp₁, hne, hd₁⟩ := hsecond
    exact Or.inl (sysCutCount_of_two_inputs hN θ hD hp₀ hp₁ (Ne.symm hne) hd₀ hd₁)
  · push_neg at hsecond
    have huni : ∀ r ∈ θ.parts, r ≠ p₀ → θ.dir r = Dir.outputs := by
      intro r hr hrp
      by_contra hdr
      exact hdr (hsecond r hr hrp)
    refine Or.inr ?_
    rw [sysCutCount_of_unique_inputs hN θ hD hp₀ hd₀ huni]
    exact card_mul_compl_le p₀

end Master

end IIT
