/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantShield

/-!
# Every proper candidate system has `φ_s < 4`

The shielded witness.  Pick `d ∉ S`.  Either `S` has a doubled gap or a stranded unit --
in which case `φ_s(S) = 0` outright -- or `pred d` and `shift d` both lie in `S`.  Writing
`e = pred d`, the arc of `S` running backwards from `e`, sized to half of `S`, damages
**exactly one** unit: `e` itself, whose only live input `shift d` lies outside the arc.
Every other unit of the arc keeps its live inputs inside, the critical case being the unit
one step back from `e`, which is *shielded* because its second window slot is `d ∉ S`.

The normalizer of that two-block partition is `⌊|S|²/4⌋`, so `sysPhi_circNet_gen_le`
gives `φ_s(S) ≤ |S|(|S|-1)/⌊|S|²/4⌋ < 4`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Competitor

variable [NeZero N]

/-- The predecessor of `e` after `N-1` steps is its successor. -/
lemma pred_iterate_pred_card (e : Fin N) : pred^[N - 1] e = shift e := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hstep : pred (pred^[N - 1] e) = e := by
    have h1 : pred^[N - 1 + 1] e = pred (pred^[N - 1] e) :=
      Function.iterate_succ_apply' pred (N - 1) e
    rw [show N - 1 + 1 = N by omega, pred_iterate_card] at h1
    exact h1.symm
  calc pred^[N - 1] e = shift (pred (pred^[N - 1] e)) := (shift_pred _).symm
    _ = shift e := by rw [hstep]

/-- If `d ∉ S` then `S` is swept in `N-1` backward steps from `e = pred d`. -/
lemma subset_arcBack_pred_card {S : Finset (Fin N)} {d : Fin N} (hd : d ∉ S)
    (e : Fin N) (he : shift e = d) : S ⊆ arcBack e (N - 1) := by
  intro a ha
  have hmemu : a ∈ arcBack e N := by
    rw [arcBack_card_eq_univ]
    exact Finset.mem_univ a
  obtain ⟨t, htN, hta⟩ := mem_arcBack.1 hmemu
  refine mem_arcBack.2 ⟨t, ?_, hta⟩
  rcases Nat.lt_or_ge t (N - 1) with h | h
  · exact h
  · exfalso
    have hteq : t = N - 1 := by omega
    rw [hteq, pred_iterate_pred_card, he] at hta
    exact hd (hta ▸ ha)

/-- The two-block partition `P / S \ P`, the first severing its inputs. -/
noncomputable def shieldPart {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) : SysPartition N S where
  parts := {P, S \ P}
  dir p := if p = P then Dir.inputs else Dir.outputs
  parts_nonempty := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact hP
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact hrest
  parts_subset := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact hPS
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact Finset.sdiff_subset
  parts_disjoint := by
    intro p hp q hq hpq
    rcases Finset.mem_insert.1 hp with rfl | hp' <;>
      rcases Finset.mem_insert.1 hq with rfl | hq'
    · exact absurd rfl hpq
    · rw [Finset.mem_singleton] at hq'
      subst hq'
      exact Finset.disjoint_sdiff
    · rw [Finset.mem_singleton] at hp'
      subst hp'
      exact Finset.disjoint_sdiff.symm
    · rw [Finset.mem_singleton] at hp' hq'
      subst hp'
      subst hq'
      exact absurd rfl hpq
  parts_cover := by
    intro i hi
    by_cases h : i ∈ P
    · exact ⟨P, Finset.mem_insert_self _ _, h⟩
    · exact ⟨S \ P, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        Finset.mem_sdiff.2 ⟨hi, h⟩⟩
  two_le := by
    have hne : P ≠ S \ P := by
      intro heq
      obtain ⟨x, hx⟩ := hP
      have : x ∈ S \ P := heq ▸ hx
      exact (Finset.mem_sdiff.1 this).2 hx
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

lemma shieldPart_dir_P {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) : (shieldPart hPS hP hrest).dir P = Dir.inputs := by
  unfold shieldPart
  simp

lemma shieldPart_mem_P {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) : P ∈ (shieldPart hPS hP hrest).parts := by
  unfold shieldPart
  simp

lemma shieldPart_mem_rest {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) : S \ P ∈ (shieldPart hPS hP hrest).parts := by
  unfold shieldPart
  simp

lemma shieldPart_ne {S P : Finset (Fin N)} (hP : P.Nonempty) : P ≠ S \ P := by
  intro heq
  obtain ⟨x, hx⟩ := hP
  have : x ∈ S \ P := heq ▸ hx
  exact (Finset.mem_sdiff.1 this).2 hx

lemma shieldPart_dir_rest {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) :
    (shieldPart hPS hP hrest).dir (S \ P) = Dir.outputs := by
  unfold shieldPart
  simp [Ne.symm (shieldPart_ne (S := S) hP)]

lemma shieldPart_cutSet_P {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) :
    (shieldPart hPS hP hrest).cutSet P = S \ P := by
  rw [SysPartition.cutSet, shieldPart_dir_P]

lemma shieldPart_cutSet_rest {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) :
    (shieldPart hPS hP hrest).cutSet (S \ P) = ∅ := by
  rw [SysPartition.cutSet, shieldPart_dir_rest]
  have hfil : ((shieldPart hPS hP hrest).parts.filter
      fun r => r ≠ S \ P ∧ ((shieldPart hPS hP hrest).dir r = Dir.outputs ∨
        (shieldPart hPS hP hrest).dir r = Dir.both)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro r hr
    have hpts : (shieldPart hPS hP hrest).parts = {P, S \ P} := rfl
    rw [hpts] at hr
    rcases Finset.mem_insert.1 hr with rfl | hr'
    · rintro ⟨-, hd⟩
      rw [shieldPart_dir_P] at hd
      rcases hd with h | h <;> exact absurd h (by decide)
    · rw [Finset.mem_singleton] at hr'
      subst hr'
      rintro ⟨hne, -⟩
      exact hne rfl
  rw [hfil]
  exact Finset.sup_empty

/-- The normalizer of the shielded partition. -/
lemma sysCutCount_shieldPart {S P : Finset (Fin N)} (hPS : P ⊆ S) (hP : P.Nonempty)
    (hrest : (S \ P).Nonempty) :
    sysCutCount (shieldPart hPS hP hrest) = P.card * (S.card - P.card) := by
  have hpts : (shieldPart hPS hP hrest).parts = {P, S \ P} := rfl
  have hnm : P ∉ ({S \ P} : Finset (Finset (Fin N))) := by
    simpa using shieldPart_ne (S := S) hP
  rw [sysCutCount, hpts, Finset.sum_insert hnm, Finset.sum_singleton,
    shieldPart_cutSet_P, shieldPart_cutSet_rest, Finset.card_empty, mul_zero, add_zero]
  congr 1
  rw [Finset.card_sdiff, Finset.inter_eq_left.2 hPS]

/-- Longer sweeps contain shorter ones. -/
lemma arcBack_mono (e : Fin N) {T T' : ℕ} (h : T ≤ T') : arcBack e T ⊆ arcBack e T' := by
  intro j hj
  obtain ⟨t, ht, htj⟩ := mem_arcBack.1 hj
  exact mem_arcBack.2 ⟨t, by omega, htj⟩

/-- Cancelling `t` backward steps with `t` forward ones. -/
lemma shift_iterate_pred_iterate (t : ℕ) (x : Fin N) : shift^[t] (pred^[t] x) = x := by
  induction t generalizing x with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply' pred, Function.iterate_succ_apply shift,
        shift_pred, ih]

/-- No cycle shorter than `N`. -/
lemma shift_iterate_ne_self {e : Fin N} {k : ℕ} (hk0 : 0 < k) (hkN : k < N) :
    shift^[k] e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  rw [shift_iterate_val] at hv
  have hlt := e.isLt
  rcases Nat.lt_or_ge (e.val + k) N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have h2 : e.val + k - N < N := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2] at hv
    omega

/-- **The successor of the gap lies outside a short sweep**: `shift d = shift² e` is not
reached in fewer than `N-1` backward steps from `e`. -/
lemma shift_shift_notMem_arcBack {e : Fin N} {T : ℕ} (hT : T ≤ N - 2) (hN : 3 ≤ N) :
    shift (shift e) ∉ arcBack e T := by
  intro hmem
  obtain ⟨t, htT, hte⟩ := mem_arcBack.1 hmem
  have hcancel : shift^[t + 2] e = e := by
    have h1 : shift^[t] (pred^[t] e) = e := shift_iterate_pred_iterate t e
    have h2 : shift^[t] (shift (shift e)) = e := by rw [← hte]; exact h1
    calc shift^[t + 2] e = shift^[t] (shift^[2] e) := by
          rw [← Function.iterate_add_apply]
      _ = e := h2
  exact shift_iterate_ne_self (by omega) (by omega) hcancel

/-- **The shielded witness damages exactly one unit.** -/
theorem damagedCountOn_shield (hN : 3 ≤ N) {S : Finset (Fin N)} {d : Fin N}
    (hd : d ∉ S) (heS : pred d ∈ S) (hsd : shift d ∈ S) {T : ℕ} (hT2 : T ≤ N - 2)
    (hT1 : 1 ≤ T)
    (hP : (S ∩ arcBack (pred d) T).Nonempty)
    (hrest : (S \ (S ∩ arcBack (pred d) T)).Nonempty) :
    damagedCountOn S (shieldPart Finset.inter_subset_left hP hrest) = 1 := by
  classical
  set e := pred d with hedef
  have he : shift e = d := shift_pred d
  set P := S ∩ arcBack e T with hPdef
  have heP : e ∈ P := Finset.mem_inter.2 ⟨heS,
    mem_arcBack.2 ⟨0, by omega, rfl⟩⟩
  set θ := shieldPart (Finset.inter_subset_left : P ⊆ S) hP hrest with hθdef
  have hcutP : θ.cutSet P = S \ P := shieldPart_cutSet_P _ hP hrest
  have hcutR : θ.cutSet (S \ P) = ∅ := shieldPart_cutSet_rest _ hP hrest
  have hdam : damagedOn S θ = {e} := by
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨hjS, k, hkl, hkc⟩ := Finset.mem_filter.1 hj
      rw [Finset.mem_singleton]
      by_contra hje
      by_cases hjP : j ∈ P
      · -- a unit of the arc other than `e` keeps its live inputs inside
        rw [θ.partOf_eq (shieldPart_mem_P _ hP hrest) hjP, hcutP] at hkc
        obtain ⟨hkS, hkP⟩ := Finset.mem_sdiff.1 hkc
        obtain ⟨t, htT, htj⟩ := mem_arcBack.1 (Finset.mem_inter.1 hjP).2
        have ht1 : 1 ≤ t := by
          rcases Nat.eq_zero_or_pos t with h0 | h
          · rw [h0] at htj
            exact absurd htj.symm hje
          · exact h
        rcases mem_liveInputs.1 hkl with rfl | rfl
        · exact hkP (Finset.mem_inter.2 ⟨hkS,
            shift_mem_arcBack (Finset.mem_inter.1 hjP).2 hje⟩)
        · exact hkP (Finset.mem_inter.2 ⟨hkS, by
            rcases Nat.lt_or_ge t 2 with h2 | h2
            · exfalso
              have ht : t = 1 := by omega
              rw [ht] at htj
              have := shift_shift_of_one_step htj
              rw [this, he] at hkS
              exact hd hkS
            · exact shift_shift_mem_arcBack htT htj h2⟩)
      · -- units outside the arc see an empty cut set
        have hjR : j ∈ S \ P := Finset.mem_sdiff.2 ⟨hjS, hjP⟩
        rw [θ.partOf_eq (shieldPart_mem_rest _ hP hrest) hjR, hcutR] at hkc
        simp at hkc
    · intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      refine Finset.mem_filter.2 ⟨heS, shift (shift e), mem_liveInputs.2 (Or.inr rfl), ?_⟩
      rw [θ.partOf_eq (shieldPart_mem_P _ hP hrest) heP, hcutP]
      refine Finset.mem_sdiff.2 ⟨by rw [he]; exact hsd, ?_⟩
      intro hmem
      exact shift_shift_notMem_arcBack hT2 hN (Finset.mem_inter.1 hmem).2
  rw [damagedCountOn, hdam, Finset.card_singleton]

/-- **Every proper candidate system has `φ_s < 4`**, for every `N ≥ 3` with at least two
units in the candidate.  This is the competitor half of `[IIT4, Eq 26]`'s exclusion. -/
theorem sysPhi_circNet_lt_four (hN : 3 ≤ N) {S : Finset (Fin N)}
    (hprop : S ≠ Finset.univ) (hS2 : 2 ≤ S.card) (u s : State N) :
    sysPhi (circNet N) S u s < 4 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d ∉ S := by
    by_contra hc
    push_neg at hc
    exact hprop (Finset.eq_univ_of_forall hc)
  by_cases h1 : pred d ∈ S
  · by_cases h2 : shift d ∈ S
    · -- the shielded witness
      obtain ⟨T, hTN, hTcard⟩ := exists_arc_card S (pred d) (m := S.card / 2) (by omega)
      have hPS : S ∩ arcBack (pred d) T ⊆ S := Finset.inter_subset_left
      have hP : (S ∩ arcBack (pred d) T).Nonempty := by
        rw [← Finset.card_pos, hTcard]
        omega
      have hT1 : 1 ≤ T := by
        rcases Nat.eq_zero_or_pos T with h0 | h
        · exfalso
          rw [h0, arcBack_zero, Finset.inter_empty, Finset.card_empty] at hTcard
          omega
        · exact h
      have hT2 : T ≤ N - 2 := by
        by_contra hc
        push_neg at hc
        have hsub : S ⊆ arcBack (pred d) T :=
          (subset_arcBack_pred_card hd (pred d) (shift_pred d)).trans
            (arcBack_mono (pred d) (by omega))
        rw [Finset.inter_eq_left.2 hsub] at hTcard
        omega
      have hrest : (S \ (S ∩ arcBack (pred d) T)).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.2 hPS, hTcard]
        omega
      have hdam := damagedCountOn_shield hN hd h1 h2 hT2 hT1 hP hrest
      have hcc := sysCutCount_shieldPart hPS hP hrest
      have hbound := sysPhi_circNet_gen_le hN u s (shieldPart hPS hP hrest)
      rw [hdam, hcc, hTcard] at hbound
      have harith : S.card * (S.card - 1)
          < 4 * (S.card / 2 * (S.card - S.card / 2)) := by
        rcases Nat.even_or_odd S.card with ⟨q, hq⟩ | ⟨q, hq⟩
        · have hdiv : S.card / 2 = q := by omega
          rw [hdiv, hq, show q + q - q = q by omega, show q + q - 1 = 2 * q - 1 by omega]
          obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
          nlinarith
        · have hdiv : S.card / 2 = q := by omega
          have hq1 : 1 ≤ q := by omega
          rw [hdiv, hq, show 2 * q + 1 - q = q + 1 by omega,
            show 2 * q + 1 - 1 = 2 * q by omega]
          nlinarith
      have hBpos : 0 < S.card / 2 * (S.card - S.card / 2) := by
        have a1 : 1 ≤ S.card / 2 := by omega
        have a2 : 1 ≤ S.card - S.card / 2 := by omega
        exact Nat.mul_pos a1 a2
      refine lt_of_le_of_lt hbound ?_
      rw [Nat.cast_one, mul_one,
        div_lt_iff₀ (by exact_mod_cast hBpos : (0 : ℝ) <
          ((S.card / 2 * (S.card - S.card / 2) : ℕ) : ℝ))]
      have hcast : ((S.card * (S.card - 1) : ℕ) : ℝ)
          < ((4 * (S.card / 2 * (S.card - S.card / 2)) : ℕ) : ℝ) := by
        exact_mod_cast harith
      calc ((S.card * (S.card - 1) : ℕ) : ℝ)
          < ((4 * (S.card / 2 * (S.card - S.card / 2)) : ℕ) : ℝ) := hcast
        _ = 4 * ((S.card / 2 * (S.card - S.card / 2) : ℕ) : ℝ) := by push_cast; ring
    · -- `pred d` is stranded
      have hlive : liveInputs (pred d) ∩ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        obtain ⟨hxl, hxS⟩ := Finset.mem_inter.1 hx
        rcases mem_liveInputs.1 hxl with rfl | rfl
        · rw [shift_pred] at hxS
          exact hd hxS
        · rw [shift_pred] at hxS
          exact h2 hxS
      have hrest : (S.erase (pred d)).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem h1]
        omega
      rw [sysPhi_circNet_eq_zero_of_no_live h1 hrest hlive u s]
      norm_num
  · -- doubled gap at `(pred d, d)`
    have hgap := sysPhi_circNet_eq_zero_of_double_gap (S := S) (m := pred d) h1
      (by rw [shift_pred]; exact hd) u s
    rw [hgap]
    norm_num

end Competitor





end IIT
