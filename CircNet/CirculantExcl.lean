/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantGap

/-!
# Subsystems with a doubled gap are reducible

`CircNet/CirculantGap.lean` shows that a unit of `S` reading nothing else in `S` forces
`φ_s(S) = 0`.  This file supplies such a unit whenever the complement of `S` contains two
consecutive units: walking backwards from the gap, the first unit of `S` one meets has
both of its live inputs inside the gap.

Consequently the only candidate subsystems that can survive `[IIT4, Eq 26]` are those
whose complement contains no two consecutive units, i.e. the isolated deletions.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Backward

variable [NeZero N]

/-- `shift` iterated `N` times is the identity. -/
lemma shift_iterate_card (b : Fin N) : shift^[N] b = b := by
  apply Fin.ext
  rw [shift_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt b.isLt]

/-- The cyclic predecessor. -/
noncomputable def pred (i : Fin N) : Fin N := shift^[N - 1] i

lemma shift_pred (i : Fin N) : shift (pred i) = i := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : shift (shift^[N - 1] i) = shift^[N] i := by
    rw [← Function.iterate_succ_apply' shift (N - 1) i]
    congr 1
    omega
  rw [pred, this, shift_iterate_card]

lemma pred_shift (i : Fin N) : pred (shift i) = i :=
  shift_injective (by rw [shift_pred])

/-- Every unit is reached from any other by iterating the predecessor. -/
lemma exists_iterate_pred (a b : Fin N) : ∃ m : ℕ, pred^[m] b = a := by
  have key : ∀ m : ℕ, ∀ x : Fin N, pred^[m] (shift^[m] x) = x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ p ih =>
        intro x
        rw [Function.iterate_succ_apply' shift, Function.iterate_succ_apply pred,
          pred_shift]
        exact ih x
  obtain ⟨m, hm⟩ := exists_iterate_shift b a
  exact ⟨m, by rw [← hm, key m a]⟩

/-- **A doubled gap strands a unit.**  If `m` and `m+1` both lie outside `S` and `S` is
nonempty, then walking backwards from `m` the first unit of `S` encountered has both of its
live inputs outside `S`. -/
theorem exists_no_live_of_double_gap {S : Finset (Fin N)} (hS : S.Nonempty)
    {m : Fin N} (hm : m ∉ S) (hm2 : shift m ∉ S) :
    ∃ j ∈ S, liveInputs j ∩ S = ∅ := by
  classical
  have hex : ∃ t : ℕ, pred^[t] m ∈ S := by
    obtain ⟨a, ha⟩ := hS
    obtain ⟨t, ht⟩ := exists_iterate_pred a m
    exact ⟨t, ht ▸ ha⟩
  obtain ⟨t₀, hmem, hmin⟩ : ∃ t, pred^[t] m ∈ S ∧ ∀ r < t, pred^[r] m ∉ S :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  have ht0pos : 0 < t₀ := by
    rcases Nat.eq_zero_or_pos t₀ with h | h
    · rw [h] at hmem; simp at hmem; exact absurd hmem hm
    · exact h
  refine ⟨pred^[t₀] m, hmem, ?_⟩
  -- the two live inputs are the two units walked over
  have hstep : ∀ r : ℕ, shift (pred^[r + 1] m) = pred^[r] m := by
    intro r
    rw [Function.iterate_succ_apply']
    exact shift_pred _
  have h1 : shift (pred^[t₀] m) = pred^[t₀ - 1] m := by
    obtain ⟨r, hr⟩ : ∃ r, t₀ = r + 1 := ⟨t₀ - 1, by omega⟩
    subst hr
    simpa using hstep r
  have h1notin : shift (pred^[t₀] m) ∉ S := by
    rw [h1]; exact hmin _ (by omega)
  have h2notin : shift (shift (pred^[t₀] m)) ∉ S := by
    rw [h1]
    rcases Nat.lt_or_ge t₀ 2 with hlt | hge
    · have ht1 : t₀ - 1 = 0 := by omega
      rw [ht1]
      simpa using hm2
    · obtain ⟨r, hr⟩ : ∃ r, t₀ = r + 2 := ⟨t₀ - 2, by omega⟩
      have : shift (pred^[t₀ - 1] m) = pred^[t₀ - 2] m := by
        have he : t₀ - 1 = (t₀ - 2) + 1 := by omega
        rw [he, hstep (t₀ - 2)]
      rw [this]
      exact hmin _ (by omega)
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨hxl, hxS⟩ := Finset.mem_inter.1 hx
  rcases mem_liveInputs.1 hxl with rfl | rfl
  · exact h1notin hxS
  · exact h2notin hxS

/-- **Every subsystem whose complement contains two consecutive units is reducible.**

So the only candidate systems that can compete with the whole substrate under
`[IIT4, Eq 26]` are those obtained by deleting an *independent* set of units. -/
theorem sysPhi_circNet_eq_zero_of_double_gap {S : Finset (Fin N)} {m : Fin N}
    (hm : m ∉ S) (hm2 : shift m ∉ S) (u s : State N) :
    sysPhi (circNet N) S u s = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty S with rfl | hS
  · exact sysPhi_eq_zero_of_card_le_one _ u s (by simp)
  obtain ⟨j, hj, hlive⟩ := exists_no_live_of_double_gap hS hm hm2
  rcases Finset.eq_empty_or_nonempty (S.erase j) with hrest | hrest
  · refine sysPhi_eq_zero_of_card_le_one _ u s ?_
    have : S.card - 1 = 0 := by
      rw [← Finset.card_erase_of_mem hj, hrest, Finset.card_empty]
    have hpos : 0 < S.card := Finset.card_pos.2 hS
    omega
  · exact sysPhi_circNet_eq_zero_of_no_live hj hrest hlive u s

end Backward

end IIT
