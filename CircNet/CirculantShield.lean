/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantSub

/-!
# The backward sweep, and the shield

Machinery for the shielded witness of a proper candidate system `S`.

`arcBack e T` is the arc of `T` units running backwards from `e`.  Two facts drive the
construction: the sweep grows by at most one unit per step, so every intermediate
cardinality is realised (`exists_arc_card`); and the arc is **backward closed**, so a unit
of it other than `e` keeps its live inputs inside -- except possibly the predecessor of
`e`, which is *shielded* when `shift e ∉ S`, because then its second window slot is not a
live input at all (`shield`).
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Sweep

variable [NeZero N]

/-- `shift` iterated a multiple of `N` times is the identity. -/
lemma shift_iterate_mul_card (x : Fin N) (q : ℕ) : shift^[q * N] x = x := by
  induction q with
  | zero => simp
  | succ p ih =>
      rw [show (p + 1) * N = p * N + N by ring, Function.iterate_add_apply,
        shift_iterate_card, ih]

/-- `pred` iterated `N` times is the identity. -/
lemma pred_iterate_card (x : Fin N) : pred^[N] x = x := by
  have hp : (pred : Fin N → Fin N) = shift^[N - 1] := rfl
  rw [hp, ← Function.iterate_mul]
  exact shift_iterate_mul_card x (N - 1)

lemma pred_iterate_mul_card (x : Fin N) (q : ℕ) : pred^[q * N] x = x := by
  induction q with
  | zero => simp
  | succ p ih =>
      rw [show (p + 1) * N = p * N + N by ring, Function.iterate_add_apply,
        pred_iterate_card, ih]

/-- Iterating `pred` is periodic with period `N`. -/
lemma pred_iterate_mod (x : Fin N) (m : ℕ) : pred^[m % N] x = pred^[m] x := by
  have hm : m = m % N + (m / N) * N := by
    conv_lhs => rw [← Nat.div_add_mod m N]
    rw [Nat.mul_comm]
    omega
  conv_rhs => rw [hm]
  rw [Function.iterate_add_apply, pred_iterate_mul_card]

/-- The arc of `T` units running backwards from `e`. -/
noncomputable def arcBack (e : Fin N) (T : ℕ) : Finset (Fin N) :=
  (Finset.range T).image fun t => pred^[t] e

lemma mem_arcBack {e : Fin N} {T : ℕ} {j : Fin N} :
    j ∈ arcBack e T ↔ ∃ t < T, pred^[t] e = j := by
  unfold arcBack
  simp only [Finset.mem_image, Finset.mem_range]

lemma arcBack_zero (e : Fin N) : arcBack e 0 = (∅ : Finset (Fin N)) := by
  unfold arcBack
  simp

lemma arcBack_succ (e : Fin N) (T : ℕ) :
    arcBack e (T + 1) = insert (pred^[T] e) (arcBack e T) := by
  unfold arcBack
  rw [Finset.range_add_one, Finset.image_insert]

/-- After `N` steps the whole cycle has been swept. -/
lemma arcBack_card_eq_univ (e : Fin N) : arcBack e N = Finset.univ := by
  refine Finset.eq_univ_of_forall fun a => ?_
  obtain ⟨m, hm⟩ := exists_iterate_pred a e
  exact mem_arcBack.2 ⟨m % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N)),
    by rw [pred_iterate_mod]; exact hm⟩

omit [NeZero N] in
/-- The sweep grows by at most one unit per step. -/
lemma card_inter_step (S A : Finset (Fin N)) (x : Fin N) :
    (S ∩ insert x A).card ≤ (S ∩ A).card + 1 := by
  classical
  have hsub : S ∩ insert x A ⊆ insert x (S ∩ A) := by
    intro y hy
    rw [Finset.mem_inter, Finset.mem_insert] at hy
    obtain ⟨hyS, hyA⟩ := hy
    rcases hyA with rfl | hyA'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hyS, hyA'⟩)
  calc (S ∩ insert x A).card ≤ (insert x (S ∩ A)).card := Finset.card_le_card hsub
    _ ≤ (S ∩ A).card + 1 := Finset.card_insert_le _ _

/-- **Discrete intermediate value.**  Every cardinality up to `|S|` is realised by some
prefix of the backward sweep, and by one of length at most `N`. -/
theorem exists_arc_card (S : Finset (Fin N)) (e : Fin N) {m : ℕ} (hm : m ≤ S.card) :
    ∃ T ≤ N, (S ∩ arcBack e T).card = m := by
  classical
  have hfull : (S ∩ arcBack e N).card = S.card := by
    rw [arcBack_card_eq_univ, Finset.inter_univ]
  have hex : ∃ T, m ≤ (S ∩ arcBack e T).card := ⟨N, by rw [hfull]; exact hm⟩
  obtain ⟨T, hT, hmin⟩ : ∃ T, m ≤ (S ∩ arcBack e T).card ∧
      ∀ r < T, ¬ (m ≤ (S ∩ arcBack e r).card) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  have hTN : T ≤ N := by
    by_contra hlt
    push_neg at hlt
    exact hmin N hlt (by rw [hfull]; exact hm)
  refine ⟨T, hTN, ?_⟩
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0
    rw [arcBack_zero, Finset.inter_empty, Finset.card_empty] at hT ⊢
    omega
  · obtain ⟨r, rfl⟩ : ∃ r, T = r + 1 := ⟨T - 1, by omega⟩
    have hlow : (S ∩ arcBack e r).card < m := by
      have := hmin r (by omega)
      omega
    have hstep : (S ∩ arcBack e (r + 1)).card ≤ (S ∩ arcBack e r).card + 1 := by
      rw [arcBack_succ]
      exact card_inter_step S (arcBack e r) (pred^[r] e)
    omega

end Sweep

section Closure

variable [NeZero N]

/-- **Backward closure**: a unit of the arc other than `e` has its successor in the
arc. -/
lemma shift_mem_arcBack {e : Fin N} {T : ℕ} {j : Fin N} (hj : j ∈ arcBack e T)
    (hje : j ≠ e) : shift j ∈ arcBack e T := by
  obtain ⟨t, htT, htj⟩ := mem_arcBack.1 hj
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact absurd htj.symm hje
  · obtain ⟨r, rfl⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
    refine mem_arcBack.2 ⟨r, by omega, ?_⟩
    rw [← htj, Function.iterate_succ_apply', shift_pred]

/-- The second successor of a unit two or more steps back is still in the arc. -/
lemma shift_shift_mem_arcBack {e : Fin N} {T : ℕ} {j : Fin N} {t : ℕ}
    (htT : t < T) (htj : pred^[t] e = j) (ht2 : 2 ≤ t) :
    shift (shift j) ∈ arcBack e T := by
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 2 := ⟨t - 2, by omega⟩
  refine mem_arcBack.2 ⟨r, by omega, ?_⟩
  rw [← htj]
  rw [show r + 2 = (r + 1) + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply', shift_pred, shift_pred]

/-- A unit exactly one step back from `e` has `shift e` as its second window slot. -/
lemma shift_shift_of_one_step {e : Fin N} {j : Fin N} (htj : pred^[1] e = j) :
    shift (shift j) = shift e := by
  rw [← htj]
  simp only [Function.iterate_one]
  rw [shift_pred]

end Closure

end IIT
