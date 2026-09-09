/-
The window-3 exclusive-or circulant on `Fin N`.

Unit `i` computes `s i ⊕ s (i+1) ⊕ s (i+2)`, indices modulo `N`; as a matrix over
`GF(2)` this is `A = I + P + P²` with `P` the cyclic shift.

This file proves, for **arbitrary `N`**, that the dynamics is a bijection exactly when
`3 ∤ N`.  The argument is a linear recurrence: a kernel element satisfies
`d (i+2) = d i ⊕ d (i+1)`, hence `d (i+3) = d i`; when `3` is invertible modulo `N` that
upgrades to `d (i+1) = d i`, so `d` is constant, and the relation forces the constant to
be `false`.  Bijectivity is what makes the cause side as strong as the effect side.

All index arithmetic is carried out on natural-number representatives, since `Fin N`
carries no `NatCast` for a variable `N`.
-/
import CircNet.Explore

namespace IIT

variable {N : ℕ}

/-! ## The dynamics -/

/-- The cyclic shift `i ↦ i+1` on `Fin N`. -/
def shift [NeZero N] (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

/-- The representative of `shift` is `+1` modulo `N`. -/
lemma shift_val [NeZero N] (i : Fin N) : (shift i).val = (i.val + 1) % N := rfl

/-- The next state of unit `i`: the exclusive-or over the window `{i, i+1, i+2}`. -/
def circVal [NeZero N] (i : Fin N) (s : State N) : Bool :=
  xor (xor (s i) (s (shift i))) (s (shift (shift i)))

/-- The state the circulant produces from `s`. -/
def circNext [NeZero N] (s : State N) : State N := fun i => circVal i s

/-! ## The modular inverse of `3`

Explicitly: if `N % 3 = 1` then `3 * (N - N/3) = 2N + 1`, and if `N % 3 = 2` then
`3 * (N/3 + 1) = N + 1`. -/

lemma exists_three_inv (hN : 0 < N) (h3 : ¬ (3 ∣ N)) : ∃ a b : ℕ, 3 * a = b * N + 1 := by
  have hdm : N = 3 * (N / 3) + N % 3 := (Nat.div_add_mod N 3).symm
  have hlt : N % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : N % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  have hcase : N % 3 = 1 ∨ N % 3 = 2 := by omega
  rcases hcase with h | h
  · exact ⟨N - N / 3, 2, by omega⟩
  · exact ⟨N / 3 + 1, 1, by omega⟩

/-! ## Two exclusive-or identities

Both are finite checks over `Bool`, stated separately because `cases` on a compound term
such as `s i` does not substitute its occurrences. -/

/-- Subtracting two equal three-fold exclusive-ors leaves `false`. -/
lemma xor_triple_cancel (a a' b b' c c' : Bool)
    (h : xor (xor a b) c = xor (xor a' b') c') :
    xor (xor (xor a a') (xor b b')) (xor c c') = false := by
  revert h; revert a a' b b' c c'; decide

/-- `xor a b = false` says `a = b`. -/
lemma eq_of_xor_eq_false {a b : Bool} (h : xor a b = false) : a = b := by
  revert h; revert a b; decide

/-! ## Bijectivity -/

section Kernel

variable [NeZero N] {d : State N}

/-- The kernel relation `[d i ⊕ d (i+1) ⊕ d (i+2) = false]`. -/
def InKernel (d : State N) : Prop :=
  ∀ i : Fin N, xor (xor (d i) (d (shift i))) (d (shift (shift i))) = false

/-- A kernel element read along natural-number representatives. -/
def ker_seq (d : State N) (k : ℕ) : Bool :=
  d ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

lemma ker_seq_succ (k : ℕ) :
    ker_seq d (k + 1) = d (shift ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩) := by
  unfold ker_seq
  congr 1
  apply Fin.ext
  simp [shift_val, Nat.mod_add_mod]

/-- The recurrence on representatives. -/
lemma ker_seq_step (h : InKernel d) (k : ℕ) :
    ker_seq d (k + 2) = xor (ker_seq d k) (ker_seq d (k + 1)) := by
  have hi := h ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩
  have e1 : ker_seq d (k + 1)
      = d (shift ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩) := ker_seq_succ k
  have e2 : ker_seq d (k + 2)
      = d (shift (shift ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩)) := by
    have : k + 2 = (k + 1) + 1 := by omega
    rw [this, ker_seq_succ (k + 1)]
    congr 2
    apply Fin.ext
    simp [shift_val, Nat.mod_add_mod]
  have e0 : ker_seq d k = d ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩ := rfl
  rw [e0, e1, e2]
  revert hi
  cases d ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩ <;>
    cases d (shift ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩) <;>
    cases d (shift (shift ⟨k % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩)) <;> simp

/-- Three-periodicity. -/
lemma ker_seq_period_three (h : InKernel d) (k : ℕ) : ker_seq d (k + 3) = ker_seq d k := by
  have h1 := ker_seq_step h (k + 1)
  have h2 := ker_seq_step h k
  have e : k + 1 + 2 = k + 3 := by omega
  have e' : k + 1 + 1 = k + 2 := by omega
  rw [e, e', h2] at h1
  rw [h1]
  cases ker_seq d k <;> cases ker_seq d (k + 1) <;> simp

lemma ker_seq_period_three_mul (h : InKernel d) (a k : ℕ) :
    ker_seq d (k + 3 * a) = ker_seq d k := by
  induction a with
  | zero => simp
  | succ m ih =>
      have e : k + 3 * (m + 1) = (k + 3 * m) + 3 := by omega
      rw [e, ker_seq_period_three h, ih]

/-- `N`-periodicity, immediate from the definition. -/
lemma ker_seq_period_N (b k : ℕ) : ker_seq d (k + b * N) = ker_seq d k := by
  unfold ker_seq
  congr 1
  apply Fin.ext
  simp [Nat.add_mul_mod_self_right]

/-- With `3` invertible mod `N`, three-periodicity upgrades to one-periodicity. -/
lemma ker_seq_shift_one (h3 : ¬ (3 ∣ N)) (h : InKernel d) (k : ℕ) :
    ker_seq d (k + 1) = ker_seq d k := by
  obtain ⟨a, b, hab⟩ := exists_three_inv (Nat.pos_of_ne_zero (NeZero.ne N)) h3
  calc ker_seq d (k + 1) = ker_seq d (k + 1 + b * N) := (ker_seq_period_N b (k + 1)).symm
    _ = ker_seq d (k + 3 * a) := by rw [hab]; ring_nf
    _ = ker_seq d k := ker_seq_period_three_mul h a k

lemma ker_seq_const (h3 : ¬ (3 ∣ N)) (h : InKernel d) (k : ℕ) :
    ker_seq d k = ker_seq d 0 := by
  induction k with
  | zero => rfl
  | succ p ih => rw [ker_seq_shift_one h3 h p, ih]

/-- **The kernel is trivial when `3 ∤ N`.** -/
theorem kernel_eq_zero (h3 : ¬ (3 ∣ N)) (h : InKernel d) : ∀ i, d i = false := by
  have hc := ker_seq_const h3 h
  have h0 := ker_seq_step h 0
  rw [hc 2, hc 1, hc 0] at h0
  have hzero : ker_seq d 0 = false := by
    revert h0; cases ker_seq d 0 <;> simp
  intro i
  have : ker_seq d i.val = d i := by
    unfold ker_seq
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [← this, hc i.val, hzero]

end Kernel

/-- **The window-3 circulant is injective, hence a bijection, whenever `3 ∤ N`.**

This is the hypothesis every later result needs: a bijective substrate has a cause side
as sharp as its effect side. -/
theorem circNext_injective [NeZero N] (h3 : ¬ (3 ∣ N)) :
    Function.Injective (circNext : State N → State N) := by
  intro s s' h
  have hker : InKernel (fun i => xor (s i) (s' i)) := by
    intro i
    have hi : circVal i s = circVal i s' := congrFun h i
    rw [circVal, circVal] at hi
    exact xor_triple_cancel _ _ _ _ _ _ hi
  funext i
  exact eq_of_xor_eq_false (kernel_eq_zero h3 hker i)

/-- The circulant is a bijection on states. -/
noncomputable def circEquiv (N : ℕ) [NeZero N] (h3 : ¬ (3 ∣ N)) : State N ≃ State N :=
  Equiv.ofBijective circNext (Finite.injective_iff_bijective.1 (circNext_injective h3))/-! ## Strong connectivity

`[IIT4, p.18]` (after Eq 23) records that `φ_s = 0` unless the substrate is strongly
connected, so this is a genuine prerequisite and not a formality.  Unit `j` is an input to
unit `i` exactly when `j ∈ {i, i+1, i+2}`; in particular `shift i` is always an input to
`i`, and those edges alone traverse the whole cycle. -/

section Connectivity

variable [NeZero N]

/-- The units unit `i` reads: its own window `{i, i+1, i+2}`. -/
def inputs (i : Fin N) : Finset (Fin N) := {i, shift i, shift (shift i)}

/-- `j` feeds `i` when `j` lies in `i`'s window. -/
def Feeds (j i : Fin N) : Prop := j ∈ inputs i

/-- The cyclic successor always feeds its predecessor: these edges alone form a
Hamiltonian cycle. -/
lemma feeds_shift (i : Fin N) : Feeds (shift i) i := by
  unfold Feeds inputs
  simp

/-- Representative of an iterated shift. -/
lemma shift_iterate_val (b : Fin N) (m : ℕ) : (shift^[m] b).val = (b.val + m) % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt b.isLt]
  | succ p ih =>
      rw [Function.iterate_succ_apply', shift_val, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- The shift acts transitively: every unit is an iterated shift of every other. -/
lemma exists_iterate_shift (a b : Fin N) : ∃ m : ℕ, shift^[m] b = a := by
  refine ⟨(a.val + N - b.val) % N, Fin.ext ?_⟩
  have hb := b.isLt
  have ha := a.isLt
  rw [shift_iterate_val, Nat.add_mod_mod]
  have h1 : b.val + (a.val + N - b.val) = a.val + N := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt ha]

/-- Reachability along the input edges. -/
def Reaches : Fin N → Fin N → Prop := Relation.ReflTransGen Feeds

/-- An iterated shift reaches its base point. -/
lemma reaches_of_iterate (b : Fin N) : ∀ m : ℕ, Reaches (shift^[m] b) b := by
  intro m
  induction m with
  | zero => exact Relation.ReflTransGen.refl
  | succ p ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.ReflTransGen.head (feeds_shift _) ih

/-- **The window-3 circulant is strongly connected**, for every `N`. -/
theorem circ_strongly_connected (a b : Fin N) : Reaches a b := by
  obtain ⟨m, hm⟩ := exists_iterate_shift a b
  rw [← hm]
  exact reaches_of_iterate b m

end Connectivity

/-! ## The substrate as a `UnitTPM`, and the halving law

From here on `3 ≤ N`, so that a unit's window `{i, i+1, i+2}` consists of three distinct
units.  (At `N ≤ 2` the window degenerates: at `N = 2` the rule collapses to `s (i+1)`.)
-/

section Net

variable [NeZero N]

/-- The window-3 circulant as a deterministic `UnitTPM`. -/
noncomputable def circNet (N : ℕ) [NeZero N] : UnitTPM N where
  prob i s b := if b = circVal i s then 1 else 0
  nonneg i s b := by by_cases h : b = circVal i s <;> simp [h]
  normalized i s := by cases h : circVal i s <;> simp [h]

/-- For `3 ≤ N` a unit differs from its own successor. -/
lemma shift_ne_self (hN : 3 ≤ N) (j : Fin N) : shift j ≠ j := by
  intro h
  have hval := congrArg Fin.val h
  rw [shift_val] at hval
  have hj := j.isLt
  by_cases he : j.val + 1 = N
  · rw [he, Nat.mod_self] at hval
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- For `3 ≤ N` a unit differs from its second successor. -/
lemma shift_shift_ne_self (hN : 3 ≤ N) (j : Fin N) : shift (shift j) ≠ j := by
  intro h
  have := congrArg Fin.val h
  rw [shift_val, shift_val] at this
  have hj := j.isLt
  have hmod : (j.val + 1) % N = if j.val + 1 = N then 0 else j.val + 1 := by
    by_cases he : j.val + 1 = N
    · rw [if_pos he, he, Nat.mod_self]
    · rw [if_neg he, Nat.mod_eq_of_lt (by omega)]
  rw [hmod] at this
  by_cases he : j.val + 1 = N
  · rw [if_pos he] at this
    simp [Nat.mod_eq_of_lt (show 1 < N by omega)] at this
    omega
  · rw [if_neg he] at this
    by_cases he2 : j.val + 2 = N
    · rw [he2, Nat.mod_self] at this; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at this; omega

/-- The two nontrivial window members are distinct. -/
lemma shift_shift_ne_shift (hN : 3 ≤ N) (j : Fin N) : shift (shift j) ≠ shift j :=
  fun h => shift_ne_self hN (shift j) h

/-- **Flipping a live input flips the unit's next value.**  Each of `i+1`, `i+2` occurs
exactly once in the window, so the exclusive-or changes sign. -/
lemma circVal_flipAt_shift (hN : 3 ≤ N) (j : Fin N) (s : State N) :
    circVal j (flipAt (shift j) s) = !(circVal j s) := by
  rw [circVal, circVal,
    flipAt_apply_of_ne (Ne.symm (shift_ne_self hN j)) s,
    flipAt_apply_self,
    flipAt_apply_of_ne (shift_shift_ne_shift hN j) s]
  cases s j <;> cases s (shift j) <;> cases s (shift (shift j)) <;> simp

lemma circVal_flipAt_shift_shift (hN : 3 ≤ N) (j : Fin N) (s : State N) :
    circVal j (flipAt (shift (shift j)) s) = !(circVal j s) := by
  rw [circVal, circVal,
    flipAt_apply_of_ne (Ne.symm (shift_shift_ne_self hN j)) s,
    flipAt_apply_of_ne (Ne.symm (shift_shift_ne_shift hN j)) s,
    flipAt_apply_self]
  cases s j <;> cases s (shift j) <;> cases s (shift (shift j)) <;> simp

/-- The live (non-self) inputs of a unit. -/
def liveInputs (j : Fin N) : Finset (Fin N) := {shift j, shift (shift j)}

lemma mem_liveInputs {j k : Fin N} : k ∈ liveInputs j ↔ k = shift j ∨ k = shift (shift j) := by
  unfold liveInputs
  simp

/-- Flipping any live input flips the unit's next value. -/
lemma circVal_flipAt_live (hN : 3 ≤ N) {j k : Fin N} (hk : k ∈ liveInputs j) (s : State N) :
    circVal j (flipAt k s) = !(circVal j s) := by
  rcases mem_liveInputs.1 hk with rfl | rfl
  · exact circVal_flipAt_shift hN j s
  · exact circVal_flipAt_shift_shift hN j s

/-- A live input is never the unit itself. -/
lemma liveInputs_ne (hN : 3 ≤ N) {j k : Fin N} (hk : k ∈ liveInputs j) : k ≠ j := by
  rcases mem_liveInputs.1 hk with rfl | rfl
  · exact shift_ne_self hN j
  · exact shift_shift_ne_self hN j

/-- **Omitting a live input halves `effUnit`.**  Flipping that input is an involution of
the marginalization fibre which flips unit `j`'s next state, so exactly half the fibre
gives each value.  This is the circulant's analogue of `effUnit_xorNet_of_not_mem`, with
the difference that only the two live inputs of `j` can halve it. -/
theorem effUnit_circNet_of_not_mem (hN : 3 ≤ N) (W : Finset (Fin N)) (m : State N)
    (j k : Fin N) (b : Bool) (hk : k ∉ W) (hlive : k ∈ liveInputs j) :
    effUnit (circNet N) W m j b = 1 / 2 := by
  classical
  have hkj : k ≠ j := liveInputs_ne hN hlive
  have hbne : ∀ c : Bool, ¬ (c = !c) := by decide
  have hbnot : ∀ c d : Bool, ¬ (c = d) → c = !d := by decide
  have hmaps : ∀ s ∈ agree W m, flipAt k s ∈ agree W m := by
    intro s hs
    rw [mem_agree] at hs ⊢
    intro i hi
    rw [flipAt_apply_of_ne (by rintro rfl; exact hk hi) s]
    exact hs i hi
  have hsum : ∑ s ∈ agree W m, (circNet N).prob j s b
      = ((((agree W m).filter fun s => b = circVal j s)).card : ℝ) := by
    rw [← Finset.sum_boole]
    rfl
  have hbij : (((agree W m).filter fun s => b = circVal j s)).card
      = (((agree W m).filter fun s => ¬ (b = circVal j s))).card := by
    refine Finset.card_nbij' (flipAt k) (flipAt k) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [circVal_flipAt_live hN hlive s, ← hs.2]
      exact hbne b
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [circVal_flipAt_live hN hlive s]
      exact hbnot _ _ hs.2
    · intro s _; exact flipAt_flipAt k s
    · intro s _; exact flipAt_flipAt k s
  have htot := Finset.card_filter_add_card_filter_not (s := agree W m)
    (fun s => b = circVal j s)
  have hcpos : 0 < (agree W m).card := Finset.card_pos.2 (agree_nonempty W m)
  have hc : (agree W m).card
      = 2 * (((agree W m).filter fun s => b = circVal j s)).card := by omega
  have h1 : (0 : ℝ) < ((((agree W m).filter fun s => b = circVal j s)).card : ℝ) := by
    have hp : 0 < (((agree W m).filter fun s => b = circVal j s)).card := by omega
    exact_mod_cast hp
  rw [effUnit, hsum, hc]
  push_cast
  field_simp

end Net

/-! ## The damage model

`φ_E` at a partition is exactly the number of **damaged** units: those with a live input
in their own block's cut set.  This is the circulant's counterpart of the `xorNet`
analysis, but it is genuinely sharper: for `xorNet` every unit reads every other, so a
nonempty cut set severs *every* unit of the block, whereas here a unit survives unless the
cut reaches one of its two live inputs.  That difference is exactly what separates the
whole substrate from its subsystems.
-/

section Damage

variable [NeZero N]

/-- Unit `j` is damaged by `θ` when the cut reaches one of its live inputs. -/
def Damaged (θ : SysPartition N Finset.univ) (j : Fin N) : Prop :=
  ∃ k ∈ liveInputs j, k ∈ θ.cutSet (θ.partOf j)

open scoped Classical in
/-- The damaged units. -/
noncomputable def damaged (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  Finset.univ.filter fun j => Damaged θ j

/-- The number of damaged units: the value of `φ_E` at `θ`. -/
noncomputable def damagedCount (θ : SysPartition N Finset.univ) : ℕ := (damaged θ).card

/-- On the fibre of a conditioning set containing `j`'s whole window, `circVal j` is
constant. -/
lemma circVal_eq_of_agree {W : Finset (Fin N)} {m s : State N} (hs : s ∈ agree W m)
    {j : Fin N} (hj : j ∈ W) (h1 : shift j ∈ W) (h2 : shift (shift j) ∈ W) :
    circVal j s = circVal j m := by
  rw [circVal, circVal, mem_agree.1 hs j hj, mem_agree.1 hs (shift j) h1,
    mem_agree.1 hs (shift (shift j)) h2]

/-- A conditioning set containing the whole window determines the unit. -/
lemma effUnit_circNet_of_window_subset (W : Finset (Fin N)) (m : State N) (j : Fin N)
    (b : Bool) (hj : j ∈ W) (h1 : shift j ∈ W) (h2 : shift (shift j) ∈ W) :
    effUnit (circNet N) W m j b = if b = circVal j m then 1 else 0 := by
  classical
  rw [effUnit]
  have hconst : ∀ s ∈ agree W m,
      (circNet N).prob j s b = if b = circVal j m then 1 else 0 := by
    intro s hs
    rw [show (circNet N).prob j s b = if b = circVal j s then 1 else 0 from rfl,
      circVal_eq_of_agree hs hj h1 h2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (agree W m).card := by
    exact_mod_cast Finset.card_pos.2 (agree_nonempty _ m)
  field_simp

/-- **A damaged unit contributes exactly one half.** -/
lemma effUnit_circNet_damaged (hN : 3 ≤ N) (θ : SysPartition N Finset.univ) (m : State N)
    (j : Fin N) (b : Bool) (h : Damaged θ j) :
    effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ m j b = 1 / 2 := by
  obtain ⟨k, hlive, hk⟩ := h
  exact effUnit_circNet_of_not_mem hN _ _ _ k _ (by simpa using hk) hlive

/-- **An undamaged unit contributes exactly one**, at the state the substrate produces. -/
lemma effUnit_circNet_undamaged (θ : SysPartition N Finset.univ) (m : State N)
    (j : Fin N) (h : ¬ Damaged θ j) :
    effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ m j (circVal j m) = 1 := by
  have hj : j ∈ (θ.cutSet (θ.partOf j))ᶜ := by
    simpa using notMem_cutSet_partOf θ j
  have hlive : ∀ k ∈ liveInputs j, k ∈ (θ.cutSet (θ.partOf j))ᶜ := by
    intro k hk
    simp only [Finset.mem_compl]
    intro hmem
    exact h ⟨k, hk, hmem⟩
  have h1 : shift j ∈ (θ.cutSet (θ.partOf j))ᶜ :=
    hlive _ (mem_liveInputs.2 (Or.inl rfl))
  have h2 : shift (shift j) ∈ (θ.cutSet (θ.partOf j))ᶜ :=
    hlive _ (mem_liveInputs.2 (Or.inr rfl))
  rw [effUnit_circNet_of_window_subset _ _ _ _ hj h1 h2, if_pos rfl]

/-- The partitioned effect probability of the state the substrate actually produces is
`(1/2)` to the number of damaged units. -/
lemma sysPartEffProb_circNet (hN : 3 ≤ N) (u s : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartEffProb (circNet N) Finset.univ u θ s (circNext s)
      = (1 / 2 : ℝ) ^ damagedCount θ := by
  classical
  rw [sysPartEffProb, merge_univ]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ s j (circNext s j)
        = if Damaged θ j then (1 / 2 : ℝ) else 1 := by
    intro j _
    by_cases h : Damaged θ j
    · rw [if_pos h]
      exact effUnit_circNet_damaged hN θ s j _ h
    · rw [if_neg h]
      exact effUnit_circNet_undamaged θ s j h
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, damagedCount, damaged]

/-- The unpartitioned effect probability of the produced state is `1`. -/
lemma sysEffProb_circNet (u s : State N) :
    sysEffProb (circNet N) Finset.univ u s (circNext s) = 1 := by
  rw [sysEffProb, merge_univ]
  refine Finset.prod_eq_one fun i _ => ?_
  show (if circNext s i = circVal i s then (1 : ℝ) else 0) = 1
  simp [circNext]

/-- **`φ_E` is the number of damaged units**, at every directional partition, for every
`N ≥ 3`.  This is the reduction of the system level to combinatorics: the analytic content
of `[IIT4, Eqs 17-19]` is discharged once and for all, and what remains is counting
damaged units against `[IIT4, Eq 23]`'s normalizer. -/
theorem sysPhiE_circNet (hN : 3 ≤ N) (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiE (circNet N) Finset.univ u θ s (circNext s) = (damagedCount θ : ℝ) := by
  rw [sysPhiE, sysEffProb_circNet, sysPartEffProb_circNet hN, one_mul]
  have hinv : (((1 : ℝ) / 2) ^ damagedCount θ)⁻¹ = (2 : ℝ) ^ damagedCount θ := by
    rw [one_div, inv_pow, inv_inv]
  rw [div_eq_mul_inv, one_mul, hinv, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos,
    max_eq_right (by positivity)]

end Damage

/-! ## The cause side

`sysPartCauseProb` marginalizes with the *forward* `effUnit`, evaluated at the previous
state, so the very same `Damaged` predicate governs it: a unit whose live inputs survive
the cut is pinned to the state it actually came from, and one whose live input is severed
contributes a half.  Both directions therefore equal `damagedCount`, and `φ_s` at a
partition is that count.

Bijectivity (`3 ∤ N`) is what makes this work: it is what puts the unpartitioned cause
probability at `1` rather than spreading it over a fibre.
-/

section Cause

variable [NeZero N]

/-- The state the circulant came from. -/
noncomputable def circPrev (h3 : ¬ (3 ∣ N)) (s : State N) : State N := (circEquiv N h3).symm s

lemma circNext_circPrev (h3 : ¬ (3 ∣ N)) (s : State N) : circNext (circPrev h3 s) = s :=
  (circEquiv N h3).apply_symm_apply s

lemma circPrev_circNext (h3 : ¬ (3 ∣ N)) (s : State N) : circPrev h3 (circNext s) = s :=
  (circEquiv N h3).symm_apply_apply s

lemma sysEffProb_circNet_eq (u s t : State N) :
    sysEffProb (circNet N) Finset.univ u s t = if t = circNext s then 1 else 0 := by
  by_cases ht : t = circNext s
  · rw [ht, if_pos rfl, sysEffProb_circNet]
  · rw [if_neg ht, sysEffProb, merge_univ]
    have hex : ∃ i, t i ≠ circVal i s := by
      by_contra hall
      push_neg at hall
      exact ht (funext fun i => hall i)
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    show (if t i = circVal i s then (1 : ℝ) else 0) = 0
    rw [if_neg hi]

lemma fullProb_circNet_eq (v t : State N) :
    fullProb (circNet N) v t = if t = circNext v then 1 else 0 := by
  have h := sysEffProb_circNet_eq v v t
  rwa [sysEffProb, merge_univ] at h

lemma sum_fullProb_circNet_pos (h3 : ¬ (3 ∣ N)) (u : State N) :
    0 < ∑ v : State N, fullProb (circNet N) v u := by
  refine Finset.sum_pos' (fun v _ => fullProb_nonneg _ v u)
    ⟨circPrev h3 u, Finset.mem_univ _, ?_⟩
  rw [fullProb_circNet_eq, circNext_circPrev, if_pos rfl]
  norm_num

lemma sysUncEff_circNet (h3 : ¬ (3 ∣ N)) (u t : State N) :
    sysUncEff (circNet N) Finset.univ u t = 1 / 2 ^ N := by
  rw [sysUncEff, avgOverStates]
  have hswap : ∀ s : State N,
      sysEffProb (circNet N) Finset.univ u s t = if s = circPrev h3 t then (1 : ℝ) else 0 := by
    intro s
    rw [sysEffProb_circNet_eq]
    by_cases hs : s = circPrev h3 t
    · subst hs
      simp [circNext_circPrev]
    · rw [if_neg fun ht => hs (by rw [ht, circPrev_circNext]), if_neg hs]
  rw [Finset.sum_congr rfl fun s _ => hswap s,
    Fintype.sum_ite_eq' (circPrev h3 t) fun _ => (1 : ℝ)]

lemma sysCauseProb_circNet (h3 : ¬ (3 ∣ N)) (u s t : State N) :
    sysCauseProb (circNet N) Finset.univ u s t = if t = circPrev h3 s then 1 else 0 := by
  rw [sysCauseProb_univ _ _ _ _ (sum_fullProb_circNet_pos h3 u), fullProb_circNet_eq]
  congr 1
  apply propext
  constructor
  · rintro rfl; rw [circPrev_circNext]
  · rintro rfl; rw [circNext_circPrev]

lemma sysUncCause_circNet (h3 : ¬ (3 ∣ N)) (u s : State N) :
    sysUncCause (circNet N) Finset.univ u s = 1 / 2 ^ N := by
  rw [sysUncCause, avgOverStates,
    Finset.sum_congr rfl fun t _ => sysCauseProb_circNet h3 u s t,
    Fintype.sum_ite_eq' (circPrev h3 s) fun _ => (1 : ℝ)]

lemma sysPartCauseProb_circNet_univ (h3 : ¬ (3 ∣ N)) (u s t : State N) (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (circNet N) Finset.univ u θ s t
      = ∏ j, effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ t j (s j) := by
  rw [sysPartCauseProb]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
    rw [bgWeight_univ _ _ _ (sum_fullProb_circNet_pos h3 u), mul_one, merge_univ]]
  rw [Finset.sum_const, card_state, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The partitioned cause probability at the state the substrate actually came from is
again a half for each damaged unit. -/
lemma sysPartCauseProb_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (circNet N) Finset.univ u θ s (circPrev h3 s)
      = (1 / 2 : ℝ) ^ damagedCount θ := by
  classical
  rw [sysPartCauseProb_circNet_univ h3]
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      effUnit (circNet N) (θ.cutSet (θ.partOf j))ᶜ (circPrev h3 s) j (s j)
        = if Damaged θ j then (1 / 2 : ℝ) else 1 := by
    intro j _
    by_cases h : Damaged θ j
    · rw [if_pos h]
      exact effUnit_circNet_damaged hN θ (circPrev h3 s) j _ h
    · rw [if_neg h]
      have hval : circVal j (circPrev h3 s) = s j := congrFun (circNext_circPrev h3 s) j
      have := effUnit_circNet_undamaged θ (circPrev h3 s) j h
      rwa [hval] at this
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, damagedCount, damaged]

private lemma pos_logb_half_pow' (m : ℕ) :
    pos (Real.logb 2 (1 / (1 / 2 : ℝ) ^ m)) = m := by
  rw [div_pow, one_pow, one_div_one_div, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos, max_eq_right (Nat.cast_nonneg m)]

/-- **`φ_C` is also the number of damaged units.** -/
theorem sysPhiC_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiC (circNet N) Finset.univ u θ s (circPrev h3 s) = (damagedCount θ : ℝ) := by
  rw [sysPhiC, sysBackCause, sysCauseProb_circNet h3, if_pos rfl, sysUncCause_circNet h3,
    Finset.card_univ, Fintype.card_fin]
  have hback : (1 : ℝ) / ((2 : ℝ) ^ N * (1 / 2 ^ N)) = 1 := by
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  rw [hback, one_mul, sysPartCauseProb_circNet h3 hN, pos_logb_half_pow']

/-- **Both directions agree**, so `φ_s` at a partition is exactly the number of damaged
units.  With this the system level of the circulant is entirely combinatorial: only
`damagedCount` and `[IIT4, Eq 23]`'s normalizer remain. -/
theorem sysPhiAt_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiAt (circNet N) Finset.univ u θ s (circPrev h3 s) (circNext s)
      = (damagedCount θ : ℝ) := by
  rw [sysPhiAt, sysPhiC_circNet h3 hN, sysPhiE_circNet hN, min_self]

end Cause

/-! ## From a partition to `φ_s`

The maximal cause and effect states are unique -- the substrate is deterministic and
bijective, so exactly one state is produced and exactly one produced it -- which collapses
the tie-handling of `[IIT4, Eq 22]` and `[IIT4, S1 Text]`.  What is left is the statement
that `φ_s` is the largest damaged count over the minimum information partitions.
-/

section Assembly

variable [NeZero N]

lemma sysIiE_circNet (h3 : ¬ (3 ∣ N)) (u s t : State N) :
    sysIiE (circNet N) Finset.univ u s t = if t = circNext s then (N : ℝ) else 0 := by
  rw [sysIiE, sysEffProb_circNet_eq, sysUncEff_circNet h3]
  by_cases ht : t = circNext s
  · rw [if_pos ht, if_pos ht, one_mul, one_div_one_div, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]
  · rw [if_neg ht, if_neg ht, zero_mul]

lemma sysIiC_circNet (h3 : ¬ (3 ∣ N)) (u s t : State N) :
    sysIiC (circNet N) Finset.univ u s t = if t = circPrev h3 s then (N : ℝ) else 0 := by
  rw [sysIiC, sysBackCause, sysCauseProb_circNet h3, sysUncCause_circNet h3,
    Finset.card_univ, Fintype.card_fin]
  by_cases ht : t = circPrev h3 s
  · rw [if_pos ht, if_pos ht]
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    rw [show (1 : ℝ) / ((2 : ℝ) ^ N * (1 / 2 ^ N)) = 1 by field_simp, one_mul,
      one_div_one_div, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  · rw [if_neg ht, if_neg ht, zero_div, zero_mul]

lemma sysMaxEffStates_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) :
    sysMaxEffStates (circNet N) Finset.univ u s = {circNext s} := by
  have hNpos : (0 : ℝ) < N := by
    have h : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun t ht => ?_⟩
  · rw [sysMaxEffStates, argmaxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun t => ?_⟩
    rw [sysIiE_circNet h3, sysIiE_circNet h3, if_pos rfl]
    split
    · exact le_refl _
    · exact Nat.cast_nonneg N
  · rw [sysMaxEffStates, mem_argmaxSet] at ht
    have h := ht (circNext s)
    rw [sysIiE_circNet h3, sysIiE_circNet h3, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    linarith

lemma sysMaxCauseStates_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) :
    sysMaxCauseStates (circNet N) Finset.univ u s = {circPrev h3 s} := by
  have hNpos : (0 : ℝ) < N := by
    have h : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun t ht => ?_⟩
  · rw [sysMaxCauseStates, argmaxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun t => ?_⟩
    rw [sysIiC_circNet h3, sysIiC_circNet h3, if_pos rfl]
    split
    · exact le_refl _
    · exact Nat.cast_nonneg N
  · rw [sysMaxCauseStates, mem_argmaxSet] at ht
    have h := ht (circPrev h3 s)
    rw [sysIiC_circNet h3, sysIiC_circNet h3, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    linarith

/-- The normalized quantity `[IIT4, Eq 23]` minimizes, in combinatorial form. -/
lemma normalizedSysPhiAt_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N)
    (θ : SysPartition N Finset.univ) :
    normalizedSysPhiAt (circNet N) Finset.univ u θ s (circPrev h3 s) (circNext s)
      = (damagedCount θ : ℝ) / (sysCutCount θ : ℝ) := by
  rw [normalizedSysPhiAt, sysPhiAt_circNet h3 hN]

/-- **`φ_s` is the largest damaged count over the minimum information partitions.**

Everything analytic is now gone: `[IIT4, Eqs 14-23]` for this substrate is the statement
that one maximizes `damagedCount` over the partitions minimizing
`damagedCount / sysCutCount`. -/
theorem sysPhi_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) :
    sysPhi (circNet N) Finset.univ u s
      = sup'OrZero (argminSet fun θ : SysPartition N Finset.univ =>
            (damagedCount θ : ℝ) / (sysCutCount θ : ℝ))
          fun θ => (damagedCount θ : ℝ) := by
  rw [sysPhi, sysMaxCauseStates_circNet h3 hN, sysMaxEffStates_circNet h3 hN,
    Finset.singleton_product_singleton]
  have hne : ({(circPrev h3 s, circNext s)} : Finset (State N × State N)).Nonempty :=
    ⟨_, Finset.mem_singleton_self _⟩
  rw [sup'OrZero, dif_pos hne, Finset.sup'_singleton, sysPhiOfState, sysMipSetAt]
  exact sup'OrZero_argminSet_congr (fun θ => normalizedSysPhiAt_circNet h3 hN u s θ)
    (fun θ => sysPhiAt_circNet h3 hN u s θ)

end Assembly

/-! ## Damage is never zero

A block closed under the shift is everything, because the shift generates the cycle.  That
single fact gives the floor `1 ≤ damagedCount`, and it is the seed of the finer counting
that the exclusion bounds need: a block whose cut set is its own complement always loses
at least one unit, and an arc loses its last two.
-/

section Floor

variable [NeZero N]

/-- **A nonempty block closed under the shift is the whole substrate.** -/
lemma eq_univ_of_shift_closed {p : Finset (Fin N)} (hne : p.Nonempty)
    (hcl : ∀ j ∈ p, shift j ∈ p) : p = Finset.univ := by
  obtain ⟨j, hj⟩ := hne
  have hiter : ∀ m : ℕ, shift^[m] j ∈ p := by
    intro m
    induction m with
    | zero => simpa using hj
    | succ q ih =>
        rw [Function.iterate_succ_apply']
        exact hcl _ ih
  refine Finset.eq_univ_of_forall fun a => ?_
  obtain ⟨m, hm⟩ := exists_iterate_shift a j
  rw [← hm]
  exact hiter m

/-- A block whose cut set is its own complement damages one of its own units: otherwise it
would be closed under the shift, hence everything, contradicting `k ≥ 2`. -/
lemma exists_damaged_of_cutSet_compl (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) :
    ∃ j ∈ p, Damaged θ j := by
  by_contra hcon
  push_neg at hcon
  have hcl : ∀ j ∈ p, shift j ∈ p := by
    intro j hj
    by_contra hns
    refine hcon j hj ⟨shift j, mem_liveInputs.2 (Or.inl rfl), ?_⟩
    rw [θ.partOf_eq hp hj, hcut]
    simpa using hns
  have huniv : p = Finset.univ := eq_univ_of_shift_closed (θ.parts_nonempty p hp) hcl
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p := by
    by_contra hc
    push_neg at hc
    have hsub : θ.parts ⊆ {p} := fun r hr => Finset.mem_singleton.2 (hc r hr)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    have := θ.two_le
    omega
  obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
  exact absurd (huniv ▸ Finset.mem_univ j)
    (Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hj)

/-- **At least one unit is always damaged.**

Either some block severs its inputs, in which case its cut set is its own complement, or
every block severs only its outputs, in which case each block's cut set is the union of all
the others, again its complement.  Either way `exists_damaged_of_cutSet_compl` applies. -/
theorem one_le_damagedCount (θ : SysPartition N Finset.univ) : 1 ≤ damagedCount θ := by
  classical
  have hex : ∃ j, Damaged θ j := by
    by_cases hall : ∀ p ∈ θ.parts, θ.dir p = Dir.outputs
    · obtain ⟨p, hp⟩ : θ.parts.Nonempty := by
        rw [← Finset.card_pos]
        have := θ.two_le
        omega
      have hcut : θ.cutSet p = pᶜ := by
        rw [SysPartition.cutSet, hall p hp]
        ext x
        simp only [Finset.mem_sup, Finset.mem_filter, Finset.mem_compl, id]
        constructor
        · rintro ⟨q, ⟨hq, hqp, -⟩, hxq⟩
          exact Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hxq
        · intro hx
          obtain ⟨q, hq, hxq⟩ := θ.parts_cover x (Finset.mem_univ x)
          refine ⟨q, ⟨hq, ?_, Or.inl (hall q hq)⟩, hxq⟩
          rintro rfl
          exact hx hxq
      obtain ⟨j, -, hj⟩ := exists_damaged_of_cutSet_compl θ hp hcut
      exact ⟨j, hj⟩
    · push_neg at hall
      obtain ⟨p, hp, hd⟩ := hall
      have hcut : θ.cutSet p = pᶜ := by
        rw [SysPartition.cutSet]
        cases hdp : θ.dir p
        · ext x; simp [Finset.mem_sdiff]
        · exact absurd hdp hd
        · ext x; simp [Finset.mem_sdiff]
      obtain ⟨j, -, hj⟩ := exists_damaged_of_cutSet_compl θ hp hcut
      exact ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  rw [damagedCount, damaged, Finset.one_le_card]
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩⟩

end Floor

/-! ## Blocks that sever their inputs damage two units unless they are singletons

This is the counting step behind the exclusion bounds.  A block whose cut set is its own
complement loses its "arc ends"; and if it has at least two units, the unit *before* an arc
end loses its second live input, giving a second damaged unit.  Only a singleton escapes
with one.
-/

section Pairs

variable [NeZero N]

/-- For a block whose cut set is its complement, damage is exactly "some live input leaves
the block". -/
lemma damaged_iff_of_cutSet_compl (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) {j : Fin N}
    (hj : j ∈ p) : Damaged θ j ↔ (shift j ∉ p ∨ shift (shift j) ∉ p) := by
  unfold Damaged
  rw [θ.partOf_eq hp hj, hcut]
  constructor
  · rintro ⟨k, hk, hkc⟩
    rcases mem_liveInputs.1 hk with rfl | rfl
    · exact Or.inl (by simpa using hkc)
    · exact Or.inr (by simpa using hkc)
  · rintro (h | h)
    · exact ⟨shift j, mem_liveInputs.2 (Or.inl rfl), by simpa using h⟩
    · exact ⟨shift (shift j), mem_liveInputs.2 (Or.inr rfl), by simpa using h⟩

/-- **A block severing its inputs damages two distinct units once it has two units.**

Some unit `y` of the block has `shift y` outside it, or the block would be shift-closed and
hence everything.  If some `w` of the block shifts *to* `y`, then `w`'s second live input
`shift (shift w) = shift y` is outside, so `w` is damaged too.  Otherwise `y` is the only
unit shifting out, and removing it leaves a nonempty shift-closed set, again everything. -/
theorem two_le_damaged_of_cutSet_compl (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) (hcard : 2 ≤ p.card) :
    ∃ j₁ ∈ p, ∃ j₂ ∈ p, j₁ ≠ j₂ ∧ Damaged θ j₁ ∧ Damaged θ j₂ := by
  classical
  have hpne : p.Nonempty := Finset.card_pos.1 (by omega)
  have hpuniv : p ≠ Finset.univ := by
    intro huniv
    obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p := by
      by_contra hc
      push_neg at hc
      have hsub : θ.parts ⊆ {p} := fun r hr => Finset.mem_singleton.2 (hc r hr)
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      have := θ.two_le
      omega
    obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
    exact absurd (huniv ▸ Finset.mem_univ j)
      (Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hj)
  obtain ⟨y, hyp, hyout⟩ : ∃ y ∈ p, shift y ∉ p := by
    by_contra hc
    push_neg at hc
    exact hpuniv (eq_univ_of_shift_closed hpne hc)
  have hydam : Damaged θ y :=
    (damaged_iff_of_cutSet_compl θ hp hcut hyp).2 (Or.inl hyout)
  by_cases hw : ∃ w ∈ p, shift w = y
  · obtain ⟨w, hwp, hwy⟩ := hw
    have hne : w ≠ y := by
      rintro rfl
      have hmem : shift w ∈ p := by rw [hwy]; exact hwp
      exact hyout hmem
    refine ⟨y, hyp, w, hwp, Ne.symm hne, hydam, ?_⟩
    refine (damaged_iff_of_cutSet_compl θ hp hcut hwp).2 (Or.inr ?_)
    rw [hwy]
    exact hyout
  · push_neg at hw
    by_cases hy2 : ∃ y' ∈ p, y' ≠ y ∧ shift y' ∉ p
    · obtain ⟨y', hy'p, hy'ne, hy'out⟩ := hy2
      exact ⟨y, hyp, y', hy'p, Ne.symm hy'ne, hydam,
        (damaged_iff_of_cutSet_compl θ hp hcut hy'p).2 (Or.inl hy'out)⟩
    · push_neg at hy2
      exfalso
      have hcl : ∀ j ∈ p.erase y, shift j ∈ p.erase y := by
        intro j hj
        obtain ⟨hjy, hjp⟩ := Finset.mem_erase.1 hj
        have hin : shift j ∈ p := hy2 j hjp hjy
        exact Finset.mem_erase.2 ⟨fun hcon => hw j hjp hcon, hin⟩
      have hne : (p.erase y).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hyp]
        omega
      have huniv := eq_univ_of_shift_closed hne hcl
      have hymem : y ∈ p.erase y := huniv ▸ Finset.mem_univ y
      exact (Finset.mem_erase.1 hymem).1 rfl

end Pairs

/-! ## The `D = 1` classification

A partition damaging exactly one unit is forced into a single shape: one singleton block
severing its inputs, and at most one block severing its outputs (whose cut set is then
empty).  Hence its normalizer is exactly `N - 1`.

Two structural facts do the work.  A block severing its inputs has its own complement as
cut set, so it damages at least one of its own units; and `shift` is injective, so at most
one unit of the substrate can shift into a given singleton -- which forces any second
outputs block to be shift-closed, hence everything.
-/

section DOne

variable [NeZero N]

/-- Severing a block's inputs cuts it off from everything else. -/
lemma cutSet_eq_compl_of_dir (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hd : θ.dir p = Dir.inputs ∨ θ.dir p = Dir.both) : θ.cutSet p = pᶜ := by
  rw [SysPartition.cutSet]
  rcases hd with h | h <;> rw [h] <;> · ext x; simp [Finset.mem_sdiff]

/-- If every block severs its outputs, each block's cut set is again its complement. -/
lemma cutSet_eq_compl_of_all_outputs (θ : SysPartition N Finset.univ)
    (hall : ∀ q ∈ θ.parts, θ.dir q = Dir.outputs) {p : Finset (Fin N)} (hp : p ∈ θ.parts) :
    θ.cutSet p = pᶜ := by
  rw [SysPartition.cutSet, hall p hp]
  ext x
  simp only [Finset.mem_sup, Finset.mem_filter, Finset.mem_compl, id]
  constructor
  · rintro ⟨q, ⟨hq, hqp, -⟩, hxq⟩
    exact Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hxq
  · intro hx
    obtain ⟨q, hq, hxq⟩ := θ.parts_cover x (Finset.mem_univ x)
    refine ⟨q, ⟨hq, ?_, Or.inl (hall q hq)⟩, hxq⟩
    rintro rfl
    exact hx hxq

/-- Damaged units of distinct blocks are distinct, so each block with a complement cut set
contributes its own damaged unit to the total. -/
lemma card_le_damagedCount_of_forall_compl (θ : SysPartition N Finset.univ)
    {B : Finset (Finset (Fin N))} (hB : B ⊆ θ.parts)
    (hcut : ∀ p ∈ B, θ.cutSet p = pᶜ) : B.card ≤ damagedCount θ := by
  classical
  choose! f hf using fun p (hp : p ∈ B) =>
    exists_damaged_of_cutSet_compl θ (hB hp) (hcut p hp)
  have hinj : ∀ p ∈ B, ∀ q ∈ B, f p = f q → p = q := by
    intro p hp q hq hfe
    by_contra hpq
    have h1 := (hf p hp).1
    have h2 := (hf q hq).1
    rw [hfe] at h1
    exact Finset.disjoint_left.1 (θ.parts_disjoint p (hB hp) q (hB hq) hpq) (hfe ▸ h1) h2
  have hmaps : ∀ p ∈ B, f p ∈ damaged θ := by
    intro p hp
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hf p hp).2⟩
  rw [damagedCount]
  exact Finset.card_le_card_of_injOn f hmaps hinj

end DOne

/-! ## Existence

Every directional partition damages at least one unit, so the value at the minimum
information partition is at least one: `φ_s ≥ 1` for the whole substrate, at every state,
for every valid `N`.  With `circ_strongly_connected` this discharges `[IIT4]`'s existence
postulate exactly as `[IIT4, p.18]` demands.
-/

section Existence

variable [NeZero N]

theorem one_le_sysPhi_circNet (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) :
    1 ≤ sysPhi (circNet N) Finset.univ u s := by
  classical
  rw [sysPhi_circNet h3 hN]
  have : Nonempty (SysPartition N Finset.univ) := ⟨singletonParts (by omega)⟩
  obtain ⟨θ, hθ⟩ := argminSet_nonempty
    (fun θ : SysPartition N Finset.univ => (damagedCount θ : ℝ) / (sysCutCount θ : ℝ))
  refine le_trans ?_ (le_sup'OrZero hθ)
  exact_mod_cast one_le_damagedCount θ

/-- **Existence** `[IIT4, Eq 14ff]`: the window-3 circulant has strictly positive system
integrated information, for every `N ≥ 3` with `3 ∤ N`, in every state. -/
theorem sysPhi_circNet_pos (h3 : ¬ (3 ∣ N)) (hN : 3 ≤ N) (u s : State N) :
    0 < sysPhi (circNet N) Finset.univ u s :=
  lt_of_lt_of_le zero_lt_one (one_le_sysPhi_circNet h3 hN u s)

end Existence

/-! ## The `D = 1` classification

A partition damaging exactly one unit is forced into a single shape: one **singleton**
block severing its inputs, together with exactly one block severing its outputs, whose cut
set is then empty.  Its normalizer is therefore exactly `N - 1`.
-/

section DOneClass

variable [NeZero N]

/-- The shift is injective. -/
lemma shift_injective : Function.Injective (shift : Fin N → Fin N) := by
  intro a b hab
  have hva := congrArg Fin.val hab
  rw [shift_val, shift_val] at hva
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  by_cases hA : a.val + 1 = N <;> by_cases hB : b.val + 1 = N
  · omega
  · rw [hA, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hva; omega
  · rw [hB, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hva; omega
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hva; omega

/-- No block is the whole substrate, since there are at least two of them. -/
lemma block_ne_univ (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) : p ≠ Finset.univ := by
  intro huniv
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p := by
    by_contra hc
    push_neg at hc
    have hsub : θ.parts ⊆ {p} := fun r hr => Finset.mem_singleton.2 (hc r hr)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    have := θ.two_le
    omega
  obtain ⟨j, hj⟩ := θ.parts_nonempty q hq
  exact absurd (huniv ▸ Finset.mem_univ j)
    (Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hj)

/-- A unit lies in the cut set of another block whenever its own block is a third one that
severs its outputs. -/
lemma mem_cutSet_of_mem_other (θ : SysPartition N Finset.univ) {q r : Finset (Fin N)}
    (hr : r ∈ θ.parts) (hrq : r ≠ q) (hdr : θ.dir r = Dir.outputs)
    (hdq : θ.dir q = Dir.outputs) {x : Fin N} (hx : x ∈ r) : x ∈ θ.cutSet q := by
  rw [SysPartition.cutSet, hdq]
  exact Finset.mem_sup.2 ⟨r, Finset.mem_filter.2 ⟨hr, hrq, Or.inl hdr⟩, hx⟩

lemma mem_cutSet_of_mem_both (θ : SysPartition N Finset.univ) {q r : Finset (Fin N)}
    (hr : r ∈ θ.parts) (hrq : r ≠ q) (hdr : θ.dir r = Dir.both)
    (hdq : θ.dir q = Dir.outputs) {x : Fin N} (hx : x ∈ r) : x ∈ θ.cutSet q := by
  rw [SysPartition.cutSet, hdq]
  exact Finset.mem_sup.2 ⟨r, Finset.mem_filter.2 ⟨hr, hrq, Or.inr hdr⟩, hx⟩

end DOneClass

section DOneMain

variable [NeZero N]

/-- **The `D = 1` classification.**  A partition damaging exactly one unit is a singleton
block severing its inputs together with exactly one block severing its outputs, whose cut
set is then empty.  So its normalizer is exactly `N - 1`, and its normalized value is
`1 / (N - 1)`. -/
theorem sysCutCount_eq_of_damagedCount_one (hN : 3 ≤ N) (θ : SysPartition N Finset.univ)
    (hD : damagedCount θ = 1) : sysCutCount θ = N - 1 := by
  classical
  -- (1) some block severs its inputs
  have hnotall : ¬ (∀ q ∈ θ.parts, θ.dir q = Dir.outputs) := by
    intro hall
    have hle := card_le_damagedCount_of_forall_compl θ (Finset.Subset.refl _)
      (fun p hp => cutSet_eq_compl_of_all_outputs θ hall hp)
    have := θ.two_le
    omega
  push_neg at hnotall
  obtain ⟨p₀, hp₀, hdir₀⟩ := hnotall
  have hd₀ : θ.dir p₀ = Dir.inputs ∨ θ.dir p₀ = Dir.both := by
    cases h : θ.dir p₀
    · exact Or.inl rfl
    · exact absurd h hdir₀
    · exact Or.inr rfl
  have hcut₀ : θ.cutSet p₀ = p₀ᶜ := cutSet_eq_compl_of_dir θ hd₀
  -- (2) it is a singleton
  have hsingle : p₀.card = 1 := by
    by_contra hne
    have h2 : 2 ≤ p₀.card := by
      have := Finset.card_pos.2 (θ.parts_nonempty p₀ hp₀)
      omega
    obtain ⟨j₁, hj₁, j₂, hj₂, hne12, hd1, hd2⟩ :=
      two_le_damaged_of_cutSet_compl θ hp₀ hcut₀ h2
    have hsub : ({j₁, j₂} : Finset (Fin N)) ⊆ damaged θ := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hd1⟩
      · rw [Finset.mem_singleton] at hx'
        subst hx'
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hd2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hne12), Finset.card_singleton] at hcard
    rw [damagedCount] at hD
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hsingle
  -- (3) `b` is the damaged unit, so every unit outside `p₀` is undamaged
  have hbmem : b ∈ p₀ := by rw [hb]; exact Finset.mem_singleton_self b
  have hbdam : Damaged θ b := by
    refine ⟨shift b, mem_liveInputs.2 (Or.inl rfl), ?_⟩
    rw [θ.partOf_eq hp₀ hbmem, hcut₀, hb]
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact shift_ne_self hN b
  have hdam_eq : damaged θ = {b} := by
    have hbin : b ∈ damaged θ := Finset.mem_filter.2 ⟨Finset.mem_univ _, hbdam⟩
    have : ({b} : Finset (Fin N)) ⊆ damaged θ := by
      intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hbin
    exact (Finset.eq_of_subset_of_card_le this (by rw [Finset.card_singleton, ← damagedCount, hD])).symm
  have hundam : ∀ j : Fin N, j ≠ b → ¬ Damaged θ j := by
    intro j hj hcon
    have : j ∈ damaged θ := Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩
    rw [hdam_eq, Finset.mem_singleton] at this
    exact hj this
  -- (4) every other block severs its outputs
  have hother : ∀ q ∈ θ.parts, q ≠ p₀ → θ.dir q = Dir.outputs := by
    intro q hq hqp
    by_contra hdq
    have hdq' : θ.dir q = Dir.inputs ∨ θ.dir q = Dir.both := by
      cases h : θ.dir q
      · exact Or.inl rfl
      · exact absurd h hdq
      · exact Or.inr rfl
    have hle := card_le_damagedCount_of_forall_compl θ (B := {p₀, q})
      (by
        intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr'
        · exact hp₀
        · rw [Finset.mem_singleton] at hr'; subst hr'; exact hq)
      (by
        intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr'
        · exact hcut₀
        · rw [Finset.mem_singleton] at hr'; subst hr'
          exact cutSet_eq_compl_of_dir θ hdq')
    rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hqp),
      Finset.card_singleton, hD] at hle
    omega
  -- (5) for a block other than `p₀`, the shift stays inside it or lands on `b`
  have hstep : ∀ q ∈ θ.parts, q ≠ p₀ → ∀ j ∈ q, shift j ∈ q ∨ shift j = b := by
    intro q hq hqp j hj
    by_contra hcon
    push_neg at hcon
    obtain ⟨hnq, hnb⟩ := hcon
    obtain ⟨r, hr, hjr⟩ := θ.parts_cover (shift j) (Finset.mem_univ _)
    have hrq : r ≠ q := by rintro rfl; exact hnq hjr
    have hrp : r ≠ p₀ := by
      rintro rfl
      rw [hb, Finset.mem_singleton] at hjr
      exact hnb hjr
    have hmem : shift j ∈ θ.cutSet q :=
      mem_cutSet_of_mem_other θ hr hrq (hother r hr hrp) (hother q hq hqp) hjr
    have hjb : j ≠ b := by
      rintro rfl
      exact hqp (by
        have := Finset.disjoint_left.1 (θ.parts_disjoint q hq p₀ hp₀ hqp) hj
        exact absurd hbmem this)
    exact hundam j hjb ⟨shift j, mem_liveInputs.2 (Or.inl rfl), by
      rwa [θ.partOf_eq hq hj]⟩
  -- (6) `p₀` severs its inputs, not both: otherwise no other block could exist
  have hdirin : θ.dir p₀ = Dir.inputs := by
    rcases hd₀ with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p₀ := by
        by_contra hc
        push_neg at hc
        have hsub : θ.parts ⊆ {p₀} := fun r hr => Finset.mem_singleton.2 (hc r hr)
        have hle := Finset.card_le_card hsub
        rw [Finset.card_singleton] at hle
        have := θ.two_le
        omega
      have hcl : ∀ j ∈ q, shift j ∈ q := by
        intro j hj
        rcases hstep q hq hqp j hj with hin | hbj
        · exact hin
        · exfalso
          have hjb : j ≠ b := by
            rintro rfl
            exact absurd hbmem (Finset.disjoint_left.1
              (θ.parts_disjoint q hq p₀ hp₀ hqp) hj)
          refine hundam j hjb ⟨shift j, mem_liveInputs.2 (Or.inl rfl), ?_⟩
          rw [θ.partOf_eq hq hj]
          exact mem_cutSet_of_mem_both θ hp₀ (Ne.symm hqp) h (hother q hq hqp)
            (by rw [hbj]; exact hbmem)
      exact block_ne_univ θ hq (eq_univ_of_shift_closed (θ.parts_nonempty q hq) hcl)
  -- (7) exactly one other block, and it is everything but `b`
  have hcontains : ∀ q ∈ θ.parts, q ≠ p₀ → ∃ w ∈ q, shift w = b := by
    intro q hq hqp
    by_contra hc
    push_neg at hc
    have hcl : ∀ j ∈ q, shift j ∈ q := by
      intro j hj
      rcases hstep q hq hqp j hj with hin | hbj
      · exact hin
      · exact absurd hbj (hc j hj)
    exact block_ne_univ θ hq (eq_univ_of_shift_closed (θ.parts_nonempty q hq) hcl)
  have huniq : ∀ q₁ ∈ θ.parts, q₁ ≠ p₀ → ∀ q₂ ∈ θ.parts, q₂ ≠ p₀ → q₁ = q₂ := by
    intro q₁ hq₁ hqp₁ q₂ hq₂ hqp₂
    by_contra hne
    obtain ⟨w₁, hw₁, hs₁⟩ := hcontains q₁ hq₁ hqp₁
    obtain ⟨w₂, hw₂, hs₂⟩ := hcontains q₂ hq₂ hqp₂
    have : w₁ = w₂ := shift_injective (by rw [hs₁, hs₂])
    subst this
    exact Finset.disjoint_left.1 (θ.parts_disjoint q₁ hq₁ q₂ hq₂ hne) hw₁ hw₂
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ θ.parts, q ≠ p₀ := by
    by_contra hc
    push_neg at hc
    have hsub : θ.parts ⊆ {p₀} := fun r hr => Finset.mem_singleton.2 (hc r hr)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    have := θ.two_le
    omega
  have hparts : θ.parts = {p₀, q} := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hrp : r = p₀
      · subst hrp; exact Finset.mem_insert_self _ _
      · rw [huniq r hr hrp q hq hqp]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · exact hp₀
      · rw [Finset.mem_singleton] at hr'; subst hr'; exact hq
  -- (8) the outputs block has empty cut set
  have hcutq : θ.cutSet q = ∅ := by
    rw [SysPartition.cutSet, hother q hq hqp]
    have hfil : (θ.parts.filter
        fun r => r ≠ q ∧ (θ.dir r = Dir.outputs ∨ θ.dir r = Dir.both)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r hr
      rw [hparts] at hr
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · rintro ⟨-, hd⟩
        rw [hdirin] at hd
        rcases hd with h | h <;> exact absurd h (by decide)
      · rw [Finset.mem_singleton] at hr'
        subst hr'
        rintro ⟨hne, -⟩
        exact hne rfl
    rw [hfil]
    exact Finset.sup_empty
  -- (9) the normalizer is `1 * (N - 1)`
  rw [sysCutCount, hparts, Finset.sum_insert (by simpa using Ne.symm hqp),
    Finset.sum_singleton, hcutq, Finset.card_empty, mul_zero, add_zero, hcut₀,
    Finset.card_compl, Fintype.card_fin, hsingle, one_mul]

end DOneMain

/-! ## The exact damage count of a block

For a block whose cut set is its own complement, the damaged units split as a **disjoint
union**: the *exit points* (units whose successor leaves the block) together with those
units whose successor is itself an exit point.  Counting runs, this is
`Σ over maximal runs of min(runlength, 2)` -- but no run decomposition is needed to state
or prove it, which is what makes it usable.

The disjointness is the crux: an exit point has its successor outside the block, while a
predecessor-of-an-exit-point has its successor inside it, so nothing is double counted.
-/

section ExactDamage

variable [NeZero N]

/-- The units of `p` whose successor leaves `p`: one per maximal run. -/
def exitSet (p : Finset (Fin N)) : Finset (Fin N) := p.filter fun j => shift j ∉ p

lemma mem_exitSet {p : Finset (Fin N)} {j : Fin N} :
    j ∈ exitSet p ↔ j ∈ p ∧ shift j ∉ p := by
  unfold exitSet
  simp

/-- The units of `p` whose successor is an exit point: one per run of length `≥ 2`. -/
def preExitSet (p : Finset (Fin N)) : Finset (Fin N) := p.filter fun j => shift j ∈ exitSet p

lemma mem_preExitSet {p : Finset (Fin N)} {j : Fin N} :
    j ∈ preExitSet p ↔ j ∈ p ∧ shift j ∈ exitSet p := by
  unfold preExitSet
  simp

/-- Exit points and pre-exit points are disjoint. -/
lemma exitSet_disjoint_preExitSet (p : Finset (Fin N)) :
    Disjoint (exitSet p) (preExitSet p) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact (mem_exitSet.1 hj).2 (mem_exitSet.1 (mem_preExitSet.1 hj').2).1

/-- **The damaged units of a block, exactly.** -/
theorem damaged_inter_eq (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) :
    damaged θ ∩ p = exitSet p ∪ preExitSet p := by
  classical
  ext j
  simp only [Finset.mem_inter, Finset.mem_union, damaged, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hdam, hjp⟩
    rcases (damaged_iff_of_cutSet_compl θ hp hcut hjp).1 hdam with h1 | h2
    · exact Or.inl (mem_exitSet.2 ⟨hjp, h1⟩)
    · by_cases hs : shift j ∈ p
      · exact Or.inr (mem_preExitSet.2 ⟨hjp, mem_exitSet.2 ⟨hs, h2⟩⟩)
      · exact Or.inl (mem_exitSet.2 ⟨hjp, hs⟩)
  · rintro (hin | hin)
    · obtain ⟨hjp, hout⟩ := mem_exitSet.1 hin
      exact ⟨(damaged_iff_of_cutSet_compl θ hp hcut hjp).2 (Or.inl hout), hjp⟩
    · obtain ⟨hjp, hex⟩ := mem_preExitSet.1 hin
      exact ⟨(damaged_iff_of_cutSet_compl θ hp hcut hjp).2
        (Or.inr (mem_exitSet.1 hex).2), hjp⟩

/-- **The damage count of a block, exactly**: exit points plus pre-exit points. -/
theorem card_damaged_inter (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) (hcut : θ.cutSet p = pᶜ) :
    (damaged θ ∩ p).card = (exitSet p).card + (preExitSet p).card := by
  rw [damaged_inter_eq θ hp hcut,
    Finset.card_union_of_disjoint (exitSet_disjoint_preExitSet p)]

/-- A nonempty proper block has at least one exit point. -/
lemma exitSet_nonempty (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) : (exitSet p).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hcl : ∀ j ∈ p, shift j ∈ p := by
    intro j hj
    by_contra hout
    exact absurd (mem_exitSet.2 ⟨hj, hout⟩) (by rw [hemp]; simp)
  exact block_ne_univ θ hp (eq_univ_of_shift_closed (θ.parts_nonempty p hp) hcl)

/-- **A block with a run of length `≥ 2` has a pre-exit point**, hence damage `≥ 2`.
Together with `exitSet_nonempty` this recovers `two_le_damaged_of_cutSet_compl`
quantitatively. -/
lemma preExitSet_nonempty_of_shift_mem (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} {y : Fin N} (hy : y ∈ exitSet p) (hw : ∃ w ∈ p, shift w = y) :
    (preExitSet p).Nonempty := by
  obtain ⟨w, hwp, hwy⟩ := hw
  exact ⟨w, mem_preExitSet.2 ⟨hwp, by rw [hwy]; exact hy⟩⟩

end ExactDamage

/-! ## Towards the `D = 2` bound

Two ingredients.  First an arithmetic fact: a block and its complement have product at
most `N²/4`, so a *single* block severing its inputs can never contribute more than that
to `[IIT4, Eq 23]`'s normalizer.  Second, the all-outputs configuration cannot damage
exactly two units, which removes the one shape whose normalizer could otherwise reach
`N²/2`.
-/

section DTwo

variable [NeZero N]

/-- `4·x·y ≤ (x+y)²`, i.e. AM-GM in `ℕ`. -/
lemma four_mul_le_sq (x y : ℕ) : 4 * (x * y) ≤ (x + y) * (x + y) := by
  have hz : (4 : ℤ) * ((x : ℤ) * (y : ℤ)) ≤ ((x : ℤ) + (y : ℤ)) * ((x : ℤ) + (y : ℤ)) := by
    nlinarith [sq_nonneg ((x : ℤ) - (y : ℤ))]
  exact_mod_cast hz

/-- **A block's normalizer contribution is at most `N²/4`.** -/
theorem card_mul_compl_le (p : Finset (Fin N)) :
    4 * (p.card * pᶜ.card) ≤ N * N := by
  have hsum : p.card + pᶜ.card = N := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h := Finset.card_le_univ p
    rw [Fintype.card_fin] at h
    omega
  calc 4 * (p.card * pᶜ.card) ≤ (p.card + pᶜ.card) * (p.card + pᶜ.card) :=
        four_mul_le_sq _ _
    _ = N * N := by rw [hsum]

/-- **The all-outputs configuration never damages exactly two units.**

Every block then has its own complement as cut set, so each damages at least one unit and
`k ≤ 2`.  With `k = 2` one block has at least two units, hence damages two by
`two_le_damaged_of_cutSet_compl`, and the other damages one more: three in all. -/
theorem not_all_outputs_of_damagedCount_two (hN : 3 ≤ N)
    (θ : SysPartition N Finset.univ) (hD : damagedCount θ = 2) :
    ¬ (∀ q ∈ θ.parts, θ.dir q = Dir.outputs) := by
  classical
  intro hall
  have hcompl : ∀ p ∈ θ.parts, θ.cutSet p = pᶜ :=
    fun p hp => cutSet_eq_compl_of_all_outputs θ hall hp
  have hk : θ.parts.card ≤ 2 :=
    hD ▸ card_le_damagedCount_of_forall_compl θ (Finset.Subset.refl _) hcompl
  have hk2 := θ.two_le
  have hcard : θ.parts.card = 2 := by omega
  obtain ⟨p, q, hpq, hpar⟩ := Finset.card_eq_two.1 hcard
  have hp : p ∈ θ.parts := by rw [hpar]; exact Finset.mem_insert_self _ _
  have hq : q ∈ θ.parts := by
    rw [hpar]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  -- the two blocks partition the substrate
  have hunion : p ∪ q = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    obtain ⟨r, hr, hxr⟩ := θ.parts_cover x (Finset.mem_univ x)
    rw [hpar] at hr
    rcases Finset.mem_insert.1 hr with rfl | hr'
    · exact Finset.mem_union_left _ hxr
    · rw [Finset.mem_singleton] at hr'; subst hr'
      exact Finset.mem_union_right _ hxr
  have hdisj : Disjoint p q := θ.parts_disjoint p hp q hq hpq
  have hsum : p.card + q.card = N := by
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at this
    omega
  -- one of them has at least two units
  have hbig : 2 ≤ p.card ∨ 2 ≤ q.card := by
    have h1 : 1 ≤ p.card := Finset.card_pos.2 (θ.parts_nonempty p hp)
    have h2 : 1 ≤ q.card := Finset.card_pos.2 (θ.parts_nonempty q hq)
    omega
  -- that one damages two, the other damages one more
  have hthree : 3 ≤ damagedCount θ := by
    rcases hbig with hb | hb
    · obtain ⟨j₁, hj₁, j₂, hj₂, hne, hd1, hd2⟩ :=
        two_le_damaged_of_cutSet_compl θ hp (hcompl p hp) hb
      obtain ⟨j₃, hj₃, hd3⟩ := exists_damaged_of_cutSet_compl θ hq (hcompl q hq)
      have hs : ({j₁, j₂, j₃} : Finset (Fin N)) ⊆ damaged θ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
      have h13 : j₁ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj (h ▸ hj₁) hj₃
      have h23 : j₂ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj (h ▸ hj₂) hj₃
      have := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem (by simp [hne, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton] at this
      rw [damagedCount]; omega
    · obtain ⟨j₁, hj₁, j₂, hj₂, hne, hd1, hd2⟩ :=
        two_le_damaged_of_cutSet_compl θ hq (hcompl q hq) hb
      obtain ⟨j₃, hj₃, hd3⟩ := exists_damaged_of_cutSet_compl θ hp (hcompl p hp)
      have hs : ({j₁, j₂, j₃} : Finset (Fin N)) ⊆ damaged θ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by assumption⟩
      have h13 : j₁ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj hj₃ (h ▸ hj₁)
      have h23 : j₂ ≠ j₃ := fun h => Finset.disjoint_left.1 hdisj hj₃ (h ▸ hj₂)
      have := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem (by simp [hne, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton] at this
      rw [damagedCount]; omega
  omega

end DTwo

end IIT
