/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CircFamily

/-!
# Only arcs are distinctions

`CircNet/CircFamily.lean` proves that every contiguous arc of length at least three is a
distinction of the interval circulant (`isDistinctionMech_arc`).  This file proves the
converse: **nothing else is**.  Together the two give the classification of the
distinctions of `circNet N` at the all-ones state.

## The argument

Everything rests on one observation.  A purview unit `k` is *determined* by a mechanism
`M` exactly when its whole window `inputs k = {k, k+1, k+2}` lies in `M`, and a
partition of `(M, Z)` costs nothing at `k` when `k`'s window survives inside `k`'s own
block (`phiEofPartition_circNet_eq_zero`).  So to prove `φ_e(M) = 0` it suffices, for
every purview `Z`, to exhibit one partition of `(M, Z)` that cuts no determined window.

A window is three *consecutive* units, so it can never straddle a gap of `M`.  Hence if
`M` is cut along a **run** — a maximal arc of consecutive units of `M`, produced by
`exists_run` — every determined window lies entirely on one side of the cut
(`inputs_subset_of_mem_run`, `inputs_disjoint_of_notMem_run`).  The resulting two-block
partition `runPartition` is therefore free, and `φ_e(M) = 0`.

The construction needs the run to be a *proper* part of `M`, which is exactly the
`proper` condition `[IIT4, Eq 38]` on partitions.  A run fails to be proper only when the
run is all of `M` — that is, only when `M` is itself an arc.  This is where the
hypothesis enters, and it is the whole content of the theorem: **an arc is the one shape
that cannot be cut along a gap, because it has only one.**

No graph-theoretic notion of connectivity is needed anywhere; cutting along a run of `M`
replaces it.

## Main results

* `phiEmech_circNet_eq_zero_of_not_arc` — `φ_e(M) = 0` whenever `M` is not an arc of
  length at least three;
* `not_isDistinctionMech_of_not_arc` — such an `M` is not a distinction;
* `isDistinctionMech_circNet_iff` — **the classification**: the distinctions of
  `circNet N` at all-ones are exactly the arcs of length at least three.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section OnlyArcs

variable [NeZero N]

/-! ## Windows have three units -/

lemma shift_iterate_ne {a : Fin N} {i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    shift^[i] a ≠ shift^[j] a := fun h => hij (shift_iterate_inj hi hj h)

/-- A window is three units, so a mechanism of at most two units determines nothing. -/
lemma card_inputs (hN : 3 ≤ N) (k : Fin N) : (inputs k).card = 3 := by
  have key : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → shift^[i] k ≠ shift^[j] k := by
    intro i j hi hj hij h
    exact hij (shift_iterate_inj (by omega) (by omega) h)
  have e0 : shift^[0] k = k := rfl
  have e1 : shift^[1] k = shift k := by rw [Function.iterate_one]
  have e2 : shift^[2] k = shift (shift k) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [Finset.card_eq_three]
  refine ⟨k, shift k, shift (shift k), ?_, ?_, ?_, rfl⟩
  · have := key 0 1 (by omega) (by omega) (by omega); rwa [e0, e1] at this
  · have := key 0 2 (by omega) (by omega) (by omega); rwa [e0, e2] at this
  · have := key 1 2 (by omega) (by omega) (by omega); rwa [e1, e2] at this

/-- Nothing is determined by a mechanism with fewer than three units. -/
lemma not_inputs_subset_of_card_lt (hN : 3 ≤ N) {M : Finset (Fin N)} (hM : M.card < 3)
    (k : Fin N) : ¬ inputs k ⊆ M := by
  intro h
  have := Finset.card_le_card h
  rw [card_inputs hN] at this
  omega

/-! ## Runs -/

/-- The predecessor as an iterated shift. -/
lemma shift_iterate_pred (hN : 1 ≤ N) (a : Fin N) : shift^[N - 1] a = a - 1 := by
  have hN0 : 0 < N := hN
  apply Fin.ext
  rw [shift_iterate_val, Fin.sub_def]
  simp only [Fin.val_one']
  rcases Nat.lt_or_ge 1 N with h | h
  · rw [Nat.mod_eq_of_lt h]
    congr 1
    omega
  · -- `N = 1`: every value is `0`
    interval_cases N
    · simp

/-- **Every nonempty proper subset of the cycle has a run**: an arc inside `M` whose
successor lies outside `M`, starting at a unit whose predecessor lies outside `M`. -/
lemma exists_run (hN : 3 ≤ N) {M : Finset (Fin N)} (hne : M.Nonempty)
    (hlt : M ≠ Finset.univ) :
    ∃ (a : Fin N) (L : ℕ), 1 ≤ L ∧ L ≤ N - 1 ∧ arcAt a L ⊆ M ∧
      shift^[L] a ∉ M ∧ shift^[N - 1] a ∉ M := by
  obtain ⟨a, haM, hpred⟩ := exists_pred_not_mem hne hlt
  rw [← shift_iterate_pred (by omega) a] at hpred
  -- the least positive number of steps leaving `M`
  have hex : ∃ L, 1 ≤ L ∧ shift^[L] a ∉ M := ⟨N - 1, by omega, hpred⟩
  classical
  let L := Nat.find hex
  obtain ⟨hL1, hLout⟩ : 1 ≤ L ∧ shift^[L] a ∉ M := Nat.find_spec hex
  have hLmin : ∀ j, j < L → ¬ (1 ≤ j ∧ shift^[j] a ∉ M) := fun j hj => Nat.find_min hex hj
  have hLN : L ≤ N - 1 := by
    by_contra h
    push_neg at h
    exact (hLmin (N - 1) (by omega)) ⟨by omega, hpred⟩
  refine ⟨a, L, hL1, hLN, ?_, hLout, hpred⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_arcAt.1 hx
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simpa using haM
  · by_contra hmem
    exact (hLmin i hi) ⟨hipos, hmem⟩

/-! ### Windows do not straddle a run

The two lemmas that make the whole argument work: relative to a run of `M`, a determined
window is either wholly inside the run or wholly outside it. -/

variable {M : Finset (Fin N)} {a : Fin N} {L : ℕ}

/-- A determined window meeting a run lies inside it. -/
lemma inputs_subset_of_mem_run (hsub : arcAt a L ⊆ M) (hnext : shift^[L] a ∉ M)
    {k : Fin N} (hkM : inputs k ⊆ M) (hk : k ∈ arcAt a L) : inputs k ⊆ arcAt a L := by
  obtain ⟨i, hi, rfl⟩ := mem_arcAt.1 hk
  -- the window would otherwise reach the unit just past the run
  have h1 : shift^[i + 1] a ∈ M := by
    refine hkM ?_
    rw [Function.iterate_succ_apply']
    exact shift_mem_inputs _
  have h2 : shift^[i + 2] a ∈ M := by
    refine hkM ?_
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact shift_shift_mem_inputs _
  have hne1 : i + 1 ≠ L := by rintro rfl; exact hnext h1
  have hne2 : i + 2 ≠ L := by rintro rfl; exact hnext h2
  exact inputs_subset_arcAt (by omega)

/-- Undoing a shift: `N - r` further steps return to the start. -/
lemma shift_iterate_sub_add_cancel (hN : 1 ≤ N) (x : Fin N) (r : ℕ) (hr : r ≤ N)
    (hrpos : 1 ≤ r) : shift^[N - r] (shift^[r] x) = x := by
  rw [← Function.iterate_add_apply]
  have : N - r + r = N := by omega
  rw [this, shift_iterate_self]

/-- Iterated shifts are injective as maps. -/
lemma shift_iterate_injective (r : ℕ) :
    Function.Injective ((shift : Fin N → Fin N)^[r]) := by
  have h : Function.Injective (shift : Fin N → Fin N) := shift_injective
  exact h.iterate r

/-- If a run starts `r` steps past `k` (with `1 ≤ r ≤ 2`), then `k`'s `r`-th predecessor
is the unit just before the run, which lies outside `M`. -/
lemma notMem_of_run_starts_past (hN : 3 ≤ N) (hpred : shift^[N - 1] a ∉ M) {k : Fin N}
    {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (h : a = shift^[r] k) :
    shift^[r - 1] k ∉ M := by
  have hNr : shift^[N - 1] a = shift^[r - 1] k := by
    rw [h, ← Function.iterate_add_apply]
    have hsplit : N - 1 + r = N + (r - 1) := by omega
    rw [hsplit, Function.iterate_add_apply, shift_iterate_self]
  rwa [hNr] at hpred

/-- A determined window missing a run is disjoint from it. -/
lemma inputs_disjoint_of_notMem_run (hN : 3 ≤ N) (hpred : shift^[N - 1] a ∉ M)
    {k : Fin N} (hkM : inputs k ⊆ M) (hk : k ∉ arcAt a L) :
    Disjoint (inputs k) (arcAt a L) := by
  -- the three members of the window, as iterated shifts of `k`
  have hmem : ∀ r : ℕ, r ≤ 2 → shift^[r] k ∈ inputs k := by
    intro r hr
    interval_cases r
    · exact self_mem_inputs k
    · rw [Function.iterate_one]; exact shift_mem_inputs k
    · rw [Function.iterate_succ_apply', Function.iterate_one]
      exact shift_shift_mem_inputs k
  rw [Finset.disjoint_left]
  intro x hx hxarc
  obtain ⟨j, hj, hjx⟩ := mem_arcAt.1 hxarc
  -- write `x = k + r` with `r ≤ 2`
  obtain ⟨r, hr, rfl⟩ : ∃ r ≤ 2, shift^[r] k = x := by
    rcases mem_inputs.1 hx with rfl | rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, by rw [Function.iterate_one]⟩
    · exact ⟨2, by omega, by rw [Function.iterate_succ_apply', Function.iterate_one]⟩
  rcases Nat.lt_or_ge j r with hjr | hjr
  · -- the run starts strictly inside the window: its predecessor is a window unit of `M`
    have hstart : a = shift^[r - j] k := by
      apply shift_iterate_injective j
      rw [hjx, ← Function.iterate_add_apply]
      congr 1
      omega
    have := notMem_of_run_starts_past hN hpred (by omega : 1 ≤ r - j) (by omega) hstart
    exact this (hkM (hmem (r - j - 1) (by omega)))
  · -- otherwise `k` itself lies in the run
    refine hk (mem_arcAt.2 ⟨j - r, by omega, ?_⟩)
    apply shift_iterate_injective r
    rw [← Function.iterate_add_apply]
    have : r + (j - r) = j := by omega
    rw [this, hjx]

/-! ## Partitions that cost nothing

Two partitions of `(M, Z)`.  The first cuts `M` along a run; the second is the degenerate
cut used when `M` is too small to determine anything at all. -/

section Partitions

variable (M Z R : Finset (Fin N))

/-- **The run partition**: one block carries the run `R` and the purview units inside it,
the other carries everything else.  It is a legitimate partition exactly because `R` is a
proper nonempty part of `M`. -/
noncomputable def runPartition (hRM : R ⊆ M) (hRne : R.Nonempty) (hRne' : R ≠ M) :
    Partition N M Z where
  blocks := {(R, Z ∩ R), (M \ R, Z \ R)}
  mech_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hRM
    · exact Finset.sdiff_subset
  purv_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact Finset.inter_subset_left
    · exact Finset.sdiff_subset
  mech_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_sdiff
    · exact Finset.sdiff_disjoint
    · exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_left.2 fun x hx hx' =>
        (Finset.mem_sdiff.1 hx').2 (Finset.mem_inter.1 hx).2
    · exact Finset.disjoint_left.2 fun x hx hx' =>
        (Finset.mem_sdiff.1 hx).2 (Finset.mem_inter.1 hx').2
    · exact absurd rfl hne
  mech_cover := by
    intro i hi
    by_cases h : i ∈ R
    · exact ⟨(R, Z ∩ R), by simp, h⟩
    · exact ⟨(M \ R, Z \ R), by simp, Finset.mem_sdiff.2 ⟨hi, h⟩⟩
  purv_cover := by
    intro k hk
    by_cases h : k ∈ R
    · exact ⟨(R, Z ∩ R), by simp, Finset.mem_inter.2 ⟨hk, h⟩⟩
    · exact ⟨(M \ R, Z \ R), by simp, Finset.mem_sdiff.2 ⟨hk, h⟩⟩
  proper := by
    intro b hb hbM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact absurd hbM hRne'
    · exfalso
      obtain ⟨x, hx⟩ := hRne
      have hbM' : M \ R = M := hbM
      have hxM : x ∈ M \ R := by rw [hbM']; exact hRM hx
      exact (Finset.mem_sdiff.1 hxM).2 hx

variable {M Z R}

lemma runPartition_effPart_of_mem {hRM : R ⊆ M} {hRne : R.Nonempty} {hRne' : R ≠ M}
    {k : Fin N} (hkZ : k ∈ Z) (hkR : k ∈ R) :
    (runPartition M Z R hRM hRne hRne').effPart k = R :=
  Partition.effPart_eq _ (b := (R, Z ∩ R)) (by simp [runPartition])
    (Finset.mem_inter.2 ⟨hkZ, hkR⟩)

lemma runPartition_effPart_of_notMem {hRM : R ⊆ M} {hRne : R.Nonempty} {hRne' : R ≠ M}
    {k : Fin N} (hkZ : k ∈ Z) (hkR : k ∉ R) :
    (runPartition M Z R hRM hRne hRne').effPart k = M \ R :=
  Partition.effPart_eq _ (b := (M \ R, Z \ R)) (by simp [runPartition])
    (Finset.mem_sdiff.2 ⟨hkZ, hkR⟩)

/-- **The degenerate partition** used when `M` determines nothing. -/
noncomputable def trivPartition (hM : M.Nonempty) : Partition N M Z where
  blocks := {(M, ∅), (∅, Z)}
  mech_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact Finset.Subset.refl M
    · exact Finset.empty_subset M
  purv_subset := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact Finset.empty_subset Z
    · exact Finset.Subset.refl Z
  mech_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_empty_right M
    · exact Finset.disjoint_empty_left M
    · exact absurd rfl hne
  purv_disjoint := by
    intro b hb b' hb' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb hb'
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_empty_left Z
    · exact Finset.disjoint_empty_right Z
    · exact absurd rfl hne
  mech_cover := fun i hi => ⟨(M, ∅), by simp, hi⟩
  purv_cover := fun k hk => ⟨(∅, Z), by simp, hk⟩
  proper := by
    intro b hb hbM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · rfl
    · exact absurd hbM.symm (Finset.nonempty_iff_ne_empty.1 hM)

lemma trivPartition_effPart {hM : M.Nonempty} {k : Fin N} (hkZ : k ∈ Z) :
    (trivPartition (Z := Z) hM).effPart k = ∅ :=
  Partition.effPart_eq _ (b := ((∅ : Finset (Fin N)), Z)) (by simp [trivPartition]) hkZ

end Partitions

/-! ## A safe partition exists whenever `M` is not an arc -/

/-- `M` is an arc of length at least three (the whole cycle included, at `L = N`). -/
def IsLongArc (M : Finset (Fin N)) : Prop :=
  ∃ (a : Fin N) (L : ℕ), 3 ≤ L ∧ L ≤ N ∧ M = arcAt a L

/-- An arc of full length is the whole cycle. -/
lemma arcAt_card_eq_univ (a : Fin N) : arcAt a N = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [card_arcAt a le_rfl, Fintype.card_fin]

/-- **The key construction.**  If `M` is not an arc of length at least three, then for
every purview there is a partition cutting no determined window. -/
theorem exists_safe_partition (hN : 3 ≤ N) {M : Finset (Fin N)} (hM : M.Nonempty)
    (harc : ¬ IsLongArc M) (Z : Finset (Fin N)) :
    ∃ θ : Partition N M Z, ∀ k ∈ Z, inputs k ⊆ M → inputs k ⊆ θ.effPart k := by
  -- the whole cycle is an arc, so `M` is proper
  have hne : M ≠ Finset.univ := by
    rintro rfl
    exact harc ⟨0, N, hN, le_rfl, (arcAt_card_eq_univ 0).symm⟩
  obtain ⟨a, L, hL1, hLN, hsub, hnext, hpred⟩ := exists_run hN hM hne
  by_cases hfull : arcAt a L = M
  · -- the run exhausts `M`, so `M` is an arc; it must then be a short one
    have hshort : L < 3 := by
      by_contra h
      exact harc ⟨a, L, by omega, by omega, hfull.symm⟩
    have hcard : M.card < 3 := by
      rw [← hfull, card_arcAt a (by omega)]
      omega
    refine ⟨trivPartition (Z := Z) hM, ?_⟩
    intro k _ hk
    exact absurd hk (not_inputs_subset_of_card_lt hN hcard k)
  · -- cut `M` along the run
    refine ⟨runPartition M Z (arcAt a L) hsub (arcAt_nonempty a (by omega)) hfull, ?_⟩
    intro k hkZ hkM
    by_cases hkR : k ∈ arcAt a L
    · rw [runPartition_effPart_of_mem hkZ hkR]
      exact inputs_subset_of_mem_run hsub hnext hkM hkR
    · rw [runPartition_effPart_of_notMem hkZ hkR]
      intro x hx
      refine Finset.mem_sdiff.2 ⟨hkM hx, ?_⟩
      exact Finset.disjoint_left.1 (inputs_disjoint_of_notMem_run hN hpred hkM hkR) hx

/-! ## `φ_e` vanishes -/

/-- **A partition cutting no determined window costs nothing.** -/
theorem phiEofPartition_circNet_eq_zero (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (θ : Partition N M Z)
    (hsafe : ∀ k ∈ Z, inputs k ⊆ M → inputs k ⊆ θ.effPart k) :
    phiEofPartition (circNet N) M allOnes Z allOnes θ = 0 := by
  have hfil : (Z.filter fun k => ¬ inputs k ⊆ θ.effPart k) = circZund M Z := by
    rw [circZund]
    refine Finset.filter_congr fun k hk => ?_
    constructor
    · exact fun h hM => h (hsafe k hk hM)
    · exact fun h h' => h (h'.trans (θ.effPart_subset k))
  rw [phiEofPartition, effRep_circNet_allOnes_allOnes hN,
    partEffRep_circNet_allOnes hN M Z θ (allOnes_agree_circ M Z), hfil,
    div_self (by positivity), Real.logb_one]
  simp [pos]

/-- **`φ_e` at a purview vanishes** once one partition costs nothing. -/
theorem phiEat_circNet_eq_zero_of_safe (hN : 3 ≤ N) (M Z : Finset (Fin N))
    (hM : M.Nonempty) (θ₀ : Partition N M Z)
    (hsafe : ∀ k ∈ Z, inputs k ⊆ M → inputs k ⊆ θ₀.effPart k) :
    phiEat (circNet N) M allOnes Z allOnes = 0 := by
  have hfact : Fact M.Nonempty := ⟨hM⟩
  have h0 := phiEofPartition_circNet_eq_zero hN M Z θ₀ hsafe
  rw [phiEat]
  refine le_antisymm (sup'OrZero_le le_rfl ?_)
    (sup'OrZero_nonneg fun θ _ => phiEofPartition_nonneg _ _ _ _ _ _)
  intro θ hθ
  rcases Z.eq_empty_or_nonempty with rfl | hZne
  · exact le_of_eq (phiEofPartition_circNet_eq_zero hN M ∅ θ (by simp))
  · have hcc : (0 : ℝ) < (cutCount M Z θ : ℝ) := by exact_mod_cast cutCount_pos hZne θ
    have hnorm0 : normalizedPhi (circNet N) M allOnes Z allOnes θ₀ = 0 := by
      rw [normalizedPhi, h0, zero_div]
    have hmin : normalizedPhi (circNet N) M allOnes Z allOnes θ ≤ 0 := by
      have hle := (mem_argminSet.1 hθ) θ₀
      rwa [hnorm0] at hle
    have hge : 0 ≤ normalizedPhi (circNet N) M allOnes Z allOnes θ := by
      rw [normalizedPhi]
      exact div_nonneg (phiEofPartition_nonneg _ _ _ _ _ _) (le_of_lt hcc)
    have heq : normalizedPhi (circNet N) M allOnes Z allOnes θ = 0 := le_antisymm hmin hge
    have hw := normalizedPhi_wellDefined (circNet N) M allOnes Z allOnes θ hZne
    rw [heq, zero_mul] at hw
    exact le_of_eq hw.symm

/-- **`φ_e` over one purview vanishes.** -/
theorem phiEpurview_circNet_eq_zero (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (M Z : Finset (Fin N))
    (hM : M.Nonempty) (θ₀ : Partition N M Z)
    (hsafe : ∀ k ∈ Z, inputs k ⊆ M → inputs k ⊆ θ₀.effPart k) :
    phiEpurview (circNet N) M allOnes Z = 0 := by
  have hzero : ∀ z ∈ maxEffStates (circNet N) M allOnes Z,
      phiEat (circNet N) M allOnes Z z = 0 := by
    intro z hz
    rw [phiEat_circNet_allOnes_eq_of_agree hN M Z
      (agree_of_mem_maxEffStates_circNet hN h3 M Z hz) (allOnes_agree_circ M Z)]
    exact phiEat_circNet_eq_zero_of_safe hN M Z hM θ₀ hsafe
  rw [phiEpurview]
  refine le_antisymm (Finset.sup'_le _ _ fun z hz => le_of_eq (hzero z hz)) ?_
  have hmem := allOnes_mem_maxEffStates_circNet hN h3 M Z
  calc (0 : ℝ) = phiEat (circNet N) M allOnes Z allOnes := (hzero _ hmem).symm
    _ ≤ _ := Finset.le_sup' (f := fun z => phiEat (circNet N) M allOnes Z z) hmem

/-- **`φ_e(M) = 0` for every mechanism that is not an arc of length at least three.** -/
theorem phiEmech_circNet_eq_zero_of_not_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N))
    {M : Finset (Fin N)} (hM : M.Nonempty) (harc : ¬ IsLongArc M) :
    phiEmech (circNet N) Finset.univ M allOnes = 0 := by
  have hzero : ∀ Z : Finset (Fin N), phiEpurview (circNet N) M allOnes Z = 0 := by
    intro Z
    obtain ⟨θ₀, hθ₀⟩ := exists_safe_partition hN hM harc Z
    exact phiEpurview_circNet_eq_zero hN h3 M Z hM θ₀ hθ₀
  rw [phiEmech]
  refine le_antisymm (Finset.sup'_le _ _ fun Z _ => le_of_eq (hzero Z)) ?_
  have hmem : (∅ : Finset (Fin N)) ∈ (Finset.univ : Finset (Fin N)).powerset :=
    Finset.empty_mem_powerset _
  calc (0 : ℝ) = phiEpurview (circNet N) M allOnes ∅ := (hzero ∅).symm
    _ ≤ _ := Finset.le_sup' (f := fun Z => phiEpurview (circNet N) M allOnes Z) hmem

/-! ## The classification -/

/-- **Only arcs are distinctions.** -/
theorem not_isDistinctionMech_of_not_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    {M : Finset (Fin N)} (harc : ¬ IsLongArc M) :
    ¬ IsDistinctionMech (circNet N) Finset.univ u allOnes M := by
  rintro ⟨hpos, -⟩
  rcases M.eq_empty_or_nonempty with rfl | hM
  · -- the empty mechanism has `φ_d = 0`
    rw [phiD_empty_mech] at hpos
    exact lt_irrefl 0 hpos
  · have hle := phiD_le_phiEmech (circNet N) Finset.univ M allOnes
    rw [phiEmech_circNet_eq_zero_of_not_arc hN h3 hM harc] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

/-- **The distinctions of the interval circulant are exactly its arcs of length at least
three.**  This is the converse half of `isDistinctionMech_arc`. -/
theorem isDistinctionMech_circNet_iff (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (M : Finset (Fin N)) :
    IsDistinctionMech (circNet N) Finset.univ u allOnes M ↔ IsLongArc M := by
  constructor
  · intro h
    by_contra harc
    exact not_isDistinctionMech_of_not_arc hN h3 u harc h
  · rintro ⟨a, L, hL, -, rfl⟩
    exact isDistinctionMech_arc hN h3 u a hL

/-! ## The count -/

/-- **The Finset of arcs**: the arcs of length `3` to `N - 1`, together with the whole
cycle. -/
noncomputable def circArcsFinset (N : ℕ) [NeZero N] : Finset (Finset (Fin N)) :=
  insert (Finset.univ : Finset (Fin N))
    ((Finset.univ ×ˢ Finset.Ico 3 N).image fun p => arcAt p.1 p.2)

lemma mem_circArcsFinset (hN : 3 ≤ N) {M : Finset (Fin N)} :
    M ∈ circArcsFinset N ↔ IsLongArc M := by
  rw [circArcsFinset, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · exact ⟨0, N, hN, le_rfl, (arcAt_card_eq_univ 0).symm⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Ico] at hp
      exact ⟨p.1, p.2, hp.1, le_of_lt hp.2, rfl⟩
  · rintro ⟨a, L, hL3, hLN, rfl⟩
    rcases hLN.lt_or_eq with hLlt | hLeq
    · exact Or.inr ⟨(a, L),
        Finset.mem_product.2 ⟨Finset.mem_univ a, Finset.mem_Ico.2 ⟨hL3, hLlt⟩⟩, rfl⟩
    · exact Or.inl (hLeq ▸ arcAt_card_eq_univ a)

/-- **`(arc, its arc parameters)` is injective on the range the count needs.** -/
lemma injOn_arcAt_of_range :
    Set.InjOn (fun p : Fin N × ℕ => arcAt p.1 p.2)
      (Finset.univ ×ˢ Finset.Ico 3 N : Finset (Fin N × ℕ)) := by
  rintro ⟨a, L⟩ hp ⟨a', L'⟩ hp' heq
  simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_Ico, Set.mem_prod, Set.mem_univ,
    Set.mem_Ico, true_and] at hp hp'
  obtain ⟨h1, h2⟩ : a = a' ∧ L = L' :=
    arcAt_injective (by omega) (by omega) (by omega) (by omega) heq
  simp [h1, h2]

/-- **A short arc is never the whole cycle.** -/
lemma arcAt_ne_univ_of_lt {a : Fin N} {L : ℕ} (hL : L < N) : arcAt a L ≠ Finset.univ := by
  intro h
  have hc : (arcAt a L).card = N := by rw [h, Finset.card_univ, Fintype.card_fin]
  rw [card_arcAt a (by omega)] at hc
  omega

/-- **`circArcsFinset` has `N(N - 3) + 1` elements.** -/
theorem card_circArcsFinset (hN : 3 ≤ N) : (circArcsFinset N).card = N * (N - 3) + 1 := by
  rw [circArcsFinset, Finset.card_insert_of_notMem, Finset.card_image_of_injOn
    injOn_arcAt_of_range, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Nat.card_Ico]
  · intro h
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Ico] at hp
    exact arcAt_ne_univ_of_lt hp.2 hpe

/-- **`Φ` counts `N(N - 3) + 1` distinctions.** This is Proposition 6.2's stated
consequence, the count that feeds `Remark 7.2`'s discussion of the sharp constants. -/
theorem card_distinctionMechs_circNet (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) :
    (distinctionMechs (circNet N) Finset.univ u allOnes).card = N * (N - 3) + 1 := by
  have heq : distinctionMechs (circNet N) Finset.univ u allOnes = circArcsFinset N := by
    ext M
    rw [mem_distinctionMechs, mem_circArcsFinset hN]
    constructor
    · exact fun h => (isDistinctionMech_circNet_iff hN h3 u M).1 h.2
    · exact fun harc => ⟨Finset.subset_univ M,
        (isDistinctionMech_circNet_iff hN h3 u M).2 harc⟩
  rw [heq, card_circArcsFinset hN]

end OnlyArcs

end IIT
