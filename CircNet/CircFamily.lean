/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CircMechEffect
import CircNet.CircMechCause
import CircNet.PhiFamily

/-!
# The interval circulant: the arc family and the doubly exponential bound

The assembly, with the **contiguous arcs** in place of
the puncture mechanisms.  For `8 ≤ N` with `3 ∤ N`, every arc

  `arcAt a L = {a, a+1, …, a+L-1}`,  `3 ≤ L ≤ N-1`,

is a distinction mechanism of the interval circulant at the all-ones state
(`isDistinctionMech_arc`).  Two chain arguments -- one on each causal side -- show that
every `[IIT4, Eq 38]` partition of an arc severs some window
(`exists_not_determined_arc_eff`, `exists_not_determined_arc_cause`), which gives
`φ_e ≥ 1` and `φ_c ≥ (1/2)^N`, hence `φ_d ≥ (1/2)^N` (`le_phiD_arc`).

Unlike the puncture mechanisms of the chordal circulant, the windows of an arc do **not**
cover the substrate, so the maximizing cause purview is not the whole substrate and
`maxCausePurviews_circNet_univ` does not apply.  The first section therefore develops the
cause side over an **arbitrary** purview `Z` at all-ones: `causeFwd` is `(1/2)^u` on the
fibre `{z | circVal k z = true for every k ∈ M whose window lies in Z}` and `0` off it
(`causeFwd_circNet_gen`), so all-ones is a maximal cause state of every purview
(`allOnes_mem_maxCauseStates_circNet_gen`), a positive `φ_c` forces the fibre
(`fib_of_phiCat_pos`), and `φ_c` is constant on it (`phiCat_circNet_eq_of_fib`).  Hence
all-ones can be swapped into any maximizing cause purview
(`mem_maxCausePurviews_circNet_allOnes`), which is what supplies the congruent witness.

The arcs containing the unit `0` are parameterized by a pair `(s, e)` -- the arc
`[-s, e]` -- and the parameter rectangle `1 ≤ s < N/2`, `1 ≤ e < N - N/2` has
`(N/2 - 1)(N - N/2 - 1) ≥ N²/8` points (`nat_sq_div_eight_le`).  Feeding the resulting
family to `doubly_exp_le_PhiMax_of_family` gives

  `Φ_max ≥ (2^{|F|} - 1 - |F|) · (1/2)^N / (2N)`  (`card_family_le_PhiMax_circNet`),

displayed as `Φ_max ≥ 2^{N²/8} · (1/2)^N / (2N) - 1` (`two_pow_sq_le_PhiMax_circNet`):
doubly exponential in `N` -- indeed `2^{Θ(N²)}` -- on a substrate that is already known to
be a complex (`isComplex_circNet_univ`, `CircNet/CirculantD3Final.lean`).

The constants are chosen for directness rather than sharpness: the per-unit floor proved
here is `(1/2)^N/(2N)`, which suffices for the growth rate.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

/-! ## The cause side over an arbitrary purview -/

section GenCause

variable [NeZero N]

/-- **The cause repertoire of `M` at all-ones over an arbitrary purview `Z`.**  Every unit
of `M` whose window lies inside `Z` is pinned, every other one contributes one half. -/
theorem causeFwd_circNet_gen (hN : 3 ≤ N) (M Z : Finset (Fin N)) (z : State N) :
    causeFwd (circNet N) Z z M allOnes
      = if (∀ k ∈ M, inputs k ⊆ Z → circVal k z = true) then
          (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card else 0 := by
  rw [causeFwd_eq]
  by_cases h : ∀ k ∈ M, inputs k ⊆ Z → circVal k z = true
  · rw [if_pos h]
    have hterm : ∀ k ∈ M, effUnit (circNet N) Z z k (allOnes k)
        = if inputs k ⊆ Z then 1 else (1 / 2 : ℝ) := by
      intro k hk
      by_cases hw : inputs k ⊆ Z
      · rw [if_pos hw, effUnit_circNet_of_inputs_subset _ _ _ _ hw, allOnes_apply, h k hk hw,
          if_pos rfl]
      · rw [if_neg hw, effUnit_circNet_of_not_inputs_subset hN _ _ _ _ hw]
    rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨k, hk, hw, hv⟩ := h
    refine Finset.prod_eq_zero hk ?_
    rw [effUnit_circNet_of_inputs_subset _ _ _ _ hw, allOnes_apply, if_neg]
    exact fun hc => hv hc.symm

/-- The partitioned cause repertoire at a fibre state, over an arbitrary purview. -/
theorem partCauseFwd_circNet_gen (hN : 3 ≤ N) (M Z : Finset (Fin N)) (θ : Partition N M Z)
    {z : State N} (hz : ∀ k ∈ M, inputs k ⊆ Z → circVal k z = true) :
    partCauseFwd (circNet N) Z z M allOnes θ
      = (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ θ.causePart k).card := by
  rw [partCauseFwd]
  have hterm : ∀ k ∈ M, effUnit (circNet N) (θ.causePart k) z k (allOnes k)
      = if inputs k ⊆ θ.causePart k then 1 else (1 / 2 : ℝ) := by
    intro k hk
    by_cases h : inputs k ⊆ θ.causePart k
    · rw [if_pos h, effUnit_circNet_of_inputs_subset _ _ _ _ h, allOnes_apply,
        hz k hk (h.trans (θ.causePart_subset k)), if_pos rfl]
    · rw [if_neg h, effUnit_circNet_of_not_inputs_subset hN _ _ _ _ h]
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]

/-- **All-ones is a maximal cause state of every mechanism over every purview.** -/
theorem allOnes_mem_maxCauseStates_circNet_gen (hN : 3 ≤ N) (M Z : Finset (Fin N)) :
    (allOnes : State N) ∈ maxCauseStates (circNet N) M allOnes Z := by
  rw [maxCauseStates, mem_argmaxSet]
  intro w
  have hcpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card := by positivity
  have hfibAll : ∀ k ∈ M, inputs k ⊆ Z → circVal k (allOnes : State N) = true :=
    fun k _ _ => circVal_allOnes k
  have hall : causeFwd (circNet N) Z (allOnes : State N) M allOnes
      = (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card := by
    rw [causeFwd_circNet_gen hN, if_pos hfibAll]
  have hle : ∀ s : State N, causeFwd (circNet N) Z s M allOnes
      ≤ (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card := by
    intro s
    rw [causeFwd_circNet_gen hN]
    split_ifs
    · exact le_rfl
    · exact hcpos.le
  have hUle : uncCauseFwd (circNet N) Z M allOnes
      ≤ (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card := by
    rw [uncCauseFwd, avgOverStates, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
    calc (∑ s : State N, causeFwd (circNet N) Z s M allOnes)
        ≤ ∑ _s : State N, (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card :=
          Finset.sum_le_sum fun s _ => hle s
      _ = (1 / 2 : ℝ) ^ (M.filter fun k => ¬ inputs k ⊆ Z).card * (2 : ℝ) ^ N := by
          rw [Finset.sum_const, card_state, nsmul_eq_mul]
          push_cast
          ring
  have hUpos : 0 < uncCauseFwd (circNet N) Z M allOnes := by
    rw [uncCauseFwd, avgOverStates]
    refine div_pos ?_ (by positivity)
    refine Finset.sum_pos' (fun s _ => causeFwd_nonneg _ _ _ _ _)
      ⟨allOnes, Finset.mem_univ _, ?_⟩
    rw [hall]
    exact hcpos
  have hlogb : 0 ≤ Real.logb 2 (causeFwd (circNet N) Z (allOnes : State N) M allOnes
      / uncCauseFwd (circNet N) Z M allOnes) := by
    refine Real.logb_nonneg (by norm_num) ?_
    rw [hall, le_div_iff₀ hUpos, one_mul]
    exact hUle
  have hiiAll : 0 ≤ iiC (circNet N) M allOnes Z (allOnes : State N) :=
    mul_nonneg (causeRep_nonneg _ _ _ _ _) hlogb
  by_cases hw : ∀ k ∈ M, inputs k ⊆ Z → circVal k w = true
  · have hfw : causeFwd (circNet N) Z w M allOnes
        = causeFwd (circNet N) Z (allOnes : State N) M allOnes := by
      rw [causeFwd_circNet_gen hN, causeFwd_circNet_gen hN, if_pos hw, if_pos hfibAll]
    have heq : iiC (circNet N) M allOnes Z w
        = iiC (circNet N) M allOnes Z (allOnes : State N) := by
      simp only [iiC, causeRep, hfw]
    rw [heq]
  · have hfw : causeFwd (circNet N) Z w M allOnes = 0 := by
      rw [causeFwd_circNet_gen hN, if_neg hw]
    have hz0 : iiC (circNet N) M allOnes Z w = 0 := by
      rw [iiC, causeRep, hfw, zero_div, zero_mul]
    rw [hz0]
    exact hiiAll

/-- **A positive `φ_c` forces the fibre.**  Off the fibre the cause repertoire vanishes, so
every partition scores zero. -/
theorem fib_of_phiCat_pos (hN : 3 ≤ N) (M Z : Finset (Fin N)) {z : State N}
    (hpos : 0 < phiCat (circNet N) Z z M allOnes) :
    ∀ k ∈ M, inputs k ⊆ Z → circVal k z = true := by
  by_contra h
  have hfwd : causeFwd (circNet N) Z z M allOnes = 0 := by
    rw [causeFwd_circNet_gen hN, if_neg h]
  have hrep : causeRep (circNet N) Z z M allOnes = 0 := by
    rw [causeRep, hfwd, zero_div]
  have hle : phiCat (circNet N) Z z M allOnes ≤ 0 := by
    rw [phiCat]
    refine sup'OrZero_le le_rfl fun θ _ => ?_
    rw [phiCofPartition, hrep, zero_mul]
  exact absurd hpos (not_lt.2 hle)

/-- **`φ_c` is constant on the fibre**, over an arbitrary purview. -/
theorem phiCat_circNet_eq_of_fib (hN : 3 ≤ N) (M Z : Finset (Fin N)) {z : State N}
    (hz : ∀ k ∈ M, inputs k ⊆ Z → circVal k z = true) :
    phiCat (circNet N) Z z M allOnes = phiCat (circNet N) Z (allOnes : State N) M allOnes := by
  have hfibAll : ∀ k ∈ M, inputs k ⊆ Z → circVal k (allOnes : State N) = true :=
    fun k _ _ => circVal_allOnes k
  have hfwd : causeFwd (circNet N) Z z M allOnes
      = causeFwd (circNet N) Z (allOnes : State N) M allOnes := by
    rw [causeFwd_circNet_gen hN, causeFwd_circNet_gen hN, if_pos hz, if_pos hfibAll]
  have hrep : causeRep (circNet N) Z z M allOnes
      = causeRep (circNet N) Z (allOnes : State N) M allOnes := by
    rw [causeRep, causeRep, hfwd]
  have hpart : ∀ θ : Partition N M Z, partCauseFwd (circNet N) Z z M allOnes θ
      = partCauseFwd (circNet N) Z (allOnes : State N) M allOnes θ := by
    intro θ
    rw [partCauseFwd_circNet_gen hN M Z θ hz, partCauseFwd_circNet_gen hN M Z θ hfibAll]
  have hphi : ∀ θ : Partition N M Z, phiCofPartition (circNet N) Z z M allOnes θ
      = phiCofPartition (circNet N) Z (allOnes : State N) M allOnes θ := by
    intro θ
    rw [phiCofPartition, phiCofPartition, hrep, hfwd, hpart]
  have hnorm : ∀ θ : Partition N M Z, normalizedPhiC (circNet N) Z z M allOnes θ
      = normalizedPhiC (circNet N) Z (allOnes : State N) M allOnes θ := by
    intro θ
    rw [normalizedPhiC, normalizedPhiC, hphi]
  have hmip : mipSetC (circNet N) Z z M allOnes
      = mipSetC (circNet N) Z (allOnes : State N) M allOnes := by
    ext θ
    simp only [mipSetC, mem_argminSet, hnorm]
  rw [phiCat, phiCat, hmip]
  exact sup'OrZero_congr hphi

/-- **Swapping all-ones into a maximal cause purview.**  The cause-side counterpart of
`mem_maxEffPurviews_circNet_allOnes`, with no covering hypothesis. -/
theorem mem_maxCausePurviews_circNet_allOnes (hN : 3 ≤ N) (M : Finset (Fin N))
    (hpos : 0 < phiCmech (circNet N) Finset.univ M allOnes)
    {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews (circNet N) Finset.univ M allOnes) :
    (p.1, (allOnes : State N)) ∈ maxCausePurviews (circNet N) Finset.univ M allOnes := by
  have hpcat : 0 < phiCat (circNet N) p.1 p.2 M allOnes :=
    phiCat_pos_of_mem_maxCausePurviews _ _ _ hpos hp
  have hfib := fib_of_phiCat_pos hN M p.1 hpcat
  have heq : phiCat (circNet N) p.1 p.2 M allOnes
      = phiCat (circNet N) p.1 (allOnes : State N) M allOnes :=
    phiCat_circNet_eq_of_fib hN M p.1 hfib
  obtain ⟨-, hmax⟩ := Finset.mem_filter.1 hp
  have hcand : (p.1, (allOnes : State N))
      ∈ causeCandidates (circNet N) Finset.univ M allOnes := by
    rw [causeCandidates, Finset.mem_biUnion]
    exact ⟨p.1, Finset.mem_powerset.2 (Finset.subset_univ _),
      Finset.mem_image_of_mem _ (allOnes_mem_maxCauseStates_circNet_gen hN M p.1)⟩
  exact Finset.mem_filter.2 ⟨hcand, fun q hq => (hmax q hq).trans_eq heq⟩

/-- A stated purview at all-ones sits inside the system's all-ones stated purview. -/
lemma stated_allOnes_subset_univ (Z : Finset (Fin N)) :
    stated Z (allOnes : State N) ⊆ stated Finset.univ (allOnes : State N) := by
  intro q hq
  rw [mem_stated] at hq ⊢
  exact ⟨Finset.mem_univ _, hq.2⟩

end GenCause

/-! ## Arcs -/

section Arcs

variable [NeZero N]

/-- The contiguous arc `{a, a+1, …, a+L-1}` of length `L` starting at `a`. -/
noncomputable def arcAt (a : Fin N) (L : ℕ) : Finset (Fin N) :=
  (Finset.range L).image fun i => shift^[i] a

lemma mem_arcAt {a : Fin N} {L : ℕ} {x : Fin N} :
    x ∈ arcAt a L ↔ ∃ i < L, shift^[i] a = x := by
  simp [arcAt, Finset.mem_image, Finset.mem_range]

lemma self_mem_arcAt (a : Fin N) {L : ℕ} (hL : 0 < L) : a ∈ arcAt a L :=
  mem_arcAt.2 ⟨0, hL, rfl⟩

lemma arcAt_nonempty (a : Fin N) {L : ℕ} (hL : 0 < L) : (arcAt a L).Nonempty :=
  ⟨a, self_mem_arcAt a hL⟩

/-- Iterating the shift `N` times is the identity. -/
lemma shift_iterate_self (x : Fin N) : shift^[N] x = x := by
  apply Fin.ext
  rw [shift_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-- The orbit map `i ↦ a + i` is injective below `N`. -/
lemma shift_iterate_inj {a : Fin N} {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : shift^[i] a = shift^[j] a) : i = j := by
  have hv := congrArg Fin.val h
  rw [shift_iterate_val, shift_iterate_val] at hv
  have hmod : i ≡ j [MOD N] := Nat.ModEq.add_left_cancel' a.val hv
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod

/-- **An arc of length `L ≤ N` has `L` units.** -/
lemma card_arcAt (a : Fin N) {L : ℕ} (hL : L ≤ N) : (arcAt a L).card = L := by
  rw [arcAt, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  exact shift_iterate_inj (lt_of_lt_of_le (Finset.mem_range.1 hi) hL)
    (lt_of_lt_of_le (Finset.mem_range.1 hj) hL) h

/-- The window of `a + i` lies inside the arc as soon as `i + 3 ≤ L`. -/
lemma inputs_subset_arcAt {a : Fin N} {L i : ℕ} (h : i + 3 ≤ L) :
    inputs (shift^[i] a) ⊆ arcAt a L := by
  intro x hx
  rcases mem_inputs.1 hx with rfl | rfl | rfl
  · exact mem_arcAt.2 ⟨i, by omega, rfl⟩
  · exact mem_arcAt.2 ⟨i + 1, by omega, by rw [Function.iterate_succ_apply']⟩
  · exact mem_arcAt.2 ⟨i + 2, by omega, by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']⟩

/-- **The determined set of an arc**: the arc of length `L - 2` at the same start, all of
whose windows lie inside the arc. -/
lemma inputs_subset_of_mem_arcDet {a : Fin N} {L : ℕ} {k : Fin N}
    (hk : k ∈ arcAt a (L - 2)) : inputs k ⊆ arcAt a L := by
  obtain ⟨i, hi, rfl⟩ := mem_arcAt.1 hk
  exact inputs_subset_arcAt (by omega)

/-- The windows of the determined set cover the arc. -/
lemma arcAt_subset_windows {a : Fin N} {L : ℕ} (hL : 3 ≤ L) {x : Fin N}
    (hx : x ∈ arcAt a L) : ∃ i < L - 2, x ∈ inputs (shift^[i] a) := by
  obtain ⟨j, hj, rfl⟩ := mem_arcAt.1 hx
  obtain ⟨i, hi1, hi2⟩ : ∃ i, i < L - 2 ∧ (j = i ∨ j = i + 1 ∨ j = i + 2) :=
    ⟨min j (L - 3), by omega, by omega⟩
  refine ⟨i, hi1, ?_⟩
  rcases hi2 with rfl | rfl | rfl
  · exact self_mem_inputs _
  · rw [Function.iterate_succ_apply']; exact shift_mem_inputs _
  · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact shift_shift_mem_inputs _

/-! ### Recovering the parameters of an arc -/

lemma pred_notMem_arcAt {a : Fin N} {L : ℕ} (hL : 1 ≤ L) (hLN : L ≤ N - 1) :
    shift^[N - 1] a ∉ arcAt a L := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  intro h
  obtain ⟨i, hi, hieq⟩ := mem_arcAt.1 h
  have := shift_iterate_inj (a := a) (by omega : i < N) (by omega : N - 1 < N) hieq
  omega

lemma pred_mem_arcAt {a : Fin N} {L : ℕ} {x : Fin N} (hx : x ∈ arcAt a L) (hxa : x ≠ a) :
    shift^[N - 1] x ∈ arcAt a L := by
  obtain ⟨i, hi, rfl⟩ := mem_arcAt.1 hx
  have hi0 : i ≠ 0 := by rintro rfl; exact hxa rfl
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine mem_arcAt.2 ⟨i - 1, by omega, ?_⟩
  have he : (N - 1) + i = N + (i - 1) := by omega
  rw [← Function.iterate_add_apply, he, Function.iterate_add_apply, shift_iterate_self]

/-- **The start of an arc is determined by the arc.** -/
lemma arcAt_start_eq {a a' : Fin N} {L L' : ℕ} (h1 : 1 ≤ L) (h2 : L ≤ N - 1)
    (h : arcAt a L = arcAt a' L') : a = a' := by
  by_contra hne
  have ha : a ∈ arcAt a' L' := h ▸ self_mem_arcAt a (by omega)
  have hmem := pred_mem_arcAt ha hne
  rw [← h] at hmem
  exact pred_notMem_arcAt h1 h2 hmem

/-- **`(a, L)` is determined by the arc `arcAt a L`.** -/
theorem arcAt_injective {a a' : Fin N} {L L' : ℕ} (h1 : 1 ≤ L) (h2 : L ≤ N - 1)
    (h1' : 1 ≤ L') (h2' : L' ≤ N - 1) (h : arcAt a L = arcAt a' L') : a = a' ∧ L = L' := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨arcAt_start_eq h1 h2 h, ?_⟩
  have hc : (arcAt a L).card = (arcAt a' L').card := by rw [h]
  rwa [card_arcAt a (by omega), card_arcAt a' (by omega)] at hc

end Arcs

/-! ## Every partition of an arc severs a window -/

section Chain

variable [NeZero N]

lemma arcBlock_eq_of_mem_mech {M Z : Finset (Fin N)} (θ : Partition N M Z)
    {b b' : Finset (Fin N) × Finset (Fin N)} (hb : b ∈ θ.blocks) (hb' : b' ∈ θ.blocks)
    {x : Fin N} (hx : x ∈ b.1) (hx' : x ∈ b'.1) : b = b' := by
  by_contra hne
  exact absurd hx' (Finset.disjoint_left.1 (θ.mech_disjoint b hb b' hb' hne) hx)

lemma arcBlock_eq_of_mem_purv {M Z : Finset (Fin N)} (θ : Partition N M Z)
    {b b' : Finset (Fin N) × Finset (Fin N)} (hb : b ∈ θ.blocks) (hb' : b' ∈ θ.blocks)
    {x : Fin N} (hx : x ∈ b.2) (hx' : x ∈ b'.2) : b = b' := by
  by_contra hne
  exact absurd hx' (Finset.disjoint_left.1 (θ.purv_disjoint b hb b' hb' hne) hx)

/-- **The effect chain.**  Consecutive determined units share a window member, so a
partition that severs nothing puts the whole determined set in one block, whose mechanism
part then exhausts the arc -- forbidden by `[IIT4, Eq 38]`. -/
theorem exists_not_determined_arc_eff {a : Fin N} {L : ℕ} (hL : 3 ≤ L)
    (θ : Partition N (arcAt a L) (arcAt a (L - 2))) :
    ∃ k ∈ arcAt a (L - 2), ¬ inputs k ⊆ θ.effPart k := by
  by_contra hall
  push_neg at hall
  obtain ⟨b, hb, h0b⟩ := θ.purv_cover a (self_mem_arcAt a (by omega))
  have key : ∀ i, i < L - 2 → shift^[i] a ∈ b.2 := by
    intro i
    induction i with
    | zero => intro _; simpa using h0b
    | succ p ih =>
      intro hp
      have hp' : p < L - 2 := by omega
      have hpb := ih hp'
      have h1 : inputs (shift^[p] a) ⊆ b.1 := by
        rw [← θ.effPart_eq hb hpb]
        exact hall _ (mem_arcAt.2 ⟨p, hp', rfl⟩)
      have hmem : shift^[p + 1] a ∈ b.1 := by
        rw [Function.iterate_succ_apply']
        exact h1 (shift_mem_inputs _)
      obtain ⟨b', hb', hxb'⟩ := θ.purv_cover (shift^[p + 1] a) (mem_arcAt.2 ⟨p + 1, hp, rfl⟩)
      have h2 : inputs (shift^[p + 1] a) ⊆ b'.1 := by
        rw [← θ.effPart_eq hb' hxb']
        exact hall _ (mem_arcAt.2 ⟨p + 1, hp, rfl⟩)
      have hbb : b = b' := arcBlock_eq_of_mem_mech θ hb hb' hmem (h2 (self_mem_inputs _))
      rw [hbb]
      exact hxb'
  have hmech : arcAt a L ⊆ b.1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := arcAt_subset_windows hL hx
    have h1 : inputs (shift^[i] a) ⊆ b.1 := by
      rw [← θ.effPart_eq hb (key i hi)]
      exact hall _ (mem_arcAt.2 ⟨i, hi, rfl⟩)
    exact h1 hxi
  have hb1 : b.1 = arcAt a L := Finset.Subset.antisymm (θ.mech_subset b hb) hmech
  have hb2 := θ.proper b hb hb1
  rw [hb2] at h0b
  exact Finset.notMem_empty _ h0b

/-- **The cause chain**, with the whole substrate as purview. -/
theorem exists_not_determined_arc_cause {a : Fin N} {L : ℕ} (hL : 3 ≤ L)
    (θ : Partition N (arcAt a L) Finset.univ) :
    ∃ k ∈ arcAt a L, ¬ inputs k ⊆ θ.causePart k := by
  by_contra hall
  push_neg at hall
  obtain ⟨b, hb, h0b⟩ := θ.mech_cover a (self_mem_arcAt a (by omega))
  have key : ∀ i, i < L → shift^[i] a ∈ b.1 := by
    intro i
    induction i with
    | zero => intro _; simpa using h0b
    | succ p ih =>
      intro hp
      have hp' : p < L := by omega
      have hpb := ih hp'
      have h1 : inputs (shift^[p] a) ⊆ b.2 := by
        rw [← θ.causePart_eq hb hpb]
        exact hall _ (mem_arcAt.2 ⟨p, hp', rfl⟩)
      have hmem : shift^[p + 1] a ∈ b.2 := by
        rw [Function.iterate_succ_apply']
        exact h1 (shift_mem_inputs _)
      obtain ⟨b', hb', hxb'⟩ := θ.mech_cover (shift^[p + 1] a) (mem_arcAt.2 ⟨p + 1, hp, rfl⟩)
      have h2 : inputs (shift^[p + 1] a) ⊆ b'.2 := by
        rw [← θ.causePart_eq hb' hxb']
        exact hall _ (mem_arcAt.2 ⟨p + 1, hp, rfl⟩)
      have hbb : b = b' := arcBlock_eq_of_mem_purv θ hb hb' hmem (h2 (self_mem_inputs _))
      rw [hbb]
      exact hxb'
  have hmech : arcAt a L ⊆ b.1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_arcAt.1 hx
    exact key i hi
  have hb1 : b.1 = arcAt a L := Finset.Subset.antisymm (θ.mech_subset b hb) hmech
  have hb2 := θ.proper b hb hb1
  have h00 := hall a (self_mem_arcAt a (by omega))
  rw [θ.causePart_eq hb h0b, hb2] at h00
  exact Finset.notMem_empty _ (h00 (self_mem_inputs a))

end Chain

/-! ## The integrated information of an arc -/

section PhiBounds

variable [NeZero N]

/-- **`φ_e ≥ 1`** for an arc, witnessed on its determined set. -/
theorem one_le_phiEmech_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    1 ≤ phiEmech (circNet N) Finset.univ (arcAt a L) allOnes :=
  one_le_phiEmech_circNet hN h3 (arcAt a L) (arcAt a (L - 2)) (arcAt_nonempty a (by omega))
    (fun _ hk => inputs_subset_of_mem_arcDet hk)
    (fun θ => exists_not_determined_arc_eff hL θ)

/-- **`φ_c ≥ (1/2)^N`** for an arc. -/
theorem le_phiCmech_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    (1 / 2 : ℝ) ^ N ≤ phiCmech (circNet N) Finset.univ (arcAt a L) allOnes := by
  refine le_trans ?_ (le_phiCmech_circNet hN h3 (arcAt a L) (arcAt_nonempty a (by omega))
    (fun θ => exists_not_determined_arc_cause hL θ))
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le _ _)

/-- **`φ_d ≥ (1/2)^N`** for an arc. -/
theorem le_phiD_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    (1 / 2 : ℝ) ^ N ≤ phiD (circNet N) Finset.univ (arcAt a L) allOnes := by
  rw [phiD]
  refine le_min (le_phiCmech_arc hN h3 a hL) ?_
  refine le_trans ?_ (one_le_phiEmech_arc hN h3 a hL)
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem phiD_arc_pos (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    0 < phiD (circNet N) Finset.univ (arcAt a L) allOnes :=
  lt_of_lt_of_le (by positivity) (le_phiD_arc hN h3 a hL)

lemma phiCmech_arc_pos (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    0 < phiCmech (circNet N) Finset.univ (arcAt a L) allOnes :=
  lt_of_lt_of_le (by positivity) (le_phiCmech_arc hN h3 a hL)

/-- **The hull lemma for an arc**: the arc lies inside every maximizing cause purview, so a
chosen unit of the arc lands in the support of its distinction. -/
theorem hull_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (a : Fin N) {L : ℕ} (hL : 3 ≤ L)
    {p : Finset (Fin N) × State N}
    (hp : p ∈ maxCausePurviews (circNet N) Finset.univ (arcAt a L) allOnes) :
    arcAt a L ⊆ p.1 :=
  mem_of_mem_maxCausePurviews hN (arcAt a L) allOnes (phiCmech_arc_pos hN h3 a hL) hp

end PhiBounds

/-! ## Arcs are distinction mechanisms -/

section DistinctionMech

variable [NeZero N]

/-- **Every arc of length `3 ≤ L` specifies a distinction** `[IIT4, Eq 48]` at the
all-ones state. -/
theorem isDistinctionMech_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) (a : Fin N)
    {L : ℕ} (hL : 3 ≤ L) :
    IsDistinctionMech (circNet N) Finset.univ u allOnes (arcAt a L) := by
  unfold IsDistinctionMech
  refine ⟨phiD_arc_pos hN h3 a hL, ?_⟩
  obtain ⟨p₀, hp₀⟩ :=
    maxCausePurviews_nonempty (circNet N) Finset.univ (arcAt a L) allOnes
  have hc := mem_maxCausePurviews_circNet_allOnes hN (arcAt a L)
    (phiCmech_arc_pos hN h3 a hL) hp₀
  obtain ⟨p₁, hp₁⟩ :=
    maxEffPurviews_nonempty (circNet N) Finset.univ (arcAt a L) allOnes
  have he := mem_maxEffPurviews_circNet_allOnes hN h3 (arcAt a L) hp₁
  refine ⟨(p₀.1, allOnes), hc, (p₁.1, allOnes), he, ?_⟩
  exact congruent_circNet_of_subset hN h3 u (stated_allOnes_subset_univ _)
    (stated_allOnes_subset_univ _)

theorem arc_mem_distinctionMechs (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N) (a : Fin N)
    {L : ℕ} (hL : 3 ≤ L) :
    arcAt a L ∈ distinctionMechs (circNet N) Finset.univ u allOnes :=
  mem_distinctionMechs.2 ⟨Finset.subset_univ _, isDistinctionMech_arc hN h3 u a hL⟩

end DistinctionMech

/-! ## The distinction of an arc under any selector -/

section Support

variable [NeZero N]

/-- **The shared stated unit.**  A unit of the arc -- in particular `0`, when the arc
contains it -- lies in the support of the arc's distinction, in state `true`. -/
theorem zero_mem_support_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) (a : Fin N) {L : ℕ} (hL : 3 ≤ L)
    (h0 : (0 : Fin N) ∈ arcAt a L) :
    ((0 : Fin N), true) ∈ (distinctionOf (circNet N) Finset.univ u allOnes σ (arcAt a L)
      (arc_mem_distinctionMechs hN h3 u a hL)).support := by
  have hM := arc_mem_distinctionMechs hN h3 u a hL
  have hcong := subset_of_congruent_circNet hN h3 u (σ.congruent _ hM)
  have hmem := mem_stated_of_mem_maxCausePurviews hN (arcAt a L) allOnes
    (phiCmech_arc_pos hN h3 a hL) (σ.cause_mem _ hM) hcong.1 h0
  exact Finset.mem_union_left _ hmem

/-- The support of an arc distinction has at most `2 N` stated units. -/
theorem support_card_le_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    ((distinctionOf (circNet N) Finset.univ u allOnes σ (arcAt a L)
      (arc_mem_distinctionMechs hN h3 u a hL)).support).card ≤ 2 * N := by
  change (stated (σ.causeOf (arcAt a L)).1 (σ.causeOf (arcAt a L)).2 ∪
      stated (σ.effectOf (arcAt a L)).1 (σ.effectOf (arcAt a L)).2).card ≤ 2 * N
  refine (Finset.card_union_le _ _).trans ?_
  rw [card_stated, card_stated]
  have h1 : (σ.causeOf (arcAt a L)).1.card ≤ N := by
    simpa using Finset.card_le_univ (σ.causeOf (arcAt a L)).1
  have h2 : (σ.effectOf (arcAt a L)).1.card ≤ N := by
    simpa using Finset.card_le_univ (σ.effectOf (arcAt a L)).1
  omega

/-- **Per-unit integration of an arc distinction is at least `(1/2)^N / (2 N)`**
`[IIT4, Eq 53]`. -/
theorem le_phiPerUnit_arc (hN : 3 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) (a : Fin N) {L : ℕ} (hL : 3 ≤ L) :
    (1 / 2 : ℝ) ^ N / (2 * N) ≤ (distinctionOf (circNet N) Finset.univ u allOnes σ
      (arcAt a L) (arc_mem_distinctionMechs hN h3 u a hL)).phiPerUnit := by
  set D := distinctionOf (circNet N) Finset.univ u allOnes σ (arcAt a L)
    (arc_mem_distinctionMechs hN h3 u a hL) with hD
  have hphi : (1 / 2 : ℝ) ^ N ≤ D.phi := le_phiD_arc hN h3 a hL
  have hcard : (D.support.card : ℝ) ≤ 2 * N := by
    exact_mod_cast support_card_le_arc hN h3 u σ a hL
  have hc0 : (0 : ℝ) < D.support.card := by exact_mod_cast D.card_support_pos
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < 2 * N := by linarith
  rw [Distinction.phiPerUnit, div_le_div_iff₀ hN0 hc0]
  exact mul_le_mul hphi hcard hc0.le D.phi_pos.le

end Support

/-! ## The arc family -/

section Family

variable [NeZero N]

/-- The parameter rectangle: the arc `[-s, e]` for `1 ≤ s < N/2` and `1 ≤ e < N - N/2`. -/
noncomputable def arcParams (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (N / 2)) ×ˢ (Finset.Ico 1 (N - N / 2))

lemma mem_arcParams {p : ℕ × ℕ} :
    p ∈ arcParams N ↔ (1 ≤ p.1 ∧ p.1 < N / 2) ∧ (1 ≤ p.2 ∧ p.2 < N - N / 2) := by
  simp [arcParams, Finset.mem_product, Finset.mem_Ico]

lemma card_arcParams : (arcParams N).card = (N / 2 - 1) * (N - N / 2 - 1) := by
  rw [arcParams, Finset.card_product, Nat.card_Ico, Nat.card_Ico]

/-- The arc of a parameter pair: start `-s`, length `s + e + 1`, so it contains `0`. -/
noncomputable def paramArc (p : ℕ × ℕ) : Finset (Fin N) :=
  arcAt (shift^[N - p.1] (0 : Fin N)) (p.1 + p.2 + 1)

lemma three_le_paramLength {p : ℕ × ℕ} (hp : p ∈ arcParams N) : 3 ≤ p.1 + p.2 + 1 := by
  rw [mem_arcParams] at hp
  omega

lemma paramLength_le {p : ℕ × ℕ} (hN : 8 ≤ N) (hp : p ∈ arcParams N) :
    p.1 + p.2 + 1 ≤ N - 1 := by
  rw [mem_arcParams] at hp
  omega

lemma zero_mem_paramArc {p : ℕ × ℕ} (hN : 8 ≤ N) (hp : p ∈ arcParams N) :
    (0 : Fin N) ∈ paramArc (N := N) p := by
  have hp' := hp
  rw [mem_arcParams] at hp'
  refine mem_arcAt.2 ⟨p.1, by omega, ?_⟩
  rw [← Function.iterate_add_apply]
  have he : p.1 + (N - p.1) = N := by omega
  rw [he, shift_iterate_self]

lemma paramArc_injective (hN : 8 ≤ N) {p q : ℕ × ℕ} (hp : p ∈ arcParams N)
    (hq : q ∈ arcParams N) (h : paramArc (N := N) p = paramArc (N := N) q) : p = q := by
  have hp' := hp
  have hq' := hq
  rw [mem_arcParams] at hp' hq'
  obtain ⟨hstart, hlen⟩ := arcAt_injective (by omega) (paramLength_le hN hp)
    (by omega) (paramLength_le hN hq) h
  have hs : N - p.1 = N - q.1 :=
    shift_iterate_inj (a := (0 : Fin N)) (by omega) (by omega) hstart
  have h1 : p.1 = q.1 := by omega
  have h2 : p.2 = q.2 := by omega
  exact Prod.ext h1 h2

lemma paramArc_mem_distinctionMechs (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    {p : ℕ × ℕ} (hp : p ∈ arcParams N) :
    paramArc (N := N) p ∈ distinctionMechs (circNet N) Finset.univ u allOnes :=
  arc_mem_distinctionMechs (by omega) h3 u _ (three_le_paramLength hp)

/-- **The arc family**: the distinctions of the arcs containing `0` cut out by the
parameter rectangle, bundled under a selector `σ`. -/
noncomputable def circArcFamily (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) : Finset (Distinction N) :=
  (arcParams N).attach.image fun p =>
    distinctionOf (circNet N) Finset.univ u allOnes σ (paramArc (N := N) p.1)
      (paramArc_mem_distinctionMechs hN h3 u p.2)

lemma circArcFamily_injective (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    Function.Injective (fun p : {x // x ∈ arcParams N} =>
      distinctionOf (circNet N) Finset.univ u allOnes σ (paramArc (N := N) p.1)
        (paramArc_mem_distinctionMechs hN h3 u p.2)) := by
  intro p q h
  apply Subtype.ext
  exact paramArc_injective hN p.2 q.2 (congrArg Distinction.mech h)

/-- **The arc family has `(N/2 - 1)(N - N/2 - 1)` members.** -/
theorem card_circArcFamily (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    (circArcFamily hN h3 u σ).card = (N / 2 - 1) * (N - N / 2 - 1) := by
  rw [circArcFamily, Finset.card_image_of_injective _ (circArcFamily_injective hN h3 u σ),
    Finset.card_attach, card_arcParams]

/-- The parameter rectangle is quadratic: `N²/8 ≤ (N/2 - 1)(N - N/2 - 1)` for `8 ≤ N`. -/
theorem nat_sq_div_eight_le {N : ℕ} (hN : 8 ≤ N) :
    N ^ 2 / 8 ≤ (N / 2 - 1) * (N - N / 2 - 1) := by
  obtain ⟨x, y, hx, hy⟩ : ∃ x y : ℕ, N / 2 - 1 = x ∧ N - N / 2 - 1 = y := ⟨_, _, rfl, rfl⟩
  have h1 : N = x + y + 2 := by omega
  have h2 : 3 ≤ x := by omega
  have h3 : y = x ∨ y = x + 1 := by omega
  rw [hx, hy]
  have hkey : N ^ 2 ≤ 8 * (x * y) := by
    rcases h3 with h | h
    · rw [h1, h]
      nlinarith [Nat.mul_le_mul h2 (le_refl x)]
    · rw [h1, h]
      nlinarith [Nat.mul_le_mul h2 (le_refl x)]
  calc N ^ 2 / 8 ≤ 8 * (x * y) / 8 := Nat.div_le_div_right hkey
    _ = x * y := Nat.mul_div_cancel_left _ (by norm_num)

/-- **`N²/8` is a lower bound on the size of the arc family.** -/
theorem sq_div_eight_le_card_circArcFamily (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    N ^ 2 / 8 ≤ (circArcFamily hN h3 u σ).card := by
  rw [card_circArcFamily]
  exact nat_sq_div_eight_le hN

/-- The arc family lies inside the distinctions `[IIT4, Eq 48]` of the structure. -/
theorem circArcFamily_subset_distinctions (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    circArcFamily hN h3 u σ ⊆ distinctions (circNet N) Finset.univ u allOnes σ := by
  intro D hD
  unfold circArcFamily at hD
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hD
  rw [distinctions]
  exact Finset.mem_image.2
    ⟨⟨paramArc (N := N) p.1, paramArc_mem_distinctionMechs hN h3 u p.2⟩,
      Finset.mem_attach _ _, rfl⟩

/-- Every member of the arc family has `(0, true)` in its support. -/
theorem mem_circArcFamily_shared (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    ∀ D ∈ circArcFamily hN h3 u σ, ((0 : Fin N), true) ∈ D.support := by
  intro D hD
  unfold circArcFamily at hD
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hD
  exact zero_mem_support_arc (by omega) h3 u σ _ (three_le_paramLength p.2)
    (zero_mem_paramArc hN p.2)

/-- Every member of the arc family integrates at least `(1/2)^N / (2 N)` per support
unit. -/
theorem mem_circArcFamily_floor (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    ∀ D ∈ circArcFamily hN h3 u σ, (1 / 2 : ℝ) ^ N / (2 * N) ≤ D.phiPerUnit := by
  intro D hD
  unfold circArcFamily at hD
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hD
  exact le_phiPerUnit_arc (by omega) h3 u σ _ (three_le_paramLength p.2)

end Family

/-! ## Assembly -/

section Assembly

variable [NeZero N]

/-- **`Φ_max ≥ (2^{|F|} - 1 - |F|) · (1/2)^N / (2 N)`** for the interval circulant at
all-ones, `8 ≤ N`, `3 ∤ N`, any background: the arc family fed to
`doubly_exp_le_PhiMax_of_family`. -/
theorem card_family_le_PhiMax_circNet (hN : 8 ≤ N) (h3 : ¬ (3 ∣ N)) (u : State N)
    (σ : Selector (circNet N) Finset.univ u allOnes) :
    ((2 ^ (circArcFamily hN h3 u σ).card - 1 - (circArcFamily hN h3 u σ).card : ℕ) : ℝ)
        * ((1 / 2 : ℝ) ^ N / (2 * N))
      ≤ PhiMax (circNet N) Finset.univ u allOnes := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ N / (2 * N) := div_pos (by positivity) (by linarith)
  exact doubly_exp_le_PhiMax_of_family hc (mem_circArcFamily_shared hN h3 u σ)
    (mem_circArcFamily_floor hN h3 u σ) (circArcFamily_subset_distinctions hN h3 u σ)

/-- **`Φ_max ≥ 2^{N²/8} · (1/2)^N / (2 N) - 1`**: the bound of
`card_family_le_PhiMax_circNet` with the quadratic floor on the family size inserted and
the second-order terms absorbed into the `- 1`.  Doubly exponential in `N`. -/
theorem two_pow_sq_le_PhiMax_circNet (h3 : ¬ (3 ∣ N)) (hN : 8 ≤ N) (u : State N) :
    (2 : ℝ) ^ (N ^ 2 / 8) * ((1 / 2 : ℝ) ^ N / (2 * N)) - 1
      ≤ PhiMax (circNet N) Finset.univ u allOnes := by
  have σ : Selector (circNet N) Finset.univ u allOnes := Classical.arbitrary _
  refine le_trans ?_ (card_family_le_PhiMax_circNet hN h3 u σ)
  set K := (circArcFamily hN h3 u σ).card with hK
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hc : (0 : ℝ) < (1 / 2 : ℝ) ^ N / (2 * N) := div_pos (by positivity) (by linarith)
  have hA : K + 1 ≤ 2 ^ K := by
    have hlt : K < 2 ^ K := Nat.lt_two_pow_self
    omega
  have hcast : ((2 ^ K - 1 - K : ℕ) : ℝ) = (2 : ℝ) ^ K - 1 - K := by
    have hsub : 2 ^ K - 1 - K = 2 ^ K - (K + 1) := by omega
    rw [hsub, Nat.cast_sub hA]
    push_cast
    ring
  rw [hcast]
  have hKge : N ^ 2 / 8 ≤ K := by
    rw [hK]
    exact sq_div_eight_le_card_circArcFamily hN h3 u σ
  have hpow : (2 : ℝ) ^ (N ^ 2 / 8) ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hKge
  have hKN : K ≤ N * N := by
    rw [hK, card_circArcFamily]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hlt : N < 2 ^ N := Nat.lt_two_pow_self
  have hnat : K + 1 ≤ 2 ^ N * (2 * N) := by nlinarith [hKN, hlt, hN]
  have hnatr : ((K : ℝ) + 1) ≤ (2 : ℝ) ^ N * (2 * N) := by exact_mod_cast hnat
  have hcval : (1 / 2 : ℝ) ^ N / (2 * N) = 1 / ((2 : ℝ) ^ N * (2 * N)) := by
    rw [one_div_pow, div_div]
  have hsmall : ((K : ℝ) + 1) * ((1 / 2 : ℝ) ^ N / (2 * N)) ≤ 1 := by
    rw [hcval, mul_one_div, div_le_one (by positivity)]
    exact hnatr
  have hstep : (2 : ℝ) ^ (N ^ 2 / 8) * ((1 / 2 : ℝ) ^ N / (2 * N))
      ≤ (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ N / (2 * N)) :=
    mul_le_mul_of_nonneg_right hpow hc.le
  have hexp : ((2 : ℝ) ^ K - 1 - K) * ((1 / 2 : ℝ) ^ N / (2 * N))
      = (2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ N / (2 * N))
        - ((K : ℝ) + 1) * ((1 / 2 : ℝ) ^ N / (2 * N)) := by ring
  rw [hexp]
  linarith

end Assembly

end IIT
