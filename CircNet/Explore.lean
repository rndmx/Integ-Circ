import IIT

/-!
# A system with `φ_s > 0` in every dimension

For each `N ≥ 2` this file exhibits a substrate of `N` units whose system integrated
information is bounded below by `1`, proved rather than computed.  The point is that the
bound holds for every `N`, including sizes beyond the reach of direct evaluation.

## The system

`copyRing N` is the cyclic COPY network: unit `i` takes the state unit `i - 1` had at the
previous step, deterministically.  Its transition matrix is a permutation matrix, which is
what makes the argument short.

## The argument

Fix the whole substrate as the candidate system and any state `s`.

* The dynamics is deterministic, so at the state `t` it actually produces,
  `sysEffProb = 1`.
* Every admissible partition severs at least one ring edge.  `[IIT4, Eq 14]` requires two
  or more blocks, so no block is all of `S`, and a proper nonempty subset of a cycle always
  contains a unit whose predecessor lies outside it.  That unit's conditioning set loses
  its only input, so its `effUnit` averages a fair coin: exactly `1/2`.
* Hence `sysPartEffProb ≤ 1/2`, and `sysPhiE = 1 · log₂(1 / (1/2)) ≥ 1` for *every*
  partition, so in particular at the minimum information partition.

The cause side is the same argument run backwards, the ring being a permutation.

Nothing here evaluates a logarithm or enumerates a partition: the bound comes from the
connectivity of the cycle, uniformly in `N`.
-/

namespace IIT

variable {N : ℕ}

/-! ### The cyclic COPY network -/

/-- The cyclic COPY network on `N` units: unit `i` copies the previous state of unit
`i - 1`, indices read modulo `N`. -/
noncomputable def copyRing (N : ℕ) [NeZero N] : UnitTPM N where
  prob i s b := if b = s (i - 1) then 1 else 0
  nonneg i s b := by by_cases h : b = s (i - 1) <;> simp [h]
  normalized i s := by cases h : s (i - 1) <;> simp [h]

/-! ### Connectivity of the cycle

The one combinatorial input: a nonempty set of units closed under taking predecessors is
everything.  Contrapositively, a proper nonempty subset of the ring has a unit whose
predecessor lies outside it, which is the edge a partition severs. -/

/-- A nonempty set closed under predecessor is the whole ring. -/
theorem eq_univ_of_pred_closed [NeZero N] {r : Finset (Fin N)} (hne : r.Nonempty)
    (hcl : ∀ j ∈ r, j - 1 ∈ r) : r = Finset.univ := by
  obtain ⟨j₀, hj₀⟩ := hne
  have key : ∀ v : ℕ, ∀ d : Fin N, d.val = v → j₀ - d ∈ r := by
    intro v
    induction v with
    | zero =>
        intro d hd
        have h0 : d = 0 := by ext; simp [hd]
        simpa [h0] using hj₀
    | succ k ih =>
        intro d hd
        have hd0 : d ≠ 0 := by
          intro h0
          rw [h0] at hd
          simp at hd
        have hpred : (d - 1).val = k := by
          rw [Fin.val_sub_one_of_ne_zero hd0, hd]
          omega
        have hmem := hcl _ (ih (d - 1) hpred)
        have harith : j₀ - (d - 1) - 1 = j₀ - d := by abel
        rwa [harith] at hmem
  refine Finset.eq_univ_of_forall fun k => ?_
  have h := key (j₀ - k).val (j₀ - k) rfl
  have harith : j₀ - (j₀ - k) = k := by abel
  rwa [harith] at h

/-- A proper nonempty subset of the ring contains a unit whose predecessor is outside it. -/
theorem exists_pred_not_mem [NeZero N] {r : Finset (Fin N)} (hne : r.Nonempty)
    (hlt : r ≠ Finset.univ) : ∃ j ∈ r, j - 1 ∉ r := by
  by_contra h
  exact hlt (eq_univ_of_pred_closed hne (by simpa using h))

/-! ### A severed unit contributes exactly one half

If the conditioning set omits unit `j`'s only input then `effUnit` averages over both
values of that input, and the two branches of the `if` contribute `1` and `0`. -/

/-- `effUnit` of the ring on a conditioning set that omits the predecessor. -/
theorem effUnit_copyRing_of_pred_not_mem [NeZero N] (W : Finset (Fin N)) (m : State N)
    (j : Fin N) (b : Bool) (h : j - 1 ∉ W) :
    effUnit (copyRing N) W m j b = 1 / 2 := by
  have hWlt : W.card < N := by
    by_contra hge
    push_neg at hge
    have hcard : W.card = N :=
      le_antisymm (by simpa using W.card_le_univ) hge
    have huniv : W = Finset.univ :=
      Finset.eq_univ_of_card W (by simp [hcard])
    rw [huniv] at h
    exact h (Finset.mem_univ _)
  have hsum : ∑ s ∈ agree W m, (copyRing N).prob j s b
      = ((agree (insert (j - 1) W) (Function.update m (j - 1) b)).card : ℝ) := by
    have hset : (agree W m).filter (fun s => b = s (j - 1))
        = agree (insert (j - 1) W) (Function.update m (j - 1) b) := by
      ext s
      simp only [Finset.mem_filter, mem_agree, Finset.mem_insert]
      constructor
      · rintro ⟨hW, hb⟩ i hi
        rcases hi with rfl | hiW
        · rw [Function.update_self]; exact hb.symm
        · rw [Function.update_of_ne (by rintro rfl; exact h hiW)]
          exact hW i hiW
      · intro hall
        refine ⟨fun i hiW => ?_, ?_⟩
        · have hi := hall i (Or.inr hiW)
          rwa [Function.update_of_ne (by rintro rfl; exact h hiW)] at hi
        · have hi := hall (j - 1) (Or.inl rfl)
          rw [Function.update_self] at hi
          exact hi.symm
    rw [← hset]
    simp [copyRing, Finset.sum_boole]
  rw [effUnit, hsum, card_agree, card_agree, Finset.card_insert_of_notMem h]
  rw [show N - W.card = (N - (W.card + 1)) + 1 from by omega, pow_succ]
  have hpos : (0 : ℝ) < 2 ^ (N - (W.card + 1)) := by positivity
  push_cast
  field_simp

/-- `effUnit` of the ring on a conditioning set that retains the predecessor. -/
theorem effUnit_copyRing_of_pred_mem [NeZero N] (W : Finset (Fin N)) (m : State N)
    (j : Fin N) (b : Bool) (h : j - 1 ∈ W) :
    effUnit (copyRing N) W m j b = if b = m (j - 1) then 1 else 0 := by
  rw [effUnit]
  have hconst : ∀ s ∈ agree W m,
      (copyRing N).prob j s b = if b = m (j - 1) then 1 else 0 := by
    intro s hs
    have hval := mem_agree.1 hs _ h
    simp [copyRing, hval]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (agree W m).card := by
    exact_mod_cast Finset.card_pos.2 (agree_nonempty W m)
  field_simp

/-! ### The bound -/

/-- The state the ring produces from `s`: every unit takes its predecessor's state. -/
def ringNext [NeZero N] (s : State N) : State N := fun i => s (i - 1)

/-- The dynamics is deterministic, so the effect probability of the state it produces
is `1`. -/
theorem sysEffProb_copyRing [NeZero N] (u s : State N) :
    sysEffProb (copyRing N) Finset.univ u s (ringNext s) = 1 := by
  rw [sysEffProb, merge_univ]
  exact Finset.prod_eq_one fun i _ => by simp [copyRing, ringNext]

/-- No block of an admissible partition is the whole substrate: there are at least two,
disjoint and nonempty. -/
private lemma part_ne_univ [NeZero N] (θ : SysPartition N Finset.univ)
    {p : Finset (Fin N)} (hp : p ∈ θ.parts) : p ≠ Finset.univ := by
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (lt_of_lt_of_le one_lt_two θ.two_le) p
  obtain ⟨x, hx⟩ := θ.parts_nonempty q hq
  intro hup
  exact Finset.disjoint_left.1 (θ.parts_disjoint q hq p hp hqp) hx (hup ▸ Finset.mem_univ x)

/-- Every admissible partition severs a ring edge. -/
theorem exists_severed [NeZero N] (θ : SysPartition N Finset.univ) :
    ∃ j : Fin N, j - 1 ∈ θ.cutSet (θ.partOf j) := by
  by_cases hall : ∀ p ∈ θ.parts, θ.dir p = Dir.outputs
  · -- every block severs only its outputs, so each is cut by all the others
    have hpne : θ.parts.Nonempty :=
      Finset.card_pos.1 (lt_of_lt_of_le two_pos θ.two_le)
    obtain ⟨p, hp⟩ := hpne
    obtain ⟨j, hjp, hjpred⟩ :=
      exists_pred_not_mem (θ.parts_nonempty p hp) (part_ne_univ θ hp)
    obtain ⟨q, hq, hjq⟩ := θ.parts_cover (j - 1) (Finset.mem_univ _)
    have hqp : q ≠ p := fun h => hjpred (h ▸ hjq)
    refine ⟨j, ?_⟩
    rw [θ.partOf_eq hp hjp, SysPartition.cutSet, hall p hp]
    exact (Finset.le_sup (f := id)
      (Finset.mem_filter.2 ⟨hq, hqp, Or.inl (hall q hq)⟩)) hjq
  · -- some block severs its inputs, cutting it from the rest of the substrate
    push_neg at hall
    obtain ⟨p, hp, hdp⟩ := hall
    obtain ⟨j, hjp, hjpred⟩ :=
      exists_pred_not_mem (θ.parts_nonempty p hp) (part_ne_univ θ hp)
    refine ⟨j, ?_⟩
    rw [θ.partOf_eq hp hjp, SysPartition.cutSet]
    cases hd : θ.dir p with
    | inputs => exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hjpred⟩
    | both => exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hjpred⟩
    | outputs => exact absurd hd hdp

/-- The partitioned effect probability is at most one half. -/
theorem sysPartEffProb_copyRing_le [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartEffProb (copyRing N) Finset.univ u θ s (ringNext s) ≤ 1 / 2 := by
  obtain ⟨j₀, hj₀⟩ := exists_severed θ
  rw [sysPartEffProb, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀),
    effUnit_copyRing_of_pred_not_mem _ _ _ _ (by simpa using hj₀)]
  refine mul_le_of_le_one_right (by norm_num) ?_
  exact Finset.prod_le_one (fun j _ => effUnit_nonneg _ _ _ j _)
    (fun j _ => effUnit_le_one _ _ _ j _)

/-! ### The ring is a permutation

Exactly one prior state produces each state, which is what collapses every unconstrained
average to `2^{-N}` and pins both maximal cause--effect states. -/

/-- The state the ring came from: every unit hands its state to its successor. -/
def ringPrev [NeZero N] (s : State N) : State N := fun i => s (i + 1)

lemma ringNext_ringPrev [NeZero N] (s : State N) : ringNext (ringPrev s) = s := by
  funext i
  show s (i - 1 + 1) = s i
  congr 1
  abel

lemma ringPrev_ringNext [NeZero N] (s : State N) : ringPrev (ringNext s) = s := by
  funext i
  show s (i + 1 - 1) = s i
  congr 1
  abel

/-- `sysEffProb` of the ring is the indicator of the state it produces. -/
lemma sysEffProb_copyRing_eq [NeZero N] (u s t : State N) :
    sysEffProb (copyRing N) Finset.univ u s t = if t = ringNext s then 1 else 0 := by
  by_cases ht : t = ringNext s
  · rw [ht, if_pos rfl, sysEffProb_copyRing]
  · rw [if_neg ht, sysEffProb, merge_univ]
    have hex : ∃ i, t i ≠ s (i - 1) := by
      by_contra hall
      push_neg at hall
      exact ht (funext fun i => hall i)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [copyRing, hi])

/-- `fullProb` of the ring is the same indicator. -/
lemma fullProb_copyRing_eq [NeZero N] (v t : State N) :
    fullProb (copyRing N) v t = if t = ringNext v then 1 else 0 := by
  have h := sysEffProb_copyRing_eq v v t
  rwa [sysEffProb, merge_univ] at h

/-- The current state is reachable: its unique preimage contributes `1`. -/
lemma sum_fullProb_copyRing_pos [NeZero N] (u : State N) :
    0 < ∑ v : State N, fullProb (copyRing N) v u := by
  refine Finset.sum_pos' (fun v _ => fullProb_nonneg _ v u)
    ⟨ringPrev u, Finset.mem_univ _, ?_⟩
  rw [fullProb_copyRing_eq, ringNext_ringPrev, if_pos rfl]
  norm_num

lemma sysUncEff_copyRing [NeZero N] (u t : State N) :
    sysUncEff (copyRing N) Finset.univ u t = 1 / 2 ^ N := by
  rw [sysUncEff, avgOverStates]
  have hswap : ∀ s : State N,
      sysEffProb (copyRing N) Finset.univ u s t = if s = ringPrev t then (1 : ℝ) else 0 := by
    intro s
    rw [sysEffProb_copyRing_eq]
    by_cases hs : s = ringPrev t
    · subst hs
      simp [ringNext_ringPrev]
    · rw [if_neg fun ht => hs (by rw [ht, ringPrev_ringNext]), if_neg hs]
  rw [Finset.sum_congr rfl fun s _ => hswap s,
    Fintype.sum_ite_eq' (ringPrev t) fun _ => (1 : ℝ)]

lemma sysCauseProb_copyRing [NeZero N] (u s t : State N) :
    sysCauseProb (copyRing N) Finset.univ u s t = if t = ringPrev s then 1 else 0 := by
  rw [sysCauseProb_univ _ _ _ _ (sum_fullProb_copyRing_pos u), fullProb_copyRing_eq]
  congr 1
  apply propext
  constructor
  · rintro rfl; rw [ringPrev_ringNext]
  · rintro rfl; rw [ringNext_ringPrev]

lemma sysUncCause_copyRing [NeZero N] (u s : State N) :
    sysUncCause (copyRing N) Finset.univ u s = 1 / 2 ^ N := by
  rw [sysUncCause, avgOverStates,
    Finset.sum_congr rfl fun t _ => sysCauseProb_copyRing u s t,
    Fintype.sum_ite_eq' (ringPrev s) fun _ => (1 : ℝ)]

/-! ### The intrinsic informations, exactly -/

lemma sysIiE_copyRing [NeZero N] (u s t : State N) :
    sysIiE (copyRing N) Finset.univ u s t = if t = ringNext s then (N : ℝ) else 0 := by
  rw [sysIiE, sysEffProb_copyRing_eq, sysUncEff_copyRing]
  by_cases ht : t = ringNext s
  · rw [if_pos ht, if_pos ht, one_mul, one_div_one_div, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]
  · rw [if_neg ht, if_neg ht, zero_mul]

lemma sysIiC_copyRing [NeZero N] (u s t : State N) :
    sysIiC (copyRing N) Finset.univ u s t = if t = ringPrev s then (N : ℝ) else 0 := by
  rw [sysIiC, sysBackCause, sysCauseProb_copyRing, sysUncCause_copyRing]
  by_cases ht : t = ringPrev s
  · rw [if_pos ht, if_pos ht, one_div_one_div, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one, Finset.card_univ, Fintype.card_fin]
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  · rw [if_neg ht, if_neg ht, zero_div, zero_mul]

lemma ringNext_mem_sysMaxEffStates [NeZero N] (u s : State N) :
    ringNext s ∈ sysMaxEffStates (copyRing N) Finset.univ u s := by
  rw [sysMaxEffStates, argmaxSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun t => ?_⟩
  rw [sysIiE_copyRing, sysIiE_copyRing, if_pos rfl]
  split
  · exact le_refl _
  · exact Nat.cast_nonneg N

lemma ringPrev_mem_sysMaxCauseStates [NeZero N] (u s : State N) :
    ringPrev s ∈ sysMaxCauseStates (copyRing N) Finset.univ u s := by
  rw [sysMaxCauseStates, argmaxSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun t => ?_⟩
  rw [sysIiC_copyRing, sysIiC_copyRing, if_pos rfl]
  split
  · exact le_refl _
  · exact Nat.cast_nonneg N

/-! ### Both directions of `φ_s` are at least `1` at every partition -/

lemma sysPartEffProb_copyRing_pos [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    0 < sysPartEffProb (copyRing N) Finset.univ u θ s (ringNext s) := by
  rw [sysPartEffProb]
  refine Finset.prod_pos fun j _ => ?_
  rw [merge_univ]
  by_cases h : j - 1 ∈ (θ.cutSet (θ.partOf j))ᶜ
  · rw [effUnit_copyRing_of_pred_mem _ _ _ _ h]
    have hval : ringNext s j = s (j - 1) := rfl
    rw [hval, if_pos rfl]
    norm_num
  · rw [effUnit_copyRing_of_pred_not_mem _ _ _ _ h]
    norm_num

lemma one_le_sysPhiE_copyRing [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    1 ≤ sysPhiE (copyRing N) Finset.univ u θ s (ringNext s) := by
  rw [sysPhiE, sysEffProb_copyRing, one_mul]
  have hx0 := sysPartEffProb_copyRing_pos u s θ
  have hxle := sysPartEffProb_copyRing_le u s θ
  have h2 : (2 : ℝ) ≤ 1 / sysPartEffProb (copyRing N) Finset.univ u θ s (ringNext s) := by
    rw [le_div_iff₀ hx0]
    linarith
  have hlog : (1 : ℝ) ≤ Real.logb 2
      (1 / sysPartEffProb (copyRing N) Finset.univ u θ s (ringNext s)) := by
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  exact hlog.trans (le_pos _)

/-- On the whole substrate the partitioned cause probability collapses to a plain product
of conditioned units, the background sum being constant. -/
lemma sysPartCauseProb_copyRing_univ [NeZero N] (u s t : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (copyRing N) Finset.univ u θ s t
      = ∏ j, effUnit (copyRing N) (θ.cutSet (θ.partOf j))ᶜ t j (s j) := by
  rw [sysPartCauseProb]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
    rw [bgWeight_univ _ _ _ (sum_fullProb_copyRing_pos u), mul_one, merge_univ]]
  rw [Finset.sum_const, card_state, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  push_cast
  field_simp

lemma sysPartCauseProb_copyRing_pos [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    0 < sysPartCauseProb (copyRing N) Finset.univ u θ s (ringPrev s) := by
  rw [sysPartCauseProb_copyRing_univ]
  refine Finset.prod_pos fun j _ => ?_
  by_cases h : j - 1 ∈ (θ.cutSet (θ.partOf j))ᶜ
  · rw [effUnit_copyRing_of_pred_mem _ _ _ _ h]
    have hval : ringPrev s (j - 1) = s j := by
      show s (j - 1 + 1) = s j
      congr 1
      abel
    rw [hval, if_pos rfl]
    norm_num
  · rw [effUnit_copyRing_of_pred_not_mem _ _ _ _ h]
    norm_num

lemma sysPartCauseProb_copyRing_le [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (copyRing N) Finset.univ u θ s (ringPrev s) ≤ 1 / 2 := by
  obtain ⟨j₀, hj₀⟩ := exists_severed θ
  rw [sysPartCauseProb_copyRing_univ,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀),
    effUnit_copyRing_of_pred_not_mem _ _ _ _ (by simpa using hj₀)]
  refine mul_le_of_le_one_right (by norm_num) ?_
  exact Finset.prod_le_one (fun j _ => effUnit_nonneg _ _ _ j _)
    (fun j _ => effUnit_le_one _ _ _ j _)

lemma one_le_sysPhiC_copyRing [NeZero N] (u s : State N)
    (θ : SysPartition N Finset.univ) :
    1 ≤ sysPhiC (copyRing N) Finset.univ u θ s (ringPrev s) := by
  rw [sysPhiC, sysBackCause, sysCauseProb_copyRing, if_pos rfl, sysUncCause_copyRing,
    Finset.card_univ, Fintype.card_fin]
  have hback : (1 : ℝ) / ((2 : ℝ) ^ N * (1 / 2 ^ N)) = 1 := by
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  rw [hback, one_mul]
  have hx0 := sysPartCauseProb_copyRing_pos u s θ
  have hxle := sysPartCauseProb_copyRing_le u s θ
  have h2 : (2 : ℝ) ≤ 1 / sysPartCauseProb (copyRing N) Finset.univ u θ s (ringPrev s) := by
    rw [le_div_iff₀ hx0]
    linarith
  have hlog : (1 : ℝ) ≤ Real.logb 2
      (1 / sysPartCauseProb (copyRing N) Finset.univ u θ s (ringPrev s)) := by
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  exact hlog.trans (le_pos _)

/-! ### An admissible partition exists, so the MIP set is nonempty -/

/-- The bipartition `{{0}, {0}ᶜ}`, both directions severed: the witness that `[IIT4,
Eq 14]`'s `k ≥ 2` can be met at all, which is what makes `sysMipSetAt` nonempty. -/
noncomputable def twoBlocks [NeZero N] (hN : 2 ≤ N) : SysPartition N Finset.univ where
  parts := {{0}, {0}ᶜ}
  dir _ := Dir.both
  parts_nonempty := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨0, Finset.mem_singleton_self 0⟩
    · rw [Finset.mem_singleton] at hp
      subst hp
      rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
  parts_subset := fun p _ => p.subset_univ
  parts_disjoint := by
    intro p hp q hq hpq
    rcases Finset.mem_insert.1 hp with rfl | hp <;>
      rcases Finset.mem_insert.1 hq with rfl | hq
    · exact absurd rfl hpq
    · rw [Finset.mem_singleton] at hq
      subst hq
      exact disjoint_compl_right
    · rw [Finset.mem_singleton] at hp
      subst hp
      exact disjoint_compl_left
    · rw [Finset.mem_singleton] at hp hq
      subst hp; subst hq
      exact absurd rfl hpq
  parts_cover := by
    intro i _
    by_cases h : i = (0 : Fin N)
    · exact ⟨{0}, Finset.mem_insert_self _ _, by simp [h]⟩
    · exact ⟨{0}ᶜ, Finset.mem_insert.2 (Or.inr (Finset.mem_singleton_self _)),
        by simpa using h⟩
  two_le := by
    have hne : ({0} : Finset (Fin N)) ≠ ({0}ᶜ : Finset (Fin N)) := by
      intro h
      have h0 := Finset.mem_singleton_self (0 : Fin N)
      rw [h] at h0
      simp at h0
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- **`φ_s ≥ 1` for the cyclic COPY network on `N` units**, for every `N ≥ 2` and in every
state.  Proved uniformly in `N`, with no evaluation of `φ_s` at any particular size. -/
theorem one_le_sysPhi_copyRing [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    1 ≤ sysPhi (copyRing N) Finset.univ u s := by
  have hinst : Nonempty (SysPartition N Finset.univ) := ⟨twoBlocks hN⟩
  have hpair : ((ringPrev s, ringNext s) : State N × State N)
      ∈ (sysMaxCauseStates (copyRing N) Finset.univ u s) ×ˢ
        (sysMaxEffStates (copyRing N) Finset.univ u s) :=
    Finset.mem_product.2
      ⟨ringPrev_mem_sysMaxCauseStates u s, ringNext_mem_sysMaxEffStates u s⟩
  refine le_trans ?_ (le_sup'OrZero hpair)
  rw [sysPhiOfState, sysMipSetAt]
  obtain ⟨θ₀, hθ₀⟩ := argminSet_nonempty fun θ =>
    normalizedSysPhiAt (copyRing N) Finset.univ u θ s (ringPrev s) (ringNext s)
  refine le_trans ?_ (le_sup'OrZero hθ₀)
  rw [sysPhiAt]
  exact le_min (one_le_sysPhiC_copyRing u s θ₀) (one_le_sysPhiE_copyRing u s θ₀)

/-!
## A system attaining the maximum, `φ_s = N`

`xorNet N` is the deterministic network in which unit `0` takes the XOR of all `N` units
and unit `i ≠ 0` the XOR of every unit but itself.  For every `N ≥ 2` and every state its
system integrated information is exactly `N`, the largest value `N` binary units admit.

## The argument

* Flipping any unit `k` flips the parity, hence flips the next state of every unit
  `j ≠ k`.  So a conditioning set that omits some `k ≠ j` leaves `effUnit` at exactly
  `1/2` (`effUnit_xorNet_of_not_mem`).
* A unit is never in its own block's cut set (`notMem_cutSet_partOf`), so a block with a
  nonempty cut set severs every one of its units.  Writing `m` for the number of severed
  units, both `sysPhiE` and `sysPhiC` are exactly `m` at every partition.
* Counting `[IIT4, Eq 23]`'s normalizer over units rather than blocks
  (`sysCutCount_eq_sum_units`) gives `∑ᵢ |S⁽ⁱ⁾| |X⁽ⁱ⁾| ≤ m (N - 1)`, so the normalized
  quantity is at least `1 / (N - 1)` for every partition.  The all-singletons partition
  attains that value with `m = N`, so it is a minimum information partition and
  `φ_s = N`.

The cause side matches the effect side because the map is a bijection: over `GF(2)` its
matrix is `J + I + e₀e₀ᵀ`, and `Ax = 0` forces `x = 0`.
-/

/-! ### The XOR network -/

/-- The XOR of all `N` units, `Bool` carrying its Boolean-ring addition. -/
def xorAll (s : State N) : Bool := ∑ i, s i

/-- Flipping the state of a single unit. -/
def flipAt (k : Fin N) (s : State N) : State N := Function.update s k (!(s k))

lemma flipAt_apply_self (k : Fin N) (s : State N) : flipAt k s k = !(s k) :=
  Function.update_self ..

lemma flipAt_apply_of_ne {i k : Fin N} (h : i ≠ k) (s : State N) : flipAt k s i = s i :=
  Function.update_of_ne h _ _

lemma flipAt_flipAt (k : Fin N) (s : State N) : flipAt k (flipAt k s) = s := by
  funext i
  by_cases h : i = k
  · subst h
    rw [flipAt_apply_self, flipAt_apply_self, Bool.not_not]
  · rw [flipAt_apply_of_ne h, flipAt_apply_of_ne h]

lemma xorAll_flipAt (k : Fin N) (s : State N) : xorAll (flipAt k s) = !(xorAll s) := by
  have key : ∀ a r : Bool, (!a) + r = !(a + r) := by decide
  have hrest : ∀ i ∈ Finset.univ.erase k, flipAt k s i = s i :=
    fun i hi => flipAt_apply_of_ne (Finset.ne_of_mem_erase hi) s
  rw [xorAll, xorAll, ← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ s (Finset.mem_univ k), Finset.sum_congr rfl hrest,
    flipAt_apply_self]
  exact key _ _

/-- The next state of unit `i`: the XOR of every unit except `i` itself, unit `0`
taking the XOR of all of them. -/
def xorVal [NeZero N] (i : Fin N) (s : State N) : Bool :=
  xor (xorAll s) (if i = 0 then false else s i)

lemma xorVal_flipAt [NeZero N] {j k : Fin N} (h : k ≠ j) (s : State N) :
    xorVal j (flipAt k s) = !(xorVal j s) := by
  have key : ∀ a c : Bool, xor (!a) c = !(xor a c) := by decide
  rw [xorVal, xorVal, xorAll_flipAt, flipAt_apply_of_ne (Ne.symm h) s, key]

/-- The XOR network on `N` units, deterministic as `copyRing` is: unit `0` takes the XOR
of all `N` units and unit `i ≠ 0` the XOR of every unit but itself. -/
noncomputable def xorNet (N : ℕ) [NeZero N] : UnitTPM N where
  prob i s b := if b = xorVal i s then 1 else 0
  nonneg i s b := by by_cases h : b = xorVal i s <;> simp [h]
  normalized i s := by cases h : xorVal i s <;> simp [h]

/-- The state the XOR network produces from `s`. -/
def xorNext [NeZero N] (s : State N) : State N := fun i => xorVal i s

lemma xorNext_injective [NeZero N] : Function.Injective (xorNext : State N → State N) := by
  intro s s' h
  have hval : ∀ i, xorVal i s = xorVal i s' := fun i => congrFun h i
  have hcancel : ∀ a x y : Bool, xor a x = xor a y → x = y := by decide
  have hnotself : ∀ a : Bool, ¬ (a = !a) := by decide
  have hnotof : ∀ a b : Bool, ¬ (a = b) → b = !a := by decide
  have h0 : xorAll s = xorAll s' := by simpa [xorVal] using hval 0
  have hoff : ∀ i, i ≠ 0 → s i = s' i := by
    intro i hi
    have hv := hval i
    rw [xorVal, xorVal, if_neg hi, if_neg hi, h0] at hv
    exact hcancel _ _ _ hv
  funext i
  by_cases hi : i = 0
  · subst hi
    by_contra hne
    have hupd : s' = flipAt 0 s := by
      funext m
      by_cases hm : m = 0
      · subst hm
        rw [flipAt_apply_self]
        exact hnotof _ _ hne
      · rw [flipAt_apply_of_ne hm]
        exact (hoff m hm).symm
    rw [hupd, xorAll_flipAt] at h0
    exact hnotself _ h0
  · exact hoff i hi

/-- The XOR network is a bijection on states, which is what makes the cause side as
strong as the effect side. -/
noncomputable def xorEquiv (N : ℕ) [NeZero N] : State N ≃ State N :=
  Equiv.ofBijective xorNext (Finite.injective_iff_bijective.1 xorNext_injective)

/-- The state the XOR network came from. -/
noncomputable def xorPrev [NeZero N] (s : State N) : State N := (xorEquiv N).symm s

lemma xorNext_xorPrev [NeZero N] (s : State N) : xorNext (xorPrev s) = s :=
  (xorEquiv N).apply_symm_apply s

lemma xorPrev_xorNext [NeZero N] (s : State N) : xorPrev (xorNext s) = s :=
  (xorEquiv N).symm_apply_apply s

/-! ### Halving -/

lemma effUnit_xorNet_univ [NeZero N] (m : State N) (j : Fin N) (b : Bool) :
    effUnit (xorNet N) Finset.univ m j b = if b = xorVal j m then 1 else 0 := by
  rw [effUnit]
  have hconst : ∀ s ∈ agree (Finset.univ : Finset (Fin N)) m,
      (xorNet N).prob j s b = if b = xorVal j m then 1 else 0 := by
    intro s hs
    have hsm : s = m := funext fun i => mem_agree.1 hs i (Finset.mem_univ i)
    rw [hsm]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (agree (Finset.univ : Finset (Fin N)) m).card := by
    exact_mod_cast Finset.card_pos.2 (agree_nonempty _ m)
  field_simp

/-- **A conditioning set that omits any other unit halves `effUnit`.**  Flipping the
omitted unit `k` is an involution of the marginalization fibre that flips unit `j`'s next
state, so exactly half the fibre gives each value. -/
theorem effUnit_xorNet_of_not_mem [NeZero N] (W : Finset (Fin N)) (m : State N)
    (j k : Fin N) (b : Bool) (hk : k ∉ W) (hkj : k ≠ j) :
    effUnit (xorNet N) W m j b = 1 / 2 := by
  classical
  have hbne : ∀ c : Bool, ¬ (c = !c) := by decide
  have hbnot : ∀ c d : Bool, ¬ (c = d) → c = !d := by decide
  have hmaps : ∀ s ∈ agree W m, flipAt k s ∈ agree W m := by
    intro s hs
    rw [mem_agree] at hs ⊢
    intro i hi
    rw [flipAt_apply_of_ne (by rintro rfl; exact hk hi) s]
    exact hs i hi
  have hsum : ∑ s ∈ agree W m, (xorNet N).prob j s b
      = ((((agree W m).filter fun s => b = xorVal j s)).card : ℝ) := by
    rw [← Finset.sum_boole]
    rfl
  have hbij : (((agree W m).filter fun s => b = xorVal j s)).card
      = (((agree W m).filter fun s => ¬ (b = xorVal j s))).card := by
    refine Finset.card_nbij' (flipAt k) (flipAt k) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [xorVal_flipAt hkj s, ← hs.2]
      exact hbne b
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs ⊢
      refine ⟨hmaps s hs.1, ?_⟩
      rw [xorVal_flipAt hkj s]
      exact hbnot _ _ hs.2
    · intro s _; exact flipAt_flipAt k s
    · intro s _; exact flipAt_flipAt k s
  have htot := Finset.card_filter_add_card_filter_not (s := agree W m)
    (fun s => b = xorVal j s)
  have hcpos : 0 < (agree W m).card := Finset.card_pos.2 (agree_nonempty W m)
  have hc : (agree W m).card
      = 2 * (((agree W m).filter fun s => b = xorVal j s)).card := by omega
  have h1 : (0 : ℝ) < ((((agree W m).filter fun s => b = xorVal j s)).card : ℝ) := by
    have hp : 0 < (((agree W m).filter fun s => b = xorVal j s)).card := by omega
    exact_mod_cast hp
  rw [effUnit, hsum, hc]
  push_cast
  field_simp

/-! ### Cut sets -/

lemma partOf_mem_parts [NeZero N] (θ : SysPartition N Finset.univ) (j : Fin N) :
    θ.partOf j ∈ θ.parts := by
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
  rw [θ.partOf_eq hp hjp]
  exact hp

lemma mem_partOf [NeZero N] (θ : SysPartition N Finset.univ) (j : Fin N) :
    j ∈ θ.partOf j := by
  obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
  rw [θ.partOf_eq hp hjp]
  exact hjp

lemma cutSet_subset_sdiff [NeZero N] (θ : SysPartition N Finset.univ) {p : Finset (Fin N)}
    (hp : p ∈ θ.parts) : θ.cutSet p ⊆ Finset.univ \ p := by
  rw [SysPartition.cutSet]
  cases hd : θ.dir p with
  | inputs => exact subset_rfl
  | outputs =>
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hq1, hq2, -⟩ := Finset.mem_filter.1 hq
      exact Finset.subset_sdiff.2 ⟨q.subset_univ, θ.parts_disjoint q hq1 p hp hq2⟩
  | both => exact subset_rfl

lemma notMem_cutSet_partOf [NeZero N] (θ : SysPartition N Finset.univ) (j : Fin N) :
    j ∉ θ.cutSet (θ.partOf j) := fun h =>
  (Finset.mem_sdiff.1 (cutSet_subset_sdiff θ (partOf_mem_parts θ j) h)).2 (mem_partOf θ j)

lemma card_cutSet_partOf_le [NeZero N] (θ : SysPartition N Finset.univ) (j : Fin N) :
    (θ.cutSet (θ.partOf j)).card ≤ N - 1 := by
  have h1 : (θ.cutSet (θ.partOf j)).card ≤ (Finset.univ \ θ.partOf j).card :=
    Finset.card_le_card (cutSet_subset_sdiff θ (partOf_mem_parts θ j))
  have h2 : (Finset.univ \ θ.partOf j).card = N - (θ.partOf j).card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  have h3 : 0 < (θ.partOf j).card := Finset.card_pos.2 ⟨j, mem_partOf θ j⟩
  omega

/-- The units whose block has a nonempty cut set. -/
noncomputable def severed [NeZero N] (θ : SysPartition N Finset.univ) : Finset (Fin N) :=
  Finset.univ.filter fun j => 0 < (θ.cutSet (θ.partOf j)).card

/-- How many units are severed. -/
noncomputable def severedCount [NeZero N] (θ : SysPartition N Finset.univ) : ℕ :=
  (severed θ).card

lemma severedCount_le [NeZero N] (θ : SysPartition N Finset.univ) : severedCount θ ≤ N := by
  rw [severedCount, severed]
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N))
    fun j => 0 < (θ.cutSet (θ.partOf j)).card

/-- **`[IIT4, Eq 23]`'s normalizer counted over units.**  `∑ᵢ |S⁽ⁱ⁾| |X⁽ⁱ⁾|` is the sum
over units of the size of the cut set of the unit's own block. -/
lemma sysCutCount_eq_sum_units [NeZero N] (θ : SysPartition N Finset.univ) :
    sysCutCount θ = ∑ j : Fin N, (θ.cutSet (θ.partOf j)).card := by
  classical
  have hcover : θ.parts.biUnion id = (Finset.univ : Finset (Fin N)) := by
    refine Finset.eq_univ_of_forall fun j => ?_
    obtain ⟨p, hp, hjp⟩ := θ.parts_cover j (Finset.mem_univ j)
    exact Finset.mem_biUnion.2 ⟨p, hp, hjp⟩
  have hdisj : Set.PairwiseDisjoint (↑θ.parts : Set (Finset (Fin N))) id :=
    fun p hp q hq hpq => θ.parts_disjoint p hp q hq hpq
  have hbi := Finset.sum_biUnion (f := fun j => (θ.cutSet (θ.partOf j)).card) hdisj
  rw [hcover] at hbi
  rw [sysCutCount, hbi]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [show (id p) = p from rfl,
    Finset.sum_congr rfl (fun j hj => by rw [θ.partOf_eq hp hj]), Finset.sum_const,
    smul_eq_mul]

/-- Every cut set misses its own block, so it has at most `N - 1` units and the
normalizer is at most `(N - 1)` times the number of severed units. -/
lemma sysCutCount_le_severed [NeZero N] (θ : SysPartition N Finset.univ) :
    sysCutCount θ ≤ severedCount θ * (N - 1) := by
  classical
  rw [sysCutCount_eq_sum_units, ← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin N)) (fun j => 0 < (θ.cutSet (θ.partOf j)).card)]
  have hzero : ∑ j ∈ Finset.univ.filter
      (fun j => ¬ (0 < (θ.cutSet (θ.partOf j)).card)), (θ.cutSet (θ.partOf j)).card = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have := (Finset.mem_filter.1 hj).2
    omega
  have hle : ∑ j ∈ Finset.univ.filter
      (fun j => 0 < (θ.cutSet (θ.partOf j)).card), (θ.cutSet (θ.partOf j)).card
      ≤ severedCount θ * (N - 1) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (N - 1) fun j _ =>
      card_cutSet_partOf_le θ j) ?_
    rw [smul_eq_mul, severedCount, severed]
  omega

/-! ### A severed unit contributes exactly one half -/

lemma effUnit_xorNet_severed [NeZero N] (θ : SysPartition N Finset.univ) (m : State N)
    (j : Fin N) (b : Bool) (h : 0 < (θ.cutSet (θ.partOf j)).card) :
    effUnit (xorNet N) (θ.cutSet (θ.partOf j))ᶜ m j b = 1 / 2 := by
  obtain ⟨k, hk⟩ := Finset.card_pos.1 h
  refine effUnit_xorNet_of_not_mem _ _ _ k _ (by simpa using hk) ?_
  rintro rfl
  exact notMem_cutSet_partOf θ _ hk

private lemma prod_eq_half_pow [NeZero N] (θ : SysPartition N Finset.univ) (f : Fin N → ℝ)
    (hsev : ∀ j, 0 < (θ.cutSet (θ.partOf j)).card → f j = 1 / 2)
    (huns : ∀ j, ¬ (0 < (θ.cutSet (θ.partOf j)).card) → f j = 1) :
    ∏ j, f j = (1 / 2 : ℝ) ^ severedCount θ := by
  classical
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      f j = if 0 < (θ.cutSet (θ.partOf j)).card then (1 / 2 : ℝ) else 1 := by
    intro j _
    by_cases h : 0 < (θ.cutSet (θ.partOf j)).card
    · rw [if_pos h]; exact hsev j h
    · rw [if_neg h]; exact huns j h
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one, severedCount, severed]

/-! ### The effect side -/

lemma sysEffProb_xorNet [NeZero N] (u s : State N) :
    sysEffProb (xorNet N) Finset.univ u s (xorNext s) = 1 := by
  rw [sysEffProb, merge_univ]
  exact Finset.prod_eq_one fun i _ => by simp [xorNet, xorNext]

lemma sysEffProb_xorNet_eq [NeZero N] (u s t : State N) :
    sysEffProb (xorNet N) Finset.univ u s t = if t = xorNext s then 1 else 0 := by
  by_cases ht : t = xorNext s
  · rw [ht, if_pos rfl, sysEffProb_xorNet]
  · rw [if_neg ht, sysEffProb, merge_univ]
    have hex : ∃ i, t i ≠ xorVal i s := by
      by_contra hall
      push_neg at hall
      exact ht (funext fun i => hall i)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [xorNet, hi])

lemma fullProb_xorNet_eq [NeZero N] (v t : State N) :
    fullProb (xorNet N) v t = if t = xorNext v then 1 else 0 := by
  have h := sysEffProb_xorNet_eq v v t
  rwa [sysEffProb, merge_univ] at h

lemma sum_fullProb_xorNet_pos [NeZero N] (u : State N) :
    0 < ∑ v : State N, fullProb (xorNet N) v u := by
  refine Finset.sum_pos' (fun v _ => fullProb_nonneg _ v u)
    ⟨xorPrev u, Finset.mem_univ _, ?_⟩
  rw [fullProb_xorNet_eq, xorNext_xorPrev, if_pos rfl]
  norm_num

lemma sysUncEff_xorNet [NeZero N] (u t : State N) :
    sysUncEff (xorNet N) Finset.univ u t = 1 / 2 ^ N := by
  rw [sysUncEff, avgOverStates]
  have hswap : ∀ s : State N,
      sysEffProb (xorNet N) Finset.univ u s t = if s = xorPrev t then (1 : ℝ) else 0 := by
    intro s
    rw [sysEffProb_xorNet_eq]
    by_cases hs : s = xorPrev t
    · subst hs
      simp [xorNext_xorPrev]
    · rw [if_neg fun ht => hs (by rw [ht, xorPrev_xorNext]), if_neg hs]
  rw [Finset.sum_congr rfl fun s _ => hswap s,
    Fintype.sum_ite_eq' (xorPrev t) fun _ => (1 : ℝ)]

lemma sysCauseProb_xorNet [NeZero N] (u s t : State N) :
    sysCauseProb (xorNet N) Finset.univ u s t = if t = xorPrev s then 1 else 0 := by
  rw [sysCauseProb_univ _ _ _ _ (sum_fullProb_xorNet_pos u), fullProb_xorNet_eq]
  congr 1
  apply propext
  constructor
  · rintro rfl; rw [xorPrev_xorNext]
  · rintro rfl; rw [xorNext_xorPrev]

lemma sysUncCause_xorNet [NeZero N] (u s : State N) :
    sysUncCause (xorNet N) Finset.univ u s = 1 / 2 ^ N := by
  rw [sysUncCause, avgOverStates,
    Finset.sum_congr rfl fun t _ => sysCauseProb_xorNet u s t,
    Fintype.sum_ite_eq' (xorPrev s) fun _ => (1 : ℝ)]

lemma sysIiE_xorNet [NeZero N] (u s t : State N) :
    sysIiE (xorNet N) Finset.univ u s t = if t = xorNext s then (N : ℝ) else 0 := by
  rw [sysIiE, sysEffProb_xorNet_eq, sysUncEff_xorNet]
  by_cases ht : t = xorNext s
  · rw [if_pos ht, if_pos ht, one_mul, one_div_one_div, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one]
  · rw [if_neg ht, if_neg ht, zero_mul]

lemma sysIiC_xorNet [NeZero N] (u s t : State N) :
    sysIiC (xorNet N) Finset.univ u s t = if t = xorPrev s then (N : ℝ) else 0 := by
  rw [sysIiC, sysBackCause, sysCauseProb_xorNet, sysUncCause_xorNet]
  by_cases ht : t = xorPrev s
  · rw [if_pos ht, if_pos ht, one_div_one_div, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), mul_one, Finset.card_univ, Fintype.card_fin]
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  · rw [if_neg ht, if_neg ht, zero_div, zero_mul]

/-! ### The partitioned probabilities -/

lemma sysPartEffProb_xorNet [NeZero N] (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPartEffProb (xorNet N) Finset.univ u θ s (xorNext s)
      = (1 / 2 : ℝ) ^ severedCount θ := by
  rw [sysPartEffProb]
  refine prod_eq_half_pow θ _ (fun j hj => ?_) (fun j hj => ?_)
  · rw [merge_univ]
    exact effUnit_xorNet_severed θ s j _ hj
  · rw [merge_univ]
    have hemp : θ.cutSet (θ.partOf j) = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [hemp, Finset.compl_empty, effUnit_xorNet_univ]
    exact if_pos rfl

lemma sysPartCauseProb_xorNet_univ [NeZero N] (u s t : State N)
    (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (xorNet N) Finset.univ u θ s t
      = ∏ j, effUnit (xorNet N) (θ.cutSet (θ.partOf j))ᶜ t j (s j) := by
  rw [sysPartCauseProb]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w _ => by
    rw [bgWeight_univ _ _ _ (sum_fullProb_xorNet_pos u), mul_one, merge_univ]]
  rw [Finset.sum_const, card_state, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  push_cast
  field_simp

lemma sysPartCauseProb_xorNet [NeZero N] (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPartCauseProb (xorNet N) Finset.univ u θ s (xorPrev s)
      = (1 / 2 : ℝ) ^ severedCount θ := by
  rw [sysPartCauseProb_xorNet_univ]
  refine prod_eq_half_pow θ _ (fun j hj => ?_) (fun j hj => ?_)
  · exact effUnit_xorNet_severed θ (xorPrev s) j _ hj
  · have hemp : θ.cutSet (θ.partOf j) = ∅ := Finset.card_eq_zero.1 (by omega)
    have hval : xorVal j (xorPrev s) = s j := congrFun (xorNext_xorPrev s) j
    rw [hemp, Finset.compl_empty, effUnit_xorNet_univ, hval, if_pos rfl]

/-! ### Both directions equal the severed count -/

private lemma pos_logb_half_pow (m : ℕ) :
    pos (Real.logb 2 (1 / (1 / 2 : ℝ) ^ m)) = m := by
  rw [div_pow, one_pow, one_div_one_div, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one, pos, max_eq_right (Nat.cast_nonneg m)]

lemma sysPhiE_xorNet [NeZero N] (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiE (xorNet N) Finset.univ u θ s (xorNext s) = severedCount θ := by
  rw [sysPhiE, sysEffProb_xorNet, one_mul, sysPartEffProb_xorNet, pos_logb_half_pow]

lemma sysPhiC_xorNet [NeZero N] (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiC (xorNet N) Finset.univ u θ s (xorPrev s) = severedCount θ := by
  rw [sysPhiC, sysBackCause, sysCauseProb_xorNet, if_pos rfl, sysUncCause_xorNet,
    Finset.card_univ, Fintype.card_fin]
  have hback : (1 : ℝ) / ((2 : ℝ) ^ N * (1 / 2 ^ N)) = 1 := by
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  rw [hback, one_mul, sysPartCauseProb_xorNet, pos_logb_half_pow]

/-- **Both directions of `φ_s` equal the severed count, at every partition.** -/
lemma sysPhiAt_xorNet [NeZero N] (u s : State N) (θ : SysPartition N Finset.univ) :
    sysPhiAt (xorNet N) Finset.univ u θ s (xorPrev s) (xorNext s) = severedCount θ := by
  rw [sysPhiAt, sysPhiC_xorNet, sysPhiE_xorNet, min_self]

/-! ### The maximal cause and effect states -/

lemma sysMaxEffStates_xorNet [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    sysMaxEffStates (xorNet N) Finset.univ u s = {xorNext s} := by
  have hNpos : (0 : ℝ) < N := by
    have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun t ht => ?_⟩
  · rw [sysMaxEffStates, argmaxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun t => ?_⟩
    rw [sysIiE_xorNet, sysIiE_xorNet, if_pos rfl]
    split
    · exact le_refl _
    · exact Nat.cast_nonneg N
  · rw [sysMaxEffStates, mem_argmaxSet] at ht
    have h := ht (xorNext s)
    rw [sysIiE_xorNet, sysIiE_xorNet, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    linarith

lemma sysMaxCauseStates_xorNet [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    sysMaxCauseStates (xorNet N) Finset.univ u s = {xorPrev s} := by
  have hNpos : (0 : ℝ) < N := by
    have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun t ht => ?_⟩
  · rw [sysMaxCauseStates, argmaxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun t => ?_⟩
    rw [sysIiC_xorNet, sysIiC_xorNet, if_pos rfl]
    split
    · exact le_refl _
    · exact Nat.cast_nonneg N
  · rw [sysMaxCauseStates, mem_argmaxSet] at ht
    have h := ht (xorPrev s)
    rw [sysIiC_xorNet, sysIiC_xorNet, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    linarith

/-! ### The minimising partition -/

/-- The all-singletons partition, every block severed in both directions. -/
noncomputable def singletonParts [NeZero N] (hN : 2 ≤ N) : SysPartition N Finset.univ where
  parts := Finset.univ.image fun j : Fin N => ({j} : Finset (Fin N))
  dir _ := Dir.both
  parts_nonempty := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨j, Finset.mem_singleton_self j⟩
  parts_subset := fun p _ => p.subset_univ
  parts_disjoint := by
    intro p hp q hq hpq
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hq
    exact Finset.disjoint_singleton.2 fun h => hpq (by rw [h])
  parts_cover := fun i _ =>
    ⟨{i}, Finset.mem_image_of_mem _ (Finset.mem_univ i), Finset.mem_singleton_self i⟩
  two_le := by
    rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ,
      Fintype.card_fin]
    exact hN

lemma singletonParts_partOf [NeZero N] (hN : 2 ≤ N) (j : Fin N) :
    (singletonParts hN).partOf j = {j} :=
  (singletonParts hN).partOf_eq (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    (Finset.mem_singleton_self j)

lemma singletonParts_card_cutSet [NeZero N] (hN : 2 ≤ N) (j : Fin N) :
    ((singletonParts hN).cutSet ((singletonParts hN).partOf j)).card = N - 1 := by
  have hcut : (singletonParts hN).cutSet {j} = Finset.univ \ ({j} : Finset (Fin N)) := rfl
  rw [singletonParts_partOf, hcut, ← Finset.compl_eq_univ_sdiff, Finset.card_compl,
    Finset.card_singleton, Fintype.card_fin]

lemma severedCount_singletonParts [NeZero N] (hN : 2 ≤ N) :
    severedCount (singletonParts hN) = N := by
  have hall : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      0 < ((singletonParts hN).cutSet ((singletonParts hN).partOf j)).card := by
    intro j _
    rw [singletonParts_card_cutSet]
    omega
  rw [severedCount, severed, Finset.filter_true_of_mem hall, Finset.card_univ,
    Fintype.card_fin]

lemma sysCutCount_singletonParts [NeZero N] (hN : 2 ≤ N) :
    sysCutCount (singletonParts hN) = N * (N - 1) := by
  rw [sysCutCount_eq_sum_units,
    Finset.sum_congr rfl (fun j _ => singletonParts_card_cutSet hN j),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The quantity minimized by `[IIT4, Eq 23]` is at least `1 / (N - 1)` at every
partition. -/
lemma normalizedSysPhiAt_xorNet_ge [NeZero N] (hN : 2 ≤ N) (u s : State N)
    (θ : SysPartition N Finset.univ) :
    1 / ((N : ℝ) - 1)
      ≤ normalizedSysPhiAt (xorNet N) Finset.univ u θ s (xorPrev s) (xorNext s) := by
  rw [normalizedSysPhiAt, sysPhiAt_xorNet]
  have hcR : (0 : ℝ) < (sysCutCount θ : ℝ) := by exact_mod_cast sysCutCount_pos θ
  have hNR : (0 : ℝ) < (N : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [div_le_div_iff₀ hNR hcR]
  have hle := (Nat.cast_le (α := ℝ)).2 (sysCutCount_le_severed θ)
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hle
  linarith

lemma normalizedSysPhiAt_singletonParts [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    normalizedSysPhiAt (xorNet N) Finset.univ u (singletonParts hN) s (xorPrev s)
        (xorNext s) = 1 / ((N : ℝ) - 1) := by
  have hNR : (0 : ℝ) < (N : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN0 : ((N : ℝ)) ≠ 0 := by
    have h : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    intro h0
    rw [h0] at h
    linarith
  rw [normalizedSysPhiAt, sysPhiAt_xorNet, severedCount_singletonParts,
    sysCutCount_singletonParts, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  field_simp

/-- The all-singletons partition attains that bound, so it is a minimum information
partition `[IIT4, Eq 22]`. -/
lemma singletonParts_mem_sysMipSetAt [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    singletonParts hN ∈ sysMipSetAt (xorNet N) Finset.univ u s (xorPrev s) (xorNext s) := by
  rw [sysMipSetAt, mem_argminSet]
  intro θ
  rw [normalizedSysPhiAt_singletonParts]
  exact normalizedSysPhiAt_xorNet_ge hN u s θ

lemma sysPhiOfState_xorNet [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    sysPhiOfState (xorNet N) Finset.univ u s (xorPrev s) (xorNext s) = N := by
  refine le_antisymm ?_ ?_
  · rw [sysPhiOfState]
    refine sup'OrZero_le (Nat.cast_nonneg N) fun θ _ => ?_
    rw [sysPhiAt_xorNet]
    exact_mod_cast severedCount_le θ
  · rw [sysPhiOfState]
    have h := le_sup'OrZero
      (f := fun θ => sysPhiAt (xorNet N) Finset.univ u θ s (xorPrev s) (xorNext s))
      (singletonParts_mem_sysMipSetAt hN u s)
    rwa [sysPhiAt_xorNet, severedCount_singletonParts] at h

/-- **`φ_s = N` for the XOR network on `N` units**, for every `N ≥ 2` and in every state.
This is the largest value an `N`-unit substrate admits under `[IIT4, Eqs 22, 23]` here,
and as with `one_le_sysPhi_copyRing` it is proved uniformly in `N`. -/
theorem sysPhi_xorNet_eq [NeZero N] (hN : 2 ≤ N) (u s : State N) :
    sysPhi (xorNet N) Finset.univ u s = N := by
  have hprod : (sysMaxCauseStates (xorNet N) Finset.univ u s) ×ˢ
      (sysMaxEffStates (xorNet N) Finset.univ u s)
      = {((xorPrev s, xorNext s) : State N × State N)} := by
    rw [sysMaxCauseStates_xorNet hN, sysMaxEffStates_xorNet hN]
    ext p
    simp [Prod.ext_iff]
  rw [sysPhi, hprod]
  refine le_antisymm ?_ ?_
  · refine sup'OrZero_le (Nat.cast_nonneg N) fun p hp => ?_
    rw [Finset.mem_singleton] at hp
    subst hp
    exact le_of_eq (sysPhiOfState_xorNet hN u s)
  · have h := le_sup'OrZero
      (s := ({((xorPrev s, xorNext s) : State N × State N)} : Finset (State N × State N)))
      (f := fun p : State N × State N => sysPhiOfState (xorNet N) Finset.univ u s p.1 p.2)
      (Finset.mem_singleton_self _)
    rwa [sysPhiOfState_xorNet hN] at h

end IIT
