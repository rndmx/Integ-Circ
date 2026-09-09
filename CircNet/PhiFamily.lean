/-
A general lower bound on `Φ` from a family of distinctions with a shared support point.

In a lower bound on `Φ_max` obtained from a family of distinctions, the substrate plays
no role in the final combinatorial step.  What does the work is

* a family `F` of distinctions of the structure,
* a single stated unit lying in **every** member's support, so that every subfamily has a
  nonempty congruent overlap `[IIT4, Eq 55]` and therefore relates, and
* a uniform positive lower bound `c` on each member's `φ_d` per support unit.

Given those, each of the `2^|F| - 1 - |F|` subfamilies of size `≥ 2` contributes at least
`c` to the relation sum of `[IIT4, Eq 59]`.

This file isolates that argument, so any construction supplying such a family inherits the
bound.  The point of the abstraction is that `|F|` may grow exponentially in the substrate
size, in which case `2^|F|` is doubly exponential.
-/
import IIT.System

namespace IIT

variable {N : ℕ}

section Family

variable {T : UnitTPM N} {S : Finset (Fin N)} {u s : State N} {σ : Selector T S u s}
variable {F : Finset (Distinction N)} {p : Fin N × Bool} {c : ℝ}

/-- **Every subfamily relates**: the shared stated unit keeps the congruent overlap
nonempty, and `c` bounds the per-unit integration from below. -/
lemma le_relPhi_of_shared (hc : 0 < c) (hp : ∀ D ∈ F, p ∈ D.support)
    (hcF : ∀ D ∈ F, c ≤ D.phiPerUnit)
    {d : Finset (Distinction N)} (hd : d.Nonempty) (hsub : d ⊆ F) :
    c ≤ relPhi d hd := by
  have hpt : p ∈ d.inf Distinction.support := by
    rw [mem_finset_inf]
    exact fun D hD => hp D (hsub hD)
  have hcard : (1 : ℝ) ≤ ((d.inf Distinction.support).card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.2 ⟨_, hpt⟩)
  have hmin : c ≤ d.inf' hd Distinction.phiPerUnit := by
    rw [Finset.le_inf'_iff]
    exact fun D hD => hcF D (hsub hD)
  calc c = 1 * c := (one_mul _).symm
    _ ≤ ((d.inf Distinction.support).card : ℝ) * d.inf' hd Distinction.phiPerUnit :=
        mul_le_mul hcard hmin hc.le (le_trans zero_le_one hcard)
    _ = relPhi d hd := rfl

/-- Every subfamily of size `≥ 2` is a genuine relation `[IIT4, Eq 56]`. -/
lemma mem_relationSets_of_shared (hc : 0 < c) (hp : ∀ D ∈ F, p ∈ D.support)
    (hcF : ∀ D ∈ F, c ≤ D.phiPerUnit) (hFD : F ⊆ distinctions T S u s σ)
    {d : Finset (Distinction N)} (hd : d ∈ F.powerset.filter fun t => 2 ≤ t.card) :
    d ∈ relationSets T S u s σ := by
  obtain ⟨hsub', h2⟩ := Finset.mem_filter.1 hd
  have hsub : d ⊆ F := Finset.mem_powerset.1 hsub'
  have hne : d.Nonempty := Finset.card_pos.mp (by omega)
  exact Finset.mem_filter.2
    ⟨Finset.mem_powerset.2 (hsub.trans hFD), hne, h2,
      lt_of_lt_of_le hc (le_relPhi_of_shared hc hp hcF hne hsub)⟩

/-- The subsets of `F` of size at least two number `2^|F| - 1 - |F|`: all subsets, less
the empty set and the singletons. -/
lemma card_filter_two_le (F : Finset (Distinction N)) :
    (F.powerset.filter fun t => 2 ≤ t.card).card = 2 ^ F.card - 1 - F.card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F.powerset) (p := fun t : Finset (Distinction N) => 2 ≤ t.card)
  have hfil : (F.powerset.filter fun t => ¬ (2 ≤ t.card))
      = insert (∅ : Finset (Distinction N))
          (F.image fun a => ({a} : Finset (Distinction N))) := by
    ext t
    constructor
    · intro ht
      rw [Finset.mem_filter, Finset.mem_powerset] at ht
      obtain ⟨hsub, hlt⟩ := ht
      have hc : t.card = 0 ∨ t.card = 1 := by omega
      rcases hc with h | h
      · rw [Finset.card_eq_zero] at h
        subst h
        exact Finset.mem_insert_self _ _
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.2 ⟨a, hsub (Finset.mem_singleton_self a), rfl⟩)
    · intro ht
      rw [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.empty_subset _, by simp⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.singleton_subset_iff.2 ha, by simp⟩
  have hnotmem : (∅ : Finset (Distinction N))
      ∉ F.image fun a => ({a} : Finset (Distinction N)) := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 h
    exact Finset.singleton_ne_empty a ha
  have hinj : Function.Injective
      fun a : Distinction N => ({a} : Finset (Distinction N)) := by
    intro a b hab
    simpa using hab
  have hcard1 : (F.powerset.filter fun t => ¬ (2 ≤ t.card)).card = 1 + F.card := by
    rw [hfil, Finset.card_insert_of_notMem hnotmem,
      Finset.card_image_of_injective _ hinj]
    omega
  rw [Finset.card_powerset] at hsplit
  omega

/-- **The relation sum**: `(2^|F| - 1 - |F|) · c` is a lower bound on the `[IIT4, Eq 56]`
sum of `[IIT4, Eq 59]`. -/
lemma sum_relPhi_ge (hc : 0 < c) (hp : ∀ D ∈ F, p ∈ D.support)
    (hcF : ∀ D ∈ F, c ≤ D.phiPerUnit) (hFD : F ⊆ distinctions T S u s σ) :
    ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c
      ≤ ∑ d ∈ relationSets T S u s σ, relPhiOrZero d := by
  classical
  set R₀ := F.powerset.filter fun t => 2 ≤ t.card with hR₀
  have hsub : R₀ ⊆ relationSets T S u s σ :=
    fun d hd => mem_relationSets_of_shared hc hp hcF hFD hd
  have hterm : ∀ d ∈ R₀, c ≤ relPhiOrZero d := by
    intro d hd
    obtain ⟨hsub', h2⟩ := Finset.mem_filter.1 hd
    have hdsub : d ⊆ F := Finset.mem_powerset.1 hsub'
    have hne : d.Nonempty := Finset.card_pos.mp (by omega)
    rw [relPhiOrZero, dif_pos hne]
    exact le_relPhi_of_shared hc hp hcF hne hdsub
  have hnonneg : ∀ d ∈ relationSets T S u s σ, 0 ≤ relPhiOrZero d :=
    fun d _ => relPhiOrZero_nonneg d
  calc ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c
      = (R₀.card : ℝ) * c := by rw [card_filter_two_le F]
    _ = ∑ _d ∈ R₀, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ R₀, relPhiOrZero d := Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ relationSets T S u s σ, relPhiOrZero d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ => hnonneg d hd

/-- **The general bound.**  A family `F` of distinctions sharing a stated support unit,
each integrating at least `c > 0` per support unit, forces

  `Φ_max ≥ (2^|F| - 1 - |F|) · c`.

Only `|F|` and `c` enter; the substrate is arbitrary.  When `|F|` grows exponentially in
the substrate size this is doubly exponential. -/
theorem doubly_exp_le_PhiMax_of_family (hc : 0 < c) (hp : ∀ D ∈ F, p ∈ D.support)
    (hcF : ∀ D ∈ F, c ≤ D.phiPerUnit) (hFD : F ⊆ distinctions T S u s σ) :
    ((2 ^ F.card - 1 - F.card : ℕ) : ℝ) * c ≤ PhiMax T S u s := by
  have h1 := sum_relPhi_ge hc hp hcF hFD
  have hPhi : ∑ d ∈ relationSets T S u s σ, relPhiOrZero d ≤ PhiOf T S u s σ := by
    rw [PhiOf]
    have hd : 0 ≤ ∑ d ∈ distinctions T S u s σ, d.phi :=
      Finset.sum_nonneg fun d _ => d.phi_pos.le
    have hs : 0 ≤ ∑ d ∈ selfRelationDistinctions T S u s σ, selfRelPhi d :=
      Finset.sum_nonneg fun d hd => (Finset.mem_filter.1 hd).2.le
    linarith
  exact h1.trans (hPhi.trans (PhiOf_le_PhiMax T S u s σ))

end Family

end IIT
