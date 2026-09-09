/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.MinDep
import CircNet.Circulant

/-!
# A unit with no live inputs in `S` forces `φ_s(S) = 0` on the circulant

If `j ∈ S` has `{j+1, j+2} ∩ S = ∅`, the window of `j` is pinned on the split fibre
and min-dependency applies.  Consecutive deletions are the intended source of such a `j`.
-/

namespace IIT

open scoped Classical

variable {N : ℕ}

section Gap

variable [NeZero N]

lemma circVal_of_agree_no_live {S : Finset (Fin N)} {j : Fin N} {s u v : State N}
    (hlive : liveInputs j ∩ S = ∅)
    (hv : v ∈ agree (S.erase j)ᶜ (merge S s u)) :
    circVal j v = circVal j (merge S s u) := by
  have hW : ∀ i, i = j ∨ i ∉ S → v i = merge S s u i := by
    intro i hi
    have : i ∉ S.erase j := by
      intro hmem
      rcases hi with hij | nS
      · subst hij
        exact (Finset.mem_erase.1 hmem).1 rfl
      · exact nS (Finset.mem_of_mem_erase hmem)
    exact mem_agree.1 hv i (Finset.mem_compl.2 this)
  have hvj : v j = merge S s u j := hW j (Or.inl rfl)
  have h1 : shift j ∉ S := by
    intro h
    have : shift j ∈ liveInputs j ∩ S :=
      Finset.mem_inter.2 ⟨mem_liveInputs.2 (Or.inl rfl), h⟩
    exact Finset.notMem_empty _ (hlive ▸ this)
  have h2 : shift (shift j) ∉ S := by
    intro h
    have : shift (shift j) ∈ liveInputs j ∩ S :=
      Finset.mem_inter.2 ⟨mem_liveInputs.2 (Or.inr rfl), h⟩
    exact Finset.notMem_empty _ (hlive ▸ this)
  have hv1 : v (shift j) = merge S s u (shift j) := hW _ (Or.inr h1)
  have hv2 : v (shift (shift j)) = merge S s u (shift (shift j)) := hW _ (Or.inr h2)
  simp [circVal, hvj, hv1, hv2]

/-- If `j ∈ S` reads nothing else in `S` and `|S| ≥ 2`, then `φ_s(S) = 0`. -/
theorem sysPhi_circNet_eq_zero_of_no_live {S : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ S) (hrest : (S.erase j).Nonempty) (hlive : liveInputs j ∩ S = ∅)
    (u s : State N) : sysPhi (circNet N) S u s = 0 := by
  refine sysPhi_eq_zero_of_splitFibre hj hrest u s ?_
  intro t v hv
  have hval := circVal_of_agree_no_live hlive hv
  simp [circNet, hval]

end Gap

end IIT
