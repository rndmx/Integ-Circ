# CircNet

A machine-checked proof, in Lean 4, that an explicit family of substrates satisfies
**every postulate of IIT 4.0 — exclusion included — while its integrated information
grows as `2` to a power quadratic in the number of units**.

The substrate is as plain as a system can be. Arrange `N` binary units in a circle; at
each tick every unit looks at itself and its two clockwise neighbours and turns on
exactly when an odd number of the three are on. Write `R_N` for this ring.

The main theorem, the lower bound on `Φ`, is `IIT.two_pow_sq_le_PhiMax_circNet` in
`CircNet/CircFamily.lean`.

## Relation to the core formalization

This repository contains **no** formalization of IIT 4.0 itself. The definitions —
repertoires, causal marginalization, `φ_d`, distinctions, relations, `Φ`, system
partitions, `φ_s`, and the exclusion postulate — live in a separate library, which this
one imports as a versioned dependency:

* repository: <https://github.com/rndmx/Integ>, release `v1`
* companion paper: *A Machine-Checked Formalization of Integrated Information Theory in
  Lean 4*, [doi:10.5281/zenodo.22659407](https://doi.org/10.5281/zenodo.22659407)

Nothing from that package is duplicated here. A reader wishing to audit the
correspondence between IIT 4.0 as published and as formalized should read it there; what
is added here is substrate-specific.

## Building

```sh
lake update      # fetches Integ v1 and Mathlib
lake build
```

Lean modules are `CircNet.*`; the Lean *namespace* is `IIT`, so theorem names read
`IIT.isComplex_circNet_univ`. Every theorem here is checked by the Lean kernel and
depends on no axioms beyond the three of the ambient logic (`propext`,
`Classical.choice`, `Quot.sound`), with no use of `native_decide` and no appeal to
numerical evaluation the kernel does not itself perform. To re-check the axiom
dependencies:

```lean
import CircNet
#print axioms IIT.isComplex_circNet_univ
#print axioms IIT.two_pow_sq_le_PhiMax_circNet
#print axioms IIT.isDistinctionMech_circNet_iff
#print axioms IIT.card_distinctionMechs_circNet
```


## Layout

* `CircNet/Common.lean` — the handful of substrate-independent definitions and lemmas
  used below (the all-ones state, the partition severing one unit from its purview, two
  facts about stated purviews and maximal cause purviews).
* `CircNet/Explore.lean`, `CircNet/MinDep.lean`, `CircNet/PhiFamily.lean` — general
  support: XOR substrates, minimal dependence, and the family bound that converts many
  distinctions sharing a unit into a lower bound on `Φ`.
* `CircNet/Circulant*.lean` — the system level: the damage model, the classification of
  partitions by damage, the competitor bound, and exclusion.
* `CircNet/CircSys.lean`, `CircNet/CircMech{Effect,Cause}.lean`,
  `CircNet/CircFamily.lean` — the mechanism level: that the contiguous arcs of length at
  least three are distinctions, and the resulting lower bound on `Φ`.
* `CircNet/CircOnlyArcs.lean` — the converse: no other mechanism is a distinction, so the
  distinctions at the all-ones state are exactly those arcs, `N * (N - 3) + 1` of them.

## Licence

MIT.
