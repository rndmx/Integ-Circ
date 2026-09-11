# CircNet

A machine-checked proof, in Lean 4, that an explicit family of substrates satisfies
**every postulate of IIT 4.0 — exclusion included — while its integrated information
grows as `2` to a power quadratic in the number of units**.

The substrate is as plain as a system can be. Arrange `N` binary units in a circle; at
each tick every unit looks at itself and its two clockwise neighbours and turns on
exactly when an odd number of the three are on. Write `R_N` for this ring.

## The theorems

For every `N ≥ 8` with `3 ∤ N`:

| | Lean name | file |
|---|---|---|
| `R_N` is a **complex** — it strictly exceeds every nonempty proper subsystem in system integrated information, **in every state and against every background** | `IIT.isComplex_circNet_univ` | `CircNet/CirculantD3Final.lean` |
| its **integrated information** at the all-ones state is at least `2 ^ (N ^ 2 / 8) * (1/2) ^ N / (2 * N) - 1` | `IIT.two_pow_sq_le_PhiMax_circNet` | `CircNet/CircFamily.lean` |
| the **distinctions** of `R_N` at the all-ones state are exactly its arcs of length at least three, including the whole cycle | `IIT.isDistinctionMech_circNet_iff` | `CircNet/CircOnlyArcs.lean` |
| there are exactly `N * (N - 3) + 1` of them | `IIT.card_distinctionMechs_circNet` | `CircNet/CircOnlyArcs.lean` |

All four are checked by the Lean kernel and depend on no axioms beyond the three of the
ambient logic (`propext`, `Classical.choice`, `Quot.sound`). The development contains no
use of `native_decide`, and no appeal to numerical evaluation that the kernel does not
itself perform. All four are checked in a single import closure, so they are established
of the same object.

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
`IIT.isComplex_circNet_univ`. To re-check the axiom dependencies:

```lean
import CircNet
#print axioms IIT.isComplex_circNet_univ
#print axioms IIT.two_pow_sq_le_PhiMax_circNet
#print axioms IIT.isDistinctionMech_circNet_iff
#print axioms IIT.card_distinctionMechs_circNet
```

On a machine with limited memory, build with `LEAN_NUM_THREADS=1`; several parallel
`lean` processes each map the whole of Mathlib and can exhaust the commit charge,
which surfaces as spurious `failed to read file '....olean'` errors.

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
