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

## Licence

MIT.
