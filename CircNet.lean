/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under the MIT licence.
Authors: Arnaud Mayeux
-/
import CircNet.CirculantD3Final
import CircNet.CircFamily

/-!
# CircNet: the interval window-3 ring

The two theorems of the accompanying paper, on top of the core formalization of
IIT 4.0 (the `IIT` package, https://github.com/rndmx/Integ, release `v1`):

* `IIT.isComplex_circNet_univ` -- the ring is a complex: it strictly exceeds every
  nonempty proper subsystem in system integrated information, in every state and
  against every background (`CircNet/CirculantD3Final.lean`);
* `IIT.two_pow_sq_le_PhiMax_circNet` -- its integrated information at the all-ones
  state is at least `2 ^ (N ^ 2 / 8) * (1/2) ^ N / (2 * N) - 1`
  (`CircNet/CircFamily.lean`).

Nothing in the `IIT` package is duplicated here: this library imports it as a
versioned dependency and adds only substrate-specific material.
-/
