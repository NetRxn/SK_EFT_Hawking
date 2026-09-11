# Bounded classical uniqueness backport

This directory records the upstream attribution and exact source closure for the
67 vendored modules under `lean/NavierStokes`. Source and original pins are in
`source-manifest.json`; Apache-2.0 license is preserved verbatim in `LICENSE`.
Port modifications are listed in the manifest and marked in the affected source files.

The separate `NavierStokes` Lean library preserves upstream `autoImplicit=true`.
Its root imports only `NavierStokes.R3.WholeSpaceUniqueness`. Euler, Comparator
and challenge modules are outside the selected closure. The project stays on its
existing coupled Lean/Mathlib/PhysLib/REPL 4.32 pins.

Status: initial compiler experiment; no compatibility or adapter acceptance yet.
Acceptance requires a successful project build, full selected-theorem axiom audit,
review of any port changes, and a concrete consumer with explicit hypotheses.
The theorem concerns smooth classical flows with a compact reference and a
finite-energy competitor; it does not establish global or weak-solution uniqueness.
