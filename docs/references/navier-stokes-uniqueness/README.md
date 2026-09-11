# Bounded classical uniqueness backport

This directory records the upstream attribution and exact source closure for the
67 vendored modules under `lean/NavierStokes`. Source and original pins are in
`source-manifest.json`; Apache-2.0 license is preserved verbatim in `LICENSE`.
Port modifications are listed in the manifest and marked in the affected source files.

The separate `NavierStokes` Lean library preserves upstream `autoImplicit=true`.
Its root imports only `NavierStokes.R3.WholeSpaceUniqueness`. Euler, Comparator
and challenge modules are outside the selected closure. The project stays on its
existing coupled Lean/Mathlib/PhysLib/REPL 4.32 pins.

The bounded closure compiles on the existing pins at `4390030d`: the project
build passed 10,911 jobs. Four files required the disclosed proof-normalization
adaptations; independent review confirmed unchanged theorem statements.
Original source hashes, import-closure completeness and the license were verified.
The elaborated axiom closure of `classical_uniqueness_on_Icc` contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. This measured compatibility
supports the bounded backport without a coordinated toolchain upgrade.

Model-specific consumers must explicitly transport coordinates, derivatives,
support, measure and energy, and discharge the theorem's hypotheses.
The theorem concerns smooth classical flows with a compact reference and a
finite-energy competitor; it does not establish global or weak-solution uniqueness.
