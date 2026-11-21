# Periodic Navier–Stokes Lean library

The three modules under `lean/NavierStokes/` come from
[OpenAI's NavierStokesAndEuler repository at f9e8bc5](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd).
The [manifest](source-manifest.json) records their original hashes, and
the [Apache 2.0 license](LICENSE) is preserved verbatim. The port changes
one boundary simplification to its Lean 4.32 equivalent in
`PeriodicIntegration.lean`.

Build the separate library with `lake build NavierStokes` from `lean/`.
It retains upstream `autoImplicit = true` and uses the project's existing
toolchain and Mathlib pins. The root exports periodic integration and
classical velocity uniqueness at unit viscosity on a bounded time interval
under the explicit initial
data, smoothness, divergence, periodicity, and common forcing hypotheses.
`ProblemStatement.candidateStatement` remains an open existence proposition.
