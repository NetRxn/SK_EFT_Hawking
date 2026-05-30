# Stage 13 Adversarial Review — Phase 6x KMM Theorem-1 converse + grid-synthesis back-end

**Date:** 2026-05-29 (fresh-context reviewer, separate from the implementing context).
**Scope:** `lean/SKEFTHawking/FKLW/RossSelinger/KMMCompleteness.lean` + `GridSolver.lean`
(the synthesis half of the Ross-Selinger Clifford+T compiler shipped this session).

## VERDICT: GREEN (0 BLOCKER / 0 REQUIRED / 0 ADVISORY; 2 benign NITs)

Both files build clean (1571 jobs), carry only the accepted axiom set, and the two headline
results are mathematically sound and non-vacuous. Independently verified by the reviewer.

## Findings (independently verified, not docstring-trusted)

**Q1 — keystone `blochEntry_real` CORRECT + unconditional + non-vacuous.**
`∀ M i j, conj(blochEntry M i j) = blochEntry M i j` holds for ANY M (no unitarity). Reviewer
checked it on a deliberately non-unitary matrix AND a fully-generic symbolic `!![a,b;c,d]`
(incl. the (0,0)/(1,1) entries with `iS²`); the `fin_cases <;> ring` discharges a TRUE reality
identity, not a false goal. `conj` is a genuine non-trivial ring-involution (`conj ωS = ωS⁷ ≠ ωS`,
`conj iS = -iS`, `iS²=-1`, all kernel `decide`). The Bloch map is the correct SO(3) image
(`R(T)_zz=1`, `R(H)_xz=1`, `R(X)_yy=-1`, `R(T)₀₀≠R(T)_zz`). Axioms: 3 std only (no native_decide).

**Q2 — `kmm_completeness` SOUND + non-vacuous.** Strong induction on `muMeasure` is well-founded
(`mu_decrease`'s conclusion is *definitionally* `muMeasure(reduceStep M k) < muMeasure M`); the
reconstruction `interp(reconWordC k)·reduceStep M k = M` is correct; the `∃k, det M = ωS^k`
hypothesis is genuinely USED (via `unitary_col1`, propagated by `det_reduceStep`/`det_stripMat'`)
and jointly satisfiable (reviewer built a concrete realizable instance).

**Q3 — grid chain GENUINE, not circular.** `nonempty_kmmReduction` is unconditional;
`gridFindT_realizable` genuinely establishes realizability via the converse; `diophantineSearch_sound`
is real soundness; and the finder genuinely returns `some` (`#eval gridFindT ⟨0,0,0,1⟩ 1 2 = some ⟨-1,0,0,0⟩`,
a real solution) — so `gridSynthWord_correct`/`gridCompile_correct` are non-vacuously satisfiable.

**Q4 — invariants PASS.** Inv #15: no new `axiom` (only `{propext, Classical.choice, Quot.sound}`
+ the 4 pre-accepted native_decide box-cores). Inv #10: no `maxHeartbeats` in proof bodies.
No `sorry`/`admit`. Both files use kernel `decide`, not native_decide.

**Q5 — strengthening discipline PASS.** `isCliffordTRealizable_assembleUnitary`, `det_adjoint`,
`conj_omegaS_pow`, `diophantineSearch_sound` are all load-bearing — no P3/P5 tautologies.

## NITs (non-blocking)
- `GridSolver.lean:95` `attribute [local instance] nonempty_kmmReduction` surfaces a benign
  `local instance` source-scan flag in `lean_verify` (instance is unconditionally proven).
- Pre-existing linter warnings (`ring does nothing`, deprecations) in dependency files
  (`ZOmega.lean`, `ZOmegaSqrt2.lean`, `SdeMatrix.lean`) — out of scope; future cleanup pass.

## Scope note
This Stage 13 covers the **synthesis half** (KMM converse + back-end). The FINDER front-end
(RS §5 ε-region grid completeness, Items G-concrete/H/I) is gated on the dispatched DR
(`Lit-Search/tasks/20260529_phase6x_rs_grid_completeness_verbatim.md`) and will receive its own
Stage 13 when shipped.
