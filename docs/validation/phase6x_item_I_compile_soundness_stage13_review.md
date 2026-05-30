# Phase 6x Item I — `compile_correct` soundness chain — Stage 13 adversarial review

**Date:** 2026-05-30  **Verdict:** ✅ **GREEN** (0 BLOCKER / 0 REQUIRED / 0 ADVISORY)
**Reviewer:** fresh-context adversarial agent (read-only), per Wave Execution Pipeline Stage 13.

## Scope reviewed

The Ross-Selinger Clifford+T exact-synthesis **soundness** chain shipped this session
(scope-corrected: SOUNDNESS in Lean + empirical completeness via pygridsynth; the NT arc is the
documented deferred follow-on). Files:

- `lean/SKEFTHawking/FKLW/RossSelinger/CompileApprox.lean` — `linftyOpNorm_fin_two_le`, `su2_entry_structure`
- `lean/SKEFTHawking/FKLW/RossSelinger/GridCompileCorrect.lean` — `toComplex_conj`, `linftyOpNorm_sub_le_of_su2_col`, `approx_assembleUnitary`, `compile_correct_core`, `gridNumerator`(+`toComplex_*`), `gridNumerator_approx`, `compile_correct_grid`
- `lean/SKEFTHawking/FKLW/RossSelinger/GridSolutions.lean` — `oneDimGridSolution`/`twoDimGridSolution` (+specs)
- `lean/SKEFTHawking/FKLW/RossSelinger/Compile.lean` — `compileColumn`, `compile`, `compile_correct`, `compileColumn_approx`

Commits: `d747b24`, `91a63be`, `5fd6acf`, `9eb7b84`, `bf13fec`, `f896158`, `3828768`, `167eb56`,
`02662f8`, `b5ac08a`, `1a3b771` (+ Stage 9/10 `d16972b`).

## Findings: NONE

Adversarial checks (vacuity, statement correctness, norm identity, composition integrity,
constant/scaling sanity) all passed:

- **No `sorry`/`admit`/new `axiom`/`maxHeartbeats`** in any of the 4 files (grep hits are docstring
  compliance notes only). No `axiom` declaration anywhere in `RossSelinger/`.
- **Axiom closure** (`lean_verify`): `compile_correct`/`compile_correct_core`/`compile_correct_grid`
  close over `{propext, Classical.choice, Quot.sound}` + the four PRE-EXISTING KMM-coverage
  `native_decide` cores (`bridge_box_core`, `cliffordBase_box_core`, `kmm_lemma3_alg2`,
  `maStep_exists_core`) — already tracked by the `axiom_closure_allowlist` gate, NOT new.
  `compileColumn_approx`/`su2_entry_structure` close over only the 3 standard axioms. No `sorryAx`.
- **Non-vacuity**: the det-1 constraint `normSq u + normSq t = ⟨0,0,0,2^k⟩` is satisfiable for
  genuinely nonzero `u, t` (e.g. `u=1, t=ω²` at `k=1`, `#eval`-confirmed). The compile-soundness
  hypotheses are jointly satisfiable.
- **Norm**: `‖·‖` is `Matrix.linftyOpNorm` (the SK-headline norm), via the local instance — not a
  weaker norm. `toComplex` is a faithful embedding (`toComplex √2 = √2` real; `omegaC² = i`).
- **`compile_correct` points at the actual output** `w = gridSynthWord (compileColumn U k) t k`;
  proves `compile = some w` (`gridCompile_correct.1`) then `‖toComplexMat(interp w) − U‖ ≤ 2ε` by a
  genuine `interp w → assembleUnitary` rewrite + `approx_assembleUnitary` — not a vacuous identity.
- **`compileColumn_approx`** discharges the first-column hypothesis unconditionally for `k` with
  `1+√2 ≤ 2ε√2^k` (satisfiable ∀ε>0); the `2ε`/`4δ` constant bookkeeping is correct.
- Clean compile (`lake env lean Compile.lean`, exit 0, zero diagnostics).

## Scope notes (not defects)

Completeness is intentionally out of Lean scope (the finder *producing* a valid `(u,t)` / the
unconditional `t`-existence is the empirical pygridsynth / parked-NT follow-on). Docstrings are
honest about this. The four `native_decide` cores are inherited from the upstream KMM-coverage
proof, correctly disclosed.

## Disposition

The Item-I `compile_correct` soundness chain passes Stage 13. Remaining for Item I EXIT (out of
this review's scope): pygridsynth ≥50-case cross-val (empirical completeness), Item G headline,
Item L (SU(8)).
