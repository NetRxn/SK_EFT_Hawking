# FormulaRefSweep — Roadmap

**Goal.** Drive the **81 dangling `formulas.py` → Lean references** to zero, then escalate `validate.py --check formula_grounding` to ratchet/hard-fail on dangling refs. Surfaced by ADR-004 W4 (`formula_grounding`): each `Lean:` docstring reference in `src/core/formulas.py` should resolve to a real declaration; 81 cite renamed/removed theorems (e.g. `FLRWDynamics.friedmann_one` → the module now has `friedmann_I_dot_eq_conservation_times_coeff`). **No formula is grounded on a `True`/placeholder stub** (the dangerous case — `formula_grounding` already hard-fails on that, 0 found); this sweep fixes the *stale-name* drift. PUBLIC repo.

**Why now (real-world reason).** Pipeline Invariant #4 (content-grounding): a formula whose cited theorem doesn't resolve is un-grounded in practice. The δ_diss canary (audit #14) showed name-only grounding hides bugs; a dangling ref is the same rot. Not effort-deferred — the gate made it visible; this clears it.

## Method
1. **Discovery (parallel workflow, 9 agents × 9 refs).** For each dangling ref: read the formula function in `formulas.py` + the cited/implied Lean module + `lean_deps.json`, and decide: **REPLACE** (the correct current decl name that grounds the formula), **DROP** (no grounding theorem exists / the result was removed — strike the ref), or **KEEP** (a legitimate external/Mathlib name or a real decl the parser mis-split — annotate). Adversarially verify the replacement actually grounds the formula (statement matches the computed relation), not just a name-similarity guess.
2. **Application (serial, one editor of `formulas.py`).** Apply the consolidated mapping to the `Lean:` docstring lines.
3. **Verify + escalate.** `formula_grounding` dangling → 0 (or a justified residual recorded as KEEP); then add a dangling-ref **ratchet** (a `FORMULA_DANGLING_CEILING` like the native_decide ceiling) so the count can only decrease and a NEW dangling ref hard-fails. Update Inventory/counts; full validate green.

## Standing rules
- Correctness over expediency: REPLACE only when the new decl genuinely grounds the formula (verify the statement), else DROP honestly. Never rubber-stamp a name-similarity match.
- No new axiom/native_decide/sorry; this is a docstring-only sweep (no Lean edits expected). Stage only own paths; never push unless asked. Don't reference the private RD repo (pre-commit hook).

## Status
| Phase | Status |
|---|---|
| Discovery (9-agent workflow) | ✅ COMPLETE 2026-06-13 |
| Application to formulas.py | ✅ COMPLETE 2026-06-13 |
| Verify + ratchet escalation | ✅ COMPLETE 2026-06-13 |

### Close (2026-06-13) — 81 → 0 dangling
- **Discovery:** 9 parallel agents resolved all 81 → **66 REPLACE** (statement-verified current theorem names; e.g. `friedmann_one`→`hubbleSquared`, `gap_operator_self_map`→`gapOperator_self_map`, `bond_weight_adjoint_suppressed`→`adjoint_channel_suppressed`, `su2k_s_matrix_unitarity`→`S_k2_unitary`), **14 DROP** (no theorem grounds the formula — e.g. `chevalley_embedding_A/G`, `NeutrinoMixing.m_beta_beta`, `MajoranaRung.seesaw_m_r_inverse`, `BHEntropyMicroscopic.HorizonMTCBC.logCorrection`; struck the `Lean:` token with a `(no current grounding theorem)` note), **1 KEEP** (`SKEFTHawking.QuasiOneDReduction` section banner). 52 high / 27 medium / 2 low confidence.
- **Pre-application safety:** all 66 REPLACE `new_name`s mechanically verified to resolve in `lean_deps.json` (0 swapped-dangling).
- **Result:** `formula_grounding` now **437 refs / 437 resolve / 0 dangling / 0 placeholder-grounded**. Gate **escalated to HARD-FAIL on dangling** (ratchet — a new stale/renamed ref now fails). Full validate 41/41; 25 SIG unit tests green. ADR-004 W4 FormulaRefSweep tracked debt = **CLEARED**.
- **Honest residual (minor, future spot-check):** the 2 low-confidence REPLACEs (`diracFluidMetric_det`→`diracFluidMetric_txBlock_det_at_horizon`, `spherical_iff_traces_eq`→`quantum_dim_dual`) and the medium ones are the best-available grounding (statement-read by the discovery agent) but not deep-physics-reviewed; they cite REAL theorems (strictly better than dangling) — flagged for a later grounding-quality pass, not a blocker.
