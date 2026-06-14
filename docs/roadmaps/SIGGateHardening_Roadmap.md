# SIG Gate Hardening + Semantic Grounding Audit — Roadmap

**Goal.** Close the **4 SIG detector blind-spots** the 2026-06-13 ledger-reconciliation found (the "presence-not-load" root cause recurring *inside* the ADR-004 gates) **+ build the real semantic formula-grounding audit (audit #14 / Wave-21)**. PUBLIC repo. Then PLAN the Rokhlin `topo` discharge (separate wave).

**Why now (real-world reason).** The SIG gates (ADR-004) close the substance/disclosure QI classes via **pathway #2 (structural prevention)** — which the pipeline (Stage-14 policy) makes *mandatory* for these classes. A detector with evadable holes is a partial pathway-#2: the generator survives. The reconcilers found 4 concrete evasions + the #14 semantic check is only half-built (name-resolution shipped; the "conclusion proves something" check open). Closing them completes the structural prevention.

## Blind-spots (reconciler-verified, on disk)
| ID | Evasion | Fix |
|---|---|---|
| #23 | `proxy_body_audit` R2: anonymous-constructor body `⟨Equiv.refl _, …⟩` evades `_TRIVIAL_BODY_RES` (`z16_classification`, `dai_freed_spin_z4`) | add anon-ctor-of-trivials body pattern |
| #25 | `_scan_lean_theorem_bodies` returns **empty body** when `:=` + body are on a *continuation* line (`body_start_col` uses the joined-`acc` offset, not the line offset) → R2 silently skips (`hom_tensor_adjunction_dim`) | fix `body_start_col = lines[j].find(':=')` |
| #45 | R2 is name-gated (`_STRUCTURAL_NAME_RE`) + excludes `norm_num`, so bare-arith theorems (`tetrad_components : 4*4=16`, `spin_connection_gap : 6>1`) slip | new **type-based** `vacuous_statement_audit` (name-agnostic) |
| #9 | No check that paper prose matches a theorem's disclosure tier — D5 says an aggregator "establishes the 8/8 closure" while its `MODELING_ASSUMPTION_THEOREMS` entry says "bookkeeping" | new `disclosure_consistency` check |
| #14 | `formula_grounding` only rejects `type=='True'`; a formula grounded on a reflexive `Eq N N` (proves nothing) passes (5 live: `fib_wrt_rank`, `ising_wrt_rank`, `fierz_channel_count`, `fib_wrt_S2xS1`, `ising_wrt_S2xS1`) | harden with the thin-type predicate |

## Design (calibrated against 20,502 decls + 437 groundings)
**Core: `_thin_type_label(type)`** over the elaborated lean_deps type — high-precision, name-agnostic:
- **HARD** (unambiguously vacuous): `True` (non-PLACEHOLDER); reflexive `Eq X X` (bracket-aware 2-arg split, ==); hypothesis-return `… → P` with `P` ∈ hypotheses (top-level `→` split). Probe: ~15–25 tree-wide after fixing parser FPs.
- **ADVISORY** (surface, don't block — 105 ground-arith mixes vacuous-dressing with **legit counts** like `metric_independent_components : 4*5/2=10`; no syntactic separator exists): ground-arithmetic (closed numeric prop, no free vars / named idents).
- Exempt: `PLACEHOLDER_LEAN_NAMES` + `MODELING_ASSUMPTION_THEOREMS` (reason+discloses).

**Checks:**
- `vacuous_statement_audit` (new, R2-companion) — hard-fail on HARD-thin project theorems/lemmas; advisory on ground-arith.
- `formula_grounding` (#14) — additionally reject groundings on HARD-thin theorems.
- `disclosure_consistency` (#9) — no paper claims a `definitional`/`vacuous_proxy`-disclosed theorem "establishes/proves/demonstrates" a result (reuse `_VERIFY_CLAIM_RE`/`_HEDGE_CLAIM_RE` + optional `claim_pattern`).
- `proxy_body_audit` (#23) + `_scan_lean_theorem_bodies` (#25) — body fixes.

## Disposition policy for surfaced HARD-thin theorems (triage)
- **Safe-delete** (0 external refs, real proof exists alongside): `nogo_fails_with_three_violations`, `tetrad_modes_nf_independent`.
- **Restate** to a substantive statement where feasible (the 5 WRT/Fierz `Eq N N` → `Eq <computed expr> N`, or reground the formula on the real computation theorem).
- **Disclose** (vacuous_proxy + discharge) where a consumer/paper ref makes deletion unsafe (`tetrad_components`, `spin_connection_gap` — collide with `ADWMechanism` def + paper5).
- **#23**: disclose as `definitional` (the cobordism iso is a genuine Mathlib-absent wall; the `∃φ,Equiv.refl` is honestly documented) — or convert to a named opaque tracked-Prop.
- **#54**: restate `vestigial_phase_eta_violates_microscope_bound` over named Lean constants (breaks on drift).
- **#9**: reframe D5 prose L911-924 (aggregator = classification-ledger, not "establishes").
- **#25**: reconcile ChangeOfRings module docstring ("H2 DISCHARGED") with the now-honest `_TODO`; delete/disclose the two identity-wrappers.

## Standing rules
No axiom/native_decide/sorry/maxHeartbeats. Detectors ship calibration whitelist + unit tests (`tests/test_substrate_integrity_gates.py`). Stage only own paths; never push unless asked. Don't reference the private RD repo. Lean edits → rebuild lib + ExtractDeps + lean_deps regen (force `_run_extraction()`).

## Status
| Phase | Status |
|---|---|
| W1 scanner `body_start_col` fix (#25) + R2 anon-ctor (#23) | ✅ |
| W2 `_thin_type_label` + `vacuous_statement_audit` (#45/#54) | ✅ |
| W3 `formula_grounding` hardening (#14) | ✅ |
| W4 `disclosure_consistency` (#9) | ✅ |
| W5 baseline ratchet + named-exemplar dispositions | ✅ (ratchet) |
| W6 tests + full validate green + commit | ⏳ |
| — then PLAN Rokhlin topo discharge (separate wave) | ⏳ |

### Close note (2026-06-13)
**The 4 blind-spots are closed structurally; the gate UN-HID a widespread pre-existing class.** Fixing the scanner empty-body bug (#25), adding the anon-ctor pattern (#23), and the name-agnostic type-thinness classifier (#45/#54) surfaced **~48 content-thin theorems** the prior name-gated/norm_num-excluding/body-mis-parsing detectors silently skipped (an entire RHMC `P→P` cluster — `even_odd_force_equivalence`, `schur_complement_det`, `spin4_orthogonal`, `majorana_gamma_squared_identity`, … — plus a reflexive `Eq N N` count/dim cluster — `three_gaps`, `wilson_*`, `fib_wrt_*`, `hom_tensor_adjunction_dim`, `z16_classification`, …).

**Calibration wins (don't regress):** (a) `*.congr_simp` / `*.mk.*` are Lean/Mathlib auto-generated lemmas → `_is_autogen_decl` excludes them. (b) lean_deps' pretty-printed `type` **elides implicit args**, so a genuine transfer `P_ℝ→P_ℚ` (`sigPos_cast_pos`, a real 20-line density proof) prints as `P→P` → type-based hyp-return is OMITTED and reflexive is restricted to SIMPLE args. (c) ground-arith mixes vacuous-dressing (`4*4=16`) with real counts (`4*5/2=10`) → ADVISORY, not hard.

**Disposition = identity-pinned BASELINE ratchet** (`VACUOUS_STATEMENT_BASELINE`, 48 names, constants.py): grandfathered as VISIBLE tracked debt; both `vacuous_statement_audit` + `proxy_body_audit` report baseline → advisory, NEW → hard-fail (closes the generator, ADR-004 pathway #2). The set may only SHRINK. #14: 5 thin formula-groundings regrounded onto `wrt_S2xS1_eq_rank` (4) + Fierz count dropped (1). #9: D5 prose reframed (aggregators "record the tally / classification ledger", not "establish"); `entropic_gravity_no_go_count_eight` + `r_d_independent_count_eight` disclosed definitional.

**→ FOLLOW-ON `/goal`: "Vacuous Statement Sweep"** — disposition the 48 baselined theorems (strengthen / restate / delete / disclose), shrinking the baseline to 0. Several are genuinely deletable (`nogo_fails_with_three_violations`, `tetrad_modes_nf_independent`, 0 refs); some need restatement (the RHMC `P→P` cluster → real transfer statements or deletion); `_DEFINITIONAL`-suffixed ones → MODELING_ASSUMPTION. ~40-person-day class at project rate = a focused wave.
