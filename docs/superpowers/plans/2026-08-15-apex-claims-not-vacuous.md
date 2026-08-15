# Plan — `apex_claims_not_vacuous`

**Design:** [`../specs/2026-08-15-apex-claims-not-vacuous-design.md`](../specs/2026-08-15-apex-claims-not-vacuous-design.md) ·
**Decisions:** [`ADR-016`](../../adrs/ADR-016-apex-claims-and-the-vacuity-registers.md)

## Global constraints (inherited by every task)

* The repo is shared with concurrent agents — **stage explicit paths only**. Never
  `git add -A`, `git add .`, `git commit -a`. `papers/D2/bundle_metadata.json` in
  particular is being written concurrently by a Stage-13 recorder; re-read before editing
  and diff before staging.
* Paths through `_H.<NAME>` at each use; flags through `_cfg.<FLAG>` by attribute.
* Every ceiling carries **zero headroom** and a test asserting it equals the live value.
* No declaration is added to `VACUOUS_STATEMENT_BASELINE` or to any exemption set by this
  work. Ever. (ADR-016 D4.)

## Phases

**P1 — documents first** (rule 2). ADR-016, this spec, this plan. ✅

**P2 — D2 metadata repair** (ADR-016 D7). Independent of the check and done first so the
ceilings are set against a repaired corpus rather than one the same commit is about to
change. ✅

**P3 — the shared classifier's one new label** (ADR-016 D3). `_thin_type_label` gains
`reflexive-literal (R n n)`; **not** in `_THIN_HARD`. Blast radius measured: 4
declarations, all advisory in `vacuous_statement_audit`.

**P4 — the check.** `apex_claims_not_vacuous` in `bundles_readiness.py`, its two ceilings,
and `APEX_CLAIMS_SCORED_FLOOR` 639 → 638.

**P5 — registration.** The seven sites `registration_sites.py` reports, plus
`CI_MIN_CHECKS_RUN` + 1.

**P6 — the non-vacuity test**, production-seeded through `seed_journal`, three seeds
(placeholder / thin-hard / undisclosed trivial-witness), registered in `MUTATION_VERIFIED`.

**P7 — documents the change makes wrong** (rule 2, same commit): `VALIDATION_GATE_TOPOLOGY`
(what the gate computes), `QA_QI_INFRASTRUCTURE_MAP` §3 if the coverage statement moves,
`SURFACE_INVENTORY` regenerated, `BUNDLE_DIRECTORY_SCHEMA` (`claims` now has a reader and
a disclosure convention), the finding this discharges.

**P8 — findings** at `papers/AutomatedReviews/2026-08-15-apex-claims-unbacked/infra.md`,
each with a `Verify` that fails at HEAD: the 15 undisclosed rows by bundle, the
sound-but-irrelevant axis (ADR-016 D6), the 4 reflexive-literal declarations, and
`sm_with_nu_R_anomaly_free`.

## File → task map

| file | phase |
|---|---|
| `docs/adrs/ADR-016-*.md`, `docs/superpowers/{specs,plans}/2026-08-15-apex-claims-not-vacuous*.md` | P1 |
| `papers/D2/bundle_metadata.json` | P2 |
| `scripts/validation/checks/lean_statements.py` | P3 |
| `scripts/validation/checks/bundles_readiness.py` | P4 |
| `scripts/validate.py`, `scripts/verify_scope.py`, `tests/test_validate_registry_contract.py`, `tests/test_ci_mode.py` | P5 |
| `tests/test_d5_bundles_readiness.py`, `tests/test_d5_mutation_obligation.py` | P6 |
| `docs/architecture/*`, `docs/BUNDLE_DIRECTORY_SCHEMA.md`, the discharged finding | P7 |
| `papers/AutomatedReviews/2026-08-15-apex-claims-unbacked/infra.md` | P8 |

## Out of scope, and who owns it

* Remediating the 15 undisclosed rows in D1/D3/D4/D5/D8/D10/F — P8's finding, per bundle,
  and it needs the draft read alongside the metadata.
* A relevance/path check for ADR-016 D6 — P8's finding §1.4.
* `proxy_body_audit`'s name gate — unchanged by design (ADR-016 D2).
