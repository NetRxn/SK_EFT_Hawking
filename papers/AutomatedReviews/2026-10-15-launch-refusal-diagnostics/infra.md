# Typed launch and restoration witnesses are lost at CLI error presentation

### 1.1 — 🟡 REQUIRED — Preserve bounded explicit failure provenance at the CLI

- **Severity:** major
- **Lane:** `infra`
- **Location:** `scripts/lean_slots/cli.py`; `scripts/lean_slots/state.py`; `scripts/lean_slots/supervisor.py`; `tests/test_lean_lifecycle_observation.py`
- **Verify:** `.venv/bin/python -m pytest -m '' tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q -s`

The CLI formats the caught exception message without its typed observation fields.
The launch rollback, paused transition, paired activation, counterpart restoration,
global startup rollback and borrowed discovery cleanup wrappers retain secondary
error strings while discarding their actual nested exception relation. Copying
direct secondary observations alone also loses nested causes and their provenance.

Extend existing SlotError diagnostic data and CLI handling with bounded explicit
cause/labelled-secondary traversal. Keep each admitted witness with its originating
exception, preserve exact small typed fields, disclose omissions and unknown tails,
and retain every existing lifecycle decision and persistent error string.

Verify must exercise the actual production wrappers and CLI through isolated
external seams, cover nested and multiple cleanup failures and strict serialization
bounds, and retain compatibility and unchanged-control assertions. Two independent
production mutations must fail their specific secondary-provenance and CLI-receipt
assertions, with exact source restoration and green reruns. Existing lifecycle
identity and cleanup fixes remain valid; this is a separate presentation defect.

Closure requires whole independent source/evidence review, normal commit/integration
and the existing close_finding.py writer executing the declared Verify. Isolated
diagnostic tests do not establish the cause of a native refusal or loaded runtime
reliability. Broader project and scientific acceptance remain separate.
