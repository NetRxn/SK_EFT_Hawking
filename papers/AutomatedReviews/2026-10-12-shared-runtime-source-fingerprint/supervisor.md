# Shared-runtime source fingerprint

**Status: SOURCE FINDINGS CLOSED THROUGH THE CANONICAL WRITER / CURRENT PROJECT GATES AND NATIVE ADMISSION PENDING.**
No native-process or host-prevalence claim. Implementation, independent acceptance,
current gates, integration and supported closure remain separate.

## Findings

### 1 — Inventory-local enumeration omits imported shared controller source

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 fingerprint SOURCE integration
- **Location:** scripts/lean_slots/supervisor.py (_RuntimeSourcePass, Supervisor._runtime_fingerprint/_runtime_inputs/_spawn/_resource_status); tests/test_lean_runtime_fingerprint.py; tests/test_lean_slots.py
- **Observed:** At the frozen before-implementation source, fingerprint enumerates the inventory-local package and skips absent sources. A launcher importing shared code elsewhere can bind its own bytes without that imported implementation. Existing status/reuse compare this incomplete digest. Public launcher uses direct import; slot_repo lacks launcher/package. This is source analysis, not an executed overlay reproduction.
- **Expected:** Actual loaded supervisor/state origins, complete package Python bytes and supported actual child route agree. Launcher/local/shared inputs have distinct deterministic namespaces. Missing, denied, malformed, incoherent or drifting mandatory inputs refuse currentness. This binds expected/recorded source inputs, not process memory.
- **Fix:** Proposed SF-1–SF-7 [design](../../../docs/superpowers/specs/2026-10-12-shared-runtime-source-fingerprint-design.md) and [plan](../../../docs/superpowers/plans/2026-10-12-shared-runtime-source-fingerprint.md). Extend existing fingerprint/consumers, no registry/API/PID adoption.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_runtime_fingerprint.py tests/test_lean_slots.py tests/test_lean_lifecycle_observation.py tests/test_codex_lean_slot_policy.py tests/test_architecture_claims.py -q`


The declared Verify command passed in the primary checkout: 469 tests in 224.28s.
ROOT verified the admitted baseline/red/restored campaign: 56 scenarios, 52 distinct
production images and 168 command captures. Every red result is a native assertion
against the intended production omission; source restoration is exact. Independent
whole implementation review accepted the complete source and original contracts,
including captured-environment route selection, refusal, cost and provenance guards.
The current whole-review report SHA256 is
`30dfc344de4b7abc301b272ee4abad595159672c317028f02bc7b7ebdd7af97e`;
the ROOT actual-campaign report SHA256 is
`225527da00622bc277e80f81844b1176a431ef90a7a4f8e83c5414211ed6acab`.
Raw machine-local captures remain local; no host environment or backend credentials
are published here. Historical invalid and exploratory attempts remain unqualified.

The source repairs are present in the primary checkout. The canonical closure writer
ran each finding's declared verification and wrote its source closure. Canonical counts
include the new test module. Current full-project gates and normal commit remain
separate work. Source acceptance
does not establish loaded process bytes, request drain, ownership, lease, reconnect or
backend rotation.

### 2 — Identity-preserving conversion erased supported transform provenance

- **Severity:** major
- **Lane:** infra
- **Gate:** WHOLE_SF4_SFR4_SOURCE_ACCEPTANCE
- **Observed:** Whole R2 review and ROOT's unchanged genuine-wrapper probe found that str(SHARED) followed by Path reconstructs the same resolved operand as fresh source, admitting a forbidden second expanduser().resolve(). The probe failed its native typed-refusal assertion; it is regression evidence, not mutation credit.
- **Expected/Fix obligation:** Carry same-operand last-transform state through string/Path reconstruction and selected fallback propagation. Retain legitimate derived operand expansion, legal string fallbacks, eager validation, capture and all original contracts.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_runtime_fingerprint.py -q -k "fp_34 or fp_37"`
- **Evidence:** Genuine inline/alias/fallback launchers refuse through actual fingerprint/status/spawn with typed witnesses, exact populated records/reservations and no new pending/Popen/signal. Admitted distinct production omission triads discriminate and restore the current source.

### 3 — Derived operations erased the cumulative parent recipe budget

- **Severity:** major
- **Lane:** infra
- **Gate:** WHOLE_SF4_DECLARED_BOUNDS
- **Observed:** R2 source-derived review showed that literal join, string reconstruction, expand and resolve reset parent_steps, admitting recipes with more than four parent operations. This finding is source-derived; no native runtime measurement is claimed.
- **Expected/Fix obligation:** Carry cumulative parent steps across aliases, conversions, joins and transforms independently of new derived-operand transform state. Preserve available-parent typed refusal and valid recipes totaling at most four; parents[index] consumes index + 1.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_runtime_fingerprint.py -q -k "fp_35 or fp_37"`
- **Evidence:** Genuine >4 versus <=4 complete launchers, including eager inactive defaults/selectors, discriminate at actual fingerprint/status/spawn. Exact resource/effect assertions and admitted distinct production omission triads are retained.
