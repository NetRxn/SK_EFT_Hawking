# Lean proxy client-session value plan

Status: **DOCUMENT AUTHORING ONLY / fresh exact tracked-text review required before
implementation.** No implementation, actual Handler test, mutation, source
integration, scanner or native acceptance is recorded here. Contract:
[ADR-008 ST-1–ST-8](../../adrs/ADR-008-shared-lean-slot-control-plane.md#client-session-value-boundary-st-amendment),
[design](../specs/2026-10-15-lean-proxy-client-session-value-design.md) and
[operator guide](../../dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md#client-session-value-boundary).

## Global constraints

Extend the existing `proxy.py` Handler boundary and existing `test_lean_slots.py`
`Wire` seam in one coherent implementation/test package after specification review.
Use the existing remediation planner and closure writer. This plan creates no
checker, registry, routing ledger, CLI, lifecycle API, gate, workflow or controller
policy. Keep public source self-contained. No scientific source, proofs, cache,
canonical data or mathematical acceptance is part of this correction.

ROOT owns source integration, Git commits, exact-head CI assessment, notebook and
closure writes, project builds/gates and every runtime operation. Assigned authors
write only their packet's paths and report exact bytes; independent reviewers do
not certify their own work. The document-authoring assignment permits only the
owning ADR, design, plan and guide plus its ignored report. It does not permit code,
tests, mutations, service or socket activity. A matching continuity snapshot is
freshness evidence rather than execution or acceptance authority.

Preserve the original contracts throughout: case-insensitive singleton selection;
`None` versus explicit empty; strip only outer SP/HTAB; nonempty `0x21..0x7E` with
all visible punctuation and opaque comma; reject duplicates even identical; no
UUID grammar, generic repair or lower cap. Place the single call after existing
auth/lease checks and before initialize/mint/cache/broker/backend work. Static 400
detail and no session echo preserve the independently serialized JSON-RPC ID.
HEAD remains nonconsuming. Reuse one canonical key/echo and remove first-value
reselection; preserve S-Q mint, unknown adoption, sessionless reuse and one retry.
GET/backend header passthrough remains a separate boundary.

## File-to-task map

| Surface | Responsibility and review dependency |
|---|---|
| `docs/adrs/ADR-008-shared-lean-slot-control-plane.md` | ST decisions and overlap with S-D/S-N/S-Q, LO-5 and SF; keep source/native acceptance explicit. |
| `docs/superpowers/specs/2026-10-15-lean-proxy-client-session-value-design.md` | Exact selector, error/consumer boundaries, H01–H14 and parser/backend limitations. |
| This plan | Coherent order, ownership, non-vacuity and required verification; no execution ledger. |
| `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md` | Client/session behavior and separate ROOT-controlled runtime admission. |
| `scripts/lean_slots/proxy.py` | Later implementation only: one pure `_client_session_id(headers)` and one `_handle` call, separate static failure branch, canonical key/echo; remove old selection. Leave `SessionBroker`, gate, backend and HEAD semantics intact. |
| `tests/test_lean_slots.py` | Later implementation only: compatibly extend existing actual Handler `Wire` seam for methods, raw ordered fields, absent/empty distinction and raw output; implement all design matrix rows and mutation oracles. |
| Existing slot policy/lifecycle/architecture-claims/runtime-fingerprint test modules | Execute current relevant regressions; no edits allocated here. A newly necessary edit needs a coherent revised assignment and review. |

## Phase A — exact documents before code

1. Reconcile current continuity packet and source pins. Read architecture ownership,
   ADR-008, guide, current Handler/SessionBroker and existing tests. The baseline
   source is `d87df4da8943b7e6ad4d67733ad6941ee9b94e08`; exact relevant file bytes,
   rather than unrelated branch progress, bind the specification.
2. Author the ADR amendment, design, this plan and necessary guide amendment.
   Describe mechanisms, limitations and acceptance states. Keep private paths,
   identifiers and context out of tracked documents. Add no narrative census.
3. Obtain fresh independent adversarial review of the exact complete tracked texts
   against current code and an intent-drift assessment against the authorized
   bounded selected-value correction. Proposal review is not review of these
   documents. Resolve mandatory findings and obtain ROOT specification intake
   before implementing or executing tests/mutations. The architecture-change skill
   applies again before treating the specification as settled.
4. Freeze exact document/source hashes, decision/case/refinement mapping, commands
   actually run and remaining limits in the assigned ignored report. ROOT owns
   normal commit/integration. This phase makes no population-shape assertion or
   population pilot claim; any later such claim requires the existing pilot.

## Phase B — one implementation and actual Handler package

After accepted specification and a fresh explicit implementation assignment:

1. Extend `_post`'s existing `Wire` mechanics compatibly with old callers. Preserve
   the old call/return behavior while making ordered raw fields and raw request
   bytes expressible; do not collapse duplicates into a dictionary. Treat `None`
   as absent and `""` as explicitly present. Support GET/POST/DELETE and HEAD in
   this seam, and expose raw emitted bytes before `HTTPResponse` parsing can hide
   a malformed response. No socket server or parallel fake production Handler.
2. Establish the old-code red control before adding the guard: use an authorized
   retained folded session value through the actual Handler with a scripted
   successful backend. The oracle expects static 400/no echo/no side effects and
   must fail because old code reaches the buffered response. Backend failure,
   offline fallback, a helper-only predicate or an unrelated exception is not the
   defect reproduction. Retain original output and exact source hash.
3. Implement the design's pure selector and one call immediately after the
   existing gate. Catch selector failure separately; call the existing `_deny`
   with static `invalid Mcp-Session-Id header` and independent request ID. Remove
   old first-value selection; use the canonical string for key/echo and `None`
   alone for `"\x00sessionless"`. Keep broker lifecycle and HEAD intact.
4. Complete H01–H14 in the same module. H04/H06/H13 explicitly exercise raw
   positive/negative DELETE. H06 covers retained parsed controls, including folded
   CR/LF, VT/FF and non-ASCII boundaries; H07 keeps parser-erasure cases distinct.
   H02 asserts static error detail and no session-header-derived echo/detail,
   without forbidding an independently equal JSON-RPC ID. H08 records actual
   runtime/framing for the 65518/65519 canonical line cases.
5. Keep positive and refusal paths together. Preserve valid punctuation/case,
   explicit comma/percent literals, absent versus empty, identical valid
   duplicates, source UUID and unknown token adoption. Keep existing identity and
   policy tests, add actual Handler unleased tool and GET cases, and assert
   initialize/offline/cache/head/retry side-effect order. Script connection and
   broker effects independently; do not mock the admission verdict.
6. Correct any owning text made wrong by implementation in the same implementation
   commit. A material boundary or scope change returns the whole revised
   specification for review before expanding the package.

## Phase C — independent review and current verification

ROOT executes controls only in the authorized isolated candidate using the
canonical primary interpreter by absolute path with the candidate as working
directory. No candidate dependency installation or controller activity is needed.
Retain actual logs, exits and exact source hashes. Independent implementation
review covers the entire code/test/document package, the original defect and every
matrix row, rather than only added lines.

Run separate sole production mutations against the actual Handler controls:

| Mutation | Decisive control |
|---|---|
| Bypass the production selector call with the former first-value selection so unchecked input reaches consumers; do not create an undefined variable. | The retained folded-value actual Handler negative reaches unsafe buffered behavior and turns red; H02/H06 remain the boundary witnesses. |
| Bypass only duplicate rejection, allowing a first value to be used. | H03 with identical individually valid fields turns red even though the alphabet guard would accept either value. |
| Bypass only the visible-ASCII guard, keeping presence/multiplicity handling. | H06 with a nonempty retained NUL/control or fold turns red for unsafe flow, rather than an unrelated encoding exception; H04 positive visible punctuation still passes. |

Use `scripts/seed_journal.py` for source mutation/restoration. Preserve original,
sole mutant and restored bytes/output. Restore exactly and rerun each control green
before the next mutant. A test assertion mutation, several simultaneous bypasses,
an unrelated exception or failure before the unsafe path does not establish
non-vacuity. Retain independent positive initialize, unknown/sessionless/retry and
DELETE cases across the campaign.

From canonical primary after reviewed source integration, required commands are:

```text
.venv/bin/python -m pytest tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q
.venv/bin/python -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py tests/test_architecture_claims.py -q
.venv/bin/python -m pytest tests/test_lean_runtime_fingerprint.py -q
.venv/bin/python -m pytest -q
git diff --check
```

Also run the focused actual Handler controls and each mutation/restoration oracle
by its real collected test name once implemented. Zero collected tests is not a
pass. Recompute collected/executed/pass/fail/skip counts and record source/runtime
versions, scopes and exclusions. Do not copy a historical runner-pass count into
current acceptance. The default pytest configuration includes repository and
plugin tests while excluding `slow` and `e2e`; that result is not all-marker,
Lean/full-project, native or publication acceptance. Preserve broader failures and
apply existing required gates without a new gate family.

ROOT inspects the current exact-head CI aggregate, if run, and records its actual
state. Local tests do not imply remote CodeQL recognition or resolve scanner
findings. No suppression or scanner-green promise is part of this plan. Use the
existing closure writer only after its actual declared evidence is met; source
review, integration, project gates, merged-wave and native acceptance stay distinct.

## Phase D — later ROOT-controlled runtime transition

This phase is separate from source implementation and is not authorized by authoring
or reviewing these documents. ROOT preserves ongoing mathematical work and first
coordinates every relevant lease owner, freezes dispatch/probes and accounts for
actual completed owned requests. A source edit, commit, scan, FREE lease, closed
socket, timeout or expected launch-source fingerprint cannot prove request drain or
loaded code.

Meet existing LO-5 known-owned replacement rules: reliable FREE, complete capable
current census, both-role backend/project/retained-descendant absence, target-slot
then one lifecycle lock, exact proxy/listener identity and required before/after
TCP/thread/state-directory observations. Supplementary samples do not establish
completion of unaccounted work. Unknown resources remain reserved and untouched.
Under the held lifecycle lock use existing unlocked internals, without reacquiring
its nonreentrant public wrapper. Global start/stop/status semantics do not change.
No cache, lease, epoch or process record may be fabricated to obtain admission.

Separately measure loaded-source evidence and native initialize/list/unleased
denial, matching-lease dispatch, release/reconnect/recovery and paired epoch checks
where applicable. A persistent proxy's backend-session rotation does not establish
client continuity through replacement of that proxy. Keep source acceptance,
loaded-runtime acceptance, mathematical acceptance and broader project/publication
states explicit. ROOT owns ordinary integration, final close-out and any later
runtime admission records.
