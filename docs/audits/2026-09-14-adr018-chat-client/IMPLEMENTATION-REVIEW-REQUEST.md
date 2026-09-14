# ADR-018 independent implementation review request

**Status:** requested after author-side hardening completes. Read-only independent implementation review; this request does not authorize live slot execution.

**Implementation PR:** #76 — `implementation/adr018-chat-slot-client`

**Accepted specification:** PR #75 @ `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, final COMMENT review `5202241729`: `ACCEPT`, residual B1 `CLOSED`, B2–B6 no regression.

Resolve the **current PR #76 head and base immediately before review**. The implementation head is expected to move during pre-review hardening; do not trust a stale SHA copied from another artifact.

## Independence / posture

- reviewer is independent from the implementation author/control conversation;
- durable prior specification-review lineage may be read; independence is not amnesia;
- read-only review: do not modify PR #76 files;
- inspect actual code/tests/docs, not only PR prose;
- do not run live slots, restart supervisor, invoke Lean MCP, perform an authoritative build, or execute a real project task;
- distinguish `REMOTE_VERIFIED` source inspection from mechanical tests actually run; absent hosted execution is `NOT_MEASURED`, not PASS;
- file the complete result as GitHub PR **COMMENT** review, never APPROVE/REQUEST_CHANGES;
- review evidence has `authorization_effect = none`.

## Native authorities

Read:

- `CLAUDE.md` progressive-disclosure rules as needed;
- `.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md`;
- `docs/architecture/README.md` slot-ownership row;
- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`;
- `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`;
- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`;
- `docs/superpowers/specs/2026-09-14-adr018-chat-slot-client-design.md`;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`;
- `docs/superpowers/plans/2026-09-14-adr018-chat-slot-client.md`;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`;
- prior review/reconciliation artifacts in `docs/audits/2026-09-14-adr018-chat-client/`;
- issue #74.

Inspect the complete PR #76 diff, especially:

- `config/lean-slots.public.json`;
- `scripts/lean_slots/state.py`;
- `scripts/lean_slots/controller.py`;
- `scripts/lean_slots/proxy.py`;
- `scripts/lean_slots/cli.py`;
- `tests/test_adr018_chat_client.py` and any ADR-018 additions to existing Lean-slot tests;
- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`;
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`;
- any architecture claim/routing docs changed by implementation.

Caller-side `NetRxn/chat-control-plane` PR #37 may be inspected only for compatibility with the eventual Gate-A caller boundary. SK_EFT remains authoritative for lease, admission, build, integration, removal, and slot lifecycle semantics.

## Falsification questions

### Admission authority

1. Is `Inventory.allowed_clients` genuinely the single lease/dispatch admission owner, or does any CLI/proxy/controller/caller retain a competing hard-coded roster?
2. Does schema-1 absence resolve to exactly `{codex, claude}` and never inherit/derive `chat` from a paired public inventory?
3. Can a direct Python caller create an unadmitted lease or session environment before authoritative validation runs?
4. Does bearer proxy identity reject an unadmitted client even when a stale token file exists, without unrelated stale token files breaking valid admitted clients?
5. Can malformed client names escape the state-root client-token namespace or alias another client's token path?

### Removal / revocation / non-vacuity

6. Does removal preflight evaluate the **prospective** roster exactly, including an explicitly empty set, rather than falling back through truthiness/default behavior?
7. Does it refuse a removal that would leave the inventory's required non-empty roster invalid?
8. Does doctor seed/read the real lease artifact and report an active current-roster mismatch red while leaving lease bytes/state untouched?
9. Is the mismatch predicate excluded from `_lease_for_command()` so correct-owner cleanup remains legal?
10. Does `session revoke-token --client` implement the accepted bearer-only, still-admitted, no-live-client-lease, exact-path, idempotent, no-secret-output contract?
11. Challenge the **concurrency window** between removal-preflight / token revocation / roster edit: can a concurrent `acquire` recreate a token or lease after the quiescence check and before the edit, stranding or invalidating state? Determine whether the accepted operational-quiescence model is sufficient or whether the implementation introduced an unguarded race requiring a project-native lock/precondition.
12. Can later re-admission silently reuse the pre-removal credential under any path?

### Renderer / capability separation

13. Does `acquire --client` / `session env --client` delegate admission to inventory while `config render --client` remains an exhaustive renderer capability over only real renderers?
14. Can `chat` or an unknown value fall through to Codex renderer behavior or write config before failure?

### Lifecycle / authority

15. Did implementation alter ADR-008 slot count, build ownership, ready/absorb authority, quarantine behavior, lease owner semantics, private dependency pinning, or no-worker-build rules beyond ADR-018's accepted client-admission extension?
16. Does adding Chat accidentally grant `absorb`, merge, build, repair, push, publication, or private-repository authority?
17. Are owner diagnostics client-neutral without weakening owner checks?
18. Does doctor/reporting remain observational rather than a hidden lifecycle mutation path?

### Migration / documentation

19. Does a production-shaped paired public-explicit/private-legacy fixture exercise `paired_inventory()` and prove private/downstream schema-1 stays Codex/Claude-only?
20. Are ADR-008 S-A/S-C and any other load-bearing current client-enumeration statements reconciled in the implementation wave without rewriting historical records into false present-tense claims?
21. Is the operator guide's removal sequence exactly the accepted canonical sequence and exact `revoke-token` operation?
22. Did the change make any architecture routing/claim document false without updating it?

### Tests / evidence

23. Which tests are production-seeded at the actual seam and which are fixture/helper-only?
24. Are negative controls present for unadmitted programmatic acquire, stale bearer token, wrong client/lease identity, empty/duplicate/malformed roster, legacy pairing, renderer fallthrough, active-lease removal, wrong owner, and credential non-reuse?
25. Do new tests accidentally mutate only `Inventory.raw` in a way that could pass while the production path reads a file/reloaded inventory/process snapshot instead?
26. No hosted test run should be reported as passed unless an actual run exists; identify every required mechanical check still `NOT_MEASURED`.

## Required report

Return:

1. exact repo/PR/current head/base;
2. independence statement;
3. verdict exactly `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`;
4. blocking findings with evidence location, failure sequence, impact, and required disposition;
5. non-blocking findings;
6. unknowns / `NOT_MEASURED` mechanical evidence;
7. duplicate-authority / architecture-overlap analysis;
8. removal/revocation race and non-vacuity analysis;
9. public/private migration analysis;
10. documentation/shipping-obligation analysis;
11. what must change before bounded live Gate A;
12. review limitations.

A favorable result closes only the **implementation-review** gate for the reviewed exact head. It does not authorize merge or live execution. Gate A remains separately bounded and no-mutation; real source mutation remains behind ADR-018 Phase 6.5/7.