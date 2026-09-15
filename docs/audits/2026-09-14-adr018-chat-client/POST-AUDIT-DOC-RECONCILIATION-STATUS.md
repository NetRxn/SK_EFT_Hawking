# ADR-018 post-audit document reconciliation status

Status: AUTHOR_DOC_REPAIRS_COMPLETE_PENDING_VERIFICATION_AND_REVIEW.

## Ownership and handoff

Author lane accepted coordinator handoff after runtime repair `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44` and audit-routing commit `eae41dac6ef8a0e6c7205014b5269e02f2a8ba3b`. PR #76 was re-resolved at head `eae41dac6ef8a0e6c7205014b5269e02f2a8ba3b`, base `design/adr018-chat-slot-client` @ `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, immediately before author edits. No intervening branch move or prior reconciliation-status owner record was observed, so this lane proceeded. The branch remained a fast-forward through the final readback correction; any later unexpected writer move must still be treated as `CONCURRENT_CHANGE`, not overwritten.

No child jobs, automation mutations, runtime/test execution, other-repository writes or review filing were performed by this author lane.

## D1 — current-document reconciliation

**AUTHOR COMPLETE.** Current status/gate statements were reconciled without rewriting historical review artifacts or changing accepted removal/lifecycle semantics.

Changed current surfaces:

- `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md`;
- `docs/adrs/ADR-018-b1-removal-preflight-addendum.md`;
- `docs/superpowers/specs/2026-09-14-adr018-chat-slot-client-design.md`;
- `docs/superpowers/specs/2026-09-14-adr018-b1-removal-preflight-design.md`;
- `docs/superpowers/plans/2026-09-14-adr018-chat-slot-client.md`;
- `docs/superpowers/plans/2026-09-14-adr018-b1-removal-preflight.md`;
- `docs/audits/2026-09-14-adr018-chat-client/REVIEW-STATUS.md`;
- `docs/audits/2026-09-14-adr018-chat-client/README.md`;
- `docs/audits/2026-09-14-adr018-chat-client/POST-AUDIT-REPAIR.md`.

Current truth is now: specification `ACCEPT` at PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` / COMMENT `5202241729`; bounded author implementation in progress; prior implementation review `5203396570` applies only to `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`; mechanical evidence and a fresh exact-head independent implementation re-review remain pending before Gate A. Canonical D8/S18-9 ordering remains pre-edit bearer revocation while still admitted, with observational mismatch reporting and owner cleanup unchanged.

Initial final-file readback found one surviving stale shorthand in main-plan Phase 0 Task 0.2 (`quiesce, edit, token cleanup, ...`) even though the current operator section had already been corrected. Commit `404aa7b60b86526874e10c6a0e30b21d9f1a0264` corrected that historical disposition summary to the accepted canonical order: quiesce + removal preflight → bearer revocation while still admitted → roster edit → restart → verify. This was a documentation consistency correction, not a new mechanism or decision.

## D2 — focused implementation re-review request

**PREPARED / NOT ENQUEUED.** `POST-AUDIT-IMPLEMENTATION-REREVIEW-REQUEST.md` scopes a changed-head read-only review of:

- prior implementation-review B1 document/status contradiction;
- the original absent-vs-explicit-null failure;
- neighboring malformed values (`null`, booleans, numerics, strings, object, empty array and existing member/name validation);
- positive controls for absent legacy fallback, explicit narrow roster, and valid public immutable roster;
- both authentication modes in the artifact-seeded parser test;
- no runtime-authority expansion and no D8/S18-9 regression;
- authored-versus-executed mechanical evidence.

It explicitly requires current head/base resolution, COMMENT-only filing, and independence/context limitations. It is intentionally **not** posted to central review intake while independent scheduled context is unresolved.

## D3 — mechanical verification feasibility

**READ-ONLY FEASIBILITY COMPLETE; EXECUTION NOT_MEASURED.**

Observed repository facts at author handoff and final documentation heads:

- `.github/` contains `dependabot.yml` and no `.github/workflows/` directory. The repository's own `tests/test_architecture_claims.py::test_there_is_no_scheduled_ci_runner` explicitly asserts that there is deliberately no scheduled GitHub workflow runner.
- Actions workflow-runs queries filtered to the author handoff head `eae41dac6ef8a0e6c7205014b5269e02f2a8ba3b` and documentation handoff head `4a6ce8ddd0534dd749be093a542287a1e497f1cb` each returned `total_count: 0`. No PASS is inferred for later documentation-only heads either.
- `pyproject.toml` requires Python `>=3.14`, includes `pytest>=9.0.3`, sets `pythonpath = ["."]`, and by default excludes `slow` and `e2e` tests.
- `tests/test_adr018_roster_validation.py` imports only stdlib/pytest plus `Inventory`/`SlotError`, uses `tmp_path` and `monkeypatch`, writes disposable inventory JSON, sets `LEAN_SLOT_STATE_DIR` to a temporary location, and asserts parser loading creates no runtime-state directory. It does not invoke Git, slots, server, Lean, MCP or controller lifecycle.
- `tests/test_adr018_chat_client.py` is broader but still synthetic: it requires the `git` executable, creates disposable Git repositories/worktrees, sets `LEAN_SLOT_SKIP_SUPERVISOR=1`, uses inert synthetic build commands, and exercises controller/proxy/CLI admission behavior without needing a live supervisor or Lean process.

Existing exact verification commands, in increasing scope:

```text
uv run python -m pytest tests/test_adr018_roster_validation.py -q
uv run python -m pytest tests/test_adr018_roster_validation.py tests/test_adr018_chat_client.py -q
uv run python -m pytest tests/test_architecture_claims.py -q
uv run python scripts/validate.py --check architecture_inventory_fresh
```

The second command is the finding's native `Verify` command. The documentation commands come from the repository's architecture guidance. These commands were **identified, not run**.

Minimum environment/evidence requirements:

- repository checkout at the exact head being claimed;
- Python 3.14+ and project test dependencies resolved from the repository configuration; `uv` for the native commands;
- `git` executable for `tests/test_adr018_chat_client.py`;
- no secret, slot, supervisor, Lean or MCP credential is required for the parser-only test;
- on a cold environment, dependency resolution/install may require ordinary package access; source inspection here does not prove an external hosted image already has the environment;
- PASS requires captured command result tied to the exact resulting head. A green result from another SHA or source inspection is not transferable.

**Hosted-path conclusion:** no repository-owned GitHub Actions workflow exists to run these checks automatically, and no exact-head hosted run was observed. An external/private runner outside repository-visible configuration is UNKNOWN and must not be inferred absent. Therefore mechanical evidence remains `NOT_MEASURED`.

Smallest next verification step is not a new CI project: on an already authorized mechanical runner with a clean exact-head checkout, execute the parser-only regression first, then the finding-native pair and the two documentation checks above, recording exact SHA and outputs. This author lane does not have authority to dispatch that runner or execute the commands locally.

## Evidence boundaries and remaining work

- Code/test repair: `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44` — authored, NOT_MEASURED.
- Audit-routing handoff: `eae41dac6ef8a0e6c7205014b5269e02f2a8ba3b`.
- D1–D3 substantive author document reconciliation: `01bacd198ef20e496a8d9ba01d2cc6661017e0fe`.
- Initial author status handoff: `4a6ce8ddd0534dd749be093a542287a1e497f1cb`.
- Final-plan readback correction: `404aa7b60b86526874e10c6a0e30b21d9f1a0264`.
- Specification acceptance: PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, COMMENT `5202241729`.
- Prior implementation review: COMMENT `5203396570` at `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa`, `ACCEPT_WITH_CHANGES`.
- D1–D3 changed paths are the nine current surfaces listed above plus `POST-AUDIT-IMPLEMENTATION-REREVIEW-REQUEST.md` and this status file.
- No current head receives independent acceptance from this author work.
- Roster-null finding remains open pending project-owned verification/closure evidence.
- Remaining before Gate A: exact-head applicable mechanical evidence; independently established reviewer context; focused exact-head implementation re-review; project-native disposition of findings/gates.
- Remaining before source mutation: all Gate A requirements plus heartbeat, disposable write/checkpoint/ready evidence, and separately reviewed same-owner integration continuation.

Current owner handoff: AUTHOR_DOC_REPAIRS_COMPLETE_PENDING_VERIFICATION_AND_REVIEW. No further author documentation mutation is required unless readback exposes another contradiction or another writer changes the branch. The current PR head is the authoritative freshness key and must be resolved before later verification/review.
