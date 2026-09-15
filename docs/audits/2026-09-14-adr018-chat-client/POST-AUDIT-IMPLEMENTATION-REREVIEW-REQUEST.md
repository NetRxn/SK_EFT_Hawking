# ADR-018 focused post-audit implementation re-review request

**Status:** PREPARED / NOT ENQUEUED. This is a durable review scope, not review evidence or execution authorization.

## Target and lineage

Target `NetRxn/SK_EFT_Hawking` PR #76 on branch `implementation/adr018-chat-slot-client`. Resolve the **current** PR head and base immediately before review; do not inherit a verdict from a prior head.

Specification authority is PR #75 head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f`, COMMENT review `5202241729`: `ACCEPT`, residual B1 `CLOSED`, no B2–B6 regression. Prior implementation review `5203396570` applies only to head `42803dfc2baa5e5a26b152557e0c7e0d8c9504aa` and returned `ACCEPT_WITH_CHANGES`, with current-document status contradiction as the blocking finding and mechanical execution explicitly NOT_MEASURED.

Subsequent author repair includes `fbfeb76e3ed5736ec95268e3ede9acd0dad59d44`, which fixes the explicit-null/missing-key roster distinction and adds `tests/test_adr018_roster_validation.py`, followed by author-side current-document reconciliation. These are author changes, not independent closure.

Do not enqueue this request through central review intake until the coordinator has established an independent reviewer-only launch context. A scheduled task identity or self-attestation alone is not proof of independence.

## Required reads

Follow repository progressive disclosure and architecture-change rules. At minimum read:

- `CLAUDE.md` architecture-document rules and `.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md`;
- accepted ADR-018 and parent design/plan plus B1 addendum/spec/plan supplements;
- `docs/audits/2026-09-14-adr018-chat-client/REVIEW-STATUS.md`;
- prior implementation COMMENT review `5203396570`;
- `docs/audits/2026-09-14-adr018-chat-client/POST-AUDIT-REPAIR.md` and document-reconciliation status;
- `papers/AutomatedReviews/2026-09-14-adr018-roster-null/ADR018.md`;
- actual changed implementation surfaces, especially `scripts/lean_slots/state.py`, the existing ADR-018 tests, and `tests/test_adr018_roster_validation.py`;
- current PR #76 complete changed-file set.

Treat PR prose and author status records as routing/evidence claims, not proof. Do not use author-private transcript/reasoning as review authority.

## R1 — prior implementation-review B1: current-document truth

Attempt to falsify that the current normative/status surfaces now express one consistent state:

- specification ACCEPT at exact head `469e4e47607b7d74da0b9b3c81dc56d04c3dd24f` / COMMENT `5202241729`;
- author implementation in progress on PR #76;
- historical review verdicts stay tied to their exact heads;
- mechanical verification is not promoted from authored tests/source inspection;
- fresh exact-head independent implementation re-review is still required;
- Gate A and all source-mutation/build/absorb/merge/publication authority remain separate and pending.

Inspect the whole current ADR, both specs, both plans, B1 addendum, audit status and audit README. In particular look for deeper present-tense statements that still say implementation is forbidden pending the already-completed specification review. Preserve historical quotations/requests as historical evidence rather than demanding they be rewritten.

Confirm canonical removal ordering remains exactly ADR D8 / spec S18-9: quiesce acquire/credential-producing callers and leases; removal preflight; bearer `session revoke-token` while still admitted; roster edit; restart; doctor + controller/proxy denial verification. Documentation repair must not rewrite the accepted mechanism.

## R2 — explicit-null roster repair

The original failure was semantic, not cosmetic: schema-1 compatibility is allowed only when `server.allowed_clients` is **absent**. At the prior implementation head, `server.get("allowed_clients")` made an absent key and explicit JSON `null` both produce `None`, so a present malformed roster could silently restore the legacy Codex/Claude admission pair.

Inspect the current `Inventory.allowed_clients` implementation and prove by source reasoning that compatibility is selected by key absence and that **every present value** reaches roster validation. Challenge at least these neighboring present values:

- JSON `null`;
- `false` / `true`;
- numeric `0` and `1`;
- empty and nonempty strings;
- object `{}`;
- empty array `[]`;
- arrays with duplicate, non-string or unsafe-name entries through the existing validation path.

Positive controls must include:

- absent schema-1 key → exactly immutable `{codex, claude}`, never Chat;
- explicit narrow roster such as `["chat"]` → exactly that roster, with legacy clients not silently restored;
- valid public roster `["codex", "claude", "chat"]` → immutable validated set.

Review the artifact-seeded regression test itself, not only the helper predicate. `tests/test_adr018_roster_validation.py` writes disposable inventory JSON and calls real `Inventory.load`; its parametrized malformed-value tests run under both `trusted-local` and `bearer` modes. Confirm the test would fail against the original `value is None` behavior and that the positive controls prevent an overcorrection that simply rejects all legacy/missing inventories.

Do not infer test execution from test source. Authored tests are design evidence until exact-head mechanical execution exists.

## R3 — authority and regression boundary

Confirm the null repair did **not** add or broaden runtime authority:

- no second admission roster or lifecycle mechanism;
- no client-specific privilege difference;
- no hidden roster re-check in already-issued lifecycle cleanup;
- no new token path, renderer, build, repair, push, absorb, merge or publication capability;
- missing-key legacy compatibility and explicit public admission remain the accepted S18-8/D9 mechanism;
- D8/S18-9 removal ordering and owner cleanup remain unchanged.

Re-sweep the prior implementation review's non-blocking claims where the changed files can affect them. If a prior favorable observation no longer holds, report it; do not inherit it.

## R4 — mechanical evidence boundary

Resolve mechanical evidence for the **exact reviewed head** separately from source inspection.

At author reconciliation time, `.github/workflows/` was absent and an exact-head Actions query returned no runs; this means NOT_MEASURED, not PASS and not proof that every possible external runner is absent. If a naturally triggered hosted check later exists on the reviewed head, inspect its exact SHA, command/scope and conclusion. Otherwise keep relevant tests/document checks NOT_MEASURED.

The project-owned finding names this native verification command:

```text
uv run python -m pytest tests/test_adr018_roster_validation.py tests/test_adr018_chat_client.py -q
```

The author feasibility record also identifies narrower parser and documentation checks. Do not execute local/project code as part of this read-only review unless the project creates a separately authorized mechanical surface; do not convert a proposed command into executed evidence.

## Required result

File a GitHub **COMMENT** review on PR #76 only after independently resolving the current head/base and completing the read-only source/evidence review. Do not APPROVE or REQUEST_CHANGES. Include:

1. exact repo/PR/head/base;
2. independence statement and any context-isolation limitation;
3. verdict exactly `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT`;
4. disposition of prior implementation-review B1 current-document contradiction;
5. disposition of the explicit-null repair, including original failure, neighboring malformed values and positive controls;
6. whether the new test is non-vacuous against the production parser seam;
7. authority/regression sweep;
8. exact mechanical evidence actually observed versus NOT_MEASURED items;
9. remaining gates and limitations.

`authorization_effect = none`. A favorable COMMENT is review evidence only. It does not itself close the roster-null finding, authorize Gate A, attach an executor, authorize live slot/Lean use, authorize source mutation/build/absorb, merge the PR, or publish anything.
