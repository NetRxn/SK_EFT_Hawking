# ADR-018 — distinct Chat client for shared Lean slots: implementation plan

**Status:** proposed plan only. **Blocked on independent adversarial specification review.**

**Design:** [`2026-09-14-adr018-chat-slot-client-design.md`](../specs/2026-09-14-adr018-chat-slot-client-design.md)

**ADR:** [`ADR-018`](../../adrs/ADR-018-chat-client-for-shared-lean-slots.md)

**Measured base:** `codex/memory-process-clocks` @ `9ea7b61a33e91190ffe99e843247e03a51e8fb3e`.

## Global constraints

- ADR-008 remains the slot lifecycle/build/integration authority.
- No code implementation begins until independent adversarial review accepts the ADR/spec/plan or all blocking changes are reconciled.
- Do not add a second slot/worktree/backend/proxy/integration mechanism.
- `chat` must be a distinct client identity; never impersonate `claude` or `codex`.
- Inventory owns admission. No duplicated client roster in proxy/controller/CLI.
- No worker-side `lean_build`, direct slot push, merge, publication, deployment, or automatic repair/discard.
- Preserve paired public/private dependency invariants.
- Live no-mutation acceptance precedes any source-mutating Chat task.

## Phase 0 — independent design review

### Task 0.1 — fresh-reader adversarial review

Reviewer reads, at minimum:

- `CLAUDE.md`;
- `.claude/plugins/skeft-qa/skills/architecture-change/SKILL.md`;
- `docs/architecture/README.md`;
- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`;
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`;
- issue #74;
- ADR-018;
- ADR-018 design spec;
- this plan;
- measured implementation surfaces in `config/lean-slots.public.json` and `scripts/lean_slots/{state,controller,proxy,cli}.py`;
- relevant existing slot tests.

Required output:

- blocking findings;
- non-blocking findings;
- unknowns / measurements required;
- conflicts with existing architecture/process;
- missing non-vacuity tests;
- explicit `ACCEPT`, `ACCEPT_WITH_CHANGES`, or `REJECT` verdict.

No implementation proceeds on `REJECT` or unresolved blocking findings.

### Task 0.2 — reconcile review

For each accepted finding:

- amend ADR/spec/plan first;
- re-measure any disputed code/state claim;
- preserve stable decision numbering;
- request another independent pass if changes materially alter the design.

## Phase 1 — make admission versioned data

### Task 1.1 — inventory property and validation

**Files**

- `config/lean-slots.public.json`
- `scripts/lean_slots/state.py`
- `tests/test_lean_slots.py`

**Change**

- add `server.allowed_clients = ["codex", "claude", "chat"]` to public inventory;
- add `Inventory.allowed_clients` validation/projection;
- define safe grammar consistently with existing token-file naming;
- validate non-empty + unique;
- decide missing-field legacy behavior only after review/private compatibility assessment.

**Negative tests**

- empty;
- duplicate;
- malformed;
- missing-field behavior exactly matches the reviewed migration decision.

## Phase 2 — enforce admission at every project boundary

### Task 2.1 — controller admission

**Files**

- `scripts/lean_slots/controller.py`
- `tests/test_lean_slots.py`

**Change**

- validate client in `Controller.acquire()` before lease creation/mutation;
- validate client in `session_environment()` before token/environment behavior;
- keep generic lease record shape.

**Non-vacuity**

Programmatic unadmitted `Controller.acquire(... client="other" ...)` must fail and leave no lease artifact.

### Task 2.2 — proxy admission

**Files**

- `scripts/lean_slots/proxy.py`
- `tests/test_lean_slots.py`

**Change**

- trusted-local identification consumes `Inventory.allowed_clients`;
- bearer mode additionally rejects clients absent from current admission even if a stale token file exists.

**Tests**

- `chat` discovery under admitted inventory;
- unknown client reject;
- no lease dispatch reject;
- chat lease/chat hint pass;
- chat lease/claude hint reject;
- claude lease/chat hint reject;
- bearer hint/token mismatch reject;
- removed-client stale token reject.

### Task 2.3 — CLI delegates admission authority

**Files**

- `scripts/lean_slots/cli.py`
- `tests/test_lean_slots.py`

**Change**

- remove client-specific argparse `choices` where inventory/controller owns admission;
- preserve clear failure messages from project authority.

**Test**

CLI with `--client other` parses but fails through controller/inventory without creating state.

## Phase 3 — documentation and architecture claims

### Task 3.1 — correct every mechanism document changed by implementation

Inspect and update only where implementation makes existing prose incomplete/wrong:

- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`;
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`;
- `docs/architecture/README.md` if routing/ownership wording needs adjustment;
- architecture claim tests if a new load-bearing claim is introduced.

Do not add hand-maintained counts.

### Task 3.2 — operator guide client-neutral wording

Document that:

- admitted clients derive from versioned inventory;
- `chat` uses `LEAN_SLOT_OWNER_SESSION`;
- bridge connects directly to proxy URL with `?client=chat`;
- no Chat-specific workspace renderer is required;
- transport connection does not grant a lease.

## Phase 4 — mechanical verification

Run project-native relevant tests and checks, at minimum:

- targeted `tests/test_lean_slots.py`;
- full applicable Python test slice required by project conventions;
- architecture/document checks affected by the changed files;
- `slotctl doctor` in non-destructive/read-only mode as appropriate after implementation and proxy restart requirements are understood.

Explicitly verify the loaded proxy fingerprint cannot silently represent pre-change code after implementation changes.

No live Chat MCP dispatch yet in this phase.

## Phase 5 — independent implementation review

Separate from the specification review and separate from the implementer.

Review questions:

- is inventory genuinely the only client roster?
- can any programmatic path create an unadmitted lease?
- can stale bearer tokens retain admission?
- did existing Codex/Claude behavior drift?
- did the implementation accidentally expand worker/build/integration authority?
- are downstream/private compatibility consequences explicit rather than assumed?
- do tests mutate/drive the actual production-shaped admission paths rather than fixture-only helpers?

Blocking findings must be fixed and re-reviewed before live acceptance.

## Phase 6 — bounded no-mutation live acceptance

**Only after implementation + independent review are green.**

Use one currently clean/free slot.

1. ensure supervisor/proxy fingerprint current;
2. set one opaque `LEAN_SLOT_OWNER_SESSION` for the full lifecycle;
3. `slotctl acquire --slot N --client chat --base-ref <exact admitted ref>`;
4. `slotctl prepare --slot N`;
5. bridge calls only task-allowlisted diagnostics/`lean_verify` over proxy `?client=chat`;
6. verify worktree clean and no new commits;
7. `slotctl release --slot N`;
8. capture structured evidence.

Acceptance requires both positive and negative evidence:

- positive Chat call works under its own lease;
- same endpoint refuses a mismatched client identity;
- `lean_build` remains unavailable/denied;
- no source mutation occurred.

## Phase 7 — first source-mutating direct Chat task

Only after Phase 6 acceptance.

Bound one real Lean task with:

- exact ref/SHA;
- one slot;
- explicit owned files;
- exact Lean MCP tool allowlist;
- no worker build/push;
- fixed resource bounds;
- verification floor;
- independent review requirement.

Flow:

`acquire → prepare → read/Lean-MCP/edit loop → diagnostics → lean_verify → commit → ready`.

The existing project lead/orchestrator then owns `absorb`, authoritative build/validation, review, and integration.

## File-to-task map

| File | Phase/task |
|---|---|
| `config/lean-slots.public.json` | 1.1 |
| `scripts/lean_slots/state.py` | 1.1 |
| `scripts/lean_slots/controller.py` | 2.1 |
| `scripts/lean_slots/proxy.py` | 2.2 |
| `scripts/lean_slots/cli.py` | 2.3 |
| `tests/test_lean_slots.py` | 1.1, 2.1, 2.2, 2.3 |
| `docs/adrs/ADR-018-chat-client-for-shared-lean-slots.md` | review/reconciliation |
| `docs/superpowers/specs/2026-09-14-adr018-chat-slot-client-design.md` | review/reconciliation |
| `docs/superpowers/plans/2026-09-14-adr018-chat-slot-client.md` | this plan |
| ADR-008/operator/architecture docs | 3, only where live implementation changes current truth |

## Stop conditions

Stop and return to design/review rather than implementing around the issue if:

- review finds an existing client-admission owner we missed;
- downstream/private migration cannot be made explicit safely;
- direct Chat would require impersonating another client;
- Chat identity needs different privileges from existing workers;
- client admission cannot be enforced at the controller boundary;
- implementation requires changing slot count/lifecycle/build ownership;
- live acceptance would require repairing/quarantined state rather than using a clean admitted slot.
