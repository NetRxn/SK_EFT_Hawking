# Finding-closure lifecycle — design

**Date:** 2026-08-12
**Status:** spec, pending implementation plan
**Implements:** ADR-012 D6, and the gap ADR-012 did not cover — the ledger's **write** side
**Supersedes nothing.** Extends existing mechanisms; adds one script and one check.

---

## Why this exists

`docs/review_finding_supersessions.json` is the only channel that can close a blocking
`ReviewFinding`. It has **no writer**. All 870 records were hand-typed into a 645 KB JSON file,
and it shows: **256 of them (29%) carry a `finding_id` that matches no minted node**, so they are
inert — the findings they meant to close still read `open`.

ADR-012 was drafted, piloted against 117 open critical findings, and amended, and it still missed
this. The pilot found the *consequences* (98 findings fixed but never recorded, a false closure, two
malformed keys) without naming the *cause*. The cause is that closing a finding requires
hand-constructing a key with no feedback when you get it wrong. Nobody skips a script; people skip a
hand-edit, and when they do not skip it, 29% of the time it silently does nothing.

### Original intent, from git

Introduced 2026-04-28 (`dc4f6ba8`), by "Phase 6i Wave 2 Stage 13 Finding 11.1 +
qi-fixpropagation-tracking QI candidate". The original schema made `superseded_by` central: it named
**the re-review that confirmed the fix**, matching Stage 13's rule that "the re-run is evidence".
Every record in the first commit carried one.

That intent eroded. Closure now happens without a re-review, which is how both the unrecorded fixes
and the false closure arose. **Operator decision (2026-08-12): do not restore the re-review
requirement.** A re-review per closure is disproportionate for the trivially-verifiable majority.
The replacement obligation is a `verify` command that names its invariant — cheaper, machine-checked,
and it catches the "recorded fixed, still live" class that a re-review would also catch.

### Deviations from the architecture docs, with evidence

| # | deviation | evidence |
|---|---|---|
| 1 | No writer tool was ever built or planned | no commit on any branch adds a script that writes the ledger; `record_review.py` writes `bundle_metadata`, not this |
| 2 | 29% orphan rate | 256 of 870 `finding_id`s resolve to no node minted by `extract_review_finding_nodes` |
| 3 | Id scheme forked 2026-05-01 (`ed4aef04`) | live census: `review:` 680, `bundle-stage13:` 150, `bundle-stage10:` 29, `bundle-stage9:` 8, `policy_`/`session_` 3. 190 use conventions the minter never produced |
| 4 | Records attempt to close several findings at once | `…:D5:5.1+5.2+5.3`, `…:I2:5.1-5.3` — syntax the schema cannot express, so they close nothing |
| 5 | `_entry_format` disagrees with its only reader | declares `date`; `build_graph` accepts `commit`/`date`/`closed_date`/`applied_at` |
| 6 | The architecture documents only the read side | `QA_QI_INFRASTRUCTURE_MAP.md:195` shows the ledger as an append-only input; `END_TO_END_MAP.md:43` models the writer as `HUMAN`; `READINESS_GATES.md` — the canonical gate document — never mentions the ledger at all |

⚠️ Deviation 6 is not a documentation lapse to correct in passing. `END_TO_END_MAP.md` is *accurate
today*: a human does write it, by hand. The doc is right and the system is wrong.

---

## Architecture

Three participants, one new.

| participant | role | change |
|---|---|---|
| `build_graph.extract_review_finding_nodes` | mints ids, reads the ledger, applies the closure bar | two edits (ADR-012 D6) |
| `docs/review_finding_supersessions.json` | the ledger | schema amended |
| **`scripts/close_finding.py`** | the only supported writer | new |

**Load-bearing constraint: `close_finding.py` imports the id-minting function from `build_graph`;
it does not reimplement it.** This repo has already paid for that lesson — `_recurrence_norm` was
moved to module scope so its test binds the real matcher, after a period when the production matcher
could have been deleted or inverted with the test still green. A second minter would reproduce
deviation 2 by construction. The minting logic is extracted to a named function and imported by
both.

---

## Components

### `scripts/close_finding.py`

```
--doc PATH            review document containing the finding
--section N.N [N.N …] one or more section numbers
--status              fixed | accepted | reopened
--evidence TEXT       what was done, where, when
--commit SHA          }  at least one anchor required
--date ISO            }
--verify CMD          optional; run before writing, must exit 0
--superseded-by ID    optional; the re-review that confirmed it
```

**Refuses to write** when:

1. the minted id matches no live node — kills deviation 2 at the source
2. `evidence` is under the bar for a blocking severity
3. no anchor is supplied
4. a `--verify` command is supplied and exits non-zero

**Multiple sections write one record each, sharing the evidence string.** This meets the need that
produced `5.1+5.2+5.3` without breaking the one-id-per-record invariant the reader depends on
(deviation 4). Writing is idempotent: the same id and status twice is a no-op, not a duplicate.

### Schema amendment

`_entry_format` gains the anchors the reader actually accepts (deviation 5), and one new field:

```
verified_by: {command: string, exit_code: int, run_at: ISO-8601} | null
```

`superseded_by` remains optional.

### `build_graph` edits (ADR-012 D6)

1. **Remove the severity scoping from the closure bar.** It is currently gated on
   `severity in ('critical','major','blocker')`; below that line any two-key record closes a
   finding. This is a filed finding, open across four consecutive rounds, and it reproduced
   byte-for-byte at HEAD during the ADR-012 pilot.
2. **Require `verified_by`** for closures of findings that carry a `verify` command.

### New check: `ledger_finding_ids_resolve`

Reports the count of ledger records whose `finding_id` resolves to no node, and ratchets it
**downward only**. Current value 256; 247 after re-keying the nine mechanically re-keyable records.
Makes 29% of a safety mechanism doing nothing *visible* rather than silent.

It follows `CHECK_AUTHORING_GUIDE.md` rather than amending it, and per ADR-012 D8 ships with a
seeded-defect test: a record with a deliberately broken id must turn the check red.

---

## Data flow

```
reviewer emits review doc
  → extract_review_finding_nodes mints one node per finding
  → remediation happens
  → close_finding.py  ── mints the same id, runs --verify, appends ──> ledger
  → next graph build applies the override through the closure bar
  → readiness_submission_gate reflects it
```

---

## Error handling

- **Unresolvable id** — refuse, and print the ids that *do* exist for that document, so the caller
  sees the real section numbers instead of guessing. This is the difference between a tool that
  prevents deviation 2 and one that merely complains about it.
- **`--verify` fails** — refuse, print the command's output.
- **Unreadable or malformed ledger** — fail closed. An absent ledger is not a licence to write one.
- **Concurrent writes** — re-read immediately before appending.

---

## Testing

Per ADR-012 D8, every refusal path ships with a seeded-defect test that observes red. Two matter
more than the rest:

- **the minter is shared, not copied** — a test that binds the real `build_graph` function, so a
  future divergence fails rather than silently re-creating the orphan class
- **round-trip** — write a record, rebuild nodes, assert the status actually flipped. Without this,
  every other test could pass while the ledger change reaches nothing.

---

## Architecture documents updated in this change

Per architecture rule 2, these land **with** the code, not after it.

| document | why it goes stale | change |
|---|---|---|
| `docs/READINESS_GATES.md` | canonical gate doc; **zero** mentions of the ledger today, so a reader cannot learn how a gate un-blocks | add the closure contract: open-by-default, the ledger as sole transition channel, the bar's requirements (ADR-012 D3) |
| `docs/architecture/END_TO_END_MAP.md` | line 43 models the writer as `HUMAN` — accurate today, wrong after this | route the edge through `close_finding.py` |
| `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` | line 195 shows the ledger as an append-only input with no writer named | name the writer; note the orphan class and its check |
| `docs/WAVE_EXECUTION_PIPELINE.md` | §13 describes emission and re-invocation but not how a closure is written | add the closure step, cross-referencing `READINESS_GATES.md` rather than restating it |
| `docs/KNOWLEDGE_GRAPH.md` | line 167 documents `SUPERSEDES` as unimplemented because supersession is ledger-based — still true, but silent on the writer | note the writer alongside the existing entry |
| `docs/architecture/SURFACE_INVENTORY.md` | derived | regenerate — picks up the new check and script automatically |
| `docs/adrs/ADR-012-…md` | D6 is specified here in more detail than the ADR carries | add a pointer to this spec; record that the write-side gap was found after the ADR's own pilot |

**Verified as not needing changes:** `docs/architecture/CHECK_AUTHORING_GUIDE.md` (the new check
follows it; the guide does not change), `docs/architecture/README.md` and
`VALIDATION_GATE_TOPOLOGY.md` (no ledger claims; the new check's topology row, if the format
requires one, is a mechanical addition to be confirmed during implementation rather than asserted
here).

---

## Sequencing

1. Re-key the nine mechanically re-keyable records
2. Add `ledger_finding_ids_resolve` at its measured value
3. Fix the closure bar (D6.1) — remove severity scoping
4. Ship `close_finding.py` + schema amendment + doc updates
5. **Then** write the 98 pending closures from the ADR-012 pilot through the tool

Step 5 is last on purpose. Closing a backlog through a bar that can still be walked around would
bake the defect into 98 records.

---

## Out of scope

- Migrating the 187 bundle-era and 57 unmatchable orphans. They become tracked, ratcheted debt.
  Operator decision 2026-08-12: re-key the nine, ratchet the rest.
- The `/skeft-qa:close-finding` plugin command. Agreed as a later thin wrapper over this script; the
  script is the contract, the command is ergonomics.
- Any change to what reviewers look for, or to finding routing (ADR-012 D1/D2).
