# Documentation scale and read-routing — 2026-08-13

**Found by** reading all eight `docs/architecture/` documents end to end for content and
purpose, after an operator challenge to a coverage claim derived from grep rather than
from reading.

**What it is.** Two separate problems that present as one symptom — an agent greps the
documentation instead of reading it, then is surprised by machinery that already exists.

1. **Scope creep, which presents as scale.** The architecture set is right-sized and was
   not the problem: eight documents, 7–28 KB each, read end to end in two tool calls. The
   documents that go unread are an order of magnitude larger — and the most-cited of them
   (finding 1) is a six-day-old temporary working doc that quietly became a second
   remediation queue beside the one ADR-012 built. Size is the symptom; unbounded scope is
   the cause, and sharding would have entrenched it.
2. **Routing.** Four surfaces route a reader to documentation, and until this pass they
   disagreed. The Inventory Index asserted that this repo has no `CLAUDE.md` — it has a
   21 KB one that is the primary bootstrap — and named no architecture document at all.

**Repaired in the same pass, and therefore NOT part of this finding:** the Index's false
routing sentence, its missing pointer to `docs/architecture/`, `architecture/README.md`'s
missing "what is deliberately not here" section, a ~10 KB changelog pruned from the Index
header, and `inventory_index_autogen_fresh` extended with two blocking narrative legs
(size ceiling read from the file's own declared rule; hand-written counts ratcheted
down-only at 19).

⚠️ **Sharding is NOT the disposition, and assuming it was is what this document got wrong
first.** No measured defect this session was *caused* by a document being too large — the
cause was choosing a cheap proxy measurement over reading the artifact, and finding 1's real
defect is a scope boundary nobody enforced. Size is a symptom. Each finding below states its
own disposition; none of them is "shard it because it is big".

## Measured population — tracked `.md` over 100 KB

| document | size | why it matters |
|---|---:|---|
| `SK_EFT_Hawking_Inventory.md` | 319 KB | the prose module inventory `CLAUDE.md` routes to; never read whole |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | 276 KB | the accuracy record for the architecture set |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | 191 KB | **created 2026-08-07 as a temporary working doc; now a second remediation queue** — see finding 1. Size is the least of it |
| `docs/roadmaps/Phase6n_Roadmap.md` | 162 KB | phase roadmap |
| `docs/roadmaps/Phase6p_Roadmap.md` | 154 KB | phase roadmap |
| `SK_EFT_Hawking_Inventory_Index.md` | 93 KB | **now within its declared 100 KB ceiling and gated** — repaired this pass |

**Where sharding IS the answer, the pattern already exists.** `docs/dev-loops/SYSTEM2_REGISTER.md`
splits into an active register (`## Index` + Open + Process Wins) and `SYSTEM2_ARCHIVE.md`
(Closed + Misfiled, read on demand). Follow that shape rather than inventing a second one —
but establish that a document should exist at its current scope before making it easier to
keep.

---

## Findings

### 1 — 🔵 A temporary working doc became a second remediation queue

- **Severity:** minor
- **Lane:** infra
- **Location:** `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD`

⚠️ **This finding was first filed as "shard it — 191 KB is unreadable", at `major`. Both
halves were wrong, and the operator caught it.** Sharding entrenches the document as
canonical, which is the actual defect; and severity here means *blocks a bundle from
submission*, which this does not.

**The defect is scope, not size.** It was created **2026-08-07** — six days before this
finding — as a temporary working doc with limited scope. Measured today:

| | |
|---|---|
| size / commits / D-numbered items | 191 KB · 105 commits · 51 items |
| cited **by identifier** from canonical docs | `architecture/README.md` (`TODO-D5`, `TODO-D10`, `TODO-D11`) · `VALIDATION_GATE_TOPOLOGY.md` and `END_TO_END_MAP.md` (`TODO-D8`) · `tests/test_architecture_claims.py` (`B2`) |
| cited from production code | `scripts/extract_lean_deps.py` · `scripts/sync.py` · two `validation/checks/` modules · `src/core/visualizations.py` |
| cited from a **manuscript** | `papers/I1/paper_draft.tex:880` — *"RESOLVED 2026-08-11 (ARCHITECTURE_TODOs D49)"* |
| tracked files naming it | 46 |

**And ADR-012 built the mechanism that owns this job.** The finding queue holds **62 open
`infra`-lane findings** today, each with a declared severity, lane and verify, routed and
ratcheted and closable through a single writer. The working doc is the pre-queue mechanism
still standing beside it — *"building a second mechanism beside one that already exists"*,
which is `architecture/README.md` rule 1's own example, inside the directory that names it.

⚠️ **The `D` namespace collision the README already warns about is a symptom of this.**
`TODO-D11` is a citation defect *in* bundle D11; `TODO-D10` is about a module roster, not
bundle D10. A scratch file's numbering was never meant to share a namespace with the
publication roster, and it does because it outgrew its scope.

**Verify:** `CLAUDE.md` routes new remediation items to the finding queue and states that
this file takes no new entries *(done 2026-08-13)*; then its open items are re-filed as
findings and its closed items become history. **Do not renumber** — the `TODO-D*`
identifiers are cited from four canonical documents, seven source files and a manuscript,
so the file stays readable at its current identifiers until every citation is retired.

### 2 — 🔵 `SK_EFT_Hawking_Inventory.md` has no index into it

- **Severity:** minor
- **Lane:** infra
- **Location:** `SK_EFT_Hawking_Inventory.md`


The Index is the pointer layer *for* this document, but it points at the file, not into it.
A reader who needs one module's entry loads 319 KB or greps. The Index's own contract
("pointers only — `file path + one-line summary`") is the right shape; what is missing is
per-section anchors so a pointer can land somewhere specific.

**Verify:** an Index entry resolves to a section anchor in the prose inventory, not merely
to the filename.

### 3 — 🔵 `ACCURACY_LEDGER.md` has no stated read path

- **Severity:** minor
- **Lane:** infra
- **Location:** `docs/architecture/.working-docs/ACCURACY_LEDGER.md`


Neither `CLAUDE.md` nor `architecture/README.md` says when to read it or what question it
answers — unlike the eight architecture documents, each of which declares its question in a
machine-compared `> **Answers:**` line. A 276 KB document with no declared question is read
by nobody and cited by anybody.

**Verify:** it either gains a declared question and a route, or is explicitly marked as an
append-only record not meant for reading, which is also a valid answer.

### 4 — 🔵 No mechanism gates documentation SIZE outside the Index

- **Severity:** minor
- **Lane:** infra
- **Location:** `scripts/validation/checks/freshness.py`


`inventory_index_autogen_fresh` now enforces the size ceiling the Index declares for
itself, by reading that ceiling out of the file. Nothing generalises this: any other
document may grow past the point of being readable, silently, and the first symptom is an
agent grepping it.

**Verify:** a document that declares a size ceiling has it enforced; the mechanism is the
one already written for the Index, generalised rather than duplicated.

---

## Not filed, and why

**The architecture set itself needs no sharding.** Eight documents, 7–28 KB, one declared
question each, machine-pinned so the ownership assignment cannot drift. It is the model the
rest of the corpus should move toward, not a target for change.

**The `docs/roadmaps/` files above 100 KB are out of scope here.** They are append-only
phase records, read by phase rather than by question, and no infrastructure change routes
through them. They appear in the population table for completeness, not as work.
