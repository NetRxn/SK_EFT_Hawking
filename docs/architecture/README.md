# Architecture — the index

**Every document in this directory is LIVING.** None is a dated snapshot, none carries a
"as of" figure, and none states a count. If you find any of those three here, it is a
defect — fix it rather than working around it.

---

## Which document answers which question

| your question | document |
|---|---|
| **Before building anything: what already covers this surface?** | **BOTH layers, always** — [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) for checks and gates, **and** [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) §3 plus the [reviewer-agent roster](../../.claude/plugins/skeft-qa/README.md) for what an agent already reviews |
| **How many** of anything — checks, gates, hooks, agents, commands, node/edge types, registries, bundles | [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md) |
| How does work get from a roadmap to a signed-off publication? | [`END_TO_END_MAP.md`](END_TO_END_MAP.md) |
| How is the validation suite **built** — modules, contracts, hazards, the memo | [`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md) |
| **When** does each gate run, what does it block, and what does each gate actually compute? | [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) |
| I am writing a new check — what do I owe? | [`CHECK_AUTHORING_GUIDE.md`](CHECK_AUTHORING_GUIDE.md) |
| Which derived artifact has which writer and staleness key? How does a review finding become a gate? Where does a human actually decide? | [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) |
| What are we publishing, what state is it in, and what is outstanding? | [`PUBLICATION_PORTFOLIO_MAP.md`](PUBLICATION_PORTFOLIO_MAP.md) |
| What does the operator control surface show, which of its actions persist, and where does it read each panel from? | [`DASHBOARD.md`](DASHBOARD.md) |
| Which cited sources do we actually **hold**, at what fidelity, and what may a claim rest on? | [`../adrs/ADR-014-source-acquisition-and-citation-fidelity.md`](../adrs/ADR-014-source-acquisition-and-citation-fidelity.md) (normative) + [`../SOURCE_ACQUISITION_REGISTER.md`](../SOURCE_ACQUISITION_REGISTER.md) (derived). Where a loop may **fetch** from, and what enforces it, is the hook layer — [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) §1.5. ⚠️ **This row was missing until 2026-08-15, and its absence had the cost the row below predicts.** With no document owning *do we hold this source*, the check that walks the population measured file-presence instead of fidelity — an `abstract.txt` counted as a held source — and the repair was written into a **manuscript** as four disclosures that we cite what we have not read. A fix with nowhere to be specified goes into the artifact it was found in. |
| How do the parallel Lean **slots** work — leases, endpoints, the proxy, what an agent may drive unattended? | [`../adrs/ADR-008-shared-lean-slot-control-plane.md`](../adrs/ADR-008-shared-lean-slot-control-plane.md) (normative) + [`../dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`](../dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md) (operator's copy). ⚠️ **This row was missing until 2026-08-15, and its absence had a cost:** with no architecture document owning the surface, ADR-008 became the de-facto home for operator rules, and **twice** a defect in our own front door was written up there as a constraint for operators to obey rather than fixed — the `503`-on-`initialize` regression (S-N) and the session-ordering rule (S-P, retired by S-Q). A surface with no owning document accumulates workarounds, because there is nowhere for the fix to be specified. |

⚠️ **`D` is overloaded across this project — always qualify it.** Five namespaces share the
prefix: publication bundles (`D1`–`D12`), ADR-010's decisions (`§D1`–`§D7`, `§D5a`), ADR-009's
(`D1`–`D5`), the operator decisions in the 2026-08-01 audit's `SYNTHESIS.md` §5 (`D-1`–`D-6`), and
the `D`-prefixed items in
[`.working-docs/ARCHITECTURE_TODOs.MD`](.working-docs/ARCHITECTURE_TODOs.MD).
Write `ADR-010 §D5a`, `ADR-009 D2`, `SYNTHESIS D-1`, `TODO-D5`; reserve a bare `D6`
for the bundle.

The TODO list is numbered sequentially and has now grown past the bundle roster's lowest
numbers, so **some TODO identifiers collide outright with bundle names** — `TODO-D11` is a
citation defect *in* bundle D11, and `TODO-D10` is about a hand-listed module roster, not
about bundle D10. The `TODO-` prefix is the only thing separating them; never drop it.

## What is deliberately NOT here

These documents describe **mechanisms** — a check, a gate, a writer, an edge type, an operator
surface — and each one answers exactly one question from the table above. Three neighbouring
questions they do not answer, and where each is answered instead:

| your question | not here — go to |
|---|---|
| **What does this module do?** What is `<some>.py`/`.sh`/`.ipynb`, what is the per-Lean-family map | [`../MODULE_CENSUS.md`](../MODULE_CENSUS.md) for Python, shell and notebooks (derived — docstring, leading comment block, or opening markdown cell, per language); `docs/counts.json` `lean.module_names` and `lean/atlas_view.json` for Lean |
| **What must I do, in what order?** The 14 stages, the invariants | [`../WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md) — and why each rule exists, [`../WAVE_PIPELINE_RATIONALE.md`](../WAVE_PIPELINE_RATIONALE.md) |
| **How do I run an architecture change?** The orient → measure → specify → review → pilot → plan → ship → terminate sequence | the `architecture-change` skill, which owns the *sequence* and deliberately restates none of the *rules* below |

⚠️ **A module's absence from this directory is therefore expected, not a defect** — the test is
whether a module implements a mechanism one of these documents owns. Counting filename absences
here measures a shortfall against a contract nobody wrote.

⚠️ **The Inventory pair is RETIRED (ADR-013 D7/D8, 2026-08-13).** Both files are deleted and
`inventory_index_autogen_fresh` with them; [`../MODULE_CENSUS.md`](../MODULE_CENSUS.md) answers
*what is this module* for Python, shell and notebooks, wholly derived. This paragraph used to
end *"Read it for pointers; verify anything it asserts"* — advice pointing at two files that no
longer exist.

⚠️ **AND IT SURVIVED THE RETIREMENT, WHICH IS THE INSTRUCTIVE PART.** It names the pair and its
gate in **prose**, never as a path, so `doc_refs_resolve` — the one mechanical guard on
rot-by-deletion, described three paragraphs below — could not see it: that leg matches
*path-like* references. The retirement's own hand-grep missed it too, because that sweep looked
for *routing rows* and this is a caveat. **A deletion is only as visible as the shape the prose
used to name the thing.**

Decisions live in [`../adrs/`](../adrs/); the graph schema in
[`../KNOWLEDGE_GRAPH.md`](../KNOWLEDGE_GRAPH.md); the process law in
[`../WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md), whose *why* — the incident
behind each rule — is split into [`../WAVE_PIPELINE_RATIONALE.md`](../WAVE_PIPELINE_RATIONALE.md)
so the law reads as a law. **Change a rule and the rationale entry changes with it**: a rule
whose stated reason no longer holds is the next rule somebody relitigates.

## The two rules

### 1. Counts live in exactly one file, and it is derived

`SURFACE_INVENTORY.md` is generated by `scripts/architecture_inventory.py` and gated by
`validate.py --check architecture_inventory_fresh`. **No other document in this directory
may state a count** — link to the census instead.

That check enforces three things, and the third is the only mechanical guard on doc
*accuracy* that exists:

1. the census matches a fresh derivation;
2. no narrative states a census count;
3. **every path-like reference in a narrative resolves to a file that exists.** It cannot
   check whether a description is *true*, but it catches the way these documents actually
   rot — a rename or a deletion the prose never followed. Deliberate absences (a document
   naming a file precisely to say it is missing) live in an explicit, reasoned exception set
   in the check.

⚠️ **AND NO CHECK NOTICES A SUBSYSTEM THAT IS SIMPLY ABSENT FROM THESE DOCUMENTS.** The
census covers checks, gates, graph types, hooks, agents, commands, registries and bundles —
**not modules.** Measured 2026-08-13: five modules implementing operator surfaces this
directory owns had landed with **zero** mentions here, and every gate was green over all of
them. The checks verify what *is* written; nothing asks what *should have been*. That is this
project's own defect class — absence rendered as success — sitting one level above the
documents that name it.

⚠️ **Nor does any check parse markdown STRUCTURE.** A prose paragraph inserted between two
rows of a table splits it in two and turns every row below into literal pipe-delimited text;
the census, the counts leg, the answers-contract and the path-resolution leg all stay green,
and the diff shows only added lines. Measured the same day, in
[`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) §6, where it destroyed five rows
of the field-ownership table — including the row the paragraph beneath it was about.

⚠️ **"Absent from these documents" is not the same as "undocumented", and conflating them
produces a number that measures nothing.** A module belongs *here* when it implements a
mechanism one of these documents owns — a check, a gate, an artifact writer, an operator
surface. The per-module inventory of `scripts/` and `src/` is
[`../MODULE_CENSUS.md`](../MODULE_CENSUS.md)'s question, not this
directory's; a filename's absence from a narrative that names *mechanisms* is expected, and
counting those absences yields a shortfall against a contract nobody wrote. Ask whether every
mechanism is described and whether each description is **true** — the second is the one with
no mechanical guard at all.

Rule 2 is therefore the only guard on new-surface coverage, and it is discipline rather than
a mechanism. When a change adds a module, a writer, or an operator-facing surface, the
document that owns that surface gains it **in the same commit**, and a green suite is not
evidence that this happened.

⚠️ **No check verifies a prose claim** — a description can be fluent, well-cited, and wrong,
and the suite stays green. That is why rule 2 exists, and why the load-bearing claims are
additionally pinned by executable assertions in
[`tests/test_architecture_claims.py`](../../tests/test_architecture_claims.py).

**Those assertions bind in both directions, which is the whole design.** Each one asserts (a)
that its claim's sentence is still present in the document, verbatim, and (b) the code fact
that makes it true. Reword the claim and the test fails, forcing re-verification; change the
code and the test fails, forcing the document to follow. A one-way assertion rots the moment
somebody rephrases the sentence, which is the failure mode these documents are most prone to:
a claim is true when written, and nothing re-reads it afterwards.

Coverage there is deliberately partial — the claims a reader would *act on*, not every
sentence. Adding one is cheap; choosing which is the work.

This is not tidiness. Chasing counts across narrative documents is the lowest-value work
this repository does, it recurs every time anything is added, and it has repeatedly
produced documents that contradict themselves *and each other* while reading as
authoritative. Removing the counts removes the chase.

Rule of thumb: if a sentence would need editing because a number changed, the sentence
belongs in the census or should name a *mechanism* instead of a *magnitude*.

### 2. Design is written here first

A design change lands in these documents **before** the code that implements it, and
these documents are read **before** new design work starts. A doc written afterwards is
a changelog; a doc written first is a specification, and only the second kind prevents
the next contradiction.

## Scope boundary — why there are two maps

`END_TO_END_MAP` is the **spine**: the path work travels, and where that path is broken.
`QA_QI_INFRASTRUCTURE_MAP` is the **quality layer's interior**: per-artifact writers and
staleness keys, the review-finding pipeline and its silent drops, the human decision
points, and the claim-lineage detector — subsystems the spine references but does not
open up.

They overlap by design at exactly one point: the spine names a defect, the interior
explains the machinery it lives in. Neither restates the other's tables.
