# Publication portfolio — what we are publishing, its state, and which sources are safe

> **Answers:** What are we publishing, what state is it in, and what is outstanding?
>
> *(TODO-D8: this line is the required-content contract. `README.md`'s ownership
> table assigns this question to this document; `architecture_inventory_fresh`
> asserts the two agree verbatim, so the assignment cannot drift silently.)*

**Living document.** Start at [`README.md`](README.md). States no counts — the bundle roster is in
[`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md).

The other documents here map the **machinery**. This one maps the **thing the machinery serves** —
the manuscripts — and, because much of the surrounding process documentation predates the current
model, **which documents can be read as truth and which cannot**.

**Companions:** [`END_TO_END_MAP.md`](END_TO_END_MAP.md) §7–§8 (authoring, review, and the promotion
path) · [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) §4 (what each readiness gate
computes) · [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) §5 (claim lineage).

---

## 1. The model changed, and most process documents describe the old one

**This is the fact that makes older documents misleading rather than merely stale.**

**The superseded model — a bundle's substrate is its source papers.** A phase produced a per-paper
draft; a row in `PAPER_DRAFT_MAPPING.md` routed it to a bundle section; `source_manifest.md`
recorded the lift; freshness was the **mtime** of the source directory against `last_lift`. The
absorption protocol, the lift procedure and the strategy document are all written to this model.

**Why it broke.** Later phases produce Lean modules and working-docs syntheses with **no per-paper
draft** — the sourceless pattern. Their mapping rows carry synthetic tokens (`D9_initial_draft`,
`_phase6t_lean_only`) naming no directory, so there is nothing to mtime-compare. The freshness
trigger is structurally dead for every bundle authorized from D6 onward, and a large fraction of
source assignments portfolio-wide name a directory that does not exist. Those bundles now report
`UNMEASURABLE` rather than a fabricated `fresh`, so the gap is visible — but not closed.

**The current model — a bundle declares what it claims, and its substrate is derived.** Under
ADR-010 §D5a a bundle declares `apex_theorems` in `bundle_metadata.json`: the results its abstract
already asserts in prose. Everything else follows — the substrate is the **derived closure** of
those apexes, and freshness is a **content hash** of that closure rather than a source mtime. The
apex list is bundle-local so a merge concatenates and a split partitions; the closure is a graph
**overlay** annotating `meta`, never materialised edges, because emitting them would roughly double
the graph.

Design and measurements:
[`.working-docs/PUBLICATION_INTAKE_DESIGN.md`](.working-docs/PUBLICATION_INTAKE_DESIGN.md) (the
*what*) · [`.working-docs/PUBLICATION_INTAKE_SHAPE.md`](.working-docs/PUBLICATION_INTAKE_SHAPE.md)
(the *how*, the retrofit method and the queue).

⚠️ **Read every process document against this transition.** A statement about source manifests,
mapping rows or mtime freshness describes machinery being replaced. It is not wrong about history,
and it is not a description of how a phase-sourced bundle works now.

## 2. Which sources are safe

`CROSS-absorbability-and-strategy-drift.md` §1 in the audit below carries a per-document drift
ledger with file-and-line evidence. Its consequence for a reader:

| document | status |
|---|---|
| `PAPER_STRATEGY.md` | **charters and roster are current; the STATE claims are not.** Its readiness assertions, its ready-to-ship list and its sequencing section are contradicted by the live heatmap, and the sequencing section never gained the later-authorized targets. Use it for *what a bundle is for*, never for *what state it is in*. |
| `LATE_PHASE6_ABSORPTION_PROTOCOL.md` | **stages and branch index are sound; its roster arithmetic is not.** The branch index was repaired under ADR-011 Phase 6 — the stage table and the decision table now both carry every branch, including D.0 (unsound target: home the work, do not absorb) and the sourceless D.4 that modern phases use. The Stage-B authorization gate still counts bundles instead of naming the registry that owns them, so its arithmetic is a roster many targets out of date. |
| `BUNDLE_LIFT_PROCEDURE.md` | **workflow is current and in use.** Its tier profiles name only the earliest Tier-1 and Tier-3 members, so later bundles have no defined review profile; its source-readiness pre-condition is documented and unenforced. |
| `RESEARCH_STATUS_OVERVIEW.md` | ⛔ **do not orient from it.** Several Tier-1 bundles are absent entirely and its portfolio verdict inverts the live one. |
| `ARXIV_DEPOSIT_PLAN.md` | ⛔ several Tier-1 bundles have **no deposit path** in it at all. |
| `PAPER_TABLES_STATUS.md` | ⛔ covers the per-paper drafts only. **No publication bundle is wired to the table pipeline.** |
| `bundle_metadata.json` statuses | ⛔ pre-date the current infrastructure and are not evidence — §3. |

**Authoritative instead:** this directory for the machinery · `SURFACE_INVENTORY.md` for any count ·
the audit below for portfolio state · ADR-010 for the reassessment's constraints and open items ·
`PUBLICATION_INTAKE_SHAPE.md` for the intake model and retrofit progress ·
[`../audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md`](../audits/2026-08-08-adr010-d4-adjudication/ADJUDICATION.md)
for the merge/split/retire decision on every proposed change, argued from the manuscripts.

⚠️ **Read the adjudication before quoting a closure intersection at a merge question.** The two
pairs it examines fail in opposite directions and the intersection number gives the wrong answer for
both: D6+D9 share **zero** declarations and one holds 44 % of the other's paper; D4+D8 share **280**
and are cleanly divided by an explicit cession in D8's own text. Closure measures shared
*substrate*; a merge turns on shared *claims*, which only the drafts carry.

⚠️ **The drift ledger is itself a 2026-08-01 snapshot, and it has drifted.** Verified item by item
2026-08-07: **three closed** (all in the process law — the roster enum and the check count now name
their owning artifact instead of copying a value), **most still open**, one unverifiable because the
assertion it quotes does not appear in the file it names.

**More importantly, several items' *correcting evidence* is now itself wrong**, so an item can be
open while the reason given for it is stale:

- its "five different check counts" tally is down to two, and the live check total is not the
  number it anchors on;
- its `ls papers/*/tables.py → none` command is **false as written** (legacy per-paper drafts do
  carry one) — the substantive claim, that no *bundle* has one, survives only under an explicit
  per-bundle test;
- its citation-cache gap and draft-directory count have both moved.

**Re-derive an item before acting on it, including its evidence line.** Roughly a third of the
ledger is about a document's own count or enumeration; the rest are substantive state assertions,
dependencies or missing targets, and a few pair a wrong number with a wrong claim in one sentence —
fixing the number there leaves the claim false.

## 3. Portfolio state

**[`docs/audits/2026-08-01-publication-readiness/`](../audits/2026-08-01-publication-readiness/README.md)**
is the current assessment and supersedes any impression formed from metadata. Thirteen
fresh-context auditors against a shared rubric, each establishing ground truth itself — compiling
the LaTeX, reading page counts off the PDF, grepping the Lean tree — instructed to treat metadata
statuses as claims to check.

Verdict: **no bundle is submittable; best grade C−.** Tier-1 aggregate length is far below charter,
and the shortfall concentrates where duplication lives. Read
[`SYNTHESIS.md`](../audits/2026-08-01-publication-readiness/SYNTHESIS.md) first.

⚠️ **Do not run a fresh publication assessment before reading that one.** It anticipates most of
what a new pass surfaces.

**Why the readiness verdict is not a quality ranking.** `readiness` derives from finding counts,
findings are minted by reviews, and bundles with the least review evidence therefore carry the
fewest findings and the best verdicts. A bundle with no `claims_review.json` at all ranks highest
of all. The promotion path and its missing actor are in
[`END_TO_END_MAP.md` §8](END_TO_END_MAP.md#the-promotion-path--how-a-bundle-reaches-submission-ready);
the measured anti-correlation is in
[`PROMOTION-PATH-AND-SIGNAL.md`](../audits/2026-08-01-publication-readiness/PROMOTION-PATH-AND-SIGNAL.md).

## 4. The governing decision record

**[`ADR-010`](../adrs/ADR-010-publication-portfolio-reassessment.md)** owns the reassessment. It
diagnoses the Tier-1 shortfall at its generator — authorization carries no content floor, so a
container is created and then hopefully filled — and constrains how a roster change may be argued:

- **C4** — no merge, split or retirement rests on a summary, a bundle name, an audit table or a
  subagent report. The manuscripts and the Lean are read directly.
- **C5** — the publication schedule is the flexible variable; claim strength is not.
- **§6a** (`REMEDIATION_PLAN.md`) — no new check, gate or script without approval: establish what
  existing machinery covers the defect *by reading the code*, describe the residue, ask, then build.

**Open, and operator-owned** (ADR-010 §Open): the roster number · D10's scope · L1's disposition ·
the `native_decide` disclosure posture · the graphene `Γ_H` dimensional question · the
Lean-module-content absorption trigger. Each changes a charter, so a recommendation states its
dependence rather than assuming a resolution.

**Analysis owed before the roster recommendation** (ADR-010 §"What remains"): per-target purpose
statements re-derived from the manuscripts; the per-target merge/split/retire recommendation; and
homing dispositions for the un-homed substrate, whose measured scope is several times what the
charter assumed.

**Infrastructure defects** are in
[`.working-docs/ARCHITECTURE_TODOs.MD`](.working-docs/ARCHITECTURE_TODOs.MD) — none built, per §6a.

## 5. The apex retrofit — the live workstream

The retrofit migrates the portfolio onto the §D5a model, walking the roster **bundle by bundle** and
reading each draft in full before anything is declared. A sweep would reproduce the
authorization-before-measurement pattern that created the problem. Method and queue:
[`PUBLICATION_INTAKE_SHAPE.md`](.working-docs/PUBLICATION_INTAKE_SHAPE.md) §3b and §5. Progress is
tracked by `UNDECLARED_APEX_CEILING` in `scripts/validation/checks/bundles_readiness.py` and gated
by `validate.py --check bundle_apex_resolves`.

⚠️ **An apex declaration has two halves and they are gated separately.**
`bundle_apex_resolves` owns the **name** — it hard-fails on an apex resolving to no live
declaration, and on one resolving to something other than a theorem. The `claims` **string** beside
it was read by nothing until ADR-015 D3, and `apex_theorem_claims_grounded` now owns it: present
and non-placeholder, not a restatement of the theorem's own name, and its numerals traceable to the
statement. **Neither check establishes that the claim describes the theorem** — claim-to-type
equivalence is not decidable, and the check's docstring enumerates what its silence does not mean.
Reading a green on both as "this bundle's declared results are verified" is exactly the
inference the second check was written to make impossible.

**It is evidence-generating, not bookkeeping — and it has already overturned audit conclusions.**
The audit recommends merging D6+D9+D12 on the strategy document's own three-layer outline; the
derived closures say D12 does not belong (D6∩D12 empty, D9∩D12 negligible). It also **relocated**
the D6/D9 finding: the shared theorems reproduce, but their *declared* closures are
disjoint — D6 cites declarations from D9's namespace and claims almost none of them. Borrowing, not
duplication, and a different fix from a merge.

**Both merge questions ADR-010 left untested are now answered, and both by disconfirmation.**
D12 does not belong with D6+D9, and D10 shares *no* substrate with D11 — that pairing tracked the
order the two were authorized, not their content. D10's real coupling is to D9, which its own
prose acknowledges in the section that uses it but not in its novelty carve-out.

**The retrofit also finds what a closure alone cannot.** Reading a draft in full against its
statements — not against the prose describing them — surfaced two claim-integrity results the
dependency graph is blind to: a bundle whose manuscript omits a sixth of its own proved substrate,
and a bundle whose first-ever-formalization claim rests on theorems stated over structures with no
inhabitant, where the Lean source discloses the gap and the manuscript does not.

**Where a measurement and an audit conclusion disagree, the measurement is the evidence and the
audit conclusion is the hypothesis it tested.** Per-bundle working is under
`docs/audits/2026-08-*-*-retrofit/`.

Re-tiering waits on the retrofit: closure shape says where to look, but tier is also a claim about
audience and framing, and that is the operator's call.
