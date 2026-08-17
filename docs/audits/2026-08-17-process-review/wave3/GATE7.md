# GATE-7 root cause — the `NarrativeGrounding` gate's dead `SUPPORTS` edge

Scope: this is a deeper root-cause dig on wave2's `GATE-1` finding
(`docs/audits/2026-08-17-process-review/wave2/GATE.md`), which already established the
symptom (6/64 papers permanently blocked, 58/64 pass vacuously) and the disclosure
mechanism (`GATE_EDGE_TYPES_WITHOUT_EMITTERS`). This document does not re-litigate that
measurement; it answers **why the edge was never built, whether the machinery to build it
already exists, and which side of the plugin/repo boundary owns the fix.**

**Bottom line, stated first:** the emitter-capable resolver already exists, is already
running against every paper the gate blocks, and is already wired into the graph — under
a **different, newer node/edge pair** (`Sentence`/`BACKED_BY`, sourced from the
`claims-reviewer` plugin agent) that supersedes the one the gate queries
(`ProseClaim`/`SUPPORTS`, an April schema stub). The fix is **wiring inside the repo**
(`scripts/readiness_gates.py` and/or `scripts/build_graph.py`), not new plugin
construction, and not new repo construction either — the semantic judgment the operator
suspected belongs to the plugin is already a plugin agent's job, and it already does it.

---

## 1. Design intent — was an emitter ever planned, and did it slip?

`SUPPORTS` was never wired, and this was never silently forgotten — it was **declared,
scheduled, and then never assigned to a wave**, which is a different and more specific
failure than "an emitter was removed" or "the gate was authored against nothing."

Traced through `docs/roadmaps/Phase5v_Roadmap.md` (the roadmap that shipped the whole
readiness-gate subsystem) and `git log --oneline -S SUPPORTS`:

- **Wave 2a** (`746b20f6`, 2026-04-15, "schema skeleton for readiness system") registers
  `SUPPORTS` as one of 8 new edge types in the schema. Docstring: *"All stub extractors
  return `[]`; nodes materialize as each wiring wave lands (2b–2g, then 4)."*
- **Wave 2b**'s edge table (`Phase5v_Roadmap.md:304-315`) gives `SUPPORTS` its declared
  shape: `artifact → artifact`, attribute `evidence`, purpose *"Mutual reinforcement (dual
  of CONTRADICTS)"* — a **generic, symmetric, artifact-to-artifact** relation, not a
  ProseClaim-specific grounding edge.
- **Every other Wave-2 edge type got an assigned wiring wave and a commit**: `VERIFIES`
  → Wave 2c (`39a67931`), `FLAGS` → Wave 2d (`0f6fa0ba`), `PRODUCES` → explicitly
  *"deferred to Wave 4 where run-to-claim mapping is curated"* (`Phase5v_Roadmap.md:220`),
  `REPORTS` → Wave 2g (`a437dbc5`). **`SUPPORTS` appears in no wave's "Deferred to Wave 2"
  checklist (`Phase5v_Roadmap.md:216-223`) at all** — every checklist item there is a node
  extractor; the edge itself was never assigned an owner.
- **Wave 4** (`615b1fdc`, 2026-04-15, "readiness state machine (165 gates, CHECK 18)")
  ships `_eval_narrative_grounding` (Gate 7) querying `SUPPORTS` anyway, **with the roadmap
  itself documenting the gate firing on a known-dead edge at ship time**:
  `Phase5v_Roadmap.md:394,403` lists *"NarrativeGrounding: 8 papers ('interesting' prose
  claims without SUPPORTS edges)"* as the **expected, headline** Wave-4 output — Paper 6's
  "Monte Carlo evidence" claim is used as the worked example of the gate "exemplif[ying]
  the whole point": surfacing a real defect (the April MC run's `BrokenPipeError`) via a
  P1 blocker, without an emitter behind the edge it names.
- **Wave 4c** shipped the gate **WARN-only**, explicitly for this reason: *"WARN-only
  during rollout (expected to flag all 15 papers red until remediation) — escalate to FAIL
  when papers start hitting green."* That escalation happened later and separately (§1a
  below) — not as part of closing the `SUPPORTS` gap.
- **Wave 5b** (dashboard graph-tab integration) lists *"SUPPORTS/CONTRADICTS green/red
  dashed edges (once SUPPORTS/CONTRADICTS edges are emitted)"* under **DEFERRED**
  (`Phase5v_Roadmap.md:442`) — the last explicit acknowledgment in the roadmap that the
  edge type is unemitted. No later wave revisits it.

So: **an emitter was never written and later removed — it was scheduled into an
unassigned slot between two enumerated waves, shipped anyway as a consuming gate with a
disclosed, accepted defect, and then never returned to.** This is not "the gate was
authored against an edge that never existed" in the sense of a design mistake; it is a
deliberately-deferred build item whose deferral was never closed, on a subsystem
(`Phase5v_Roadmap.md`) whose Wave 2/4 sections are marked "DONE."

### 1a. Why this only recently became consequential

The gate's `state='blocked'` has been computed the same way since 2026-04-15, but it did
not actually block anything at the merge gate until **2026-08-03**. Before that date,
`readiness_submission_gate` — the check that aggregates all 165 `ReadinessGate` nodes into
pass/fail — was **inverted**: it failed only when *zero* papers were red
(`docs/adrs/ADR-009-validation-suite-modularization.md:579-596`, fixed `fd470314`, ADR-009
§Deferred item 2). The dead-`SUPPORTS` defect and the inverted-aggregator defect are
independent bugs that happened to compound: the first made Gate 7 return a wrong verdict
on 6 papers from April onward; the second made that wrong verdict invisible to the merge
gate for four months. Fixing the aggregator (correctly) is what turned a dormant defect
into a live, permanently-blocking one — which is also why wave-1/wave-2's framing of this
as a fresh, urgent finding is accurate for *consequence* even though the *cause* is four
months old.

---

## 2. What would emit it — does the resolver already exist?

**Yes.** A prose-sentence → formal-artifact resolver sourced from an LLM judgment already
exists, already runs, already covers every one of the 6 blocked papers, and is already
wired into `build_graph.py` as a first-class edge type. It is simply a different pair of
node/edge types than the one Gate 7 queries.

### The three prose→Lean/formal resolution paths in this repo

| # | Path | What it resolves | Source of truth | Consumer |
|---|---|---|---|---|
| 1 | `scripts/validation/checks/prose_lean_refs.py` (`prose_theorem_reference_coverage`) | A **verbatim, syntactically-named** Lean reference in bundle prose (`\texttt{}`, `\lean{}`, `\thm{}`, backtick-quote, and preamble aliases of these) resolves to a real declaration in `lean_deps.json` | Structural macro/brace parse of the `.tex` source itself | `validate.py` CHECK 25 |
| 2 | `build_graph.canonicalize_link` (`docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:571`) | Canonicalizes a chain-link reference (module alias vs. Lean declaration vs. short name) to one graph id | Internal to `build_graph`; the project's single resolver for chain links | Every check/gate that needs a chain-link target resolved |
| 3 | **`build_graph.extract_sentence_nodes` + `extract_backed_by_edges`** (`scripts/build_graph.py:3011-3245`, "Phase 5v Wave 10b") | **A prose sentence's semantic claim** → the formula/theorem/axiom/parameter/citation/hypothesis/Aristotle-run/production-run/module that backs it — an LLM judgment call, not a syntactic parse | **`papers/<bundle>/claims_review.json`**, written by the `claims-reviewer` **plugin agent** (Stage 10, `chain_proposed.links[]` per sentence) | Emits `BACKED_BY` edges (Sentence → artifact); feeds `last_modified` propagation, the freshness layer, and the dashboard's sentence-level chain-of-backing inspector |

Path 1 (named by `CLAUDE.md` rule 1 and `CHECK_AUTHORING_GUIDE.md:21` as the thing not to
duplicate) resolves **explicit textual citations**, not claims — it is the wrong tool for
`SUPPORTS`, which needs to know whether a *claim* (not a Lean-name mention) is backed.
Path 3 is the right tool, and it is not hypothetical: it is live.

**Confirmed against the exact 6 blocked papers** — every one already has a
`claims_review.json` on disk (`papers/{D10,D5,D8,paper10_modular_generation,
paper12_polariton,paper6_vestigial}/claims_review.json`, verified present), and the
extractor already ingests it. Spot-checked `paper6_vestigial` (the paper the Wave-4
roadmap used as its worked example): its `claims_review.json` carries 7 abstract
sentences, several with `agent_verdict: PASS` and resolved
`chain_proposed.links` — e.g. the sentence claiming vestigial gravity's EP-violation
resolves to `SKEFTHawking.VestigialGravity.ep_violation_in_vestigial` and
`ep_distinguishes_phases`; the Weingarten-integration claim resolves to
`SKEFTHawking.SO4Weingarten`. **The exact "Monte Carlo evidence" abstract sentence the
Wave-4 roadmap named as its motivating example carries `agent_verdict: TRANSITION` and an
empty `links: []`** — i.e. the independently-built semantic layer *also* finds this
specific claim unbacked, which corroborates that Gate 7's underlying concern is real, not
a false positive from a dead edge; only the delivery mechanism (`SUPPORTS`) is dead.

### Why this is the crux, restated

`SUPPORTS`, as declared in the schema (Wave 2b: `artifact → artifact`, "mutual
reinforcement, dual of CONTRADICTS"), was never even scoped to be a ProseClaim-specific
grounding edge — Gate 7's actual query (`idx.outgoing(pc['id'], 'SUPPORTS')` from a
`ProseClaim`) is a narrower use than what was declared. Meanwhile a **different, later,
already-shipped** subsystem (`Sentence`/`BACKED_BY`, landed after Wave 4 as the graph
schema's own "fine-grained full-coverage layer" — `Phase5v_Roadmap.md:834`: *"ProseClaim
retained as curated high-priority-claim layer... Sentence is the fine-grained full-coverage
layer — different roles, both valuable"*) does exactly the job `SUPPORTS` was meant for,
at finer grain (every sentence, not just the abstract), with real semantic judgment behind
it (an LLM review agent), not a hand-rolled resolver. **Building a `SUPPORTS` emitter from
scratch would be the fourth prose→Lean/formal resolver `CHECK_AUTHORING_GUIDE.md:21` warns
against** — the third already exists and already covers this exact surface.

---

## 3. Plugin vs. repo — the ownership question

### What the documented boundary actually says

There is no single "ownership table" file titled as such; the boundary is established by
`docs/architecture/VALIDATION_ARCHITECTURE.md:14-18` and `docs/architecture/
QA_QI_INFRASTRUCTURE_MAP.md` §1–1.5, and confirmed by the plugin's own
`.claude/plugins/skeft-qa/README.md`:

- **The repo (`scripts/`, `scripts/validation/checks/`) owns the mechanized, deterministic
  layer**: framework + domain-module checks that are AST-walks, regex parses, graph
  traversals, or arithmetic — reproducible without judgment. This is where extractors
  (`build_graph.py`), gates (`readiness_gates.py`), and checks live.
- **The plugin (`.claude/plugins/skeft-qa/`) owns the fresh-context judgment layer**:
  reviewer agents (`claims-reviewer`, `adversarial-reviewer`, `prose-reviewer`,
  `figure-reviewer`) that read prose or figures and render a verdict a deterministic parser
  cannot — "is this claim backed," "is this an overclaim," "does this argument land" —
  plus harness agents, skills, commands, and the `PreToolUse` hook enforcement layer.
  `VALIDATION_ARCHITECTURE.md:14`: *"This document covers ONE of the project's two
  verification layers. The other is the reviewer-agent layer... Before concluding that a
  surface is uncovered, check both."*

The dividing line is **judgment vs. mechanism**, not "prose vs. Lean" and not "which
directory." A check that needs to *decide* whether unstructured text supports a claim is
plugin work (an agent produces a verdict); a check that needs to *read a produced verdict
and gate on it* is repo work (deterministic aggregation of already-judged data).

### Where Gate 7 and the `SUPPORTS` emitter actually sit

**Both are correctly repo-side**, and correctly so — but only if they consume the
plugin's judgment rather than re-deriving it. `readiness_gates.py` (repo) is exactly where
a deterministic aggregation of "does this claim have a backing chain" belongs: it should
not itself judge prose, it should read a verdict. The defect is not that this logic is in
the wrong repository component — it's that it is aggregating the **wrong artifact**
(`ProseClaim`/`SUPPORTS`, a stub the repo tried to populate itself and never did) instead
of the **right one** (`Sentence`/`BACKED_BY`, populated by the plugin's judgment and
already flowing into the graph).

**The operator's instinct is right about *which part* is plugin work, and that part is
already built and already shipping**: *"an agent asserting the claim→theorem link during
drafting"* is precisely what `claims-reviewer` already does at Stage 10, per sentence,
with a structured `chain_proposed.links[]` verdict. There is no missing plugin
component here. What's missing is the repo-side step of pointing the gate at that
agent's output instead of at an orphaned, never-populated schema stub the repo tried (and
failed) to fill on its own in April.

### One separable sub-question: tagging `interesting`

*Should* the decision "is this claim important enough to require grounding" be an agent
judgment (plugin) rather than a regex heuristic (repo)? Given `claims-reviewer` already
classifies every sentence with `agent_verdict` (PASS / FAIL / WARN / INFO / UNGROUNDED /
TRANSITION) and `finding_classes`, it is a strictly richer signal than the five-pattern
regex described in §4 below, and re-deriving "interesting" from `agent_verdict ∈
{UNGROUNDED, FAIL}` (or similar) over the `Sentence` layer would both fix the emitter gap
and retire a second, weaker classifier doing the same job. This is a design option to
weigh at fix time, not a separate defect — flagged here because it falls directly out of
recognizing that `Sentence` supersedes `ProseClaim`.

---

## 4. Who tags `interesting` — mechanism and population

**Confirmed: a heuristic, not an author, and not the `claims-reviewer` agent.**
`scripts/build_graph.py:1338-1345`, in `extract_prose_claim_nodes` (Wave 2f,
`docstring: "Heuristic 'interesting claim' triggers"`):

```python
_INTERESTING_PATTERNS = [
    (re.compile(r'\bfirst\b.*\b(proof\s+assistant|formali[sz]ed|verified|computed)\b', re.IGNORECASE), 'first-claim'),
    (re.compile(r'\ball\s+the\s+same\b|\bconverge\b.*\b16\b|\brooted\s+in\b', re.IGNORECASE), 'unification-claim'),
    (re.compile(r'\b(Dedekind|Ramanujan|eta\s+function)\b', re.IGNORECASE), 'attribution-claim'),
    (re.compile(r'\b(programmable|tunable|within\s+reach|feasible)\b', re.IGNORECASE), 'feasibility-claim'),
    (re.compile(r'\b(Monte\s+Carlo\s+evidence|evidence\s+from\s+simulation)\b', re.IGNORECASE), 'simulation-evidence-claim'),
]
```

Applied to every sentence of every paper's `\begin{abstract}...\end{abstract}` block
only (body/intro/conclusion prose is out of scope for `ProseClaim` by design — the
docstring defers that to Stage-13 adversarial review). A sentence is `interesting` iff it
matches ≥1 of these 5 regexes; `tags` records which. **Confirmed live count: 7**,
matching the prior measurement (wave2/GATE.md and `graph_atlas.py`'s
`GATE_EDGE_TYPES_WITHOUT_EMITTERS` docstring, which separately measured "9 `interesting`
ProseClaims across 7 papers" on 2026-08-06 — the 7-vs-9 difference is claim-count vs.
paper-count, not a contradiction).

**This is a distinct, real defect, as the task anticipated**: a paper is blocked by a tag
it never chose, computed by five narrow, hand-picked regexes with no relationship to
what the paper's own abstract actually claims as novel. It selects on *surface lexical
form* ("first", "Ramanujan", "Monte Carlo evidence") rather than *rhetorical weight* — an
abstract could open with an unhedged, load-bearing overclaim that matches none of the 5
patterns and passes vacuously, while a hedged, well-cited sentence that happens to contain
the word "feasible" gets flagged. Because `claims-reviewer` already classifies every
sentence (not just 5 lexical shapes, and not just the abstract) with a verdict grounded in
actual chain-resolution rather than word-matching, it is the strictly better selector
already available — see §3's sub-question.

---

## Compact answers

1. **Design intent**: `SUPPORTS` was declared in Wave 2a/2b (2026-04-15) as a generic
   `artifact→artifact` edge, scheduled into an unassigned wiring slot, and Gate 7 shipped
   in Wave 4 querying it anyway — a **disclosed, accepted defect at ship time** (the
   roadmap's own Paper-6 worked example), not an emitter that was built and later removed,
   and not a gate authored blind. It went from dormant to a live merge blocker on
   2026-08-03 when an unrelated aggregator-inversion bug (ADR-009 §Deferred item 2) was
   fixed, four months after the gate shipped.

2. **Does an emitter-capable resolver already exist?** **Yes.** `claims-reviewer` (plugin
   agent) + `build_graph.extract_sentence_nodes`/`extract_backed_by_edges` (repo,
   "Phase 5v Wave 10b") already compute exactly this — sentence-level claim → formal-
   artifact backing, via LLM judgment, sourced from `claims_review.json`, already present
   for all 6 blocked papers, already emitting a `BACKED_BY` edge type the gate simply
   doesn't query. **The fix is wiring `readiness_gates.py`/`build_graph.py` to the
   existing `Sentence`/`BACKED_BY` layer, not building a fourth resolver.**

3. **Is Gate 7 on the correct side of the plugin/repo line?** **Yes, structurally** — a
   deterministic aggregator reading an already-produced verdict is correct repo-side work.
   It is aggregating the **wrong source** (an orphaned repo-side stub) instead of the
   **right one** (the plugin-produced `Sentence`/`BACKED_BY` layer). The specific piece the
   operator suspected belongs to the plugin — an agent asserting the claim→theorem link —
   **already is plugin work, already shipped, already running**; nothing new needs to be
   added there.

4. **Who tags `interesting`?** A 5-regex lexical heuristic in `build_graph.py`
   (`extract_prose_claim_nodes`), applied only to abstract sentences, flagging on surface
   word-shapes with no relationship to actual claim weight or backing — confirmed 7 live
   claims. A distinct, real defect: papers are blocked by a tag no author chose and that a
   strictly better signal (`claims-reviewer`'s per-sentence verdict) already supersedes.

**One-sentence root cause:** Gate 7 queries a `SUPPORTS` edge that was scheduled but never
assigned an owning wave in April 2026 and shipped anyway as a disclosed defect, while a
semantically equivalent and strictly richer resolver — the `claims-reviewer` plugin
agent's per-sentence chain-of-backing, already flowing into the graph as `Sentence`/
`BACKED_BY` since Wave 10b — has existed the whole time and already covers every paper
the gate blocks; the defect is that nobody re-pointed the gate at it, not that the
resolver doesn't exist.
