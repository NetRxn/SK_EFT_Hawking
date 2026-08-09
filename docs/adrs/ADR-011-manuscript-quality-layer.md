# ADR-011 — The manuscript-quality layer and the reviewer promotion path

- **Status:** ✅ **ACCEPTED AND BUILT (2026-08-09).** All eight phases shipped. Gates 12–15
  (`bundle_manuscript_length`, `bundle_figure_adequacy`, `bundle_structural_coherence`,
  `bundle_reader_facing_voice`) are registered and running; F-02, F-03, F-05, F-07 and F-09 are
  implemented; the promotion path, the authoring skill and the prose-reviewer are in the repo.

  **Two consequences are deliberately visible rather than resolved**, because resolving them means
  writing manuscripts rather than infrastructure: `bundle_manuscript_length` is RED for 11 bundles
  under floor, and `bundle_figure_adequacy` is green **by declared deferral** — 42 drawn against 40
  deferred, with 8 bundles carrying no drawn figure. Both magnitudes ride on the gates' own summary
  lines, so neither can hide behind a colour. See `ACCURACY_LEDGER` V70 and V72; V72 records a
  closure reviewer's charge that the figure gate's green is a scope move, and does not defend it away.

  Build was authorized by the operator 2026-08-08
  (*"approved to build"*), with three standing directions that shaped the plan below:
  1. **Flywheel ordering** — *"always prioritize steps that will pay the biggest dividends as we
     continue developing."* Phases are ordered by downstream leverage, not by shippability.
  2. **Ships as a unit** — *"All this work will ship as a unit on a merge back to main, so optimize
     for overall correctness."* No phase is designed to be independently releasable; correctness of
     the whole is the objective.
  3. **Venue reassignment is open** — *"it's possible papers are going to shift around a bit and be
     added, i'm open to reassignment as appropriate; sensible default publication venues that would
     be likely to accept an achievable version of the work can be added."*

- **Supersedes / absorbs:** `ARCHITECTURE_TODOs.MD` **D24** (duplicate of Gate 16 assertion #2),
  and schedules **D5**, **D7**, **D18**, **G-01**, **G-02**.
- **Implements:** `CROSS-absorbability-and-strategy-drift.md` §4.6 (**F-01…F-10**) and §5.4
  (**Gates 12–16**), and `PROSE-QUALITY-BASELINE.md` §Remediation.
- **Governed by:** `REMEDIATION_PLAN.md` §6a — *defect → existing coverage by reading the code →
  residue → approval → build.* Approval obtained; the reading is recorded per phase.

---

## Context

### The defect, in one sentence

`BUNDLE_LIFT_PROCEDURE.md` has **no manuscript-quality layer**. The 2026-08-01 audit walked all
fourteen lift steps and classified what each owns: metadata, filesystem, structural scaffold,
sentence, citation, artifact, claim, finding, metadata, tooling, metadata. **Not one step owns the
document.**

The consequence is measured, not asserted:

- **9 of 21 bundles ship zero figures and zero `\begin{figure}`** — including the flagship. Stage 9's
  pass criterion is *"ALL figures PASS"*, which over an empty set is `True`. `papers/D10` records
  `stage9_status: "green"` for a bundle with no figures.
- **171 body sentences exceed 60 words**; seven bundles contain a sentence over 100 (D7 peaks at
  **179**). Em-dash density spans **11×** *within this corpus* — L1 at 36/1000, D9 at 391/1000 — so
  the low end is in-corpus evidence of the achievable, not an external ideal.
- **The prose gradient tracks recency.** The newest bundles occupy the top of the density table.
  Quality degraded monotonically as the corpus grew, because nothing measured it.
- **Section architecture is a projection of the source roster.** D3: 31 sources → 37 sections.
  D1: 12 → 12. `bundle_append.py` inserts one section per registered source and no later step ever
  re-plans what it created.

`PROSE-QUALITY-BASELINE.md` states the mechanism exactly, and it is the reason this ADR exists:

> *"The same project produced a 1,123-theorem kernel-pure Lean corpus, because the kernel refuses bad
> proofs. It produced unreadable prose because nothing refuses bad prose. **The distinguishing
> variable is the presence of a decider, not the author.**"*

### Why the process law is the load-bearing surface

`WAVE_EXECUTION_PIPELINE.md` is what the development agents read and follow. **It has not been
amended for any of the seventeen proposals.** It says nothing about charters, page budgets, figure
plans, prose review, or scar tissue. Every wave executed under the current law reproduces what the
audit measured — the corpus is the law working as written.

This is why the doc-first discipline in `docs/architecture/README.md` rule 2 is not bureaucracy here:
a mechanism that lands without its law amendment is a mechanism the agents do not know exists.

### The second defect: reviewer verdicts are not machine-readable

Independently of prose, the promotion path is broken at one transition
(`END_TO_END_MAP.md` §8):

| # | transition | performed by |
|---|---|---|
| 1 | bundle created → `stage{9,10,13}_status = "pending"` | `bundle_source_manifest.py:129-131` |
| 2 | **`"pending"` → `"green"`** | ⛔ **nothing** |
| 3 | `"green"` → `"pending"` on append | `bundle_append.py:320-325` |
| 4 | findings → `blockers_open`, `readiness` | `bundle_readiness.write_metadata_counts` |
| 5 | conditions met → submission | operator runs `gate_precheck.py submission` |

**No code path writes `"green"` to any `stage*_status`.** Every green in the corpus is a hand edit,
and the reviewer agents that would earn one have no write path to the field they gate on.

Two consequences that bear directly on this ADR's design:

- **A fourth reviewer built today inherits the defect** — it would deposit its verdict in a fourth
  field that nothing writes and nothing reads. Phase 1 therefore precedes the prose reviewer.
- **`review_recorded` does not discriminate review KIND or SCOPE.** Any document referenced by
  `stage13_review_doc` satisfies the unreviewed-guard, so a targeted 16-anchor attribution sweep
  counts exactly as a full adversarial pass. That, not an absent guard, is how a bundle whose
  Stage 10 never ran reached GREEN.

---

## Constraints — verified, and load-bearing for the design

### C1. The pipeline must NOT be renumbered. Verified blast radius.

The obvious design — "insert a prose stage between 10 and 11" — is **rejected**, because the stage
numbers are load-bearing in four places, each verified by reading the code:

| Consumer | Coupling | Breaks how |
|---|---|---|
| `scripts/paper_tables/sources.py:418` `pipeline_stages()` | Parses `Stage N: NAME → Gate: …` out of the law's ASCII overview block | Regenerates **paper 15 Table 1** — a shipped table in a draft |
| `scripts/gate_precheck.py` | Stage names `s9` / `s10` / `s13` / `s13-lean` / `submission` | The executable gate vocabulary; `VALIDATION_GATE_TOPOLOGY.md` §1 tiers key on it |
| `bundle_metadata.json` | Field names `stage9_status`, `stage10_status`, `stage13_status` across **21 bundles** | Schema break + every reader in `bundles_readiness.py`, `bundle_readiness.py`, `datastar_bundles.py` |
| Every doc citing "Stage 13" | prose, ~all of `docs/` | Mass drift |

**Design consequence:** the read-through reviewer lands as a **second sub-gate inside Stage 10**,
not as a new numbered stage. This follows the precedent already set by finding B6 (2026-08-07):
Stage 10 is `PAPER DRAFT` and *already* carries claims review as a sub-gate; adding a second sub-gate
is the shape the law already has. **There is no Stage 10a, and no renumbering.**

### C2. The charter is far cheaper than the audit assumed — three of its five fields already exist.

F-01 specifies a `CHARTER.md` with five fields. Measured against the tree:

| Charter field | Status | Source |
|---|---|---|
| target venue | ✅ **exists for all 21** | `bundle_metadata.json.target_journal`, populated at init from `PAPER_STRATEGY.md` |
| hard length limit | ⚠️ **exists as prose, unparsed** | `PAPER_STRATEGY.md` §6 Length column: `4pp`, `~40pp`, `80–150pp`, `2–3pp`, `~15pp` — for all 21 |
| one-sentence contribution claim | ✅ **exists for all 21** | The ADR-010 §D2 purpose statements authored during the apex retrofit (2026-08-06/07), one per bundle, each carrying *Audience · Venue · the claim only this container can make · Substrate · Honest size vs charter* |
| planned section architecture | ❌ **does not exist** | genuinely new authoring |
| figure plan | ❌ **does not exist** | genuinely new authoring |

**The apex retrofit already paid for most of the charter.** This materially changes the phase
ordering: the length-target half of the charter is a *transcription* of data the strategy already
holds, not an authoring exercise, and it unlocks Gate 12 immediately.

### C3. The page instrument exists and is deliberately unwired.

`scripts/compile_bundle_pdf.py:105-112` computes the page count via `pdfinfo` and at `:114`
`ok = not errors and unresolved <= 0 and not unused_opts` — **`pages` enters only the
human-readable string.** Gate 12 is a wiring job, not an instrument build. Same for `pdftotext`,
already a dependency of the same script.

### C4. `length_target` must tolerate reassignment.

Per the operator's third direction, venues and the roster may still move. The schema therefore
records the target as **data with a provenance field**, not as a frozen constant, and a bundle whose
target is not yet decided records `length_target: null` with a stated reason — which reads as
UNMEASURED, never as passing. A charter is a current commitment, not a freeze.

### C5. The decider must not be the generator.

Carried verbatim from `PROSE-QUALITY-BASELINE.md` §Remediation item 4. An LLM rewriting LLM prose
converges on a different bad attractor. Hence: the voice gate (Phase 3) is **deterministic**, the
read-through reviewer (Phase 5) carries a **distinct brief** and is explicitly not the
adversarial-reviewer, and human calibration happens on a *sample*.

---

## Decision

### D1 — Build the manuscript-quality layer as six phases, ordered by downstream leverage

Ordering rationale is recorded per phase in §Plan. The governing principle is the operator's:
prioritize what pays the biggest dividends as development continues. Concretely, three dividend
classes were weighed:

- **unlocks-downstream** — how many later mechanisms consume this phase's output;
- **prevents-waste** — how much future work this stops from being done wrong;
- **informs-a-pending-decision** — whether the output feeds a decision the operator still owes
  (the roster number, the four merges).

### D2 — Every phase amends `WAVE_EXECUTION_PIPELINE.md` in the same commit as its mechanism

Per `docs/architecture/README.md` rule 2. This ADR is the specification that precedes all of them.
No mechanism ships without the law describing it, and no law text ships describing a mechanism that
does not exist.

### D3 — The law names owners, never values

Extending the B5 pattern (2026-08-07) that fixed five wrong facts in the law by replacing copied
values with pointers to the artifact that owns them. Every amendment in this ADR cites its owner:
`bundle_metadata.json.length_target` for budgets, `validate.py --list` for the check roster,
`CHARTER.md` for section and figure plans. **No amendment enumerates a roster.**

### D4 — D24 closes as a duplicate

The Stage-9/10-before-13 ordering assertion is Gate 16 assertion #2 and sub-item 3 of TODO-D5. It
ships inside Phase 1 with the other four sub-items, not as a standalone check. Filing it separately
was itself an instance of the failure `docs/architecture/README.md` rule 1 names.

---

## Plan

### Phase 1 — `length_target` + Gate 12 `bundle_manuscript_length`

**Why first.** Highest dividend-to-cost ratio in the set. The data exists (C2), the instrument
exists and is unwired (C3), and the output **feeds a decision the operator still owes**: the audit
records that this single gate would have flagged D7 and D10 *on the day they were closed GREEN*, and
per-bundle size-vs-charter is direct evidence for the four merge proposals in ADR-010 §D4. It is the
only phase that pays a dividend into a STOP-AND-ASK item.

1. Add `length_target` + `venue_provenance` to the `bundle_metadata.json` schema
   (`BUNDLE_DIRECTORY_SCHEMA.md` first).
2. Transcribe `PAPER_STRATEGY.md` §6 Length into all 21, with `unit` ∈ {`pages`,
   `word_equivalents`} and PRL-class targets using the rubric's word-equivalent rule.
   Missing/changed targets get a **sensible default for a venue likely to accept an achievable
   version of the work**, recorded as such (operator direction 3).
3. Wire `pages` through `compile_bundle_pdf.py` instead of discarding it; persist
   `compiled_pages` so the heatmap need not recompile.
4. `bundle_manuscript_length`: `floor ≤ compiled ≤ ceiling`; **UNMEASURED — never PASS — when
   `length_target` is null or the draft does not compile.**
5. Law: Stage 10 gains the length budget; lift procedure gains §0.

### Phase 2 — The promotion path (TODO-D5, five sub-items; absorbs D24)

**Why second.** It is the socket every later reviewer verdict plugs into. Building Phase 5 first
would create a fourth unreadable status field. It also converts the lift procedure's §10 and §12
from prose into enforcement, which the audit calls *"the single change that would have prevented
most of §4.5."*

1. **Writers, or removal.** Decide and implement how `stage*_status` reaches `green`. Preferred:
   the reviewer cycle writes its own verdict, making the field derived like `blockers_open`, with
   `apex_theorems`-style hand-declaration only where a human attestation is genuinely the input.
2. **Review KIND** recorded on `stage13_review_doc`, so an attribution sweep no longer satisfies
   the same guard as a full adversarial pass.
3. **UNMEASURED, never GREEN** for a bundle with no `claims_review.json` — the bundle-layer
   analogue of `CheckResult.measured` (ADR-009 D2).
4. **Gate 16 assertions #2/#3/#4** — ordering (= D24), `readiness == GREEN` implies both, and
   `stage13_redo_required` implies a review newer than `last_lift`.
5. **Enum discipline** — the live corpus uses five values, three undeclared. Declare or reject.
6. Law: Stage 9 / Stage 10 / Stage 13 gain their enforcement statements; lift §12's exit condition
   becomes machine-checkable. **Folds in the `freshness_stale` contradiction** (S1): lift §12 still
   lists `freshness_stale == false` as a GREEN exit condition, which the absorption protocol
   retired on 2026-07-31 as *"an mtime signal, not a readiness verdict."* §12 is being edited
   anyway; the correction lands with it.

### Phase 3 — the em-dash prohibition, and one narrow voice class

**⚠️ RESCOPED 2026-08-08, and the measurement is why.** The phase originally proposed four
denylist classes plus a generic AI-slop vocabulary. Both were measured before building and both
mostly died:

- **The generic slop denylist would be a check that cannot fire.** Twenty markers scanned across
  all 21 bundles: **11 hits total, 17 of the 20 at zero.** No `delve`, `tapestry`, `realm of`,
  `testament to`, `it is worth noting`, `moreover`/`furthermore`, `in conclusion`. Whatever
  produced this corpus does not write chatbot vocabulary. Building the denylist would have
  produced a gate passing vacuously forever — the exact anti-pattern this suite exists to catch.
- **The wide vocabulary class does not survive contact with the corpus.** `bundle` is 230
  publication-architecture uses against **9 genuinely mathematical** ones, and `lift` is
  irreducibly mixed: a context-regex classifier written to separate them misclassified in *both*
  directions on its own samples. `sorry` is always `\texttt{sorry}` inside "zero `\texttt{sorry}`",
  a claim about the artifact rather than scar tissue.
- **There is no historical Pareto for prose.** 273 review documents carry 926 BLOCKER findings,
  but the classifier buckets them to readiness gates — citations, parameters, theorem substance —
  every one of which already has a check. **Prose style was first reviewed on 2026-08-01**, so
  any wider prose gate would extrapolate from a single measurement.

**Operator direction (2026-08-08):** be conservative; anything needing judgment to fix belongs to
the prose agent, not to a check. What survives that line is two things.

**1. `bundle_prose_em_dash_free` — target ZERO, not a ratcheted rate.**

The operator's framing, which changes the disposition: *"any em-dash immediately signals AI
authorship to human readers in 2026, and has the effect of decreasing trust."* That makes it a
binary trust signal, not a style density. **Measured: 741 em-dashes (621 `---` + 120 literal `—`),
and 0 of 21 bundles are clean.**

⚠️ **The en-dash distinction is load-bearing and a naive check would be catastrophic.**
`--` is MANDATORY typography — `Bose--Einstein`, `Bekenstein--Hawking`, `SK--EFT`,
`Kaul--Majumdar`, page ranges — and there are **1,121 of them**. A scan that did not distinguish
exactly-three from exactly-two would flag 1,862 occurrences and be wrong about 1,121. One line
carries both: `observables---also drives the SK--EFT`.

**2. `bundle_reader_facing_voice` — matching the ACT of self-narration, not the vocabulary.**

⚠️ **Re-scoped a second time, again by measurement.** The audit specified a word denylist —
`Stage 13`, `reviewer`, `adversarial review`, `BLOCKER`, `round-N`. Measured on the corpus that
scores **90 hits, of which I1 alone holds 48**, because I1 is the methodology paper and the
review pipeline is its *subject matter*. Worse, `reviewer` splits three ways:

- **scar tissue** in F — *"Adversarial review (`\texttt{adversarial-reviewer}` agent;
  fresh-context Stage-13 pass)"*, internal harness vocabulary in an RMP physics review;
- **subject matter** in I1 — *"Stage 9 runs a figure-reviewer agent"*;
- **the paper's actual audience** in I2/I3 — *"lets reviewers calibrate effort"*,
  *"Mathlib4 reviewers can calibrate expectations"*.

A gate over that vocabulary needs a per-bundle exemption and is a judgment call wearing a regex,
which is exactly what the operator assigned to the prose agent.

**Matching the act instead scores 13 hits across 4 bundles with I1 at ZERO**, so there is no
exemption mechanism to maintain or drift. Four patterns, none with any legitimate use in a
manuscript: a correction stamped with an ISO date; an account of what an earlier draft of this
text said; a first-person superseded claim (*"We previously shipped…"*); an internal
review-round finding reference. Live examples: *"three earlier drafts of this sentence named…"*,
*"(corrected 2026-08-01, D11 Stage-13 round-14 finding 6.2)"*.

**Removal is not deletion.** The narration wraps real content — a retraction is a scientific
disclosure, a scope correction states the correct scope — so the substantive claim is restated
in the present tense and only the editing account goes. Per F-05 the history moves to
`change_log.md` and the supersession ledger, where a later reader can actually check it.

It is a regression guard an agent run cannot be: the deposits accumulate *between* reviews, one
per remediation round, and D11/D12 ran fourteen Stage-13 rounds in a single day.

**3. F-05:** lift §11 gains *"a fix may not narrate itself"*; §12 gains a terminal de-scarring
pass.

**Dropped entirely and deferred to the prose agent:** the slop vocabulary, `bundle`/`lift`/`sorry`,
sentence length, and em-dash *density* as distinct from em-dash *presence*.

### Phase 4 — Charter §2/§3 (section plan + figure plan), Gates 13/14, F-02/F-03

**Why fourth.** The genuinely expensive authoring — 21 planned outlines and figure plans — and the
phase that removes the sedimentation *mechanism* rather than its symptom. It is deliberately after
Phases 1–3 because their measurements (size, voice, promotion state) are inputs to authoring a
charter honestly.

1. `CHARTER.md` per bundle: section architecture (6–12 sections, each with what it argues) +
   figure plan (`{id, shows, source}`), seeded from the existing §D2 purpose statements.
2. **F-02** — **Registering a source must never create a section.** ✅ **Shipped 2026-08-09,
   and *not* against a charter.** The plan is read off the draft's own top-level sections
   (`bundle_append.py --target-section`), because a plan stored beside the document it
   describes drifts from it while a plan read *from* the document cannot. This buys the same
   validation the charter was for — you may only append where the architecture already has a
   home, or say so explicitly via `--new-section --section-rationale` — with nothing to
   author and nothing to keep in sync, which also retires the charter dependency that had
   deferred this item. Measured before the change: **74 of 74 content lifts created a
   top-level section**, 28 of them in D3. See TODO-D26.
3. **F-03** ✅ **Exercised 2026-08-09, and the measurement is the point.** The
   `\figuredeferred{id}{reason}` form this phase mandated had **zero uses across all 21
   drafts** until now; nine bundles carried no figures and no plan. Forty deferrals are
   now declared (F 8, seven Tier-1 bundles 4 each, I3 2, D8 1, D12 1), each naming what
   the figure shows and what blocks it, with the macro defined once in
   `docs/figuredeferred.tex` beside `docs/counts.tex`. `bundle_figure_adequacy` is green
   — **and its summary now carries `N drawn, N declared-deferred, N bundle(s) with zero
   drawn figures`**, so a green can never hide an all-deferred corpus, which would be the
   vacuous-Stage-9 failure rebuilt one layer up. Original text: §6 becomes figure
   *realisation*; `\figuredeferred{id}{reason}`; Stage 9 stops passing
   vacuously on an empty set.
4. **Gate 13** `bundle_figure_adequacy`, **Gate 14** `bundle_structural_coherence` (sedimentation
   ratio, required-section set, non-empty bibliography — which alone catches D8's and D10's
   zero-`\bibitem` state).

### Phase 5 — the authoring skill AND the read-through reviewer, over one shared reference set

**⚠️ SCOPE EXPANDED by operator direction 2026-08-08.** The phase was one deliverable, the
reviewer. The operator identified the gap it left: *"we don't actually have a scientific paper
authorship skill."* That is correct and is the deeper defect. The pipeline has **three reviewer
agents and no authoring guidance** — everything about how to write is scattered through
`BUNDLE_LIFT_PROCEDURE` §7 as a bookkeeping checklist read at lift time. A corpus with 741
em-dashes and 541 process-narration hits is what an unguided generator produces; adding a fourth
reviewer without an author only moves the work downstream.

**Why fifth.** Both consume the prior phases: a verdict socket (P2), a length budget (P1), a voice
baseline (P3), and a section plan (P4).

**1. `skills/paper-authoring/` — the generative side (new).**
Follows the plugin's existing convention (`goal-dev`, `goal-prompt` both carry `references/`):

```
skills/paper-authoring/
  SKILL.md
  references/
    prohibited-patterns.md   ← SHARED, mandatory read on drafting
    house-voice.md
    venue-conventions.md
```

`prohibited-patterns.md` is authored from the em-dash sweep's field evidence — six Sonnet agents
read all 741 occurrences in context and reported the *generative habits* behind them, not just the
symptom, so the reference prohibits the sentence shapes rather than the punctuation.

Two rules it must carry, because both are failure modes the prohibition itself creates:
- **Em-dash removal is a rewrite, not a substitution.** The dash usually joins two clauses; the
  right fix is a colon, a semicolon, parentheses, a full stop, or restructuring, chosen by the job
  the dash was doing. A skill saying only "no em-dashes" yields comma splices.
- **En-dashes are REQUIRED.** An author told "no dashes" will break `Bose--Einstein`. The check
  counts exactly-three and would not catch that regression.

**2. `agents/prose-reviewer.md` — the deciding side.**
Brief: *read start to finish as a referee at the named venue who has never seen the repository.*
Five blocking questions per F-04. **Output is a restructuring instruction, not a finding list** —
which is precisely why it is not the adversarial-reviewer, whose output is findings-only by design.
Runs before the claims sub-gate and before Stage 9, per lift §7.5. Law documents Stage 10's
sub-gate structure; **no renumbering** (C1).

**3. The shared-reference design, and the collision it must resolve.**
The operator's proposal — *"the prose reviewer and drafting agent share the references directory,
reducing risk of divergence"* — is right, and it collides with C5 (*the decider must not be the
generator*). A reviewer briefed entirely off the author's rule list can only check compliance with
rules the author already followed, and would pass anything the author produced.

**Resolution: shared floor, divergent ceiling.** Both read `references/prohibited-patterns.md` —
objective, enumerable, and genuinely one source of truth, so a rule cannot drift between writing
and review. The reviewer additionally carries a brief the author does **not** have, framed on
reader outcome rather than rule compliance: *where would you stop reading; does the abstract lead
with the result; does each section advance a single argument*. The author is never given those
questions as a checklist to satisfy.

### Phase 6 — Absorption repair (F-07 parts 2–3, F-08, F-09, F-10)

**Why last, and flagged.** This is ADR-010 §D6, previously carried as a separate approval. It is
included here because the operator's *"we'll scope everything in together"* covers it; it is called
out so it can be dropped without disturbing Phases 1–5, on which nothing here depends.

1. **F-07** — a Lean-substrate freshness trigger; promote to FAIL at the submission gate.
   ✅ **Shipped 2026-08-09, and the design changed under measurement.** *Mtimes are
   rejected* — a checkout or fresh clone rewrites the whole tree's mtimes and would mark
   every sourceless bundle stale at once — so the signal is the last **commit** that
   touched the file. And `append_log.json`'s registrations were **not sufficient**: D6 and
   D7, the two bundles most in need of a trigger, register zero modules, so the population
   is the union of the registrations and the **derived apex closure**, which is declared
   for all 21. The submission-gate promotion needed no work; the strict-mode branch was
   already live. See TODO-D27.
2. **F-08** — branch **D.0**: *target unsound → home the work, do not absorb.* Decouples homing
   from absorbing so a defective bundle stops growing.
3. **F-09** — per-phase mapping rows, not per-bundle. ✅ **Shipped 2026-08-09, twelve rows
   rather than the nine scoped here** — D10's 6BA/6BB/6BC carry the identical defect and
   were missed. 6CC is deliberately excluded: it is PARKED, and a row for a phase with no
   substrate registers an absorption unit that can never be absorbed.
4. **F-10** — `bundle_lean_module_coverage`: declared modules must appear in the draft.

### Phase 7 — `WAVE_EXECUTION_PIPELINE.md` becomes a clean reader-facing law (RUNS LAST)

**Operator direction, mid-Phase-2:** once the pipeline document is fully aligned with the process
and stable, it needs a pass that removes the back-and-forth, oscillation and troubleshooting
language. It is read by nearly every agent during development work, so it must be **lightweight,
100% aligned, and 100% accurate**. Progressive disclosure into a companion document is permitted.

**Sequenced last by construction.** Every phase in this ADR amends the pipeline document, so a
rewrite performed earlier would be re-dirtied by the phases after it. That includes my own P1–P6
amendments: **they are written in the current house style and are in scope for this sweep, not
exempt from it.**

**Starting measurement (2026-08-08, before any edit):** 828 lines, **9,303 words**, 51 headings,
**53 provenance-citation sites**. The distribution is the actionable part, and it is not what the
"oscillation language" framing would predict:

| marker class | hits |
|---|---:|
| ADR / TODO / audit back-references | 31 |
| dated incident references (`20NN-NN-NN`) | 18 |
| correction / retraction / supersession phrasing | 6 |
| first-person process voice | 3 |
| hedging | 2 |
| troubleshooting voice | **0** |

**The document does not hedge and does not troubleshoot; it cites its own history.** It reads as an
annotated changelog of *why* each rule exists, and that history is what makes it heavy. The sites
are concentrated, so the rewrite is surgical rather than wholesale:

| section | sites |
|---|---:|
| Pipeline Invariants | 15 |
| Stage 14 (meta-process) | 10 |
| Stage 10 (paper draft) | 6 |
| Stage 4 (Aristotle) | 5 |
| Stage 7 (cross-layer validation) | 4 |
| everything else (8 sections) | 13 |

Stages 1–3, 5, 6, 8, 9, 11–13 carry 0–3 sites each: **the stage body is already close to law.**

**Approach:** the law states the rule; the provenance moves to progressive disclosure. A rule an
agent must follow stays in the document; the incident that produced it, the ADR that decided it and
the audit that found it become a reference a reader can follow when they want to know why. Nothing
is deleted — deleting provenance would violate the same accuracy discipline this ADR is built on.

⚠️ **Accuracy is the gate, not brevity.** A shorter document that misstates the process is a worse
outcome than the current one. The rewrite is verified against the same substrate the phases
touched, and the word count is a consequence, not a target.

**Outcome.** The law is 5,716 words (from 9,303, a 39% reduction) with dated incident references at
**0** (from 18); the provenance moved to `docs/WAVE_PIPELINE_RATIONALE.md` (2,094 words), keyed by
stage and invariant. Stage headings 1–14 and invariant numbers 1–17 are byte-preserved.

**The rewrite found four accuracy defects, which is why this phase was not cosmetic:**

1. **The Quick Reference block invoked an interface Stage 4 declares archived and disabled.** It
   still carried the pre-ADR-006 flags (`--priority`, `--integrate`, `--resume`); the live CLI is
   subcommand-based. An agent copying from the command block — which is exactly what a quick
   reference is for — would have driven the disabled path.
2. **Stage 13's bundle-tier table was stale.** It listed Tier 1 as D1–D5 and Tier 3 as I1–I2; the
   registry has **Tier 1 = D1–D12** and **Tier 3 = I1–I3**.
3. **The absorption-branch set was stale in two places and inconsistent between them** — one site
   said D.1–D.3, the other D.1–D.4, and both predated branch D.0 added in Phase 6. The protocol
   ships D.0–D.4.
4. **Paper 15's Table 1 described gates that no longer existed.** `pipeline_stages()` parses this
   document's overview block, so the table had been reproducing pre-ADR-011 gate text. It now reads
   `provenance + claims + length + read-through` for Stage 10 and names figure adequacy and verdict
   recording at Stages 8 and 9. Regenerated in this change.

**Verification that nothing operative was lost.** Every file path, check name, script and CONSTANT
in the pre-rewrite document was extracted and tested for presence in the law-plus-rationale pair.
The first pass reported 61 missing and was wrong — the extractor keyed on `--check <name>` and on
exact path strings, so a check named in a table and a path written more fully both read as absent.
Re-run on basenames, 31 were genuinely gone; each was classified operative or provenance, and the
operative ones were restored (the stakeholder and reference rows of the Stage-12 sync table,
`PLACEHOLDER_TOTAL_COUNT`, `NATIVE_DECIDE_DECL_CLOSURE_CEILING`,
`scripts/render_tracked_hypotheses.py`, the Invariant-14 propagation machinery, and others). What
remains absent is deliberate: the agent invocation form replaced a file path, and `<Module>.lean`
replaced the placeholder `Y.lean`.

### Phase 8 — the `skeft-qa` plugin is reviewed and synchronised to intended state

**Added by operator direction 2026-08-08**, on noticing staleness in `skills/wave-close/SKILL.md`
and `skills/sync/SKILL.md` while reviewing the shared-reference design. Scope is the whole
plugin — `agents/`, `commands/`, `hooks/`, `scripts/`, `skills/`, `tests/`, `README.md` — for
architecture alignment and synchronisation, not just the two files that prompted it.

**Measured against the `plugin-dev` skill's own criteria** (loaded 2026-08-08 at operator
direction, so the review runs against published best practice rather than assumption):

| skill | model-invocable | body words | 3rd-person description | broken `references/` links |
|---|---|---:|---|---|
| `goal-prompt` | no (`disable-model-invocation`) | 2,784 | n/a | none |
| `harvest` | yes | 1,105 | **NO** | none |
| `goal-dev` | yes | 966 | yes | none |
| `sync` | yes | 665 | **NO** | none |
| `debrief` | no (`disable-model-invocation`) | 591 | n/a | none |
| `wave-close` | yes | 483 | **NO** | none |

> ⚠️ **Two claims in the first draft of this table were wrong, and both were my own.** They are
> corrected above and recorded here rather than silently overwritten, because the way they failed
> is the reusable lesson.
>
> - *"Six of six skills miss the third-person form."* Two errors compounded. The scan tested
>   `description.startswith("this skill")`, so `goal-dev` — which carries the phrase mid-sentence
>   — read as a miss; and folded YAML (`description: >`) wraps the description across lines, so a
>   raw substring match splits the very phrase it is looking for. The rule also does not bind on
>   the two skills carrying `disable-model-invocation: true`, whose description is never matched
>   against a user turn; it is a human-facing label. **Real figure: 3 of 5 model-invocable skills.**
> - *"`goal-prompt` names two reference files that do not exist."* They are cross-skill references
>   — `goal-dev/references/lab-notebook.md` and `.../parallel-worktrees.md` — and both exist. The
>   scan's regex captured only the basename after `references/`, discarding the `goal-dev/` prefix
>   that made them resolve. **No broken reference links exist anywhere in the plugin.**
>
> Same root cause both times, and the same one as the `lean_modules` near-miss in Phase 6: a scan
> keyed too narrowly reports a live thing as absent, and an empty result reads as evidence. Hence
> the mitigation below is a *test*, not an edit.

What the review actually found, once measured correctly:

1. **The README documented a fraction of what ships** — 4 of 9 agents, 4 of 6 commands, 4 of 5
   hooks. Every component here is auto-discovered from the filesystem, so a new file goes live
   the moment it lands with nothing forcing the README to follow.
2. **The README asserted a safety posture that was false.** It described the hooks as
   *"four (all default-inert + fail-open)"*. The undocumented fifth is the web-egress guard,
   which is deliberately **unconditional and fail-CLOSED** — the exact opposite, and the one
   whose posture matters most. The blanket sentence was wrong precisely because the hook it
   omitted is the exception.
3. **Three model-invocable skills lack the trigger form** (`harvest`, `sync`, `wave-close`).
4. **Three bare `scripts/X.py` prose references were ambiguous.** Both the plugin and the repo
   have a `scripts/` directory; these named plugin scripts in a form that resolves to nothing
   from the repo root a reader is standing in.
5. **`prose-reviewer` shipped with no `tools:` field**, so it inherited Write, Edit and Bash. Its
   body says *"You do not edit"* — the whole reason it is separate from the author — but that was
   a request, not an enforcement.
6. **The entire plugin test suite ran nowhere.** `testpaths = ["tests"]` collected 5,781 repo
   tests and zero plugin tests; there is no CI workflow and the pre-commit hook runs only IP
   clearance. The 156 existing guards — including `test_skill_safety.py`, which exists to catch
   shipped defects — fired only when someone passed the plugin path by hand.

A seventh finding surfaced only when the combined suite first ran, and it landed on this phase's
own work: **a repo-side guard I had not found already covered part of what I was building.**
`tests/test_plugin_prompt_code_refs.py` requires every `scripts/...`-shaped string in a plugin file
to resolve, and it failed on the literal placeholder in the new test's docstring. Both tests are
kept — the repo-side one accepts either root and is the broad net; the new one requires prose to
resolve from the repo root a reader actually stands in — and their relationship is documented in
the new file's header so neither is later deleted as redundant. The process lesson is architecture
rule 1: read what owns the surface *before* building on it, or you build the second mechanism
beside one that already exists.

**The fix for a drift class is a guard, not an edit.** `tests/test_plugin_surface.py` (10 checks)
pins the surface-to-README contract: every agent, command, skill and hook script must appear in the
README; the README's spelled-out hook count must equal what `hooks.json` wires; every
`${CLAUDE_PLUGIN_ROOT}` path must resolve; bare `scripts/` prose must resolve from the repo root;
every agent must state `model:` explicitly; every model-invocable skill must carry the trigger form.
Each was production-seeded to confirm it catches its defect. `testpaths` now collects both suites.

⚠️ **This phase is a review, not a rewrite.** `goal-prompt` at 2,784 words against the 1,500–2,000
target is a real finding and is **filed as TODO-D28**, not fixed here — splitting a mandatory
always-on posture document is a content change that deserves its own change, not a passing edit.

The new `paper-authoring` skill (Phase 5) is authored to these criteria from the start, so it
does not join the backlog it is landing beside.

---

## Consequences

**Every phase adds a gate that fires on the current corpus.** Phase 1 on the mis-sized bundles,
Phase 3 on 19 of 21, Phase 4 on the 9 zero-figure bundles and the two zero-`\bibitem` bundles. This
is intended: the gates are being built *because* the corpus is in the state they detect. The
validation suite will be red on the paper corpus for the duration, which `--scope substrate`
already handles for Lean waves (`VALIDATION_GATE_TOPOLOGY.md` §2).

**Publication is deferred further**, consistent with ADR-010 §C5 and the operator's standing
posture: the schedule is the flexible variable, the claim strength is not.

**Ratchet discipline applies to every new gate** — zero headroom, shrink-only, production-seeded
mutation, seam guard against a vacuous empty population, per
`docs/architecture/CHECK_AUTHORING_GUIDE.md`'s seven obligations.

---

## Alternatives considered

**Insert a new numbered stage for prose review.** Rejected on C1 — four verified consumers of the
stage numbering, one of which regenerates a shipped paper table.

**Build the prose reviewer first, since it is the operator-identified gap.** Rejected: it would
deposit its verdict in a fourth field that nothing writes, replicating the exact defect TODO-D5
names. The gap is real and is Phase 5; the ordering is what makes it work.

**Author all 21 charters first, as F-01 specifies.** Rejected as written. Three of five charter
fields already exist (C2), so the length half unlocks Gate 12 at transcription cost, while the
section/figure half is authoring that is better informed by Phases 1–3's measurements.

**Defer everything until the roster number is settled.** Rejected: Phase 1's output is *evidence
for* that decision, so waiting inverts the dependency.

---

## References

- `docs/audits/2026-08-01-publication-readiness/CROSS-absorbability-and-strategy-drift.md` §4, §5
- `docs/audits/2026-08-01-publication-readiness/PROSE-QUALITY-BASELINE.md`
- `docs/architecture/END_TO_END_MAP.md` §8 — the promotion-path state machine
- `docs/architecture/VALIDATION_GATE_TOPOLOGY.md` §5 — enforcement reality
- `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` — D5, D7, D18, D24
- `docs/adrs/ADR-010-publication-portfolio-reassessment.md` §D3, §D6, §D7
- `docs/architecture/CHECK_AUTHORING_GUIDE.md` — the seven obligations every new check owes
- `docs/WAVE_EXECUTION_PIPELINE.md` — the process law, rewritten by Phase 7
- `docs/WAVE_PIPELINE_RATIONALE.md` — created by Phase 7; the provenance behind each pipeline rule
- `.claude/plugins/skeft-qa/tests/test_plugin_surface.py` — created by Phase 8; pins the
  plugin-surface-to-README contract that had silently drifted
