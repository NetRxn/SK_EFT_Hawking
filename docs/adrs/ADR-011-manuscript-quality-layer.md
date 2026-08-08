# ADR-011 — The manuscript-quality layer and the reviewer promotion path

- **Status:** 📋 **PROPOSED (2026-08-08).** Build authorized by the operator 2026-08-08
  (*"approved to build"*), with three standing directions that shape the plan below:
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

**2. `bundle_reader_facing_voice` — the review/revision narration class only** (76 hits).
`Stage 13`, `adversarial review`, `round-N`, `the audit found`, `BLOCKER`, `previously read`,
`an earlier draft`, `⚠`, `scope correction`. This is not a style judgment but a **category
error**: the manuscript addressing the review process instead of a reader. The fix is deletion,
with no version of "keep it" that is correct, which is what keeps it on the deterministic side of
the operator's line. It is also the pattern that accumulates *between* agent reviews, one deposit
per remediation round — so it is a regression guard, which an agent run cannot be.

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
2. **F-02** — `bundle_append.py --charter-section`, validated against the charter. **Registering a
   source must never create a section.**
3. **F-03** — §6 becomes figure *realisation*; `\figuredeferred{id}{reason}`; Stage 9 stops passing
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

1. **F-07** — track Lean-module mtimes (the data already exists: `bundle_append.py --lean-modules`
   writes to `append_log.json`); promote to FAIL at the submission gate.
2. **F-08** — branch **D.0**: *target unsound → home the work, do not absorb.* Decouples homing
   from absorbing so a defective bundle stops growing.
3. **F-09** — per-phase mapping rows, not per-bundle.
4. **F-10** — `bundle_lean_module_coverage`: declared modules must appear in the draft.

### Phase 8 — the `skeft-qa` plugin is reviewed and synchronised to intended state

**Added by operator direction 2026-08-08**, on noticing staleness in `skills/wave-close/SKILL.md`
and `skills/sync/SKILL.md` while reviewing the shared-reference design. Scope is the whole
plugin — `agents/`, `commands/`, `hooks/`, `scripts/`, `skills/`, `tests/`, `README.md` — for
architecture alignment and synchronisation, not just the two files that prompted it.

**Measured against the `plugin-dev` skill's own criteria** (loaded 2026-08-08 at operator
direction, so the review runs against published best practice rather than assumption):

| skill | body words | 3rd-person description | 2nd-person in body | broken `references/` links |
|---|---:|---|---:|---|
| `goal-prompt` | 2,784 | **NO** | 1 | **2** (`lab-notebook.md`, `parallel-worktrees.md`) |
| `harvest` | 1,105 | **NO** | 0 | — |
| `goal-dev` | 966 | **NO** | 0 | — |
| `sync` | 665 | **NO** | 0 | — |
| `debrief` | 591 | **NO** | 0 | — |
| `wave-close` | 483 | **NO** | 0 | — |

Three findings fall straight out, and the third is a genuine defect rather than a style note:

1. **No skill uses the third-person description form.** `plugin-dev` requires
   *"This skill should be used when the user asks to …"* with concrete trigger phrases, because
   the description is what decides whether a skill loads at all. Six of six miss it.
2. **`goal-prompt` is 2,784 words** against the 1,500–2,000 target, with `references/` already
   present — the progressive-disclosure split exists but was not used.
3. **`goal-prompt` names two reference files that do not exist.** `references/lab-notebook.md`
   and `references/parallel-worktrees.md` are cited in the body and absent from disk. This is
   the same failure class as a chain-of-backing link naming a theorem that is not there
   (TODO-B4), and the same class as `PRE_DECISIONS.md` naming a slash command never built — a
   mandatory-read document promising material that does not exist.

⚠️ **This phase is a review, not a rewrite.** The four skills at 483–1,105 words are within
budget and their content is not in question; what is stale is metadata, cross-references and
alignment with the tree. Findings that require content changes get filed, not fixed in passing.

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
