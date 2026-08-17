# Wave Pipeline — Rationale

**Companion to [WAVE_EXECUTION_PIPELINE.md](WAVE_EXECUTION_PIPELINE.md). That document states the
rules; this one records why each exists.**

Read this when a rule looks arbitrary, when you are considering an exception, or when you are
about to rebuild something the project already tried. Every entry below is a rule that was paid
for: an incident, an audit finding, or a measurement. None of it is needed to *follow* the
pipeline, which is why it lives here and not in the law.

Entries are keyed to the stage or invariant they explain.

---

## Stage 3a — the strengthening discipline

The checklist exists because first-pass theorem statements recur through six anti-patterns
catalogued in the memory `feedback_post_wave_strengthening_audit.md`. The cross-module bridge item
comes from `feedback_python_lean_refs_drift.md`: a docstring cross-reference not backed by an
actual call in the proof body rots silently.

**Measured effect (wave 6b.1, 2026-04-27):** applying the checklist prospectively reduced
strengthening cost from 12 retroactive theorems (the 6c.3 baseline) to 5, a 58% reduction. It did
not reach zero. The discipline catches the obvious patterns (∃-absorption, biconditional tautology
in conditional violators) and misses subtler ones: identity-function wrappers
(`theorem foo (h : P) : P := h`), within-own-±2σ-band tautologies (vacuously true for any positive
σ), pairwise-distinctness on inductive constructors (decidable from the inductive structure alone),
and definitional-unfolding-as-physics (`0.34 = 2 × 0.17`).

**That is why both passes are mandatory.** The post-wave review is the safety net for the classes
the prospective checklist provably does not catch.

## Stage 3a — the antipattern list

Every item on it is documented to have failed or corrupted a session:

- **Heartbeat overrides in proof bodies** — see Invariant 10 below.
- **`ring`/`ring_nf` on non-commutative rings** — `Uqsl2Aff`, `Uqsl3` and `RingQuot`-based types
  are `Ring`, not `CommRing`. Relatedly, when `rw` fails with "did not find pattern" on a
  `RingQuot` type, use `erw`: the pipeline's `rw` operates at `.reducible` transparency where
  `RingQuot` instances are not definitionally reducible
  (`Lit-Search/Phase-5p/RingQuot's typeclass diamond breaks rw at reducible transparency.md`).
- **Monolithic `simp`/`simp_rw` over 50+ terms**, and `simp_rw` with rules that can cycle (the
  Serre relation in both directions loops forever).
- **`match_scalars` at the wrong decomposition level** — when cancellation is inter-atom rather
  than per-atom it produces an unprovable `⊢ 1 = 0`.
- **Blind `lake build` iteration on hard proofs** — the MCP loop is roughly 1000× faster per cycle
  and shows live goal state. Installing MCP is always cheaper than grinding on `lake build`.

## Stage 4 — why the submission process was rewritten

Until 2026-06-25 Stage 4 uploaded the full project and applied results with a blind whole-file
`--integrate`. [ADR-006](adrs/ADR-006-aristotle-submission-rewrite.md) replaced this with partial
submission (the target's transitive import closure only) plus verify-then-graft with auto-revert.

The old implementation is archived at `scripts/archive/submit_to_aristotle.py`. It is retained
**only** as the Methods-of-record for papers that were produced under it, and must not be
re-enabled for new work. Its CLI took `--priority` / `--integrate` / `--resume` flags; the current
CLI is subcommand-based. If you find those flags quoted anywhere as live instructions, that text
predates ADR-006 and is wrong.

**On the toolchain gap:** Aristotle runs Lean/Mathlib 4.28.0 while this project runs the pin in
`lean/lean-toolchain` (with Mathlib and PhysLib matched in `lean/lakefile.toml`), which is ahead
of it. This is a known and tolerated risk rather than a
blocker, because the verification gauntlet rejects anything that does not build and kernel-verify
on *our* toolchain. A version mismatch therefore costs a run, not substrate integrity. No local
4.28.0 pre-build is required.

## Stage 5 — why the clean-rebuild command is so specific

Before 2026-04-22 the published clean-rebuild procedure was a bare `lake build`. That produced a
silent gap: the build succeeded with the library alone, `ExtractDeps.olean` was never produced, and
downstream checks expecting `lean_deps.json` failed for reasons that looked unrelated to the
rebuild. An attempted fix — adding `extractDeps` to `defaultTargets` — triggered a macOS
argument-length link failure. The single explicit command in the law is the resolution of both.

## Stage 8 — why figure adequacy is checked at all

The bundle-lift procedure only ever *migrated* figures that already existed. Nothing ever asked
whether a bundle had the figures its tier owes a reader, so **9 of 21 bundles shipped zero
figures**. Neither Stage 9 nor `paper_provenance` could object: both are vacuously true over an
empty figure set. Added ADR-011 Phase 4.

## Stage 9 and Stage 13 — why verdicts are written by a script

Until 2026-08-08 **no code path wrote `green` to any `stage*_status` field.** Creation set
`pending`, and `bundle_append.py` demoted `green` back to `pending`. Every green in the corpus was
therefore a hand edit, and bundle status could not be read as evidence that a review had happened.
`scripts/record_review.py` closes that gap (ADR-011 Phase 2); `bundle_reviewer_stage_ordering`
catches a hand edit that bypasses it.

The `--kind` requirement on Stage-13 verdicts exists because a targeted attribution sweep and a
full fresh-context pass are different evidence, and the metadata previously could not tell them
apart. Only `full-adversarial` earns a green.

## Stage 10 — why there is no Stage 10a, and no renumbering

Stage 10 acquired two review sub-gates (the read-through and the claims review). The obvious
move — promoting them to numbered stages — is forbidden, because **stage numbers are load-bearing
in four places**:

1. `scripts/paper_tables/sources.py:pipeline_stages()`, which regenerates paper 15's Table 1
2. `gate_precheck.py`'s stage vocabulary (`s9`, `s10`, `s13`, `s13-lean`, `submission`)
3. the `stage{9,10,13}_status` metadata fields across all bundles
4. every document that cites "Stage 13"

Renumbering would silently invalidate all four. `BUNDLE_LIFT_PROCEDURE.md` §9 and
`gate_precheck.py s10` use "Stage 10" as shorthand for the claims sub-gate specifically; that is
the same stage narrowed to its exit condition, not a second Stage 10.

## Stage 10 — why a dispatch brief must name each claim's origin

A brief is an instruction, not a deliverable. No gate reads it, no reviewer audits it, and the
pipeline's controls all sit downstream of it — so a wrong premise in a brief is discovered only after
a drafting agent has read sources and formed prose against it.

The receiving side was already built to survive this: `paper-drafter` ranks a reading rule above its
brief and is required to report contradictions between the brief and the sources. That detection
works. It is simply the *only* control, so every brief defect is paid for at full dispatch cost.

Naming the origin is the counterpart that acts while the brief is being written. It is self-checking
rather than enforced: a claim whose artifact you cannot name is a claim you did not verify, and the
sentence is where that surfaces.

Measured on the D9 dispatch, 2026-08-17, and recorded in that dispatch's own filed finding —
`papers/AutomatedReviews/2026-08-17-d9-stage10-redraft/D9.md` §3. The brief asserted a manuscript
contained fifteen `\texttt` spans, and concluded from it that a 169-reference audit population could
not be prose. The receiving agent measured it: fifteen literal `\texttt` spans, but **196** `\lean{}`
spans over **176 distinct declaration names**, because `\lean` is defined as `\texttt{#1}` in the
preamble. The prose population is 176, so the audit figure was consistent with prose all along. The
brief had warned against token-level scans two paragraphs above the claim that a token-level scan
produced.

The rule is owned by the `paper-authoring` skill's `references/dispatch-brief.md`; Stage 10 names it
rather than restating it, per ADR-011 D3.

## Stage 10 — why the prose rules are exactly these two

**The em-dash rule is a trust signal, not a style preference.** An em-dash reads as AI authorship
to a 2026 reader and costs credibility, so the target is zero rather than a density. Removing one
is a rewrite, not a substitution: an em-dash usually marks a sentence doing two jobs.

`--` is a *different character* and is **mandatory** — `Bose--Einstein`, `Schwinger--Keldysh`,
`Kaul--Majumdar`, page ranges. At the ADR-011 Phase 3 sweep the corpus held 741 em-dashes and
1,121 en-dashes; all 741 were removed and all 1,121 left untouched. The check cannot see a
*broken* en-dash, which is why that half of the rule lives in the authoring reference where a
human reads it.

**Why the deterministic set stops at two rules.** Everything else about prose belongs to the
read-through reviewer. This was measured, not assumed: a proposed vocabulary denylist produced 90
hits of which 48 were legitimate subject matter in the methodology paper, and a generic AI-slop
denylist produced 11 hits across 20 markers with 17 markers at zero. A check with that
false-positive rate trains authors to ignore it.

## Stage 10 — why manuscript length has a floor as well as a ceiling

The ceiling catches a letter that became a monograph. The **floor** catches the failure this
corpus actually exhibited: a container declared as a deep paper whose content is a letter. Neither
bound was measured anywhere before 2026-08-08 — `compile_bundle_pdf.py` computed the page count
and discarded it — which is how two Tier-1 bundles were closed GREEN at a small fraction of their
declared target. Added ADR-011 Phase 1.

## Stage 12 — why the hand-maintained inventory was removed

Until 2026-08-13 this stage mandated maintaining a 319 KB hand-written inventory and its index:
a four-step maintenance procedure, a *what to update* table naming both files, and a six-item
*watch for* list. Its gate was **"manual spot-check of three count-sensitive files."**

**Nothing mechanical asserted any of it.** Measured before removal: zero checks referenced the
Inventory's §1 or §2 or its `Last synced` date. So the enforcement for a hand catalogue of the
whole system was a hand-run sample of three files, and the outcome was exactly what that
predicts — the Inventory's largest section named 85 of 2040 live Lean modules (4.2%), and the
Index's narrative had gone two months stale beside a generated table that was fresh.

That last detail is the generalisable one, and it is why the pair was replaced rather than
repaired: **a half-generated document inherits the credibility of its generated half.** The
Index's AUTOGEN block was current; the prose around it claimed a theorem count roughly half the
generated one and asserted this repo has no `CLAUDE.md`. Every gate was green, because every
gate looked only inside the markers.

`docs/MODULE_CENSUS.md` (ADR-013) is generated in whole from module docstrings, so there is no
hand-edited region for that failure to recur in, and the fix for a bad description is a better
docstring rather than a parallel prose file that drifts. Three of the four legs that guarded the
Index have no counterpart, because the hazards they guarded cannot occur in a wholly generated
file — see `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` §2.1.

**The lesson is not "people should have been more careful."** It is that a rule requiring
sustained hand-maintenance of a derived-in-principle artifact will be broken, and a gate that
samples three files cannot see it. Where the content can be derived, derive it; where it cannot,
gate it mechanically.

## Stage 13 — why the stage exists

The April 2026 external adversarial-review round found a 13-dimension problem space that had
passed the entire 12-stage internal pipeline. Stage 13 is the fresh-context backstop for failure
classes that the internal stages cannot detect by construction. `docs/READINESS_GATES.md` is the
canonical definition of the 11 readiness gates it backstops.

**Why citation findings are unconditional blockers.** In the paper40 round-1 incident a
hallucinated `CalmetCapozzielloPryer2019` arXiv ID resolved to an unrelated graph-neural-network
paper. Without a content-layer cache, an agent can confabulate a plausible-but-wrong citation from
training-data context. Two layers now prevent it: the metadata cache
(`docs/citation_verifications.jsonl` + `scripts/citation_cache.py`, which amortizes Crossref/arXiv
resolution to at most once per 90 days per bibkey) and the primary-source content cache
(`Lit-Search/Phase-X/primary-sources/`), enforced by `citation_primary_sources_present`.

## Stage 14 — why proof-substance QI items may close only by structural prevention

`qi-leanproofsubstance` (closed 2026-04-29, Wave 4) and `qi-assumptiondisclosure` (closed
2026-04-29, Wave 5) were both closed via per-finding supersession. The 2026-06-13 whole-substrate
weakness audit found **both classes recurring** in modules that shipped after those closures (the
6n / 6e / 5q.B / 5x / 5z arc).

The lesson generalizes: per-finding supersession fixes the catalogued instances but leaves the
*generator* alive, so any failure class with a live generator recurs. Both were re-closed via the
standing ADR-004 gates (`proxy_body_audit`, `tracked_hypothesis_ledger`, `placeholder_not_cited`,
`formula_grounding`).

## Invariant 4 — why "content-grounded" replaced "named theorem exists"

The old check verified only that a *named* theorem existed, against a 7-function hardcoded map. A
formula could therefore be "grounded" on a theorem that proved nothing. This is the δ_diss-class
hazard: a 7-to-9-order dimensional error hid behind a reference that resolved to a placeholder
(audit 2026-06-13, finding 14). `formula_grounding` now checks all references for real,
non-placeholder targets.

## Invariant 9 — why placeholder citation is enforced twice

The 2026-06-13 audit (finding 3) found paper 7 presenting a `True := trivial` stub for a general-G
gauge-emergence equivalence as "end-to-end formal verification". The deterministic check
(`placeholder_not_cited`) matches the Lean declaration name and an optional published-claim
`tex_signature`. The claims-reviewer Class PC additionally catches the conceptual form, where a
paper names the claim in prose or math notation rather than by its Lean declaration name — the
paper 7 `Z(Vec_G) ≅ Rep(D(G))` case.

## Invariant 10 — why metaprograms are exempt and proofs are not

The distinguishing test is whether the work scales with the **number of declarations processed** or
with the **complexity of a single proof goal**. A proof can always be decomposed into smaller
goals. An environment walker cannot be decomposed into "walk fewer declarations", because walking
all of them is the requirement.

`ExtractDeps.lean` is the only file in the project currently claiming the exception. It walks every
declaration in the `SKEFTHawking` namespace, runs `collectAxioms` on each to compute transitive
axiom closures, and pretty-prints every type signature. Its `maxHeartbeats := 0` lives in the
`Lean.Core.Context` of its own `IO Unit` entry point and cannot leak into any theorem, because it
is a separate `lean_exe` rather than part of `lean_lib SKEFTHawking`.

## Invariant 16 — the honest scope limit

`tracked_hypothesis_ledger` auto-detects Prop-codomain `H_*` / `*Conjecture` / `*Hypothesis`
definitions consumed through a `(h : Name …)` binder. **Prop-valued struct fields are not
auto-enumerated** — for example `SmoothSpinManifold4.topo` (`2 ∣ σ/8`), whose codomain is not
`Prop` and whose name does not match the pattern. Those are covered case by case (`topo` via
`rokhlin_sigma_mod_16.dependent_theorems`), and `proxy_body_audit`'s `fun _ => _.field` pattern
catches struct-field-projection proof *bodies*. General struct-field-assumption auto-detection is
tracked debt (ADR-004 W7 finding H1).

The two-ledger predecessor state is why this invariant is written as "the single registry": the
prior arrangement kept two hand-maintained ledgers whose contents had become **disjoint** — a
latent drift bug found by the 2026-06-13 substrate audit (finding 2).

## Invariant 17 — why the negative front is machine-encoded

A no-go that is provably false makes the bad path *unprovable*, which is the robust and
self-enforcing form of a settled fork. Prose alone does not survive a fresh-context worker: an
agent with no shared history is the highest-risk re-deriver of an already-settled dead end.

Encoding it in `KERNEL_NOGO_REGISTRY` with a kernel-pure, non-vacuous backing theorem lets the
atlas surface it as a **negative frontier** through `atlas_view.json` →
`harness_common.antifrontier_from_atlas` → the SessionStart digest and `/skeft-qa:frontier`. Fan-out
is then steered away from dead paths by machine data rather than by a prose warning someone has to
remember to read.

**Scope is deliberately narrow.** Policy, route and preference bans are not *false*, cannot be
kernel-encoded, and remain governed solely by `docs/dev-loops/SETTLED_FORKS.md` prose (ADR-007 N-B).

## Invariant 15 — the axiom-count history

The pre-Phase-6p axiom count was 1 (`gapped_interface_axiom`, `SPTClassification.lean`). Phase 6p
added two (`bridge_axiom_FKLW`, `sk_axiom_Dawson_Nielsen`) on deep-research authority alone, which
is precisely what the sign-off policy now forbids. Both were retroactively scheduled for
substantive discharge via Phase 6p Waves 2c (Aharonov-Arad) and 2d (Dawson-Nielsen). Policy locked
2026-05-12.

---

## Where the rest of the history lives

| Kind of history | Document |
|---|---|
| Architecture decisions, with alternatives considered | `docs/adrs/ADR-0NN-*.md` |
| Per-claim verification records for a change | `docs/architecture/.working-docs/ACCURACY_LEDGER.md` |
| Known gaps not yet built | `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` |
| Paper-production process findings (System 1) | `docs/QI_REGISTER.md` |
| Dev-loop / harness process findings (System 2) | `docs/dev-loops/SYSTEM2_REGISTER.md` |
| Settled dead ends, prose form | `docs/dev-loops/SETTLED_FORKS.md` |
| Per-bundle content history | `papers/<bundle>/change_log.md` |
