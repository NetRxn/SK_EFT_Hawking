# H1 — Goal fit: is the QA/QI system the right SHAPE for producing publishable papers?

**Reviewer:** H1 (holistic architecture review, not defect hunt)
**Date:** 2026-08-05 · **Tree:** `db430c65`, worktree `rv1`
**Question:** not *"is it broken"* — *"does its coverage match what it exists to do."*

> **Stated purpose (operator):** the QA/QI layer exists so that *"the human in the loop reviewer is
> given greatest possible chance of successful review — if a referee of a high-impact journal would
> raise a concern, it shouldn't be something the user is left to discover on their own."*

---

## 0. Verdict on the working thesis

**SUPPORTED, and sharpened.** The thesis as handed to me was:

> the suite measures *internal consistency* extremely well and *content sufficiency and substrate
> attachment* not at all.

Both halves reproduce. But "not at all" understates the structural point, because it reads as an
omission. It is not an omission — it is a **consequence of a uniform logical form**, and that form
is shared by the validation suite *and* the readiness gates *and* the bundle aggregator:

> **Every content-facing predicate in the system is universally quantified over a population the
> draft itself supplies:  ∀x ∈ S(draft) . P(x).  Not one is existential (∃x ∈ S) or
> cardinality-bounded (|S| ≥ N). Every universal over ∅ is true.**

So the system cannot distinguish *"this bundle is correct"* from *"this bundle contains nothing to
be wrong about."* Worse than neutral: because every finding-counter is also population-derived, the
aggregator is **monotone in emptiness**. The single 🟢 GREEN bundle in the portfolio, D9, is 12 pp
against a ~40 pp charter, references **3** Lean modules, and had Stage 10 never run — and it is
green *because* of that, not despite it. The 2026-08-01 audit already put this in one line
(`CROSS-absorbability-and-strategy-drift.md`): **"The verdict function rewards emptiness."**

One correction to the framing I was given: the count is **60 checks**, not 59
(`uv run --no-sync python scripts/validate.py --list | grep -cE '^  [a-z]'` → 60 on `db430c65`).
`CLAUDE.md`, `QA_QI_INFRASTRUCTURE_MAP.md` §1 and `CHECK_AUTHORING_GUIDE.md` §2.4 all still say 59.
Minor, but it is a count in the docs that the artifact contradicts.

---

## 1. All 60 checks, classified by the QUESTION they answer

Axes refined from the suggested set. `readiness_submission_gate` is broken out because it answers no
question of its own — it aggregates the 11 readiness gates, and inherits their shape (§2.2).

| # | Category | Question the check answers | Count | Share |
|---|---|---|---:|---:|
| A | **Consistency / agreement** | do two artifacts state the same number/name? | **12** | 20 % |
| B | **Resolution / existence** | does a name mentioned here resolve to a real entity? | **13** | 22 % |
| C | **Freshness** | was this derived artifact regenerated from current sources? | **7** | 12 % |
| D | **Lean-statement substance** | does this theorem's *statement* prove anything? | **5** | 8 % |
| E | **Physics / numerics correctness** | is the computed value right? | **4** | 7 % |
| J | **Build & trust surface** | does it build; what does the proof trust? | **7** | 12 % |
| I | **Process / ledger hygiene** | was the bookkeeping done? | **9** | 15 % |
| H | **Presentation quality** | is the artifact legible / stylistically conformant? | **2** | 3 % |
| — | *aggregate* | `readiness_submission_gate` | 1 | 2 % |
| **F** | **Content sufficiency** | **is there enough of it?** | **0** | **0 %** |
| **G** | **Substrate attachment** | **does this bundle present the substrate it claims?** | **0** | **0 %** |

<details>
<summary>Per-check assignment (all 60, in <code>--list</code> order)</summary>

| Check | Cat | Check | Cat |
|---|:-:|---|:-:|
| `formulas` | B | `counts_fresh` | C |
| `placeholder_not_cited` | D | `tables_fresh` | C |
| `disclosure_consistency` | D | `claim_clusters_fresh` | C |
| `proxy_body_audit` | D | `numerical_literals` | I |
| `tracked_hypothesis_ledger` | B | `bundle_tables_use_pipeline` | I |
| `tracked_hypotheses_fresh` | C | `graph_integrity` | B |
| `formula_grounding` | B | `atlas_integrity` | A |
| `vacuous_statement_audit` | D | `atlas_hypothesis_discipline` | I |
| `nogo_substrate_integrity` | D | `count_literals` | I |
| `native_decide_regression` | J | `recurrence_reopens_closures` | I |
| `numerical` | E | `review_severity_declared` | I |
| `identities` | E | `review_docs_mint_findings` | I |
| `paper_table` | A | `accepted_findings_carry_rationale` | I |
| `d1_hierarchy_table` | A | `bundle_metadata_matches_graph` | A |
| `f_hierarchy_claims` | A | `notebook_stored_outputs_current` | C |
| `theorems` | B | `readiness_verdicts_agree` | A |
| `notebooks` | I | `readiness_submission_gate` | *agg* |
| `lean_source` | B | `citation_primary_sources_present` | B |
| `cgl_fdr` | E | `provenance_doi_in_registry` | B |
| `lean_build` | J | `bundle_consistency` | A |
| `axiom_closure_allowlist` | J | `bundle_source_freshness` | C |
| `elaboration_knob_watchlist` | J | `bibitem_title_primary_source` | A |
| `bundle_figure_integrity` | H | `quantum_network` | A |
| `viz_consistency` | H | `bundle_registry_consistency` | A |
| `notebook_exec` | J | `paper_latex_compiles` | J |
| `physical_bounds` | E | `axiom_count_prose_consistency` | A |
| `cross_path_consistency` | A | `prose_theorem_reference_coverage` | B |
| `paper_provenance` | B | `theorem_name_embedded_citations` | B |
| `parameter_provenance` | B | `inventory_index_autogen_fresh` | C |
| `lean_docstring_refs_resolve` | B | `paper_toolchain_pin_drift` | J |

</details>

### 1.1 What is thick, what is empty

**Thick (A+B+C = 32 of 60, 53 %).** *Agreement, resolution, freshness.* This is the drift-prevention
core, and it is genuinely excellent — 32 independent instruments guaranteeing that no two places in
the repo say different things and no derived artifact rots. For a project with 2,012 Lean modules,
40,262 declarations, 137 Python modules and 64 drafts, that is the right investment and it works.

**Also real (D+E+J = 16 of 60, 27 %).** Substance of Lean statements, physics correctness, and build
trust. `vacuous_statement_audit` / `proxy_body_audit` / `placeholder_not_cited` /
`disclosure_consistency` are, as far as I can tell, unusual in the formalization world — a suite
that mechanically asks *"does this theorem's statement carry content"* is a genuine asset and should
be said so plainly.

**Empty (F+G = 0 of 60).** No check anywhere answers *"is there enough of this"* or *"does this
bundle present the substrate it advertises."*

### 1.2 The four near-misses — checks that look like F/G and are not

These matter because they are what makes the gap invisible.

1. **`prose_theorem_reference_coverage`** looks like substrate attachment. It is resolution (B). It
   iterates `for bundle in BUNDLE_CODES` (`scripts/validation/checks/prose_lean_refs.py:532`) and
   accumulates `n_candidates += len(by_token)` (`:548`) **portfolio-wide**. A bundle whose
   `by_token` is `{}` contributes zero details and zero to every counter. **I ran it:** it fails
   today (83 unresolved refs over the frozen ceiling of 79) — and every single failing line names a
   *legacy* draft (`paper44_riemannian_connection`, `paper26_bh_entropy`, …). It emitted **nothing
   about D12, which references zero Lean modules**, nor D10 (3), nor D7 (4). The check ran, saw the
   most substrate-detached bundles in the portfolio, and had nothing to say. Its closing banner read
   `✓ SUBSTRATE: clean`.

2. **`bundle_figure_integrity`** looks like presentation coverage. It iterates the figure specs that
   *exist*, filtered to `d11_`/`d12_` prefixes (`bundles_readiness.py:132`). It enforces an 8.0 pt
   legibility floor on 7 figures. **Nine of 21 bundles ship zero figures** — F, D1, D2, D3, D4, D6,
   D7, D10, I3 (my measurement: `\includegraphics` in the body of each `paper_draft.tex`) — and the
   check is structurally incapable of noticing, because zero figures means zero specs means zero
   iterations means pass.

3. **Gate 1 CitationIntegrity** looks like citation coverage. `readiness_gates.py:165` has an
   explicit early return: `if not bibkeys: r.state = 'passed'; r.notes = 'no bibitems'`. **D8 and
   D10 have zero `\bibitem` in their drafts** (my count) — they are clean CitationIntegrity passes.

4. **`paper_provenance`** — the fourth case, and the branch already found and fixed it, which makes
   it the best available proof that the shape is real rather than my inference. Its theorem-reference
   leg was deleted as dead code on 2026-08-05 (QI-32): the regex could not cross the `\_` LaTeX
   escape, so across all 64 drafts it saw **480 raw matches, 0 usable**. Per its own docstring, it
   *"FAILED loudly on nothing for five months while printing 'N theorem references verified' for
   zero references."* Same shape, one level down: a count of what was scanned, mistaken for evidence
   that the population was reached.

The pattern is identical in all four: **the check verifies the quality of what is present and is
blind by construction to what is absent.** That is a correct design for a drift detector and the
wrong design for a submission gate.

---

## 2. Mapping the coverage against what actually blocks publication

Source: `docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md` §3 (six defect classes, 80 P0
findings), `REMEDIATION_PLAN.md`, `readiness_gates.py`, `bundle_readiness.py`.

### 2.1 The six defect classes vs. the 60 checks

| Class (SYNTHESIS §3) | Severity | Checks that address it | Mechanizable? |
|---|---|---:|---|
| **1 — Claim/substrate divergence** (found by all 10 bundle auditors; the reputational risk) | 🔴 highest | ~6 partial | **partly** |
| **2 — Duplication / self-competition** (D6∩D9 = 78 theorems; D4§9 vs D8 priority dispute) | 🔴 high | **0** | **yes, cheaply** |
| **3 — Referee-facing scar tissue** (F's checkbox tracker in the PDF; agent tool budgets as content) | 🟠 high | **0** | **partly** |
| **4 — Length and structure** (39 % of charter; 9 bundles zero figures; 0/21 data-availability) | 🟠 high | **0** | **yes, trivially** |
| **5 — Mechanical** (compile errors, stale PDFs, pin drift, literals) | 🟡 lowest | **~12** | yes — and mostly done |
| **6 — Un-homed work / dead absorption** (1,403–1,633 of 2,039 modules in no draft) | 🔴 high | 1, **vacuous for 9 bundles** | **yes** |

**The single most important line in this report:** *check coverage is inversely correlated with
defect severity.* The least severe class (5 — Mechanical) has ~12 instruments and is now largely
clean (21/21 compile). The three most severe classes (1, 2, 4/6) have between zero and one, and the
one is the instrument ADR-010 M6 found returning `fresh: all 1 source paper(s)…` over **zero
measurable sources** for nine bundles.

This is not evidence of neglect. It is the natural attractor of an incremental defect-driven build:
**every check in this suite was written in response to a defect that had already escaped**, so the
suite's shape is the shape of the escapes that were *noticed* — and mechanical escapes are the ones
a machine notices. The classes that require reading a draft never generated a mechanical trigger, so
they never generated a check. The system optimised faithfully for the wrong loss function.

### 2.2 The readiness gates: vacuity is systemic, not incidental

I had `readiness_gates.py` read in full. Of the 11 gates, **9 return `passed` on an empty input
population**, and the two exceptions are partial:

| # | Gate | P | can `blocked`? | empty population ⇒ |
|---|---|:-:|:-:|---|
| 1 | CitationIntegrity | 1 | ✅ | **passed** — explicit `if not bibkeys` branch (`:165`) |
| 2 | CrossPaperConsistency | 1 | ✅ | **passed** (`:227`) |
| 3 | ParameterProvenance | 1 | ✅ | `open` iff inline literals present, else **passed** (`:279`) |
| 4 | ComputationCorrectness | 1 | ✅ | `open` — *the only originally-honest gate* (`:393`) |
| 5 | LeanProofSubstance | 1 | ✅ | **passed** — set-intersection, ∅ ∩ X = ∅ (`:453`) |
| 6 | AssumptionDisclosure | 1 | ✅ | **passed** — explicit branch (`:502`) |
| 7 | NarrativeGrounding | 1 | ✅ | `open` iff `\begin{abstract}` present, else **passed** (`:541`) |
| 8 | ProductionRunHealth | 1 | ✅ | **passed** (`:609`) |
| 9 | NumericalFreshness | 2 | ❌ | **passed** (`:693`) |
| 10 | FirstClaimVerification | 2 | ❌ | **passed** (`:725`) |
| 11 | FixPropagation | 2→1 | ✅ | **passed** — *"never reviewed" and "reviewed clean" are the same green* (`:797`) |

**An empty bundle scores 9 `passed` + 2 `open` → YELLOW. An empty bundle with no `\begin{abstract}`
block and no inline literals scores 11/11 `passed` → GREEN.**

Two consequences worth stating explicitly:

- **Gate 5 LeanProofSubstance is the substrate-attachment gate the architecture *implies* exists.**
  Its predicate is *"cited theorems ∌ PlaceholderMarker."* It is a set-intersection emptiness test,
  so a bundle citing zero theorems passes maximally. It also still discovers theorems by `\texttt{}`
  only (`readiness_gates.py:430`) — **the identical blind spot that commits `c7148779` /
  `c5f384b4` fixed in `prose_theorem_reference_coverage` (564 references) was not propagated here.**
  D6 (`\verb`), D8 and D9 (`\lean{}` alias) are substantially invisible to their own P1 substance
  gate. That is a concrete, unfiled finding, and it belongs to R1's population-reach question as much
  as to mine.
- **`bundle_readiness.aggregate_by_bundle` (`:370-377`) takes no content input at all.** Every term
  is a `ReviewFinding` counter. The 2026-06-10 S5 patch added `review_recorded`, which requires that
  a dated review *file exists* — not that it examined anything. The `blocked_p1_gates` downgrade
  (`:383`, `:390`) is inert exactly where it would matter, because an empty bundle blocks no P1 gate.

The heatmap makes this legible at a glance: **17 RED / 3 YELLOW / 1 GREEN**, and the verdict is
monotone in *reviewer attention*, not readiness. D12 is RED because a reviewer wrote 148 findings
about it; D9 is GREEN because nobody did.

### 2.3 Per blocker: is a check possible?

| Blocker | Check exists? | Mechanizable? | The check that should exist |
|---|---|---|---|
| Bundle at 8–39 % of charter (D7 3 pp, D10 5 pp) | no | **yes, trivially** | `bundle_charter_fill` — parse the `Length` column of `PAPER_STRATEGY.md` §6 (a real markdown table), read `kMDItemNumberOfPages`/`pdfinfo` off the built PDF, fail below a fraction. **Both halves already exist**: ADR-010 M1 wrote the charter parser, and `scripts/compile_bundle_pdf.py:105-112` already computes `pages` — and then drops it, because `ok` at `:114` never references it. |
| Density-gamed length (D3 at 205 w/pp vs corpus 550) | no | **yes** | same check, second leg on words/page — ADR-010 M1(d) shows page count alone scores the stitched lift as the healthiest bundle |
| Bundle references 0–4 Lean modules (D12/D10/D7/D6) | no | **yes** | `bundle_substrate_attachment` — per-bundle floor on resolved declaration references, and the inverse ledger of un-homed modules. `SYNTHESIS.md` §5 names this `bundle_lean_module_coverage`; **it does not exist** (ADR-010 M2 confirms it is a proposal). Note `bundle_metadata.json` already carries a `lean_modules_referenced` field — written by `bundle_append.py:299`, `[]` on disk for every bundle, read by nothing. A dead field where the gate should be. |
| 9 of 21 bundles ship zero figures | no | **yes, trivially** | `bundle_figure_floor` — extend `bundle_figure_integrity` from "the figures present are legible" to "a bundle at tier ≥1 has ≥N figures" |
| 0 of 21 data-availability statements | no | **yes, trivially** | regex for the required statement blocks |
| D6∩D9 = 78 shared theorems | no | **yes, cheaply** | `bundle_substrate_overlap` — pairwise intersection of resolved declaration references + 8-gram shingle overlap. ADR-010 M4 already computed it; it is ~40 lines |
| Scar tissue (F's rendered checkbox tracker, agent tool budgets, "Stage 13 round 7") | no | **partly** | `paper_process_leakage` — regex for `round \d+`, `Stage 1[0-4]`, `localhost:`, `\item\[ \]`, "tool calls". Catches the mechanical half; voice needs an LLM |
| Manuscript asserts what the Lean does not say (D2 `rank = rank`, D4 `Real.log_pos_iff`) | **partial** | **partly** | `vacuous_statement_audit` + `disclosure_consistency` are the right mechanism and exist. Residue: the *semantic* half — "the theorem is non-vacuous but says something else" — is **irreducibly LLM judgement** |
| D5 enumerates 8 taxonomy labels; the Lean inductive has 7 constructors | no | **yes** | `prose_constructor_enumeration` — every constructor name a draft enumerates for a named inductive must exist in it. Narrow, but this exact class recurred |
| I1 claims an Aristotle batch with no run ID | no | **yes** | cross-check prose Aristotle claims against `ARISTOTLE_THEOREMS` (322 entries, 44 runs) |
| "First formalization in any proof assistant" (D10, I2, D2, D8) | no | **no** | irreducibly human/LLM — a claim about the external record |
| L1 misattributes a claim to a living author | no | **no** | irreducibly human — requires reading the cited paper |
| Citation *content* (does the cited work support the sentence?) | no | **no** | `bibitem_title_primary_source` verifies the title matches the cached PDF's page 1 — that is as far as mechanism reaches |

**Score: of ~13 distinct blocker families, 9 are mechanizable and 8 of those 9 have no check.**
Only three are genuinely irreducible (external-record priority claims, misattribution, citation
content). The "it needs human judgement" framing covers far less of the gap than it appears to.

---

## 3. The central design question: deliberate boundary or backlog?

`VALIDATION_ARCHITECTURE.md` §6 is four lines:

> - It does not verify **figure content**, recompute **paper-quoted numbers** from their formulas,
>   check that a **cited theorem's statement** supports the prose, or verify **citation content**.
>   Those are absent checks (pass-1 R5-C2…C5), routed to ADR-010.
> - It does not run in CI. There is deliberately no scheduled runner.

**Verdict: the second bullet is a principled boundary. The first is a backlog wearing a boundary's
clothes — and it is scoped to about a third of the actual gap.**

Three independent reasons.

**(a) The list is not the gap.** §6 names four things. It does not name content sufficiency, does
not name substrate attachment, does not name duplication, does not name process leakage. Those are
the classes that produced the C− verdict. A scope statement that omits the largest omission does
not function as a boundary — it functions as reassurance. Contrast the second bullet, which cites
a specific assessment document for *why* CI is declined. The first cites a destination, not a
rationale. **"Routed to ADR-010" is a forwarding address, not a decision.** The QA map's own §7
already names this failure mode in a different context: *"'Publication workstream' had become a
disposal chute for decisions not yet made (audit finding QI-22)."* §6 is the same chute one level up.

**(b) The suite's own authoring guide already prohibits the pattern — one aggregation level too
coarse.** `CHECK_AUTHORING_GUIDE.md` §2.5 says exactly the right thing:

> **Guard the seam — a scan that matches nothing passes vacuously.** Any check that greps, globs or
> walks needs a companion assertion that the population is non-empty and plausible.

The obligation exists. But it is written against a *broken instrument* (a regex that stopped
matching), so the population it protects is the **portfolio-wide** one. For
`prose_theorem_reference_coverage` the portfolio aggregate is 1,051 references — non-empty and
plausible — while D12's per-bundle population is 0. **The system's own anti-vacuity rule is one
level of aggregation too coarse to see the vacuity that matters.** That is not a philosophical
boundary; it is a scoping bug in a rule the project already believes in. Extending §2.5 from *"the
scan found something"* to *"the scan found something in every unit the verdict is reported per"* is
a one-sentence change that reclassifies most of §6's residue as in-scope.

**(c) Nothing else owns it today.** I had the LLM-agent layer, the Stage-9/10/13/14 wiring and the
review-artifact reader inventory swept independently. Every candidate owner fails, and they fail the
*same* way.

**The LLM agents are falsification engines, and falsification is orientation-locked.** All three
agents — `figure-reviewer` (4 classes), `claims-reviewer` (6: IA/TP/SD/TN/HD/PC), `adversarial-reviewer`
(8, one per readiness gate) — take what the draft asserts and resolve it against the substrate.
Not one class is triggered by an *absence*. `figure-reviewer`'s scope is literally *"for each figure
in the manifest"*; `claims-reviewer`'s walk is *"sentence-by-sentence from top to bottom"*;
`adversarial-reviewer` describes itself as finding *"every way a paper can be **wrong**."* The
consequence is stark and worth stating as a test case:

> **A one-paragraph `paper_draft.tex` with zero citations, zero Lean references and zero numbers is
> a clean review from all three agents and a clean 60-check `validate.py` run.**

One agent instruction cuts explicitly *against* sufficiency — the Tier-2 profile in
`claims-reviewer.md:85`: *"do not penalize absent broader scope."* Sensible for a 4 pp letter;
there is no counterpart anywhere raising a floor for a 40 pp deep paper.

**The pipeline's own Stage gates are unread.** `stage9_status` and `stage10_status` have **zero
consumers** — written by `bundle_source_manifest.py:129-131` and demoted by `bundle_append.py:322-325`,
read by nothing. `last_stage9_review` / `last_stage10_review` are written as `None` and never read.
`stage13_status` has exactly one real guard (`bundles_readiness.py:321-326`) and it fires on
`green`-with-open-blockers — **never on `pending`**, i.e. never on an unreviewed bundle. Stage 9's
gate (*"All figures PASS LLM review"*) lives entirely in `figure_review_report.json`, whose only
reader is the dashboard. `gate_precheck.py` runs *before* dispatch as a cost guard; there is no
post-dispatch proof-of-run, and no `Stop`/`SubagentStop` hook exists. Stage 13's gate *is*
machine-checked (`readiness_submission_gate`, genuinely repaired 2026-08-03) — and is vacuously
satisfiable, because its predicate is *zero unfixed BLOCKERs among findings that exist*.

**Review staleness is not measured.** `READINESS_GATES.md:258` says so outright: *"the heatmap
performs no edit-date comparison."* The two proxy signals (`stage13_redo_required`, `freshness_stale`)
both key off **`last_lift`**, not the draft's mtime and not the review date — so a bundle edited *in
place* after its Stage-13 review trips nothing. 15 of 21 heatmap rows carry the same 2026-06-10 date;
three (D6, D11, D12) were *backfilled* from on-disk evidence rather than recorded at review time.

**And the instruments that would close the gap exist, unwired.** This is the finding I would act on
first. Five separate mechanisms already produce the right answer and reach no verdict:

| instrument | produces | consumers |
|---|---|---|
| `scripts/chain_canonicalize.py --report` | 3,442 chain links, 87 % resolved, 121 `theorem-absent`; **F and I3 have zero links — the flagship has no chain-of-backing at all** | **none that can block** (QA map §8; `REMEDIATION_PLAN` §5b) |
| `scripts/compile_bundle_pdf.py:105-112` | `pages` per bundle, via `pdfinfo` | dropped — `ok` at `:114` never references it |
| `bundle_metadata.json` `lean_modules_referenced` | intended per-bundle module inventory | written `[]` by `bundle_append.py:299`; **read by nothing** |
| `PAPER_DEPENDENCIES` (`src/core/provenance.py`) | the one *required*-substrate list in the repo — the right **shape** | cited in `claims-reviewer.md:521` prose only; **no check under `scripts/validation/` reads it**. ⚠️ **I re-measured it rather than inheriting "just wire it": 17 entries (of 64 papers / 21 bundles), each declaring ~3 `lean_modules`.** Wiring it as-is would gate almost nothing — the residue is *population*, not plumbing |
| `docs/agents/claims-reviewer-bundle-prompts.md` anchor lists | per-bundle *"load-bearing claims and citations the Stage-13 review must verify"* — the closest thing to a machine-readable charter | `review_runner.py:78` checks only that a `### <bundle>.` **heading exists**; anchors are never compared to draft content. (`review_runner.validate_review_doc`, the one coverage-shaped function in the layer, has **no caller at all**.) |

So the four §6 items and the larger unlisted gap fall through one hole: **an instrument that produces
the right answer but is not wired to a verdict is indistinguishable from an absent instrument.**

That is the most actionable thing in this report. **The cheapest path to closing the F/G gap is not
writing new instruments. It is wiring five that already exist** — and two of them
(`PAPER_DEPENDENCIES`, the anchor lists) are already *required-inventory* shaped, which is exactly
the orientation the whole layer lacks.

**The one-line diagnosis.** Every guard in this system is oriented **outward from the draft** — take
what the draft asserts, resolve it, fail on mismatch. Nothing is oriented **inward toward the draft**
— take a required inventory and fail on omission. F and G are not four missing checks. They are a
missing *direction*.

---

## 4. Is the three-layer story (Python ↔ Lean ↔ Aristotle) closed?

**Forward direction: genuinely enforced. Reverse direction: not enforced, not asserted, and it is
where 98 % of the substrate lives.**

Invariant 4 has two clauses, and they are unequal.

**"Every formula has a Lean theorem"** — *enforced, and well.* `formula_grounding` resolves every
`formulas.py` Lean reference against `lean_deps.json` and rejects placeholders; it is one of the
three checks the pre-commit hook actually runs. `formulas` and `lean_source` back it up. Measured:
**394 unique Lean names referenced from `src/core/formulas.py`.**

**"Every Lean theorem has a proof (zero sorry)"** — *enforced.* `counts.json`:
`sorry_declarations = 0`, `sorry_theorems = 0`, `axioms = 0`, guarded by `lean_build` +
`axiom_closure_allowlist` + `native_decide_regression`. This is the strongest part of the whole
system and deserves saying so: a 26,103-theorem corpus at zero sorry, zero project axioms, with a
mechanical no-go registry (`nogo_substrate_integrity`) is a real achievement.

**The reverse direction is not an invariant, and nothing measures it.** There is no clause saying
*"every Lean theorem serves a formula, a paper, or a declared purpose."* Quantified:

| population | count | share |
|---|---:|---:|
| Lean theorems (`counts.json`) | 26,103 | 100 % |
| …referenced from `formulas.py` | 394 | **1.5 %** |
| …proved via Aristotle (`aristotle_proved`) | 322 | **1.2 %** |
| Lean modules | 2,012–2,039 | 100 % |
| …reaching **no** bundle draft (ADR-010 M2, strict) | **1,633** | **80.1 %** |
| …reaching no bundle draft (loose, deliberately over-counts homed) | 1,403 | 68.8 % |

The 1,403–1,633 un-homed modules are exactly the reverse direction made visible. They are not a
defect in the Lean — they are kernel-verified and correct. They are a **portfolio** defect: work
that cost real effort and reaches no reader. The `PinPlus*` arc alone is **2,914 declarations across
180 modules with zero hits portfolio-wide**.

Two further gaps in the "closure" story:

- **Aristotle is a third layer in the architecture diagram and a registry lookup in the code.** The
  `theorems` check verifies that `ARISTOTLE_THEOREMS` entries *resolve to real declarations* — B,
  resolution — and it is *ratcheted*, i.e. it carries known unresolved debt. Nothing checks the
  converse (a paper claiming an Aristotle run has one), which is precisely how I1's *"all nine
  sub-lemmas closed in a single Aristotle priority batch"* survived to a draft with no run ID.
- **The Python↔Lean bridge is checked by name, not by content.** `formula_grounding` proves the
  *name* resolves and is non-placeholder. `quantum_network` is the one check that verifies a Python
  formula actually *satisfies* its Lean theorem's identities — one domain out of many. §6's "does
  the cited theorem's statement support the prose" is the paper-facing half of the same missing
  property, and the Python-facing half is missing too. **`quantum_network` is the template for what
  that check looks like when it is done right**, and it exists exactly once.

**Net:** the three layers are individually sound and pairwise attached by *naming*. The system
guarantees no dangling reference in either direction. It guarantees nothing about coverage in either
direction, and coverage is where the value is.

---

## 5. What will bite later — ranked by cost-of-delay

Ranked by (when it becomes expensive) × (how much harder it gets as content grows).

**1. Substrate attachment (G) — bites hardest, gets worse fastest.**
Today 1,633 modules are un-homed. The Lean substrate grows every wave; the drafts do not. The
homing decision for a module is cheapest **in the wave that builds it**, when the author knows why
it exists — and it is close to unrecoverable two years later, which is the state the `PinPlus*` arc
is already in (2,914 declarations, zero draft hits, and M3 records that *"a phase has no bundle
home" is not a machine-answerable question today* because there is no join key). Every wave shipped
without a homing gate adds permanently to a backlog that only a human who remembers the wave can
clear. **This is the one gap where delay destroys information rather than just deferring work.**
Mitigation is cheap and must be *at wave close*, not at bundle lift: a wave that adds N modules
declares their bundle target or an explicit `unhomed:reason`.

**2. Content sufficiency (F) — bites at the submission decision, and the gate must land before the
writing, not after.**
39 % fill is a writing problem, not an infrastructure problem — infrastructure cannot write D7's
missing 37 pages. But ADR-010 M1's mechanism finding is the reason this is urgent *now*: **the
charter page number is assigned by tier convention at authorization time, before any substrate is
measured** (nine of twelve D-tier bundles carry the identical `~40pp` charter). So the gap is
manufactured at *authorization*, and every new bundle authorized without a content floor
manufactures more of it. A `bundle_charter_fill` check is a few hours of work and both halves of it
already exist on disk. The expensive version is the one built after D13–D16 are authorized on the
same template.

**3. Vacuity of the gates themselves (§2.2) — bites silently, and the blast radius grows with the
roster.**
9 of 11 P1 gates green on ∅ means every *newly authorized, not-yet-written* bundle enters the
portfolio green-to-yellow and stays there until someone reviews it into RED. With 21 bundles and 12
of them Tier 1, the aggregate readiness signal is already inverted (D9 green, D12 red). Each new
bundle makes the heatmap less informative. **Fix cost is low and flat** — an
`unmeasured`/`NOT ESTABLISHED` state per gate, which the 2026-08-05 hardening of Gates 3 and 7
already prototypes, plus propagating the `\lean{}`/`\verb` fix into `readiness_gates.py:430`. Doing
it now is a one-day change; doing it after the gates acquire more consumers is an interface break.

**4. Duplication (Class 2) — bites at the roster decision, which is imminent.**
ADR-010 is *about* portfolio distribution. D6∩D9 = 78 theorems is the strongest single result
backing a merge, and D4§9-vs-D8 turned out to be a **priority conflict, not duplication** (3 shared
declarations, 0.1 % shingle overlap) — a distinction ADR-010 §C3 inherited wrong and that only a
measurement caught. Every roster decision taken without this instrument is taken on prose. **Cost
rises only if the merges happen wrong**, in which case it is rework of writing.

**5. Process leakage / voice (Class 3) — bites at referee contact, cheap to fix, easy to re-incur.**
Mechanically catchable half is a regex; the rest is the D11 rule (*correct claims silently*) which
is a discipline, not a check. Bounded cost, but it re-accumulates every review round, so it wants a
ratchet rather than a one-time sweep.

**6. Semantic claim/substrate correspondence — bites hardest per incident, and is the one that stays
human.** *"The theorem exists, is non-vacuous, and says something other than what the prose says."*
No mechanism reaches this. `chain_canonicalize` reaches the *name* half and is unwired (fix that
first — it is free). The residue is genuinely LLM/human, and it is where the claims-reviewer earns
its keep. Cost of delay is flat, but per-incident severity is the highest in the portfolio (L1).

---

## 6. Where the infrastructure is genuinely well-shaped

Stated plainly, because an even-handed read is more useful and because remediation depends on
knowing what not to touch.

- **The drift layer (32 of 60 checks) is excellent and I found nothing wrong with its shape.** For a
  repo of this size with this many derived artifacts, 32 instruments guaranteeing mutual agreement
  and freshness is proportionate and effective. `bundle_registry_consistency` — a check whose entire
  job is that a roster has exactly one home — is the kind of second-order instrument most projects
  never build.
- **The Lean-substance axis (D) is unusual and valuable.** `vacuous_statement_audit`,
  `proxy_body_audit`, `placeholder_not_cited`, `disclosure_consistency`, `nogo_substrate_integrity`
  mechanize *"does this theorem prove anything"* — a question most formalization projects answer
  only socially. Combined with zero sorry / zero axioms across 26,103 theorems, the substrate layer
  is the strongest part of the system and the §6 gap does not touch it.
- **The suite's self-knowledge is exceptional and, unusually, accurate.** `VALIDATION_ARCHITECTURE`,
  `GATE_TOPOLOGY`, `CHECK_AUTHORING_GUIDE` and the QA map name their own failure mode ("absence of
  measurement rendered as success"), track its population with a ratchet, mark their own retractions
  inline, and record the standing lesson *"a filed finding's blast radius is a claim, not a
  measurement."* That last rule is why ADR-010's re-measurement pass caught that the inherited "~340
  un-homed modules" was low by 4–5×. **A system that re-measures its own findings and publishes the
  correction is doing the hard part.** The gap this report names is not a failure of that culture —
  it is the one question that culture has not yet been pointed at.
- **`quantum_network` is the right template** for content-level Python↔Lean verification, and
  `bundle_figure_integrity`'s 8 pt typeset floor is the right template for a content-quality floor.
  Both prove the project can build F/G-class instruments; it has just built one of each.
- **The human-decision boundary (QA map §5) is well-drawn.** Six of ten decision points are
  *structurally* human-only, with agents clamped at `agent-reviewed`. That is the correct answer to
  "what should never be automated" and it is enforced in code, not policy.

---

## 7. Summary of what should exist

**Tier 1 — wire what exists (days, not weeks; no new measurement logic).**

| Priority | Action | Cat | Effect | Cost |
|---|---|:-:|---|---|
| 1 | wire `chain_canonicalize --report` to a check | — | Class 1's mechanical core, already measured, currently blocks nothing | hours |
| 1 | make `compile_bundle_pdf.py:114`'s `ok` read `pages` | **F** | a page floor exists the moment the value is not discarded | minutes |
| 1 | make `PAPER_DEPENDENCIES` a checked contract | **G** | right shape, read by no check — but **17/64 papers × ~3 modules**, so plumbing is hours and *population* is the real cost. Wire it with a coverage ratchet so the sparsity is visible rather than silently vacuous | hours + ongoing |
| 1 | compare the `claims-reviewer-bundle-prompts.md` anchor list to draft content | **F/G** | turns a prose obligation into a per-bundle charter check | ~½ day |
| 1 | propagate the `c7148779`/`c5f384b4` `\lean{}`/`\verb` fix to `readiness_gates.py:430` | — | Gate 5 LeanProofSubstance currently cannot see D6/D8/D9's references | hours |

**Tier 2 — new checks, all straightforwardly mechanizable.**

| Priority | Check | Cat | Measures | Cost |
|---|---|:-:|---|---|
| 2 | `bundle_substrate_attachment` | **G** | per-bundle floor on resolved declaration refs + un-homed ledger (populate `lean_modules_referenced`, then read it) | ~1 day |
| 2 | `bundle_charter_fill` | **F** | pages + words/page vs the `PAPER_STRATEGY` §6 `Length` column | ~½ day |
| 2 | gate `unmeasured` state | — | 9 of 11 gates green-on-∅ → `NOT ESTABLISHED`; extend the 2026-08-05 Gate 3/7 pattern to the other seven | ~1 day |
| 2 | **review-staleness**: `last_stage13_review` vs draft mtime | — | today the proxies key off `last_lift`, so in-place edits trip nothing | hours |
| 3 | `bundle_substrate_overlap` | **G** | pairwise declaration-reference ∩ + shingle overlap | ~½ day |
| 3 | `bundle_figure_floor` / data-availability | **F** | ≥N figures at tier ≥1; required statements present | hours |
| 4 | `paper_process_leakage` | H | `round \d+`, `Stage 1[0-4]`, `localhost:`, `\item[ ]` | hours |
| 4 | `prose_constructor_enumeration`, Aristotle-claim cross-check | B | narrow but recurrent Class-1 patterns | hours each |

Plus one non-check change with the widest leverage: **extend `CHECK_AUTHORING_GUIDE.md` §2.5's
non-empty-population obligation from the portfolio aggregate to every unit the verdict is reported
per.** That single sentence reclassifies most of §6's residue from "out of scope" to "an unmet
obligation the project already accepts."

---

*Method: `validate.py --list` and `--check prose_theorem_reference_coverage` executed on `db430c65`;
two read-only sweeps delegated (the `.claude/plugins/skeft-qa` agent layer + Stage-9/10/13/14 wiring
and review-artifact reader inventory; `readiness_gates.py` / `bundle_readiness.py` gate-by-gate
empty-population analysis), each returning file:line citations that I spot-checked against source;
`readiness_gates.py`, `bundle_readiness.py`, `prose_lean_refs.py`, `bundles_readiness.py`,
`CHECK_AUTHORING_GUIDE.md`, `VALIDATION_ARCHITECTURE.md` §6, `QA_QI_INFRASTRUCTURE_MAP.md`,
`SYNTHESIS.md`, `REMEDIATION_PLAN.md`, `MEASUREMENTS.md` read directly. Per-bundle figure, bibitem,
section and verbatim-Lean-token counts measured by me from `papers/*/paper_draft.tex`; theorem,
module and Aristotle counts from `docs/counts.json`; the 394 `formulas.py` Lean references extracted
from source. Page-count and module-homing figures are ADR-010 M1/M2's, cited as such and not
re-derived.*
