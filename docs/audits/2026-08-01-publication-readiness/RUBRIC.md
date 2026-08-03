# Publication-Readiness Audit — Shared Rubric (2026-08-01)

**Read this in full before assessing anything.** Every auditor in this sweep uses the same
axes, the same severity scale, and the same output contract, so the results compose into one
portfolio verdict.

---

## 0. What this audit is, and what it is NOT

The project already has extensive machinery for **claim correctness**: Stage-13 adversarial
review, the claims-reviewer sentence walker, `bundle_readiness.py`, the gate × bundle heatmap.
That machinery answers *"is each sentence backed?"*

It does **not** answer *"is this a publishable manuscript?"* — and that is the question this
audit exists to answer. The operator's stated symptoms are manuscript-level:

- drafts far below the length their own stated target journal requires
- disjointed strategy across bundles, including duplicated content
- prose that does not read professionally — in places the manuscript has degraded into a
  *discussion with an adversarial review agent* rather than an article addressed to a reader

So: **assume nothing from prior reviews.** Prior finding counts, `bundle_metadata.json`
statuses, and the readiness heatmap are *evidence to be checked*, not conclusions to inherit.
Several are already known to be internally inconsistent (e.g. `papers/D7/bundle_metadata.json`
carries `"stage13_status": "green"` alongside `"blockers_open": 12`; `docs/PAPER_STRATEGY.md`
§3 claims all bundles cleared GREEN while `docs/BUNDLE_READINESS_HEATMAP.md` renders 15 RED).
Where a status claim and the artifact disagree, **the artifact wins** and the disagreement is
itself a finding.

Read the manuscript as a **journal referee and an editor** would: someone who has never seen
this repository, cannot run the code, will not read the Lean, and decides in the first two
pages whether this is a serious paper.

---

## 1. Ground truth you must establish yourself

Do not take page counts or compile status on faith.

```bash
cd papers/<BUNDLE>
latexmk -pdf -interaction=nonstopmode -halt-on-error paper_draft.tex   # or pdflatex x2 + bibtex
pdfinfo paper_draft.pdf | grep Pages     # true page count
```

If it fails to compile, that is a **P0 finding** — record the first fatal error verbatim.
If it compiles with warnings, count `LaTeX Warning: Reference ... undefined` and
`Citation ... undefined` — each class is a finding.

Record the **true compiled page count**. Compare it against the bundle's own stated target in
`docs/PAPER_STRATEGY.md` §2 and §6. Do not substitute a word-count heuristic when a real page
count is obtainable.

**Length targets, interpreted correctly** (a shortfall is only a finding if it is real):

| Tier | Bundles | Stated target | How to judge |
|---|---|---|---|
| 0 | F | 80–150 pp (RMP / Phys. Reports) | Real shortfall if compiled ≪ 80 pp. This is a review article: breadth of coverage and completeness of the index-of-results are the substance. |
| 1 | D1–D12 | ~30–50 pp (PRD long / PRX Quantum / JHEP) | Real shortfall if compiled ≪ 25 pp. A "deep paper" at 6 pp is a letter wearing a deep paper's title. |
| 2 | L1–L3 | 4 pp (PRL) | **PRL's limit is ~3750 word-equivalents including figures, tables, captions and references.** A 2,000-word L-paper is plausibly *correct*, not automatically too short. Judge these on whether they are complete, self-contained letters — do not flag them merely for being short. Flag them if they *exceed* the limit. |
| 3 | I1–I3 | ~15–25 pp (CPC / JOSS / Phys. Reports) | JOSS papers are legitimately ~1–2 pp; CPC/Phys. Reports are not. Judge against whichever venue the bundle actually names first. |
| 4 | E1, E2 | 2–3 pp (PRL / PRR letter) | Same PRL word-equivalent rule as Tier 2. |

---

## 2. Assessment axes

Score each axis **A / B / C / D / F** with a one-line justification and concrete evidence
(file + line, or a quoted phrase). An axis score of D or F must be backed by at least one
quoted excerpt.

### Axis 1 — Manuscript completeness and structure
Does it have the parts a paper of this type must have, in the right proportion?
- Title, abstract, introduction that states the contribution in the first paragraph, a
  conclusions/discussion section, a bibliography.
- Section architecture that a reader can follow. **Symptom to hunt: the "stitched lift"** —
  a section per source draft, each ~400 words, with no connective argument. (`D3` carries 31
  sections across ~14k words; check whether that is architecture or sedimentation.)
- Are there figures and tables *at all*? Several bundles have zero of both. For a 30–50 pp
  PRD-style article that is a structural defect, not a cosmetic one. Name which results
  *should* be a figure or table.
- Equations numbered and referenced; notation defined before use.

### Axis 2 — Prose professionalism / referee-facing scar tissue
This is the operator's sharpest complaint. Hunt for text that is addressed to a *reviewer* or
to the *project's own process* rather than to a reader of the literature:
- narration of the review history ("this previously read…", "corrected 2026-07-30", "⚠ scope
  correction", "the audit found…", "an earlier draft claimed…")
- defensive hedging aimed at pre-empting an internal reviewer
- internal process vocabulary leaking into the manuscript: *Stage 13*, *wave*, *bundle*,
  *lift*, *kernel-pure*, *sorry*, *tracked Prop*, *Phase 6xx*, roadmap filenames, agent names
- **Exception, and it matters:** for `I1` (the methodology paper) the pipeline *is* the
  subject matter. Discussing Stage 13 there is legitimate content. The test for I1 is whether
  the process is described *as an object of study for an outside reader* or *performed at the
  reader*. Apply the same care to `I2`/`I3` where the library is the subject.
- Every instance you cite must be quoted with a line number, and you must say what the
  sentence should become — deletion, or rewrite into a forward-facing statement.

### Axis 3 — Scientific framing and contribution clarity
- Does the abstract lead with the *result*, or with apparatus and caveats?
- Would a subject-matter referee at the named journal recognise a contribution worth the page
  budget? State the single strongest claim, and whether the manuscript actually delivers it.
- **Overclaim and vacuity.** Novelty assertions ("first in any proof assistant", "the first
  formalization of X") are the highest-risk sentences in this corpus — one has already been
  refuted by a live prior-art sweep (6EA). For each such claim: is it hedged to what was
  actually checked, and is the check named? Flag any unqualified priority claim.
- **Verifiability by the reader.** A formally-verified result the reader cannot locate is not
  a result. Are Lean theorem names, module paths, and a public artifact reference given?

### Axis 4 — Citation and evidence integrity
- `\cite` keys with no matching `\bibitem`/bib entry, and bibliography entries never cited.
  (Known suspects: `D8` 26 cites / 0 bibitems; `D10` 13 / 0; `D5` 9 cites / 27 bibitems.)
- Citations that do not support the sentence they are attached to — spot-check the load-bearing
  ones (the anchor list is `docs/agents/claims-reviewer-bundle-prompts.md`).
- Numerical values, device parameters and published bounds: traceable to a primary source?
- Self-citation to unpublished internal drafts presented as if they were literature.

### Axis 5 — Portfolio fit (per-bundle view)
- Does this bundle's actual content match its charter in `docs/PAPER_STRATEGY.md` §2?
- Content that duplicates a sibling bundle: name the sibling and the overlapping material.
- Content that belongs in a sibling and should move: name the destination.
- Sibling cross-references asserted in the strategy (e.g. "D12 consumes D9's envelopes") —
  are they actually present in the manuscript as citations, or only in the planning doc?

### Axis 6 — Absorbability of future work
Phase 6 continues to ship. Is this manuscript structured so a future wave lands as an
*addition* rather than a rewrite?
- Is there a natural section slot for new results of the bundle's kind?
- Are the stated-but-unshipped / deferred threads honestly marked (D11's deferred
  bulk–boundary correspondence and continuum Chern invariant are the reference case), or does
  the prose still promise them?
- Does `source_manifest.md` reflect what is actually in the draft?

---

## 3. Severity scale

| Level | Meaning |
|---|---|
| **P0 — submission-blocking** | An editor would desk-reject, or the manuscript does not compile. Examples: fails to build; ≥50 % short of a hard journal length floor; broken bibliography; a refuted or unsupportable priority claim in the abstract; referee-facing process narration in the body. |
| **P1 — referee-fatal** | Survives the editor, dies in review. Examples: no figures in a 40 pp article; stitched-lift structure with no argument; an unhedged novelty claim in the body; citation that does not support its sentence. |
| **P2 — quality** | Would draw a "major revision" comment. Awkward framing, thin discussion, notation drift, uneven section depth. |
| **P3 — polish** | Copy-edit class. |

Every P0 and P1 needs: **file:line → what is wrong → what it must become → estimated remediation
size** (`trivial` < 1 h, `small` < 1 day, `medium` a few days, `large` a week+, `new-work` =
requires physics/Lean that does not exist yet).

The last one matters most for planning. Be honest when the answer is `new-work`: a 6 pp draft
that must become a 40 pp article is not an editing task, and calling it one would corrupt the
remediation plan.

---

## 4. Output contract

Write your report to the path your dispatch brief names, under
`docs/audits/2026-08-01-publication-readiness/`. Use this skeleton exactly — the synthesis
step parses it.

```markdown
# <Scope> — Publication-Readiness Audit
**Auditor:** <your dispatch id>   **Date:** 2026-08-01
**Artifacts examined:** <paths, with the compile command you ran>

## Verdict summary
| Bundle | Compiled pp | Target pp | Axis1 | Axis2 | Axis3 | Axis4 | Axis5 | Axis6 | Overall | Distance to submittable |
|---|---|---|---|---|---|---|---|---|---|---|
(Overall = worst-of-axes, adjusted by judgement. "Distance" = one of:
 `copy-edit` / `revision` / `restructure` / `substantial-new-writing` / `new-research-required`.)

## Per-bundle findings
### <BUNDLE>
**What this manuscript currently is:** <2–3 sentences, plainly. A referee's one-paragraph impression.>
**Strongest asset:** <the thing worth keeping — be specific>
**Findings**
| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| <B>-01 | P0 | 2 | paper_draft.tex:412 | … | … | small |

## Cross-bundle observations
<duplication, boundary problems, anything the portfolio synthesis needs>

## What I could not check
<explicit limits — be honest; an unchecked item silently reported as clean is worse than a gap>
```

Return to the orchestrator a **≤400-word** summary: per-bundle overall grade, the P0 count, the
single worst finding per bundle, and the total remediation size class. The full detail lives in
the file — do not paste it back.

---

## 5. Conduct

- **Quote, don't characterise.** "The prose is unprofessional" is not a finding.
  `paper_draft.tex:812` + the sentence + why it fails, is.
- **Verify before asserting.** If you claim a citation is unsupported, say how you checked. If
  you could not check it, put it under *What I could not check*.
- **Do not fix anything.** This is an assessment pass. No edits to any draft, doc, or metadata
  file. Your only writes are your own report file.
- **Do not soften.** The operator's explicit position is correctness over expediency, and a
  remediation plan built on a flattering audit is worse than no audit. If a bundle is not
  publishable, say so in the first line of its section.
- **Do not inherit difficulty estimates** from roadmaps or prior reviews. Assess the artifact.
