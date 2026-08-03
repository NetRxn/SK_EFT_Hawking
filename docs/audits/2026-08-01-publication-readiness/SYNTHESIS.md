# Publication-Readiness Audit — Synthesis

**Date:** 2026-08-01
**Scope:** all 21 publication bundles + the strategy and process layer that produces them
**Method:** 13 independent fresh-context auditors against a shared rubric ([`RUBRIC.md`](RUBRIC.md)); every
auditor established ground truth itself (compiled the LaTeX, read page counts off the PDF, grepped the
Lean tree) and was instructed to treat prior findings, `bundle_metadata.json` and the readiness heatmap
as claims to check rather than results to inherit.

---

## 1. Verdict

**No bundle in the portfolio is submittable today.** Best grade is C−. Three bundles reach C or better
(D8, D11, L3); the other eighteen are D or F. **80 P0 (submission-blocking) findings** across 21 bundles.

Tier-1 aggregate length is **~181 pp against a ~475 pp charter**. Only D3 meets its page target — and D3
is the one bundle that does not compile.

| | Bundles |
|---|---|
| **C−/C** | D8, D11, L3 |
| **D−/D** | F, D1, D3, D6, D9, D10, L2, I1, I2, E1, E2 |
| **F** | D2, D4, D5, D7, D12, L1, I3 |

The operator's three stated symptoms — length, disjointedness/duplication, unprofessional voice — are all
confirmed. But they are not the most serious problem the sweep found.

---

## 2. The systemic finding

**The project's quality instrumentation reports absence-of-measurement as success.**

Five mechanisms, found independently by five auditors, each reporting clean while measuring nothing:

| Mechanism | Reports | Actually |
|---|---|---|
| D6 `blockers_open: 0` | clean | Stage 10 never ran (`stage10_status: "skeleton"`) |
| D9 `stage13_status: green` | portfolio's only GREEN | Stage 10 never ran (`last_stage10_review: null`) — the only *unreviewed* bundle |
| F's citation-cache check | clean | cache covers 3 of 53 references |
| `check_bundle_source_freshness.py:63` | `"fresh: all 1 source paper(s) older than last_lift"` | returns `None` for sourceless keys, line 161 skips — a green it never computed |
| `validate.py --check paper_latex_compiles` | pass | coded `passed=True` unconditionally, and skipped by default |

This is why the defect was invisible until the drafts were read by a human: **every dial said fine.** It is
also why remediation must start with the instrumentation. Fixing 80 findings against a measurement layer
that cannot distinguish `unevaluated` from `clear` would leave the portfolio in the same state a quarter
from now.

Corroborating scale: **15 of 21 bundles carry `stage13_status: "green"` while `blockers_open > 0` and their
own `readiness` field reads `RED`.** 20 of 21 have `last_lift` older than the draft's mtime — meaning the
drafts were edited outside the lift procedure that is supposed to own them.

---

## 3. Defect classes, ordered by severity

### Class 1 — Claim/substrate divergence (the reputational risk)

Found by **every one of the ten bundle auditors**. The manuscript asserts proof content the Lean does not
contain. In several cases the Lean is *correct and carries an explicit disclaimer* that the prose ignores.

| Bundle | The claim | The substrate |
|---|---|---|
| **L1** | "Volovik identified the vestigial second-sound mode as the graviton, with `c_GW = c·√χ_vest`" | arXiv:2312.09435v2 read in full: no collective-mode analysis, no graviton mode, no second sound, no propagation speed. The project's own corpus says *"Wave 2 **fixed** the GW propagation speed"* and the mode *"is the J=0 Higgs amplitude mode … **not a graviton**"* |
| **D2** | §2.6 "Discharging hypothesis H2 … encoded as `ChangeOfRings.hom_tensor_adjunction_dim`" | `theorem hom_tensor_adjunction_dim (rank : ℕ) : rank = rank := rfl`. Same file, l.82–86: *"H2 is OPEN"* |
| **D7** | abstract asserts the simulability biconditional | `AnalogHawkingDemarcation.lean:31–39`, added 2026-07-17: *"NOT a proof of classical simulability or a quantum-advantage lower bound"*. Headline theorem name does not exist in the repo |
| **D5** | §12's "7-class GD taxonomy", classes 0/a/b/c/d/**e/f/g** | `DarkSectorClassificationExtension.lean:53–77` has seven constructors; **(e), (f), (g) do not exist**; real classes (b′)(b″) absent from the paper |
| **D4** | "the substrate's central QEC theorem" | `exact Real.log_pos_iff` — `codeDistance` is *defined* as a log |
| **D10** | "first formalization of Hohenberg–Kohn / Levy–Lieb in any proof assistant" | 66-line files importing only order theory; `nondegen` is a structure field asserting the conclusion |
| **D9** | `fdt_quantum_noise_floor` "replaces the classical floor in the cryogenic regime" | Johnson term cancels on both sides; content is `0 < E0/2`, two `linarith` calls |
| **I3** | title/abstract assert the stochastic-calculus mathematics | `IsNovikovCondition θ T := 0 ≤ T ∧ Continuous θ`; `IsCramerLowerBoundEsscher` character-identical to `IsCramerIIDUpperBound`; §8.9 withdraws it on p. 16 |
| **I1** | "All nine sub-lemmas closed in a single Aristotle priority batch" | no entry in `ARISTOTLE_THEOREMS` (322 entries, 34 runs); no run ID |

**L1 is the most serious single finding in the sweep.** It is the designated first submission — alone, to
PRL — and it titles a falsification of a named living author's published claim, built on a formula the
project constructed itself and a parameter range it self-describes as "project-adopted." It propagates
into D3 §6 as one of three closures the abstract says *force* ADW.

Adjacent: **D4 ships its flagship knot invariants on `by native_decide`** (29 live sites) under an abstract
advertising "zero project-local axioms" — while **D8 devotes a subsection to eliminating `native_decide` as
a trust escape.** I2 has ~99 undisclosed `native_decide` uses in exactly the modules its Mathlib PR-4 targets.

### Class 2 — Duplication and self-competition

- **D6 §5.4 = 56% of D6, sharing 78 identical Lean theorems with D9.** Both target PRX Quantum/Quantum.
  Root cause: `phase6AA_qnetwork_preprint/preprint_draft.md:7` still declares itself *"bundle D6 §6"* while
  `PAPER_STRATEGY.md:164` assigns it to D9. Neither lift removed the other.
- **D4 §9 = 3,206 words = 62% of the entire D8 manuscript**, and **both papers assert priority over it**
  (`D4:1189` vs `D8:31,42`) — a priority dispute against ourselves, in print.
- A Phase-6w block is **triplicated verbatim** across D1, E1, E2; its home is D7.
- **3 of 14 declared sibling boundaries are honoured.** Ten exist only in the planning document. The
  flagship cites D9/D10/D11/D12 **zero times**.

### Class 3 — Referee-facing scar tissue

The operator's "turned into a discussion with the review agent" symptom, located precisely:

- **F**: a 1.5-page **unticked checkbox tracker rendered into the PDF** (`:1351–1388`); an agent's **tool
  budget** quoted as content — "≤25 reads, ≤40 tool calls" (`:1681–1684`).
- **D12**: three in-body passages narrating its own revision history to the reader.
- **D11**: the correction landed *as narration of the correction* — "rounds 7 and 10 both rated this
  cosmetic, and round 12 supplied the counterexample" (`:328`).
- **D5**: all seven figure captions end *"Lifted from paperNN"*; one passage reads *"User authorization for
  a 14th bundle target would elevate this to a stand-alone Letter."*
- **D3**: rendered "Phase 7 sub-wave 7c.0 … Phase 8 is the submission roll-out"; points readers at `localhost:8050`.
- **E2** `:421–433`: a nested retraction-of-a-retraction, citing Stage-13 round numbers and instructing the
  reader how not to quote it.

**D11 is the instructive case.** Its correction pass was substantively right — independently verified: zero
`berryCurvature` declarations, no surviving promise of unshipped content, zero axioms and zero tracked Props,
and the best priority-hedging discipline in the corpus. It fixed the claim *and then told the reader it had.*
The rule to extract: **correct the claim silently; the change log is the audit trail, not the manuscript.**

### Class 4 — Length and structure

Nine of 21 bundles ship **zero figures**, including the flagship. Zero of 21 have a data-availability
statement; 20 of 21 lack code/artifact availability — indefensible for a formally-verified-results program.
F has **no repository, Zenodo or DOI pointer anywhere.**

**D3 is confirmed sedimentation**: 30 sections, median 262 words, `source_manifest.md` mapping sources 1:1
onto 22 of them. Cause identified in the procedure itself — §3a inserts one section stub per source.

Cheapest recovery available: **16 manifest-claimed sections across 7 bundles are commented-out stubs sitting
after the bibliography** while `append_log.json` still counts them. D1 has four, so part of its 73% shortfall
is self-inflicted commenting rather than missing work.

### Class 5 — Mechanical

- **D3 does not compile**: `\Imm` at `:712` (meant to be `\gamma`). Under the procedure's own mandated
  `-halt-on-error` it produces no PDF. The shipped 57-pp PDF was built by a non-halting run, so the γ
  **silently vanished**: `pdftotext` line 1203 reads "it is derived **-independently**". D3 carries
  `stage9/10/13_status: green`.
- **10 of 21 committed PDFs are stale.** Sharpest: **I1's on-disk PDF abstract says "12463 machine-checked
  theorems across 936 Lean modules"; the source compiles to "26103 … 2012 modules"** — anyone who reviewed
  the PDF read the headline counts wrong by 2–4×.
- **Dangling citations: 0 across all 21.** D8 and D10 were false alarms (BibTeX resolves cleanly). The real
  defect is inverted: **D5 has 18 of 27 bibitems never cited**, including every load-bearing primary source
  (Berezhiani–Khoury, Plaza-Kraiselburd, Tyagi, Luciano, Yoon-Guha, Van Waerbeke), named inline by bare arXiv
  number instead.
- **`\substantivetheorems{}` resolves to 26,077 — the whole project** — and is presented as the paper's own
  content in D1's, E1's and D5's abstracts. It auto-inflates (5,229 → 26,077 since the advisory was raised).
- **Four toolchain pins** across bundles (v4.28.0/4.29.0/4.29.1/4.32.0) because `counts.tex` defines no pin macro.
- Author name appears in **5 different forms**, affiliation in 3; 12 of 21 lack an affiliation.

### Class 6 — Un-homed work and dead absorption

- **The Stage-C trigger of `LATE_PHASE6_ABSORPTION_PROTOCOL` is dead for D6–D12** (see §2). Every bundle
  authorized since D6 is sourceless; nothing tracks Lean-module mtimes.
- **~340 kernel-verified Lean modules across 10 arcs appear in no bundle draft**, plus 8 fully-closed phases
  (6h, 6j, 6k, 6l, 6q, 6r, 6r′, 6s) with no bundle home. Includes the **entire Pin⁺ ℤ/16 arc** (162 `PinPlus*`
  + ~88 Smith/Wu, zero `papers/` hits) and the **whole `GenericSUd*` SU(d) substrate that D8 advertises as its
  headline**.
- **60-item drift ledger** across 11 process docs. Load-bearing: **Pipeline Invariant #14**
  (`WAVE_EXECUTION_PIPELINE.md:689`) names an 18-target enum that cannot legally hold D10/D11/D12.
  `PAPER_STRATEGY.md:332` still says D5 is "Blocked on Phase 6m" — closed 2026-04-30, two days before that
  section was written.

---

## 4. What is genuinely sound

Recorded because the remediation depends on knowing what not to touch.

- **The physics pipeline is consistent.** All ten probed shared constants agree across bundles; D1/E1/E2
  triangulation reproduces from `constants.py`/`formulas.py`. The failure is in the manuscript layer, not
  the computation layer.
- **Zero dangling citations portfolio-wide; zero missing graphics; zero `Missing $`.**
- **D8's Mathlib-upstream portfolio is fully backed** — all four named contributions plus ~30 attributed
  theorems exist at their stated modules.
- **D11's honesty discipline** — priority hedging with past-tense negatives, self-refutation guards, named
  carve-outs, pinned revision + verification method, and correct respect for *Mathlib-absence ≠ literature-absence*.
- **D5 §9 (Track B)** — the 3-of-4 → 2-of-4 Bayes-decisive self-correction and the Verlinde σ-vs-Bayes restatement.
- **I1 Worked Cases 1 and 2** verify against the Lean and the registry.
- **D10's `CoulombRelativeBound.lean`** — 2,492 lines of genuinely unconditional molecular Coulomb
  self-adjointness. Plausibly the paper D10 should actually be.
- **D12's folklore refutations** are real, first-class negative content.
- Several drafts are **more honest than the strategy document describing them** (D5's 0.83σ/1.04σ vs the
  charter's advertised 3.5–5.7σ; I3's §8.9 withdrawal vs §2.4's priority claims). Where they conflict, the
  strategy doc is usually the thing that needs fixing.

---

## 5. Decisions required from the operator

These gate the remediation plan; everything else I can execute.

**D-1. Roster consolidation, 21 → 16.** Recommended: merge D6+D9+D12 (the strategy already writes their
outline as one stack), merge D10+D11, merge E1+E2, fold D7 into D1, move D4 §9 to D8. Rationale: Tier 1 is
~181 pp against a ~475 pp charter, and the two largest duplication findings (D6/D9, D4/D8) *are* boundary
failures between bundles that should not be separate.

**D-2. First submission: L1 or L3.** L1 cannot ship until its central attribution is re-founded — that is
research, not editing. L3 is the family's only C-grade manuscript and needs `revision`. Recommend L3.

**D-3. L1's disposition.** Three options: re-found the falsification against what Volovik actually claims
(EP violation, not modified `c_GW`); restate it as a falsification of a *project-constructed* identification
with Volovik cited only as the motivating framework; or retire it. This is a scientific-integrity call.

**D-4. D10 scope.** Ship the 2,492-line Coulomb self-adjointness result as the paper, or hold D10 until the
DFT layer is real. Related open check: whether PhysLib's now-reachable spectral theory (post-v4.32.0) makes
D10's in-tree Kato–Rellich redundant — D10's only defensible novelty depends on it.

**D-5. `native_decide` posture.** D4's headline results and ~99 I2 uses rest on it. Either eliminate it in
the affected proofs, or disclose it prominently and drop the "zero project-local axioms" framing. It cannot
stay silent given D8 argues against it in the same portfolio.

**D-6. Physics adjudication — graphene `Γ_H`.** `Γ_H = (η/(sT))(κ/c_s)²` is dimensionally `s·m⁻²`, not
`s⁻¹`, in both the paper and `formulas.py`. Restoring a `c_s²` moves `δ_diss` from 1.7e-13 to ~3e-2 and
**inverts E2's "eleven orders below dispersive" headline.** Dimensions and arithmetic verified; the
derivation was not. Needs a physics call before anything in that family ships.

---

## 6. Remediation sequence

Ordered by dependency and value, not by bundle number.

**Phase 0 — instrumentation (must precede everything).**

> ⛔ **WITHDRAWN 2026-08-01 — the six items below are NOT authorized and must not be built as listed.**
> See `REMEDIATION_PLAN.md` §6a. They were written before the existing system was mapped; at least one
> (item 4) duplicates `scripts/chain_canonicalize.py`, which already works. Treat this list as a
> *defect inventory*, not a build plan: each item names a real defect, but the fix is far more likely to be
> **wiring an existing instrument** than writing a new one. Phase 0 will be re-authored as a
> defect → existing-coverage → residue table once exploration completes, and any genuine residue requires
> operator approval before implementation.

Nothing else is trustworthy until the dials work.
1. `MetadataTruthfulness` gate — fires today on 14 bundles; encode `unevaluated` distinctly from `clear`.
2. Fix `check_bundle_source_freshness.py` — track Lean-substrate mtimes; emit `unmeasurable`, never a
   fabricated green.
3. Make `paper_latex_compiles` actually compile, with `-halt-on-error`, un-skipped.
4. `bundle_headline_theorem_resolves` — every `headline_theorems` entry must resolve in `lean_deps.json`
   (catches D7's phantom headline).
5. `bundle_lean_module_coverage` — surfaces the ~340 unlifted modules.
6. Add a pin macro to `counts.tex`; scope `\substantivetheorems{}` per bundle.

**Phase 1 — integrity (the reputational items).**
L1 attribution (D-3); D2 §2.6; D7's abstract vs its Lean disclaimer; D5 §12's taxonomy; D4's QEC/RT claims
and `native_decide` disclosure; D10's DFT claim; D9's FDT claim; I3's predicate names; I1's Aristotle batch
claim. Every one is a false statement in a manuscript, and each is cheap to fix once acknowledged.

**Phase 2 — deduplication (unblocks the roster).**
Reconcile `preprint_draft.md:7`; excise D6 §5.4; move D4 §9 → D8 and settle the priority claim; delete the
triplicated Phase-6w block. Note the sequencing trap: **removing D9's content from D6 drops D6 to ~7 pp**, so
the length gap widens before it closes — which is itself an argument for D-1.

**Phase 3 — mechanical sweep (cheap, wide).**
D3's `\Imm`; regenerate 10 stale PDFs; uncomment the 16 stubbed sections; D5's 18 uncited bibitems; scar-tissue
excision across F/D12/D11/D5/D3/E2; data- and code-availability statements portfolio-wide; author/affiliation
normalization; pin sync.

**Phase 4 — structure and length (the real work).**
D3 restructure to the proposed 7-section architecture; figure programmes (D1's is `small` — 8+ generators
already exist in `visualizations.py`); F's results index, ~15 figures, 8 tables, artifact release, and
D9–D12 coverage. F is **~70% writing, ~30% not-yet-built**, where the 30% defines the deliverable.

**Phase 5 — process repair.**
Add to `BUNDLE_LIFT_PROCEDURE`: a §0 bundle charter (venue, page budget, section architecture, figure plan)
and a §7.5 whole-document read-through. Change §3a — one-section-per-source stub insertion is what manufactures
the stitched lift. Make §6 figure *planning*, not migration. Encode the D11 rule: **correct claims silently.**

---

## 7. Reading order

For a fast orientation: this file, then `CROSS-portfolio-coherence.md` (the duplication map and roster
recommendation), then `bundles/D3-L1-L3.md` (the L1 finding in full, with the primary source read).
`CROSS-build-integrity.md` holds the authoritative per-bundle mechanical table.
