---
paper: paper35_qec_holography
artifact: notebook_pair
notebooks:
  - notebooks/Phase6c4_QECHolography_Technical.ipynb
  - notebooks/Phase6c4_QECHolography_Stakeholder.ipynb
reviewer: adversarial-reviewer (notebook adaptation)
model: claude-opus-4-7[1m]
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper35_qec_holography (notebook pair)

## Summary

Reviewed Technical + Stakeholder notebooks for paper35 against
`paper_draft.tex`, `lean/SKEFTHawking/QECHolographyBridge.lean` (10
theorems), `src/qec_holography/`, and W3 upstream `BHEntropyMicroscopic`.
All seven bibitems verified live against arXiv (HaydenPreskill2007,
AlmheiriDongHarlow2015, PYHP2015, YoshidaKitaev2017, KitaevAnyons2003,
NayakAnyons2008, KitaevPreskill2006) — citation integrity is clean.
Lean theorems exist, are non-trivial, and correctly proved; the Python
mirror is faithful.

Findings count: **2 BLOCKER, 3 REQUIRED, 2 RECOMMENDED**. The blockers
are (i) a quantitative-minimality overclaim repeated in both notebooks
and the paper — Fibonacci is **not** the minimal-d_C admissible MTC
among the four substrates shown (Ising's `d_σ = √2 < φ` gives strictly
smaller `d_C ≈ 0.347 < 0.481`); the comparison `log φ < log 2` is
irrelevant to minimality among the displayed set — and (ii) a
substrate-labeling drift where the third bar is presented as
"SU(3)_{k=2}" but only carries the {vac, adj} sub-sector spectrum
(D² = 1+φ² ≈ 3.618), not the actual SU(3)_{k=2} MTC (D² = 3+3φ²
≈ 10.854). The Python `name` field is honest
(`su3_k2_fibonacci_subsector`); the notebook display labels truncate
that disclosure.

REQUIREDs: missing scope-disclosure section in the Technical notebook
(AdS/CFT, Yoshida-Kitaev, Page curve are deferred — only Stakeholder
§6 says so); H_HorizonBoundaryCondition not flagged as a *tracked
external hypothesis* in the Technical notebook §6 (Stakeholder §6 does
flag this); Stakeholder §4 prose ("yes, universally — for any
encoding choice") describes a 1-line `log d_a ≤ log D²` threshold
inequality as "Hayden-Preskill universal recovery" without the
out-of-scope caveat that no decoder is constructed.

Notebook pair is **NOT submission-ready** until findings 5.1 and 5.2
land in both notebooks and (per finding 5.1) the paper draft
`paper_draft.tex` lines 211–212, 224–227 + Lean docstring at
`QECHolographyBridge.lean:289–296` are corrected in lockstep — the
overclaim is duplicated across all four artifacts.

## Findings

### 1.1 — 🟢 PASS — Citation integrity (all 7 bibitems)

- **Gate:** CitationIntegrity
- **Location:** `paper35_qec_holography/paper_draft.tex:296–334`
- **Observed:** All seven bibitems used in the paper and referenced
  by both notebooks (`HaydenPreskill2007`, `AlmheiriDongHarlow2015`,
  `PYHP2015`, `YoshidaKitaev2017`, `KitaevAnyons2003`,
  `NayakAnyons2008`, `KitaevPreskill2006`) verified live via WebFetch
  against arXiv abstract pages.
- **Evidence:** arXiv:0708.4025 → Hayden+Preskill, JHEP 2007/9/120, "Black
  holes as mirrors..." ✓; arXiv:1411.7041 → Almheiri+Dong+Harlow, JHEP
  2015/4/163, "Bulk locality and quantum error correction in AdS/CFT" ✓;
  arXiv:1503.06237 → Pastawski+Yoshida+Harlow+Preskill, JHEP 2015/6/149,
  "Holographic quantum error-correcting codes..." ✓; arXiv:1710.03363 →
  Yoshida+Kitaev, "Efficient decoding for the Hayden-Preskill protocol",
  2017 (preprint) ✓; arXiv:quant-ph/9707021 → Kitaev, Annals Phys. 303
  (2003) 2-30, "Fault-tolerant quantum computation by anyons" ✓;
  arXiv:0707.1889 → Nayak+Simon+Stern+Freedman+Das Sarma, RMP 80, 1083
  (2008) ✓; arXiv:hep-th/0510092 → Kitaev+Preskill, PRL 96, 110404 (2006)
  ✓. All seven also present in `src/core/citations.py` `CITATION_REGISTRY`.
- **Cache:** fresh-fetch (all 7).
- **Verdict:** No finding — recorded as positive verification.

### 5.1 — 🔴 BLOCKER — "Fibonacci is the minimal admissible MTC by code-distance proxy" is false against the data the artifacts themselves display

- **Gate:** NarrativeGrounding
- **Location:**
  - `notebooks/Phase6c4_QECHolography_Technical.ipynb` cell `p35t-intro`
    line 19, cell `p35t-5-md` line 281 ("Fibonacci as the minimal
    non-abelian admissible MTC"), cell `p35t-5-code` print line 309
  - `notebooks/Phase6c4_QECHolography_Stakeholder.ipynb` cell `p35s-1-code`
    output line 66, source line 90, cell `p35s-2-code` row label line 128
    ("τ has d=φ; minimal non-abelian"), cell `p35s-5-md` line 224
    ("confirming Fibonacci as the minimal admissible MTC")
  - `papers/paper35_qec_holography/paper_draft.tex:211–212` ("$\log 2
    \approx 0.693$ locates Fibonacci as the minimal non-abelian admissible
    substrate") and `:224–227` ("locating Fibonacci as the minimal
    non-abelian admissible MTC by code-distance")
  - `lean/SKEFTHawking/QECHolographyBridge.lean:289–296` (docstring of
    `fibonacci_HPCode_codeDistance_lt_log_two`: "Locates Fibonacci as the
    *minimal* non-abelian MTC by code-distance — the bottom of the W4
    admissibility ladder.")
- **Observed:** Both notebooks claim "Fibonacci is the minimal
  non-abelian admissible MTC" using the comparison `log φ < log 2`. The
  surrounding tables in the *same* notebooks display:

  | substrate    |   d_max   |   d_C   |
  |--------------|----------:|--------:|
  | Fibonacci    |   1.6180  |  0.4812 |
  | Ising        |   1.4142  |  0.3466 |
  | SU(3)_{k=2}* |   1.6180  |  0.4812 |
  | Trivial-Ab   |   1.0000  |  0.0000 |

  Ising's `d_σ = √2 ≈ 1.414` is strictly less than `φ ≈ 1.618`, so its
  code distance `d_C = log √2 ≈ 0.347` is strictly less than Fibonacci's
  `log φ ≈ 0.481`. Among the displayed admissible substrates, **Ising
  has the smallest code distance, not Fibonacci.**
- **Evidence:** Stakeholder cell `p35s-2-code` output (review transcript)
  shows Ising d_C = 0.347 in the same table that prose calls Fibonacci
  "minimal." The comparison `log φ < log 2` referenced in both notebooks
  and the paper (line 211: "reference line at $\log 2 \approx 0.693$
  locates Fibonacci as the minimal non-abelian admissible substrate")
  has no bearing on whether `log φ` is the smallest *among admissible*
  substrates — `log √2 < log φ < log 2`, and Ising is admissible, so
  the inequality `log φ < log 2` fails to support the minimality
  claim.
- **Expected:** Either:
  (a) Replace the qualifier with the literature-supported sense:
  *Fibonacci is the minimal non-abelian MTC sufficient for fault-tolerant
  universal quantum computation* (Ising is non-abelian but not universal
  for QC — see NayakAnyons2008 §3). Drop the `log φ < log 2` framing,
  which has no role in that argument; or
  (b) Restate as a non-load-bearing reference (e.g.,
  `d_C^{Fibonacci} < log 2` is the smallest power-of-2 quantum-dimension
  reference) and stop calling Fibonacci "minimal" — the data row for
  Ising falsifies that ordering.
- **Fix:** Patch the prose in both notebooks (3 cells in Technical, 3
  cells/strings in Stakeholder), the paper draft lines 211–212 and 224–227,
  and the Lean docstring at `QECHolographyBridge.lean:289–296`. The Lean
  *theorem statement* `fibonacci_HPCode_codeDistance_lt_log_two` is fine
  on its own ($d_C^{Fib} < \log 2$ is a true inequality); only the
  surrounding prose-level "minimal" gloss needs to change.
- **Cache:** N/A.

### 5.2 — 🔴 BLOCKER — SU(3)_{k=2} third bar is the {vac, adj} sub-sector, not the full SU(3)_{k=2} MTC; D² = 3.618 ≠ true SU(3)_{k=2} D² ≈ 10.854

- **Gate:** NarrativeGrounding (cross-paper consistency)
- **Location:**
  - `notebooks/Phase6c4_QECHolography_Technical.ipynb` cell `p35t-1-code`
    print row line 60 (`SU(3)_{k=2}  | 1.6180 |  3.6180 | …`), cell
    `p35t-2-md` line 263 ("SU(3)$_{k=2}$ Fibonacci sub-sector $\{1,
    \text{adj}\}$ … Spectrum identical to Fibonacci by truncation."),
    cell `p35t-2-code` print line 80
  - `notebooks/Phase6c4_QECHolography_Stakeholder.ipynb` cell `p35s-2-md`
    line 105 ("**SU(3)$_{k=2}$ Fibonacci sub-sector** … Cross-check:
    independent path to the same observables"), cell `p35s-2-code`
    table row line 129
  - `src/qec_holography/code_distance.py:58–65` (`SU3K2_SPECTRUM` with
    `name="su3_k2_fibonacci_subsector"` and `quantum_dims=(1.0, _PHI)`)
- **Observed:** The third bar/row is **labeled** `SU(3)_{k=2}` in both
  notebook tables and the figure (paper §5 figure caption refers to
  "the Fibonacci sub-sector of $SU(3)_{k=2}$"), but the spectrum used
  numerically is the {vac, adj} 2-element truncation with d-values
  (1, φ), giving D² = 1+φ² ≈ 3.618. The actual SU(3)_{k=2} MTC has 6
  simple objects (per project Lean: `lean/SKEFTHawking/SU3kFusion.lean:131-138,151-152`
  — `vac, fund, conj, sym, symbar, adj` with quantum dimensions
  "vac,s,s̄ = 1; f,f̄,τ = φ"), giving D² = 3 + 3φ² = 3(1+φ²) ≈ 10.854.
  A reader who recomputes D² from the published "SU(3)_{k=2}" label
  will find 10.854, not 3.618.
- **Evidence:**
  - `lean/SKEFTHawking/SU3kFusion.lean:143`:
    `theorem su3k2_object_count : Fintype.card SU3k2Obj = 6`
  - `lean/SKEFTHawking/SU3kFusion.lean:151–152` (comment): "Quantum
    dimensions: vac,s,s̄ = 1; f,f̄,τ = φ (golden ratio)"
  - `src/qec_holography/code_distance.py:58–65` Python `name` field
    `"su3_k2_fibonacci_subsector"` — the underlying code is honest;
    the **notebook-side display label** is "SU(3)_{k=2}", which
    truncates the disclaimer that this is a sub-sector restriction.
  - `src/qec_holography/code_distance.py:60-64` comment is candid:
    "the full 6-simple-object spectrum is not used in W4 numerics"
- **Expected:** Display label should read
  `SU(3)_{k=2} Fib-sub` or `SU(3)_{k=2} | {1, τ}` or
  `Fibonacci sub of SU(3)_{k=2}` consistently across both notebooks
  and the figure caption. The "spectrum identical to Fibonacci by
  truncation" prose (Technical cell `p35t-2-md`) is mathematically
  correct *for the sub-sector*, but the *table headline* must not
  read `SU(3)_{k=2}` because the displayed D² is not SU(3)_{k=2}'s D².
- **Fix:**
  1. In both notebook tables (Technical `p35t-1-code` and `p35t-2-code`,
     Stakeholder `p35s-2-code`) change the row label string `SU(3)_{k=2}`
     → `SU(3)_{k=2} Fib-sub`.
  2. In Stakeholder cell `p35s-2-md` strengthen "SU(3)$_{k=2}$ Fibonacci
     sub-sector" prose with: "We display only the {vac, adj} closed
     sub-MTC; the full SU(3)$_{k=2}$ has six simple objects with D² =
     3(1+φ²) ≈ 10.854."
  3. In `papers/paper35_qec_holography/paper_draft.tex:209–210` the
     phrasing already says "Fibonacci sub-sector of $SU(3)_{k=2}$";
     verify the figure axis labels (in `fig_code_distance_vs_fusion_spectrum`)
     match this — currently both notebooks render the figure via
     `fig_code_distance_vs_fusion_spectrum()` and the legend/x-label is
     not directly visible in the notebook source, so the figure should
     be regenerated and inspected.
- **Cache:** N/A.

### 6.1 — 🟡 REQUIRED — Technical notebook lacks any out-of-scope / scope-disclosure section

- **Gate:** AssumptionDisclosure / NarrativeGrounding
- **Location:** `notebooks/Phase6c4_QECHolography_Technical.ipynb`
  (entire notebook — search for "scope|deferred|out.of.scope|page curve"
  returns 0 hits).
- **Observed:** The Stakeholder notebook §6 ("Honest scope") explicitly
  lists four deferred items: (1) non-abelian horizon MTC is an inherited
  W3 hypothesis, (2) AdS/CFT spectrum identification deferred, (3)
  Yoshida-Kitaev decoder not constructed, (4) Page curve not reproduced.
  The Technical notebook contains *no* scope/deferred section. The
  `intro` cell mentions "10 substantive theorems / 0 sorry / 0 new
  axioms" but doesn't disclose what the formalization does *not* prove.
- **Evidence:** `grep -i "scope\|deferred\|page curve\|yoshida.kitaev decoder\|adS.CFT spectrum"` against Technical notebook returns no matches.
- **Expected:** A scope-disclosure markdown cell in the Technical
  notebook mirroring Stakeholder §6, before the Lean theorem inventory.
- **Fix:** Add a markdown cell after `p35t-7-md` and before `p35t-8-md`
  (or as part of `p35t-8-md`) listing the 4 deferred items, matching
  Stakeholder §6 verbatim.
- **Cache:** N/A.

### 6.2 — 🟡 REQUIRED — Technical §6 does not flag H_HorizonBoundaryCondition as a *tracked external hypothesis*

- **Gate:** AssumptionDisclosure
- **Location:** `notebooks/Phase6c4_QECHolography_Technical.ipynb`
  cell `p35t-6-md` line 367, cell `p35t-6-code` line 392 ("In Lean,
  the W3 H_HorizonBoundaryCondition.areaLeading field requires d_max > 1.")
- **Observed:** The Technical notebook §6 describes the W3 cross-bridge
  as if `H_HorizonBoundaryCondition` were an established structural fact
  ("the W3 hypothesis bundle ... holds (area-law / second-law /
  non-abelian envelope)"). It does not disclose that this is a
  **tracked external hypothesis** Prop in the Lean module — i.e., a
  Prop the project assumes but has not derived. Stakeholder §6 does
  flag this honestly: "This is an assumption inherited from Phase 6a
  Wave 3 (`H_HorizonBoundaryCondition.areaLeading`), itself a tracked
  external hypothesis."
- **Evidence:** `lean/SKEFTHawking/BHEntropyMicroscopic.lean:373–379`
  defines `structure H_HorizonBoundaryCondition` with `areaLeading`,
  `secondLaw`, `modularInvariant := True`, `anomalyMatch := True` —
  the last two fields are explicit `True` placeholders. The bundle is
  externally tracked (project memory `feedback_tracked_hypothesis_nontrivial.md`).
  CLAUDE.md preemptive-strengthening discipline question 5 (
  "Defining-the-conclusion check") explicitly addresses this class.
- **Expected:** Technical §6 should add a sentence such as:
  "`H_HorizonBoundaryCondition` is a *tracked external hypothesis*
  Prop (W3 §4) — the project asserts but has not derived these
  conditions from microscopic dynamics; two of its five conjuncts
  (`modularInvariant`, `anomalyMatch`) are placeholder `True` props
  pending future formalization."
- **Fix:** Add disclosure prose to `p35t-6-md` at end of paragraph.
- **Cache:** N/A.

### 6.3 — 🟡 REQUIRED — "Universal recovery" phrasing in Stakeholder §4 lacks decoder-not-constructed caveat

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6c4_QECHolography_Stakeholder.ipynb`
  cell `p35s-4-md` lines 188–197 ("the Lean theorem
  `recovery_at_scrambling_bound` says **yes, universally — for any
  encoding choice.**")
- **Observed:** Stakeholder §4 frames the Lean theorem as "Hayden-Preskill
  universal recovery." The actual Lean content
  (`QECHolographyBridge.lean:167–185`) is the threshold inequality
  `Real.log d_encode ≤ Real.log D²` — i.e., the Hayden-Preskill
  *information-theoretic* threshold is met universally. The proof
  case-splits on `d_encode ≥ 1` vs `< 1` and uses `D² ≥ d_encode²`. No
  decoder is constructed; no recovery dynamics is implemented; no
  fidelity claim is proved. A reader trained on the original
  Hayden-Preskill paper (which constructs an explicit Haar-random
  decoder via decoupling) may interpret "universal recovery" as the
  full protocol.
- **Evidence:** Stakeholder §6 disclosure ("We assert recovery is
  possible at the bound but do not construct the explicit decoding
  circuit") is present, but the §4 phrasing on its own is not
  caveated; readers skipping §6 will receive an overclaim.
- **Expected:** §4 prose should add inline qualifier: "(the
  *threshold* form: `log d_a ≤ log D²`; an explicit decoder is *not*
  constructed — see §6)." Alternatively, change the section heading
  from "Universal recovery at the Hayden-Preskill bound" to "Universal
  recovery threshold at the Hayden-Preskill bound" to mirror the actual
  Lean content.
- **Fix:** Patch `p35s-4-md` markdown.
- **Cache:** N/A.

### 6.4 — 🔵 RECOMMENDED — Biconditional phrased as "$\exists$ non-abelian anyon" but Lean states `1 < d_max`

- **Gate:** AssumptionDisclosure
- **Location:** `notebooks/Phase6c4_QECHolography_Stakeholder.ipynb`
  cell `p35s-3-md` line 159 ("$\text{code distance } d_C > 0 \iff \exists
  \text{ a non-abelian anyon } (d_a > 1).$")
- **Observed:** The Stakeholder §3 prose states the structural identity
  in existential form. The actual Lean theorem
  `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class`
  states `0 < codeDistance ↔ 1 < d_max`. These are equivalent in the
  presence of the `HorizonMTCBC.d_max_attained` field
  (`BHEntropyMicroscopic.lean:301`), but the existential form is not
  the named theorem statement. The Lean module *also* provides
  `nonabelian_anyon_implies_codeDistance_pos`
  (`QECHolographyBridge.lean:265–271`) for the forward existential
  direction; the converse `1 < d_max → ∃ a, d_a > 1` follows from
  `d_max_attained`. So the equivalence does hold, but the prose
  collapses two theorems into one.
- **Evidence:** The Lean biconditional uses `H.horizon.d_max`, a
  scalar field, not an existentially quantified statement.
- **Expected:** Either (a) restate as
  `d_C > 0 ⟺ d_max > 1` with a one-line reminder that
  `d_max` is attained on some simple object, or (b) cite both Lean
  theorems instead of folding them.
- **Fix:** Two-word adjustment in the LaTeX equation in `p35s-3-md`.
- **Cache:** N/A.

### 7.1 — 🔵 RECOMMENDED — Project memory says "8 substantive theorems (was 10; -2 strengthening cuts)"; current count is 10

- **Gate:** CountFreshness
- **Location:** Memory note `project_phase6c_w4_shipped.md` (loaded in
  this session's CLAUDE.md MEMORY index): "**8 substantive thms** (was
  10; -2 strengthening cuts)". Notebooks/paper say "10 substantive
  theorems"; counts.tex `\qecHolographyThms{10}`; `grep -c "^theorem "`
  on the Lean module returns **10**.
- **Observed:** Counts in artifacts (notebook intro, paper abstract,
  paper §6) all agree at 10, matching counts.tex and the Lean grep.
  The memory index entry says 8. This is a memory-state staleness, not
  an artifact bug. Flagging because the user may rely on the memory
  index for review prep and could be misled.
- **Evidence:**
  - `lean/SKEFTHawking/QECHolographyBridge.lean` `grep -c "^theorem "` = 10
  - `docs/counts.tex:37` `\newcommand{\qecHolographyThms}{10}`
  - Notebook Technical cell `p35t-8-md` line 1 ("10 substantive")
  - Paper `paper_draft.tex:46` `\qecHolographyThms{}` (= 10)
- **Expected:** Memory index entry to be updated to 10.
- **Fix:** Update memory file `project_phase6c_w4_shipped.md` count.
  No artifact change needed.
- **Cache:** N/A.

## QI Candidate

A systemic gap surfaces here: **notebook prose can drift from the
spectrum names used in the underlying Python data**, and the validate.py
pipeline does not currently catch it. Specifically:

1. Finding 5.2: `MTCSpectrum.name = "su3_k2_fibonacci_subsector"` in
   Python source, but the notebook print/table label string is
   `"SU(3)_{k=2}"`. There is no automated check that notebook display
   labels match the canonical Python `name`.
2. Finding 5.1: A *quantitative* claim ("minimal-d_C") repeated across
   two notebooks + paper + Lean docstring + figure caption is
   contradicted by the data printed in the *same* notebook tables. No
   pipeline check verifies that prose ordering claims match the data
   ordering they sit next to.

**QI suggestion:** add `validate.py --check notebook_label_consistency`
that diffs every printed label string in `.ipynb` cells against the
`MTCSpectrum.name` (or analogous canonical-name field) of the object it
sources from, and `--check notebook_ordering_claims` that verifies any
"minimal/maximal/smallest/largest" prose claim against the numeric
data in the same cell. Stage 13 currently relies on a fresh-context
human reviewer to catch these — automating the easier half (label
match) reclaims most of the cost, and the harder half (claim ↔ data
ordering) is approachable via a small NLP heuristic.
