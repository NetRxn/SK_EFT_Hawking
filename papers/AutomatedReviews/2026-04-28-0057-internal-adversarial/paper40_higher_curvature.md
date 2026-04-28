---
paper: paper40_higher_curvature
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T00:57:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper40_higher_curvature

## Summary

Eight findings: 4 BLOCKER, 3 REQUIRED, 1 RECOMMENDED. Gates affected:
CitationIntegrity (Gate 1), CrossPaperConsistency (Gate 2),
ParameterProvenance (Gate 3), AssumptionDisclosure (Gate 6),
NarrativeGrounding (Gate 7). The paper is **NOT submission-ready**.
Core finding: the `CalmetCapozzielloPryer2019` bibitem is a wrong-target
citation — arXiv:1905.13728 is a graph-neural-networks paper, not the
claimed higher-curvature gravity reference, and INSPIRE has no
Calmet/Capozziello/Pryer co-authorship at all. The four observational
ceilings (`hc_bound_LIGO`, `hc_bound_SRG`, `hc_bound_pulsar`,
`hc_bound_cassini`) are therefore unattributed and must be re-anchored
to verifiable primary sources before any quantitative comparison stands
up. The Berti2015 venue is also wrong (CQG 32, 243001, not Living Rev
Rel 18, 1). The Lean algebra and basis-change identity verify
correctly; the structural Lean content is sound.

## Findings

### 1.1 — 🔴 BLOCKER — Wrong-target arXiv ID for `CalmetCapozzielloPryer2019`

- **Gate:** CitationIntegrity
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex:355-359`; registry `src/core/citations.py:2067-2083`
- **Observed:** Bibitem cites X. Calmet, S. Capozziello, D. Pryer,
  "Bounds on the higher-curvature corrections to general relativity",
  Eur. Phys. J. C 79, 706 (2019), [arXiv:1905.13728].
- **Evidence:** WebFetch of `https://arxiv.org/abs/1905.13728` returns
  title "Pre-Training Graph Neural Networks for Generic Structural
  Feature Extraction" by Hu, Fan, Chen, Chang, Sun — a machine-learning
  paper with no relation to gravity. INSPIRE-HEP queries
  `author Calmet author Capozziello author Pryer`,
  `title "Bounds on the higher-curvature corrections"`, and
  `eprint 1905.13728` all return zero hits. The Calmet/Capozziello/Pryer
  co-authorship does not appear in INSPIRE at all.
- **Expected:** Either a verifiable primary source for the four
  dimensionless higher-curvature observational ceilings (LIGO, SRG,
  pulsar, Cassini) or removal of the bibitem and the bound numbers it
  underwrites.
- **Fix:** (a) Identify the actual primary sources for each of the four
  bounds individually — Calmet's higher-curvature work is real but
  appears in a different paper (possibly Calmet & Latosh 2018,
  arXiv:1801.04942 or Calmet 2014, arXiv:1404.0360 — verify directly).
  (b) Update bibitem AND `CITATION_REGISTRY['CalmetCapozzielloPryer2019']`
  AND `Lean docstring references in HigherCurvatureStructure.lean §5
  (lines 213, 219, 229) which all cite "Calmet et al 2021" or "Calmet,
  Capozziello, Pryer, arXiv:1905.13728". (c) Re-fetch and append a
  `wrong_target` verdict record to `docs/citation_verifications.jsonl`.
- **Cache:** fresh-fetch (no prior verification record for this bibkey)

### 1.2 — 🔴 BLOCKER — Wrong venue for `Berti2015`

- **Gate:** CitationIntegrity
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex:361-366`; registry `src/core/citations.py:2084-2099`
- **Observed:** Bibitem and registry both report "Living Rev. Relativity
  18, 1 (2015)"; DOI `10.1007/lrr-2015-1`.
- **Evidence:** WebFetch of `https://arxiv.org/abs/1501.07274` returns
  title "Testing General Relativity with Present and Future
  Astrophysical Observations" — correct title — but journal-ref is
  **Class. Quantum Grav. 32, 243001 (2015)** (Berti, Barausse, Cardoso,
  Gualtieri, Pani, Sperhake, Stein, Wex, Yagi, et al.). Living Reviews
  in Relativity Vol 18 (2015) does NOT include this paper.
- **Expected:** Bibitem and registry to read "Class. Quantum Grav. 32,
  243001 (2015)" with DOI `10.1088/0264-9381/32/24/243001`.
- **Fix:** Update both bibitem fields and `CITATION_REGISTRY['Berti2015']`
  fields (`journal`, `volume`, `page`, `doi`). Append `wrong_venue`
  verdict to citation cache.
- **Cache:** fresh-fetch

### 1.3 — 🔴 BLOCKER — Six bibitems have `doi_verified: None` (registry not flipped after web-verification)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:2009, 2027, 2044, 2060, 2076, 2093`
  (all six paper40 bibitems: Vassilevich2003, ChristensenDuff1979,
  Stelle1977, Lovelock1971, CalmetCapozzielloPryer2019, Berti2015)
- **Observed:** All six entries have `doi_verified: None`. Gate 1 of
  READINESS_GATES.md requires `arxiv_verified == True AND
  doi_verified == True (where applicable)` for submission.
- **Evidence:** `grep -n "doi_verified" src/core/citations.py` on the
  six entries returns `None` for each.
- **Expected:** After fresh WebFetch confirmation, the four
  verifiable-as-correct entries (Vassilevich2003 ✓, Stelle1977 ✓ via
  INSPIRE, Lovelock1971 — DOI redirects to JMP article page but couldn't
  parse, ChristensenDuff1979 — DOI redirected to Elsevier but content
  blocked, Berti2015 with corrected venue) should be flipped to
  `doi_verified: True`. CalmetCapozzielloPryer2019 must be left at
  `False` until a real primary source is identified (1.1).
- **Fix:** Run a WebFetch sweep on each, flip `doi_verified`, append
  records to `docs/citation_verifications.jsonl`. Memory directive
  `feedback_citation_verification_required.md` explicitly warns: "never
  trust `doi_verified`; hallucinated citations DO occur." That memory's
  failure mode is the present finding's failure mode.
- **Cache:** fresh-fetch in this review for Vassilevich2003 and Berti2015
  (verified); ChristensenDuff/Stelle/Lovelock DOI fetches blocked by
  publisher 403/303 — flag for follow-up

### 2.1 — 🟡 REQUIRED — Vassilevich2003 shared between paper39 & paper40, no contradiction but cross-paper bibitem text not byte-identical

- **Gate:** CrossPaperConsistency
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex:339-343` vs
  `papers/paper39_heat_kernel_expansion/paper_draft.tex` (around line 486-490)
- **Observed:** Both papers cite arXiv:hep-th/0306138 with title "Heat
  kernel expansion: user's manual" — this is consistent. Submission
  Gate 2 passes for this bibkey (shared bibkey resolves to same arXiv
  ID). Flagging only as advisory because of cross-paper bibkey reuse;
  any future edit must update both copies.
- **Evidence:** `grep` confirmed identical arXiv ID + title in both
  papers; CITATION_REGISTRY entry's `used_in` list contains both.
- **Expected:** No action; informational.
- **Fix:** None required. RECOMMENDED that any future edit propagate to
  both bibitems atomically (Gate 11 FixPropagation lever).
- **Cache:** cache-verified (Vassilevich2003 has stable bibitem hash)

### 3.1 — 🔴 BLOCKER — All four observational-bound parameters lack `PARAMETER_PROVENANCE` entries with verified sources

- **Gate:** ParameterProvenance
- **Location:** `lean/SKEFTHawking/HigherCurvatureStructure.lean:215, 220,
  226, 230` — `hc_bound_LIGO = 10^62`, `hc_bound_SRG = 10^61`,
  `hc_bound_pulsar = 10^59`, `hc_bound_cassini = 10^62`. Same numbers in
  `src/higher_curvature/observational_bound_check.py:20-25 HC_OBS_BOUNDS`.
- **Observed:** The four numerical ceilings used in the entire
  correctness-push come from `CalmetCapozzielloPryer2019` (per docstring
  comments) and `Berti2015` (for the pulsar). Per Finding 1.1 the
  Calmet bibitem is wrong-target; per 1.2 the Berti venue is wrong.
  Therefore none of the four ceilings has a verified primary-source
  anchor. Gate 3 requires `human_verified_date` and a primary-source
  citation that itself passes Gate 1.
- **Evidence:** `grep "HC_OBS_BOUNDS\|hc_bound" src/core/constants.py`
  returns no results — the bounds are not even in the canonical
  `constants.py` file (which CLAUDE.md Pipeline Invariant 2 names as
  the only place experimental parameters live). They live in
  `src/higher_curvature/observational_bound_check.py` only, with no
  PARAMETER_PROVENANCE entry.
- **Expected:** Each of the four bounds gets a `PARAMETER_PROVENANCE`
  entry in `src/core/provenance.py` with a primary-source paper
  (likely four DIFFERENT primary sources: GW170817 LIGO/Virgo paper for
  speed-of-graviton; Eöt-Wash Adelberger group paper for short-range
  gravity; Hulse-Taylor or Damour-Taylor paper for the binary-pulsar
  bound; Bertotti-Iess-Tortora 2003 for Cassini). The paper-level claim
  "the predicted Wave 1 coefficients sit at $\mathcal{O}(10^{-3})$,
  some 62 orders of magnitude below" depends on this anchor.
- **Fix:** (a) Move `HC_OBS_BOUNDS` to `src/core/constants.py` per
  Invariant 2. (b) Add four `PARAMETER_PROVENANCE` entries, each with
  primary source identified independently. (c) WebFetch and verify each
  primary source. (d) Set `llm_verified_date`; `human_verified_date`
  before submission.
- **Cache:** N/A (provenance gap, not citation cache)

### 5.1 — 🟡 REQUIRED — Inconsistent reference attribution: "Calmet et al 2021" in Lean docstring vs "Calmet et al 2019" in bibitem

- **Gate:** NarrativeGrounding (drift between Lean docstring and paper)
- **Location:** `lean/SKEFTHawking/HigherCurvatureStructure.lean:33`
  ("Observational ceilings (Calmet et al. 2021, Berti et al. 2015)"),
  line 220 ("Reference: Calmet et al 2021"), line 230
  ("Reference: Calmet et al 2021") vs paper bibitem
  `CalmetCapozzielloPryer2019` and registry year 2019.
- **Observed:** Lean docstring repeatedly cites "Calmet et al 2021";
  paper, registry, and bibitem all say 2019. With Finding 1.1 unresolved
  the year is moot, but the inconsistency is itself a Gate 6 / drift
  signal: the docstring's reference target may differ from the paper's.
- **Evidence:** `grep -n "Calmet" lean/SKEFTHawking/HigherCurvatureStructure.lean`
  returns three "2021" occurrences; paper bibitem has "(2019)".
- **Expected:** A single year, after the actual Calmet primary source is
  identified.
- **Fix:** After 1.1 is resolved, propagate the corrected year to both
  Lean docstring and paper.
- **Cache:** N/A

### 6.1 — 🟡 REQUIRED — `H_HigherCurvatureWithinObservationalBounds` predicate referenced in paper but tracked-hypothesis nature not disclosed

- **Gate:** AssumptionDisclosure
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex:259-272`
- **Observed:** Paper says "The Lean Prop predicate
  `H_HigherCurvatureWithinObservationalBounds B` is a tracked hypothesis
  parameterised by an upper bound B" — the word "tracked hypothesis" is
  used, but the paper does not name what external hypothesis is being
  tracked or what it is conditional on. By project convention (memory
  `feedback_tracked_hypothesis_nontrivial.md`) tracked-hypothesis Props
  carry a load-bearing assumption that must be defended externally. The
  paper also fails to list which Lean hypothesis parameters apply to
  `higher_curvature_below_pulsar_bound` (`0 < N_f` and `N_f ≤ 100`) in
  prose. Both `hN_pos` and `hN_max` are load-bearing for the cited
  result; the paper text in §5 only says "natural fermion-count window
  $0 < N_f \le 100$" inline once, which is acceptable but should also
  be explicitly named where the theorem statement is cited (§4 main
  theorem block).
- **Evidence:** Lean `H_HigherCurvatureWithinObservationalBounds B` body
  (line 382-387 of HigherCurvatureStructure.lean) is `0 < B ∧ ∀ N_f, ...
  → ... ≤ B ∧ ... ≤ B ∧ ... ≤ B`. The pulsar-witness instance proof
  consumes `higher_curvature_below_pulsar_bound`, which itself imposes
  `0 < N_f` and `N_f ≤ 100`. The paper labels this as a "tracked
  hypothesis" but in fact the predicate is *proved* (witnessed) at
  `B = 10^59`; it carries no undischarged hypothesis. This is a
  terminology mismatch — calling a fully-proved Prop a "tracked
  hypothesis" misleads the reader.
- **Expected:** Either rename in prose to "verified upper-bound predicate"
  / "instance-witnessed Prop" and disclose the `0 < N_f ≤ 100` window as
  the only hypothesis, OR keep the "tracked hypothesis" terminology but
  identify the genuinely external assumption (e.g., the
  observational bound itself, which IS external — Finding 3.1).
- **Fix:** Rewrite §4 final paragraph to: "The Prop predicate ... is
  parameterised by an upper bound B (externally fixed by an
  observational ceiling); the pulsar-witness theorem proves the
  predicate at $B = 10^{59}$ unconditionally for the natural window
  $0 < N_f \le 100$." This separates "B is the external assumption"
  (correct framing) from "the predicate is unproved" (incorrect).
- **Cache:** N/A

### 7.1 — 🔵 RECOMMENDED — "62 orders of magnitude below" feasibility-claim is unanchored quantitatively in prose

- **Gate:** NarrativeGrounding
- **Location:** `papers/paper40_higher_curvature/paper_draft.tex:50-51,
  220-221, 320-321` (abstract, fig caption, conclusion all repeat the
  "62 orders of magnitude below" framing).
- **Observed:** The "$\sim 62$ orders of magnitude below" is computed
  as $\log_{10}(10^{59} / 10^{-3}) = 62$. The $10^{-3}$ figure is
  asserted in prose ("the predicted Wave 1 coefficients sit at
  $\mathcal{O}(10^{-3})$") but the order-of-magnitude derivation is not
  shown. For the dominant Riemann² coefficient at $N_f = 27$:
  $|c_{\mathrm{Riem}}| = N_f / 180 / (4\pi)^2 = 27 / 180 / 157.91 \approx
  9.5 \times 10^{-4}$ ≈ $10^{-3}$ ✓. The number is correct but
  unanchored to the formula in the prose. With Findings 1.1 and 3.1
  the comparison itself is in question (numerator $10^{59}$ has no
  primary source); the headline claim is structurally weakened.
- **Evidence:** `python -c "print(27/180/(4*3.14159265**2))"` returns
  $9.49 \times 10^{-4}$, consistent with $\mathcal{O}(10^{-3})$. The
  62-orders gap is verified arithmetically conditional on the bound
  number.
- **Expected:** Either (a) inline the computation in prose ("at
  $N_f = 27$, $|c_{\mathrm{Riem}}|/(4\pi)^2 \approx 9.5\times 10^{-4}$,
  yielding ratio to $10^{59}$ of $\sim 10^{62}$"), or (b) reference the
  Python test that computes the ratio. Currently the reader must
  reconstruct it.
- **Fix:** Add a one-sentence quantitative anchor in §5 between the bound
  list and the figure caption.
- **Cache:** N/A

## QI Candidate

The systemic issue this review surfaces: **`doi_verified: None` is
the registry's default state, and shipping a wave puts six bibitems
into the registry without flipping the flag.** Memory
`feedback_citation_verification_required.md` (2026-04-26) already named
this failure mode; one day later, six paper40 bibitems landed in the
same state. A pre-Stage-13 gate that refuses to ship a paper with any
`doi_verified: None` bibitem in its citation set would have caught
this, AND would have forced the WebFetch sweep that surfaced 1.1 (the
wrong-target arXiv ID) and 1.2 (the wrong Berti venue) before paper
prose was written around them. Recommended QI: add
`validate.py --check no_unverified_paper_citations` that fails any
paper whose bibitems include `doi_verified ∈ {None, False}` for entries
where a DOI is registered.
