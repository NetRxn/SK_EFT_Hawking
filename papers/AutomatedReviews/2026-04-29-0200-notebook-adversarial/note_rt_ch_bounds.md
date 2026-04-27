---
paper: note_rt_ch_bounds
artifact: notebooks/Phase6c5_RTCasiniHuerta_{Technical,Stakeholder}.ipynb
reviewer: adversarial-reviewer (notebook-adapted)
model: claude-opus-4-7
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — note_rt_ch_bounds (notebook pair)

## Summary

Fresh-context adversarial review of the technical and stakeholder notebooks
companioning the RT-vs-Kaul-Majumdar formalization note. Five bibitems verified
(three fresh-fetched, two cache-hit); all five citation targets resolve. The
knife-edge biconditional in Lean is genuinely substantive (not a definitional-
unfolding tautology). The Sen 77/45 / 212/45-3 anchor is internally consistent.
**One BLOCKER**: the notebook + paper both attribute the universal
`(c/3) log(L/eps)` 2D-CFT entanglement-entropy bound to Casini-Huerta 2009
(arXiv:0905.2562), but that paper is restricted to **free** QFTs; the universal
2D-CFT result is from Holzhey-Larsen-Wilczek (1994) and Calabrese-Cardy (2004,
hep-th/0405152). Three REQUIRED items (one quantitative-anchor naming nuance,
one out-of-scope-disclosure tightening, one Lean-attribution check). Two
RECOMMENDED. Notebooks are not submission-ready until the CH-attribution
BLOCKER is resolved.

## Findings

### 1.1 — 🔴 BLOCKER — Casini-Huerta 2009 cited as the source of the universal `(c/3) log(L/eps)` 2D-CFT bound; that paper is restricted to free QFTs

- **Gate:** CitationIntegrity (also borders NarrativeGrounding)
- **Location:**
  - `papers/note_rt_ch_bounds/paper_draft.tex:36-38` (abstract): "the
    Casini-Huerta entanglement-entropy log bound~\cite{CasiniHuerta2009}
    $S(L) \le (c/3) \log(L/\varepsilon)$"
  - `paper_draft.tex:113-129` (§2 Casini-Huerta paragraph): same attribution
  - `paper_draft.tex:269-272` (bibitem): "H. Casini and M. Huerta,
    'Entanglement entropy in free quantum field theory,' J. Phys. A 42,
    504007 (2009); arXiv:0905.2562"
  - `notebooks/Phase6c5_RTCasiniHuerta_Technical.ipynb` cell `rtch-t-1-md`:
    "the Casini-Huerta bound asserts $S_{\rm ent}(L) \le (c/3)\log(L/\epsilon)$"
  - `notebooks/Phase6c5_RTCasiniHuerta_Stakeholder.ipynb` cell `rtch-s-intro`
    + `rtch-s-4-md`: "Casini and Huerta (2009) provided a model-independent
    upper bound on entanglement entropy in 2D conformal field theory:
    $S_{\rm ent}(L) \leq (c/3)\log(L/\epsilon)$. The bound is tight for
    free CFTs."
  - `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:11-13,55-56`: header
    docstring identifies the result as "the Casini-Huerta (2009,
    arXiv:0905.2562) log bound `S(L) ≤ (c/3) log(L/ε)` on entanglement
    entropy in 2D CFTs"
  - `src/rt_ch_bounds/__init__.py:25-26`: "Casini-Huerta J. Phys. A 42,
    504007 (2009); arXiv:0905.2562" listed as primary reference for the bound
- **Observed:** WebFetch of arXiv:0905.2562 (fresh fetch this review):
  - Title: "Entanglement entropy in **free quantum field theory**"
  - Abstract excerpt (verbatim from arXiv): "In this review we first
    introduce the general methods to calculate the entanglement entropy
    for **free fields**, within the Euclidean and the real time
    formalisms. ... particular examples which have been worked out
    explicitly in two, three and more dimensions."
  - This is a **review of free-field entanglement entropy**, not a derivation
    of the universal `(c/3) log(L/eps)` 2D-CFT result.
- **Evidence:** The universal 2D-CFT formula `S = (c/3) log(L/eps)` was first
  derived by Holzhey, Larsen, Wilczek 1994 (Nucl. Phys. B 424, 443;
  hep-th/9403108) and later extended/popularized by Calabrese, Cardy 2004
  (J. Stat. Mech. P06002; hep-th/0405152). WebFetch of hep-th/0405152
  confirms Calabrese-Cardy explicitly: "we re-derive the result
  S_A ~ (c/3) log(l) of Holzhey et al. when A is a finite interval of
  length l in an infinite system." The (c/3) prefactor depends only on
  central charge — universal across **all** 2D CFTs, not just free ones.
- **Expected:** The universal 2D-CFT log bound `(c/3) log(L/eps)` should
  be attributed to Holzhey-Larsen-Wilczek 1994 and/or Calabrese-Cardy 2004.
  Casini-Huerta 2009 is appropriate as a *review* / supporting citation but
  is not the primary source for the universal CFT result. The stakeholder
  notebook's claim "Casini and Huerta (2009) provided a model-independent
  upper bound on entanglement entropy in 2D conformal field theory" is
  factually incorrect — that paper restricts to free QFTs.
- **Fix:** Three coordinated changes:
  1. Add `Calabrese-Cardy 2004` (hep-th/0405152, J. Stat. Mech. P06002) and/or
     `Holzhey-Larsen-Wilczek 1994` (hep-th/9403108, Nucl. Phys. B 424, 443)
     to `src/core/citations.py` `CITATION_REGISTRY` and to the paper's
     `\begin{thebibliography}` block.
  2. Replace the Casini-Huerta primary attribution with Calabrese-Cardy
     (or Holzhey et al.) in the abstract, §2 paragraph, both notebooks,
     the Lean module header, and `src/rt_ch_bounds/__init__.py`. Keep
     Casini-Huerta as a supporting / review citation.
  3. The stakeholder notebook explicitly says "The bound is tight for free
     CFTs" — that is correct, but doesn't rescue the attribution: the bound
     itself (universal in 2D CFTs by central charge) is not Casini-Huerta's.
- **Cache:** fresh-fetch (this review) for arXiv:0905.2562 and
  hep-th/0405152.

### 1.2 — 🔵 RECOMMENDED — Ryu-Takayanagi title in registry differs from arXiv canonical title (registry verbose form vs arXiv abbreviated form)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:2940-2941`,
  `papers/note_rt_ch_bounds/paper_draft.tex:264-267`
- **Observed:** Registry and bibitem say "Holographic derivation of
  entanglement entropy from anti-de Sitter space/conformal field theory
  correspondence"; fresh-fetch of arXiv:hep-th/0603001 returns
  "Holographic Derivation of Entanglement Entropy from AdS/CFT".
- **Evidence:** Both forms point at the same paper (PRL 96, 181602). The
  long form is the journal-version expansion of the abbreviation; PRL
  itself uses both at different places.
- **Expected:** Either form is defensible. Mention here for tracking
  consistency only.
- **Fix:** Optional — pick one form for `CITATION_REGISTRY` and use it
  uniformly across paper, notebooks, and Lean docstrings. No correctness
  impact.
- **Cache:** fresh-fetch (this review).

### 1.3 — match — Casini-Huerta 2009 metadata verifies (arXiv ID + venue + year + DOI all match registry)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:2956-2970`, paper bibitem
  `paper_draft.tex:269-272`
- **Observed:** WebFetch arXiv:0905.2562 returned: "Entanglement entropy in
  free quantum field theory" by H. Casini, M. Huerta;
  J. Phys. A 42:504007 (2009); DOI 10.1088/1751-8113/42/50/504007. All
  fields match registry.
- **Cache:** fresh-fetch (this review). No finding for cite-target accuracy
  itself; the misattribution-of-result issue is finding 1.1.

### 1.4 — match — Lewkowycz-Maldacena 2013 metadata verifies

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:2972-2987`,
  `paper_draft.tex:279-282`
- **Observed:** WebFetch arXiv:1304.4926 returned: "Generalized gravitational
  entropy" by Aitor Lewkowycz, Juan Maldacena; JHEP Vol. 2013, Article 090
  (August 2013); DOI 10.1007/JHEP08(2013)090. All fields match.
- **Cache:** fresh-fetch (this review).

### 1.5 — match — Kaul-Majumdar 2000 cache-verified

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:274-277`,
  `docs/citation_verifications.jsonl` entry dated 2026-04-26T03:10:00+00:00
- **Observed:** Cache hit, verdict=match. PRL 84, 5255-5257 (2000);
  arXiv:gr-qc/0002040.
- **Cache:** cache-verified.

### 1.6 — match — Sen 2013 cache-verified

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:284-287`,
  `docs/citation_verifications.jsonl` entry dated 2026-04-26T03:10:00+00:00
- **Observed:** Cache hit, verdict=match. JHEP 04:156 (2013);
  arXiv:1205.0971.
- **Cache:** cache-verified.

### 2.1 — 🔵 RECOMMENDED — Sen log coefficient `212/45 - 3 = 77/45 ≈ 1.711` is internally consistent but secondary-fetch verification of the explicit "212/45" rational form was not obtained

- **Gate:** ParameterProvenance
- **Location:**
  - `paper_draft.tex:75-79` (introduction) cites "Sen's 4D Schwarzschild
    log coefficient $77/45 \approx 1.711$"
  - `lean/SKEFTHawking/BHEntropyMicroscopic.lean:129`:
    `senFourDimSchwarzschildLogCoeff : ℝ := (212 : ℝ) / 45 - 3`
  - `notebooks/.../Technical.ipynb` cell `rtch-t-7-code`: "= 77/45 = 212/45 - 3"
  - `src/rt_ch_bounds/rt_comparison.py:67`: `return 212.0 / 45.0 - 3.0`
- **Observed:** Internal consistency verified: `212/45 - 3 = (212 - 135)/45
  = 77/45 ≈ 1.7111`, and the gap to `-3/2` is `77/45 + 3/2 =
  (154 + 135)/90 = 289/90 ≈ 3.2111`. All numerically self-consistent and
  the cache previously matched the citation target (Sen JHEP 04, 156 (2013)).
  However, fresh WebFetch attempts on the arXiv abstract and PDF for
  arXiv:1205.0971 in this review did **not** surface the explicit "212/45"
  rational form within the abstract (PDF binary fetch was incomplete; the
  abstract simply notes "disagreement with loop quantum gravity results").
- **Evidence:** The 212/45 form is consistent with Sen's heat-kernel
  methodology — typical 4D Schwarzschild matter-content sums produce
  rationals over 45. Project memory (`project_phase6a_track_c_status.md`)
  records the 212/45-3 = 77/45 anchor as Sen's value. The cache-verified
  match certifies the citation target is right. But the **specific rational
  form** "212/45 minus 3" was not pinned to a primary-source
  equation/table/figure number anywhere in `PARAMETER_PROVENANCE` that
  I could find.
- **Expected:** A `PARAMETER_PROVENANCE` entry for `senFourDimSchwarzschildLogCoeff`
  pinning it to a specific equation or table number in arXiv:1205.0971
  (the 77/45 value should appear in Sen 2013 §3 or §4 / a table summarizing
  4D black-hole results). Reviewer-side primary-source-equation-pin would
  let a future reader land on the exact line that justifies the rational.
- **Fix:** Either (a) cite the exact equation number in the docstring of
  `senFourDimSchwarzschildLogCoeff` and the bibitem, or (b) acknowledge in
  the paper / Sen-related project notes that the specific rational form is
  taken from a derivation chain (not a single tabulated equation), with a
  pointer to where the calculation lives in Sen 2013. The notebook prose
  "(= 77/45 = 212/45 - 3)" is fine as is; the registry-side primary-source
  pin is the missing piece.
- **Cache:** fresh-fetch (Sen abstract retrieval was uninformative; full PDF
  binary did not parse). Cache match for the citation target stands.

### 3.1 — match — Knife-edge biconditional `rt_eq_kaulMajumdar_iff_trivial_reduced_area` is genuinely substantive (not a tautology hidden by definitional unfolding)

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:159-171`
- **Observed:** The biconditional statement is
  `A / (4 * G_N) = kaulMajumdarS A G_N 0 ↔ A / (4 * G_N) = 1`. The proof
  body unfolds `kaulMajumdarS A G_N 0` to
  `A/(4 G_N) - (3/2) log(A/(4 G_N)) + 0`, then:
  - Forward: from `A/(4 G_N) = A/(4 G_N) - (3/2) log(A/(4 G_N)) + 0`,
    extracts `Real.log (A/(4 G_N)) = 0` via `linarith`, then uses
    `Real.exp_log h_pos` (positivity of `A/(4 G_N)`) and
    `Real.exp_zero` to conclude `A/(4 G_N) = 1`.
  - Reverse: from `A/(4 G_N) = 1`, uses `Real.log_one` (and `ring`).
- **Evidence:** The forward direction's substantive content is
  `Real.log x = 0 ∧ 0 < x → x = 1`, which is genuinely non-trivial — it
  uses injectivity of `exp` on positives (via `exp ∘ log = id` on `(0, ∞)`).
  This is **not** discharged by `rfl`, `decide`, or definitional unfolding
  alone; it requires `Real.exp_log` (Mathlib library lemma about the
  inverse function relationship).
- **Verdict:** No tautology. The `iff` carries real mathematical content.
  The notebook claim "Proof of forward direction extracts $\log = 0$ from
  the equality (using $\exp\circ\log = \mathrm{id}$); reverse direction
  uses $\log 1 = 0$" (cell `rtch-t-4-md`) accurately summarizes the proof.

### 3.2 — match — Quantitative anchor `rt_kaulMajumdar_gap_at_reduced_area_two = (3/2) log 2` is exact, not approximate

- **Gate:** LeanProofSubstance + ParameterProvenance
- **Location:** `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:128-136`
- **Observed:** Theorem statement: `let A := 8 * G_N; A / (4 * G_N) -
  kaulMajumdarS A G_N 0 = (3 / 2) * Real.log 2`. Proof unfolds
  `kaulMajumdarS`, computes `(8 * G_N) / (4 * G_N) = 2` via `field_simp;
  ring`, then closes with `ring`. The equality is exact in Lean's `ℝ`
  (not a `≈` / numerical approximation).
- **Evidence:** Notebook cells `rtch-t-3-code` and `rtch-s-2-code` confirm
  numerical match to 1e-12 tolerance: `(3/2) log 2 = 1.0397207708`,
  `gap_computed = 1.0397207708`. The notebook claim "exact — not asymptotic,
  not approximate" is faithful to the Lean proof.
- **Verdict:** No finding.

### 3.3 — 🟡 REQUIRED — Notebook + paper claim "Knife-edge agreement at $A = 4 G_N$" is correct but the paper's "they necessarily differ by exactly the log-correction term" is true *only because* the linear and constant parts cancel, not for any deeper reason

- **Gate:** NarrativeGrounding (overclaim, soft)
- **Location:**
  - `paper_draft.tex:30-33` (abstract): "agree only on the knife-edge case
    $A = 4\GN$ (reduced area unity); otherwise they necessarily differ by
    exactly the log-correction term"
  - `notebooks/.../Technical.ipynb` cell `rtch-t-4-md`: "Anywhere else, they
    disagree by exactly $(3/2)\log(A/(4 G_N))$"
- **Observed:** Phrasing implies a structural / conceptual punchline beyond
  algebra. In fact: the gap is just `kaulMajumdarS - linear =
  -(3/2) log(reduced)`, and `log(reduced) = 0 ⟺ reduced = 1`. The "exactly
  the log-correction term" phrasing is mathematically correct but tautological
  — `kaulMajumdarS` is *defined* as `linear - (3/2) log + c0`, so of course
  the gap equals the log term. There's no surprise; the surprise is just
  "log has a unique zero at 1".
- **Evidence:** The Lean theorem `kaul_majumdar_log_coefficient` in
  `BHEntropyMicroscopic.lean:104-108` literally states this:
  `kaulMajumdarS - reducedArea - c0 = (-3/2) * Real.log (reducedArea)`
  via pure `ring`. The current paper's framing of the gap as a "structural"
  result inflates a definitional-unfolding observation into a physics
  punchline.
- **Expected:** Either tighten the prose to acknowledge the algebraic
  triviality once the *form* of `kaulMajumdarS` is granted (the substantive
  content is the *form* of `kaulMajumdarS`, derived in Phase 6a Wave 3, not
  the gap formula here), or sharpen the punchline to be about the
  knife-edge uniqueness (a real consequence of `log` being strictly
  monotone, formalized by the biconditional).
- **Fix:** Recommended rewording in abstract / both notebook intros:
  > "The two formulas agree only on the knife-edge $A/(4 G_N) = 1$ — the
  > unique zero of `log` — and elsewhere differ by `(3/2) log(A/(4 G_N))`.
  > That the gap takes exactly this form is structurally guaranteed by
  > the *definition* of the Kaul-Majumdar entropy; the substantive content
  > here is the uniqueness of the knife-edge."
- **Cache:** n/a.

### 4.1 — match — Tracked-Prop disclosure is honest

- **Gate:** AssumptionDisclosure
- **Location:** `paper_draft.tex:97-129` (§2 External-hypothesis
  predicates), `notebooks/.../Technical.ipynb` cell `rtch-t-1-md`,
  `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:70-103`
- **Observed:** Both predicates `H_RT_Formula_Valid` and
  `H_CasiniHuerta_Bound_Valid` are clearly disclosed in the paper, in
  both notebooks, and in the Lean module header. The paper §1 says
  "we encode it as an external-hypothesis structural predicate" and
  §2 ships the verbatim Lean definitions. The stakeholder notebook
  cell `rtch-s-6-md` says "We take CH as a tracked external hypothesis,
  not a derived theorem".
- **Evidence:** All three `H_RT_Formula_Valid`-consuming theorems
  (`rt_entropy_pos`, `rt_falsified_by_kaul_majumdar`) take it as an
  explicit hypothesis. The CH bound's positivity theorem
  (`ch_log_bound_pos_at_log_pos`) and the saturated witness theorem
  both explicitly take `H_CasiniHuerta_Bound_Valid`. No undisclosed
  consumption.
- **Verdict:** No finding.

### 4.2 — 🟡 REQUIRED — Lean module docstring header references `kaulMajumdar_not_H_RT_in_Sen4D_branch` as a "concrete falsifier", but no such theorem exists in the module

- **Gate:** AssumptionDisclosure / LeanProofSubstance (drift between
  docstring-stated structure and shipped names)
- **Location:** `lean/SKEFTHawking/RTCasiniHuertaBounds.lean:25-27`:
  > "The W3 non-universality witness `sen_4d_disagrees_with_kaul_majumdar`
  > is invoked through `kaulMajumdar_not_H_RT_in_Sen4D_branch` as a
  > concrete falsifier."
- **Observed:** Grep for `kaulMajumdar_not_H_RT_in_Sen4D_branch` in the
  Lean module returns zero matches. The actual falsifier shipped is
  `kaulMajumdar_not_H_RT` (line 242), which uses `Real.log 2 > 0` and
  `linarith` — NOT a Sen-branch invocation. The Sen disagreement theorem
  `sen_4d_disagrees_with_kaul_majumdar` lives upstream in
  `BHEntropyMicroscopic.lean` and is not consumed in this module at all.
- **Evidence:** Direct grep confirms the docstring references a name that
  was never shipped. This is a Phase 6c Wave 5 docstring drift —
  consistent with project memory `feedback_python_lean_refs_drift.md` and
  cross-references the recurring class of issue.
- **Expected:** Either (a) ship `kaulMajumdar_not_H_RT_in_Sen4D_branch` as
  an actual theorem that consumes `sen_4d_disagrees_with_kaul_majumdar`,
  or (b) edit the module docstring to remove the phantom reference.
- **Fix:** Edit module docstring: replace lines 25-27 with the actual
  shipped name (`kaulMajumdar_not_H_RT`) and drop the Sen-branch claim,
  OR ship the cross-bridge theorem. The notebook does not propagate this
  phantom reference (it correctly cites `kaulMajumdar_not_H_RT` in cell
  `rtch-t-5-md`), so the impact is local to the Lean module.
- **Cache:** n/a.

### 5.1 — 🟡 REQUIRED — Notebook claim "first formalization" is implicit but not made explicit; should be stated honestly

- **Gate:** NarrativeGrounding
- **Location:**
  - `paper_draft.tex:54`: "ships \rtChThms{} substantive theorems with
    zero \texttt{sorry} statements and zero new axioms"
  - `notebooks/.../Stakeholder.ipynb` cell `rtch-s-6-md`: "Seven Lean
    theorems, zero sorry, zero new axioms. Cleanly."
- **Observed:** Neither paper nor notebook explicitly claims "first
  formalization in any proof assistant" of this RT-vs-Kaul-Majumdar
  comparison, but the framing implies novelty. Project memory
  `project_phase6c_w5_shipped.md` does not assert "first formalization"
  for this wave (unlike e.g. Phase 6f Wave 3 which explicitly does).
- **Evidence:** No explicit first-claim made; thus no falsifiable
  overclaim. Adversarial flagging is preventive: if the paper is later
  edited to add a first-claim (e.g., during Stage 13 strengthening), the
  claim should be backed by a literature search for prior formalizations
  of (a) Ryu-Takayanagi in any proof assistant, (b) any black-hole
  log-correction structural inconsistency theorem in any proof assistant.
  As of this review, neither has been searched.
- **Expected:** No first-claim is currently made, so no fix is required.
  Note this for future Stage-13 reruns: if a first-claim is added, the
  literature search must precede the prose change.
- **Fix:** No mechanical fix needed. Logged as preventive guidance.
- **Cache:** n/a.

### 6.1 — match — Out-of-scope items honestly disclosed

- **Gate:** NarrativeGrounding
- **Location:**
  - `paper_draft.tex:240-258` (§7 What is and is not done here)
  - `notebooks/.../Technical.ipynb` cell `rtch-t-9-md`: "Out of scope (per
    Phase 6c roadmap §A): bulk minimal-surface construction, full CH
    derivation from modular Hamiltonian, AdS/CFT spectrum identification"
  - `notebooks/.../Stakeholder.ipynb` cell `rtch-s-6-md`: same four items
    explicitly listed.
- **Observed:** All three notebooks/paper enumerate the deferred items
  (bulk minimal surface, modular Hamiltonian CH derivation, AdS/CFT
  dictionary). The stakeholder notebook adds a fourth honest disclosure:
  "Resolution of Sen vs Kaul-Majumdar. Both microscopic-counting answers
  are reported; the project formalizes Kaul-Majumdar but does not
  adjudicate against Sen." This is good practice.
- **Verdict:** No finding.

### 7.1 — match — Lean theorem inventory in notebook matches actual module content

- **Gate:** CountFreshness
- **Location:** `notebooks/.../Technical.ipynb` cell `rtch-t-9-md`
  inventory table.
- **Observed:** 7 substantive theorems listed: `rt_entropy_pos`,
  `rt_kaulMajumdar_gap_at_reduced_area_two`,
  `rt_eq_kaulMajumdar_iff_trivial_reduced_area`,
  `rt_falsified_by_kaul_majumdar`, `H_CasiniHuerta_Bound_Valid_witness_saturated`,
  `kaulMajumdar_not_H_RT`, `ch_log_bound_pos_at_log_pos`. Direct grep of
  `RTCasiniHuertaBounds.lean` confirms exactly these 7 theorems plus the 2
  `structure` definitions (`H_RT_Formula_Valid`, `H_CasiniHuerta_Bound_Valid`)
  documented as "tracked Prop structures" in the table. No drift.
- **Verdict:** No finding.

### 7.2 — 🔵 RECOMMENDED — Stakeholder notebook claim "minimal-surface area divided by 4 G_N" mixes RT (entanglement entropy) with Bekenstein-Hawking (horizon area)

- **Gate:** NarrativeGrounding (precision)
- **Location:** `notebooks/.../Stakeholder.ipynb` cell `rtch-s-intro`:
  "Ryu and Takayanagi (2006) made black-hole entropy *geometric* in
  AdS/CFT: $S_{\rm ent} = (\text{minimal-surface area})/(4 G_N)$."
- **Observed:** RT formalizes *entanglement entropy* of a CFT subregion as
  the area of a bulk minimal surface anchored on the boundary subregion,
  not "black-hole entropy" per se. The connection to BH entropy is via the
  special case where the bulk minimal surface is the horizon
  bifurcation surface. The current phrasing conflates the two.
- **Evidence:** Original RT paper (PRL 96, 181602): "Holographic Derivation
  of Entanglement Entropy from AdS/CFT" — the title itself is about
  entanglement entropy, not black-hole entropy.
- **Expected:** Tighten to "Ryu and Takayanagi (2006) made *entanglement
  entropy* in CFT geometric in AdS/CFT: the entanglement entropy of a
  boundary subregion is the area of a bulk minimal surface, divided by
  $4 G_N$. Specialized to a horizon bifurcation surface, this recovers
  Bekenstein-Hawking entropy."
- **Fix:** One-sentence rewrite of the stakeholder notebook intro
  paragraph.
- **Cache:** n/a.

## QI Candidate

**Issue:** This wave's primary citation-quality miss (finding 1.1) is
a recurring pattern: a *result* (the universal `(c/3) log(L/eps)`
2D-CFT bound) is attributed to a *paper that reviews* the result, not
the *paper that derives* it. The Casini-Huerta 2009 paper is a
canonical entanglement-entropy reference that **reviews** the
universal result alongside many other free-field results, but the
universal result's primary sources are Holzhey-Larsen-Wilczek 1994
and Calabrese-Cardy 2004.

This is structurally the same failure class as `feedback_deep_research_analog_conflation.md`
(Wave 5 shipped with Jacobson-Kang 1998 / Visser 1998 conflated with
Balbinot 2005), and `feedback_citation_verification_required.md`
(WetterichNJL hallucinated venue). The pipeline should treat
**citation-of-result** as distinct from **citation-of-target**:

- citation-of-target: "this paper exists and has these metadata" —
  caught by `WebFetch` against arXiv. Cache amortizes.
- citation-of-result: "this paper is the *correct primary source* for
  this specific equation / formula / bound" — *not* caught by current
  pipeline; requires a domain-knowledge check that "is this paper the
  one that first derived this result, or merely reviews/uses it?"

**QI proposal:** Add `validate.py --check citation_result_provenance`
that flags every result-attribution citation in a paper (heuristic:
"\cite{...} \verb|<formula>|" patterns) and asks the author to confirm
the cited paper is the *primary derivation* source, not a *review* or
*application* paper. The check should also offer a bibtex-time field
`primary_source_for: [list of formulas]` distinct from `provides:` so
that registry-side metadata can be queried during paper review.

## Summary of finding counts

- **BLOCKER (1):** 1.1 (CH-attribution misuse)
- **REQUIRED (3):** 3.3 (knife-edge prose tightening), 4.2 (Lean
  docstring phantom-name drift), 5.1 (preventive first-claim guidance)
- **RECOMMENDED (3):** 1.2 (RT title form), 7.2 (stakeholder
  RT-vs-BH precision), 2.1 (Sen 212/45 primary-source equation pin)
- **match (5):** 1.3, 1.4, 1.5, 1.6 (citation targets), 3.1, 3.2,
  4.1, 6.1, 7.1 (substance / disclosure / inventory checks)

**Notebooks are not submission-ready** until finding 1.1 is resolved.
The Lean module is sound — finding 4.2 is a docstring-only issue
that does not invalidate any theorem. The 7-theorem inventory and
all Lean proofs check out clean on substance review.
