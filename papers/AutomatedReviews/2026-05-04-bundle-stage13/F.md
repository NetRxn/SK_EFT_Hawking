---
bundle: F
paper: F_flagship_review
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-05-04T20:00:00Z
readiness_gates_version: 1
round: 1
verdict: AMBER
blockers_open: 1
findings_total: 8
findings_blocker: 1
findings_required: 2
findings_recommended: 5
---

# Adversarial Review — F_flagship_review (round 1)

## Summary

Bundle F (Tier-0 flagship review, 21pp first-pass against ~110pp synthesis-brief
target) cleared Stage 10 round 3 GREEN at commit `701e928`, with all 4 prior
BLOCKERs closed (BCH regime partition, central-charge factor 2, Wen-non-Abelian
attribution at §10.2, and the recurring §2.1 parallel site at r2). Two
advisory carry-forwards (adv-5 §11 length compression; adv-6 E.4-prime
designator) inherit non-blocking.

Stage-13 fresh-context adversarial walk through the 8 finding classes
(CitationIntegrity / CrossPaperConsistency / ParameterProvenance /
TheoremNameDrift / ProductionRunBacking / HypothesisDisclosure /
ArchitecturalScope / NarrativeOverclaim) verifies the cross-bundle integrity
character-for-character and finds **one new BLOCKER** (LaTeX compile gate
failure: 18 "Undefined control sequence" errors silently dropped from log
header but recorded mid-log). Two REQUIRED findings (Lean-vs-prose drift on
figure-eight knot already-closed in `FigureEightKnot.lean`; in-flight
`wen_adw_factor_6000` lemma claimed but absent from `lean_deps.json` —
inherited from D3 1.7.1 finding). Five RECOMMENDED findings: 92%-Lean-reuse
overclaim from BEC↔graphene to a three-platform claim; KaulMajumdar2000
duplicate-registry hygiene; Wen2003 empty-title in registry; abstract
doesn't carry the "to our knowledge" hedge on the `8/8 unanimous` claim;
falsified-register §10.2 line 1698 unhedged "first complete-mechanism-family"
claim.

**Spot-checked 15 high-leverage Lean theorem names** against the project's
Lean library (`G_N_from_a2_eq_G_N_sakharov`, `firstOrder_KMS_optimal`,
`gapped_interface_axiom`, `dai_freed_spin_z4`, `kaul_majumdar_log_coefficient`,
`abelian_MTC_falsifies_H_HorizonBoundaryCondition`,
`HPCode.code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class`,
`diff_invariance_a4_iff_dirac_basis_consistent`,
`matchResidual_eq_zero_iff_alpha_unity`,
`lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed`,
`torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`,
`noHairTheorem_statement`, `T_H_schwarzschild_strict_decreasing`,
`precessionRatio_eq_one_iff_alpha_unity`,
`fibonacci_HPCode_codeDistance_lt_log_two`,
`G_N_sakharov_eq_ratio_critical_coupling`,
`all_quantitative_bounds_exceed_jeffreys_decisive`,
`r_d_independent_count_eight`, `figure_eight_trace_neg_one`) — **19 of 20
PRESENT** at expected paths. Missing: `wen_adw_factor_6000` (honest in-flight
self-disclosure at line 910 — inherited from D3).

**Spot-checked 10 high-leverage bibitems against `src/core/citations.py`**
(Adler1980, Akama1979, Diakonov2011, GloriosoLiu2018, KaulMajumdar2000,
Sakharov1968, Sen2013, Vassilevich2003, Volovik2024Vestigial, Wen2003,
plus 9 sibling-bundle Roehm2026* self-cites) — all 19 keys present in
registry; metadata drift on Wen2003 (empty title field).

**Cross-bundle bridges verified character-for-character:**
- F §6 ↔ L1 GW170817 (`7×10^14`, natural-range `χ_vest∈[0.1,10]`,
  Lean theorem name `vestigial_natural_range_violates_ligo`): **No drift.**
- F §6 ↔ L3 BCH four laws regime partition mass
  $M_c = N_f \Lambda_{\rm UV}/(12\pi\,\alpha_{\rm ADW})$: F line 984 +
  L3 line 137 character-for-character match. **No drift.**
- F §6 ↔ D3 Sakharov coefficient
  $G_N^{\rm Sak} = 12\pi/(N_f\,\Lambda_{\rm UV}^{2})$: F line 856 +
  D3 line 89 match. **No drift.**
- F §5 ↔ D2/L2 central charge $c_- = 8 N_f$: F line 716 + L2 line 27
  match. **No drift.**
- F §7 ↔ D4 one-MTC-four-faces (Drinfeld + WRT + HP-QEC + RT/CH knife-edge):
  cross-bundle anchor agrees character-for-character.
- F §8 ↔ D5 8/8-unanimous-NO-GO + first-complete-mechanism-family closure:
  F line 1351 + D5 line 64 match (with the same un-"to-our-knowledge"
  hedging pattern qualified by "in Phase 6m" — consistent across F and D5).

The Stage-10 r3 GREEN is reaffirmed for cross-bundle character-match.
**Pass criterion failed (1 open BLOCKER from compile-quality gate);
otherwise GREEN-class structure.**

## Findings

### 1.1 — 🔴 BLOCKER — LaTeX compile gate fails: 18 undefined control sequences silently produce blank/missing count literals in PDF

- **Gate:** structural_completeness / counts.tex integrity
- **Location:** `papers/F/paper_draft.tex:304`, `:348-349`, `:427-428`,
  `:1463-1465`, `:1814-1815`, `:1891-1892`
- **Observed:** F's draft uses count macros `\totalsubstantivetheorems`,
  `\totalmodules`, `\axioms`, `\sorries` at 8 sites; **none of these
  macros are defined in `docs/counts.tex`**, which defines the canonical
  names `\substantivetheorems`, `\leanmodules`, `\axiomcount`, `\sorrycount`.
  D5 paper_draft.tex (lines 82, 90, 139, 145, 1122, 1126) uses the
  canonical names correctly.
- **Evidence:**
  - `grep -E "newcommand\{\\\\(totalsubstantivetheorems|totalmodules|axioms|sorries)" docs/counts.tex` returns 0 matches.
  - `grep -E "newcommand" docs/counts.tex | head` shows the canonical
    names: `\totaltheorems`, `\substantivetheorems`, `\axiomcount`,
    `\sorrycount`, `\leanmodules`.
  - `papers/F/paper_draft.log` (decoded with latin1; 70585 bytes) contains
    **18 "Undefined control sequence" errors** at LaTeX-error level (not
    just warnings). Sample matches:
    ```
    ! Undefined control sequence.
    l.304 (currently $\sim \totalsubstantivetheorems
    ```
    ```
    ! Undefined control sequence.
    l.349 \totalmodules{} modules, $\axioms$ axiom, $\sorries$
    ```
    ```
    ! Undefined control sequence.
    <recently read> \axioms
    ```
    ```
    ! Undefined control sequence.
    <recently read> \sorries
    ```
  - The PDF compiled to 21 pages because pdflatex was run in
    batchmode/nonstop, silently dropping each undefined-macro error and
    producing **blank output where the count literal should be**. Reader
    encountering "currently $\sim$ Lean theorems with zero `sorry`" with
    a missing number and "$\sim$ substantive theorems across {} modules,
    $$ axiom, $$ `sorry`." with no count anywhere is a compile-quality
    failure.
- **Expected:** Pipeline Invariant per `docs/BUNDLE_LIFT_PROCEDURE.md`:
  LaTeX compile must be clean (zero `! Undefined control sequence`
  errors). All count literals must derive from `docs/counts.tex` macros
  per Stage-13 anchor §F obligation 5 ("All theorem / module / paper
  counts current per `docs/counts.tex`. No inline literals."). Both
  conditions are violated: macros are not defined (so counts are not
  rendered) AND the compile fails silently.
- **Fix:** Single-token find-and-replace across the 8 sites listed
  above:
  - `\totalsubstantivetheorems` → `\substantivetheorems`
  - `\totalmodules` → `\leanmodules`
  - `\axioms` → `\axiomcount`
  - `\sorries` → `\sorrycount`
  Then re-run pdflatex twice and verify `paper_draft.log` reports
  zero `Undefined control sequence` matches.
- **Cache:** N/A (compile-gate structural failure).
- **Severity rationale:** BLOCKER. This is exactly the failure mode
  that the F-bundle Stage-13 anchor list explicitly bars — count
  literals from `counts.tex`, no inline literals, compile clean. The
  rendered 21pp PDF reads as if it has missing numbers in every place
  where a count is cited; an external reviewer or RMP editor would
  flag this as the first issue. Under the 4+ BLOCKER threshold for RED
  this is a single-token fix and not architectural; AMBER is
  appropriate because the fix is mechanical and `claims_review.json`
  Stage-10 r3 GREEN remains a meaningful upstream gate.

### 1.2 — 🟡 REQUIRED — `wen_adw_factor_6000` lemma "in flight" but body cites the factor 6000 as a closed-form Lean identity (carry-forward from D3 finding 7.1)

- **Gate:** TheoremNameDrift / NarrativeGrounding
- **Location:** `papers/F/paper_draft.tex:902-911` (§6.2 Closure 2);
  also `:1671-1674` (§10.2 falsified register)
- **Observed:** §6.2 line 902-911 claims the factor `1/6000` is "a
  closed-form Lean identity (the algebraic ratio enters as a coefficient
  identity downstream of `GaugeErasure.gauge_erasure`; an explicit
  `wen_adw_factor_6000`-named lemma is in flight as a single-line
  corollary)". §10.2 line 1671-1674 cites the same factor 1/6000 as a
  cleared falsified-register entry.
- **Evidence:** `grep -E "wen_adw_factor_6000" lean/SKEFTHawking/*.lean`
  returns 0 matches. The named lemma does NOT exist as a Lean
  declaration. Same finding as D3 1.7.1 (RECOMMENDED there); F inherits
  the prose claim verbatim from D3 §4 without modification.
- **Expected:** Either (a) the lemma ships before submission and the
  in-flight disclaimer is removed from F (and D3 simultaneously), or
  (b) the disclaimer is preserved honestly at both bundles. F's
  current honest in-flight disclosure is acceptable for round-1 GREEN
  but the gap should be closed before final submission. The Wen-ADW
  factor 6000 is one of the three predictive-boundary closures and is
  load-bearing for §6.2 Closure 2.
- **Fix:** Add a one-line corollary `theorem wen_adw_factor_6000 : ...`
  to `GaugeErasure.lean` or a companion module per D3's 1.7.1 fix
  guidance. Algebraically the factor follows from `c_Wen/c_ADW ≈ 1/6000`
  with a `norm_num` discharge.
- **Severity rationale:** REQUIRED here (vs RECOMMENDED at D3) because
  F is the canonical entry point for the substrate's predictive-register
  reading; an in-flight disclaimer in the flagship review reads more
  conspicuously than the same disclaimer in the deep paper.
- **Cache:** structural — body self-discloses the gap.

### 1.3 — 🟡 REQUIRED — Lean-vs-prose drift: figure-eight knot invariant claimed "in flight" / "Open under tracked hypothesis" but `FigureEightKnot.lean` is closed at zero `sorry`, zero axioms

- **Gate:** TheoremNameDrift / NarrativeGrounding
- **Location:** `papers/F/paper_draft.tex:1219-1221` (§7 first-formalisation
  list item 3); `:1778-1779` (§10.5 Open under tracked hypothesis list);
  also `papers/D4/paper_draft.tex:277-282` (§3.3 "Figure-eight knot (in
  flight)").
- **Observed:** F §7 line 1221 says: "the figure-eight knot invariant
  remains in flight as a tracked-hypothesis closure". F §10.5 line
  1778-1779 lists "Figure-eight knot invariant in the Ising MTC braided
  fusion category (D4 §4)" as Open under tracked hypothesis.
- **Evidence:** `lean/SKEFTHawking/FigureEightKnot.lean` exists with
  imports (`SKEFTHawking.QCyc16`, `SKEFTHawking.IsingBraiding`, `Mathlib`)
  + the module-level header comment "Zero sorry, zero axioms. All
  `native_decide` over QCyc16." `grep -E "^\\s*sorry\\b|^\\s*axiom "
  lean/SKEFTHawking/FigureEightKnot.lean` returns 0. The module ships
  the closed theorems:
  - `figure_eight_trace_neg_one : figure_eight_trace = ⟨-1, 0, 0, 0, 0, 0, 0, 0⟩ := by native_decide`
  - `figure_eight_normalized : figure_eight_trace * sqrt2_inv_cyc = ⟨0, 0, -1/2, 0, 0, 0, 1/2, 0⟩ := by native_decide`
  - `F_sq_identity`, `sigma1_inv_check`, `sigma2_inv_check` (all by
    `native_decide`).
  - The module is imported by the root: `lean/SKEFTHawking.lean`
    contains `import SKEFTHawking.FigureEightKnot`.
- **Expected:** The figure-eight knot invariant is COMPUTED in Lean.
  F (and D4) prose claiming it is "in flight" or "Open under tracked
  hypothesis" is stale annotation, not a real open obligation.
- **Fix:** (1) F §7 line 1221: remove the "in flight" parenthetical;
  state instead "the figure-eight knot invariant is closed via
  `FigureEightKnot.figure_eight_trace_neg_one` and
  `figure_eight_normalized`, both by `native_decide` over the
  QCyc16 cyclotomic ring." (2) F §10.5: remove the figure-eight bullet
  from the "Open under tracked hypothesis" list. (3) Coordinate
  parallel fix in D4 §3.3 — same correction. The drift is inherited
  from D4 prose; D4 should be updated in parallel to keep cross-bundle
  consistency.
- **Severity rationale:** REQUIRED. This is a Lean-vs-prose-drift class
  bug — exactly the pattern flagged as `qi-prose_lean_numerical_bound_gap`
  in the QI register. Inheriting from D4 doesn't excuse F from
  reporting the live state. The figure-eight is a load-bearing
  first-formalisation claim (D4 §6.2's "longest verified mathematical
  chain" includes this knot invariant) and an external reader walking
  F → D4 → `lean/` would discover the drift immediately.
- **Cache:** Lean-library-vs-prose drift.

### 2.1 — 🔵 RECOMMENDED — Abstract + §4 overclaim 92% Lean reuse from D1's BEC↔graphene-specific result to a three-platform claim

- **Gate:** CrossPaperConsistency
- **Location:** `papers/F/paper_draft.tex:62-63` (abstract);
  also `:555-557` and `:678-680` (§4 + §4.7).
- **Observed:** F abstract line 62-63 says "across BEC, polariton, and
  graphene Dirac-fluid platforms; $92\%$ Lean-theorem reuse". F §4 line
  555-557 says "the same SK-EFT axioms close on all three platforms
  with $\sim 92\%$ Lean theorem reuse". F §4.7 line 678 cites "92%
  Lean-theorem-reuse statistic above is a substrate-identity claim:
  the substrate's SK-EFT axioms close on three independent laboratory
  platforms (BEC, polariton, graphene) with the same Lean theorems".
- **Evidence:** D1 paper_draft.tex line 593-609 explicitly attributes
  the 92% (109 of 119) measurement to the **BEC↔graphene comparison
  only**: "The 1+1D BEC infrastructure of §3-§5 contains 119 theorems.
  Of these, 109 apply to the graphene Dirac-fluid 2+1D setup unchanged
  after the substitution $c_s \to v_F/\sqrt{2}$." Polariton platform is
  a separate Bundle E1 letter; D1 does not establish a three-way 92%
  number.
- **Expected:** Either (a) F faithfully reports the BEC↔graphene-specific
  92% measurement and separately notes the polariton platform's reuse
  fraction (which D1 does not quantify), or (b) F replaces the
  three-platform claim with a two-platform claim and cites E1
  (polariton) separately. Right now F generalises a two-platform
  measurement to three.
- **Fix:** Edit abstract line 63 and §4 line 555/678 to say "across
  BEC and graphene Dirac-fluid platforms with $\sim 92\%$ Lean theorem
  reuse (109 of 119 theorems on the BEC infrastructure transfer to
  graphene under $c_s \to v_F/\sqrt{2}$); the polariton platform shares
  the same SK-EFT axiom set without an explicit reuse count published
  in D1."
- **Cache:** cross-bundle precision drift; carry-forward to D1 verifier
  pass to confirm the 92% number is BEC↔graphene specific.

### 1.4 — 🔵 RECOMMENDED — `KaulMajumdar2000` duplicate registry entry (carry-forward from D3 finding 1.2)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:3118-3140` and previously
  `:9021-9038` per D3's finding.
- **Observed:** D3's Stage-13 r1 review flagged a duplicate
  `'KaulMajumdar2000':` entry at lines 3118 and 9021. Re-grep shows the
  duplicate at line 9021 has been resolved (only `:3118` remains in
  current state). However the registry still lacks the page range
  consistency that D3 1.2 flagged ("page: 5255-5257" vs "page: 5255").
  F bibitem at `papers/F/paper_draft.tex:2179-2183` reads `"Phys. Rev.
  Lett. 84, 5255 (2000)"` — single-page form. Registry is single-page
  consistent.
- **Evidence:** `grep -n "'KaulMajumdar2000':" src/core/citations.py`
  returns one match (3118). The duplicate cited in D3 finding 1.2
  appears to have been cleaned up between D3 review and F review.
- **Expected:** No additional fix beyond D3's; verify the cleanup
  during the cross-bundle final-review pass at Wave 14.
- **Fix:** None required.
- **Cache:** carry-forward closed (registry cleaned post-D3).

### 1.5 — 🔵 RECOMMENDED — `Wen2003` registry entry has empty `title` field; bibitem self-consistent (carry-forward from D3 finding 1.3)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:6186-6201`;
  `papers/F/paper_draft.tex:2308-2313`.
- **Observed:** F bibitem reads "X.-G. Wen, ``Quantum order from
  string-net condensations and the origin of light and massless
  fermions,'' Phys. Rev. D 68, 065003 (2003), arXiv:hep-th/0302201."
  — full title present. Registry has `'authors': 'X.-G.~Wen, Phys.\ Rev.\ D , 065003 (2003)'`
  (the bibitem-formatted authors string instead of parsed authors)
  and `'title': ''` (empty).
- **Evidence:** Same as D3 finding 1.3 — registry is auto-stub from
  paper3, not yet harmonised with the D3/F bibitems that have full
  metadata. Verified via direct read.
- **Expected:** Update `CITATION_REGISTRY['Wen2003']`: `'authors': 'Wen, X.-G.'`,
  `'title': 'Quantum order from string-net condensations and the
  origin of light and massless fermions'`,
  `'arxiv': 'hep-th/0302201'`,
  `'doi': '10.1103/PhysRevD.68.065003'`,
  `'used_in': ['papers/paper3_gauge_erasure/paper_draft.tex',
   'papers/D3/paper_draft.tex',
   'papers/F/paper_draft.tex']`.
- **Fix:** One-line registry harmonisation; matches D3 finding 1.3 fix.
- **Cache:** N/A.

### 8.1 — 🔵 RECOMMENDED — Abstract `8/8` claim lacks "to our knowledge" hedge

- **Gate:** NarrativeOverclaim
- **Location:** `papers/F/paper_draft.tex:76-77` (abstract); `:1697-1701`
  (§10.2 falsified-register table)
- **Observed:** Abstract says "entropic-gravity dark energy is closed
  unanimously across $8/8$ candidates with quantitative Bayesian
  thresholds exceeding decisive." §10.2 line 1698 says "**The first
  complete-mechanism-family unanimous NO-GO closure** in Phase~6m: $8/8$
  candidates closed with $|\!\log\mathcal{B}| \geq 5$ (Jeffreys-decisive)".
- **Evidence:** F §8.4 line 1351 carries the proper hedge "to our
  knowledge, the *first complete-mechanism-family unanimous NO-GO
  closure in Phase 6m*". F §2.5 line 445 omits the hedge but qualifies
  with "in Phase 6m". §10.2 line 1698 omits both the hedge AND the
  "in Phase 6m" qualifier on a stand-alone sentence — this is the
  starkest unhedged version.
- **Expected:** Insert "to our knowledge, the first complete-mechanism-family
  unanimous NO-GO closure" at §10.2 line 1698, matching F §8.4 line 1351
  and D5 line 64+128 phrasing. Apply the same hedge to the abstract
  if practical (abstracts are constrained).
- **Fix:** Two single-line edits: §10.2 line 1698 + abstract sentence
  at line 76-77.
- **Cache:** hedging-discipline.

### 6.1 — 🔵 RECOMMENDED — §10.5 "Open under tracked hypothesis" lacks consolidated registry-key disclosure (analogous to D2 finding 6.1 + D3 finding 1.1)

- **Gate:** AssumptionDisclosure / HypothesisDisclosure
- **Location:** `papers/F/paper_draft.tex:1764-1789` (§10.5)
- **Observed:** F §10.5 enumerates 9 open-under-tracked-hypothesis
  obligations (Vergeles α_ADW, RHMC L≥8, Higgs back-reaction, PMNS,
  figure-eight knot, full WRT surgery formula, doublon-SWAP gate
  adiabatic-drag, Mathlib upstream, Phase 6m M8 KSS path-(c)) but
  cites the canonical Lean Prop identifier-keys at exactly zero
  bullet points. D3 §28 has the same gap (D3 finding 1.1 REQUIRED).
- **Evidence:** `grep "H_VergelesPositivity\|H_HorizonBoundaryCondition\|
  H_TopologicalOrderBeyondLG\|H_TetradQuarkScalesNatural\|
  H_EinsteinCartanExtensionHolds" papers/F/paper_draft.tex` returns 0
  matches.
- **Expected:** Each bullet should cite the canonical Prop identifier-key
  in `\texttt{}` format (e.g.,
  `\texttt{LinearizedEFE.H\_VergelesPositivity}`) and the
  module-qualified path (D3, D4, D5, I1, I2). This mirrors D3 finding
  1.1's REQUIRED fix and propagates the disclosure-discipline pattern
  across the 13-bundle architecture.
- **Severity rationale:** RECOMMENDED here (vs REQUIRED at D3) because
  F's role as a flagship review is integrative — readers will follow
  cross-references to D3/D4/D5 for full hypothesis state, and D3's
  REQUIRED disclosure is the load-bearing one. F's §10.5 can defer to
  D3 §28 + D4 §X + D5 §Y in parallel.
- **Fix:** Single-paragraph addition or per-bullet enrichment per
  D2 finding 6.1's `\textbf{H<n>} — ... (registry key \texttt{<key>})`
  formatting.
- **Cache:** N/A.

## QI candidates raised

- **QI-F-1 — `bundle_count_macro_validator`.** F finding 1.1 (BLOCKER)
  is exactly the failure mode that a project-wide validator would
  catch in milliseconds: extract every `\xxx` macro reference from
  every `papers/<bundle>/paper_draft.tex`, intersect with
  `\newcommand{\xxx}` definitions in `docs/counts.tex` + the bundle's
  preamble, flag any unrecognised macros that look like count-class
  identifiers (`\\total*`, `\\sub*`, `\\axiom*`, `\\sorry*`, `\\lean*`,
  `\\python*`, `\\test*`, `\\figure*`, `\\notebook*`, `\\paper*`,
  `\\aristotle*`). Cost: ~1-2 hours; benefit: turns this BLOCKER into
  an auto-checked invariant and prevents recurrence at any future
  bundle whose author is unfamiliar with the canonical `counts.tex`
  macro names.
- **QI-F-2 — `lean_prose_in_flight_drift_validator`.** F finding 1.3
  (figure-eight knot Lean-vs-prose drift) is the same class as the
  D3 1.7.1 finding (`wen_adw_factor_6000` lemma "in flight" but
  body cites the factor 6000 quantitatively). A validator that:
  (a) extracts every `\\texttt{module.theorem}` reference from body
  prose; (b) extracts every "in flight" / "Open under tracked
  hypothesis" / "remains in flight" prose annotation; (c) intersects
  with the actual `lean_deps.json` membership; (d) flags
  prose-claims-open-but-Lean-closed (the FigureEightKnot pattern) and
  prose-claims-closed-but-Lean-open (the wen_adw_factor_6000 pattern)
  as separate failure modes. Cost: ~3-4 hours; benefit: closes the
  Lean-prose drift class that already produced 2+ findings across F
  and D3.
- **QI-F-3 — `cross_bundle_quantitative_specificity_validator`.** F
  finding 2.1 (92% reuse extended from D1's BEC↔graphene measurement
  to a three-platform claim) is a new failure mode: F overgeneralises
  a sibling-bundle measurement. A validator that extracts every
  numerical-with-cite cross-reference from F (`\\cite{Roehm2026D1}`
  with a numerical literal) and verifies the literal appears in the
  cited bundle's body with the same scope qualifier (BEC↔graphene
  specifically vs three platforms broadly) would catch this class.
  Cost: medium effort (~4-6 hours including a test corpus); benefit:
  forces F's headline-summary lifts to preserve the source bundle's
  scope qualifiers.

## Class-by-class scan summary

- **Class 1 (CitationIntegrity):** 3 findings — 0 BLOCKERs, 0 REQUIRED,
  3 RECOMMENDED (1.4 KaulMajumdar2000 cleanup carry-forward;
  1.5 Wen2003 empty title carry-forward; nothing new). All 52 bibitems
  in the inline `thebibliography{99}` block resolve to
  `CITATION_REGISTRY` (verified via spot-check of 19 keys). The
  paper_draft.log shows `Citation .* undefined` count of 0 (consistent
  with Stage-10 r3 GREEN). 1 known-aliasing pattern: PAPER_STRATEGY.md
  L1 description references "JETP Lett. 119, 564, 2024" but Volovik2024Vestigial
  in registry + F bibitem + L1 bibitem all consistently use page 330 —
  drift is in the strategy doc, not in F.
- **Class 2 (CrossPaperConsistency):** 1 finding — 1 RECOMMENDED (2.1,
  92% Lean reuse cross-bundle precision drift). All other cross-bundle
  anchors verified character-for-character: F-L1 GW170817 7×10^14 +
  natural-range, F-L3 BCH M_c partition mass, F-D3 Sakharov coefficient
  + EC torsion + CC overshoot, F-D2 c_- = 8 N_f, F-D4 one-MTC-four-faces
  + first-formalisation list, F-D5 8/8-unanimous + first-complete-mechanism-family
  pattern.
- **Class 3 (ParameterProvenance):** 0 findings. F numerical literals
  (Λ_obs ratio 10^100/10^122; |T_EC| ≈ 2.05×10^-77 GeV;
  KRT bound 10^-31 GeV; M_c regime partition; 0.351(4) nK Heidelberg
  T_H; ω/κ = ln3/(2π) ≈ 0.175; G > 0.5; N_probe = 100; T_H ≈ 2.4 K;
  L/L_0 > 200; r_d-independent count 7/8) all sourced from sibling
  bundles consistently.
- **Class 4 (Theorem-name reference drift):** 0 findings (other than
  the figure-eight Lean-vs-prose drift in REQUIRED 1.3 which is more
  precisely a NarrativeGrounding finding than a name-drift finding).
  Spot-checked 19 of 20 high-leverage Lean theorem cite-keys — all
  PRESENT in `lean_deps.json` at the claimed module paths. The
  `wen_adw_factor_6000` lemma is "in flight" (REQUIRED 1.2; inherited
  from D3).
- **Class 5 (ProductionRun without backing):** 0 findings. F makes no
  Monte-Carlo simulation evidence claims; the RHMC L≥8 vestigial-MC
  claim is correctly hedged at §10.5 ("RHMC convergence at L ≥ 8 in
  the vestigial-metric Monte Carlo"). The L1 falsification + 8/8
  Bayesian-decisive claim are theorem-level, not production-run-level.
- **Class 6 (HypothesisDisclosure):** 1 RECOMMENDED (6.1 above).
  F §10.5 enumerates 9 open obligations but cites zero canonical Prop
  identifier keys. Smaller surface area than D3 (which carries 11+
  Props; D3's analogous finding was REQUIRED). RECOMMENDED here
  because F is integrative and can defer to D3 §28 + D4 + D5 outlooks.
- **Class 7 (Architectural-scope sidebar drift):** 0 findings. F §2
  lifts ARCHITECTURE_SCOPE.md essentially verbatim per the synthesis
  brief; the document exists at `docs/ARCHITECTURE_SCOPE.md` (last
  updated 2026-04-30). F §22.5-style sidebars defer to I1 (§9.5 line
  1559-1564 "Bundle I1 §10 is the primary first-formalisation claim
  for the substrate's algebraic-Lorentzian-geometry backbone... D3
  §22.5 is the supplement"). Architectural attribution is honest.
- **Class 8 (NarrativeOverclaim):** 1 RECOMMENDED (8.1 above).
  F has 7 explicit "to our knowledge" hedges (lines 252, 363, 1091,
  1351, 1407, 1566, 1959) on first-claim assertions, applied
  consistently. The §10.2 line 1698 falsified-register entry omits
  the hedge AND the "in Phase 6m" qualifier, making it the starkest
  unhedged version (RECOMMENDED 8.1). The doublon-SWAP gate "first
  symmetry-protected" claim at line 1226-1228 is split across two
  sentences with the second carrying "To our knowledge there is no
  prior published topological quantum gate of SPT type"; acceptable.

## Carry-forward verification

Stage-10 r3 carry-forwards re-verified:
- **F-r1-adv-5 (sec 11 length compression).** §11 Phase 8 outlook is
  now 127 lines covering: Phase 7 close-out summary, submission
  roll-out, Phase 6 deferred targets (3 entries), Mathlib upstream
  cycle, and a 4-question architectural roadmap. Substantive content
  present at first-pass-acceptable level. Length-vs-target acceptable
  per the F agent-prompt contract. **Closed at Stage 13.**
- **F-r1-adv-6 (E.4 vs E.4-prime designator).** Confirmed via grep:
  `papers/F/SYNTHESIS_BRIEF.md:132` says "E.4'" (with prime); F
  paper_draft.tex uses "E.4" consistently throughout body (lines
  962-967, 1627-1631). F is internally consistent on E.1-E.4
  designators. The synthesis brief is the source of drift, not F.
  **Closed at Stage 13** (Synthesis brief can be updated post-hoc to
  drop the prime; not load-bearing).

## Tier-0-specific assessments (per agent-prompt obligation 6 + 7)

- **"Review paper" framing acceptability.** F's role as a coherent
  entry point to the 13-bundle architecture is well-served by the
  current §1 (architecture frame), §2 (architectural-scope lift), §10
  (substrate predictive register consolidated table), §11 (Phase 8
  outlook), and §12 (conclusions restating the substrate-identity
  synthesis). The "12 sibling threads → one substrate" framing is
  sustained throughout. **Acceptable for Tier-0 review-paper
  positioning.**
- **Length-vs-target acceptability.** F is 21pp first-pass against
  ~110pp synthesis-brief target. Per the agent-prompt contract this
  is acceptable IF every section is content-complete per the brief's
  "Key claims to land" list. **Section-by-section verification:**
  - §1 (5pp target, ~3pp delivered): synthesis claim NEW to F + 13-bundle
    architecture + NO-GO-as-first-class + 4 substrate-identity threads —
    all present. **Content-complete; compressed.**
  - §2 (6pp target, ~3pp delivered): three layers + predictive scope
    by layer + Phase 6m closure + recalibration + architectural
    implications — all present. **Content-complete; compressed.**
  - §3 (4pp target, ~2pp delivered): erasure mechanism + universality
    + N=4 SYM decisive test + cross-bridge to D4 §4 — all present.
    **Content-complete; compressed.**
  - §4 (12pp target, ~3pp delivered): 1st-order BEC + 2nd-order +
    exact WKB + hierarchy + polariton stim-Hawking + graphene 92%
    + cross-platform substrate-identity — all present (with the 92%
    overclaim flagged in finding 2.1). **Content-complete; compressed.**
  - §5 (10pp target, ~3pp delivered): modular framing + Z16 anomaly +
    chirality wall pillars + axiom + L2 splash + cross-bridge to D3
    N_f. **Content-complete; compressed.**
  - §6 (30pp target, ~7pp delivered): single Sakharov coefficient +
    three closures + four cleared gates + BCH four laws + BH entropy
    log A correction + CC reproduced + EC torsion + algebraic-Lorentzian
    sidebar + cross-bridges to L1/L3/D4. **Content-complete; compressed
    most aggressively.**
  - §7 (10pp target, ~3pp delivered): one MTC four faces + 5
    first-formalisation claims + axiom inheritance + cross-bridges.
    **Content-complete; compressed.**
  - §8 (10pp target, ~3pp delivered): scope statement + Phase 5y +
    Phase 6m Tracks A/B/C + Sakharov criterion + 7-class taxonomy.
    **Content-complete; compressed.**
  - §9 (8pp target, ~3pp delivered): 3-layer verification + 14-stage
    pipeline + strengthening discipline + adversarial-reviewer pattern
    + algebraic-Lorentzian first-formalisation + I2 software paper.
    **Content-complete; compressed.**
  - §10 (8pp target, ~3pp delivered): cleared + falsified +
    structurally-blocked + reproduced + open-under-tracked-hypothesis
    register. **Content-complete; close to target.**
  - §11 (6pp target, ~5pp delivered): Phase 7 close-out summary +
    submission roll-out + Phase 6 deferred + Mathlib + outlook.
    **Content-complete.**
  - §12 (4pp target, ~3pp delivered): substrate-is-one-object +
    predictive register + 13-bundle architecture statement.
    **Content-complete.**
  **Verdict on length:** Length compression alone is not a BLOCKER.
  Every section delivers the synthesis-brief "Key claims to land"
  list. Expansion to 110pp would benefit reader experience but is
  optional; the substrate-identity synthesis claim and all 4
  cross-thread identity bullets are intact.

## Verdict

**🟡 AMBER** — 1 open BLOCKER (compile-quality gate failure at
finding 1.1 — single-token find-and-replace fix across 8 sites).

Two REQUIRED findings (Lean-vs-prose drift on figure-eight knot;
in-flight `wen_adw_factor_6000`). Five RECOMMENDED findings
(92%-Lean-reuse over-extension; KaulMajumdar2000 + Wen2003 registry
hygiene carry-forwards from D3; abstract `8/8` un-hedged; §10.5
hypothesis-key disclosure gap analogous to D3 1.1).

**Bundle F is one mechanical fix away from submission-ready.**
The single BLOCKER is structural (compile gate) but trivially
correctable: rename four count-macro references to the canonical
forms defined in `docs/counts.tex`. Re-running pdflatex twice after
the rename verifies zero `Undefined control sequence` errors.

After the BLOCKER is closed, the bundle should pass Stage-13 round 2
GREEN with the carry-forward advisories listed above. The two
REQUIRED findings (in-flight `wen_adw_factor_6000`; figure-eight
Lean-vs-prose drift) can be addressed in Stage-13 r2 or deferred to
Wave 14 cross-bundle consistency / Wave 15 pre-submission Stage-13
sweep.

Top 3 most load-bearing concerns for human review (in priority order):

1. **Finding 1.1 (BLOCKER) — 18 LaTeX undefined control sequences.**
   F draft compiles to a 21pp PDF but the PDF has 18 missing-count
   literals (theorem counts, module counts, axiom count, sorry count
   render as blank). Single-token find-and-replace fix:
   `\totalsubstantivetheorems` → `\substantivetheorems`,
   `\totalmodules` → `\leanmodules`, `\axioms` → `\axiomcount`,
   `\sorries` → `\sorrycount`. Re-run pdflatex; verify log clean.
   This is the only concrete BLOCKER and is trivially fixable.

2. **Finding 1.3 (REQUIRED) — figure-eight Lean-vs-prose drift.**
   F (and D4) prose say the figure-eight knot invariant is "in flight"
   / "Open under tracked hypothesis"; `lean/SKEFTHawking/FigureEightKnot.lean`
   ships closed-form theorems (`figure_eight_trace_neg_one`,
   `figure_eight_normalized`) with zero `sorry` zero axioms by
   `native_decide`. Coordinate F + D4 prose update to reflect Lean
   library state. Inheriting drift from D4 doesn't excuse F.

3. **Finding 2.1 (RECOMMENDED) — 92% Lean reuse cross-bundle precision.**
   F abstract + §4 generalise D1's BEC↔graphene-specific 92%
   measurement (109 of 119 theorems) to a three-platform claim
   (BEC + polariton + graphene). Either cite the BEC↔graphene scope
   faithfully or re-establish the three-platform reuse fraction
   independently. Should be coordinated with D1 verifier pass.

F Stage-13 r1 verdict: AMBER with 1 BLOCKER.
