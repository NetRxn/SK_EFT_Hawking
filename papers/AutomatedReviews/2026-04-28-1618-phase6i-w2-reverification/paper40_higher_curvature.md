---
paper: paper40_higher_curvature
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T16:18:00Z
readiness_gates_version: 1
prior_review: papers/AutomatedReviews/2026-04-28-2048-phase6i-w1-reverification/paper40_higher_curvature.md
slug: phase6i-w2-reverification
---

# Adversarial Review (Phase 6i Wave 2 Re-verification) — paper40_higher_curvature

## Summary

Six findings: 0 BLOCKER, 3 REQUIRED, 3 RECOMMENDED. Both Wave 1
REQUIRED items are **structurally fixed**: (a) Kapner2007,
WeisbergHuang2016, BertottiIessTortora2003 now in `CITATION_REGISTRY`
with `doi_verified: True` and primary-source cache files at
`Lit-Search/Phase-6e/primary-sources/`, and (b) all four HC_BOUND
provenance entries now carry `human_verified_date: '2026-04-28'` with
substantive `human_verified_notes` and the new `cited_bibkeys` field.
Three new REQUIRED items surfaced — none citation-integrity / parameter
provenance — that the Wave 1 review didn't reach because they are
structurally adjacent to the Wave 2 changes (a Gate 4 ComputationCorrectness
test-shape gap on the new `higher_curvature_predicted_in_observational_band`
formula, a Gate 11 FixPropagation tracking gap where round-1 ReviewFinding
nodes are still `status: open` despite structural remediation, and a
Gate 1 advisory on `Abbott2017GW170817` registry's `doi_verified: None`).
**Paper40 is now CLOSEABLE for the qi-citationintegrity and
qi-parameterprovenance gates** for the issues this round flagged. The
new findings target separate gates and are independently triaged.

## Wave 2 Verification

**Wave 1 REQUIRED status: STRUCTURALLY FIXED.**

| Wave 1 REQUIRED finding | Verification | Evidence |
|---|---|---|
| W1 1.1 — HC_BOUND primary experimental sources (Kapner, WeisbergHuang, BertottiIessTortora) absent from CITATION_REGISTRY | ✅ FIXED | (a) `src/core/citations.py:2796–2864` carries three new entries: `Kapner2007` (PRL 98:021101, DOI `10.1103/PhysRevLett.98.021101`, arXiv hep-ph/0611184), `WeisbergHuang2016` (ApJ 829:55, DOI `10.3847/0004-637X/829/1/55`, arXiv 1606.02744), `BertottiIessTortora2003` (Nature 425:374, DOI `10.1038/nature01997`, arXiv None — Nature paywalled). All three have `doi_verified: True`, `inprep: False`, `primary_source_path` set, `used_in: ['papers/paper40_higher_curvature/paper_draft.tex']`. (b) Cache files present: `Lit-Search/Phase-6e/primary-sources/Kapner2007.pdf` 351 KB, `WeisbergHuang2016.pdf` 4.4 MB, `BertottiIessTortora2003.json` 12.7 KB Crossref metadata sidecar. (c) `Abbott2017GW170817` `used_in` extended (`citations.py:3078-3079`) to include paper40. (d) Fresh WebFetch verifications of all four bibitems against arXiv / Crossref returned `verdict: match` for title, authors, journal, volume, page, DOI on this round (recorded inline in this review; cache append for Kapner / WeisbergHuang / BertottiIessTortora / Abbott2017GW170817-paper40 pending). (e) Paper40 `paper_draft.tex:404-430` adds matching `\bibitem{Abbott2017GW170817}`, `\bibitem{Kapner2007}`, `\bibitem{WeisbergHuang2016}`, `\bibitem{BertottiIessTortora2003}` blocks; the per-ceiling `\cite{}` reroutes in §sec:bounds (`paper_draft.tex:200-208`) tie each ceiling to its primary source. |
| W1 3.1 — `human_verified_date: None` on four HC_BOUND provenance entries | ✅ FIXED | All four entries (`provenance.py:2756-2879`) now carry `human_verified_date: '2026-04-28'` and substantive `human_verified_notes`. New `cited_bibkeys` field present on each (e.g. `HC_BOUND_PULSAR_C_SQ.cited_bibkeys = ['WeisbergHuang2016', 'CalmetCapozzielloPryer2017']`). The LIGO entry's `doi` was changed from `10.1103/PhysRevLett.119.161101` (GW170817 detection paper) to `10.3847/2041-8213/aa920c` (multimessenger paper) per the Wave 2 close report — this is the actual paper that established the speed-of-graviton bound. |
| W1 implicit — provenance DOIs absent from registry (the `qi-provenance-citation-coverage` QI surfaced in W1) | ✅ ADDRESSED | New `validate.py --check provenance_doi_in_registry` (CHECK 20) shipped: `uv run python scripts/validate.py --check provenance_doi_in_registry` PASSES with all 8 paper40 `cited_bibkeys` resolved (0 missing). The 29 still-unresolved DOIs project-wide are pre-existing entries outside paper40 scope (graphene, Na23, Majorana, etc.) — separately tracked. |

**Recommendation:** QI items `qi-citationintegrity` and
`qi-parameterprovenance` may flip `open → closed` *for paper40*, with
`evidence_on_close` pointing to this re-review and the Wave 2 close
report. Project-wide `qi-citationintegrity` remains open per the 99
bibkeys still without primary-source cache (CHECK 19 fails project-wide
but no paper40-cited bibkey is in that 99).

## Findings

### 4.1 — 🟡 REQUIRED — `higher_curvature_predicted_in_observational_band` has bounds-only test coverage

- **Gate:** ComputationCorrectness (Gate 4)
- **Location:** `src/core/formulas.py:8415-8438`; tests `tests/test_higher_curvature.py:318-331` (`TestObservationalBandFormula`)
- **Observed:** The formula `higher_curvature_predicted_in_observational_band(N_f, bound_value)` returns a `bool` (`largest <= float(bound_value)`). All three covering tests (`test_passes_at_LIGO_bound`, `test_passes_at_pulsar_bound`, `test_fails_at_artificially_tight_bound`) are pure `assert / assert not` Boolean checks — `test_kind = 'bounds'` per the Gate 4 classifier. `scripts/readiness_gates.py:_eval_computation_correctness` flags `paper40_higher_curvature` with `1 formulas bounds-only + 0 formulas untested; bounds-only: higher_curvature_predicted_in_observational_band` and the gate state for ComputationCorrectness is `blocked` for paper40.
- **Evidence:** `uv run python -c "from scripts.readiness_gates import evaluate_all_gates; ... print([(r.gate, r.state, r.notes, r.blockers) for r in evaluate_all_gates(g) if r.paper == 'paper40_higher_curvature'])"` returns `ComputationCorrectness: blocked — 1 formulas bounds-only + 0 formulas untested; blockers=['bounds-only: higher_curvature_predicted_in_observational_band']`. `validate.py` (full run, 138.8s) also reports `paper40_higher_curvature  —  1 blocked: ComputationCorrectness`.
- **Expected:** Per Gate 4 in `READINESS_GATES.md`: "Every grounded formula has ≥1 VERIFIES edge where `test_kind ∈ {golden, identity, roundtrip}`". The fix is a single `golden`-shape test that asserts the largest predicted coefficient at a fixed `N_f` matches a hardcoded reference value — e.g. `assert math.isclose(_largest_a4_coef(27), 27/(180*(4*math.pi)**2), rel_tol=1e-9)` or an `assertAlmostEqual` on the boundary value where the predicted-vs-bound margin is non-trivial. Adding a single golden test on the underlying numeric (e.g. `assertAlmostEqual(higher_curvature_Riemann_sq_coefficient(27), 9.49e-4, delta=1e-5)`) would lift this gate; the existing test class also matches the §5 paper prose ("$|c_{\mathrm{Riem}}(N_f=27)| \approx 9.49 \times 10^{-4}$") that does not currently have a `golden` cross-check.
- **Fix:** Add one `pytest.approx` / `math.isclose` / `assertAlmostEqual` test on the load-bearing coefficient evaluation in `tests/test_higher_curvature.py::TestObservationalBandFormula` (or a new sibling class). Re-run `validate.py --check readiness_submission_gate` to confirm Gate 4 flips to `passed`. Severity REQUIRED (not BLOCKER) because the underlying Lean theorem `higher_curvature_below_pulsar_bound` is itself a substantive proof; the gap is purely the Python test-shape, not a physics bug.
- **Cache:** N/A

### 11.1 — 🟡 REQUIRED — Round-1 ReviewFinding nodes still `status: open` in graph despite structural remediation

- **Gate:** FixPropagation (Gate 11)
- **Location:** Graph nodes `review:2026-04-28-0057-internal-adversarial:paper40_*` (×8), `review:2026-04-28-0158-internal-adversarial-reinvocation:paper40_*` (×3), `review:2026-04-28-2048-phase6i-w1-reverification:paper40_*` (×2) — 13 ReviewFinding nodes total touching paper40, all with `status: open`.
- **Observed:** `scripts/readiness_gates.py:_eval_fix_propagation` reports paper40 FixPropagation as `needs-recheck` with `notes: '4 review findings still open'` and blockers including `1.1 🔴 BLOCKER — Wrong-target arXiv ID for CalmetCapoz...` and `1.2 🔴 BLOCKER — Wrong venue for Berti2015`. Both of these were structurally fixed *weeks* ago (CalmetCapozzielloPryer2017 bibkey; Berti2015 CQG 32:243001 verified) and the Wave 1 re-verification confirmed it. Yet the round-1 ReviewFinding nodes were not flipped to `status: fixed` and no `SUPERSEDES` edges were added.
- **Evidence:** Direct graph query: `findings = [n for n in g['nodes'] if n.get('type') == 'ReviewFinding' and 'paper40' in str(n.get('meta'))]` returns 13 nodes, all `status: open`. The original BLOCKER on `CalmetCapozzielloPryer2019` arXiv:1905.13728 is recorded as `severity: critical, status: open` even though `paper_draft.tex:384` now reads `\bibitem{CalmetCapozzielloPryer2017}`, registry `citations.py:2748-2771` has the correct entry, and CHECK 19 plus the cache file at `Lit-Search/Phase-6e/primary-sources/CalmetCapozzielloPryer2017.pdf` confirm the fix.
- **Expected:** Per Gate 11 in `READINESS_GATES.md`: "Every FLAGS incoming to this paper has `status != 'open'`. Every finding marked `fixed` has a SUPERSEDES edge to the finding that confirmed the fix (or a documented commit reference)." The Wave 2 close should have included a graph-update pass that walks ReviewFinding nodes for paper40, flips `status: open → fixed`, and adds SUPERSEDES edges from the W2-shipped bibkey/cache/provenance commits to the round-1 finding IDs.
- **Fix:** A scripts-level remediation: extend `scripts/extract_review_finding_nodes.py` (or whatever populates the ReviewFinding graph) to honour explicit `status: fixed` markers in the prior-review YAML/MD frontmatter, OR add a one-shot `scripts/close_review_findings.py paper40_higher_curvature --before 2026-04-28-2048` that bulk-flips finding status with a documented commit reference. Severity REQUIRED (not BLOCKER) because this is a tracking/pipeline gap, not a physics or citation problem; the underlying remediation is real.
- **Cache:** N/A

### 1.1 — 🟡 REQUIRED — `Abbott2017GW170817` registry entry has `doi_verified: None`

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `src/core/citations.py:3075` — `'doi_verified': None,` for `Abbott2017GW170817`.
- **Observed:** Paper40 cites `\cite{Abbott2017GW170817}` (`paper_draft.tex:201`) and ships a corresponding bibitem (`paper_draft.tex:404-409`). The registry entry has `doi_verified: None`. Per Gate 1: "Every registry entry has `arxiv_verified == True` AND `doi_verified == True` (where applicable)." DOI `10.3847/2041-8213/aa920c` was Crossref-resolvable on this round (verified via `https://arxiv.org/abs/1710.05834` returning ApJL 848:L13 (2017), DOI 10.3847/2041-8213/aa920c — match).
- **Evidence:** `grep -A18 "    'Abbott2017GW170817': {" src/core/citations.py | grep doi_verified` returns `'doi_verified': None,`. Fresh WebFetch of `https://arxiv.org/abs/1710.05834` returned title "Gravitational Waves and Gamma-rays from a Binary Neutron Star Merger: GW170817 and GRB 170817A", journal-ref ApJL 848:L13 (2017), DOI 10.3847/2041-8213/aa920c — matches paper40 bibitem character-for-character on title, journal, volume, page, year, arXiv ID. The `doi_verified: None` flag is a stale gap from when this entry was first added (Phase 6a Wave 2) before the project-wide DOI-verification pass.
- **Expected:** Flip `Abbott2017GW170817.doi_verified: None → True` in `src/core/citations.py:3075`. Append a `citation_verifications.jsonl` record with the WebFetch evidence from this round.
- **Fix:** One-line edit + cache append. Severity REQUIRED (not BLOCKER) because the citation is correct on substance — the metadata flag is a project-internal verification ledger, not the citation itself. Same paper40-cited bibkey was correctly verified before (it shipped in paper25 with the same DOI), so the `None` is bookkeeping drift, not a hallucination.
- **Cache:** fresh-fetch (verdict: match for arXiv 1710.05834 ↔ ApJL 848:L13)

### 7.1 — 🔵 RECOMMENDED — Two inline unit-bearing literals in §5 prose: `9.49\times 10^{-4}`

- **Gate:** NumericalFreshness (Gate 9, `numerical_literals` check)
- **Location:** `paper_draft.tex:263-264` (Eq. \eqref{eq:c-riem-numeric}), `paper_draft.tex:269-270` (ratio computation `10^{59}/9.49\times 10^{-4} \approx 10^{62}`).
- **Observed:** `validate.py --check numerical_literals` flags paper40 with `2 inline literal(s): L263 "9.49\times 10^"; L269 "9.49\times 10^"` (passing as warning currently). Gate 9 says: "WARN-acceptable at draft stage; FAIL at submission once retrofit is complete."
- **Evidence:** `validate.py` full-suite output: `paper40_higher_curvature  —  2 inline literal(s): L263 "9.49\times 10^"; L269 "9.49\times 10^"` (warning, not blocker). Gate state `NumericalFreshness: needs-recheck`.
- **Expected:** Move `9.49\times 10^{-4}` to a `papers/paper40_higher_curvature/tables/c_riem_anchor.tex` autogen file (via `tables.py` spec) or define a `\pipelinevalue{c_riem_27}` macro that resolves to the canonical computed value at compile time. The §5 paragraph titled "Anchoring the '62 orders below' claim" was added precisely to make this calculation explicit; the trade-off is that it introduces inline literals.
- **Fix:** Add a `\pipelinevalue{c_riem_27}` macro pointing at `formulas.higher_curvature_Riemann_sq_coefficient(27)` evaluated at compile time, OR move the equation contents into a `\input{tables/c_riem_anchor.tex}` auto-table. Severity RECOMMENDED because Gate 9 explicitly tolerates inline literals at draft stage — only at submission do they FAIL.
- **Cache:** N/A

### 7.2 — 🔵 RECOMMENDED — paper40 not yet in `PAPER_DRAFT_MAPPING.md`

- **Gate:** NarrativeGrounding (Gate 7) — adjacent: cross-paper bundle integrity
- **Location:** `docs/PAPER_DRAFT_MAPPING.md` (memory `project_phase6e_w5_shipped.md` records that paper39-42b were added but does not mention paper40 explicitly).
- **Observed:** Per `MEMORY.md > project_phase6e_w5_shipped`: "Closes Wave 4 deferred 8.1 + Phase 6e bundle-mapping gap (paper39-42b added to PAPER_DRAFT_MAPPING.md → D3 §17–§21 + D5 §7)". Paper40 (Phase 6e Wave 2) is not in the listed range. If paper40 lives outside the bundle mapping, downstream consumers (e.g. dissertation chapter assembly, dashboard's bundle view) won't surface it.
- **Evidence:** Project memory entry as quoted; this is a bookkeeping observation, not a paper-content issue.
- **Expected:** Verify `docs/PAPER_DRAFT_MAPPING.md` contains a paper40 entry; if not, add one mapping paper40 to its target dissertation section (most likely D3 §17 alongside paper39-41-42-42b given the Phase 6e thematic clustering).
- **Fix:** One-line addition to `PAPER_DRAFT_MAPPING.md`. Severity RECOMMENDED (not REQUIRED) because the gate impact is hypothetical (no consumer is currently failing on it); the issue is just dictionary completeness.
- **Cache:** N/A

### 8.1 — 🔵 RECOMMENDED — `\bibitem{Lovelock1971}` cache file is `.abstract.txt` (439 bytes) only

- **Gate:** CitationIntegrity (Gate 1) — primary-source cache shape
- **Location:** `Lit-Search/Phase-6e/primary-sources/Lovelock1971.abstract.txt` (439 B); `src/core/citations.py:Lovelock1971.primary_source_path`.
- **Observed:** Lovelock 1971 (J. Math. Phys. 12:498) is paywalled and pre-arXiv, so a full PDF is not freely available. The Phase 6i Wave 1 cache rollout retained an abstract-only sidecar at 439 bytes. This is consistent with project precedent (Bertotti-Iess-Tortora 2003 also has only a Crossref JSON sidecar, not a full PDF), but the Lovelock abstract is short enough that a future automated cross-check (e.g. "does this paper actually contain the Gauss-Bonnet identity?") would not have enough text to ground on.
- **Evidence:** `wc -c Lit-Search/Phase-6e/primary-sources/Lovelock1971.abstract.txt` → 439. The abstract is a single paragraph; mathematical identities like "δ G^μν / δ g_μν = 0 for Gauss-Bonnet density in 4D" are not present.
- **Expected:** Either accept the abstract-only sidecar as "paywalled-pre-arXiv" precedent (with notes capturing this in `citations.py:Lovelock1971.notes`), or add a richer Crossref-metadata JSON sidecar with the abstract + structured journal metadata. The current file is functional for CHECK 19 (which only requires presence) but minimal for downstream LLM-cross-check tools.
- **Fix:** Optional. If desired, replace `Lovelock1971.abstract.txt` with `Lovelock1971.json` containing Crossref full record + abstract. Severity RECOMMENDED.
- **Cache:** N/A

### Other classes — no findings

- **Class 1 (CitationIntegrity, primary):** All 11 paper40 bibkeys are in `CITATION_REGISTRY` with `doi_verified: True` (10) or `inprep: True` (1, `Roehm2026Wave1`). All 10 external entries have non-empty `primary_source_path` and the cache files exist (`Vassilevich2003.pdf` 763 KB, `ChristensenDuff1979.json` 17 KB, `Stelle1977.json` 5.8 KB, `Lovelock1971.abstract.txt` 439 B [see Finding 8.1], `CalmetCapozzielloPryer2017.pdf` 154 KB, `Berti2015.pdf` 7.1 MB, `Abbott2017GW170817.pdf` 2.1 MB at Phase-6a, `Kapner2007.pdf` 351 KB, `WeisbergHuang2016.pdf` 4.4 MB, `BertottiIessTortora2003.json` 12.7 KB). Fresh WebFetch on the four post-Wave-2 entries (Abbott, Kapner, WeisbergHuang, BertottiIessTortora) returned `verdict: match` for every bibitem field (title, authors, journal, volume, page, year, DOI, arXiv ID where present). The single Gate 1 advisory (Finding 1.1 above) is on the `doi_verified` ledger flag, not the citation itself.
- **Class 2 (ParameterDrift):** All four HC_BOUND values (`HC_BOUND_LIGO_C_SQ = 1.0e62`, `HC_BOUND_SRG_R_SQ = 1.0e61`, `HC_BOUND_PULSAR_C_SQ = 1.0e59`, `HC_BOUND_CASSINI_C_SQ = 1.0e62`) match the order-of-magnitude ceilings stated in `paper_draft.tex:200-208`. The Wave 1 Christensen-Duff-Vassilevich coefficients $(c_R, c_{\mathrm{Ric}}, c_{\mathrm{Riem}}) = (-5/2160, +7/2160, -12/2160)$ in `lean/SKEFTHawking/HigherCurvatureStructure.lean` are bit-identical to the Wave 1 paper39 inheritance (paper40 §1, Eq. \eqref{eq:a4}). The Stelle coefficients $(\alpha, \beta, \gamma) = (-1/324, -41/4320, +17/4320) \cdot N_f / (4\pi)^2$ in §3 Eq. \eqref{eq:abg} verified against the linear system Eq. \eqref{eq:linsys} by independent solve (see Wave 1 review §"Class 2"). The new `human_verified_notes` strings for the four HC_BOUND entries are substantive (mention specific table/section references in the primary sources, e.g. "Kapner Table I and abstract", "PSR B1913+16 period-decay precision 0.13% (Table 2)") — adequate provenance.
- **Class 3 (LeanProofSubstance):** All cited Lean theorems (`a4_density_eq_a4_density_in_RC2GB_basis`, `a4_alpha_neg`, `a4_beta_neg`, `a4_gamma_pos`, `higher_curvature_below_pulsar_bound`, `higher_curvature_predictions_strictly_positive`, `H_HigherCurvatureWithinObservationalBounds_pulsar_witness`, `gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination`, `weylSquared4D_eq_zero_iff_conformally_flat`) have substantive tactic-mode proof bodies (linarith / norm_num / abs_neg chains, mul_le_mul / positivity, ring after unfold) — no `rfl`-on-non-trivial, no hypothesis-as-output anonymous constructors. The 3-conjunct bundle in `higher_curvature_below_pulsar_bound` invokes three distinct Wave 1 coefficients with three distinct positivity arguments (P3 not redundant, per `paper_draft.tex:252-256`); the tracked-Prop witness consumes the correctness-push and is fully discharged at `B = 10^59` (P5 not vacuous). `LeanProofSubstance` gate state: `passed`.
- **Class 4 (CrossPaperConsistency):** Six shared bibkeys with companion papers — Vassilevich2003 (paper39, paper41, paper42, paper42b, paper43, paper40), ChristensenDuff1979 (paper39, paper41, paper42, paper40), Stelle1977 (paper41, paper42, paper42b, paper40), Berti2015 (paper42, paper40), Abbott2017GW170817 (paper25, paper40), Kapner2007/WeisbergHuang2016/BertottiIessTortora2003 (paper40-only). Sampled cross-paper bibitems (paper42 ChristensenDuff1979 / Vassilevich2003 / Stelle1977 / Berti2015; paper25 Abbott2017GW170817) match paper40 bibitems character-for-character on the load-bearing fields (arXiv ID, journal, volume, page). `CrossPaperConsistency` gate state: `passed`.
- **Class 5 (NarrativeOverclaims):** No `first formally verified` / `first in any proof assistant` / unification claims. The `~62 orders of magnitude below` feasibility claim (abstract:50-51, fig caption:218-222, conclusion:343-345) is anchored quantitatively in §5's "Anchoring the '62 orders below' claim" paragraph with explicit calculation; the inline literals there triggered Finding 7.1. No production-run / Monte-Carlo claims.
- **Class 6 (AssumptionDisclosure):** `higher_curvature_below_pulsar_bound` carries hypotheses `0 < N_f` and `N_f ≤ 100`; both disclosed in `paper_draft.tex:237` (Lean code-block: `(hN_pos : 0 < N_f) (hN_max : N_f ≤ 100)`) and §5 prose ("natural fermion-count window $0 < N_f \le 100$"). The tracked-Prop framing in §5 ("forward-compatibility hook for tighter ceilings") is correct per Wave 1 round-1 Finding 6.1 closure. `AssumptionDisclosure` gate state: `passed`.
- **Class 7 (CountFreshness):** Macros `\higherCurvatureThms{}` (= 11) and `\higherCurvatureTests{}` (= 40) sourced from `\input{../../docs/counts.tex}`; no inline count literals (the inline `9.49\times 10^{-4}` literals are unit-bearing numerical, not counts — see Finding 7.1). `validate.py --check counts_fresh` PASSES with `theorems=4504 substantive=4481 placeholder=23 modules=195 sorry=0 papers=39 aristotle_proved=322`.
- **Class 8 (ProductionRunHealth):** Paper makes no Monte Carlo / numerical-simulation evidence claims. `grep -E "Monte Carlo|numerical evidence|simulation evidence" paper_draft.tex` returns zero. `ProductionRunHealth` gate state: `passed`.

## Summary of Gate States (post-Wave-2)

| Gate | State (post-W2) | Notes |
|---|---|---|
| 1. CitationIntegrity | passed (1 advisory) | All bibkeys registered; one `doi_verified: None` ledger gap (Finding 1.1) |
| 2. CrossPaperConsistency | passed | All six shared bibkeys consistent across papers |
| 3. ParameterProvenance | passed | All four HC_BOUND human_verified |
| 4. ComputationCorrectness | **blocked** | Bounds-only test on `higher_curvature_predicted_in_observational_band` (Finding 4.1) |
| 5. LeanProofSubstance | passed | All cited theorems substantive |
| 6. AssumptionDisclosure | passed | Hypotheses disclosed |
| 7. NarrativeGrounding | passed | No unbacked interesting claims |
| 8. ProductionRunHealth | passed | No simulation claims |
| 9. NumericalFreshness | needs-recheck | 2 inline literals (Finding 7.1) |
| 10. FirstClaimVerification | passed | No first-claims |
| 11. FixPropagation | needs-recheck | 13 round-1 ReviewFinding nodes still `status: open` (Finding 11.1) |

**Submission readiness:** **NOT YET** — Gate 4 (ComputationCorrectness)
remains `blocked` until a `golden`-shape test is added on
`higher_curvature_predicted_in_observational_band`. Closing the
qi-citationintegrity + qi-parameterprovenance gates is INDEPENDENT of
Gate 4: those two are about citation-registry coverage and provenance
human-verification, both of which Wave 2 closed.

## QI Candidates

**Recommended QI flips:**

- **`qi-citationintegrity` (paper40-scoped):** flip `open → closed` for paper40. The structural failure mode that permitted the round-1 hallucination (`CalmetCapozzielloPryer2019` arXiv:1905.13728 graph-NN paper) is now blocked by Pipeline Invariant #11 (every external bibitem has a primary-source cache file) and CHECK 19 (`citation_primary_sources_present`). Paper40's 11 bibkeys all satisfy it (10 cached, 1 inprep-exempt). Project-wide `qi-citationintegrity` remains `open` until 99 outstanding bibkeys cache through Phase 6i Waves 4-5.
- **`qi-parameterprovenance` (paper40-scoped):** flip `open → closed` for paper40. All four HC_BOUND entries human-verified 2026-04-28 with substantive notes; `cited_bibkeys` field populated; CHECK 20 (`provenance_doi_in_registry`) passes for paper40's 8 cited DOIs.

**Adjacent QI surfaced by this re-review:**

- **`qi-fixpropagation-tracking`** (NEW): The Wave 2 close did not flip ReviewFinding nodes from `status: open → fixed` despite structural remediation (round-1 BLOCKER 1.1 / 1.2 are still in graph as open even though paper_draft.tex and citations.py have been correct for 10+ days). A scripts-level remediation — either (a) extend `extract_review_finding_nodes.py` to honour explicit `status: fixed` markers in re-review YAML/MD frontmatter, or (b) ship `scripts/close_review_findings.py` as a one-shot bulk-flip — would close the loop. This is the same pattern as `qi-provenance-citation-coverage` from Wave 1: a tracking infrastructure gap surfaced by the re-review.

- **`qi-formula-test-shape`** (NEW): The Gate 4 `bounds-only` failure mode for `higher_curvature_predicted_in_observational_band` is a recurrence pattern. Boolean-returning formulas naturally generate `bounds`-shape tests (`assert f(...)`, `assert not f(...)`) but Gate 4 requires `golden / identity / roundtrip`. A pre-write checklist item — "if your formula returns `bool`, add a `golden` test on the underlying numeric coefficient, not just the Boolean output" — would catch this prospectively. Could be folded into the existing preemptive-strengthening discipline (CLAUDE.md). Several other paper-blocked formulas in `validate.py` output (paper2 / paper4 / paper5 / paper6 / paper7 / paper25 / paper26 / paper41 / paper42 all show `1 blocked: ComputationCorrectness`) suggest this is a project-wide pattern, not paper40-specific.

- **`qi-doi-verification-ledger-drift`** (NEW): `Abbott2017GW170817` shipped with `doi_verified: None` despite (a) being cited in two papers, (b) being primary-source-cached, and (c) the DOI being trivially Crossref-resolvable. The `doi_verified` flag is set only when an explicit verification pass runs; passive coverage from CHECK 19 (cache presence) doesn't flip it. A `validate.py --check doi_verified_when_cached` warning would surface this class.

## Post-Review Author Action (same session, recorded for transparency)

Per the agent spec, this section documents fixes applied by the author *after*
the review was written but during the same session. These are NOT findings
the agent worked around — they are the natural author-side response to the
findings emitted above. Re-verification of these fixes will happen in the
next Stage 13 invocation; this section is a paper trail, not a substitute.

| Finding | Fix applied | Evidence |
|---|---|---|
| 1.1 — `Abbott2017GW170817.doi_verified: None` | ✅ Flipped to `True` | `src/core/citations.py:Abbott2017GW170817.doi_verified` now reads `True`. Verified by direct re-read post-edit: `doi=10.3847/2041-8213/aa920c; doi_verified=True; used_in=['papers/paper25_gravitational_waves/paper_draft.tex', 'papers/paper40_higher_curvature/paper_draft.tex']`. |
| W1 1.1 cache append | ✅ Completed | 4 records appended to `docs/citation_verifications.jsonl` recording fresh-fetch matches for `Abbott2017GW170817`, `Kapner2007`, `WeisbergHuang2016`, `BertottiIessTortora2003` against paper40 bibitem hashes. Each record carries `verdict: match`, `reviewer: adversarial-reviewer:phase6i-w2-reverification`, `verified_date: 2026-04-28`. Total cache lines: 30 → 34. |

Findings **4.1** (Gate 4 ComputationCorrectness — bounds-only test) and
**11.1** (Gate 11 FixPropagation — round-1 ReviewFinding nodes still
`status: open`) are NOT fixed in this session — they belong to separate
remediation tracks (4.1 → paper40 author; 11.1 → pipeline/scripts owner).
Findings 7.1, 7.2, 8.1 (RECOMMENDED) are draft-acceptable and queued.

## Final Verdict

**For the qi-citationintegrity and qi-parameterprovenance Wave-2-targeted
gates:** **CLOSEABLE for paper40.** Both round-1 REQUIREDs are
structurally fixed; CHECK 19 satisfied for paper40's 11 bibkeys (10
cached, 1 inprep-exempt); CHECK 20 satisfied for paper40's 8
`cited_bibkeys` (0 missing); all four HC_BOUND parameter-provenance
entries human-verified with substantive primary-source narratives;
strict-mode `parameter_provenance` is non-blocking for paper40 (the 2
project-wide strict blockers — Rb87.a_s, Steinhauer.velocity_upstream
— are not consumed by paper40).

**For overall paper40 submission readiness:** **NOT YET.** Gate 4
(ComputationCorrectness) remains `blocked` until a `golden`-shape test
is added on `higher_curvature_predicted_in_observational_band` (Finding
4.1). This is independent of Wave 2's citation/provenance scope.

**For Phase 6i Wave 2 closure (Decision Gate I.2):** **PASS** — the
gate condition is "all submission-pending papers' Pipeline Invariant 8
gate passes strict mode," which is satisfied for paper40 (the only
paper specifically named in the Wave 2 roadmap as the unblock target).

**Re-invocation needed:** Yes, after Findings 4.1 and 11.1 are fixed.
The next Stage 13 invocation should observe a fully `passed` gate
table and zero open ReviewFinding nodes — that round will mark paper40
as fully submission-ready (subject to Gate 4 remediation landing).
