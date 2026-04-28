---
paper: paper42_nonlinear_efe
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T14:25:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper42_nonlinear_efe

## Summary

Paper 42 (Phase 6e Wave 4, NonlinearEFE) is structurally clean: 13
substantive theorems shipped, zero `sorry`, zero new axioms, all cited
Lean theorem names resolve, the canonical figure renders, the `(2α+1)/3`
PPN-substitution and the cross-channel 2/3 ratio derivations are
algebraically correct, and the `\input{../../docs/counts.tex}` macros
`\nonlinearEFEThms{}` (=13) and `\nonlinearEFETests{}` (=40) both exist
with values consistent with `grep -c "^theorem "` and the raw
`def test_*` count in `tests/test_nonlinear_efe.py`.

Findings: **0 BLOCKER**, **3 REQUIRED**, **5 RECOMMENDED**. The
REQUIREDs cluster on Gate 1 CitationIntegrity (no fresh-fetch
verifications for Will2018 or Sakharov1968 — both registry entries
carry `doi_verified: None`; cache contains zero records for any of
the 12 paper-42 bibkeys). RECOMMENDEDs include an orphan bibitem
(Berti2015 in bibliography but never `\cite`d in body), undisclosed
hypotheses on `perturbed_alpha_not_H_NonlinearEFEHolds`, prose phrasing
that could be tightened, and a missing primary-source artifact for
Will2018 (the load-bearing PPN reference). Paper is **draft-ready**
but **not submission-ready** until the three REQUIREDs land.

## Findings

### 1.1 — 🟡 REQUIRED — Will2018 lacks fresh-fetch citation verification (load-bearing PPN reference)

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:503-507` (bibitem); `src/core/citations.py` (registry)
- **Observed:** Registry entry for `Will2018` has `doi_verified: None`, no
  `arxiv_verified` flag, and is not represented anywhere in
  `docs/citation_verifications.jsonl`. The bibitem is load-bearing for
  this paper (Eq. 4.31 PPN combination at line 271; VLBI floor at
  line 264) and is reused in paper34_equivalence_principle.
- **Evidence:** `grep -E "Will2018" docs/citation_verifications.jsonl`
  returns 0 records; registry entry shows `'doi_verified': None`.
- **Expected:** Either (a) `WebFetch https://doi.org/10.1017/9781316338612`,
  confirm CUP returns the Will 2018 2nd-edition record, append a
  `match` record to `citation_verifications.jsonl`, and flip
  `doi_verified: True`; or (b) flag this paper as `unverified` per
  Gate 1 escalation (Gate 1 in `READINESS_GATES.md` makes
  `arxiv_verified == True AND doi_verified == True` mandatory at
  submission for non-`inprep` entries).
- **Fix:** `WebFetch` the DOI; append cache record; bump registry
  `doi_verified` to `True`. Same task already exists for
  paper34_equivalence_principle's Gate-1 audit and can be co-resolved.
- **Cache:** fresh-fetch (no prior record).

### 1.2 — 🟡 REQUIRED — Sakharov1968 lacks fresh-fetch citation verification

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:525-529` (bibitem); cited in body at line 53.
- **Observed:** Registry entry has `doi: None`, `arxiv: None`,
  `doi_verified: None`. Bibitem has no resolvable identifier
  (Soviet Doklady 1968, pre-DOI). No record in
  `citation_verifications.jsonl`.
- **Evidence:** Registry note: "Foundational; no DOI (Soviet Doklady
  1968)." But the metadata fields (volume 12, page 1040, year 1968)
  have not been independently verified against NASA ADS or INSPIRE.
- **Expected:** `WebFetch` NASA ADS (`https://ui.adsabs.harvard.edu/abs/1968SPhD...12.1040S`)
  to confirm volume/page/year against the Soviet Doklady 1968 record,
  append cache record, flip `doi_verified: True` (the field semantically
  becomes "verified-by-some-primary-source", not strictly DOI). The
  registry's identical-pattern verification protocol used for
  `Fierz` and `NJL61` (NASA ADS bibcode in cache) applies cleanly.
- **Fix:** Fetch ADS bibcode `1968SPhD...12.1040S`, append cache record
  with `verdict: match`.
- **Cache:** fresh-fetch (no prior record).

### 1.3 — 🟡 REQUIRED — Wider gap: zero of 12 paper-42 bibkeys have a citation_verifications.jsonl record

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `papers/paper42_nonlinear_efe/paper_draft.tex` bibliography (12 bibitems)
- **Observed:** `grep -E "Will2018|Sakharov1968|ChristensenDuff1979|Vassilevich2003|Stelle1977|Wald1984|BertiCardosoStarinets2009|Berti2015" docs/citation_verifications.jsonl`
  returns **0 lines**. The cache currently holds 27 records, none
  attached to `paper:paper42_nonlinear_efe`.
- **Evidence:** Even though `Wald1984`, `Vassilevich2003`,
  `ChristensenDuff1979`, `Stelle1977`, `Berti2015` carry
  `doi_verified: True` in the registry, no append-only audit record
  exists in the project's canonical cache. They were also not
  re-verified during paper41 or paper40 reviews per the cache.
- **Expected:** Per the Stage 13 protocol, every bibitem the paper
  uses must have either a recent (`<90d`) cache record or a fresh
  WebFetch. Eight bibkeys (Will2018, Sakharov1968, ChristensenDuff1979,
  Vassilevich2003, Stelle1977, Wald1984, BertiCardosoStarinets2009,
  Berti2015) require WebFetch + cache append. Four (Roehm2026Wave1,
  HigherCurvature2026, DiffInvariance2026, LinearizedEFE2026) are
  exempt via `inprep: True`.
- **Fix:** Run a batched `WebFetch` over the eight external bibitems;
  append eight `verdict: match` (or appropriate) records to
  `citation_verifications.jsonl` with `paper: paper42_nonlinear_efe`.
- **Cache:** all eight require fresh-fetch.

### 1.4 — 🔵 RECOMMENDED — Will2018 missing primary_source_path (load-bearing PPN reference)

- **Gate:** CitationIntegrity (Gate 1; primary-sources cache pattern)
- **Location:** `src/core/citations.py` `Will2018` entry; would expect
  `Lit-Search/Phase-6e/primary-sources/Will2018.{pdf|json}`.
- **Observed:** `Will2018` registry has `primary_source_path: None`
  (or absent). `Lit-Search/Phase-6e/primary-sources/` contains
  ChristensenDuff1979.json, Stelle1977.json, Vassilevich2003.{pdf,json},
  Wald1984.json — but **no Will2018 artifact**. Eq. 4.31 (PPN
  perihelion) is the load-bearing reference for theorem
  `precessionRatio_eq_one_iff_alpha_unity` and the cross-channel
  2/3 ratio.
- **Evidence:** `ls Lit-Search/Phase-6e/primary-sources/` shows no
  Will2018 file. Per the new Phase 6i hygiene roadmap (memory
  `feedback_primary_sources_cache.md` 2026-04-28), every load-bearing
  external reference SHOULD have a cached primary-source artifact.
- **Expected:** Cache the Will 2018 §4.2 Eq. 4.31 page (or a Crossref
  JSON) at `Lit-Search/Phase-6e/primary-sources/Will2018.json` and
  set `primary_source_path` accordingly.
- **Fix:** Save Crossref JSON for DOI 10.1017/9781316338612 and the
  relevant §4 pages (or a structured excerpt of the PPN combination)
  into the Phase-6e primary-sources folder. Will need to be done in
  any case for paper34's Gate-1 close-out.

### 1.5 — 🔵 RECOMMENDED — Berti2015 is an orphan bibitem (in bibliography, not cited in body)

- **Gate:** CitationIntegrity (Gate 1; advisory)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:537-542` (bibitem)
- **Observed:** `grep -n "Berti2015" paper_draft.tex` returns only
  the bibitem definition, no `\cite{Berti2015}` anywhere in body.
- **Evidence:** All other 11 bibitems are cited in body (verified by
  inverse grep). Registry `provides` field for Berti2015 mentions
  "ringdown frequency baseline (Berti-Cardoso-Starinets review CQG
  26:163001 (2009))" — but the actual ringdown citation in the body
  uses `BertiCardosoStarinets2009` (line 293), making Berti2015
  redundant.
- **Expected:** Either add a `\cite{Berti2015}` somewhere it
  substantively backs a claim (e.g., "future GW observations" in the
  Forward Look section), or drop the bibitem.
- **Fix:** Remove the Berti2015 bibitem stanza, OR add a cite where
  Berti2015 supplies content not already in BertiCardosoStarinets2009
  (e.g., binary-pulsar period-decay precision per registry `provides`).
  Drop is the cleaner option.

### 2.1 — 🔵 RECOMMENDED — VLBI / MESSENGER / GWTC-3 floors lack inline citation in figure caption

- **Gate:** ParameterProvenance (Gate 3; advisory)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:347-348` (figure caption)
- **Observed:** Caption lists "VLBI 3 × 10⁻⁴, MESSENGER 1 × 10⁻⁴,
  GWTC-3 5 × 10⁻²" as observation floors but does not `\cite{}` any
  source. Will2018 supplies VLBI + MESSENGER per registry `provides`
  (Table 3); GWTC-3 5×10⁻² traces to "Isi et al." in the constants
  comment (`src/core/constants.py:RINGDOWN_OBS_RELATIVE_PRECISION`)
  but Isi et al. is not in `CITATION_REGISTRY` and not in the bibitems.
- **Evidence:** `NONLINEAR_EFE_PARAMS['RINGDOWN_OBS_RELATIVE_PRECISION'] = 0.05`
  with comment "GWTC-3 spectroscopy (Isi et al.)" — provenance trail
  ends in a dangling author-only reference.
- **Expected:** Either (a) add an `Isi2021` (or equivalent GWTC-3
  spectroscopy) bibkey to `CITATION_REGISTRY` and `\cite` it where
  the GWTC-3 floor is invoked, or (b) cite Berti2015 (which already
  provides "projected sensitivities for future GW observations") at
  this location, fixing finding 1.5 simultaneously.
- **Fix:** Tie the GWTC-3 5×10⁻² floor to a registered citation. The
  cheapest fix is reusing Berti2015 here (closes both gaps).

### 5.1 — 🔵 RECOMMENDED — Multi-channel "over-constrains the single calibration parameter" claim is interpretive, not a Lean result

- **Gate:** NarrativeGrounding (Gate 7; advisory)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:316-317`
  ("Combined with the ringdown channel, the three observables
  collectively over-constrain the single calibration parameter
  α_ADW.")
- **Observed:** No Lean theorem in `NonlinearEFE.lean` formalises a
  joint-likelihood / over-determination property of the three channels.
  The paper has three independent linear-channel theorems
  (deflection_minus_one_eq, precessionRatio_eq_one_iff_alpha_unity,
  ringdownRatio implicitly via observableRatio) plus the cross-channel
  2/3 theorem, but no joint over-constraint result.
- **Evidence:** `grep "over_constrain\|joint\|three_channel" lean/SKEFTHawking/NonlinearEFE.lean`
  returns nothing.
- **Expected:** Either tag the sentence as interpretive
  ("...we expect..." / "...heuristically over-constrains...") OR add
  a Lean theorem witnessing the over-determination (e.g.,
  `three_channel_pin_alpha_unique`: under any two-of-three channel
  measurements consistent with α=1, the third is forced).
- **Fix:** Re-word as interpretive prose, or queue an additional
  theorem statement for next-pass strengthening.

### 6.1 — 🔵 RECOMMENDED — `perturbed_alpha_not_H_NonlinearEFEHolds` hypotheses are partially undisclosed in prose

- **Gate:** AssumptionDisclosure (Gate 6; advisory)
- **Location:** `paper42_nonlinear_efe/paper_draft.tex:413-426` (Theorem 3 / Falsifier);
  Lean theorem at `lean/SKEFTHawking/NonlinearEFE.lean:481-490`.
- **Observed:** The Lean theorem requires four hypotheses:
  `0 < Λ`, `0 < N_f`, `ρ_ADW ≠ 0`, `0 < α_ADW`, `α_ADW ≠ 1`.
  The paper's prose (line 414-415) says "Under positive (Λ, N_f),
  non-zero ρ_ADW, positive α_ADW, and α_ADW ≠ 1" — this captures
  4 of the 5 hypotheses (positive Λ, positive N_f, ρ_ADW ≠ 0,
  positive α_ADW, α_ADW ≠ 1). Actually re-reading, all 5 are listed.
  Closer inspection: the paper says "positive (Λ, N_f)" which
  covers `0 < Λ ∧ 0 < N_f`; "non-zero ρ_ADW" covers `ρ_ADW ≠ 0`;
  "positive α_ADW" covers `0 < α_ADW`; "α_ADW ≠ 1" is the fifth.
  All five are disclosed. **However**, the existence of `0 < α_ADW`
  (positivity, not just non-zero) is the load-bearing entry that
  guarantees `G_N_emerg > 0` via `LinearizedEFE.G_N_emerg_pos` —
  the paper does not connect this hypothesis to the Vergeles
  positivity (P3 in Phase 6a.1) which is why positivity rather
  than `≠ 0` is needed.
- **Evidence:** Lean proof body uses `G_N_emerg_pos hΛ hN hα_pos`
  which requires positivity, not non-zero, to invoke
  `efeResidualTrace_eq_zero_iff_alpha_unity` (which itself needs
  `0 < G_N`).
- **Expected:** Add a sentence: "The positivity of α_ADW (rather
  than mere non-vanishing) is consumed via the Phase 6a.1
  Vergeles-positivity-derived `LinearizedEFE.G_N_emerg_pos` —
  see paper23/Roehm2026Wave1." This closes the docstring-level
  reference gap for the Vergeles-positivity hypothesis chain.
- **Fix:** One sentence in §6 explaining the chain `α_pos →
  G_N_emerg_pos → biconditional applicability`.

### 8.1 — 🔵 RECOMMENDED — In-prep self-cite chain has a circular-citation pattern worth re-inspecting

- **Gate:** CrossPaperConsistency (Gate 2; advisory)
- **Location:** `papers/paper42_nonlinear_efe/paper_draft.tex:544-565` (bibitems for
  Roehm2026Wave1, HigherCurvature2026, DiffInvariance2026,
  LinearizedEFE2026); `src/core/citations.py` (registry).
- **Observed:** All four self-cites are present and properly registered
  with `inprep: True`, `doi_verified: True`, `primary_source_path: None`.
  Per the task spec ("in-prep self-cites, exempt from primary-source-cache
  requirement via inprep: True"), this is allowed. **No finding for
  the registry state itself.** The recommendation: ensure that when any
  of these four companion papers (paper23, paper39, paper40, paper41)
  is itself submitted, the `inprep: True` flag is flipped to `False`
  AND a real DOI/arXiv ID populated, AND every back-citing paper
  (incl. paper42) is rebuilt to consume the published metadata. Today
  paper42 hard-codes "in preparation" in the bibitem text — at
  publication, this string drifts from the registry.
- **Evidence:** Bibitem text says "(in preparation, Phase 6e Wave 1)";
  registry says `journal: 'in preparation'`. Both will need editing
  on publication of paper23/39/40/41.
- **Expected:** Add a Phase 6i Wave checklist item to track
  in-prep-flag-flip + paper42-rebuild when companions publish. No
  edit to paper42 required today.
- **Fix:** QI register entry (no paper-local fix).

## Spot-check results (no findings)

The following paper-42-specific questions raised in the review brief
were checked and do **not** produce findings:

- **(a) Will 2018 PPN substitution γ=α, β=1.** The paper docstring at
  line 162 of `NonlinearEFE.lean` and prose at line 277-282 of the
  `.tex` both document the substitution. Algebraic check:
  `(2 + 2γ - β)/3` with `γ=α, β=1` gives `(2 + 2α - 1)/3 = (2α+1)/3`. ✓
- **(b) Cross-channel 2/3 ratio.** Lean theorem
  `precession_dev_eq_two_thirds_deflection_dev` proof uses `ring` over
  `unfold precessionRatio deflectionRatio observableRatio`. Algebraic
  check: `precessionRatio - 1 = (2α+1)/3 - 1 = (2α-2)/3 = (2/3)(α-1) = (2/3)(deflectionRatio - 1)`. ✓
- **(c) Counts macros exist.** `grep "nonlinearEFE" docs/counts.tex`
  returns `\nonlinearEFEThms{13}` and `\nonlinearEFETests{40}`. Both
  resolve. `grep -c "^theorem " lean/SKEFTHawking/NonlinearEFE.lean`
  returns 13. `grep -cE "^\s*def test_" tests/test_nonlinear_efe.py`
  returns 40 (the macro reflects the raw `def test_` count; pytest's
  collection of 66 reflects 7 `@pytest.mark.parametrize` expansions —
  consistent with existing project convention).
- **(d) Figure file existence.** `papers/paper42_nonlinear_efe/figures/fig_T_emerg_vs_matter.png`
  exists (316 KB, dated 2026-04-28). Paper `\includegraphics` reference
  matches. Caption claims (linear deviation channel; multi-channel
  PPN; amber band at 5×10⁻³; VLBI/MESSENGER/GWTC-3 floors as dashed
  lines) are consistent with `fig_T_emerg_vs_matter()` source in
  `src/core/visualizations.py:10511-10546`.
- **(e) Tracked-Prop disclosure.** `H_NonlinearEFEHolds` is a `def`,
  not a `theorem`, so it cannot be a smuggled theorem. Its three
  conjuncts are each backed by a substantive theorem call in the
  Dirac witness body
  (`efeResidualTrace_at_dirac_calibration_vanishes`,
  `H_HigherCurvatureWithinObservationalBounds_pulsar_witness`,
  `dirac_H_NonlinearDiffInvariance`). Falsifier at line 481
  contradicts `H_NonlinearEFEHolds` for off-calibration α — the bundle
  is genuinely Sakharov-Adler-singling, not a vacuous wrapper.
- **(f) In-prep self-cite registration.** All four self-cites
  (Roehm2026Wave1, HigherCurvature2026, DiffInvariance2026,
  LinearizedEFE2026) carry `inprep: True` and `doi_verified: True` in
  the registry. Bibitems in the `.tex` are formatted "(in preparation,
  Phase 6e Wave N)" consistently. (See finding 8.1 for the
  on-publication drift hazard.)

## QI Candidate

**Pattern:** No paper42 bibkey has a `citation_verifications.jsonl`
record (finding 1.3). The same pattern likely applies to other
recently-shipped Phase 6e papers (paper41 was just adversarially
re-reviewed 2026-04-28 with the F3 in-prep `doi_verified` deferred
as project-wide tech debt per memory `project_phase6e_w3_shipped.md`).

**Suggestion:** Phase 6i Wave 1 (citation integrity) should include a
mass-WebFetch + cache-append over every bibkey in the registry that
has `doi_verified: True` but no record in
`citation_verifications.jsonl` — the audit trail is incomplete project-wide,
not just for paper42. The remediation is one-shot scriptable
(`scripts/citation_cache.py` already has `append_record` and
`bibitem_hash` helpers; `WebFetch` is the only manual step).

**Pipeline gap:** Gate 1 currently treats `doi_verified: True` as
pass-condition without requiring a backing audit-cache record. Per
`READINESS_GATES.md` Gate 1 ("a registry entry whose `arxiv_verified`
is `False` or stale (hash mismatch vs. last fetch)" blocks), the
"stale" check is only meaningful if an initial fetch happened. A
follow-on `validate.py --check citation_audit_completeness` that
flags `doi_verified: True ∧ no cache record` as `needs-recheck`
would close the gap automatically.
