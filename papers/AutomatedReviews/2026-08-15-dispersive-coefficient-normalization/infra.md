---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T00:00:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# Residue of the dispersive-coefficient normalization pass

## Summary

**1 MAJOR, 2 REQUIRED.** The dispersive coefficient `c₁` in `δ_disp = −c₁D²` is now
declared once (`constants.EFT_PARAMS['DISPERSIVE_C1']` → `formulas.DISPERSIVE_C1`),
carries a `PARAMETER_PROVENANCE` record stating that it is a project normalization
rather than a derived constant, and is imported rather than retyped by every consumer
including `papers/E1/tables.py`. The duplicate `dispersive_hawking_correction` that
hardcoded `c₁ = 1.0` now delegates to the canonical evaluator. E1, E2 and D1 state the
coefficient's standing instead of printing `π/6` bare, and no downstream number moved.

Three items found in the course of that pass need code beyond its scope.

The MAJOR is not a consequence of the normalization work — it predates it and would
have been wrong at any value of `c₁`. It is the same ratio-versus-shift confusion that
produced the duplicate function in the first place, surviving in a notebook.

---

### 1.1 — 🔴 MAJOR — `Phase5d_Polariton_Technical.ipynb` adds 1 to a quantity that is already `1 + δ_disp`, inflating every polariton `T_eff` by ~1.8×

- **Severity:** major
- **Lane:** `pyrust`
- **Verify:** `cd "$REPO" && uv run python -c "import json; nb=json.load(open('notebooks/Phase5d_Polariton_Technical.ipynb')); src=''.join(''.join(c.get('source',[])) for c in nb['cells']); assert 'T_H * (1 + correction)' not in src, 'notebook still adds 1 to the kappa_eff/kappa RATIO returned by dispersive_hawking_correction'"`
  *What it asserts:* that the notebook no longer treats `dispersive_hawking_correction`'s
  return value — which is `κ_eff/κ = 1 + δ_disp`, not `δ_disp` — as a fractional shift.
  Renaming the local variable would not pass; only changing the arithmetic (to
  `dispersive_correction(D)`, which does return `δ_disp`) or the call would. Exits 1 at HEAD.
- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase5d_Polariton_Technical.ipynb`, code cell 10:
  `correction = dispersive_hawking_correction(D)` then `T_eff = T_H * (1 + correction)`.
- **Observed:** `dispersive_hawking_correction` returns the RATIO `κ_eff/κ = 1 + δ_disp`
  (0.815 at the LKB `D = 0.595`). The cell adds 1 to it, so the reported `T_eff` is
  `T_H × 1.815` — a horizon that radiates *hotter* than the undispersed one, from a
  correction that is negative by construction (`KappaScaling.dispersive_neg`).
- **Evidence:** The two functions differ by exactly this offset: `dispersive_correction(D)`
  returns `δ_disp = −0.185`, `dispersive_hawking_correction(D)` returns `1 + δ_disp = 0.815`.
  The correct factor is `1 + δ_disp = 0.815`; the cell computes `1.815`. The error is
  independent of `c₁` — it was present when `c₁` was 1.0 (stored output
  `correction = 0.9100, T_eff = 116.1 mK`, i.e. `T_H × 1.91`) and would be present at any
  value. ⚠️ Note the stored outputs are stale on two further counts: they show
  `D = 0.300` for every platform where the current `POLARITON_PLATFORMS` gives `D = 0.595`
  (pre-dating the reservoir-corrected `c_s`), and they were computed at the removed
  `c₁ = 1.0`.
- **Expected:** `T_eff = T_H * dispersive_hawking_correction(D)`, or
  `T_eff = T_H * (1 + dispersive_correction(D))`. Either is one call; mixing them is what
  fails.
- **Fix:** Correct the arithmetic in cell 10, correct the cell-9 markdown ("$D \approx 0.3$
  gives ~10% correction" — the current `D` is 0.595 and the correction is 18.5%), and
  re-execute the notebook so the stored outputs match the current constants. The
  `notebooks` and `viz_consistency` checks both pass at HEAD because they verify that
  physics is IMPORTED rather than re-implemented; neither re-executes a cell or reads a
  stored output, so no gate sees this.
- **Cache:** N/A.

---

### 2.1 — 🟡 REQUIRED — The "PRD 89, 124004" misprint for Coutant–Parentani 2014 was corrected in one file in 2026-04 and left live in two others

- **Severity:** required
- **Lane:** `research`
- **Verify:** `cd "$REPO" && uv run python -c "import pathlib,re; bad=[f'{p}:{s.count(chr(10),0,m.start())+1}' for p in pathlib.Path('lean').rglob('*.lean') for s in [p.read_text()] for m in re.finditer('124004', s) if 'earlier draft' not in s[max(0,m.start()-220):m.start()]]; assert not bad, f'PRD 89, 124004 asserted as the reference (not annotated as the known misprint) at: {bad}'"`
  *What it asserts:* that every surviving occurrence of the wrong volume/page is one that
  explicitly names it as an earlier draft's misprint, rather than one using it as the
  reference. It sweeps all of `lean/` rather than a hand-listed pair, so a third site
  cannot hide; and it does not merely test for the string's absence, which the existing
  deliberate `N.B.` annotation would have made unsatisfiable. Exits 1 at HEAD.
- **Gate:** CitationIntegrity
- **Location:** `lean/SKEFTHawking/WKBAnalysis.lean:175` (proof docstring, "see
  Coutant-Parentani PRD 89, 124004 (2014)"). Corrected during this pass:
  `HawkingUniversality.lean:54` and `papers/D1/paper_draft.tex:561`.
- **Observed:** `WKBAnalysis.lean:61` carries an explicit `N.B.` recording that an earlier
  draft cited "PRD 89, 124004 (2014)", that this is "a Kerr-Newman-NUT paper unrelated to
  analog Hawking", and that it was "corrected 2026-04-25". Line 175 of the same file still
  cites PRD 89, 124004.
- **Evidence:** Independently re-established 2026-08-15 by a `research-scout` sweep, which
  could locate no Coutant–Parentani paper at PRD 89, 124004 and identified the
  broadened-horizon paper as **PRD 90, 121501(R) (2014), arXiv:1402.2514**. That matches
  the `N.B.` already in the file. `papers/paper1_first_order` and `papers/paper2_second_order`
  already carry the correct bibitem.
- **Expected:** One reference for one paper, repo-wide.
- **Fix:** Correct `WKBAnalysis.lean:175`. The remaining fix is a docstring, so the
  statements and proofs are untouched; sweep for any further occurrence at the same time.
- **Cache:** `CorleyJacobson1996.pdf` and `CoutantParentani2012.pdf` are cached under
  `Lit-Search/Phase-4/primary-sources/`. **arXiv:1402.2514 is NOT cached** — it is now
  cited by D1 and E1 and should be acquired.

---

### 2.2 — 🟡 REQUIRED — Two named literature results are now cited by the substrate and by three manuscripts with no primary-source cache

- **Severity:** required
- **Lane:** `research`
- **Verify:** `cd "$REPO" && uv run python -c "from src.core.workspace import find_workspace; import pathlib; base=find_workspace()/'Lit-Search'; hits=[p.name for p in base.rglob('primary-sources/*') if 'CoutantWeinfurtner' in p.name or '1402.2514' in p.name or 'CoutantParentani2014' in p.name]; assert hits, 'neither Coutant-Weinfurtner 2017 nor Coutant-Parentani 2014 (arXiv:1402.2514) is cached, yet both now back the dispersive normalization'"`
  *What it asserts:* that the two sources the dispersive coefficient's standing now rests on
  are locally cached rather than cited from a secondary summary. Exits 1 at HEAD.
- **Gate:** CitationIntegrity
- **Location:** `PARAMETER_PROVENANCE['EFT.DISPERSIVE_C1']`,
  `src/core/formulas.dispersive_correction`, `lean/SKEFTHawking/KappaScaling.lean`
  (`dispersiveCorrection` docstring), `papers/E1/paper_draft.tex` §II,
  `papers/E2/paper_draft.tex` §, `papers/D1/paper_draft.tex` §eft-disp.
- **Observed:** The claim that the `D²` SCALING is established rests on **Coutant &
  Weinfurtner (PRD 2017)**, which is known to this repository only through the Tier-1
  deep-research summary `Lit-Search/Phase-1-and-Background/Tier-1/EFT corrections to
  acoustic Hawking radiation in BEC analog gravity.md` — a secondary source. The claim
  that the correction VANISHES for a locally linear profile rests on **Coutant & Parentani,
  arXiv:1402.2514**, verified by the `research-scout` at equation level but not cached here.
- **Evidence:** `find Lit-Search -iname "*Weinfurtner*"` returns nothing; the only Coutant
  file on disk is `CoutantParentani2012.pdf` (arXiv:1108.1821), which is a different paper.
  ADR-014 governs what a fetched source may back.
- **Expected:** Both cached under `Lit-Search/Phase-*/primary-sources/` with
  `CITATION_REGISTRY` entries, and the `Coutant2014` registry stub (currently
  `volume: 90, page: None, doi: None, arxiv: None`, auto-generated from a bibitem) completed.
- **Fix:** Acquire both, then verify at page level that Coutant & Weinfurtner's stated
  scaling is `O(ξ²κ²/c_s²)` for the effective TEMPERATURE (the summary's wording) and not
  for a different observable — the deep-research file is the only thing asserting that
  today, and it is the load-bearing half of the provenance record. Until then the
  normalization's *scaling* half is backed by a secondary source, which the provenance
  entry should say explicitly if acquisition is deferred.
- **Cache:** none — that is the finding.
