---
paper: paper27_bh_thermodynamics_four_laws
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-27T00:30:00Z
review_kind: re-invocation-3
prior_review: papers/AutomatedReviews/2026-04-26-2330-internal-adversarial-reinvocation/paper27_bh_thermodynamics_four_laws.md
prior_review_round_1: papers/AutomatedReviews/2026-04-26-2300-internal-adversarial/paper27_bh_thermodynamics_four_laws.md
readiness_gates_version: 1
---

# Adversarial Re-invocation 3 — paper27_bh_thermodynamics_four_laws

## Summary

Stage 13 third pass after the follow-up mechanical-fixes pass that
addressed the 3 NEW findings from the prior re-invocation. Of the 3
items the fix-pass targeted: 2 close cleanly (Procopio author drift
across all 5 sites; `thirdLaw_Israel_BPS_conditional` reference
rewritten as deferred-encoding disclosure). The third item (NEW
REQUIRED 5.4 — `M_c` parameter list inconsistency) **partially
closes** — 2 of 3 prose sites were fixed but the §novelty site
(now line 529) was missed by the global replace because line numbers
shifted after the §7 rewrite.

The PARTIAL 3.5 item **closes** cleanly: the old tautological
`wave3_bridge_weak_nernst_holds_strong_nernst_violated` is fully
retired; only an inline comment retains the historical note.

**Fresh 8-class sweep surfaces 1 NEW finding** (Lean docstring
drift at line 591 of `BHThermodynamicsFourLaws.lean`: the
`four_laws_consistent_with_acoustic_regime` docstring still asserts
`FourLaws_ADWExtremality` "asserts five independent physical laws"
but the post-strengthened bundle has only 3 substantive fields).

LaTeX build clean (6 pages, 396 KB, 0 errors); 13 bibitems / 11
cite-keys all in CITATION_REGISTRY; 2 unused bibitems
(`Volovik2003BraneBH`, `HawkingHorowitzRoss1995`) carried forward
unchanged from prior rounds (warnings only). Lean module: 20
substantive theorems / 0 sorry / 0 new axioms (matches
`\bhThermoTotal{20}` in `docs/counts.tex`). `_wave5_module_summary_marker`
is a `True := trivial` placeholder (counted in `\placeholdertheorems`,
not `\bhThermoTotal`).

**Verdict: NOT submission-ready.** Two findings remain:
- 🟡 REQUIRED 5.4-residual — §novelty `\Mc(\aADW, \Ladw, \Nf, \xivest)`
  parameter list still has the dangling `\xivest` (line 529).
- 🔵 RECOMMENDED 5.5-NEW — Lean module line 591 docstring claim
  "five independent physical laws" stale post-strengthening.

Both are mechanical fixes (1 deletion, 1 word swap). After they
land, paper27 is submission-ready pending the 5.4 carry-forward
RECOMMENDED on the unused bibitems and the unchanged 6.1 / 3.6
items from earlier rounds (none submission-blocking).

## Re-verification of NEW findings from prior re-invocation

### NEW BLOCKER 1.6 — Procopio author drift (5 sites) → CLOSED

- **Verification:**
  - `grep -n "Procopio" paper_draft.tex BHThermodynamicsFourLaws.lean
    citations.py` returns **zero matches**.
  - Line 39-41 (abstract) now reads "Balbinot, Fagnocchi, Fabbri (PRD~71,
    064019 (2005), arXiv:gr-qc/0405098..." — 3 authors, no Procopio.
  - Line 80 (intro) now reads "Balbinot, Fagnocchi, Fabbri" — 3 authors.
  - Line 199 (§3.2) now reads "Balbinot, Fagnocchi, Fabbri" — 3 authors.
  - `BHThermodynamicsFourLaws.lean:22` now reads
    "Balbinot–Fagnocchi–Fabbri,".
  - `BHThermodynamicsFourLaws.lean:119` now reads "**R. Balbinot, S.
    Fagnocchi, A. Fabbri**".
  - `citations.py:2501` registry entry: `'authors': 'Balbinot, R. and
    Fagnocchi, S. and Fabbri, A.'` (3 authors, `'doi_verified': True`).
- **Status:** CLOSED. All 5 prose sites now consistent with bibitem +
  registry.

### NEW BLOCKER 5.3 — Stale `thirdLaw_Israel_BPS_conditional` reference → CLOSED

- **Verification:**
  - `grep "thirdLaw_Israel_BPS_conditional" paper_draft.tex` returns
    **zero matches**.
  - Paper §7 (lines 384-413) now reads:
    "The third-law content (a quantitative claim about the
    affine-time approach) is *not* encoded as a Lean Prop in the
    post-Stage-13 strengthened module: the original Wave 5
    `thirdLaw_Israel_BPS_conditional` field was a `True` placeholder,
    and the strengthening pass removed all `True`-typed fields rather
    than ship vacuous content. Encoding the Israel form quantitatively
    requires affine-time integral formalism from Phase 6f.5
    (`ADMDecomposition.lean`); the substantive content of this
    section is the (uncoded) *prose-level* disclosure..."
  - The prose now matches the Lean reality (`FourLaws_ADWExtremality`
    has only 3 fields, no `thirdLaw_*`); explicit deferral
    disclosure is consistent with the Lean docstring at lines 559-567.
- **Status:** CLOSED. Paper §7 prose-level disclosure aligned with
  Lean-side deferred-encoding strategy.

### NEW REQUIRED 5.4 — `M_c` parameter list inconsistency → PARTIALLY CLOSED

- **Verification:**
  - `grep -n "Mc(\\\\aADW" paper_draft.tex` returns 6 matches; 5 of 6
    use the correct 3-arg form `\Mc(\aADW, \Ladw, \Nf)`:
    - line 34 (abstract setup)
    - line 58 (abstract closing) — was 4-arg in prior review, now 3-arg
    - line 105 (intro) — was 4-arg in prior review, now 3-arg
    - line 157 (eq:Mc-default)
    - line 557 (conclusion)
  - **One remaining 4-arg site:** `paper_draft.tex:529` (§novelty)
    still reads `\Mc(\aADW, \Ladw, \Nf, \xivest) = (\Nf \Ladw) /
    (12\pi \aADW)`. The mechanical fix-pass missed this because line
    numbers shifted from the §7 rewrite (the prior review flagged
    "line 511" which corresponded to this same prose; the line
    became 529 after §7 expansion).
  - The prior review's "line 511" → "line 529" drift confirms the
    fix-pass operated on a stale line list (3 line numbers from the
    prior review: 58, 105, 511 — the first two were correct in the
    new state, the third drifted).
- **Status:** PARTIALLY CLOSED → STILL OPEN (REQUIRED). See finding
  5.4-residual below.

### Original PARTIAL 3.5 — old tautological `wave3_bridge_weak_nernst_holds_strong_nernst_violated` → CLOSED

- **Verification:**
  - `grep -n "wave3_bridge_weak_nernst_holds_strong_nernst_violated"
    BHThermodynamicsFourLaws.lean` returns 1 match — but at line 766,
    inside a comment:
    ```
    -- Note: the previous tautological theorem
    -- `wave3_bridge_weak_nernst_holds_strong_nernst_violated` was retired
    -- in the post-Stage-13 strengthening pass. The substantive content
    -- (weak Nernst preserved, strong Nernst violated for the BEC-acoustic
    -- regime at the asymptotic-extremality limit) is now encoded by
    -- `wave3_bridge_kaul_majumdar_at_e_squared_anchor` above, which
    -- actually imports `SKEFTHawking.BHEntropyMicroscopic` and calls
    -- `kaulMajumdarS` at the SU(2)_k anchor area.
    ```
  - The `theorem` keyword is gone; only the inline comment retains
    the historical note. The substantive
    `wave3_bridge_kaul_majumdar_at_e_squared_anchor` (line 756) is
    the sole load-bearing Wave 3 bridge.
  - Paper-side §10 prose at lines 516-521 correctly explains:
    "The previous generic-positivity-propagation theorem
    `wave3_bridge_weak_nernst_holds_strong_nernst_violated` was a
    tautology repackaging its input hypothesis and was retired in
    the post-Stage-13 strengthening pass; the concrete-anchor bridge
    above is the load-bearing weak-Nernst/strong-Nernst encoding."
- **Status:** CLOSED. Tautology retired entirely; paper-prose drift
  hazard discharged.

## Re-verification of carry-forward findings (unchanged)

### 1.1, 1.2, 1.3, 1.4, 1.5 — CLOSED (re-verified)

- All 5 citation-integrity findings from the original Stage 13 review
  remain CLOSED.
- 13 bibitems present, 11 unique `\cite{}` keys, all 11 present in
  `CITATION_REGISTRY`. `Balbinot2005PRD` author list matches
  registry (3 authors). Reall + Kirklin titles + venues verbatim from
  prior re-invocation. `StrengtheningPost2026` removal stable.
  `GloriosoLiu2018` + `CrossleyGloriosoLiu2017` `doi_verified: True`
  + `paper27 in used_in` confirmed.

### 3.1, 3.2, 3.3, 3.4, 3.7 — CLOSED (re-verified)

- `ADWSecondLaw` substantive (2 fields, no `True`).
- `FourLaws_Schwarzschild` + `FourLaws_ADWExtremality` each ship 3
  substantive fields (lines 537-541, 569-575).
- Both falsifier theorems (`falsifier_acoustic_decay_form`,
  `falsifier_schwarzschild_heating`) substantive.
- `falsifier_third_law_form` substantive (genuine min-argument
  contradiction).
- `falsifier_alpha_ADW_dependence` rename stable.

### 4.1, 4.2 — CLOSED (re-verified)

- `BH_THERMODYNAMICS_PARAMS` no Schottky residue.
- Stale figure removed; only `fig_T_H_evolution_regime_partition.png`
  in `figures/`.

### 5.2 — CLOSED (re-verified)

- Paper line 485-490 §sec:lean now reads "three substantive sign
  claims plus two deferred placeholder fields" — 5-field overclaim
  removed. The paper's separate "five fields" mentions at lines 265,
  288 correctly refer to `H_RegimePartition` (which has exactly 5
  substantive fields, all non-`True`); not to `FourLaws_*`.

### 6.1 (RECOMMENDED, unchanged) — `H_RegimePartition.M_c_form_consistent` field trivially provable
### 3.6 (RECOMMENDED, unchanged) — `wave1_bridge_G_N_emerg_pos` is a 1-line wrapper around `G_N_emerg_eval_pos`
### 5.1 (PASS, unchanged) — Project-original disclosures adequate
### 7.1 (PASS, unchanged) — `\bhThermoTotal{20}` matches Lean theorem count exactly
### 7.2 (PASS, unchanged) — No tables in paper27
### 8.1 (PASS, unchanged) — No production runs claimed

## NEW Findings (introduced or surfaced by the fix-pass)

### 5.4-residual — 🟡 REQUIRED — `\Mc` parameter list still 4-arg in §novelty (line 529)

- **Gate:** NarrativeGrounding (paper-Lean drift) + internal-consistency
- **Location:** `papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex:529`
- **Observed:**
  ```
  \item The ADW-substrate-specific critical mass
    $\Mc(\aADW, \Ladw, \Nf, \xivest) = (\Nf \Ladw) / (12\pi \aADW)$
    ansatz is project-original.
  ```
  The 4-arg parameter list `\Mc(\aADW, \Ladw, \Nf, \xivest)` is
  inconsistent with: (a) the formula `(\Nf \Ladw)/(12\pi \aADW)`
  on the same line, which has no `\xivest` dependence; (b) the Lean
  definition at `BHThermodynamicsFourLaws.lean:243-244`:
  `noncomputable def M_c (p : ADWParams) : ℝ := p.N_f * p.Λ_UV /
  (12 * Real.pi * p.α_ADW)` — uses 3 of 4 ADWParams fields, NOT
  `χ_vest`; (c) the 5 other paper sites that correctly write the
  3-arg form (lines 34, 58, 105, 157, 557).
- **Evidence:** `grep -n "Mc(\\\\aADW" paper_draft.tex` shows 6 hits,
  5 of which use the 3-arg `(\aADW, \Ladw, \Nf)` form. Line 529 is
  the lone 4-arg outlier.
- **Expected:** §novelty line 529 should match the 5 other sites and
  the Lean definition: `\Mc(\aADW, \Ladw, \Nf) = (\Nf \Ladw) /
  (12\pi \aADW)`.
- **Fix:** Mechanical 1-token deletion at line 529 — strip `, \xivest`:
  ```
  $\Mc(\aADW, \Ladw, \Nf) = (\Nf \Ladw) / (12\pi \aADW)$
  ```
- **Why the fix-pass missed it:** The prior re-invocation cited the
  4-arg sites by line number (58, 105, 511). After the §7 rewrite
  expanded the third-law disclosure (lines 396-413), all subsequent
  line numbers shifted by ~18 lines. Line 511 (the §novelty site)
  became line 529. The fix-pass operated on the stale prior-review
  line list and missed the shifted §novelty site.
- **Cache:** N/A (Lean source compare).
- **Severity rationale:** REQUIRED. The §novelty section is one of
  the most-read sections by reviewers (the project-original
  contributions are flagged here); a parameter-list inconsistency
  in the explicit "this is what we contribute" claim is more
  high-visibility than mid-paper drift. Internal-inconsistency
  remains (3-arg vs 4-arg coexist within the same paper).

### 5.5-NEW — 🔵 RECOMMENDED — Lean module line 591 docstring stale: "FourLaws_ADWExtremality bundle asserts five independent physical laws"

- **Gate:** LeanProofSubstance (docstring drift, advisory)
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:589-593`
- **Observed:**
  ```
  Both conjuncts are non-trivial: the `FourLaws_ADWExtremality` bundle
  asserts five independent physical laws, and `dT_H/dt < 0` is the
  regime-defining sign-inversion claim primary-source-grounded by
  Balbinot 2005 Eq. Tsonic.
  ```
  This docstring on `four_laws_consistent_with_acoustic_regime`
  (theorem at line 595) still describes the **pre-strengthening**
  `FourLaws_ADWExtremality` shape (5 fields). The post-strengthened
  bundle at lines 569-575 has only 3 substantive fields:
  `firstLaw_smarr_with_substrate`, `secondLaw_ADWExt`,
  `evap_dT_dt_negative`.
- **Evidence:**
  - `grep -n "five independent\|five mutually" BHThermodynamicsFourLaws.lean`
    shows line 591 as the lone hit.
  - Anti-pattern audit at lines 103-109 correctly says "**three
    substantive fields each** (firstLaw + secondLaw + evap_dT_dt
    sign), all mutually independent" — internally inconsistent with
    line 591 within the same module.
- **Expected:** Update line 591 to match the strengthened bundle:
  ```
  Both conjuncts are non-trivial: the `FourLaws_ADWExtremality` bundle
  asserts three independent substantive sign claims (firstLaw +
  secondLaw + evap_dT_dt sign — see §8 for the deferred
  zerothLaw/thirdLaw infrastructure dependencies), and `dT_H/dt < 0`
  is the regime-defining sign-inversion claim primary-source-grounded
  by Balbinot 2005 Eq. Tsonic.
  ```
- **Fix:** Mechanical edit — replace "five independent physical
  laws" with "three independent substantive sign claims" at line 591.
- **Cache:** N/A (Lean source).
- **Severity rationale:** RECOMMENDED rather than BLOCKER/REQUIRED
  because (a) it's a docstring, not a Prop or formal claim — no
  reader will mistake it for a load-bearing theorem statement;
  (b) the surrounding documentation (anti-pattern audit at lines
  103-109, per-bundle docstring at 547-557, paper §sec:lean prose)
  all correctly describe the 3-field shape, so a reader has multiple
  consistent sources to cross-reference. But it's the kind of
  internal-inconsistency that erodes trust: a fresh reader scanning
  for "five fields" gets two different stories from the same module.

## QI Candidates (carried forward + new)

The prior re-invocation surfaced 4 QI candidates. The third pass
adds two more, both about the **line-number-drift** failure mode
that propagated 5.4-residual:

1. (Carried) `validate.py --check cross_wave_bridge_imports` —
   automated detection of phantom Wave-N bridges. Still valid.
2. (Carried) PlaceholderMarker extraction over `Prop`-typed `True`
   fields. Still valid.
3. (Carried) `validate.py --check paper_lean_ident_resolve` — would
   have caught 5.3. Still valid.
4. (Carried) `validate.py --check paper_author_consistency` — would
   have caught 1.6. Still valid.
5. **NEW: `validate.py --check paper_lean_param_list_consistency`** —
   for every `\Mc(...)`, `\GN(...)`, etc. macro in paper prose, check
   that the parameter list matches the corresponding Lean
   definition's argument count + ordering. Would have caught
   5.4-residual automatically; would also catch the original
   abstract+intro 4-arg sites in one shot rather than relying on
   manual line-listing.
6. **NEW: line-number-drift mitigation in fix-pass workflow.** The
   mechanical-fix-pass's reliance on line numbers from the prior
   review is fragile under intervening rewrites (the §7 rewrite of
   BLOCKER 5.3 shifted all subsequent line numbers by ~18). Fix-passes
   that target multi-site issues should re-scan with a regex/pattern
   match (e.g., `Mc.*xivest`) rather than apply edits at fixed line
   numbers. Pipeline addition: a "fix-pass verification step" that
   re-greps for the original symptom pattern after the edits land
   would have caught the §novelty miss before this re-invocation.

## Final remediation list

To reach submission-ready state, **2 mechanical edits** must land:

1. **REQUIRED 5.4-residual** — `paper_draft.tex:529`: strip
   `, \xivest` from `\Mc(\aADW, \Ladw, \Nf, \xivest)` →
   `\Mc(\aADW, \Ladw, \Nf)`.
2. **RECOMMENDED 5.5-NEW** (advisory, not submission-blocking) —
   `BHThermodynamicsFourLaws.lean:591`: replace
   "five independent physical laws" → "three independent substantive
   sign claims".

After 5.4-residual lands, paper27 has zero BLOCKER and zero REQUIRED
findings; submission gates 1, 5, 6, 7 pass; the paper is
**submission-ready**. 5.5-NEW is RECOMMENDED-only (docstring
hygiene) and does not block submission, though it should be cleaned
up alongside any future Lean module refactor for module-internal
consistency.

The prior round's RECOMMENDED 6.1 (`H_RegimePartition.M_c_form_consistent`
trivially provable) and 3.6 (`wave1_bridge_G_N_emerg_pos` 1-line
wrapper) remain UNCHANGED — both RECOMMENDED, neither submission-blocking.
The 2 unused bibitems (`Volovik2003BraneBH`, `HawkingHorowitzRoss1995`)
remain UNCHANGED carry-forward — produce LaTeX warnings only.
