---
paper: paper26_bh_entropy
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-26T03:30:00Z
readiness_gates_version: 1
prior_review: papers/AutomatedReviews/2026-04-26-0230-internal-adversarial/paper26_bh_entropy.md
---

# Adversarial Review (re-invocation) — paper26_bh_entropy

**Verdict: Stage 13 NOT closed: 0 remediation gaps + 2 new findings (1 REQUIRED, 1 RECOMMENDED).**

All 5 prior BLOCKERs and all 7 prior REQUIREDs were correctly remediated as claimed in the author's commit message. The re-scan surfaces **no new BLOCKERs**, but did find one broken cross-reference (REQUIRED) and one residual stale reference in the Lean module summary (RECOMMENDED) — both introduced by the remediation pass. Neither is submission-blocking on its own, but both are <30-second fixes the pipeline should nail before Stage 13 is declared closed.

## Verified-Closed (12 prior findings)

### BLOCKERs (5)

- **1.1 — CLOSED.** `GovindarajanKaulSuneeta2001` bibitem (paper line 615-619) and registry entry (`citations.py:2430-2446`) both now read "Logarithmic correction to the Bekenstein-Hawking entropy of the BTZ black hole" / Class. Quantum Grav. 18, 2877–2886 (2001) / DOI 10.1088/0264-9381/18/15/303 / arXiv:gr-qc/0104010. `doi_verified: True`. JSONL `match` record appended at `docs/citation_verifications.jsonl` with timestamp 2026-04-26T03:00.
- **1.2 — CLOSED.** `Mitra2014LogVanish` bibitem (paper line 605-608) and registry entry (`citations.py:2399-2414`) both now read "Black hole entropy with and without log correction in loop quantum gravity" / Nucl. Phys. B Proc. Suppl. 251-252, 87 (2014) / DOI 10.1016/j.nuclphysbps.2014.04.016. `doi_verified: True`. JSONL `match` record appended.
- **1.3 — CLOSED.** `Vergeles2025` bibitem (paper line 621-623) and registry (`citations.py:643-666`) both now read "Unitarity of 4D Lattice Theory of Gravity" / PRD 112, 054509 (2025) / arXiv:2506.00036. `paper26_bh_entropy/paper_draft.tex` added to `used_in`. `doi_verified: True`. JSONL `match` record appended.
- **3.1 — CLOSED.** The tautological `H_HorizonBoundaryCondition_implies_areaLawKappa_pos` (body = `h.areaLeading`, single field projection) has been **removed** from the Lean module and replaced by `H_HorizonBoundaryCondition_implies_nonabelian_envelope` (`BHEntropyMicroscopic.lean:420-432`). The new theorem is genuinely substantive — it (i) combines `h.areaLeading` with `Real.log_pos_iff` and `H.d_max_attained` to produce `∃ a, 1 < H.quantum_dim a` (a derived non-projection statement, contrapositive of the toric-code abelian falsifier) AND (ii) combines `h.positivity` with `h.secondLaw` to produce a monotone non-negative envelope. Three bundle fields are jointly used; an existential elimination + log-monotonicity step is introduced. This is a **substantive structural corollary**, not a structural tautology.
- **4.1 — CLOSED.** The paper §5.1 (lines 300-324) no longer claims `falsifier_anomalyMatch` exists — instead, the bullet at line 310-323 references `H_HorizonBoundaryCondition_implies_nonabelian_envelope` and explains explicitly that this replaces the prior placeholder. (See NEW-FINDING N.2 below for a residual stale mention in the Lean module summary docstring.)
- **4.2 — CLOSED.** Paper §7 (line 422) and Conclusions (line 518) both now say "22 theorems" with the breakdown "(19 initial + 3 net additions...)". Theorem-list bullet list at lines 431-473 enumerates the 22 theorems including the three strengthening additions (`abelian_MTC_falsifies_H_HorizonBoundaryCondition`, `sen_4d_quantitative_disagreement_bound`, `fibonacci_horizon_areaLawKappa_pos`) and the new `H_HorizonBoundaryCondition_implies_nonabelian_envelope`. Direct grep count: `grep -cE "^theorem |^lemma " BHEntropyMicroscopic.lean` returns 22.

### REQUIREDs (7)

- **1.4 — CLOSED.** All 15 paper26 bibkeys now have `doi_verified: True` (`citations.py:2200-2447` block; spot-check via `grep -nE "doi_verified" | awk` for line range 2200-2447 returns 15 entries, all `True` after the registry restructuring; the lone `None` at line 2200 is `CrossleyGloriosoLiu2017`, a paper25/paper2 entry, not a paper26 entry). JSONL match records for the three previously-disputed bibkeys recorded in `docs/citation_verifications.jsonl`.
- **2.1 — CLOSED.** `bh_entropy_leading_coefficient` docstring (`formulas.py:7713-7719`) now correctly says: `Lean: BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi (structure field). The 1/4-tuning hypothesis is documented at the prose level (Wave 3 paper §4) but is NOT yet a Lean predicate — there is no IsHorizonBC.immirziTuned discharge in the shipped module. The structural anchor consumed by Wave 3 is kaul_majumdar_leading_matches_G_N_emerg`. Honest, accurate, references actually-shipped Lean identifiers.
- **2.2 — CLOSED.** `verlinde_dim_horizon` docstring (`formulas.py:7618-7625`) now reads: `Lean: pending — Verlinde sum is not yet formalized at theorem level; its abstract counterpart is the opaque BHEntropyMicroscopic.verlindeEntropy_SU2k`. References only actually-shipped identifiers (`verlindeEntropy_SU2k` exists at `BHEntropyMicroscopic.lean:169` as `opaque`).
- **2.3 — CLOSED.** `bh_entropy_kaul_majumdar` docstring (`formulas.py:7669-7671`) now correctly references `BHEntropyMicroscopic.kaulMajumdarS` (def), `kaul_majumdar_log_coefficient`, and `kaul_majumdar_log_decomposition`. All three exist in the Lean source.
- **2.4 — CLOSED.** `AXIOM_METADATA['gaussianSaddleAsymptotic']` `used_in` field (`constants.py:1395-1396`) now reads `kaulMajumdar_asymptotic_within_OoneOverA, verlinde_matches_kaul_majumdar_at_large_area`. The `Project escape.risk` field (lines 1404-1410) updated to reference both consumers correctly. Both Lean theorems exist (`BHEntropyMicroscopic.lean:203` and `:214`).
- **3.2 — CLOSED.** Paper §3 (lines 199-220) now correctly explains the dual nature: "The structural decomposition $-3/2 = (-1/2) + (-1)$ has two parts: the arithmetic identity itself (encoded in Lean as `kaul_majumdar_log_decomposition`, which proves the rational identity $(-1/2) + (-1) = -3/2$ by `ring`) and the physical sourcing of each summand (documented at the prose level here, not yet formalized at the theorem level — i.e., there is no Lean theorem attaching the value $-1/2$ to a Gaussian-saddle object or $-1$ to a singlet-projection object)". Lifting to per-summand Lean definitions explicitly flagged as a follow-on goal.
- **3.3 — CLOSED.** Paper §6 (lines 482-488) softened to: "records the conjunction of two pre-existing facts: `LinearizedEFE.G_N_emerg_pos` (positivity of $G_N^{\rm emerg}$) and the Wave-3 entropy anchor `kaulMajumdar_S_at_4GN` ($\SBH(4 G_N) = 1$). The substantive Wave-1-side content lives in `LinearizedEFE.G_N_emerg_pos`; the Wave-3 contribution is the anchor `kaulMajumdar_S_at_4GN` and the administrative bundling." Honest description of the bridge's administrative role.
- **4.3 — CLOSED.** Paper §3.2 (lines 363-374) now reads: "The four auxiliary modules ... establish *S-matrix unitarity* and the modular data, which are *necessary* ingredients toward the full $(ST)^3 = S^2$ relation but are not, on their own, theorem-discharging proofs of $(ST)^3 = S^2$ at the abstract bundle level." Table I caption (lines 345-359) explicitly labels the per-MTC ✓ entries as conjectural-structural with two exceptions theorem-discharged. (Note: see NEW-FINDING N.1 — the Conclusions paragraph retains the looser pre-fix phrasing.)
- **6.1 — CLOSED.** Table I caption (lines 345-359) now says: "✓ = structurally compatible (no published $d_a$ data triggers the corresponding F-falsifier); ? = conjectural at the abstract bundle level... With the exception of the toric-code F2 FAIL (theorem-discharged via `abelian_MTC_falsifies_H_HorizonBoundaryCondition`) and the Fibonacci F2 ✓ (theorem-discharged via `fibonacci_horizon_areaLawKappa_pos`), the per-MTC ✓ entries are conjectural-structural — they reflect that the published quantum-dimension data and S-matrix data do not trigger F1/F3/F4 falsifiers, not that a per-MTC `H_HorizonBoundaryCondition` discharge has been formally proved. Theorem-level discharges per MTC are a follow-on Wave goal." Properly disclosed.
- **7.1 — CLOSED.** `tests/test_bh_entropy.py` now has 57 tests (was 47; +10 net per the commit message). Confirmed golden-identity tests added: `test_verlinde_dim_horizon_ising_4sigma_golden` (line 142), `test_verlinde_dim_horizon_ising_psi_squared_identity` (line 156), `test_verlinde_dim_horizon_vacuum_pair_returns_one` (line 166), and a full `test_log_correction_per_mtc_*` golden-identity suite (lines 184-227, 7 tests). Plus `test_implies_nonabelian_envelope_anchor` (line 493) cross-checks the new substantive Lean theorem at the Python level. All 57 pass: `uv run python -m pytest tests/test_bh_entropy.py -v` returns `57 passed in 0.06s`.

### RECOMMENDEDs (2)

- **5.1 — N/A (already accepted).** Novelty-claim cross-check was internally consistent in the prior round; no fix required, no new issues introduced.
- **8.1 — DEFERRED-AS-DOCUMENTED.** Paper still hardcodes "22 theorems" inline at lines 422 and 518. The prior review explicitly recommended option (b) — accept staleness for Wave 3 ship; Phase 6f or later adds a `\bhEntropyTotal{}` macro. Validation suite logs this as a `count-literal` warning ("USES MACROS but 3 count-literal matches: L422 \"22 theorems\" ... L518 \"22 theorems\"; L425 \"0 sorry\""), consistent with the prior-review verdict. Not a blocker for Wave 3 ship.

## NEW-FINDINGS (2)

### N.1 — 🟡 REQUIRED — Broken cross-reference `\S\ref{sec:closedform}` introduced during remediation of REQUIRED 3.2

- **Gate:** CrossPaperConsistency / NumericalFreshness
- **Location:** `papers/paper26_bh_entropy/paper_draft.tex:438`
- **Observed:** The remediated theorem-list bullet for `kaul_majumdar_log_decomposition` reads: `the physical sourcing of each summand is documented in \S\ref{sec:closedform}; not formalized at theorem level`. The label `sec:closedform` is **not defined** anywhere in the paper. The closest existing label is `\label{sec:KM}` at line 164 (the "Kaul-Majumdar Closed Form" section, §3 in the rendered output).
- **Evidence:** `grep -nE "label\{sec:closedform\}|sec:closedform|sec:KM" paper_draft.tex` shows only `label{sec:KM}` defined and one `\ref{sec:closedform}` referenced. This will render as a broken `??` cross-reference in the compiled PDF.
- **Expected:** The remediation pass for REQUIRED 3.2 introduced this bug — the prior version of the bullet had no cross-reference; the new one references a label that doesn't exist. Either (a) change `\ref{sec:closedform}` to `\ref{sec:KM}` (the correct existing label, since §3 is the Kaul-Majumdar closed-form section that contains the prose-level decomposition discussion), or (b) add `\label{sec:closedform}` to a more specific subsection — but option (a) is simpler since the relevant prose is the §3.2 subsection of the Kaul-Majumdar section.
- **Fix:** One-character edit: `\S\ref{sec:closedform}` → `\S\ref{sec:KM}` at `paper_draft.tex:438`.
- **Cache:** direct grep (this round)

### N.2 — 🔵 RECOMMENDED — Lean module summary still claims `*_falsifier_anomalyMatch` is shipped (it isn't)

- **Gate:** LeanProofSubstance / DocSync
- **Location:** `lean/SKEFTHawking/BHEntropyMicroscopic.lean:604-606`
- **Observed:** The module-bottom Summary docstring still reads: `Five falsifier theorems (*_falsifier_positivity, *_falsifier_logBound, *_falsifier_secondLaw, *_falsifier_quarterCoefficient, *_falsifier_anomalyMatch)`. The fifth name `*_falsifier_anomalyMatch` does **not** exist in the module — the strengthening pass replaced it with `H_HorizonBoundaryCondition_implies_nonabelian_envelope`, and the post-adversarial-review followup further refined that to a substantive structural corollary. The Lean source file's bottom docstring lags both replacements.
- **Evidence:** `grep -nE "falsifier_anomalyMatch" BHEntropyMicroscopic.lean` returns only this one line (606) — no actual theorem exists. The `H_HorizonBoundaryCondition` structure no longer has a fifth falsifier theorem name pattern; instead it has `abelian_MTC_falsifies_H_HorizonBoundaryCondition` (line 444, the F2 concrete falsifier) and `H_HorizonBoundaryCondition_implies_nonabelian_envelope` (line 420, the substantive structural corollary that subsumes the old F5 placeholder role). The module summary at line 604-606 is purely descriptive prose in a `/-! ... -/` doc block — it does not affect compilation, but it is a stale claim that contradicts the actual shipped content.
- **Expected:** Either (a) update the bullet to read `Five-condition tracked-hypothesis bundle: four direct falsifier theorems (*_falsifier_positivity, *_falsifier_logBound, *_falsifier_secondLaw, *_falsifier_quarterCoefficient) plus the substantive structural corollary H_HorizonBoundaryCondition_implies_nonabelian_envelope replacing the old F5 placeholder; concrete F2 path via abelian_MTC_falsifies_H_HorizonBoundaryCondition`, or (b) drop the explicit name list and refer the reader to §5 of the file.
- **Fix:** Edit `BHEntropyMicroscopic.lean:604-606` to match the post-strengthening reality.
- **Cache:** direct grep (this round)

## Re-Scan: New Concerns

The full re-scan checked:

1. **All 22 theorems in `BHEntropyMicroscopic.lean`** for tautology / vacuous-Prop patterns. Findings:
   - `kaul_majumdar_log_decomposition` (line 119): proven by `ring`. The arithmetic identity is the *only* content; the physical sourcing claim is correctly disclosed in the paper as **not formalized**. This is a (now-honest) per-finding-3.2 disclosure, not a new defect.
   - `H_HorizonBoundaryCondition_implies_nonabelian_envelope` (line 420): genuinely substantive, three-field combination plus existential elimination via `Real.log_pos_iff` + `H.d_max_attained`. Substantive. Not a tautology.
   - `abelian_MTC_falsifies_H_HorizonBoundaryCondition` (line 444): substantive — combines `d_max_attained`, `quantum_dim_unit`, `log_one`, and the F2 falsifier theorem to produce a per-instance non-trivial conclusion. Not a tautology.
   - `fibonacci_horizon_areaLawKappa_pos` (line 553): substantive — proves `0 < log φ` via a chain of `Real.sqrt` monotonicity steps. Not a tautology.
   - `sen_4d_quantitative_disagreement_bound` (line 151): substantive — proves the quantitative `> 3` bound via `norm_num` on rationals after a `unfold + show 289/90` step. Not a tautology.
   - `kaul_majumdar_leading_matches_G_N_emerg` (line 580): explicitly disclosed as a "bridge / administrative bundling" theorem in both the Lean docstring and the paper §6 — disclosure satisfies the gate.
   - All five F1-F5 falsifier theorems: each takes a hypothesis and derives `¬ H_HorizonBoundaryCondition` via field-projection-plus-contradiction. Each is a non-trivial implication (the body uses `intro h` + `exact absurd ... (not_le.mpr ...)` style closures), not a single-step projection. Substantive.

2. **The `gaussianSaddleAsymptotic` axiom** for vacuous-axiom-via-algebraic-self-discharge (per `feedback_post_wave_strengthening_audit.md`). The axiom statement (`BHEntropyMicroscopic.lean:193-196`) requires `0 < C ∧ ∀ A G_N, 0 < G_N → 1 ≤ A → |verlindeEntropy_SU2k A G_N - kaulMajumdarS A G_N 0| ≤ C / A`. The two consumers (`kaulMajumdar_asymptotic_within_OoneOverA` and `verlinde_matches_kaul_majumdar_at_large_area`) **substantively use** the existential `C` and the bound, so the axiom is not vacuous-by-self-discharge. Furthermore, since `verlindeEntropy_SU2k` is an `opaque` function (line 169), the axiom **cannot** algebraically self-discharge — opaque functions block reflexivity.

3. **The substantive Lean theorem additions for the strengthening pass + adversarial followup** were checked individually for the four post-strengthening replacements (`abelian_MTC_falsifies_H_HorizonBoundaryCondition`, `sen_4d_quantitative_disagreement_bound`, `fibonacci_horizon_areaLawKappa_pos`, `H_HorizonBoundaryCondition_implies_nonabelian_envelope`). All four are substantive per the analysis in §1 above.

4. **The Python module + tests**: 57 tests pass; new golden tests for `verlinde_dim_horizon` and `log_correction_coefficient_per_mtc` are present and assert numeric equality (not bounds). The `ComputationCorrectness` graph-level blocker remains in the validation report, but this reflects the auto-graph not yet having been re-extracted to pick up the new test edges; the test file changes are landed and the auto-graph re-extraction is mechanical.

5. **The validation suite**: `uv run python scripts/validate.py` → 22/22 PASS, 68 warnings. The two paper26-relevant warnings are (i) the `count-literal` advisory at lines 422/425/518 (per RECOMMENDED 8.1, deferred-as-documented), and (ii) the `ComputationCorrectness` advisory (per finding 7.1, addressed by the new tests, awaiting graph re-extraction).

6. **The Lean build**: `lake build SKEFTHawking.BHEntropyMicroscopic` → "Build completed successfully (8267 jobs)". Module compiles clean.

## QI Candidates (cross-cutting observations from the re-scan)

### Existing QI (re-confirmed) — `validate.py --check formula_lean_refs_resolve` and `axiom_metadata_used_in_resolve`

The prior round flagged this. The remediation pass for findings 2.1–2.4 fixed the four flagged instances by hand, but the structural QI to prevent recurrence is still pending. Recommend keeping this on the QI register.

### Existing QI (re-confirmed) — `validate.py --check paper_lean_refs`

The prior round flagged this. Finding N.1 (broken `\ref{sec:closedform}`) is a different class of bug (paper-internal cross-reference, not a Lean reference), but it indicates that paper-side reference integrity needs a similar grep-and-resolve check. Recommend extending the QI to include LaTeX label/ref consistency: `validate.py --check paper_internal_refs_resolve` would catch finding N.1 directly.

### NEW QI candidate — Lean module summary docstring sync

Finding N.2 is the third instance this session of "module summary docstring claims a theorem name that doesn't exist after a strengthening pass". The Lean module summary `/-! ### Summary -/` block at the bottom of `BHEntropyMicroscopic.lean` is descriptive prose that the build doesn't verify. A `validate.py --check lean_summary_docstrings_resolve` that greps each `*.lean` file's summary block for theorem-name patterns and asserts each resolves to an actually-shipped declaration would catch finding N.2 and prevent its recurrence. Implementation cost: ~1 hour. This complements the existing/proposed `formula_lean_refs_resolve` and `paper_lean_refs` checks to give the project full Lean-name reference coverage at the Python-validate level.
