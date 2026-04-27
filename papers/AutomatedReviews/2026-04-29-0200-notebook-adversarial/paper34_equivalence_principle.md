---
paper: paper34_equivalence_principle
artifact: notebooks (Technical + Stakeholder)
reviewer: adversarial-reviewer (notebook adaptation, fresh context)
model: claude-opus-4-7-1m
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper34_equivalence_principle (notebooks)

## Summary

Fresh-context audit of the two paper34 notebooks (`Phase6c3_EquivalencePrinciple_Technical.ipynb`, `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb`) against the Lean module, paper draft, citation registry, and primary sources. **2 BLOCKERs, 2 REQUIREDs, 3 RECOMMENDEDs, 1 INFO.** Both BLOCKERs and one REQUIRED are localized to the **Stakeholder notebook**, which still claims **25** Lean theorems and `13 original + 12 strengthening` even after the upstream count was corrected to 24 (Lean module currently declares exactly 24 `theorem` decls; `\epThms = 24` in `docs/counts.tex`). The Stakeholder notebook also collapses the abstract's hedged "projected design sensitivity discussed for STEP-class satellite missions" into a bare promissory "AT the STEP target", and propagates the stale "25 theorems" pointer in §7. Citations all verified `match` against arXiv. The Technical notebook is structurally clean post-correction (count = 24, breakdown 12+12) but introduces one new accuracy issue: §3 prose says the strengthening pass "*added single-claim ... alongside the originals (the bundles still exist)*" — accurate — but the same cell labels the four `*_satisfies_all_EP` 3-conjunct theorems as "bundles ... still exist" without acknowledging that they are now **logically derivable** from the new `noViolation_implies_satisfiesAt` extraction lemma (P2 redundancy is structurally explicit, not eliminated). Minor exposition issue, not a blocker. The `violatesAt_mono` Lean theorem is genuinely substantive (verified — uses `omega` over `epLevelOrder` cases with split on `violationLevel m`), so the notebook §4 monotonicity claim is sound. The 6×3 matrix is faithfully reproduced; the cross-bridge to `FangGuTorsionDM.fg_cdm_obstruction` is real (Lean line 553 invokes it directly). Overall: **NOT submission-ready until Stakeholder count drift (F-1.1) is fixed**. Re-review after edit.

## Findings

### 1.1 — 🔴 BLOCKER — Stakeholder notebook still claims "25 machine-checked Lean theorems" (actual = 24)

- **Gate:** CountFreshness (Gate 9) — count drift between published artifact and source of truth.
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-6-md` (§6 "Honest scope").
- **Observed:** "*The classification is encoded as 25 machine-checked Lean theorems with zero `sorry` statements.*"
- **Evidence:**
  - `grep -E "^theorem |^lemma " lean/SKEFTHawking/EquivalencePrinciple.lean | wc -l` → **24**.
  - `grep -E "^theorem " lean/SKEFTHawking/EquivalencePrinciple.lean` enumerates the 24 declarations (lines 196, 211, 226, 239, 252, 266, 285, 302, 326, 340, 356, 383, 423, 442, 446, 450, 454, 458, 462, 474, 495, 506, 520, 548).
  - `docs/counts.tex` line 538: `\newcommand{\epThms}{24}` — the canonical project count macro now reads 24.
  - The `2026-04-29-0100-notebook-claims-review` document (the immediately-preceding claims review) flagged this at REQUIRED severity as F-1; the Lean docstring word-wrap that caused the false positive (`theorem provides that.` at column 0 in the FangGu-bridge docstring) was the root cause and was corrected by reflowing.
  - The user's task brief explicitly notes: "the count was *just corrected* from 25 to 24 because a docstring word-wrap mis-matched at column 0".
- **Expected:** "*…encoded as 24 machine-checked Lean theorems…*"
- **Fix:** In cell `p34s-6-md`, replace the literal "25" with "24". This is a one-token edit — there is no derived prose in this cell that depends on the breakdown. Why BLOCKER and not REQUIRED: this is the **Stakeholder** notebook (the audience-sensitive surface) telling a non-specialist reader a number that is one off from the underlying artifact. A reader who clicks through to the Lean module will see 24, not 25 — destroys credibility in the same class as a wrong arXiv ID.

### 1.2 — 🔴 BLOCKER — Stakeholder §7 cell mis-states the per-bucket breakdown as "25 theorems (13 original + 12 strengthening)"

- **Gate:** CountFreshness (Gate 9).
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-7-md` (§7 "Where to go next").
- **Observed:** "*Lean module: `lean/SKEFTHawking/EquivalencePrinciple.lean` — 25 theorems (13 original + 12 strengthening).*"
- **Evidence:** Same `grep` evidence as F-1.1. The breakdown is **12 original + 12 strengthening = 24** (the Technical notebook gets this right at `p34t-intro` and `p34t-8-md`). The "13 original" tally double-counts the inductive type block (`EPLevel`/`EPMechanism`/`violationLevel`/`violatesAt`/`satisfiesAt`) as a 13th theorem; per the Technical notebook's own `p34t-8-md` parenthetical: "*(Plus structural type definitions ... — counted as definitions, not theorems.)*" — these are **not** theorems by the strict counter and not by the project's own bookkeeping convention.
- **Expected:** "*… 24 theorems (12 original + 12 strengthening).*"
- **Fix:** Replace "25 theorems (13 original + 12 strengthening)" → "24 theorems (12 original + 12 strengthening)". Co-edit with F-1.1 in the same notebook commit.

### 1.3 — 🟡 REQUIRED — Stakeholder notebook collapses paper abstract's hedged STEP-projection into bare "AT the STEP target" / "right at the STEP design sensitivity"

- **Gate:** NarrativeGrounding (Gate 7) — feasibility-claim severity.
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cells `p34s-1-code` (final printed line), `p34s-3-code` (final printed paragraph), `p34s-4-md` and `p34s-4-code` (output line), `p34s-5-md` (right-panel description).
- **Observed:**
  - `p34s-1-code` printed output (cell text, line 6 of the print block): "*η ~ 10⁻¹⁸ — STEP-class projected design sensitivity (white-paper target)*" — **OK, hedged correctly**.
  - `p34s-1-code` final summary line: "*→ vestigial relics sit at the projected STEP-class design sensitivity, well below MICROSCOPE.*" — **OK**.
  - `p34s-3-code` body: "*at the projected STEP-class design sensitivity, with the honest caveat that the classification is substrate-specific.*" — **OK**.
  - `p34s-4-md`: "*…sub-MICROSCOPE (so MICROSCOPE wouldn't see it) but at the **projected STEP-class design sensitivity**.*" — **OK**.
  - `p34s-4-code` output: "*→ predicted is AT the STEP-class design sensitivity (so STEP would see it).*" — **the "so STEP would see it" overstates**: STEP is not a launched mission. It would be more honest to say "*so a STEP-class mission at projected sensitivity would be the relevant test.*"
  - `p34s-5-md`: "*the relics bar (η~10⁻¹⁸) is at the STEP target.*" — borderline; "STEP target" without "projected" reads as if STEP exists today.
- **Issue:** The paper abstract was deliberately hedged in a prior strengthening pass from "within reach" → "at the projected design sensitivity discussed for STEP-class satellite missions" (paper_draft.tex line 41-42, recorded in inventory 2026-04-28-1130). The Stakeholder notebook propagates this hedge in most places but lapses in two outputs (`p34s-4-code` final line; `p34s-5-md` right-panel caption). For a non-specialist audience, "STEP would see it" reads as a deliverable promise; the paper abstract is more careful.
- **Evidence:**
  - `paper_draft.tex:40-42` (abstract): "*…sub-MICROSCOPE and at the projected design sensitivity discussed for STEP-class satellite missions.*"
  - The MICROSCOPE bound is a **launched-mission published** result (Touboul 2017); the STEP bound is **a design target for a future mission** that, as of 2026-04-29, has no flight schedule. The asymmetry deserves consistent prose.
  - The 2026-04-29-0000 internal-adversarial review flagged a residual un-hedged "within reach" still in the paper §II body (line 114) at RECOMMENDED severity — this notebook finding is the analogous body-level un-hedged feasibility-claim.
- **Expected:** Match the abstract's hedged framing throughout. The notebook intro paragraph (`p34s-intro`) actually does this correctly: "*STEP-class follow-ups aim for $\eta \sim 10^{-18}$.*" (aim — projected). The lapses are localized to two cells.
- **Fix:**
  - `p34s-4-code` (the print() block): change the last line from `'  → predicted is AT the STEP-class design sensitivity        (so STEP would see it).'` to `'  → predicted is AT the projected STEP-class design sensitivity   (a STEP-class mission would be the relevant test).'`
  - `p34s-5-md`: change "*the relics bar (η~10⁻¹⁸) is at the STEP target*" to "*the relics bar (η~10⁻¹⁸) is at the projected STEP-class target*".
- **Why REQUIRED, not BLOCKER:** A specialist reader would parse "STEP target" as the design target unambiguously; a stakeholder reader might not. The lapse is localized (most of the cell prose carries the hedge) but the two un-hedged surfaces are exactly the per-cell summary lines that a skim reader sees first. Submission-blocking for a stakeholder-facing artifact; advisory for the paper itself.

### 1.4 — 🟡 REQUIRED — Stakeholder §6 "honest scope" and §7 "where to go next" cells preserved an OBSOLETE Wave-naming convention ("13 original + 12 strengthening")

- **Gate:** CountFreshness (Gate 9). (Companion to F-1.2; recording separately because the *narrative consequence* of the off-by-one differs.)
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-7-md`.
- **Observed:** "*— 25 theorems (13 original + 12 strengthening).*"
- **Issue:** Beyond the count being wrong (covered in F-1.2), the per-bucket breakdown carries a narrative implication for the **review trail**: 12 + 12 (the correct breakdown) is *symmetric* — the wave shipped 12 substantive theorems and the strengthening pass shipped 12 substantive theorems, doubling the coverage. The misstated "13 + 12" obscures the symmetry and creates false suspense about which "original" theorem is missing from the strict counter. Fixing as "12 + 12" both corrects the number and restores the narrative parallel.
- **Expected:** "*— 24 theorems (12 original + 12 strengthening).*"
- **Fix:** Same edit as F-1.2; flagged separately because a partial fix (count → 24 but breakdown left as "13 + 12") would still be wrong and would fail re-review.
- **Why REQUIRED, not BLOCKER:** Subsumed by F-1.2 if both are co-fixed. Listed for traceability so the fix-review pair re-examines the breakdown not just the headline number.

### 1.5 — 🔵 RECOMMENDED — Technical §3 prose verb "bundles still exist" obscures the structural fact that the bundles are now logically derivable

- **Gate:** LeanProofSubstance (Gate 5) — exposition of strengthening-pass mechanic.
- **Location:** `Phase6c3_EquivalencePrinciple_Technical.ipynb` cell `p34t-3-md` (§3 "Single-claim violationLevel per mechanism").
- **Observed:** "*The strengthening pass added single-claim `violationLevel m = some WEP` (violators) or `violationLevel m = none` (non-violators) forms alongside the originals (the bundles still exist), plus a shared `violatesAt_mono` extraction lemma — making the substantive content explicit while leaving downstream consumers of the 3-conjunct bundles intact.*"
- **Issue:** The phrase "*the bundles still exist*" is technically correct (the four `*_satisfies_all_EP` 3-conjunct theorems remain at lines 226, 239, 252, 266) but elides the load-bearing point: those bundles are now **1-line corollaries** of `noViolation_implies_satisfiesAt` (line 474) applied to the corresponding `*_has_no_violation` theorems. The strengthening pass demonstrated the P2 redundancy structurally — it didn't paper over it. The notebook prose understates the strengthening result.
- **Evidence:**
  - Lines 474-479: `noViolation_implies_satisfiesAt {m} (h : violationLevel m = none) (L : EPLevel) : satisfiesAt m L = true` — the shared bundle-extraction lemma.
  - Lines 226-270: the four 3-conjunct bundles are proved by `refine ⟨?_, ?_, ?_⟩ <;> (unfold ...; decide)`, which post-strengthening could be redirected to `(noViolation_implies_satisfiesAt rfl, noViolation_implies_satisfiesAt rfl, noViolation_implies_satisfiesAt rfl)`. The bundles weren't refactored, but they're proven to be derivable.
- **Expected:** Tighten the prose to acknowledge derivability:
  > *The strengthening pass added single-claim `violationLevel m = some WEP` (violators) and `violationLevel m = none` (non-violators) forms alongside the original bundles, plus a shared `noViolation_implies_satisfiesAt` extraction lemma and `violatesAt_mono` monotonicity lemma. The bundles are now 1-line corollaries of these — the P2 redundancy is structurally explicit (not eliminated; downstream consumers of the bundles continue to work).*
- **Fix:** One-paragraph edit in `p34t-3-md`. No code changes.

### 1.6 — 🔵 RECOMMENDED — Stakeholder §3 ("The 6×3 matrix") final paragraph muddies the substrate-specificity hedge

- **Gate:** NarrativeGrounding (Gate 7) — universal-vs-substrate-specific overclaim.
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-3-code` (final printed paragraph).
- **Observed:** "*Pattern: only the two vestigial rows show \"✗ violates\". Within this substrate, a future EP detection in the MICROSCOPE-to-STEP precision window would point to vestigial physics — at the projected STEP-class design sensitivity, with the honest caveat that the classification is substrate-specific.*"
- **Issue:** The sentence is **correct** but its structure is convoluted: "*Within this substrate, ..., with the honest caveat that the classification is substrate-specific.*" — the substrate-specific caveat is stated twice (once as a topic-frame and once as a tail caveat). This is the **only place** in the Stakeholder notebook where the substrate-specificity is asserted as part of the matrix-reading prose. Stakeholder §6 ("Honest scope") asserts it cleanly. Recommend restructuring p34s-3-code's final paragraph to assert it once and link to §6.
- **Evidence:**
  - Stakeholder §6 (cell `p34s-6-md`) carries the canonical hedge: "*The conclusion is substrate-specific: 'In this substrate, EP violation is vestigial-only.' It is not a universal claim about all DM models.*" — clean.
- **Expected:** Either a tighter rewrite or simply reference §6.
- **Fix:** Suggested replacement for `p34s-3-code` final paragraph:
  > *Pattern: only the two vestigial rows show "✗ violates". A future EP detection in the MICROSCOPE-to-STEP precision window would point to vestigial physics within this substrate. (The classification is substrate-specific — see §6 for what this scoping means.)*
- **Why RECOMMENDED, not REQUIRED:** The current prose is technically correct; the readability concern is exposition only.

### 1.7 — 🔵 RECOMMENDED — Stakeholder §2 plain-language paragraph for "Vestigial differential coupling" overstates "MICROSCOPE has already ruled it out"

- **Gate:** NarrativeGrounding (Gate 7) — feasibility/falsification phrasing.
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-2-md`, paragraph 1.
- **Observed:** "*Vestigial differential coupling (violates WEP, η = 1). In a phase where the metric and the tetrad don't quite agree, bosons and fermions \"see\" different effective gravity. The maximum signature is a maximal Eötvös ratio. **Already ruled out by MICROSCOPE.***"
- **Issue:** The claim "*already ruled out by MICROSCOPE*" is correct **provided the η = 1 prediction is actually a hard prediction of the vestigial-phase mechanism** rather than an upper-bound estimate. The Lean module's docstring for `vestigialDifferentialCoupling` (lines 115-119) says "*VEV = 0 in vestigial phase ... `Δ_EP = 1` (maximal violation)*" — so this is a **maximal** violation in the vestigial phase, not a hard prediction. A vestigial-phase mechanism with partial tetrad VEV would predict η < 1. The Stakeholder phrasing reads as a hard exclusion of the vestigial-phase-as-mechanism, not just the η = 1 endpoint.
- **Evidence:**
  - Lean docstring (lines 38-43): "*per `VestigialGravity.ep_violation_in_vestigial`, the vestigial phase has `has_equivalence_principle = false` and EP-violation parameter `Δ_EP = 1` (maximal)*". The "maximal" qualifier was preserved in the formal model.
  - Technical notebook §1 carries the qualifier ("vestigial-phase max η_max = 1.0"); Stakeholder collapses to "the maximum signature is a maximal Eötvös ratio" without distinguishing between *predicted* η_max and *upper-bound estimate* η_max.
- **Expected:** Tighten to acknowledge the upper-bound character. Suggested rewrite:
  > *Vestigial differential coupling (violates WEP at the maximal end, η = 1). ... The maximal end of the prediction range, η = 1, is excluded by MICROSCOPE.*
- **Why RECOMMENDED, not REQUIRED:** A specialist reads the qualifier in. A non-specialist may infer the entire vestigial-phase mechanism is excluded; in fact what's excluded is the η = 1 saturation point.

### 1.8 — ℹ️ INFO — Stakeholder §6 retains a stale theorem-count pointer to "25" in inline prose; co-edits with F-1.1/F-1.2

- **Gate:** CountFreshness (Gate 9), informational.
- **Location:** `Phase6c3_EquivalencePrinciple_Stakeholder.ipynb` cell `p34s-6-md`.
- **Observed:** Same as F-1.1; recorded as INFO so the fix-review pair confirms the cells the user edits add up to all the surfaces. Three Stakeholder surfaces touch the count: `p34s-6-md` (one occurrence), `p34s-7-md` (one occurrence — F-1.2/F-1.4). The count is **NOT** inlined elsewhere — neither in `p34s-intro`, `p34s-1-md`, `p34s-2-md` ... `p34s-5-md`, nor in any printed code-cell output (the code cells compute from `EP_VIOLATION_MATRIX`, which is matrix-based, not count-based).
- **Fix:** No additional action; F-1.1 + F-1.2 cover the surfaces. Listed for the re-review checklist.

## Verifications that PASSED (no findings emitted)

The following were checked and confirmed clean for this fresh-context audit:

- **Citations.** All four bibitems verified against arXiv via `WebFetch`, all `match`:
  - `Touboul2017` arXiv:1712.01176 — "*The MICROSCOPE mission: first results of a space test of the Equivalence Principle*", Touboul et al., PRL **119**, 231101 (2017), DOI 10.1103/PhysRevLett.119.231101 — matches paper_draft.tex line 267-271 and `src/core/citations.py:3131`.
  - `Pretko2017` arXiv:1604.05329 — "*Subdimensional Particle Structure of Higher Rank U(1) Spin Liquids*", M. Pretko, PRB **95**, 115139 (2017), DOI 10.1103/PhysRevB.95.115139 — matches paper_draft.tex line 273-276 and `citations.py:1106`.
  - `Berezhiani2015` arXiv:1507.01019 — "*Theory of Dark Matter Superfluidity*", Berezhiani & Khoury, PRD **92**, 103510 (2015), DOI 10.1103/PhysRevD.92.103510 — matches paper_draft.tex line 278-281 and `citations.py:3163`.
  - `Will2018` — *Theory and Experiment in Gravitational Physics*, 2nd ed., C. M. Will, Cambridge University Press, 2018, DOI 10.1017/9781316338612 — matches paper_draft.tex line 262-265 and `citations.py:3147` (verified via Cambridge Core book record after DOI redirect).
- **Numerical constants.** All four numerical constants (`MICROSCOPE_BOUND = 1e-15`, `STEP_TARGET = 1e-18`, `VESTIGIAL_PHASE_ETA_MAX = 1.0`, `VESTIGIAL_RELICS_ETA = 1e-18`) match between `mechanism_classifier.py:64,68,75,80`, the Lean theorem statements (lines 495-507), the paper draft body (lines 193-196), and the figure (`fig_ep_violation_matrix` at `visualizations.py:8806`, verified by direct read of the rendered PNG).
- **6×3 matrix.** Both notebooks' tabular outputs reproduce `EP_VIOLATION_MATRIX` faithfully. Both vestigial mechanisms violate at all three levels; the four others satisfy at all three. Cross-check with `EP_VIOLATION_MATRIX[m][L] == violates_at(m, L)` returns `all_ok = True` (Technical p34t-2-code).
- **`violatesAt_mono` is genuinely substantive.** Direct read of Lean lines 423-432: the proof uses `cases hL : violationLevel m` followed by `omega` on the order arithmetic. Not a tautology, not a `rfl`, not a structural identity. The notebook §4 monotonicity claim is sound. (Specifically validates the user's adversarial concern #7.)
- **Cross-bridge to FangGu is real.** Lean line 4 imports `SKEFTHawking.FangGuTorsionDM`; line 553 invokes `SKEFTHawking.FangGuTorsionDM.fg_cdm_obstruction hρ htrace` directly. The paper34 notebook §6 prose ("*imports `FangGuTorsionDM` and calls `fg_cdm_obstruction` directly — no docstring drift*") matches the source. (User adversarial concern #4.)
- **Strengthening-pass removed-theorem disclosures honest.** Both Technical §5 and §8 disclose the removal of `step_target_can_test_vestigial_relics` (P5 self-equality `1.0e-18 ≤ 1.0e-18 := le_refl _`) and `module_summary_marker : True := trivial`. Neither notebook references either removed theorem as if extant. (User adversarial concern #6.)
- **`ep_violation_is_vestigial_only` substrate-specificity correctly hedged.** Stakeholder §6 explicitly: "*The conclusion is substrate-specific: 'In this substrate, EP violation is vestigial-only.' It is not a universal claim about all DM models.*". Technical §6 frames the Lean theorem as a structural conclusion within the enumerated mechanism set, not a universal quantifier. (User adversarial concern #5.)
- **Will2018 attribution accurate.** "*Will, Theory and Experiment in Gravitational Physics, 2nd ed., 2018*" matches Cambridge Core record. The 2nd edition publication year (2018) is correct; ISBN 9781316338612 is the digital ISBN, hardback is 9781107117440. No attribution drift.
- **Touboul-2017 = first-results paper** (η < 2.0e-14 90%CL). Final 2022 result (Touboul et al., PRL 129, 121102, 2022) tightens to η ~ 1.0e-15. Both notebooks and the paper draft cite the **first-results** paper while reporting the **final-results** numerical bound (1e-15). This is recorded as a `notes:` field in `citations.py:3145`: "*First-results MICROSCOPE EP bound. Final 2022 result improves to ~1e-15 systematic.*" — matches the way the paper draft uses Touboul2017 (the bound 1e-15 is the final-results number, but the bibitem points to the first-results paper for narrative continuity). Edge-case but **not a finding** since the registry note discloses it; the figure label "*MICROSCOPE bound (Touboul 2017)*" with the η < 1e-15 number is consistent with this convention.
- **`fangGuTorsionTrace` does NOT secretly violate WEP via the kinematic failure mode.** Direct read of `fangGu_failure_mode_is_kinematic_not_ep` (Lean lines 548-553): the cross-bridge theorem **explicitly conjuncts** `¬ is_dust s` (kinematic failure) with `violationLevel = none` (no EP violation). The two are independently true; the kinematic failure mode does NOT bleed into EP. (User adversarial concern #4.)
- **Paper34 paper_draft.tex `\epThms` macro resolves to 24** (current value in `docs/counts.tex:538`). Aligned with the Lean module count.

## QI Candidate

**Recurring count-drift between artifact corrections and notebook prose surfaces.** This is the second time in three days that paper34 has had a count-drift finding (`2026-04-29-0100-notebook-claims-review` F-1 was REQUIRED; this audit now flags it as BLOCKER because the Stakeholder surface is audience-sensitive). The drift survived the 2026-04-29-0100 sweep because that pass focused on the paper artifact and only documented the notebook drift. Suggestion: add a `validate.py --check notebook_count_literals` pass that greps for hard-coded theorem counts in `notebooks/*.ipynb` cells matching `\bN\s+(?:substantive|machine-checked)?\s+(?:Lean\s+)?theorems\b` and cross-checks against `docs/counts.tex` macro values. Cell content is JSON-stringified inside `.ipynb`, so the check needs to walk `cells[].source` strings; would catch this entire finding class automatically.
