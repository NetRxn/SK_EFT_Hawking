---
paper: paper26_bh_entropy
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-26T02:30:43Z
readiness_gates_version: 1
---

# Adversarial Review — paper26_bh_entropy

## Summary

Stage 13 sweep of `paper26_bh_entropy` (Phase 6a Track C Wave 3, Bekenstein-Hawking entropy from MTC state counting) surfaces 14 findings: 5 BLOCKER, 7 REQUIRED, 2 RECOMMENDED. Gates currently failing for submission readiness: CitationIntegrity (Govindarajan-Kaul-Suneeta wrong-title-and-venue is a clear primary-source mismatch; Mitra2014 wrong-title; Vergeles2025 bibitem/registry title disagreement), LeanProofSubstance (the strengthening-pass replacement `H_HorizonBoundaryCondition_implies_areaLawKappa_pos` is a single-conjunct projection of `h.areaLeading` — exactly the structural-tautology pattern the gate is meant to catch), CrossPaperConsistency (the paper's "19 theorems" claim contradicts the Inventory Index's "22 theorems" and the actual `grep` count). Stage 13 also confirms the auto-graph's existing ComputationCorrectness flag (`verlinde_dim_horizon` bounds-only, `log_correction_coefficient_per_mtc` untested). Paper is **NOT submission-ready**; requires citation fixes, Lean-substance audit, and prose-vs-Lean name reconciliation before the gate set can clear.

## Findings

### 1.1 — 🔴 BLOCKER — Govindarajan-Kaul-Suneeta citation: wrong title AND wrong venue

- **Gate:** CitationIntegrity
- **Location:** `paper26_bh_entropy/paper_draft.tex:549-552` and `src/core/citations.py:2418-2431`
- **Observed:** Bibitem `GovindarajanKaulSuneeta2001` declares title "Quantum gravity on dS$_3$" and venue "Class. Quantum Grav. 19, 4195 (2002)"; CITATION_REGISTRY entry agrees with the bibitem. The arXiv ID `gr-qc/0104010` is the same in both.
- **Evidence:** Fresh-fetch `https://arxiv.org/abs/gr-qc/0104010` returns title "Logarithmic correction to the Bekenstein-Hawking entropy of the BTZ black hole", authors T.R. Govindarajan, R.K. Kaul, V. Suneeta, journal Class. Quant. Grav. **18**, 2877 (2001). This is a different paper from "Quantum gravity on dS₃" (which is a separate Govindarajan-Kaul-Suneeta paper). The deep-research file `Lit-Search/Phase-6a/6a-Horizon\ MTC\ boundary\ conditions...md` line 94 also identifies `gr-qc/0104010` as the BTZ-CS −3/2 derivation, NOT the dS₃ paper.
- **Expected:** Either (a) update bibitem + registry to title "Logarithmic correction to the Bekenstein-Hawking entropy of the BTZ black hole" / Class. Quantum Grav. **18**, 2877 (2001), keeping `gr-qc/0104010`; or (b) if the dS₃ paper was actually intended, locate that paper's correct arXiv ID and update.
- **Fix:** Replace bibitem text and the matching `CITATION_REGISTRY['GovindarajanKaulSuneeta2001']` entry with the verified BTZ-paper metadata. Append a `match` record to `docs/citation_verifications.jsonl` once corrected.
- **Cache:** fresh-fetch (verdict `wrong_title` and `wrong_venue` against bibitem)

### 1.2 — 🔴 BLOCKER — Mitra2014 citation: wrong title and wrong venue

- **Gate:** CitationIntegrity
- **Location:** `paper26_bh_entropy/paper_draft.tex:540-542` and `src/core/citations.py:2389-2402`
- **Observed:** Bibitem and registry both record the title as "Black-hole entropy without log correction" with venue "arXiv:1406.5524 (2014)" / `journal: 'arXiv:1406.5524'`.
- **Evidence:** Fresh-fetch `https://arxiv.org/abs/1406.5524` returns title "Black hole entropy with and without log correction in loop quantum gravity" by P. Mitra, published in Nuclear Physics B Proceedings Supplements **251-252**, 87 (2014). The published title contains the qualifier "with and without" that materially changes meaning vs the bibitem ("without"); the venue is a peer-reviewed journal, not arXiv-only.
- **Expected:** Update bibitem + registry to the verified title and proceedings citation.
- **Fix:** Replace bibitem text and `CITATION_REGISTRY['Mitra2014LogVanish']` `title`/`journal`/`volume`/`page` fields. Re-verify via `scripts/citation_cache.append_record`.
- **Cache:** fresh-fetch (verdict `wrong_title`, `wrong_venue`)

### 1.3 — 🔴 BLOCKER — Vergeles2025 bibitem and registry title disagree

- **Gate:** CitationIntegrity
- **Location:** `paper26_bh_entropy/paper_draft.tex:553-558` and `src/core/citations.py:643-656`
- **Observed:** Paper bibitem text reads "Anderson-Higgs gravity and lattice formulation of emergent diffeomorphism invariance" / Phys. Rev. D 112, 054509 (2025). `CITATION_REGISTRY['Vergeles2025']` records title "Unitarity in the ADW mechanism" with the same DOI `10.1103/PhysRevD.112.054509`. Two distinct titles cannot both be correct for one DOI.
- **Evidence:** Direct file read of both sources. `Vergeles2025` `used_in` registry field is also stale: lists only `paper5_adw_gap` even though paper26 cites it (line 72: `\cite{Vergeles2025,Diakonov2011}`).
- **Expected:** Resolve to the verified canonical title via DOI fetch (`https://doi.org/10.1103/PhysRevD.112.054509`); align bibitem and registry. Add `paper26_bh_entropy/paper_draft.tex` to `Vergeles2025.used_in`.
- **Fix:** WebFetch the DOI; update whichever source is wrong. Add paper26 to `used_in`. Append a verification record to `citation_verifications.jsonl`.
- **Cache:** fetch-failed (DOI not yet fetched in this run; flagged for next round)

### 1.4 — 🟡 REQUIRED — All 15 paper26 bibkeys carry `doi_verified: None`

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:2200-2432` (paper26 block)
- **Observed:** Every one of the 15 new paper26 registry entries (KaulMajumdar2000, Kaul2012Review, DomagalaLewandowski2004, Meissner2004, EngleNouiPerez2010, Carlip2000HorizonCFT, Sen2013Schwarzschild, Solodukhin2011LivingRev, WalkerWang2012, BombelliKoulLeeSorkin1986, JacobsonInducedGravity1994, KitaevHonest2006, Mitra2014LogVanish, McGoughVerlinde2013, GovindarajanKaulSuneeta2001) has `doi_verified: None`. Per the project's `feedback_citation_verification_required.md` policy, this defers WebFetch to authorized rounds — but submission cannot proceed until they flip to `True`.
- **Evidence:** `grep -c "'doi_verified': None" src/core/citations.py` for the paper26 block returns 15. Spot-fetches in this review confirmed: KaulMajumdar2000 ✓, Sen2013 ✓, DomagalaLewandowski2004 ✓, Meissner2004 ✓, EngleNouiPerez2010 ✓, Carlip2000HorizonCFT ✓, Solodukhin2011 ✓, KitaevHonest2006 ✓, JacobsonInducedGravity1994 ✓, McGoughVerlinde2013 ✓, WalkerWang2012 ✓, Kaul2012Review ✓ — all match registry. Only GovindarajanKaulSuneeta2001 (1.1) and Mitra2014 (1.2) failed.
- **Expected:** A WebFetch-verified registry round flipping `doi_verified` from `None` → `True` for the 12 that match (and `None` → `False` while corrections land for 1.1 / 1.2 / 1.3).
- **Fix:** Run authorized citation-verification round; append `match` records to `docs/citation_verifications.jsonl`; flip flags. Draft-stage acceptable; submission-blocking.
- **Cache:** fresh-fetch (12 matches recorded mid-review; awaiting append authorization)

### 2.1 — 🟡 REQUIRED — `bh_entropy_leading_coefficient` references non-existent Lean identifier `IsHorizonBC`

- **Gate:** ParameterProvenance (formula-Lean linkage / Pipeline Invariant 4)
- **Location:** `src/core/formulas.py:7707-7708`
- **Observed:** The docstring `Lean:` reference reads `BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi (field), discharge via BHEntropyMicroscopic.IsHorizonBC.immirziTuned`. `IsHorizonBC` does not exist in `BHEntropyMicroscopic.lean`; the only structure shipped is `H_HorizonBoundaryCondition`, which has fields `positivity, areaLeading, secondLaw, modularInvariant, anomalyMatch` (no `immirziTuned`).
- **Evidence:** `grep -nE "IsHorizonBC|immirziTuned" lean/SKEFTHawking/BHEntropyMicroscopic.lean` returns zero hits. The deep-research outline (`Lit-Search/Phase-6a/6a-Horizon...md` §6) recommends `IsHorizonBC` and `immirziTuned` as the Lean shape, but the actual implementation diverged.
- **Expected:** Update the formula docstring to reference the actually-shipped Lean identifiers.
- **Fix:** In `src/core/formulas.py` `bh_entropy_leading_coefficient`, change the `Lean:` line to `BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi (field); tuning hypothesis appears informally — no formal `immirziTuned` discharge proven yet`.

### 2.2 — 🟡 REQUIRED — `verlinde_dim_horizon` formula references non-existent Lean identifier `BHEntropyMicroscopic.verlindeDimHorizon`

- **Gate:** ParameterProvenance / Pipeline Invariant 4
- **Location:** `src/core/formulas.py:7618`
- **Observed:** Docstring says `Lean: BHEntropyMicroscopic.verlindeDimHorizon`. No declaration of that name (or `verlinde_dim_horizon` / `verlindeDim`) exists in any `.lean` file.
- **Evidence:** `grep -rE "verlindeDimHorizon|verlinde_dim_horizon" lean/` returns zero hits. The actual Lean shape uses an opaque `verlindeEntropy_SU2k` plus the abstract `HorizonMTCBC` data — no Verlinde-formula sum is formalized at theorem level.
- **Expected:** Either (a) drop the `Lean:` reference until a Lean stub exists, replacing with "Lean: pending — Verlinde sum not yet formalized; abstract counterpart `verlindeEntropy_SU2k` (opaque)"; or (b) ship a Lean stub `verlindeDimHorizon` (sorry-allowed sector definition).
- **Fix:** Adjust docstring per (a) for Wave 3 ship; (b) belongs to a follow-on wave.

### 2.3 — 🟡 REQUIRED — `bh_entropy_kaul_majumdar` formula references non-existent Lean identifier `BHEntropyMicroscopic.kaulMajumdarClosedForm`

- **Gate:** ParameterProvenance / Pipeline Invariant 4
- **Location:** `src/core/formulas.py:7665`
- **Observed:** Docstring says `Lean: BHEntropyMicroscopic.kaulMajumdarClosedForm`. The actual Lean definition is `kaulMajumdarS` (line 86 of the Lean file). No declaration `kaulMajumdarClosedForm` exists.
- **Evidence:** `grep -nE "kaulMajumdarClosedForm" lean/SKEFTHawking/BHEntropyMicroscopic.lean` returns zero hits. The same fictitious name appears in `AXIOM_METADATA['gaussianSaddleAsymptotic']['used_in']` and `evidence_ladder.Project escape.risk` — propagating the staleness to the axiom-tracking infrastructure (see 2.4).
- **Expected:** Update docstring to `Lean: BHEntropyMicroscopic.kaulMajumdarS`.
- **Fix:** One-line edit in `src/core/formulas.py` line 7665.

### 2.4 — 🟡 REQUIRED — `AXIOM_METADATA['gaussianSaddleAsymptotic']` cross-references two non-existent theorems

- **Gate:** ParameterProvenance / Pipeline Invariant 4
- **Location:** `src/core/constants.py:1395, 1404`
- **Observed:** `'used_in': 'kaulMajumdarLogCoefficient, kaulMajumdarClosedForm'` and `evidence_ladder.Project escape.risk: 'Low — sole user is BHEntropyMicroscopic.kaulMajumdarClosedForm'`. Neither `kaulMajumdarLogCoefficient` nor `kaulMajumdarClosedForm` exists.
- **Evidence:** `grep -rE "kaulMajumdarLogCoefficient|kaulMajumdarClosedForm" lean/` returns nothing. Actual axiom users (per Lean source): `kaulMajumdar_asymptotic_within_OoneOverA` (line 203, `:= gaussianSaddleAsymptotic`) and `verlinde_matches_kaul_majumdar_at_large_area` (line 219, `obtain ⟨C, hCpos, hC⟩ := gaussianSaddleAsymptotic`).
- **Expected:** Update `AXIOM_METADATA` so `used_in` and the `Project escape.risk` reference the actual users.
- **Fix:** Edit `src/core/constants.py` lines 1395 and 1404 with the verified names.

### 3.1 — 🔴 BLOCKER — `H_HorizonBoundaryCondition_implies_areaLawKappa_pos` is a structural tautology

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHEntropyMicroscopic.lean:402-405`
- **Observed:** The strengthening-pass replacement for the vacuous `falsifier_anomalyMatch` is:
  ```
  theorem H_HorizonBoundaryCondition_implies_areaLawKappa_pos
      (H : HorizonMTCBC) (S_horizon : HorizonMTCBC → ℝ → ℝ)
      (h : H_HorizonBoundaryCondition H S_horizon) :
      0 < H.areaLawKappa := h.areaLeading
  ```
  The body is `h.areaLeading`. The `H_HorizonBoundaryCondition` structure declares its `areaLeading` field as `0 < H.areaLawKappa` (line 329). The theorem's conclusion is byte-for-byte the type of one of its hypothesis's fields, and the proof is the field projection. This is the canonical pattern flagged in the agent definition's class-3 BLOCKER taxonomy: "Body is a term-mode anonymous constructor or tuple that includes a hypothesis of the theorem as one of its output fields → structural tautology → BLOCKER."
- **Evidence:** Direct file read. The docstring claims this theorem is "non-vacuous because abelian-MTC instances trigger F2... witnessing the strict inequality `0 < H.areaLawKappa` as a derived fact, not a hypothesis" — but the proof is `h.areaLeading`, which IS the hypothesis. The "non-vacuity" comes from a separate theorem `abelian_MTC_falsifies_H_HorizonBoundaryCondition` (line 417), which is genuinely substantive. This theorem on its own is a one-step projection.
- **Expected:** Either (a) replace with a substantive F5 falsifier statement (e.g., a concrete chiral-c_- mismatch falsifier theorem at the per-MTC level), or (b) acknowledge in the docstring that this theorem is a *projection* and not the F5 falsifier the paper claims it is, then ship the actual F5 placeholder honestly. Option (a) is preferred per the project's "correctness over expediency" standard. The paper currently markets this theorem as if it were the F5 strengthening — see finding 4.1 for the paper-side drift.
- **Fix:** Lean-side: either prove a non-trivial corollary (e.g., monotonicity + areaLeading combined gives a quantitative lower bound on `S_horizon H A` for `A ≥ A_0`), OR rename to `H_HorizonBoundaryCondition.areaLeading'` with a comment "field accessor, not a substantive theorem." Paper-side: do not list this as a falsifier in §5.1.

### 3.2 — 🟡 REQUIRED — `kaul_majumdar_log_decomposition` does not formalize the structural decomposition

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHEntropyMicroscopic.lean:119-120`
- **Observed:** The theorem reads `(-(1 : ℝ) / 2) + (-1 : ℝ) = -3 / 2 := by ring`. This is the *arithmetic identity* on raw rationals — there is no Lean object capturing "Gaussian saddle contributes −1/2", no object capturing "SU(2)-singlet projection contributes −1", no logical link between the values and the physics interpretation.
- **Evidence:** Paper line 100-101: "The decomposition is a Lean theorem, `kaul_majumdar_log_decomposition`." This sentence implies the *physics decomposition* is machine-checked. What is actually machine-checked is `−1/2 + −1 = −3/2`. The names `c_Gaussian` and `c_singlet` appear in the *paper's prose* (line 207-209) but not in the Lean theorem signature.
- **Expected:** Either (a) reword the paper to say "the arithmetic identity that the labelled values sum to −3/2 is encoded as `kaul_majumdar_log_decomposition`; the physical sourcing of −1/2 ↔ Gaussian saddle and −1 ↔ singlet projection is documented in the surrounding prose but not formalized at theorem level"; or (b) write a Lean formalization that genuinely encodes the saddle/projection decomposition (e.g., abstract `gaussianContribution`, `singletProjectionContribution` definitions with axiomatized values, then a theorem that their sum equals the structural log coefficient).
- **Fix:** Apply (a) for Wave 3 — clearer prose; (b) is multi-day Lean work belonging to a follow-on wave.

### 3.3 — 🔵 RECOMMENDED — `kaul_majumdar_leading_matches_G_N_emerg` is a conjunction of two pre-existing theorems

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHEntropyMicroscopic.lean:553-559`
- **Observed:** The theorem packages `G_N_emerg_pos` and `kaulMajumdar_S_at_4GN` into an `∧`, with the body being a `refine ⟨..., ...⟩` that calls each. No new mathematical content is added beyond bundling.
- **Evidence:** Direct file read. Both conjuncts are pre-existing theorems; the bridge is administrative.
- **Expected:** Acceptable as a "bridge" theorem if the docstring is honest about its administrative role. The paper §6 calls it "the algebraic shape of the matching condition" — that's borderline accurate but easily misread as substantive.
- **Fix:** Soften the paper's description in §6 (line 421-424) to "records the conjunction of `G_N_emerg_pos` and the entropy-at-4G_N anchor; the substantive Wave-1-side content is in `LinearizedEFE.G_N_emerg_pos`."

### 4.1 — 🔴 BLOCKER — Paper references non-existent `falsifier_anomalyMatch`; strengthening-pass paper drift

- **Gate:** CrossPaperConsistency / FixPropagation
- **Location:** `paper26_bh_entropy/paper_draft.tex:299-302`
- **Observed:** The paper lists `\texttt{falsifier\_anomalyMatch}: trivially holds at the abstract level; substantive content lives at the per-MTC sub-corollary level (currently conjectural across all candidates).` This name does not exist in `BHEntropyMicroscopic.lean`. Per the Inventory Index (line 65), the strengthening pass on 2026-04-26 *replaced* the vacuous `falsifier_anomalyMatch` with the substantive (per the index — though see finding 3.1) corollary `H_HorizonBoundaryCondition_implies_areaLawKappa_pos`. The paper retains the old name and the old "trivially holds" framing.
- **Evidence:** `grep -nE "falsifier_anomalyMatch" lean/SKEFTHawking/BHEntropyMicroscopic.lean` returns zero hits. The Inventory Index acknowledges the rename. This is exactly the failure-class warned about in `feedback_strengthening_pass_paper_drift.md` (per CLAUDE.md's MEMORY index).
- **Expected:** Update §5.1 of the paper to reference `H_HorizonBoundaryCondition_implies_areaLawKappa_pos` (or, after fixing 3.1, whatever its correct name becomes). Update the description from "trivially holds" to whatever the strengthened theorem actually says.
- **Fix:** Edit `paper_draft.tex` lines 299-302 to match the post-strengthening Lean reality. Subject to 3.1: if the F5 theorem is replaced or renamed, this paper edit follows.

### 4.2 — 🔴 BLOCKER — Paper claims "19 theorems" but module ships 22

- **Gate:** CrossPaperConsistency / NumericalFreshness
- **Location:** `paper26_bh_entropy/paper_draft.tex:384, 453-454`
- **Observed:** Two locations in the paper assert "19 theorems": "§7 Lean Formalization: 19 theorems, 0 sorry, 1 new axiom"; "Conclusions: ships 19 theorems, 0~sorry, and one new axiom". The Inventory Index (line 65) and a direct `grep -cE "^theorem |^lemma " lean/SKEFTHawking/BHEntropyMicroscopic.lean` BOTH return 22. The system context summary also says 22. The post-strengthening pass added 4 theorems on top of an initial 19 (the index calls out `H_HorizonBoundaryCondition_implies_areaLawKappa_pos`, `abelian_MTC_falsifies_H_HorizonBoundaryCondition`, `sen_4d_quantitative_disagreement_bound`, `fibonacci_horizon_areaLawKappa_pos` — but only one of those is actually a *new* theorem replacing a vacuous one, the other three are net additions; net delta is +3, not +4. The "19 → 22" arithmetic checks).
- **Evidence:** Direct count: 22. Inventory line 65: "22 explicit thms (19 initial + 4 strengthening pass...)". Paper still says 19 in two places.
- **Expected:** Update both occurrences to 22, and re-list the cited theorems in §7 to include the 3 strengthening additions (`abelian_MTC_falsifies_H_HorizonBoundaryCondition`, `sen_4d_quantitative_disagreement_bound`, `fibonacci_horizon_areaLawKappa_pos`).
- **Fix:** Edit `paper_draft.tex` lines 384, 453, and add bullet items in §7's `\begin{itemize}` at lines 391-413.

### 4.3 — 🟡 REQUIRED — Paper's per-MTC F4 entries pass via "formalized S-matrices" that aren't the same kind of object

- **Gate:** CrossPaperConsistency
- **Location:** `paper26_bh_entropy/paper_draft.tex:330-336`
- **Observed:** The paper claims "F4 (modular invariance) entries pass via the formalized S-matrices in `SU2kFusion.lean` (verified unitary for k ∈ {2, 3, 4, 5, 10} in our pytest suite), `FibonacciMTC.lean` (proven, zero sorry, native_decide over ℚ(√5)), `IsingBraiding.lean` (proven, zero sorry), `S3CenterAnyons.lean` (proven, zero sorry)."  But F4 is `(ST)³ = S²` (paper line 281-282), not S-matrix unitarity. The four cited modules formalize S-matrix unitarity / fusion-rule data; they do not in general prove `(ST)³ = S²` for those MTCs.
- **Evidence:** Direct read of paper. The deep research file (line 207) defines F4 as `ModularInvariantHorizonZ horizonMTC.C` — the modular-invariance partition function predicate, which is `(ST)³ = S²` style. Unitarity of S is necessary but not sufficient. The paper conflates "S is unitary" with "the MTC satisfies the modular relation `(ST)³ = S²`."
- **Expected:** Either (a) reword the paper to acknowledge that F4 is `True` (placeholder) at the abstract level and the cited modules establish *S-matrix unitarity*, which is a *necessary* ingredient toward F4 but not the full predicate; or (b) cite the specific theorems in the four modules that prove `(ST)³ = S²` (not unitarity) — likely none exist.
- **Fix:** Tighten paper §3.2 prose. Spot-check each module's actually-proved modular relations.

### 5.1 — 🔵 RECOMMENDED — Novelty-claim cross-check is internally consistent with the deep research

- **Gate:** NarrativeGrounding (FirstClaimVerification adjacent)
- **Location:** `paper26_bh_entropy/paper_draft.tex:60-62, 84-87, 432-446`
- **Observed:** Three novelty flags ("Kaul-Majumdar Verlinde counting on a non-LQG ADW substrate"; "any specific finite MTC at a 4D BH horizon"; "Walker-Wang anomaly inflow ADW↔horizon SET") are repeated verbatim from the Wave 3 deep-research return §"Explicit novelty flags for Wave 3 documentation" (lines 286-291 of `Lit-Search/Phase-6a/6a-Horizon...md`). The paper does NOT claim "first formally verified" — it claims "unpublished as of April 2026", which is the deep-research verdict, not a stronger first-in-proof-assistant claim.
- **Evidence:** Paper line 60-62: "synthesis ... is unpublished as of April~2026 and is novelty-flagged accordingly." Deep research §"Recommended outcome mode" verdict 5: "Novelty flagging is required. The synthesis ... appears unpublished as of April 2026 and should be marked as original to the SK-EFT Hawking project." Wording aligns. The auto-graph's NarrativeGrounding `0 flagged interesting` is consistent with the paper's measured "unpublished" framing — no `first-claim`-level claim is being made that needs the (not-yet-implemented) FirstClaimLedger.
- **Expected:** No fix needed. Acceptable as drafted. Flagging here for the record so a future reviewer doesn't unnecessarily re-litigate the novelty framing.
- **Fix:** None.

### 6.1 — 🟡 REQUIRED — Per-MTC F1/F3/F4 ✓ entries in Table I are not formally verified at theorem level

- **Gate:** AssumptionDisclosure
- **Location:** `paper26_bh_entropy/paper_draft.tex:311-329`
- **Observed:** Table I lists Fibonacci, Ising, $D(S_3)$, SU(2)$_k$ as ✓ on F1 (positivity), F3 (second law), F4 (modular invariance). For these four MTCs there is NO Lean theorem of the form `H_HorizonBoundaryCondition fibonacciHorizonBC S_horizon` (or equivalent) being proved. There is a `fibonacciHorizonBC : HorizonMTCBC` instance and a single positive-areaLawKappa theorem `fibonacci_horizon_areaLawKappa_pos`, but no full discharge of F1/F3/F4 for any of the listed MTCs.
- **Evidence:** Direct grep of `BHEntropyMicroscopic.lean` shows the only per-MTC instance is `fibonacciHorizonBC` (line 488). No `S_horizon` candidate is constructed for it; therefore F1/F3 cannot be theorem-checked. F4 is a `True` placeholder for everyone (line 331). The Table I ✓ entries are *expectations* given the abstract structure, not verified per-instance.
- **Expected:** Either (a) reword the table caption to "expected per Wave 3 conjecture" or "structurally compatible (no F1/F3 falsifier triggered by published `d_a` data)"; or (b) ship per-MTC Lean instances of `H_HorizonBoundaryCondition fibonacciHorizonBC S_horizon_KM`, etc., for at least one MTC. Option (a) for Wave 3 ship.
- **Fix:** Edit Table I caption + footnote; add a sentence to §3.2 acknowledging the ✓ entries are conjectural-structural, not theorem-discharged.

### 7.1 — 🟡 REQUIRED — Paper's `verlinde_dim_horizon` claim is partially supported (Python only)

- **Gate:** ComputationCorrectness (auto-graph already flags this)
- **Location:** `paper26_bh_entropy/paper_draft.tex:155-162`; auto-graph blocker
- **Observed:** The auto-graph (from `evaluate_all_gates`) reports: `ComputationCorrectness: blocked. blockers: ['bounds-only: verlinde_dim_horizon', 'no tests: log_correction_coefficient_per_mtc']`. The paper claims (line 158-161): "Equation \eqref{eq:verlinde} is the literal physical content of the horizon state count, encoded as `verlinde_dim_horizon` in `src.core.formulas`. We verify numerically that for SU(2)_k at k=2 (Ising) the four-σ correlator gives dim = 2 ..."
- **Evidence:** The numerical verification mentioned IS implemented and tested (per the Inventory Index's "43 pytest covering ... Verlinde formula numerics (Ising σσσσ → 2 channels)"), but the test is a `bounds`-style check rather than `golden`/`identity`/`roundtrip`. Per Gate 4 definitions (READINESS_GATES.md §4), bounds-only coverage is the canonical "silent formula bugs ship" failure mode.
- **Expected:** Add a `golden`-style test that asserts `verlinde_dim_horizon(p=4, S_matrix=S_Ising, label_indices=[1,1,1,1]) == pytest.approx(2.0)` (numeric-equality, not bounds). Same for `log_correction_coefficient_per_mtc` (currently has no tests).
- **Fix:** Edit the paper26-relevant test file (likely `tests/test_bh_entropy.py` or similar in `tests/`). Two new tests at minimum.

### 8.1 — 🔵 RECOMMENDED — counts.tex is fresh as of 2026-04-26 02:30 UTC; paper-side counts (19) lag canonical (22)

- **Gate:** NumericalFreshness
- **Location:** `paper_draft.tex:384, 453`; vs `docs/counts.tex` post-`update_counts.py`
- **Observed:** A run of `uv run python scripts/update_counts.py --print` shows `Theorems: 4162` total; `BHEntropyMicroscopic` per-module count via grep is 22. The paper hard-codes "19 theorems". This is identical issue to 4.2 but specifically lives in NumericalFreshness — the paper does NOT use `\input{}` macros for these per-module counts (they are inline literals).
- **Evidence:** counts.tex auto-generated 2026-04-25T20:15 then re-checked 2026-04-26T02:30. Module-level theorem counts not yet exposed via macros (e.g., no `\bhEntropyTotal{}` macro analogous to `\fhdTotal{}`).
- **Expected:** Either (a) add a `\bhEntropyTotal` macro to `counts.tex` (driven by `update_counts.py`) and use `\input{...}\bhEntropyTotal{}` in the paper; or (b) update the inline literal to 22 and accept staleness on the next strengthening pass. Wave 3 ship: option (b); Phase 6f or later: option (a) per the `tables.py`-style retrofit.
- **Fix:** For now, edit lines 384 and 453 to "22 theorems."

## QI Candidate

### Systemic issue: Lean references in formulas.py and AXIOM_METADATA drift from actual Lean shipping names

Three places in this review surfaced the same root failure: a Python-side metadata field (`Lean:` docstring in `formulas.py`; `used_in` in `AXIOM_METADATA`) names a Lean identifier that does not exist in the Lean source. Findings 2.1 (`IsHorizonBC.immirziTuned`), 2.2 (`verlindeDimHorizon`), 2.3 (`kaulMajumdarClosedForm` in formulas), and 2.4 (`kaulMajumdarLogCoefficient, kaulMajumdarClosedForm` in AXIOM_METADATA) are all instances. The pattern: a wave-author drafts the Python-side metadata using *recommended* Lean names from the deep-research outline, then the actual Lean implementation diverges (often correctly — using more idiomatic names), but the Python-side references aren't updated.

**Proposed QI:** add a `validate.py --check formula_lean_refs_resolve` and `validate.py --check axiom_metadata_used_in_resolve` that grep every `Lean:` docstring line in `src/core/formulas.py` and every `used_in` field in `AXIOM_METADATA`, extract the dotted names, and assert each resolves to an actually-shipped Lean declaration. This generalizes the existing `paper_lean_refs` check (which the project's `feedback_strengthening_pass_paper_drift.md` already calls out as a QI suggestion) to non-paper Python metadata. Implementation cost: ~2 hours; covers the (3 + N) similar failures that have shipped through pipelines without detection.

### Systemic issue: paper-side prose drift after strengthening passes

Finding 4.1 (`falsifier_anomalyMatch` reference) and 4.2 (19→22 theorem count) are both instances of "post-strengthening-pass paper prose lag." The Inventory Index correctly logs the strengthening; the paper draft does not get re-grepped for the renamed/replaced theorem names and the new theorem totals. `feedback_strengthening_pass_paper_drift.md` already exists in MEMORY.md flagging this; the QI suggestion there ("`validate.py --check paper_lean_refs`") would catch 4.1 directly. Implementation belongs to whoever owns the QI register — adversarial review keeps surfacing this class.
