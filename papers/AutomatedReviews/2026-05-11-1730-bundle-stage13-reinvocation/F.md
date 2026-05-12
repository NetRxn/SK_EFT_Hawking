---
bundle: F
paper: F_flagship_review
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-05-11T17:30:00Z
readiness_gates_version: 1
round: reinvocation
verdict: BLOCKED_NEW_BLOCKERS
blockers_open: 4
findings_total: 11
findings_blocker: 4
findings_required: 3
findings_recommended: 4
---

# Adversarial Review — F_flagship_review (re-invocation 2026-05-11)

## Summary

Re-invocation pass following the 2026-05-11 Stage-13 sweep re-lift of bundle
F (Tier-0 flagship). The re-lift was intended to absorb 4 substantive
sibling-bundle corrections (DoublonGate→FermiHubbardDimer, wen_adw_factor_6000→
coupling_deficit+coupling_ratio_small, 8/8 universal-Bayes→mixed-threshold,
Sakharov biconditional→one-way implication) and remove 8 project-side
first-claim sites.

**Verdict: NEW BLOCKERS — re-lift introduced or failed to fix regressions.**
The 2026-05-04 review closed at GREEN with 4 advisory carry-forwards. This
re-invocation finds 4 new BLOCKERs that prevent bundle close:

1. **Abstract still carries the universal-Bayes overclaim** that the re-lift
   was explicitly supposed to retire (regression — the change-log claimed §1
   line ~76 was downgraded but the abstract sentence was not actually fixed).
2. **`coupling_deficit` / `coupling_ratio_small` certify a 1/1000
   four-fermion-coupling bound**, not the 1/6000 Newton-constant ratio the
   prose makes them claim (Lean-proof-substance misrepresentation introduced
   by the re-lift's §4 substitution).
3. **`dai_freed_spin_z4` is a structural-tautology theorem**
   (body: `⟨Equiv.refl _, (Equiv.refl _).bijective⟩`) cited as the L2/D2
   shared Lean anchor; the module's own docstring explicitly says it must
   be described as an external hypothesis, not Lean-verified.
4. **Wrong-namespace citation**: F cites
   `Z16Classification.dai_freed_spin_z4`; the theorem lives in
   `Z16AnomalyComputation.lean`.

Plus REQUIRED items: 8+ remaining first-formalisation / "to our knowledge"
sites that the re-lift was supposed to clean (the change-log claimed
8/8 sites removed but the actual count of project-side first-claims in
the current draft is at least 10 across 4 subsections); deprecated-alias
citation; missing T_H provenance.

## Findings

### 1.1 — 🔴 BLOCKER — Wrong-namespace citation of `dai_freed_spin_z4`

- **Gate:** CitationIntegrity (Gate 1) / LeanProofSubstance (Gate 5)
- **Location:** `papers/F/paper_draft.tex:830`
- **Observed:** `(\texttt{Z16Classification.dai\_freed\_spin\_z4})
  character-for-character.`
- **Evidence:**
  - `lean/SKEFTHawking/Z16AnomalyComputation.lean:51` —
    `theorem dai_freed_spin_z4 : ∃ (φ : ZMod 16 ≃ ZMod 16),
     Function.Bijective φ := ⟨Equiv.refl _, (Equiv.refl _).bijective⟩`
  - `lean/SKEFTHawking/Z16Classification.lean` — does NOT contain a
    `dai_freed_spin_z4` declaration; cross-referenced via grep across
    `lean/SKEFTHawking/`.
- **Expected:** `\texttt{Z16AnomalyComputation.dai\_freed\_spin\_z4}` (the
  actual module path).
- **Fix:** Replace `Z16Classification` with `Z16AnomalyComputation` at
  line 830. A reader following the F-claimed module path will not find
  the theorem.

### 1.2 — 🔴 BLOCKER — `dai_freed_spin_z4` cited as Lean-verified is structural tautology

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `papers/F/paper_draft.tex:752` and `:830`
- **Observed:**
  - Line 752: "A single Standard-Model generation contributes a
    $\mathbb{Z}_{16}$ charge of $1$ (\texttt{dai\_freed\_spin\_z4})"
  - Line 830: "The L2 splash and the D2 deep paper share the same Lean
    theorem anchor (\texttt{Z16Classification.dai\_freed\_spin\_z4})
    character-for-character."
- **Evidence:**
  - Theorem body at `Z16AnomalyComputation.lean:51`:
    `⟨Equiv.refl _, (Equiv.refl _).bijective⟩` — proves
    `∃ (φ : ZMod 16 ≃ ZMod 16), Function.Bijective φ` by invoking the
    identity self-equivalence, which is true for any nonempty type and
    encodes none of the Dai-Freed cobordism content.
  - Module docstring (`Z16AnomalyComputation.lean`, header just above
    line 51):
    > "Papers that cite this module MUST describe the Dai-Freed result
    > as an **external hypothesis**, not a Lean-verified fact.
    > Recommended phrasing: 'Lean-formalized consequence of the Dai-Freed
    > theorem, with the cobordism computation Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆
    > taken as an external hypothesis.'"
- **Expected:** Either remove the theorem citation entirely and add an
  explicit external-hypothesis disclaimer (matching the module's required
  phrasing), or cite a substantive Lean theorem that actually encodes
  the per-generation $\mathbb{Z}_{16}$ charge.
- **Fix:** Two parallel changes:
  1. Line 752: replace `(\texttt{dai\_freed\_spin\_z4})` with an external-
     hypothesis disclaimer matching the module's required phrasing.
  2. Line 830: rewrite the "character-for-character" sentence to identify
     L2 and D2's shared *external hypothesis* (the Ω₅ ≅ ℤ₁₆ cobordism
     computation), not a Lean theorem anchor.

### 1.3 — 🔴 BLOCKER — `coupling_deficit` cited for a Newton-constant claim it does not prove

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `papers/F/paper_draft.tex:912-921` and `:1693-1697`
- **Observed (§4, Closure 2):**
  > "the heat-kernel calibration applied to the Wen-extended substrate
  > produces an emergent Newton constant $G_{\mathrm{Wen}}$ that
  > differs from the ADW result by a closed-form ratio
  > $G_{\mathrm{Wen}}/G_c^{\mathrm{ADW}} \approx 1/6000$ ... The deficit
  > is a closed-form Lean identity
  > (\texttt{EmergentGravityBounds.coupling\_deficit} and
  > \texttt{EmergentGravityBounds.coupling\_ratio\_small} certify the
  > upper bound on $G_{\mathrm{Wen}}/G_c^{\mathrm{ADW}}$ at any natural
  > parameter point downstream of \texttt{GaugeErasure.gauge\_erasure})."
- **Evidence:**
  - `lean/SKEFTHawking/EmergentGravityBounds.lean:77`:
    ```
    theorem coupling_deficit (alpha Λ : ℝ) (N_f : ℕ)
      (hα0 : 0 ≤ alpha) (hα : alpha ≤ 1/5) (hΛ : Λ > 0)
      (hN : N_f ≤ 10) (hN0 : 0 < N_f) :
      perturbative_4f_coupling alpha Λ < G_c_adw N_f Λ / 1000
    ```
    Both sides are 4-fermion couplings; the theorem bounds
    `G₄f < G_c / 1000` (factor 1000, not 6000).
  - `lean/SKEFTHawking/EmergentGravityBounds.lean:103`:
    ```
    theorem coupling_ratio_small :
      coupling_ratio (1/5) 4 < 1/1000
    ```
    Specific α = 1/5, N_f = 4 instance of the same coupling ratio
    α²·N_f/(32π³), again a 1/1000 bound on the *coupling ratio*.
  - `EmergentGravityBounds.lean` module summary (line ~209):
    "Coupling deficit: G₄f < G_c/1000". The 6000 number appears only
    in an informal docstring comment ("~6,000x weaker than the ADW
    critical coupling") at line 13; no theorem proves a 1/6000 bound,
    and no theorem in the module proves a *Newton-constant* ratio
    G_{\mathrm{Wen}}/G_c^{\mathrm{ADW}}.
  - The prose claim that the cited theorems "certify the upper bound on
    $G_{\mathrm{Wen}}/G_c^{\mathrm{ADW}}$" is therefore a category error:
    they certify a 4-fermion-coupling bound, not a Newton-constant
    bound, and the factor is 1000 not 6000.
- **Expected:** Either
  (a) Update the prose to state honestly: "The Lean theorems
  `EmergentGravityBounds.coupling_deficit` (G₄f < G_c/1000 for the
  perturbative 4-fermion coupling) and `coupling_ratio_small` (the
  α=1/5, N_f=4 instance) certify a ≥3-orders-of-magnitude coupling
  deficit. The factor-6000 estimate on the emergent Newton constant
  ratio is an informal heuristic extrapolation from this coupling
  deficit and is not separately Lean-verified."
  (b) Or — if a separate Lean theorem actually does verify the
  G_{\mathrm{Wen}}/G_c^{\mathrm{ADW}} ≈ 1/6000 Newton-constant ratio —
  cite that theorem instead.
- **Fix:** Investigate whether option (b) is achievable; if not, apply
  (a). Line 1693-1697 (substrate register, "Falsified" entry) carries
  the same factor-6000 claim and must be aligned with whichever fix is
  applied.
- **Regression note:** This finding was opened *by the re-lift itself*.
  The 2026-05-04 round-2 review documented `wen_adw_factor_6000` as an
  unresolved D3-bound advisory (REQUIRED 1.2 carry-forward). The
  2026-05-11 re-lift replaced the in-flight reference with two real
  theorems but did not address the underlying mismatch between
  prose (1/6000 G_N ratio) and Lean content (1/1000 coupling ratio).

### 1.4 — 🔴 BLOCKER — Abstract still carries the universal-Bayes overclaim

- **Gate:** NarrativeGrounding (Gate 7) / CrossPaperConsistency (Gate 2)
- **Location:** `papers/F/paper_draft.tex:76-77`
- **Observed (abstract):**
  > "entropic-gravity dark energy is closed unanimously across $8/8$
  > candidates with quantitative Bayesian thresholds exceeding decisive."
- **Evidence:**
  - The change_log (`papers/F/change_log.md:12`) explicitly listed
    "§1 (line ~76)" among the 4 sites flagged for the universal-Bayes
    → mixed-threshold downgrade: "8/8 entropic-DE Bayes-decisive
    |log B|≥5 universal claim downgraded to mixed-threshold (3
    quantitative Bayes-decisive + Barrow at ΔAIC=4.7 Burnham-Anderson
    moderate)".
  - Lines 184-187 of the same draft (§1.3 NO-GO section) now correctly
    read: "three of the four quantitative mechanisms (Verlinde,
    Tsallis-aggregate, Odintsov) exceeding the Jeffreys-decisive Bayes
    threshold and the fourth (Barrow) disfavoured by information-criteria
    ΔAIC = 4.7 above the Burnham-Anderson moderate threshold".
  - Lines 367-377 (§2.3 Track B) match the corrected form.
  - Lines 1721-1726 (§10 substrate register) match the corrected form.
  - The abstract was not updated. It is therefore internally
    inconsistent with the body of the same draft and externally
    inconsistent with D5 (which has the same correction applied at
    D5/paper_draft.tex lines 848-865 and §11.5).
  - Cross-paper diff: D5 explicitly states `barrow_aic_delta = 4.7` and
    explicitly distinguishes Verlinde/Tsallis/Odintsov from Barrow.
    F's abstract collapses this distinction to "thresholds exceeding
    decisive". Direct CrossPaperConsistency violation.
- **Expected:** Abstract line 76-77 must read consistent with §1.3 and §10:
  "...entropic-gravity dark energy is closed unanimously across 8/8
  candidates at mixed quantitative thresholds (three of four
  quantitative mechanisms exceed Jeffreys-decisive |log B| ≥ 5; Barrow
  disfavoured at ΔAIC = 4.7, above Burnham-Anderson moderate)."
- **Fix:** Edit the abstract. This is the most consequential prose
  location in the paper; the universal-Bayes claim in the abstract is
  what most readers will see first.
- **Regression note:** This is a direct regression. The change-log
  documents the fix-pass; the fix did not actually land in the abstract.

### 1.5 — 🟡 REQUIRED — Eight+ project-side first-formalisation sites remain

- **Gate:** NarrativeGrounding (Gate 7) / FirstClaimVerification (Gate 10)
- **Locations:**
  - `paper_draft.tex:1097` — "five algebraic-Lorentzian-geometry
    first-formalisation appendices"
  - `paper_draft.tex:1098` — "I1 §10 ships these as the primary
    first-formalisation claim"
  - `paper_draft.tex:1101` — "the first-formalisation claims are flagged
    'to our knowledge'..."
  - `paper_draft.tex:1216` — subsection title "First-formalisation
    claims"
  - `paper_draft.tex:1218` — "D4 ships five first-formalisation claims,
    each hedged with 'to our knowledge'..."
  - `paper_draft.tex:1238` — "Doublon-SWAP gate as the substrate's
    *first* symmetry-protected topological quantum gate"
  - `paper_draft.tex:1240-1242` — "To our knowledge there is no prior
    published topological quantum gate of SPT type in proof-assistant
    form."
  - `paper_draft.tex:1580` — subsection title "Algebraic-Lorentzian-
    geometry first-formalisations"
  - `paper_draft.tex:1582` — "I1 §10 is the primary first-formalisation
    claim"
  - `paper_draft.tex:1888-1889` — "Phase 6f / 6g substrate roster
    algebraic-Lorentzian-geometry first-formalisations... primary
    first-formalisation claim"
- **Observed:** `grep -ncE "first.formalisation|first machine-checked|
  first formally verified|to our knowledge" papers/F/paper_draft.tex`
  returns 8 line matches and 10+ distinct first-claim usages once the
  multi-instance lines (e.g. 1097-1101 cluster) are counted.
- **Evidence:** change_log line 16 claims: "8 project-side 'to our
  knowledge ... the first' / 'first machine-checked X' / 'first
  formally verified X' instances fully removed (8 sites across §1, §4,
  §6, §10.4, §11, §13)". The remaining sites span §6 (Algebraic-
  Lorentzian-geometry appendices), §7.2 (D4 first-formalisation claims
  subsection), §9.5 (methodology section), and §11.3 (Phase 6 deferred
  targets) — i.e., the sweep was incomplete.
- **Expected:** Per the task spec's first-claim removal policy: full
  removal of all project-side "first machine-checked X" / "first
  formally verified X" / "first-formalisation" / "to our knowledge ...
  no prior published" instances. Program-history attributions and
  sequence-enumeration ("first of three closures") are acceptable.
- **Fix:** Remove or recast the 10+ sites listed above. The four
  subsection titles ("First-formalisation claims", "Algebraic-
  Lorentzian-geometry first-formalisations") should be renamed in
  particular — title-level first-claims read as the most assertive form.
- **Severity rationale:** REQUIRED rather than BLOCKER because the
  hedging ("to our knowledge") is uniformly applied where the claims
  live, so a reader will not be misled into believing the searches were
  exhaustive. Submission-blocking under the strict reading of the task
  spec's policy ("flag every project-side instance for full removal"),
  but recoverable mechanically.

### 1.6 — 🟡 REQUIRED — Deprecated alias `all_quantitative_bounds_exceed_jeffreys_decisive` cited

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `papers/F/paper_draft.tex:1396`
- **Observed:**
  > "The aggregator
  > \texttt{all\_quantitative\_bounds\_exceed\_jeffreys\_decisive} ships
  > the closure as a single Lean theorem..."
- **Evidence:**
  - `lean/SKEFTHawking/EntropicGravityDarkEnergy.lean:466-472`:
    ```
    @[deprecated all_three_decisive_bayes_bounds_exceed_jeffreys_decisive
      (since := "2026-05-08")]
    theorem all_quantitative_bounds_exceed_jeffreys_decisive :
      verlinde_cmb_bullet_sigma ≥ jeffreys_decisive_threshold ∧
      tsallis_log_bayes ≥ jeffreys_decisive_threshold ∧
      odintsov_log_bayes ≥ jeffreys_decisive_threshold :=
      all_three_decisive_bayes_bounds_exceed_jeffreys_decisive
    ```
  - The theorem name implies a 4-of-4 universalisation but its current
    body only conjoins 3 of 4 (Barrow is excluded; he lives in a
    separate AIC-only aggregator). The honest theorem name is
    `all_three_decisive_bayes_bounds_exceed_jeffreys_decisive` (the
    new EGDE11 from 2026-05-08 absorption session 5).
- **Expected:** Cite either the new EGDE11 name (most informative for
  readers) or, if cross-bundle citation continuity matters, cite the
  deprecated alias with an explicit note that it now contains a
  3-conjunct body matching the renamed theorem.
- **Fix:** Replace line 1396's
  `all\_quantitative\_bounds\_exceed\_jeffreys\_decisive` with
  `all\_three\_decisive\_bayes\_bounds\_exceed\_jeffreys\_decisive`.
  If the additional Barrow-AIC content is desired, add a second citation
  to `all\_quantitative\_bounds\_disfavoured` (the mixed-threshold
  4-of-4 aggregator).

### 1.7 — 🟡 REQUIRED — `T_H = 0.351(4) nK` lacks PARAMETER_PROVENANCE entry

- **Gate:** ParameterProvenance (Gate 3)
- **Location:** `papers/F/paper_draft.tex:579`
- **Observed:**
  > "The Heidelberg measurement $T_H = 0.351(4)\,\mathrm{nK}$
  > \cite{deNova2019} is the substrate's quantitative anchor in the
  > BEC platform."
- **Evidence:**
  - `grep -nE "T_H_BEC|deNova2019|0\.351|351.*pK"
    src/core/provenance.py` returns no PARAMETER_PROVENANCE entry
    keyed to this measurement.
  - `CITATION_REGISTRY['deNova2019']` exists; only the bibitem is
    registered.
- **Expected:** Per Pipeline Invariant #8: "Every experimental
  parameter has verified provenance — traced to a published source via
  PARAMETER_PROVENANCE in src/core/provenance.py."
- **Fix:** Add a `T_H_BEC_Heidelberg` (or similarly keyed) entry to
  `PARAMETER_PROVENANCE` citing de Nova 2019 with the table/figure
  number; verify the value and add `llm_verified_date` /
  `human_verified_date` fields. Cross-bundle: D1 likely has the same
  parameter and the entry will service both papers.
- **Severity rationale:** REQUIRED (the measurement is from the
  primary source and is being quoted, not predicted; the integrity gap
  is provenance-tracking discipline rather than scientific drift).

### 1.8 — 🔵 RECOMMENDED — "in flight" / TODO LaTeX-comment residue

- **Gate:** NarrativeGrounding (Gate 7) — anti-placeholder discipline
- **Location:** `papers/F/paper_draft.tex:32-49`
- **Observed:** The LaTeX comment block at lines 32-49 is a 17-line
  pre-abstract commentary block containing:
  - Line 32: "%% TODO: F abstract is the 13-bundle synthesis statement.
    Substantive content lift awaits all-12-siblings-GREEN gate."
  - Lines 33-48: full prose draft of the synthesis claim
- **Evidence:** The block is LaTeX comments (`%%` prefix); it does not
  render in the compiled PDF.
- **Expected:** Per the anti-placeholder discipline cited in the task
  spec: "tracked separately / provisional name / in flight residue" is
  flagged. TODO markers in comments inside a paper that is moving toward
  submission are a stale-bookkeeping signal even if they don't reach
  the reader.
- **Fix:** Either delete the comment block or replace the stale "TODO"
  with a "history note" that documents the synthesis-claim's lineage
  without implying outstanding work.
- **Severity rationale:** RECOMMENDED (doesn't reach the compiled PDF;
  bookkeeping-cleanup advisory).

### 1.9 — 🔵 RECOMMENDED — `Akama1979` bibitem date mismatch

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `papers/F/paper_draft.tex:2119-2122`
- **Observed:**
  ```
  \bibitem{Akama1979}
  K.~Akama,
  "An attempt at pregeometry: gravity with composite metric,"
  Prog.\ Theor.\ Phys.\ \textbf{60}, 1900 (1978).
  ```
- **Evidence:** Bibkey says "1979" but the year field in the bibitem
  says "1978". Prog. Theor. Phys. vol. 60 was indeed published in
  1978 (October-December); the bibkey appears to be off by one.
- **Expected:** Either bibkey `Akama1978` with year 1978, or bibkey
  `Akama1979` with year 1979 (whichever the CITATION_REGISTRY
  entry has). Cross-bundle: D3 likely cites Akama as well; the choice
  must be consistent across bundles per Gate 2.
- **Fix:** Verify CITATION_REGISTRY['Akama1979'] year field and align.
  Quick fix if registry year is 1978: rename bibkey to Akama1978
  across all 13 bundles.
- **Cache:** registry-resolved (CITATION_REGISTRY['Akama1979'] present;
  did not fetch primary source for this re-invocation given the
  finding is cosmetic).

### 1.10 — 🔵 RECOMMENDED — Bundle E1/E2 references in §10 "Cleared register" are projections

- **Gate:** NarrativeGrounding (Gate 7) — feasibility-claim grounding
- **Location:** `papers/F/paper_draft.tex:1654-1662`
- **Observed:** §10 "Cleared register" lists both the polariton
  stimulated-Hawking gain and the graphene Dirac-fluid analog
  Hawking as "Cleared" (within published experimental band), but
  Bundle E1 and Bundle E2 are companion **experimental letters with
  projected device parameters**, not measurements.
- **Evidence:** F line 1849-1850 itself notes "The Tier-4 experimental
  letters (E1, E2) ship with the D1 deep paper as companion content."
  No measurements have been reported on either platform; the
  predictions are forward-looking.
- **Expected:** "Cleared" partition is for predictions agreeing with
  observation. The polariton gain and graphene $T_H$ are predictions
  awaiting observation, not cleared predictions. Either
  (a) Move them to a separate "Predicted / awaiting observation"
  partition, or
  (b) Clarify in §10.1 prose that "cleared" includes "consistent with
  available bounds on substrate parameters" for predicted-not-measured
  quantities.
- **Fix:** Add a fifth partition or a hedging sentence to §10.1.
- **Severity rationale:** RECOMMENDED — the substrate register's
  4-partition framing is genuinely useful but the boundary partition
  taxonomy needs sharpening to admit "predicted / not yet measured".

### 1.11 — 🔵 RECOMMENDED — Eight cleared-vs-falsified counts in §1.3 and §10 don't tile completely

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `papers/F/paper_draft.tex:160-208` (§1.3) and
  `:1626-1788` (§10 register)
- **Observed:** The 4-partition framing of §1.3 (cleared / falsified /
  structurally blocked / reproduced) is mirrored in §10's register
  layout. But the abstract (lines 50-83) does not explicitly preview the
  4-partition; it lists examples in narrative form. Readers arriving at
  §1.3 then §10 see the formal partition for the first time; this is a
  flagship-paper UX advisory, not a substantive defect.
- **Expected:** A single-sentence partition-preview in the abstract
  (e.g., "Predictions partition into cleared, falsified, structurally
  blocked, and reproduced-not-solved categories") would make the
  flagship's "predictive register at the boundary partition"
  organising-claim load-bearing from sentence 1.
- **Fix:** Optional abstract polish.
- **Severity rationale:** RECOMMENDED — UX advisory, not load-bearing.

## Verdict rationale

- 4 BLOCKER findings (1.1-1.4) are submission-blocking and span 3
  different gates (CitationIntegrity / LeanProofSubstance / Narrative
  Grounding / CrossPaperConsistency). The re-lift introduced or failed
  to fix all four:
  - 1.1 (`Z16Classification.dai_freed_spin_z4` wrong namespace): not
    addressed by the re-lift; the wrong-namespace text was present in
    the prior draft per round-2 review (RECOMMENDED 1.3, citation
    registry hygiene carry-forward) and remains in the current draft.
  - 1.2 (`dai_freed_spin_z4` structural tautology): the re-lift focus
    was on Lean-substance fixes (DoublonGate→FermiHubbardDimer,
    wen_adw→coupling_deficit). A parallel substance-check of the
    Spin^Z4 anchor was not performed.
  - 1.3 (`coupling_deficit` misrepresentation): introduced by the
    re-lift's §4 substitution itself. The change-log claims the
    substitution is substantive; it is, but the prose now claims the
    new theorems certify a 1/6000 Newton-constant ratio when they
    actually certify a 1/1000 four-fermion-coupling ratio.
  - 1.4 (abstract universal-Bayes overclaim): direct regression. The
    change-log explicitly listed §1 line ~76 as needing the
    mixed-threshold downgrade. The change did not land in the abstract
    sentence; only landed in §1.3 (lines 184-187), §2.3 (367-377),
    and §10 register (1721-1726).

- 3 REQUIRED findings (1.5-1.7) are not BLOCKERs but block submission:
  - 1.5 (8+ first-formalisation sites): mechanical sweep incomplete.
  - 1.6 (deprecated-alias citation): cite the renamed theorem
    instead.
  - 1.7 (`T_H_BEC` provenance gap): add the provenance entry.

- 4 RECOMMENDED findings (1.8-1.11) are advisories.

**Verdict:** **BLOCKED with new BLOCKERs.** Bundle F regressed from
GREEN at 2026-05-04 to RED at 2026-05-11. The re-lift was substantively
incomplete on its own stated goals (mixed-threshold downgrade missed
the abstract; first-claim sweep missed 8+ sites) and uncovered two
pre-existing latent issues (`dai_freed_spin_z4` structural tautology
and wrong-namespace citation) that the prior round-2 review missed.

Per the task spec: "Paper cannot advance to submission until every
BLOCKER has status: fixed AND a re-invocation shows no new BLOCKER
findings." A third Stage-13 round will be required after these fixes
land.

## Findings summary

| Severity     | Count | Notes                                          |
|--------------|------:|------------------------------------------------|
| BLOCKER      |     4 | 1.1 wrong-namespace; 1.2 dai_freed structural; 1.3 coupling_deficit misrep; 1.4 abstract regression |
| REQUIRED     |     3 | 1.5 first-claim residue; 1.6 deprecated alias; 1.7 T_H provenance gap |
| RECOMMENDED  |     4 | 1.8 TODO comment; 1.9 Akama year; 1.10 cleared partition; 1.11 abstract partition preview |
| **Total**    |    11 |                                                |

## Carry-forward disposition (from 2026-05-04 review)

The 2026-05-04 round-2 review documented 4 advisory carry-forwards:

| 2026-05-04 carry-forward | Status this re-invocation |
|---|---|
| REQUIRED 1.2 wen_adw_factor_6000 | **REOPENED as BLOCKER 1.3** — re-lift's substitution misrepresents Lean content |
| RECOMMENDED 1.1 (92%-reuse precision) | Carry forward (not in scope this re-invocation) |
| RECOMMENDED 1.3 (citation registry hygiene) | Carry forward + **NEW BLOCKER 1.1 wrong namespace** related to it |
| RECOMMENDED 1.4 (§10 tracked-hypothesis disclosure) | Carry forward |
| RECOMMENDED 1.5 (per round-1 note) | Carry forward |

## QI Candidate

**Systemic issue surfaced:** The 2026-05-11 re-lift sweep used
`scripts/bundle_append.py` (per `append_log.json` and `change_log.md`)
to apply sibling-bundle corrections to F. The sweep applied the
substantive fixes (DoublonGate→FermiHubbardDimer, etc.) but did NOT
verify two things:

1. **Abstract vs. body consistency.** The change-log claimed §1 line ~76
   was downgraded to mixed-threshold but only landed the change in
   §1.3, §2.3, and §10 register — not the abstract sentence at line 76.
   A QI check should be added: when a sweep claims to update multiple
   sections, all listed sites must be diff-verified.

2. **Lean-citation substance.** The §4 substitution
   (wen_adw_factor_6000 → coupling_deficit + coupling_ratio_small) was
   purely a name swap; the prose continued claiming a 1/6000
   Newton-constant ratio, but the new theorems only certify a 1/1000
   coupling ratio. A QI check should be added: when a Lean theorem
   citation is updated, the surrounding prose's substantive claims
   must be re-checked against the new theorem's actual statement.

Both QI candidates fall under Gate 7 (NarrativeGrounding) /
Gate 5 (LeanProofSubstance) and could be implemented as a new
`validate.py --check bundle_relift_substance_consistency` rule that
diffs prose-claim numerics against citation-target statement bodies.

A third QI candidate (less load-bearing): the abstract's
`8/8 ... thresholds exceeding decisive` phrasing pattern should be
banned at lint level after the 2026-05-08 mixed-threshold honest
downgrade. A `validate.py --check abstract_body_numerical_consistency`
check (suggested by the 2026-05-07 absorption session 4 close memo)
would catch this class of regression automatically.
