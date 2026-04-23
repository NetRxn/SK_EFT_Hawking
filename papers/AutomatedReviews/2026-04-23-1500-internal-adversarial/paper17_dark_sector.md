---
paper: paper17_dark_sector
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-23T15:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper17_dark_sector

## Summary

Paper 17 synthesizes Phase 5x dark-sector work into a submission-length PRD
draft citing ~24 Lean theorems across 7 modules. The review surfaces 14
findings: **4 BLOCKER, 6 REQUIRED, 4 RECOMMENDED**. Gates impacted: Gate 1
(CitationIntegrity — 30/32 bibkeys missing from registry; one wrong-target
arXiv; one cross-paper bibkey collision), Gate 2 (CrossPaperConsistency —
`Paper8` bibkey resolves to different papers in paper7 vs paper17), Gate 5
(LeanProofSubstance — multiple cited theorems are `rfl` on author-hardcoded
constants or `decide` on author-hardcoded lookup tables, giving the veneer
of verification without the content), Gate 9 (NumericalFreshness — 11
inline count-literals, stale totals). Paper is **NOT submission-ready**:
BLOCKERs in Gates 1, 2, 5 must clear first. Citation cache stats: 1 total
records (schema only — 0 verifications). All 32 bibkeys had to be
fresh-fetched for this review.

## Findings

### 1.1 — 🔴 BLOCKER — `Glodkowski2024` citation is wrong-target

- **Gate:** CitationIntegrity
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:666`
- **Observed:** Bibitem reads `P.~G{\l}{\'o}dkowski \textit{et~al.}, arXiv:2406.12345 (2024).`
  Cited in text (L88, L263) as the p-wave-dipole-superfluid thermodynamic stability paper.
- **Evidence:** `arXiv:2406.12345` resolves to "Navigating Knowledge Management
  Implementation Success in Government Organizations: A type-2 fuzzy
  approach" by Foroutani, Fahimian, Jalalinejad, Hezarkhani, Mahmoudi,
  Gharleghi (submitted 2024-06-18). This is a public-administration /
  operations-research paper, not condensed matter. Fresh-fetch 2026-04-23.
- **Expected:** The Głódkowski et al. paper on dipole superfluids / fracton
  thermodynamic stability in `d ≥ 3` at `T > 0` (used as part of the
  p-wave-resolves-Krishna-no-go argument in §\ref{sec:fracton}).
- **Fix:** Locate the actual Głódkowski et al. arXiv ID via INSPIRE-HEP
  or the W7b Drilldown memo; update bibitem; add registry entry in
  `src/core/citations.py`.
- **Cache:** fresh-fetch

### 1.2 — 🔴 BLOCKER — 30 of 32 bibkeys absent from `CITATION_REGISTRY`

- **Gate:** CitationIntegrity
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:635-669` vs
  `src/core/citations.py`
- **Observed:** Only `Unruh1981` and `Diakonov2011` are present in
  `CITATION_REGISTRY`. Missing (30): `Visser1998, CGL2017a, CGL2017b,
  Volovik2006, KV2008, Lean4, Mathlib, Wan2019, Wang2020, Wang2021,
  Garcia-Etxebarria2019, ADW2019, BK2015, BK2025, BKWang2017, DESI2024,
  DESI2025, Sola2023, VanWaerbeke2025, Planck2018, FangGu2021, Pretko2017,
  Nandkishore2019, Shen2022, Krishna2024, Kapustin2022, Jensen2024,
  Glodkowski2024, Feistl2026, Paper8`. Per READINESS_GATES.md Gate 1 spec,
  registry absence is itself a blocker — the registry is how the
  pipeline tracks what has been verified.
- **Evidence:** `grep -E "^\s*'(<bibkey>)'" src/core/citations.py` returns
  only `Unruh1981` and `Diakonov2011`.
- **Expected:** Every bibkey in the `.tex` with a matching
  `CITATION_REGISTRY` entry carrying `arxiv_verified == True` AND
  `doi_verified == True`.
- **Fix:** Add all 30 bibkeys to `src/core/citations.py` with verified
  arXiv/DOI metadata; run Gate 1 evaluator afterwards.
- **Cache:** fresh-fetch (no prior cache entries)

### 1.3 — 🟡 REQUIRED — `BK2025` page count disagrees with arXiv metadata

- **Gate:** CitationIntegrity
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:376, 598`
- **Observed:** Paper prose states "BK 2025 Physics Reports review --
  118~pages -- contains no quantitative merger forecast" (L376) and
  similar in Discussion (L598). Bibitem `BK2025` (L652) cites
  `arXiv:2505.23900`.
- **Evidence:** arXiv:2505.23900 metadata comments field: "136 pages,
  12 figures." (Fresh-fetch 2026-04-23.) 118 vs 136 is an 18-page
  discrepancy — not a rounding difference.
- **Expected:** Paper should state the actual page count (136), or the
  published Phys. Rep. pagination if that differs. If citing a
  pre-print version with 118 pages, cite that version specifically.
- **Fix:** Change "118~pages" to "136~pages" (or to verified Phys.
  Rep. pagination). Update the BK gap narrative if the larger page
  count means the quantitative-merger claim needs to be recomputed.
- **Cache:** fresh-fetch

### 1.4 — 🔵 RECOMMENDED — Bibitems lack arXiv IDs where available

- **Gate:** CitationIntegrity
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:635-669`
- **Observed:** 16 bibitems cite only journal (volume, page, year) with no
  arXiv ID, even for papers that are indexed on arXiv: `Unruh1981`,
  `Visser1998` (arxiv gr-qc/9712010 verified), `CGL2017a`, `CGL2017b`,
  `Volovik2006`, `KV2008`, `Lean4`, `Mathlib`, `Wan2019`, `Wang2020`,
  `Wang2021`, `Garcia-Etxebarria2019`, `ADW2019`, `Diakonov2011`,
  `BK2015` (arXiv:1507.01019 verified), `BKWang2017`, `Planck2018`,
  `Pretko2017`, `Nandkishore2019`, `Shen2022`, `Krishna2024`,
  `Kapustin2022`, `Jensen2024`.
- **Evidence:** arXiv-confirmed lookups: Visser1998 → gr-qc/9712010;
  BK2015 → 1507.01019; VanWaerbeke2025 → 2506.14182.
- **Expected:** Bibitems include the arXiv ID alongside the journal
  citation so Gate 1 verification can run automatically on every
  future review.
- **Fix:** Augment each bibitem with `arXiv:<id>.` Populate
  `CITATION_REGISTRY` entries with matching `arxiv` field.
- **Cache:** partial

### 2.1 — 🔴 BLOCKER — `Paper8` bibkey points to two different papers

- **Gate:** CrossPaperConsistency
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:668` and
  `papers/paper7_chirality_formal/paper_draft.tex:375-378`
- **Observed:**
  - paper17 L668: `\bibitem{Paper8} SK-EFT Hawking Program, Paper~8, FractonNonAbelian formalization (2025).`
  - paper7 L375-378: `\bibitem{Paper8} J.~Roehm, ``The Chirality Wall: A Three-Pillar Formal Verification Survey in Lean~4'' (2026), companion paper.`
  The same bibkey resolves to different titles, different authors, and
  different topics. paper17 uses `Paper8` to cite the fracton-non-Abelian
  formalization; paper7 uses it for the chirality-wall survey.
- **Evidence:** Direct grep of `\bibitem{Paper8}` across all `papers/paper*_*/paper_draft.tex`.
- **Expected:** One bibkey → one paper. If both papers want to reference
  two different companion works, use distinct keys (e.g. `Paper8Fracton`
  vs `Paper8Chirality`, matching the internal numbering of the project).
- **Fix:** Rename `Paper8` to disambiguated key in one or both files; add
  both entries to `CITATION_REGISTRY` with distinct metadata. Verify no
  other cross-paper reuse of this bibkey.
- **Cache:** cross-reference check, no external fetch

### 2.2 — 🔵 RECOMMENDED — Paper 17 is the sole citer of 4 high-impact dark-sector bibkeys

- **Gate:** CrossPaperConsistency
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:635-669`
- **Observed:** `BK2015, BK2025, Wan2019, KV2008, Volovik2006` are cited
  only in paper17 across the 17-paper series. Given the project's
  extensive use of Volovik tetrad-condensation arguments in paper 5
  (adw_gap) and paper 6 (vestigial), absence of KV/Volovik bibkeys in
  those companions is surprising.
- **Evidence:** `grep -l` across `papers/paper*_*/paper_draft.tex`.
- **Expected:** Either companion papers share these bibkeys (which would
  force consistency checks) or they cite the same works under different
  names (which is a naming inconsistency that the registry prevents).
- **Fix:** During registry population (finding 1.2), audit paper 5 and
  paper 6 for references to Volovik / KV / Klinkhamer that should use
  the same bibkey. Non-blocking but worth the sweep.
- **Cache:** cross-reference check

### 3.1 — 🟡 REQUIRED — No `PARAMETER_PROVENANCE` entries found for paper-17-specific parameters

- **Gate:** ParameterProvenance
- **Location:** `papers/paper17_dark_sector/paper_draft.tex` throughout,
  esp. §\ref{sec:sfdm-merger}
- **Observed:** Paper uses numerical parameters
  `m_DM = 0.6 eV, Λ = 0.2 meV, c_s = 1525 km/s` (BK fiducial L304);
  `v_infall` values 2700, 2500, 3400, 2300, 2000 km/s (L308 and Lean
  file `SFDMMergerForecast.lean`); merger Mach numbers 1.77, 1.64, 2.23,
  1.51, 1.31; condensate fraction `f_c = 0.59` (L322); shock extent
  `Δr = 400 kpc` (L343); Σ_cr from `D_L = 830 Mpc` (L342); Single-cluster
  SNR `0.83` (Euclid Bullet, L346) and `1.03` (Roman Bullet, L347).
  I did not find explicit `PARAMETER_PROVENANCE` entries for these in
  `src/core/provenance.py` (not run — but grep on `paper17|dark_sector`
  in provenance.py returned nothing).
- **Evidence:** `grep -nE "paper17|dark_sector" src/core/provenance.py`
  returned no results.
- **Expected:** Each experimental parameter the paper uses has a
  `PARAMETER_PROVENANCE` entry with an `llm_verified_date` (for draft)
  and `human_verified_date` (for submission).
- **Fix:** Add provenance entries for the BK fiducial parameters
  (source: BK2015 and BK2025) and the five canonical merger
  kinematics (sources: per-cluster observational papers). Run Gate 3
  evaluator to confirm.
- **Cache:** N/A

### 3.2 — 🟡 REQUIRED — `T_dS = 2 · T_GH` numeric interpretation is author-opinion, not measurement

- **Gate:** ParameterProvenance
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:205-214`
- **Observed:** Paper states "`ρ_vac^{1/4} ≈ (few) × T_dS ≈ 2.8 meV`"
  vs observed `(2.3 meV)^4`, "agreement at the 20% level", and claims
  this is "unprecedented for a non-tuned CC mechanism." The "(few)"
  multiplier is an undisclosed fit parameter; 20% is a ratio on fourth
  powers, meaning the underlying linear-scale agreement is ~5% — but
  the constant `(few)` is tunable. The 2.8 meV value has no primary
  source referenced.
- **Evidence:** `CosmologicalConstant.lean` explicitly defers the
  numerical T3 identity to Phase 6 (L21-23: "the specific numerical
  identity requires a particular V_eff parameterization and is deferred
  pending full ADW renormalization infrastructure").
- **Expected:** Paper either sources `(few) × T_dS ≈ 2.8 meV` to a
  specific deep-research calculation with error bars, or softens the
  "20% agreement" claim to honestly reflect the tuning freedom.
- **Fix:** Cite `docs/dark_sector/W3_*.md` with the specific
  computation of `(few)`. If there isn't one, weaken the narrative to
  "within an order of magnitude" or explicitly label as a Phase-6
  numerical target.

### 5.1 — 🔴 BLOCKER — `fracton_bullet_sigma_zero` is `rfl` on an author-hardcoded constant

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:244` cites
  the Bullet-cluster compatibility. Related theorem:
  `lean/SKEFTHawking/FractonDarkMatter.lean:234`.
- **Observed:**
  ```
  def sigma_eff_isolated_fracton : ℝ := 0
  theorem fracton_bullet_sigma_zero : sigma_eff_isolated_fracton = 0 := rfl
  ```
  The "theorem" is `0 = 0 := rfl`. Paper's §\ref{sec:fracton} claim
  "σ_eff = 0 because fracton dipoles cannot interact at a distance"
  is backed by a definition (not derivation) of the symbol to zero.
  Its sister `fracton_cosmo_dust_pressureless` (L266) is the same
  pattern: `def eos_fracton_dust : ℚ := 0; theorem ... = 0 := rfl`.
  §Formal-Verification summary (L530-532) lists both as Phase 5x
  "structural" Lean theorems.
- **Evidence:** Direct read of `FractonDarkMatter.lean` L226-267.
- **Expected:** A genuine derivation of σ_eff from the fracton dipole
  algebra (Pretko 2017), or honest labeling in the paper — "definition
  of fracton effective cross-section" rather than "verified theorem."
  Paper's honesty table (L557-571) does not separate these out; they
  are listed as "Derived."
- **Fix:** Either (a) prove σ_eff = 0 from dipole-conservation + locality
  in Lean (genuine derivation), or (b) demote `fracton_bullet_sigma_zero`
  and `fracton_cosmo_dust_pressureless` to `def`-level
  "labeled-constants" and amend the paper's honesty table to move
  "σ_eff = 0 from dipole conservation" from Derived to Heuristic.
- **Cache:** N/A

### 5.2 — 🔴 BLOCKER — `phase5x_candidates_viability_matrix` is a consistency check on hardcoded flags

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:290`
  (Fig. caption Lean citation). Theorem:
  `lean/SKEFTHawking/DarkSectorSynthesis.lean:483-494`.
- **Observed:** Each `DarkSectorCandidate` record has `basic_viability : Bool`
  defined by hand in its constructor (L461-470):
  ```
  def candidate_T0 : DarkSectorCandidate := ⟨.Z16Topological_T0, true⟩
  def candidate_FG : DarkSectorCandidate := ⟨.FGTorsion, false⟩
  ...
  ```
  Then `phase5x_candidates_viability_matrix` (L483-494) proves the flag
  values match the declared flags via `decide`. The theorem verifies
  nothing about the physics — it verifies that the author typed
  `true, true, true, false, true`. Paper's Fig. 108 and abstract ("every
  Phase 5x dark-matter candidate is Standard-Model gauge singlet")
  rely on this as a machine-verified structural fact.
- **Evidence:** Direct read of `DarkSectorSynthesis.lean` L453-494.
- **Expected:** A `basic_viability` *predicate* that computes viability
  from physical inputs (SM-singlet via FractonNonAbelian, no
  direct-detection signal via σ_DD bound, etc.), with the theorem
  proving the predicate holds for each candidate from their physical
  data. Alternatively, demote to `def` and adjust paper claims.
- **Fix:** Refactor `basic_viability` to a `Prop`-valued predicate
  closed under the physical conditions listed in the docstring (L448-452),
  or weaken the paper's language (remove "Lean:
  phase5x_candidates_viability_matrix" from Fig. 108 caption).
- **Cache:** N/A

### 5.3 — 🔴 BLOCKER — `emergent_gravity_dm_invisible_collective` is `decide` on author-hardcoded lookup

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:483-485`
  ("collective-invisibility theorem ... gives log10 σ_DD ≤ -50 for every
  one of the five candidates"). Theorem:
  `lean/SKEFTHawking/DarkSectorSynthesis.lean:258-261`.
- **Observed:**
  ```
  def direct_detection_sigma_log10_cap : EmergentGravityDMKind → ℤ
    | .Z16Topological_T0 => -999
    | .Z16Singlet_S0     =>  -50
    | .Z16Mixed_C1       =>  -50
    | .FGTorsion         =>  -90
    | .FractonPWave      => -999
  theorem emergent_gravity_dm_invisible_collective
      (k : EmergentGravityDMKind) :
      direct_detection_sigma_log10_cap k ≤ -50 := by cases k <;> decide
  ```
  The "theorem" asks Lean to confirm `max(-999,-50,-50,-90,-999) ≤ -50`.
  It is arithmetic on hardcoded integers chosen by the author. The
  paper's Discussion (L589) claims "every candidate in our program is
  precisely predicted to be invisible to direct detection."
- **Evidence:** Direct read of `DarkSectorSynthesis.lean` L245-261.
- **Expected:** Either a derivation of each σ_DD bound from the
  underlying physics (Z16 gauge-singlet ⇒ no local-operator coupling ⇒
  σ_DD bound), or honest labeling in paper's honesty table that the
  "σ_DD ≤ 10^-50 cm² for each candidate" entry is a *classification*
  of deep-research-derived bounds, not a derivation.
- **Fix:** Same structural options as 5.1 / 5.2 — either upgrade the
  theorem to a genuine derivation, or amend the paper's claim.
- **Cache:** N/A

### 5.4 — 🟡 REQUIRED — `torsion_channels_distinct_sources_distinct` is enum-distinctness, not Lorentz-irrep physics

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:429-430`
  ("`torsion_channels_distinct_sources_distinct`, Wave 8"). Theorem:
  `lean/SKEFTHawking/DarkSectorSynthesis.lean:429-432`.
- **Observed:**
  ```
  def channel_of_source : TorsionSource → TorsionChannel
    | .DiracAxial  => .Antisymmetric
    | .FGLoopTheta => .Trace
    | .NoSource    => .PureTensor
  theorem ... {s₁ s₂} (h : s₁ ≠ s₂) : channel_of_source s₁ ≠ channel_of_source s₂
  ```
  The "theorem" verifies that a hand-coded injective function is
  injective. The paper's L424-427 docstring honestly notes "This
  definition encodes the physics identification step — ... if a later
  extension of FG to coupled-fermion-plus-loop condensation changes
  this, the definition and downstream theorems update accordingly."
  But the paper's honesty table (L560) lists "Two-torsion-channel
  orthogonality" as "Derived" — which over-claims.
- **Evidence:** Direct read of `DarkSectorSynthesis.lean` L395-432.
- **Expected:** Either a derivation of the channel identification from
  the Dirac-axial-current tensor + FG loop-θ tensor (Boos-Hehl 2019 and
  FG 2021) decomposed into Lorentz irreps, or a softer paper claim
  ("Identified: the two sources are placed in distinct channels per
  Boos-Hehl and FG; downstream orthogonality follows.").
- **Fix:** Move "Two-torsion-channel orthogonality" from Derived to
  Derived (taxonomy) in the honesty table, or prove the channel
  identification from the underlying tensor decomposition.
- **Cache:** N/A

### 5.5 — 🟡 REQUIRED — `empirical_hook_ranking_strict` verifies hand-chosen priorities

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:477`
  (Fig. caption) and L490 ("decidable in Lean via `hook_priority` and
  `empirical_hook_ranking_strict`"). Theorem:
  `lean/SKEFTHawking/DarkSectorSynthesis.lean:521-535`.
- **Observed:**
  ```
  def hook_priority : EmpiricalHook → ℕ
    | .MergerSonicBoom    => 5
    | .FractonCoreCusp    => 4
    | .EPViolationSTEP    => 3
    | .DESIDeR3           => 2
    | .DirectNuclearRecoil => 1
  theorem empirical_hook_ranking_strict : (5 = 4+1) ∧ (4 = 3+1) ∧ ...
  ```
  Same pattern: `decide` on hand-assigned integers. The "ranking" is
  what the author wrote, not what a detectability or timeline score
  produces. Paper cites this as "Lean:
  `empirical_hook_ranking_strict`" in Fig. 109 and "Order is decidable
  in Lean" in Table 1.
- **Evidence:** Direct read of `DarkSectorSynthesis.lean` L505-535.
- **Expected:** Either derive the priority from a physics-motivated
  score (e.g. a `detectability(hook) : ℝ` computed from Euclid/Roman
  S/N, DESI DR3 tension, STEP sensitivity, DARWIN floor) with the
  theorem proving the ordering from that score, or demote to a
  descriptive enum and remove the "Derived" claim from the honesty
  table (L562 "Merger sonic boom is the top-ranked hook").
- **Fix:** Same options as 5.4.
- **Cache:** N/A

### 5.6 — 🔵 RECOMMENDED — `lambda_magnitude_ratio_exact` is cited in §\ref{sec:adw-cc} but proves only `T/T = 1`

- **Gate:** LeanProofSubstance
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:215-216`
  ("Cross-reference: `T_dS_double_TGH` and `lambda_magnitude_ratio_exact`
  in `CosmologicalConstant.lean`"). Theorem:
  `lean/SKEFTHawking/CosmologicalConstant.lean:214-219`.
- **Observed:** Theorem body: `lambda_magnitude_ratio T T = 1`, i.e.
  the ratio of T-to-itself to the fourth power is 1. This says
  nothing about the ADW/Volovik `Λ`-magnitude. Paper cites it
  alongside `T_dS_double_TGH` as support for the 2.8 meV vs 2.3 meV
  20%-agreement claim (L213). A reader would expect the cited theorem
  to be relevant to the 20%-agreement claim; it is not.
- **Evidence:** Direct read of `CosmologicalConstant.lean` L199-219.
- **Expected:** The cross-reference should point to the theorem that
  actually formalizes the `Λ`-magnitude ratio `(T_dS/T_obs)^4` and
  establishes its positivity / behavior; `lambda_magnitude_ratio_pos`
  (L203-206) is a candidate but is not what the paper cites.
- **Fix:** Change the cross-reference to `lambda_magnitude_ratio_pos`
  (positivity from Tp, To > 0) which at least states the ratio is
  well-defined. Or remove the Lean cross-ref from this paragraph and
  acknowledge the magnitude claim is heuristic (which the honesty
  table L567 already does).
- **Cache:** N/A

### 6.1 — 🟡 REQUIRED — Hypothesis `H_MixedChannelZ16Cancels` is load-bearing for C-1 viability but not named in prose

- **Gate:** AssumptionDisclosure
- **Location:** Paper `papers/paper17_dark_sector/paper_draft.tex:145-149`
  (C-1 Wan-Wang classification) cites `c1_wan_wang_joint_constraint`
  as shipped. Theorem signature:
  `lean/SKEFTHawking/HiddenSectorMixedCharge.lean:222-226`.
- **Observed:** The theorem takes a Z16Indexing `φ` and a hypothesis
  `h_mix : H_MixedChannelZ16Cancels φ c1_wan_wang`. In other words,
  the cancellation mechanism that makes C-1 viable is a tracked
  hypothesis, not proved. Paper says "C-1: Wan-Wang mixed-charge
  completion with a dark SU(3); shipped in Wave 2b Track X as
  `c1_wan_wang_joint_constraint`" (L148-149) — no mention that this
  is conditional on `H_MixedChannelZ16Cancels`.
- **Evidence:** `HiddenSectorMixedCharge.lean` L204 documents that
  "(a) of the joint constraint (Z16 cancellation via the Wan-Wang
  Z16 ⊕ Z4 mechanism) is stated as the tracked hypothesis
  `H_MixedChannelZ16Cancels c1_wan_wang`."
- **Expected:** Paper §\ref{sec:z16} prose acknowledges that C-1
  viability depends on an unproved hypothesis of the Wan-Wang Z16 ⊕ Z4
  cancellation mechanism, similar to how §\ref{sec:speculative} treats
  `H_VestigialRelicCarriesZ16Charge`.
- **Fix:** Add a sentence: "C-1 viability is conditional on the
  Wan-Wang Z16 ⊕ Z4 mechanism, tracked as Lean hypothesis
  `H_MixedChannelZ16Cancels` pending the Phase 6 bordism upgrade."

### 7.1 — 🟡 REQUIRED — 11 inline count-literals flagged by `validate.py --check count_literals`

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `papers/paper17_dark_sector/paper_draft.tex`:
  - L46: "22 theorems" (DarkSectorSynthesis — matches actual)
  - L46-47: "30 theorems" (SFDMMergerForecast — STALE: actual 31)
  - L48: "157 modules, 3569 theorems" (STALE: actual 158, 3587)
  - L49: "2172 tests" (not in counts.tex; unverified)
  - L132: "23 theorems" (Z16AnomalyComputation — matches)
  - L184: "21 theorems" (ADWMechanism — matches)
  - L527: "30 theorems" (SFDMMergerForecast — STALE)
  - L534: "22 theorems" (DarkSectorSynthesis — matches)
  - L540-542: "157 modules, 3569 theorems" (STALE: actual 158, 3587)
- **Evidence:** `scripts/validate.py --check count_literals` reports
  "paper17_dark_sector — 11 count-literal matches". Canonical
  `docs/counts.tex` (regenerated 2026-04-23T09:38:06):
  `leanmodules=158, totaltheorems=3587, substantivetheorems=3488,
  placeholdertheorems=99`.
  Per-file theorem grep: SFDMMergerForecast.lean → 31 theorems
  (paper says 30).
- **Expected:** Replace inline literals with macro references:
  `\totaltheorems`, `\leanmodules`, etc., from `\input{../../docs/counts.tex}`;
  add per-module macros for file-level theorem counts, or move to
  `tables/` autogen.
- **Fix:** Run the paper17-specific counts retrofit — follow the
  pattern in papers 1-5 that already use `\input{counts.tex}`.
- **Cache:** N/A

### 7.2 — 🔵 RECOMMENDED — `placeholdertheorems=99` not surfaced in paper's Phase-5x count

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:540-543`
- **Observed:** Paper says "Totals: Phase 5x adds ~80 theorems across 7
  new modules; the full program stands at 157 Lean modules, 3569
  theorems, zero active `sorry`, and a single axiom ..." — does not
  mention that 99 of those theorems are registered as placeholders
  (`True := trivial` or `rfl`-on-hardcoded-constant patterns) per
  `docs/counts.tex`.
- **Evidence:** `docs/counts.tex` L5: `\newcommand{\placeholdertheorems}{99}`.
- **Expected:** If the paper reports total theorems as a mark of formal
  progress, it should also surface the substantive-vs-placeholder
  split. Otherwise the 3569 (→ 3587) figure overstates substantive
  content.
- **Fix:** Add "(of which 3488 substantive, 99 placeholder statements
  tracked for Phase 6+)" or use `\substantivetheorems` macro.

### 8.1 — 🟡 REQUIRED — Paper claims "Monte Carlo evidence" via W6a but no successful ProductionRun is linked

- **Gate:** ProductionRunHealth
- **Location:** `papers/paper17_dark_sector/paper_draft.tex:440-443`,
  L608-610
- **Observed:** Paper's §\ref{sec:speculative} states
  "Vestigial gravity phase relics... are blocked on the W6a Monte
  Carlo extension: `L = 6, 8` data are insufficient to determine the
  transition order." L608-610 notes "the MC extension to `L = 10, 12,
  16` is the gate for the vestigial-relic program." The paper thus
  refers to existing L=6,8 MC data to support "insufficient"
  conclusion.
- **Evidence:** I did not enumerate the `ProductionRun` graph nodes
  (skipping `build_graph.py --json` to avoid toolchain conflict with
  the concurrent Lean session per review instructions). The Hasenbusch
  ergodicity memory note `project_hasenbusch_ergodicity_finding` flags
  that "HS traps at high tet_m2 at L=4 g=3.385" — which, if the L=6,8
  MC runs share this ergodicity concern, strengthens rather than
  weakens the paper's "insufficient" claim, but should be cited.
- **Expected:** Paper should point to `data/vestigial/L6_*.log` /
  `L8_*.log` run IDs, or reference the W6a assessment memo, so a
  reader can trace the "insufficient" claim to a production run.
- **Fix:** Add a citation to the MC-data artifact or the Wave 6a
  memo in §\ref{sec:speculative}. During graph build, ensure
  `ProductionRun` nodes are linked to this paper's claim.

## QI Candidate

### Systematic issue: `rfl`-on-hardcoded-constant theorems escape PlaceholderMarker extractor and get cited as "verified"

The repeating pattern in `DarkSectorSynthesis.lean` and
`FractonDarkMatter.lean`:

1. Author defines a constant by hand: `def sigma_eff_fracton : ℝ := 0`.
2. Author states a theorem identical to the definition:
   `theorem sigma_fracton_zero : sigma_eff_fracton = 0 := rfl`.
3. `PLACEHOLDER_THEOREMS` (content + True-trivial) doesn't flag it
   because the body is `rfl`, not `trivial`.
4. `PlaceholderMarker` extractor in `scripts/build_graph.py` flags
   "`rfl` / `trivial` / `Equiv.refl` bodies" but only when the statement
   is non-trivial. `sigma_eff_fracton = 0` where sigma is literally
   defined as 0 is syntactically non-trivial but semantically vacuous.
5. Paper cites the theorem as if it formalizes a physics fact
   (Bullet-cluster compatibility, SFDM step-function, direct-detection
   invisibility, torsion orthogonality, hook ranking).

This is the semantic-tautology blind spot that the adversarial reviewer
spec explicitly calls out as its primary catch
(`READINESS_GATES.md` Gate 5 block 2: "A cited theorem whose proof is
structurally tautological — semantic check — primary responsibility of
the adversarial reviewer, not the syntactic extractor"). Five independent
instances in one paper:

- `fracton_bullet_sigma_zero` (σ_eff = 0)
- `fracton_cosmo_dust_pressureless` (w = 0)
- `phase5x_candidates_viability_matrix` (hand-assigned Bool flags)
- `emergent_gravity_dm_invisible_collective` (hand-assigned ℤ caps)
- `torsion_channels_distinct_sources_distinct` + `channel_of_source`
  (hand-assigned enum-to-enum mapping)
- `empirical_hook_ranking_strict` + `hook_priority` (hand-assigned ℕ)

**Pattern class:** `constant-eq-constant-rfl` — a theorem whose
statement is `f(c₁) = f(c₂)` or `f(x) ≤ K` where `f` is a finite
lookup table or `def`-level constant the author wrote by hand, and
the proof is `rfl`, `decide`, or `native_decide`. The theorem verifies
"I typed what I said I typed"; it does not verify the physics
content the paper attributes to it.

**Proposed extractor rule:** extend `scripts/build_graph.py`
`extract_placeholder_marker_nodes` to flag any theorem whose RHS is
a literal, whose LHS is a `def` of that literal, and whose proof is
`rfl` / `decide` / `native_decide` — mark as `SemanticTautology`
sub-type of `PlaceholderMarker`. Cross-reference: similar pattern
likely recurs in other Phase 5x papers (papers 15, 16 also synthesize
classification results — audit both).

**Pipeline gap:** Gate 5 currently relies on human / adversarial
catching these. An automated check (even conservative false-positive
heavy) would harden the submission gate. Priority: P1 — this directly
affects the submission-readiness of papers 15, 16, 17 (all three are
synthesis papers).
