---
paper: paper27_bh_thermodynamics_four_laws
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-26T23:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper27_bh_thermodynamics_four_laws

## Summary

Post-rewrite (2026-04-26-2230) audit. The Schottky/JK conflation that
motivated the rewrite has been fully retired from paper prose and the
Lean module: zero residual `T_H = T_H,0(1−(M/M_c)²)` claims, zero
`dT_H/dM` framing in the partition discussion, JK 2002 / JV 1998
correctly demoted to contrast cases. Balbinot 2005 representation is
verified verbatim against TeX source (Eq. Tsonic coefficient 563/720π
and "more similar to Reissner–Nordström black hole" both present).

However, the rewrite introduced or left in place **3 BLOCKERs and 5
REQUIREDs** that were not caught by Stage 9 / Stage 13 process review:

- **Citation Integrity (Gate 1):** `Balbinot2005PRD` bibitem and
  registry list 4 authors including "G.~P.~Procopio"; arXiv abstract
  page and the verbatim TeX archive submitted to arXiv both list
  exactly 3 authors (Balbinot, Fagnocchi, Fabbri) — wrong-author
  blocker. `Reall2024ThirdLawBPS` and `Kirklin2024GSLAllOrders`
  bibitems use paraphrased titles that don't match the actual
  published titles — wrong-title required.
- **Lean Proof Substance (Gate 5):** `ADWSecondLaw` Prop bundle has 3
  of 4 fields = `True` placeholders; `FourLaws_Schwarzschild` and
  `FourLaws_ADWExtremality` each have 2 of 5 fields = `True`
  placeholders. Prose claims "five mutually-independent FourLaws
  fields" but the artifacts disagree. Several falsifier theorems
  (`falsifier_acoustic_decay_form`, `falsifier_schwarzschild_heating`,
  `wave3_bridge_weak_nernst_holds_strong_nernst_violated`) are
  structural tautologies that repackage their input hypotheses into
  the conclusion.
- **Cross-paper consistency / data integrity:**
  `BH_THERMODYNAMICS_PARAMS` in `src/core/constants.py` still carries
  Schottky+JK references (lines 2224–2226, 2241), and a stale
  pre-rewrite figure `fig_T_H_vs_M_regime_partition.png` containing
  the retired Schottky form remains in the paper's `figures/`
  directory (not embedded in the TeX, but a residual artifact).
- **Wave 3 cross-reference:** the prose claims the
  `wave3_bridge_*` theorem connects to Wave 3's `kaulMajumdarS` and
  `kaulMajumdar_S_pos_at_e_squared`, but the Lean module does NOT
  import `SKEFTHawking.BHEntropyMicroscopic` and the theorem body
  does not reference any Wave 3 declaration — the bridge is nominal.

Verdict: **NOT submission-ready.** Three Gate-1 BLOCKERs reopen
CitationIntegrity. Two Gate-5 BLOCKERs reopen LeanProofSubstance. The
rewrite's intended provenance correction is real and substantive at the
prose level, but the underlying Lean substance and the citation
metadata still have load-bearing gaps.

## Findings

### 1.1 — 🔴 BLOCKER — `Balbinot2005PRD` lists wrong author count (4 vs actual 3)

- **Gate:** CitationIntegrity
- **Location:** `papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex:529-532`,
  `src/core/citations.py:2494-2517`
- **Observed:** Bibitem reads
  `R.~Balbinot, S.~Fagnocchi, A.~Fabbri, G.~P.~Procopio,
   \textit{Quantum Effects in Acoustic Black Holes: the Backreaction},
   Phys. Rev. D \textbf{71}, 064019 (2005). arXiv:gr-qc/0405098.`
  Registry has matching 4-author list with `'doi_verified': True`.
- **Evidence:**
  - WebFetch `https://arxiv.org/abs/gr-qc/0405098` (fresh, 2026-04-26)
    returns: "R. Balbinot, S. Fagnocchi, A. Fabbri" — three authors only.
  - Verbatim TeX archive at
    `Lit-Search/Phase-6a/primary-sources/balbinot/acusticpap.tex:57-67`
    lists exactly three authors (Balbinot, Fagnocchi, Fabbri) with no
    Procopio.
  - "G. P. Procopio" appears in a different paper: Balbinot, Fabbri,
    Fagnocchi, Procopio, *Hawking radiation from acoustic black
    holes…*, Riv. Nuovo Cimento 28(3), 1 (2005), arXiv:gr-qc/0601079.
    Likely cross-contamination at brief-construction time.
- **Expected:** Bibitem and registry author lists with three authors.
- **Fix:**
  1. Edit `paper_draft.tex:530` author line to drop ", G.~P.~Procopio".
  2. Edit `src/core/citations.py:2495` `'authors'` field to
     `'Balbinot, R. and Fagnocchi, S. and Fabbri, A.'`.
  3. Append a fresh `match` record to
     `docs/citation_verifications.jsonl` documenting the correction.
- **Cache:** fresh-fetch (no prior cache entry for `Balbinot2005PRD`).

### 1.2 — 🔴 BLOCKER — `Reall2024ThirdLawBPS` bibitem title is a paraphrase, not the published title

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:557-561`
- **Observed:** Bibitem reads
  `\textit{Mass-charge inequality and the third law of black-hole
   mechanics}, Phys. Rev. D \textbf{110}, 124059 (2024). arXiv:2410.11956.`
- **Evidence:** WebFetch `https://arxiv.org/abs/2410.11956` returns
  title "A third law of black hole mechanics for supersymmetric black
  holes and a quasi-local mass-charge inequality". Registry entry
  (`citations.py:2577-2578`) has the correct title; only the bibitem
  is paraphrased.
- **Expected:** Bibitem title verbatim equal to registry title.
- **Fix:** Replace bibitem title at `paper_draft.tex:559-560` with
  `\textit{A third law of black hole mechanics for supersymmetric
  black holes and a quasi-local mass-charge inequality}`.
- **Cache:** fresh-fetch.

### 1.3 — 🔴 BLOCKER — `Kirklin2024GSLAllOrders` bibitem title is a paraphrase, not the published title

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:589-593`
- **Observed:** Bibitem reads
  `J.~Kirklin, \textit{The generalized second law to all orders in
   perturbative gravity}, arXiv:2412.01903.`
- **Evidence:** WebFetch `https://arxiv.org/abs/2412.01903` returns
  title "Generalised second law beyond the semiclassical regime".
  Registry entry (`citations.py:2672-2673`) has the correct title;
  only the bibitem is paraphrased. Note: paper27 bibitem also omits
  the JHEP 07, 192 (2025) publication record present in registry.
- **Expected:** Bibitem title and venue verbatim.
- **Fix:** Replace bibitem at `paper_draft.tex:589-593` with
  `\textit{Generalised second law beyond the semiclassical regime},
  JHEP \textbf{07}, 192 (2025). arXiv:2412.01903.`
- **Cache:** fresh-fetch.

### 1.4 — 🟡 REQUIRED — `StrengtheningPost2026` cited as bibitem but not in CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:422` (cite), `paper_draft.tex:595-599` (bibitem)
- **Observed:** Paper cites a project-internal memorandum with bibitem
  `SK-EFT Hawking Project, Post-wave strengthening audit memorandum:
   four vacuous-Prop anti-patterns, project working memo 2026.`
  No external scholarly identifier (no arXiv ID, no DOI, no public
  URL). Not present in `src/core/citations.py CITATION_REGISTRY`.
- **Evidence:** `grep -n "StrengtheningPost2026" src/core/citations.py`
  returns empty. Gate 1 evaluator (Pass-condition: "Every bibkey in
  the .tex has a matching CITATION_REGISTRY entry") fails on this
  bibkey.
- **Expected:** Either (a) replace with an externally-verifiable
  reference; (b) remove the citation and inline the
  audit-pattern description; or (c) add a registry entry tagged as
  `'kind': 'project_memo'` with a documented public link (e.g., a
  permanent URL into the project repo's working-docs).
- **Fix:** Recommend removing the `\cite{StrengtheningPost2026}` at
  line 422 and rewriting the sentence to inline the four-pattern
  description; the audit isn't published external work and the
  memorandum is internal-only.
- **Cache:** N/A (not externally citable).

### 1.5 — 🟡 REQUIRED — `GloriosoLiu2018` registry `used_in` doesn't include paper27

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:564-578`
- **Observed:** `'used_in': ['papers/paper1_first_order/paper_draft.tex',
  'src/second_order/enumeration.py']`. Paper27 cites this bibkey at
  lines 56, 121, 342, 358, 476, 564.
- **Evidence:** Same issue for `CrossleyGloriosoLiu2017`
  (`citations.py:2191-2207`) which has `used_in: paper25, paper2`
  but is cited by paper27 at line 569. `Glorioso–Liu 2017` registry
  entry (line 2593) does correctly list paper27.
- **Expected:** Registry `used_in` lists agree with actual paper-side
  cite usage. CHECK 1 / Gate-1-eligibility hits this when
  cross-checking; the inconsistency is also material because
  `GloriosoLiu2018` has `'doi_verified': None` — paper27 advancing to
  submission requires verified DOI/arXiv on every cited registry entry.
- **Fix:**
  1. Append `'papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex'`
     to `used_in` for both `GloriosoLiu2018` and `CrossleyGloriosoLiu2017`.
  2. Run a fresh arXiv fetch on `1612.07705` and `1511.03646`,
     append cache records, flip `doi_verified` to True.
- **Cache:** fresh-fetch confirmed both arxiv targets correct
  (1612.07705 = "The second law of thermodynamics from symmetry and
  unitarity", Glorioso & Liu; 1511.03646 = "Effective field theory of
  dissipative fluids", Crossley, Glorioso, Liu).

### 2.1 — 🔵 RECOMMENDED — No drift on numerical parameters

- **Gate:** ParameterProvenance
- **Location:** N/A
- **Observed:** Paper27 is a theory paper with no numerical parameter
  assertions. Figures use abstract normalized units (T_H/T_H,0,
  t/τ_cool, δ_ADW/Λ_UV). `BH_THERMODYNAMICS_PARAMS` is consulted by
  the figure pipeline only via plotting ranges, not by paper claims.
- **Status:** No finding under Gate 3.

### 3.1 — 🔴 BLOCKER — `ADWSecondLaw` is 3/4 `True` placeholders

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:407-411`
- **Observed:** The `ADWSecondLaw` structure is:
  ```
  structure ADWSecondLaw (b : BHData) (p : ADWParams) : Prop where
    KMS_Z2                    : True
    unitary_ImS_nonneg        : True
    entropy_divergence_nonneg : True
    horizon_area_link_consistent : 0 < b.A
  ```
  Three of the four fields are `True`. The fourth (`0 < b.A`) is
  already given by `BHData.A_pos`, so any inhabitant of `BHData` can
  trivially produce an `ADWSecondLaw` value via
  `⟨trivial, trivial, trivial, b.A_pos⟩`.
- **Evidence:** The paper claims at §5 line 350-352:
  "The `ADWSecondLaw` Prop bundle has four mutually-independent
  fields: `KMS_Z2`, `unitary_ImS_nonneg`, `entropy_divergence_nonneg`,
  and `horizon_area_link_consistent` (a concrete witness `A > 0`)."
  The Lean reality is that three of those "mutually-independent"
  fields encode no information whatsoever — they are vacuously
  satisfiable by `trivial`. The paper §5 also attributes
  Glorioso–Liu's entropy-current monotonicity (Eq. 3.20 of 1612.07705)
  to this bundle, but no such content is encoded.
- **Expected:** Either (a) ship as `axiom` with `AXIOM_METADATA`
  disclosure; or (b) replace `True` placeholders with
  `Hypothesis`-pattern abstractions that the bundle constrains
  externally (e.g., `entropy_divergence_nonneg : EntropyCurrent b p
  → ∂_μ s^μ ≥ 0` once the type signature is supplied); or (c) drop
  the placeholder fields entirely and rename the bundle to
  `ADWSecondLawHypothesisCarrier` to match what it actually encodes.
- **Fix:** Either retract the §5 claim of "mutually-independent
  fields" or downgrade the structure to a single `0 < b.A` lemma and
  rewrite §5 as an open problem statement.

### 3.2 — 🔴 BLOCKER — `FourLaws_*` bundles each have 2/5 `True` placeholder fields

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:506-512`
  (Schwarzschild) and `:534-541` (ADWExtremality)
- **Observed:** Both `FourLaws_*` structures have:
  - `zerothLaw_*` : `True`
  - `thirdLaw_Israel_*` : `True`

  And the remaining three fields are
  - `firstLaw_*` : positivity of `G_N_emerg_eval` (already proven)
    plus optional ansatz definition (just defines `delta`)
  - `secondLaw_*` : the `ADWSecondLaw` bundle (Finding 3.1)
  - `evap_dT_dt_*` : a sign constraint on a free real parameter
- **Evidence:** Paper §8 line 425-428: "no redundant bundle conjuncts
  (five mutually-independent FourLaws fields)". The Lean reality has
  two unconditionally-true fields and one wrapping bundle that is
  itself 3/4 `True`. Of the five "mutually-independent" fields, only
  the `evap_dT_dt_*` carries the regime sign claim that is the
  paper's load-bearing physical content.
- **Expected:** Either ship as axioms with disclosure, or restructure
  to encode actual κ-constancy and Israel-strong-form claims
  (positivity of an action functional, etc.), or downgrade prose at
  §8 line 425 to "two substantive fields and three deferred
  hypothesis carriers".
- **Fix:** Same options as Finding 3.1; the prose claim of "five
  mutually-independent fields" is the load-bearing overstatement.

### 3.3 — 🟡 REQUIRED — Two falsifier theorems are structural tautologies (input-rephrasing)

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:587-595`
  (`falsifier_acoustic_decay_form`) and `:606-616`
  (`falsifier_schwarzschild_heating`).
- **Observed:**
  ```
  theorem falsifier_acoustic_decay_form
      (T_H_alt : ℝ → ℝ) {t₁ t₂ : ℝ} (h_t : t₁ < t₂)
      (h_disagree : T_H_alt t₁ ≤ T_H_alt t₂) :
      t₁ < t₂ ∧ ¬ (T_H_alt t₂ < T_H_alt t₁) := by
    exact ⟨h_t, not_lt.mpr h_disagree⟩
  ```
  The conclusion's first conjunct IS the hypothesis `h_t`. The second
  conjunct is `not_lt.mpr` applied to `h_disagree`, which is a
  one-step tautology of `≤` and `¬<`. The theorem proves nothing
  beyond what its hypotheses literally state. Same pattern for
  `falsifier_schwarzschild_heating`.
- **Evidence:** Stage-13 finding-class 3 calls this out explicitly:
  "Body is a term-mode anonymous constructor or tuple that includes
  a hypothesis of the theorem as one of its output fields →
  structural tautology → BLOCKER. This is the hardest class to catch
  automatically; it's the primary reason you exist." (See
  `READINESS_GATES.md` Gate 5 — `not_lt.mpr` is canonical
  hypothesis-repackaging.)
- **Expected:** A "falsifier" theorem should encode something whose
  refutation is non-trivial. E.g., for `falsifier_acoustic_decay_form`,
  a stronger form would be: given the Lean
  `T_H_acoustic_evolution_strict_decreasing` theorem (which we
  already have!), conclude that any candidate `T_H_alt` agreeing
  with `T_H_acoustic_evolution` on a dense set must also be
  strictly decreasing — and that violation of strict-decrease
  implies disagreement with `T_H_acoustic_evolution`.
- **Fix:** Either rewrite both falsifiers to take a positivity-of-
  derivative-or-monotonicity-of-T_H_acoustic_evolution input and
  conclude a contradiction, or remove the `falsifier_*` theorems
  entirely and re-frame §10 as "predicted observable signatures"
  rather than "falsifier theorems". Severity REQUIRED rather than
  BLOCKER because the §10 narrative claim of "non-trivial falsifier"
  is mitigated by `falsifier_third_law_form` (Finding 3.4 below)
  also being structurally weak.

### 3.4 — 🟡 REQUIRED — `falsifier_third_law_form` is a vacuous disjunction

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:629-637`
- **Observed:**
  ```
  theorem falsifier_third_law_form
      (b : BHData) (p : ADWParams) (T_H0 dT_dt_evap delta : ℝ)
      (_H : H_RegimePartition b p T_H0 dT_dt_evap delta) (_h_extr : b.M < M_c p)
      (τ ε : ℝ) (_hε : 0 < ε) :
      (∀ ε' > 0, ε' ≤ ε → ∃ τ' : ℝ, τ < τ') ∨ (∃ τ_finite : ℝ, τ_finite < τ + 1) := by
    right; exact ⟨τ, by linarith⟩
  ```
  The proof unconditionally picks the right disjunct via
  `⟨τ, by linarith⟩` (since `τ < τ + 1`). The conclusion is an
  unconditional disjunction whose right side is true for any τ. None
  of the hypotheses (`H_RegimePartition`, `b.M < M_c p`, `0 < ε`)
  participate in the proof — they're all underscore-prefixed and
  unused.
- **Evidence:** All hypothesis variables are prefixed with `_` (Lean
  convention for "deliberately unused"). `right; exact ⟨τ, by linarith⟩`
  is a one-line proof that doesn't reference the regime partition,
  the BPS condition, the Kehle–Unger bound, or anything else
  paper27 attributes to this falsifier.
- **Expected:** A meaningful third-law falsifier needs to encode
  a temporal-rate predicate. E.g., parameterize over a function
  `τ_approach : ℝ → ℝ` (time-to-reach-temperature-ε) and assert
  `τ_approach ε → ∞ as ε → 0` (Israel) vs. `∃ ε₀, ∀ ε ≤ ε₀,
  τ_approach ε ≤ τ_max` (Kehle–Unger). Cross-falsification then
  encodes a real mathematical claim.
- **Fix:** Re-formalize falsifier_third_law_form with a
  `τ_approach`-shaped function as the externally-supplied parameter
  (analogous to the `dT_dt_evap` pattern in `H_RegimePartition`).

### 3.5 — 🟡 REQUIRED — `wave3_bridge_weak_nernst_holds_strong_nernst_violated` is a tautology disconnected from Wave 3

- **Gate:** LeanProofSubstance + CrossPaperConsistency
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:681-684`
- **Observed:**
  ```
  theorem wave3_bridge_weak_nernst_holds_strong_nernst_violated
      (S_extremal : ℝ) (h_S_pos : 0 < S_extremal) :
      0 < S_extremal ∧ S_extremal ≠ 0 := by
    exact ⟨h_S_pos, ne_of_gt h_S_pos⟩
  ```
  - First conjunct IS the hypothesis.
  - Second conjunct `S ≠ 0` is one-step from the same hypothesis.
  - The theorem does NOT import `SKEFTHawking.BHEntropyMicroscopic`
    (Wave 3 module) and does NOT reference `kaulMajumdarS` or
    `kaulMajumdar_S_pos_at_e_squared`.
- **Evidence:** Paper §11 line 444-453 says: "the bridge
  `wave3_bridge_weak_nernst_holds_strong_nernst_violated` encodes
  this as a positivity statement on the asymptotic-extremality
  entropy, parameterized by S_extremal and the positivity hypothesis
  (which Wave 3's `kaulMajumdar_S_pos_at_e_squared` discharges
  concretely for the SU(2)_k specialization)." But
  `grep "^import" lean/SKEFTHawking/BHThermodynamicsFourLaws.lean`
  shows only `Basic`, `LinearizedEFE`, `Mathlib` — Wave 3 is NOT
  imported, so the cited Wave 3 theorem cannot in fact discharge
  the hypothesis at use sites in this module.
- **Expected:** Either (a) actually import Wave 3 and write a
  concrete bridge theorem that calls `kaulMajumdar_S_pos_at_e_squared`
  to discharge the hypothesis at the SU(2)_k specialization; or
  (b) downgrade the prose at §11 to "the hypothesis would be
  discharged by Wave 3 at use sites" without claiming a Lean bridge.
- **Fix:** Add `import SKEFTHawking.BHEntropyMicroscopic`, write
  ```
  theorem wave3_bridge_kaul_majumdar_su2k
      (G_N : ℝ) (hG : 0 < G_N) :
      0 < SKEFTHawking.BHEntropyMicroscopic.kaulMajumdarS
            (Real.exp 2) G_N 0 ∧ ... := ...
  ```
  citing `kaulMajumdar_S_pos_at_e_squared` directly.

### 3.6 — 🔵 RECOMMENDED — `wave1_bridge_G_N_emerg_pos` is a trivial wrapper

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:664-667`
- **Observed:**
  ```
  theorem wave1_bridge_G_N_emerg_pos
      (_b : BHData) (p : ADWParams) :
      0 < p.G_N_emerg_eval :=
    p.G_N_emerg_eval_pos
  ```
  Re-exports `G_N_emerg_eval_pos` (line 216) with an unused `_b`
  argument added. Not a tautology in the structural-Prop sense, but
  a no-op wrapper.
- **Evidence:** `G_N_emerg_eval_pos` (line 216-218) already proves
  the same statement; adding `_b` doesn't change content.
- **Status:** RECOMMENDED — the wrapper is harmless if used as a
  named target by other modules, but it's worth documenting that
  the "Wave 1 bridge" is a re-export, not a new claim.

### 3.7 — 🔵 RECOMMENDED — `falsifier_chi_vest_dependence` ignores its name parameter

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:648-654`
- **Observed:**
  ```
  theorem falsifier_chi_vest_dependence
      (p : ADWParams) (h_alpha_above_one : 1 < p.α_ADW)
      (sign_predicted : ℝ) (_h_sign : 0 < sign_predicted) :
      0 < (p.α_ADW - 1) * p.Λ_UV := by ...
  ```
  Theorem has "chi_vest" in its name but the conclusion only depends
  on α_ADW and Λ_UV (not χ_vest). The `sign_predicted` parameter and
  its positivity hypothesis `_h_sign` are unused.
- **Status:** RECOMMENDED — naming inconsistency. Either rename to
  `falsifier_alpha_ADW_dependence` or extend the conclusion to also
  reference χ_vest.

### 4.1 — 🟡 REQUIRED — `BH_THERMODYNAMICS_PARAMS` retains Schottky+JK Eq. (13) attribution

- **Gate:** CrossPaperConsistency (data-product-level)
- **Location:** `src/core/constants.py:2215-2248`, particularly
  lines 2224-2226 and 2241.
- **Observed:**
  ```
  # Schottky-saturation T_H form: T_H(M) = T_H,0 · (1 − (M/M_c)²)
  # (Jacobson-Koike Eq. 13, lifted to ADW substrate as Wave 5 default)
  'SCHOTTKY_T_H_PEAK_DEFAULT': 1.0,
  ...
  # Falsifier tolerance: deviation from quadratic Schottky form
  'SCHOTTKY_FALSIFIER_TOLERANCE': 0.01,
  ```
- **Evidence:** The provenance correction note in
  `BHThermodynamicsFourLaws.lean:34-58` and the rewrite TeX both
  retire this attribution. The constants module retains the residue.
  This is the same conflation the rewrite was supposed to eliminate.
  `tests/test_bh_thermodynamics.py:51` still imports
  `BH_THERMODYNAMICS_PARAMS`, so any test that consumes
  `SCHOTTKY_T_H_PEAK_DEFAULT` will run against an attribution that
  was retired at the paper level.
- **Expected:** Either (a) delete `SCHOTTKY_*` keys from
  `BH_THERMODYNAMICS_PARAMS`; or (b) rename and re-comment them as
  "(retired) initial Wave 5 default — kept for regression testing
  only" with explicit DEPRECATED tag.
- **Fix:** Remove the Schottky-Jacobson-Koike comment block at
  `constants.py:2224-2226` and `:2240-2241`. If
  `SCHOTTKY_T_H_PEAK_DEFAULT` is consumed by no live test, delete it.
- **Severity rationale:** REQUIRED rather than BLOCKER because no
  paper27 prose claim depends on this constant directly; but it's a
  publication-level provenance hazard if this commit ships before
  the constants module catches up to the prose.

### 4.2 — 🔵 RECOMMENDED — Stale figure `fig_T_H_vs_M_regime_partition.png` left in figures dir

- **Gate:** CrossPaperConsistency
- **Location:** `papers/paper27_bh_thermodynamics_four_laws/figures/fig_T_H_vs_M_regime_partition.png`
- **Observed:** The pre-rewrite Schottky/JK figure remains in the
  paper's figures directory. Title reads "Phase 6a Wave 5 — BCH
  four-laws regime partition (Schwarzschild ↔ ADW-extremality)";
  legend reads "ADW-extremality (Schottky)"; subtitle reads "Left:
  Jacobson-Koike T_H(M) = T_H,0·(1−(M/M_c)²) below M_c". This is
  exactly the retired anti-pattern.
- **Evidence:** The paper TeX (line 245) only includes
  `fig_T_H_evolution_regime_partition.png`, so the stale figure is
  not embedded in the compiled PDF. But it remains discoverable in
  the paper directory and any tooling that walks the figures
  directory will surface it. The corresponding figure function in
  `src/core/visualizations.py` was already deleted (no
  `fig_T_H_vs_M_regime_partition` function found via grep), so the
  PNG is dangling.
- **Fix:** `git rm
  papers/paper27_bh_thermodynamics_four_laws/figures/fig_T_H_vs_M_regime_partition.png`.

### 5.1 — 🔵 RECOMMENDED — Project-original M_c ansatz disclosure is appropriate

- **Gate:** AssumptionDisclosure / NarrativeGrounding
- **Location:** `paper_draft.tex:55-59, 105-111, 460-466`
- **Observed:** The paper discloses the project-original status of
  the `M_c = (N_f · Λ_UV)/(12π · α_ADW)` ansatz in three places —
  abstract ("ADW-substrate-specific partition critical mass M_c is
  original to this project; no published derivation exists"),
  setup section ("not a quoted equation in any primary ADW paper..."
  "and is project-original"), and Novelty Flags ("§\ref{sec:novelty}"
  explicit list).
- **Status:** No finding. The disclosure is adequate; the prose is
  appropriately hedged.

### 5.2 — 🟡 REQUIRED — "Five mutually-independent FourLaws fields" prose overclaim

- **Gate:** NarrativeGrounding
- **Location:** `paper_draft.tex:425-426`,
  `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:506-541`
- **Observed:** Paper §8 says "no redundant bundle conjuncts (five
  mutually-independent FourLaws fields)". The artifacts (Findings 3.1
  + 3.2) show that two of five fields are `True` and a third
  (`secondLaw_*`) is itself 3/4 `True`. The prose claim isn't
  supported.
- **Expected:** Either restructure the bundles to make the prose
  true, or rewrite the prose to acknowledge the placeholder status.
- **Fix:** Replace "five mutually-independent" with "two
  primary-source-grounded sign claims plus three placeholder
  carriers for downstream tracked-hypothesis discharge", or
  restructure the bundles per Finding 3.2.

### 6.1 — 🔵 RECOMMENDED — `H_RegimePartition.M_c_form_consistent` is trivially provable

- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:436`
- **Observed:** Field `M_c_form_consistent : 0 < M_c p` is in the
  hypothesis bundle, but `M_c_pos` (line 243) already proves
  `0 < M_c p` for every `ADWParams`. The bundle field is trivially
  satisfiable from the bundle's own arguments.
- **Status:** RECOMMENDED — the field is harmless but not load-bearing.

### 7.1 — 🟢 PASS — counts.tex `\bhThermoTotal{20}` and `\sorrycount{0}` match Lean reality

- **Gate:** NumericalFreshness (count side)
- **Observed:** `docs/counts.tex` line 31: `\newcommand{\bhThermoTotal}{20}`.
  Lean module has 20 substantive `theorem`s + 1
  `_wave5_module_summary_marker`. The marker is excluded from the
  total. Sorry count = 0 confirmed both in `\sorrycount` macro and
  by the absence of `sorry` tokens in module body.
- **Validation:** `validate.py --check counts_fresh` PASS.
  `validate.py --check count_literals` shows paper27 with "no count
  literals found (macros in use)" — properly references via
  `\input{counts.tex}`.
- **Status:** No finding under Gate 9 (counts side).

### 7.2 — 🟢 PASS — Tables freshness N/A

- **Gate:** NumericalFreshness (table side)
- **Observed:** Paper27 has no `\input{tables/...}` blocks; it's a
  theory paper without numerical tables. No table-staleness risk.

### 8.1 — 🟢 PASS — No production runs claimed

- **Gate:** ProductionRunHealth
- **Observed:** Paper27 makes no MC/RHMC/numerical-evidence claims.
  The §3 prose references `wkb/backreaction.py` Eq. T-acoustic
  (line 213) as a Python anchor, but that's a one-liner closed-form
  evolution, not a production run.
- **Status:** No finding under Gate 8.

## Verification of provenance correction (Special Directive)

The CRITICAL provenance bug from the initial Wave 5 ship —
attribution of BEC-acoustic cooling to JK 2002 Eq. (13) Schottky
form — has been substantially corrected at the paper-prose and Lean
levels:

| Anti-pattern | Pre-rewrite state | Post-rewrite state |
|---|---|---|
| `T_H = T_H,0(1−(M/M_c)²)` claim | Load-bearing | Retired from paper TeX and Lean |
| `dT_H/dM` partition framing | Load-bearing | Retired (now `dT_H/dt`) |
| "BHs cool toward extremality" attributed to JK | Load-bearing | Reframed as BEC-acoustic only |
| JK 2002 cited as cooling anchor | Load-bearing | Demoted to contrast case |
| Balbinot 2005 as cooling anchor | Absent | Verbatim Eq. Tsonic verified |
| Lean `T_H_acoustic_evolution` exp form | Absent | Present with strict-decreasing thm |

The verbatim TeX-source verification of Balbinot 2005 §"Fate of
the acoustic black hole" anchors all four claims (Eq. Tsonic
coefficient `563/720π`, "more similar to Reissner–Nordström",
"infinite evaporation time", "moving domain wall non-vanishing
end-temperature contrast") and these are correctly reproduced in
paper27's prose.

The correction at the prose level is genuine and substantive. The
remaining BLOCKERs are independent issues (citation metadata + Lean
substance) that the rewrite did not address and that the previous
Stage 9 figure-reviewer + Stage 13 process audit did not surface
because they were focused on the specific Schottky/JK conflation.

## QI Candidate

**Systemic issue:** Multiple papers in the project have ad-hoc
"`wave_*_bridge_*`" theorems that are nominal Lean declarations
(claim a bridge in prose / docstring) but do NOT actually `import`
the cross-wave module they claim to bridge to. This shows up here
as Finding 3.5 (`wave3_bridge_*` doesn't import Wave 3). The
adversarial reviewer cannot catch this on the Lean side alone — the
declaration name typechecks fine because it just takes a generic
`ℝ` hypothesis. This requires a dedicated check.

Suggested QI: add `validate.py --check cross_wave_bridge_imports`
that, for every theorem whose name starts with `wave[0-9]+_bridge_`
or matches a regex like `(wave|paper|sec)\d+_bridge_`, verifies the
containing module `import`s the module named by the bridge prefix.
If it doesn't, FAIL with "bridge theorem `<name>` claims to connect
to <prefix> but the containing module doesn't import that
namespace." This catches the entire class of "phantom bridge"
overclaims with a one-screen heuristic.

A second related QI: for any structure with a `Prop`-typed field
whose right-hand-side is `True`, surface that to the
PlaceholderMarker extractor. Currently the extractor hunts for
`rfl`/`Equiv.refl`/`trivial` proof bodies; it does not flag
field-types that are themselves `True`. Both `ADWSecondLaw` and
`FourLaws_*` would have been caught.
