---
paper: paper35_qec_holography
artifact: notebooks
notebooks:
  - SK_EFT_Hawking/notebooks/Phase6c4_QECHolography_Technical.ipynb
  - SK_EFT_Hawking/notebooks/Phase6c4_QECHolography_Stakeholder.ipynb
reviewer: claims-reviewer-v2 (notebook adaptation)
model: claude-opus-4-7-1m
review_date: 2026-04-29T01:00:00Z
finding_classes: [IA, TP, SD, TN, HD]
---

# Notebook Claims Review — paper35_qec_holography

## Summary

Sentence-level claims audit of the two paper35 companion notebooks (Technical + Stakeholder) against the Lean module `lean/SKEFTHawking/QECHolographyBridge.lean`, the Python module `src/qec_holography/`, the visualization function `src/core/visualizations.py:9540 fig_code_distance_vs_fusion_spectrum`, and the paper draft `papers/paper35_qec_holography/paper_draft.tex`.

**Verdict: clean.** No BLOCKER, REQUIRED, or RECOMMENDED findings. All 10 substantive Lean theorem references in the Technical notebook resolve to theorems present in the current Lean module. The cross-wave-strengthening removals (`scramblingTimeBound_pos_iff_nontrivial`, `codeDistance_pos_iff_non_abelian`) are honestly disclosed as removed in §8 of the Technical notebook and are NOT cited as live theorems anywhere. All four MTC substrate spectra match the canonical Python definitions; all numerical claims (`log φ ≈ 0.481`, `log 2 ≈ 0.693`, `D²_{Fib} ≈ 3.618`, `t_{scr,Ising} ≈ 1.386`, `d_σ = √2 ≈ 1.414`) reproduce to within display precision. The theorem count of 10 substantive matches `\qecHolographyThms = 10` in `docs/counts.tex` and `grep -c '^theorem ' QECHolographyBridge.lean = 10`. All cited references (Hayden-Preskill 2007, Almheiri-Dong-Harlow 2015, PYHP 2015, Yoshida-Kitaev 2017, Kitaev 2003 anyons, Nayak et al. RMP 2008) are present in the paper bibliography. Out-of-scope deferrals (AdS/CFT spectrum, Yoshida-Kitaev decoder, Page curve) are honestly disclosed in both notebooks. Two **INFO**-level observations recorded below.

## Findings

(none — no BLOCKER / REQUIRED / RECOMMENDED issues)

## INFO observations (no action required)

### INFO-1 (Class TN-adjacent) — Technical §6 paraphrase of `H_HorizonBoundaryCondition` fields

- **File:** `notebooks/Phase6c4_QECHolography_Technical.ipynb` cell `p35t-6-md`.
- **Quote:** "If the W3 hypothesis bundle `H_HorizonBoundaryCondition` holds (area-law / second-law / non-abelian envelope), then $1 < d_{\max}$ and admissibility follows."
- **Observation:** The Lean structure `H_HorizonBoundaryCondition` (BHEntropyMicroscopic.lean:373–379) has **five** fields: `positivity`, `areaLeading`, `secondLaw`, `modularInvariant` (placeholder `True`), `anomalyMatch` (placeholder `True`). The notebook paraphrase enumerates three (area-law / second-law / non-abelian envelope), conflating "areaLeading + areaLawKappa > 0" with "non-abelian envelope" (the notebook is using "non-abelian" as shorthand for the implication `areaLeading ⇒ d_max > 1`). The proof body in `horizon_BC_implies_HP_admissible` only invokes `h.areaLeading`, so the simplification is operationally accurate and the cross-bridge proof is correct. This is INFO not REQUIRED because (a) the simplification is consistent with the paper draft framing (paper §VII discloses the abstract-level `S_horizon` parametrization), and (b) the omitted `modularInvariant`/`anomalyMatch` fields are placeholder `True` Props.
- **Verdict:** PASS with INFO note. No action recommended.

### INFO-2 (Class SD-adjacent) — Stakeholder substrate-vs-encoding framing of "code distance"

- **File:** `notebooks/Phase6c4_QECHolography_Stakeholder.ipynb` cell `p35s-1-md`.
- **Quote:** "Code distance $d_C := \log d_{\max}$, where $d_{\max}$ is the largest quantum dimension of any anyon. Heuristically: how much 'topological room' the substrate gives the encoded qubit to hide from local errors."
- **Observation:** The strengthened paper draft (lines 87–93) introduces `d_C` deliberately as a *code-distance proxy* that is "a *substrate-level* quantity --- it depends only on the MTC spectrum, not on the specific encoding-anyon choice --- upper-bounding any per-encoding code distance one would obtain from an explicit Yoshida-Kitaev decoder." The Stakeholder notebook does not use the word "proxy" anywhere and frames `d_C` directly as "code distance" with a heuristic ("topological room … hide from local errors") that could be read as the per-encoding QEC code distance. The Technical notebook does use "code-distance proxy" (cell `p35t-5-code` and §5 final print). Operationally, both notebooks compute `code_distance(spectrum)` as a pure substrate function (no `encoding_idx`), so the implementation is unambiguous; only the Stakeholder prose runs marginally looser than the strengthened paper. This is the same conflation that the prior adversarial pass (Class 5, REQUIRED-5.1) flagged for the paper §III, was resolved there, and has not been propagated into the Stakeholder companion. RECOMMENDED if a stakeholder audience is expected to compare with `d_C`-as-distance-bound in published QEC literature; INFO under the agent's stricter "is the chain falsifiable / does the implementation match" rubric — yes, the Python function `code_distance(spectrum)` correctly takes only a spectrum, and the cross-bridge to encoding-recovery (`recovery_at_scrambling_bound`) is presented separately.
- **Verdict:** PASS with INFO note. **Optional improvement** (RECOMMENDED-grade if elevated): align Stakeholder §1 prose with the paper's "proxy" qualifier.

## Verification matrix

### Class TN — theorem-name reference drift

All theorems referenced in either notebook resolve in `lean/SKEFTHawking/QECHolographyBridge.lean`:

| Reference | Notebook | Lean (`grep -c '^theorem <name>'`) | Verdict |
|---|---|---|---|
| `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` | Technical §3, §8 | 1 (line 208) | PASS |
| `recovery_at_scrambling_bound` | Both, §4 | 1 (line 167) | PASS |
| `horizon_BC_implies_HP_admissible` | Technical §6, §8 | 1 (line 249) | PASS |
| `fibonacci_HPCode_codeDistance_lt_log_two` | Technical §5, §8 | 1 (line 297) | PASS |
| `fibonacci_HPCode_scramblingTimeBound_pos` | Technical §8 | 1 (line 326) | PASS |
| `trivialAbelian_violates_admissibility` | Technical §6, §8 | 1 (line 371) | PASS |
| `nonabelian_anyon_implies_codeDistance_pos` | Technical §8 | 1 (line 265) | PASS |
| `one_le_globalDimSq` | Technical §8 | 1 (line 100) | PASS |
| `scramblingTimeBound_nonneg` | Technical §8 | 1 (line 125) | PASS |
| `codeDistance_nonneg` | Technical §8 | 1 (line 142) | PASS |
| `H_HorizonBoundaryCondition` | Both, §6 | 1 (BHEntropyMicroscopic.lean:373) | PASS |
| `H_HorizonBoundaryCondition.areaLeading` | Technical §6 | field exists (line 376) | PASS |
| `fibonacci_horizon_areaLawKappa_pos` | Technical §6 | 1 (BHEntropyMicroscopic.lean:600) | PASS |

**Cross-wave-strengthening removed names** (per 2026-04-28-0030):
- `scramblingTimeBound_pos_iff_nontrivial` — appears once in Technical §8, ONLY in the disclosure sentence "Cross-wave strengthening removed earlier API specializations …". No live citation. PASS.
- `codeDistance_pos_iff_non_abelian` — same; disclosure-only. PASS.

### Class IA — internal arithmetic / count drift

All numerical claims reproduce. Spot-check via `python3` matches printed values to display precision:

| Claim | Notebook | Recomputed | Source | Verdict |
|---|---|---|---|---|
| φ ≈ 1.618034 | Both, §1/§5 | 1.618034 | `(1+√5)/2` | PASS |
| log φ ≈ 0.481212 (also 0.481) | Both, §1/§5 | 0.481212 | `math.log(φ)` | PASS |
| log 2 ≈ 0.693147 (also 0.693) | Both, §1/§5/figure | 0.693147 | `math.log(2)` | PASS |
| log φ < log 2 | Both | True | direct | PASS |
| D²_Fib = 1+φ² ≈ 3.618 | Both, table | 3.618034 | `1+φ²` | PASS |
| t_{scr,Fib} ≈ 1.286 | Both, table | 1.285931 | `log(3.618)` | PASS |
| D²_Ising = 4.000 | Both, table | 4.0 | `1+2+1` | PASS |
| t_{scr,Ising} ≈ 1.386 | Both, table | 1.386294 | `log(4)` | PASS |
| d_σ = √2 ≈ 1.414 | Both, §2 | 1.414214 | `math.sqrt(2)` | PASS |
| d_C(Ising) ≈ 0.347 | Stakeholder table | 0.346574 | `log(√2)` | PASS |
| trivial-abelian d_max=1, D²=1, d_C=t_scr=0 | Both, §2/§6 | 1, 1, 0, 0 | direct | PASS |

Theorem count claim "10 substantive theorems":
- Technical §intro: "10 substantive theorems / 0 sorry / 0 new axioms" — matches `grep -c '^theorem ' QECHolographyBridge.lean = 10` ✓
- Technical §8: numbered list of 10 theorems — matches Lean module exactly ✓
- Stakeholder §6: "10-theorem Lean module with zero `sorry` and zero new axioms" — matches `\qecHolographyThms = 10` in `docs/counts.tex:37` ✓
- `grep -c sorry QECHolographyBridge.lean = 0` ✓
- `grep -c '^axiom ' QECHolographyBridge.lean = 0` ✓

### Class TP — toolchain pin drift

No literal Lean / Mathlib / Aristotle version mention in either notebook. N/A.

### Class SD — stealth pipeline-vs-prose drift

| Prose | Implementation | Verdict |
|---|---|---|
| "four MTC substrates" (both notebooks) | `FIBONACCI_SPECTRUM`, `ISING_SPECTRUM`, `SU3K2_SPECTRUM`, `TRIVIAL_ABELIAN_SPECTRUM` (4 in `src/qec_holography/code_distance.py:48–70`) | PASS |
| Fibonacci `{1, τ}` with `d_τ = φ` (Technical §2) | `(1.0, _PHI)` (code_distance.py:50) | PASS |
| Ising `{1, σ, ψ}` with `d_σ = √2`, `d_ψ = 1` implicit (Technical §2) | `(1.0, _SQRT2, 1.0)` (code_distance.py:55) | PASS |
| SU(3)_{k=2} Fibonacci sub-sector "spectrum identical to Fibonacci by truncation" (Technical §2) | `(1.0, _PHI)` with comment "vac + adj sub-sector forms a Fibonacci MTC by Hirono-Tanizaki SU(3)_k=2 ↔ Z_3 + Fibonacci decomposition" (code_distance.py:58–65) | PASS |
| Trivial-abelian `{1}`, `d_max=1`, `D²=1` (both notebooks) | `(1.0,)` (code_distance.py:67–70) and `trivialAbelianHorizonBC` (QECHolographyBridge.lean:340) | PASS |

Stakeholder §3 prose: "biconditional 'positive code distance ↔ ∃ non-abelian anyon'" + "forward implication d_C > 0 ⇒ t_scr > 0" — matches Lean theorem `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` shape `(0 < d_C ↔ 1 < d_max) ∧ (0 < d_C → 0 < t_scr)` (modulo `1 < d_max` ↔ `∃ a, 1 < d_a` via `nonabelian_anyon_implies_codeDistance_pos` + `d_max_attained` field). PASS.

### Class HD — hypothesis disclosure gap

The W3-inherited tracked hypothesis `H_HorizonBoundaryCondition` is disclosed:
- Technical §6 — explicitly names the bundle and its `areaLeading` field.
- Stakeholder §6 ("Honest scope") — discloses: "*That nature has a non-abelian horizon MTC.* This is an assumption inherited from Phase 6a Wave 3 (`H_HorizonBoundaryCondition.areaLeading`), itself a tracked external hypothesis."

PASS. (See INFO-1 above for the minor 5-fields-vs-3-fields paraphrase observation.)

### Citations cross-check

All citations in Stakeholder §intro/§6 are present in `papers/paper35_qec_holography/paper_draft.tex` bibliography (lines 298–334):

| Citation | Paper bibitem | Verdict |
|---|---|---|
| Hayden-Preskill 2007 | `HaydenPreskill2007` (line 298) | PASS |
| Almheiri-Dong-Harlow 2015 | `AlmheiriDongHarlow2015` (line 303) | PASS |
| Pastawski-Yoshida-Harlow-Preskill 2015 | `PYHP2015` (line 308) | PASS |
| Yoshida-Kitaev 2017 | `YoshidaKitaev2017` (line 314) | PASS |
| Kitaev 2003 (anyons) | `KitaevAnyons2003` (line 319) | PASS |
| Nayak et al. RMP 2008 | `NayakAnyons2008` (line 324) | PASS |
| Hawking 1976 (information loss) | not in paper bibliography (Stakeholder §intro mentions "Hawking's 1976 calculation" without `\cite{}`) | INFO — Stakeholder is non-cited prose; paper draft does not need this bibitem. PASS at notebook level. |

### Out-of-scope deferral disclosure

Stakeholder §6 discloses three deferrals that match the paper §I/§II scope statements and the Lean module header (lines 35–40):

1. AdS/CFT spectrum identification — matches paper deferral and Lean header "out of scope".
2. Yoshida-Kitaev decoder construction — matches.
3. Page-curve quantitative reproduction — matches.

PASS. Honest scoping.

## Cross-checks against the visualization

`fig_code_distance_vs_fusion_spectrum()` (visualizations.py:9540–9677) renders four bars in left and right panels with the same four spectra, labels `Fibonacci<br>(d_τ = φ)`, `Ising<br>(d_σ = √2)`, `SU(3)_k=2<br>(adj sector, φ)`, `Trivial<br>abelian (d=1)`. The notebook descriptions in Technical §7 and Stakeholder §5 match the figure's actual contents (admissibility threshold at d_C=0, log 2 reference line on left panel, scrambling-time bars on right with `t_scr=0` reference line). PASS.

**Minor visualization docstring observation (NOT a notebook finding):** The Lean docstring at visualizations.py:9555–9558 lists `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` twice consecutively (a duplicate). Doesn't affect notebook claims, but worth noting in the next visualization-docstring sweep.

## Reconciliation with prior reports

Prior 2026-04-29-0000 internal-adversarial review of `paper35_qec_holography` (paper draft, not notebooks) found zero new BLOCKER/REQUIRED/RECOMMENDED issues after a strengthening pass that:
- Added "code-distance proxy" qualifier (REQUIRED-5.1 resolved).
- Disclosed `S_horizon` parametrization (RECOMMENDED-6.1 resolved).
- Retrofitted `\qecHolographyThms{}` macro (RECOMMENDED-5.2 resolved).

The notebooks **inherit the proxy framing only partially**: Technical notebook uses "proxy" once (cell `p35t-5-code`); Stakeholder notebook uses no proxy framing. See INFO-2 for optional improvement.

No prior notebook-level claims review exists for paper35; this is the first notebook audit.

## Summary statistics

- Notebooks audited: 2
- Markdown cells walked: ~16 (Technical 9 + Stakeholder 7)
- Code cells walked: ~10
- Lean theorem references: 13 unique (10 in QECHolographyBridge + 3 inherited from BHEntropyMicroscopic)
- All references resolve: ✓
- Numerical claims spot-checked: 11 — all PASS
- Citations cross-checked: 6 (paper bibliography) + 1 non-cited prose (Hawking 1976) — all PASS
- BLOCKER findings: 0
- REQUIRED findings: 0
- RECOMMENDED findings: 0
- INFO observations: 2 (paraphrase precision; Stakeholder proxy framing)
- Notebooks ready for downstream consumption: yes

## Optional follow-ups (do not block)

1. **Stakeholder §1 proxy framing alignment** (INFO-2): one-line edit to align Stakeholder cell `p35s-1-md` first bullet with the paper §III "code-distance proxy" + "substrate-level quantity" qualifier. Cost: 2 sentences. Benefit: stops a stakeholder reader from inferring `d_C` is a per-encoding QEC distance bound (which it is not — it is the substrate-level proxy, with the per-encoding bound separately handled by `recovery_at_scrambling_bound`).

2. **Technical §6 H_HorizonBoundaryCondition field-list precision** (INFO-1): one-line edit to either say "five-field bundle (positivity / areaLeading / secondLaw / modularInvariant / anomalyMatch)" or to qualify "the relevant fields for this bridge are areaLeading and secondLaw — modularInvariant and anomalyMatch are placeholder Props at this abstract level". Currently "(area-law / second-law / non-abelian envelope)" risks misreading as the full bundle.

3. **Visualization docstring de-duplication** (visualizations.py:9555–9558): drop the duplicate `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` line. Cosmetic.

None of these are blocking.
