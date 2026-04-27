---
paper: paper35_qec_holography
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper35_qec_holography

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`QECHolographyBridge.lean` ships 10 substantive theorems with no
`rfl`/`trivial`/structural-tautology placeholders; all theorem bodies
invoke load-bearing structural lemmas (`Real.log_pos_iff`, sum bounds
via `Finset.single_le_sum`, `Real.log_le_log` with case-splits). The
Fibonacci witness theorem `fibonacci_HPCode_codeDistance_lt_log_two`
genuinely bounds `log φ < log 2` via `√5 < 3 ⇔ 5 < 9`. Class 1
cache-skip on all seven citation bibitems. Two REQUIRED issues: (a)
paper §6 prose claims the proof "case-splits on `d_encode ≥ 1` versus
`d_encode < 1`" but a stronger (and easier) proof would use the
`d_e ≤ d_e²` step uniformly when `d_e ≥ 1`, and `log` monotonicity
when `d_e < 1`; the prose is accurate but the implied substantive
content is the universal recovery, not the case split — minor; (b)
paper §3 `\dC := \log\dmax` — the paper claims this is reused as
"the topological-shielding scale of an encoded logical qubit" but the
Lean definition `codeDistance := H.horizon.areaLawKappa` does not
actually instantiate any specific anyon's contribution; it is just
`log d_max`, a property of the substrate, not of the encoding. The
prose conflates the substrate-level `d_C` (what's defined) with a
per-encoding code distance (what the QEC literature usually means).

## Findings

### 5.1 — 🟡 REQUIRED — `codeDistance` is a substrate property, not a per-encoding code distance, but prose conflates the two

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper35_qec_holography/paper_draft.tex:86-89, 124-128, 130-138, 199-205`; `lean/SKEFTHawking/QECHolographyBridge.lean:139`
- **Observed:** Lean: `noncomputable def codeDistance : ℝ := H.horizon.areaLawKappa`. The definition does not depend on `H.encoding_obj` (the encoding anyon) — it depends only on `H.horizon`. So the "code distance" is a property of the substrate, not of any particular encoding choice. Paper §3 prose: "a localized boundary error must traverse `\dC` units of fusion-channel entropy before disturbing the logical operator." This is a per-encoding statement; the Lean definition does not capture it.
- **Evidence:** `QECHolographyBridge.lean:139` — definition does not pattern-match on `encoding_obj`. The QEC literature (Kitaev 2003, Hayden-Preskill 2007) uses "code distance" to mean the minimum weight of an undetectable logical error, which depends on the encoding choice. The paper's `\dC := \log d_{\max}` is more properly an *upper bound proxy* on the substrate side (the maximum quantum dimension among simple objects); calling it "code distance" without qualification is a misrepresentation.
- **Expected:** Either (a) rename the Lean definition to `substrateCodeDistanceProxy` or `topologicalShieldingScale` and update prose to match — making explicit it is a *proxy* on the substrate side, not the per-encoding distance, or (b) refactor to make `codeDistance` a function of `(H.horizon, H.encoding_obj)`, e.g. `log (H.horizon.quantum_dim H.encoding_obj)`. (Option (b) is more substantive but reframes the Fibonacci witness to use the τ anyon at d=φ.)
- **Fix:** Recommend (a) — add a docstring sentence at `codeDistance` clarifying "this is the substrate-level proxy `log d_max`; per-encoding code distance is a stricter quantity bounded above by this proxy via `H.horizon.d_max_upper`." Update paper §3 prose to read "`\dC := \log d_{\max}`, the maximum-fusion-channel-entropy proxy bounding the per-encoding code distance from above." Adjust the boxed prose accordingly at `paper_draft.tex:124-128`.

### 5.2 — 🔵 RECOMMENDED — abstract "ten substantive theorems" matches the file's `theorem` declarations exactly; counts.tex sources

- **Gate:** NumericalFreshness (Gate 9) — flagged for completeness
- **Location:** `paper35_qec_holography/paper_draft.tex:46, 256`
- **Observed:** Both abstract and §formalization say "ten substantive theorems"; my count of `^theorem ` declarations in `QECHolographyBridge.lean` returns 10. Match.
- **Evidence:** `grep -cE "^theorem " QECHolographyBridge.lean = 10`.
- **Expected:** If counts.tex retrofit lands for paper 35, this literal "ten" should become a counts-macro lookup. As of now, retrofit is not complete project-wide; flagged advisory.
- **Fix:** When the counts retrofit reaches paper 35, replace `ten` (lines 46, 256) with a `\input{}`-based macro.

### 6.1 — 🔵 RECOMMENDED — `horizon_BC_implies_HP_admissible` cross-bridge type-shape is opaque in prose

- **Gate:** AssumptionDisclosure (Gate 6)
- **Location:** `paper35_qec_holography/paper_draft.tex:236-249`; `lean/SKEFTHawking/QECHolographyBridge.lean:249-255`
- **Observed:** The Lean theorem signature is `horizon_BC_implies_HP_admissible (S_horizon : HorizonMTCBC → ℝ → ℝ) (h : H_HorizonBoundaryCondition H.horizon S_horizon) : 1 < H.horizon.d_max`. The hypothesis depends on a horizon-entropy function `S_horizon` parameter and the tracked-Prop bundle `H_HorizonBoundaryCondition`. Paper §7 prose describes only the bundle's "area-law / second-law / non-abelian envelope" content, but does not name the auxiliary `S_horizon` parameter. A reader cannot reconstruct the theorem signature from the prose.
- **Evidence:** Paper line 240-243: "takes a hypothesis instance of the project's `H_HorizonBoundaryCondition` structural assumption." No mention of `S_horizon`.
- **Expected:** Add one sentence noting "the assumption bundle is parametrized by an abstract horizon-entropy function `S_horizon`; the area-law-leading field of the bundle is the load-bearing input."
- **Fix:** At paper line 240-243, add: "the bundle is parametrized by an abstract horizon-entropy function (instantiated downstream by the project's `S_horizon` candidates), and the proof uses only the bundle's `areaLeading` field."

## Class 1 cache-skip summary

All seven bibitems are major published works, inspected by author/title/venue plausibility:
- `HaydenPreskill2007` — arXiv:0708.4025, JHEP 09, 120 (2007) — `cache-skip`.
- `AlmheiriDongHarlow2015` — arXiv:1411.7041, JHEP 04, 163 (2015) — `cache-skip`.
- `PYHP2015` — arXiv:1503.06237, JHEP 06, 149 (2015) — `cache-skip`.
- `YoshidaKitaev2017` — arXiv:1710.03363 (2017) — `cache-skip`.
- `KitaevAnyons2003` — arXiv:quant-ph/9707021, Annals Phys. 303, 2 (2003) — `cache-skip` (also cited identically in paper 36).
- `NayakAnyons2008` — RMP 80, 1083 (2008) — `cache-skip`.
- `KitaevPreskill2006` — arXiv:hep-th/0510092, PRL 96, 110404 (2006) — `cache-skip`.

## Class 4 cross-paper consistency

`KitaevAnyons2003` shared with paper 36 (center symmetry); both papers cite the identical bibitem (Annals Phys. 303, 2 (2003); arXiv:quant-ph/9707021). Consistent.

## Class 3 (placeholder/structural-tautology)

All ten cited theorems inspected:
- `one_le_globalDimSq` — substantive `Finset.single_le_sum` proof, OK.
- `scramblingTimeBound_nonneg` — uses `Real.log_nonneg`, OK.
- `codeDistance_nonneg` — inherits W3 result, OK.
- `recovery_at_scrambling_bound` — case-split `1 ≤ d_e` / `d_e < 1`, substantive, OK.
- `code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class` — load-bearing `Real.log_pos_iff` plus sum bound, substantive, OK.
- `horizon_BC_implies_HP_admissible` — invokes `H_HorizonBoundaryCondition.areaLeading` then `Real.log_pos_iff`, substantive, OK.
- `nonabelian_anyon_implies_codeDistance_pos` — invokes correctness-push, substantive, OK.
- `fibonacci_HPCode_codeDistance_lt_log_two` — full `√5 < 3` chain, substantive, OK.
- `fibonacci_HPCode_scramblingTimeBound_pos` — invokes correctness-push `.2`, substantive, OK.
- `trivialAbelian_violates_admissibility` — derives `1 < 1` contradiction via the biconditional, substantive, OK.

No P3/P4/P5 tautology patterns detected.
