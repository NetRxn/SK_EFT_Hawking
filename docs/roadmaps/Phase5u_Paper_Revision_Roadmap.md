# Phase 5u: Paper Revision from April 2026 Review Round

## Technical Roadmap — April 2026

*Prepared 2026-04-13 | Triggered by: consolidated findings of 7 automated review documents (2026-04-10 Perplexity Citation + Comprehensive + LKB-Paris + IndependentVerification-01; 2026-04-12 Paper 10 Deep + Master Systematic Checklist + Updated Paper Assessment).*

**Scope:** Remediate substantive paper issues uncovered in the April review round. Separate from:
- Phase 5s (q-Serre sorry closure + Muger + FK axiom) — Lean formalization track
- Phase 6 (vestigial MC at scale) — compute track
- Phase 6 VerifiedStatistics — pipeline upgrade track

**Why a separate wave:** The issues fall into 4 categories:
1. **Post-parameter-correction stragglers** (Paper 1 Table 1, Paper 12 polariton values) — paper didn't get regenerated when constants.py was corrected
2. **Citation content errors** (Paper 3 Adler page, Paper 10 bibliography 4 issues, arXiv resolution) — beyond what `claims-reviewer` Layer 4 checks
3. **Lean content-meaningfulness** (`sixteen_convergence_full`, `dai_freed_spin_z4`) — theorems exist but encode nothing
4. **Textbook-fact errors in prose** (Paper 3 SO(4k) center, Paper 10 ℤ₁₆ in class D, Paper 10 "16 = 8 × 2")

These are **process gaps**, not just edits. The fix is both (a) do the paper edits and (b) close the process gaps so similar issues don't land in the next round.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read `temporary/working-docs/reviews/papers/2026-04-12-Perplexity/IndependentVerification-02.md` — authoritative findings
> 3. Read agent definitions: `.claude/plugins/physics-qa/agents/claims-reviewer.md`, `.claude/plugins/physics-qa/agents/figure-reviewer.md`
> 4. Do NOT modify Paper 6 to indicate MC crashed status — roadmap tracks this, paper should reflect post-MC-completion state (see Phase 4/5 roadmaps)

---

## Track A — Paper 1 Revision (Parameter Correction Propagation)

### Wave 1 — Table 1 regeneration [Pipeline: Stages 1, 2, 3, 6, 7, 10]

**2026-04-13 — scope expanded after discovering a provenance-grounded pipeline bug.**
What was originally "rerun transonic solver, update table" turned out to involve a
dimensional bug in `compute_dissipative_correction` that has been present since the
function was first committed (`d72f197`). The bug: treats Beliaev-derived transport
coefficients γ₁, γ₂ (units [m²/s]) as if they were damping rates (units [s⁻¹]),
missing a k_H² = (κ/c_s)² conversion factor. This produces δ_diss off by a factor
of ~10⁷–10⁸ from the correct Beliaev prediction.

Four of the project's internal authorities all agree on the correct formula:
- Lean docstring `SecondOrderSK.lean:352`: δ_diss = Γ_H / κ
- `formulas.first_order_correction`: matches Lean
- `formulas.beliaev_transport_coefficients`: returns γ in [m²/s], docstring explicit
- `provenance.py:657` `PAPER_DEPENDENCIES`: *"Γ_H = (γ₁+γ₂)(κ/c_s)²"*

Only `transonic_background.compute_dissipative_correction` is wrong. **The identity
Γ_H = (γ₁+γ₂) k_H² has no Lean theorem** — that is the root cause: without a Lean
anchor, a Python-layer dimensional mistake never tripped a validation check. Tests
pass because they use hand-picked γ values and only assert `|δ_diss| < 0.1`, which
any formula satisfies for small inputs.

**Original problem (parameter propagation):**
Paper 1 Table 1 values were computed against a pre-correction parameter set. Current pipeline produces:

| Platform | Quantity | Paper | Current | Δ |
|----------|----------|-------|---------|---|
| Steinhauer | c_s (mm/s) | 0.46 | 0.5476 | 19.0% |
| Steinhauer | ξ (μm) | 1.57 | 1.3344 | 15.0% |
| Heidelberg | c_s (mm/s) | 3.37 | 3.9194 | 16.3% |
| Heidelberg | ξ (μm) | 0.48 | 0.4159 | 13.4% |
| Trento | c_s (mm/s) | 1.83 | 2.1848 | 19.4% |
| Trento | ξ (μm) | 1.51 | 1.2644 | 16.3% |

All 6 rows outside 0.5% tolerance. Also:
- Inline `a_s = 5.77 nm = 109 a₀` (old) → `5.31 nm = 100.4 a₀` (current, van Kempen 2002)
- Figures 1–4 derived from these parameters need regeneration

**Deliverables — split into 4 sub-waves:**

#### Wave 1a — Fix `compute_dissipative_correction` dimensional bug [Pipeline: Stage 2]
- [ ] Edit `src/core/transonic_background.py:compute_dissipative_correction`:
  introduce `k_H_sq = (kappa / cs)**2`; set `Gamma_H = (gamma_1 + gamma_2) * k_H_sq`;
  call `first_order_correction(Gamma_H, kappa)`.
- [ ] Replace the contradictory inline comment "γ₁, γ₂ here have units [s⁻¹]" with
  the correct "γ₁, γ₂ in [m²/s] (EFT Lagrangian units); Γ_H = (γ₁+γ₂)(κ/c_s)² gives the damping rate".
- [ ] Remove the `hbar` local variable (unused, set but never referenced in the function).

#### Wave 1b — Ground the identification in Lean [Pipeline: Stage 3]
- [ ] Add a theorem to `SecondOrderSK.lean` (or equivalently `SKDoubling.lean`):
  `theorem gamma_H_from_transport (γ₁ γ₂ κ c_s : ℝ) (hc : c_s > 0) : Γ_H γ₁ γ₂ κ c_s = (γ₁+γ₂) * (κ/c_s)^2`
  with `Γ_H` defined as `(γ₁+γ₂) * (κ/c_s)^2` (i.e., the theorem is `rfl`-provable once the
  def is in place — the value is in formalizing the def, not in proving anything hard).
- [ ] Corollary: `delta_diss_from_transport : first_order_correction (Γ_H γ₁ γ₂ κ c_s) κ = (γ₁+γ₂) * κ / c_s^2`
- [ ] Update `formulas.first_order_correction` docstring to list this theorem as its `Lean:` anchor.

#### Wave 1c — Test coverage for the Beliaev→transport→correction chain [Pipeline: Stage 6]
- [ ] Add `tests/test_transonic_background.py::TestBeliaevChainConsistency` with:
  - `test_delta_diss_matches_Gamma_Bel_over_kappa`: run `beliaev_transport_coefficients`,
    feed to `compute_dissipative_correction`, verify `abs(δ_diss - Γ_Bel/κ) / (Γ_Bel/κ) < 1e-10`.
  - `test_gamma_units_consistent`: verify `Γ_H = (γ₁+γ₂) * (κ/c_s)²` within float tolerance
    for all three platforms.
  - `test_delta_diss_physical_magnitude`: at Steinhauer parameters, assert `1e-6 < δ_diss < 1e-3`
    (Beliaev regime; tightens the `< 0.1` bound that allowed the bug to persist).

#### Wave 1d — Regenerate paper Table 1 + body + figures [Pipeline: Stages 7, 8, 10]
- [ ] Rerun transonic solver with bugfix; regenerate all 6 rows of Table 1.
- [ ] Update `papers/paper1_first_order/paper_draft.tex` Table 1 (lines 247–251).
- [ ] Update inline `a_s` text: `5.77 nm (109 a₀)` → `5.31 nm (100.4 a₀)`.
- [ ] Add main-text note: κ profile-dependence (tanh ≈ 4.8 s⁻¹ vs Steinhauer step ≈ 290 s⁻¹ — 60× factor — currently only in caption).
- [ ] **Rewrite the γ₁ / damping-regime paragraph (§ 4 around line 282).** Paper currently
  states "γ₁ ~ 10⁻³ to 10⁻¹ s⁻¹" (Zaremba kinetic-theory, finite-T) and derives
  δ_diss ~ 10⁻⁵ to 10⁻³ without disclosing the regime choice. The pipeline's Beliaev
  prediction (zero-T, 3-phonon decay) gives ~10⁻⁵ — ~10× smaller than Zaremba at experimental T.
  Rewrite to explicitly present both regimes: "Pipeline prediction (Beliaev, T=0):
  δ_diss ≈ 2.4×10⁻⁵ (Steinhauer). Finite-T correction via kinetic-theory Zaremba
  damping is a factor ~10 larger at typical experimental temperatures." Cite Zaremba 1999
  and Beliaev 1958 explicitly. Paper's 4.2×10⁻⁴ headline value was apparently a
  hand-estimate from the Zaremba range — replace with pipeline-computed value with
  clear regime disclosure.
- [ ] Rerun `scripts/review_figures.py` for fig1–fig4. Copy regenerated PNGs.
- [ ] Re-run `physics-qa:claims-reviewer` against Paper 1.
- [ ] Re-run `physics-qa:figure-reviewer` on regenerated figures.

**Estimated LOE:** 3–5 hours
**Risk:** Low — purely computational
**Depends on:** None (no Lean or MC blocker)

### Wave 2 — Paper 1 Son:2002 framing [Pipeline: Stage 10]

**Problem:** Paper 1 describes Son:2002 (hep-ph/0204199) as "Galilean-invariant / nonrelativistic", but the paper is titled *"Low-Energy Quantum Effective Action for **Relativistic** Superfluids"*.

**State:** Bibitem already extended to include Endlich et al. 2013 as co-citation (fixes partial attribution). Body text NOT yet rewritten.

**Deliverables:**
- [x] Paper 1 lines 57, 69 — rewritten to clarify Son:2002 is the *relativistic* EFT framework; non-relativistic Madelung adaptation follows Endlich \textit{et al.} (PRD 88, 105001, 2013). Line 130 "Galilean Invariance" left as-is — it refers to the axiom constraint on the non-relativistic action used in the paper, which is correctly Galilean-invariant. (2026-04-13)
- [x] Paper 2 line 448 — bibitem extended: added Son relativistic title and Endlich co-citation. (2026-04-13)

**Estimated LOE:** 30 minutes — DONE
**Risk:** Low

---

## Track B — Paper 12 Polariton Parameter Resolution

### Wave 3 — Resolve Falque κ primary-source disagreement [Pipeline: Stage 1 provenance]

**Problem — CRITICAL:** Two LLM readings of Falque PRL 135, 023401 (2025) disagree:
- `src/core/provenance.py:430–442` (LLM verified 2026-03-31): "Falque 2025 demonstrated polariton horizons with SLM **but did not report surface gravity κ**. Value 5e10 s⁻¹ is an order-of-magnitude estimate..."
- `temporary/working-docs/reviews/papers/2026-04-10-Perplexity/LKB-Paris-Polariton-Assessment.md` (2026-04-10): "The measured surface gravity values are κ = 0.07 ps⁻¹ (smooth), κ = 0.08 ps⁻¹ (smooth), and κ = 0.11 ps⁻¹ (steep)."

**Resolution path:**
- [ ] Human read or third-LLM read Falque PRL 135, 023401 full text (not abstract)
- [ ] Document ground-truth: does Falque report κ values or not?
- [ ] If Falque DOES report κ:
  - [ ] Update `Paris_long.kappa` to 7–11 × 10¹⁰ range (or use 0.07 as conservative smooth default)
  - [ ] Update `provenance.py` detail + llm_verified_notes
  - [ ] Recompute derived quantities in Paper 12: T_H (~85–134 mK range instead of 61 mK), D, G(ω) threshold
- [ ] If Falque does NOT report κ:
  - [ ] Document where LKB audit got its numbers from (fabrication? Supplemental?)
  - [ ] Keep 5×10¹⁰ estimate; update provenance detail to cite source of estimate

**Estimated LOE:** 1–2 hours
**Risk:** Medium — depends on primary source access. If Falque does report κ, a chain of revisions propagates.

### Wave 4 — Paper 12 c_s framing [Pipeline: Stage 10]

**Problem:** Paper 12 abstract says c_s = 0.5 μm/ps "confirmed by three independent measurements". Provenance shows:
- Falque 2025: 0.40 μm/ps
- Estrecho 2021: 0.40 μm/ps
- Amo 2009: 0.81 μm/ps (resonant drive)

Median = 0.40; mean = 0.54. "0.5 μm/ps" is the arithmetic mean, not a value "confirmed" by all three (two agree on 0.40).

**Deliverables:**
- [ ] Paper 12 abstract: reword "confirmed by three independent measurements" → accurate phrasing ("representative midpoint of three independent measurements spanning 0.4–0.8 μm/ps, reflecting reservoir-corrected c_s") OR adopt Falque's 0.40 and recompute
- [ ] Consistency: decide whether to match Falque (primary source paper cites most) or keep blended value
- [ ] If switching to 0.40: update `Paris_long.c_s` = 4.0e5 m/s in constants.py, recompute derived values, update all papers using this parameter

**Estimated LOE:** 1 hour (phrasing) / 3 hours (if changing constant)
**Risk:** Low for phrasing, Medium for constant change (propagation)

### Wave 5 — Paper 12 "programmable" attribution [Pipeline: Stage 10]

**Problem:** "Programmable" appears in Giacobino & Jacquet lecture notes (arXiv:2512.14194), not in Falque PRL body. Falque uses "tunable" / "all-optical control".

**Deliverables:**
- [ ] Paper 12 lines 21, 56, 295 — either change "programmable" → "all-optically tunable" (Falque's language), OR add `\cite{Giacobino2025}` (arXiv:2512.14194) alongside Falque
- [ ] If adding Giacobino2025: add bibitem
- [ ] Optional: add other LKB ecosystem citations per LKB audit (Gil de Olivera 2025, Claude 2022, Guerrero 2025) — lower priority

**Estimated LOE:** 30 min

### Wave 6 — Paper 12 "inside horizon" phrasing [Pipeline: Stage 10]

**Problem:** Paper 12 line 58–59 says "inside the horizon"; Falque uses "in the supersonic regions".

**Deliverables:**
- [ ] Paper 12 line 58 — change "inside the horizon" → "in the supersonic (post-horizon) region"

**Estimated LOE:** 5 min
**Risk:** None

---

## Track C — Textbook-Fact Errors

### Wave 7 — Paper 3 SO(4k) center [Pipeline: Stage 10]

**Problem:** Paper 3 line 114 says "Z₂ × Z₂ for SO(4k)". Correct: center of SO(4k) is Z₂. Z₂ × Z₂ is center of **Spin**(4k).

**Deliverables:**
- [x] Paper 3 line 114 — rewritten to separate SO-group centers (Z₂ for SO(2k)) from Spin-group centers (Z₂ for Spin(2k+1), Z₄ for Spin(4k+2), Z₂×Z₂ for Spin(4k)). (2026-04-13)

**Estimated LOE:** 5 min
**Risk:** None

### Wave 8 — Paper 10 "time-reversal" for ℤ₁₆ [Pipeline: Stage 10]

**Problem:** Paper 10 lines 197–198 say "topological superconductors with time-reversal symmetry have a ℤ₁₆ classification". Class D has NO time-reversal (particle-hole only). Kitaev's ℤ₁₆ (16-fold way) is specifically for 2D class D free-fermion ℤ reduced to interacting ℤ₁₆.

**Deliverables:**
- [x] Paper 10 lines 196–200 — rewritten: "2D topological superconductors in symmetry class D (particle-hole symmetry, no time-reversal) admit a free-fermion ℤ classification that reduces to ℤ₁₆ under interactions." (2026-04-13)
- [x] Added `[FidkowskiKitaev2010]` bibitem (arXiv:0904.2197, PRB 81, 134509) for the interacting ℤ₁₆ reduction. (2026-04-13)

**Estimated LOE:** 20 min — DONE
**Risk:** Low (textbook-level correction)

### Wave 9 — Paper 10 "16 = 8 × 2" numerology [Pipeline: Stage 10]

**Problem:** Paper 10 presents "16 = 8 × 2, where 8 is the Bott period and 2 is the Pfaffian factor" as the unifying physical insight. Bott period is 8 for π_n(O) (real K-theory) — correct. But "2 is the Pfaffian factor" is not a theorem; "16 = 8 × 2 connects all four 16s" is an aesthetic heuristic, not a derivation. Wang 2024 connects them via the Smith homomorphism, not via Bott × Pfaffian.

**Deliverables:**
- [x] Paper 10 "16 Convergence" section — "16 = 8 × 2" numerology removed; replaced with Wang 2024 Smith homomorphism framing: "The four appearances of 16 are connected through the algebraic topology of spin structures in four dimensions: Wang (2024) establishes the relationship between the Rokhlin bound, the ℤ₁₆ anomaly, and the SM fermion count via the string bordism ℤ₂₄ class and the associated Smith homomorphism. The relationship to the Kitaev ℤ₁₆ classification is suggestive but has not been formalized here." (2026-04-13)

**Estimated LOE:** 15 min — DONE

---

## Track D — Paper 10 Bibliography

### Wave 10 — Bibliography errors [Pipeline: Stage 10]

**Problem:** Paper 10 bibliography has multiple verifiable errors.

**Deliverables:**
- [x] ABP1967 page 256 → **271** and title `Structure of the spin cobordism ring` added to bibitem. (2026-04-13)
- [x] Stolz1993 removed entirely — option (a) chosen. ABP1967 + BeaudryCampbell cover the algebraic topology needed; the Stolz PSC work is tangential to A(1) Ext / Rokhlin and the cited coordinates (Math. Ann. 296, 685) could not be verified. BeaudryCampbell now cited at Section 6 alongside ABP1967 (was orphan bibitem before). (2026-04-13)
- [x] BeaudryCampbell page 1 → **89** (also added title and end page 136 for completeness). (2026-04-13)
- [x] Kitaev2009 end page added (22–30). (2026-04-13)
- [x] `[diFrancesco1997]` *Conformal Field Theory* added for CFT/Casimir physical interpretation; line 138 reworded to distinguish analytic (Rademacher) from physical (diFrancesco + framing anomaly) origins of the 24 in the modular phase. (2026-04-13)
- [ ] `[FreedHopkins2021]` — NOT YET ADDED. Wang 2024 cites this for framing anomaly context. Consider adding in a future revision if referee requests deeper context. Low priority since the Wang citation already covers the framing-anomaly argument we use.

**Estimated LOE:** 30 min — DONE (except FreedHopkins addition, marked as future)
**Risk:** Low

### Wave 11 — Paper 3 Adler page [Pipeline: Stage 10]

**Problem:** Paper 3 line 339 cites Adler et al. 2024, Nature 636, **87**. Correct first page per DOI 10.1038/s41586-024-08188-0 is **80** (pp. 80–85).

**Deliverables:**
- [x] Paper 3 line 339 — changed `87` → `80`. (2026-04-13)

**Estimated LOE:** 1 min — DONE

---

## Track E — Lean Content-Meaningfulness

### Wave 12 — `sixteen_convergence_full` structural tautology [Pipeline: Stages 3, 10]

**Problem:** `RokhlinBridge.lean:88` theorem conclusion has four conjuncts:
1. `(∑ f, components f) = 16` — substantive (sum over SM fermions)
2. `(16 : ZMod 16) = 0` — `decide`-trivial
3. `∀ M, (16 : ℤ) ∣ M.signature` — literal echo of hypothesis `h_rokhlin`
4. `(∑ f, components f) = (16 : ℕ)` — re-typed version of #1

Proof: `⟨total_components_with_nu_R, by decide, h_rokhlin, total_components_with_nu_R⟩`. Theorem does NOT prove connection between the four 16s — only that 16 appears in four contexts.

**Deliverables:**
- [x] Option (b) chosen: comprehensive docstring added to `sixteen_convergence_full` in `RokhlinBridge.lean` disclosing the structural tautology — three of four conjuncts are either decide-trivial, hypothesis echoes, or retypes of the first. Docstring explicitly states the theorem enumerates but does NOT unify, that the physical connection is Wang (2024) external input, and directs papers to use "formally recorded" not "formally verified convergence". (2026-04-13)
- [x] Paper 10 "16 Convergence" section rewritten — now uses "formally recorded" language and the Wang Smith-homomorphism framing. (2026-04-13)

**Estimated LOE:** 30 min — DONE via option (b)
**Risk:** None (docstring-only change, no proof mods)

### Wave 13 — `dai_freed_spin_z4` Equiv.refl placeholder [Pipeline: Stages 3, 10]

**Problem:** `Z16AnomalyComputation.lean:39` — theorem statement is `∃ (φ : ZMod 16 ≃ ZMod 16), Function.Bijective φ`. Proves nothing about Dai-Freed spin bordism groups; just that a bijection exists on a finite set (trivially true via `Equiv.refl`).

**Deliverables:**
- [x] Comprehensive docstring added to `dai_freed_spin_z4` in `Z16AnomalyComputation.lean` — labels it PLACEHOLDER, explains the statement is trivially true (Equiv.refl), states the actual Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆ cobordism identification is external (García-Etxebarria–Montero / Dai-Freed), and instructs papers to describe it as an external hypothesis, not a Lean-verified fact. (2026-04-13)
- [x] Paper 8 line 431 reworded — "former ℤ₁₆ cobordism axiom discharged (tautological)" replaced with explicit "converted to trivially-true placeholder theorem (dai_freed_spin_z4) pending Mathlib cobordism theory; the cobordism computation is an external input, as standard in the ℤ₁₆ literature." (2026-04-13)
- [N/A] Paper 9, 10 — no claims of "Lean-verified Dai-Freed theorem" found; both papers already cite GarciaEtxebarria2019 as the source of the ℤ₁₆ bordism identification. Paper 9 §SPT Stacking formalizes the GROUP STRUCTURE of ℤ₁₆ stacking (legitimately proved by `decide`), not the cobordism identification. No updates needed there.

**Estimated LOE:** 15 min — DONE
**Risk:** None

---

## Track F — Agent Checklist Upgrades (Process Improvement)

### Wave 14 — claims-reviewer Layer 2 extensions [Pipeline: N/A — infrastructure]

**Problem:** Layer 2 currently checks theorem existence and absence of `sorry`. Does not check content meaningfulness.

**Deliverables:**
- [ ] Add **"vacuous conjunct" detector**: For each theorem cited in a paper, inspect the Lean source and check if the conclusion contains:
  - (a) `True` as a top-level term
  - (b) conjuncts that are literal echoes of hypotheses
  - (c) conjuncts that are `decide`/`rfl`-trivial AND no other non-trivial conjunct
- [ ] Add **"name / content match" detector**: For each theorem cited as "verification of X", check the Lean statement body mentions X (identifiers matching).
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md` to document these checks.

**Estimated LOE:** 2 h
**Risk:** Low

### Wave 15 — claims-reviewer Layer 4 extensions (citation integrity) [Pipeline: N/A]

**Problem:** Layer 4 only checks presence in CITATION_REGISTRY, not content correctness.

**Deliverables:**
- [ ] Layer 4a — **bibitem-registry consistency**: For each `\bibitem`, verify title / authors / journal / volume / page / year / DOI all match the registry entry verbatim.
- [ ] Layer 4b — **DOI resolution**: For each registry entry with DOI, fetch metadata via doi.org and compare against registry.
- [ ] Layer 4c — **arXiv resolution**: For each `arXiv:XXXX.XXXXX`, fetch arxiv.org metadata and compare. **This would have caught the Tier 1 catastrophic errors in one pass.**
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md`.

**Estimated LOE:** 4 h
**Risk:** Medium (depends on reliable API access)

### Wave 16 — claims-reviewer Layer 3b (prose-provenance consistency) [Pipeline: N/A]

**Deliverables:**
- [ ] For each parameter cited in a paper, compare paper's epistemic phrasing ("measured", "projected", "confirmed by N measurements") against `PARAMETER_PROVENANCE.tier` and `detail`. Flag mismatches.
- [ ] Update agent spec.

**Estimated LOE:** 2 h

### Wave 17 — claims-reviewer Layer 5 extensions (textbook facts) [Pipeline: N/A]

**Problem:** Layer 5 targets feasibility claims; misses textbook mathematical facts in prose (Paper 3 SO(4k), Paper 10 class D ℤ₁₆).

**Deliverables:**
- [ ] Add **"Referenced Textbook Facts"** sub-layer: extract mathematical factual claims that are not derived from formulas.py but presented as fact. For each, require either a `\cite{}` to authoritative source OR a Lean theorem. Missing support → WARN.

**Estimated LOE:** 3 h
**Risk:** Medium — hard to automate the extraction; may require LLM-driven classification.

### Wave 18 — NEW Layer 8: Cross-LLM provenance consistency [Pipeline: N/A]

**Problem:** `provenance.py` said Falque did not report κ; LKB audit said Falque reports κ = 0.07–0.11 ps⁻¹. No mechanism to detect this conflict.

**Deliverables:**
- [ ] For each `PARAMETER_PROVENANCE` entry with a `source` field citing an arXiv/DOI, search `Lit-Search/` and `temporary/working-docs/reviews/` for docs referencing the same source. Cross-check their claims.
- [ ] Flag conflicts as WARN with both texts quoted.

**Estimated LOE:** 2 h

### Wave 19 — NEW Layer 9: Constants-source fidelity [Pipeline: N/A]

**Deliverables:**
- [ ] For each parameter value in `constants.py`, compare against the specific values reported in its provenance `source` (when extractable).
- [ ] Flag WARN when constant value differs from primary source value without explicit tier explanation.

**Estimated LOE:** 2 h

### Wave 20 — NEW Invariant 11: constants.py change invalidates claims_review [Pipeline: Stage 12]

**Deliverables:**
- [ ] Add to Pipeline Invariants: "When `src/core/constants.py` changes, all `papers/paper*/claims_review.json` files are invalidated and claims-reviewer MUST be re-run against all papers before the next submission gate."
- [ ] Add git hook or validate.py check: compare `constants.py` mtime vs each `claims_review.json` mtime. Claims review older than constants change = FAIL.

**Estimated LOE:** 1 h

### Wave 21 — NEW Invariant 12: Lean-grounding audit for formulas.py [Pipeline: Stage 12]

**Problem discovered 2026-04-13 (during Wave 1 investigation):** The δ_diss dimensional
bug in `compute_dissipative_correction` escaped detection for the project's entire
lifetime because the **identification** Γ_H = (γ₁+γ₂)(κ/c_s)² existed only in prose
(`provenance.py:657`, docstring comments) — it had no Lean theorem. Pipeline Invariant 4
says *"Every formula has a Lean theorem"*, but the project interpreted this as "every
function name in formulas.py appears in some Lean docstring", not as "every function's
computational content has a machine-checked Lean statement that could be cross-verified
against the Python implementation".

The distinction matters: the `first_order_correction` function had its Lean anchor
(`firstOrder_correction_zero_iff`) — but that theorem only states δ_diss=0 iff Γ_H=0.
The critical identification that converts EFT transport coefficients to the horizon
damping rate was entirely unformalized. A reviewer running "check that each formula
has a Lean theorem" would mark `first_order_correction` as grounded and move on,
never seeing the unit mismatch.

**Deliverables:**
- [ ] Add to Pipeline Invariant 4: "A function F in `formulas.py` is considered Lean-grounded
  only if (i) F has a `Lean:` line in its docstring citing a specific theorem name,
  (ii) the cited theorem exists in `lean/SKEFTHawking/*.lean`, and (iii) the theorem's
  statement logically implies the Python computation (not just mentions it). Specifically
  for identities that convert between unit conventions (e.g., EFT coefficients to damping
  rates), the identity itself must be formalized — a theorem about boundary conditions
  (e.g., 'vanishes iff input zero') is not sufficient."
- [ ] Add to `scripts/validate.py` a new check `lean_grounding_audit`: for each function
  in `formulas.py`, find its `Lean:` reference, resolve it in the Lean source, verify the
  theorem's conclusion mentions the function's output structure.
- [ ] One-time audit: sweep all ~137 functions in `formulas.py`, identify which have weak
  Lean anchors (existence-only, vanishing-only) vs. strong anchors (the formula identity
  itself). Results → `docs/validation/lean_grounding_audit.md`.
- [ ] Update `.claude/plugins/physics-qa/agents/claims-reviewer.md` Layer 2 to include this
  strength-of-anchor check.

**Estimated LOE:** 3-4 h for infrastructure + audit sweep
**Risk:** Medium — may uncover more Lean-anchoring gaps similar to the δ_diss bug

**Why this is HIGH VALUE:** The δ_diss bug is a canary. If it existed 9 orders of magnitude
off for the project's entire history, there are almost certainly other weakly-anchored
formulas where smaller bugs could hide. Finding them before submission is worth significant
investigation time.

---

## Dependencies

```
Wave 1 (P1 Table 1) → Wave 2 (P1 Son:2002 framing) — independent
Wave 3 (Falque κ resolution) → Wave 4 (P12 c_s framing) → Wave 5-6 (P12 wording)
Wave 7-9 (textbook facts) — independent
Wave 10-11 (bibliography) — independent
Wave 12-13 (Lean quality) — independent
Wave 14-20 (agent upgrades) — independent, do in parallel with paper edits
```

All tracks are independent; maximum parallelism.

---

## Timeline

| Wave | Scope | LOE | Priority | Status (2026-04-13) |
|------|-------|-----|----------|---------------------|
| Wave 1a | Fix compute_dissipative_correction k_H² bug | 30 min | 🔴 A | IN PROGRESS 2026-04-13 |
| Wave 1b | Add Lean theorem `gamma_H_from_transport` | 30 min | 🔴 A | IN PROGRESS 2026-04-13 |
| Wave 1c | Test Beliaev→transport→correction chain | 30 min | 🔴 A | IN PROGRESS 2026-04-13 |
| Wave 1d | Regenerate Paper 1 Table 1 + body + figures | 2-3 h | 🔴 A (blocks PRL submission) | IN PROGRESS 2026-04-13 |
| Wave 2 | Paper 1 Son:2002 framing | 30 min | 🟡 B | **DONE 2026-04-13** |
| Wave 3 | Falque κ resolution (primary source read) | 1-2 h | 🔴 A (blocks Paper 12) | OPEN — requires human primary-source verification |
| Wave 4 | Paper 12 c_s framing | 1 h | 🟡 B | OPEN — depends on Wave 3 |
| Wave 5 | Paper 12 "programmable" | 30 min | 🟡 B | OPEN — depends on Wave 3 |
| Wave 6 | Paper 12 "inside horizon" | 5 min | 🔵 C | OPEN |
| Wave 7 | Paper 3 SO(4k) center | 5 min | 🟡 B | **DONE 2026-04-13** |
| Wave 8 | Paper 10 ℤ₁₆ class D | 20 min | 🟡 B | **DONE 2026-04-13** |
| Wave 9 | Paper 10 "16 = 8 × 2" | 15 min | 🟡 B | **DONE 2026-04-13** |
| Wave 10 | Paper 10 bibliography | 30 min | 🟡 B | **DONE 2026-04-13** (FreedHopkins deferred) |
| Wave 11 | Paper 3 Adler page | 1 min | 🟡 B | **DONE 2026-04-13** |
| Wave 12 | sixteen_convergence_full | 30 min | 🟡 B | **DONE 2026-04-13** (docstring option b) |
| Wave 13 | dai_freed_spin_z4 | 15 min | 🟡 B | **DONE 2026-04-13** |
| Wave 14 | claims-reviewer Layer 2 ext | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 15 | claims-reviewer Layer 4 ext | 4 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 16 | claims-reviewer Layer 3b | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 17 | claims-reviewer Layer 5 ext | 3 h | 🔵 C | OPEN — infrastructure |
| Wave 18 | Cross-LLM provenance | 2 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 19 | Constants-source fidelity | 2 h | 🔵 C | OPEN — infrastructure |
| Wave 20 | Invariant 11 + hook | 1 h | 🔵 C (HIGH VALUE) | OPEN — infrastructure |
| Wave 21 | Invariant 12: Lean-grounding audit | 3-4 h | 🔵 C (HIGH VALUE) | OPEN — uncovered by Wave 1 investigation |

**Progress 2026-04-13**: Waves 2, 7, 8, 9, 10, 11, 12, 13 complete (8 of 13 substantive waves). Remaining substantive: Wave 1 (Paper 1 Table 1 — requires MC-free window to run transonic solver) and Waves 3–6 (Paper 12 polariton — requires human primary-source verification of Falque PRL). Track F (agent checklist upgrades) untouched per user directive (substantive fixes only).

**Total**: ~24 hours of edit + verification work; ~17 hours of agent upgrades. Parallelizable to 1–2 working days with concurrent tracks.

---

## What Success Looks Like

- Paper 1 Table 1 matches current pipeline to <0.5%; claims-reviewer passes with zero FAIL.
- Paper 12 parameters (c_s, κ, T_H, D) are consistent between abstract / table / constants.py / provenance — and defensibly match primary sources.
- Paper 3, Paper 10 textbook-fact errors all corrected.
- Paper 10 bibliography pages / citations all verified against primary sources.
- `sixteen_convergence_full` either strengthened or honestly labeled as "record of four 16s"; `dai_freed_spin_z4` labeled as placeholder.
- `claims-reviewer` agent can now catch:
  - Catastrophic arXiv errors in one pass (Wave 15)
  - Vacuous Lean theorems (Wave 14)
  - Constants/source drift (Waves 18, 19)
  - Stale claims_review after constants.py change (Wave 20)

**After Wave 20**, the process failures that caused this review round are systemically prevented, not just patched paper-by-paper.

---

## Out of Scope

- **Counts**: Per user directive (2026-04-13), count staleness is deferred — counts will change as Lean work continues. Will be reconciled atomically at paper submission.
- **Paper 6 MC status**: Per user directive, paper is NOT modified to indicate crashed status. Phase 4/5 roadmaps already track MC not-done. The Apr 10 reviews referenced legacy `run_vestigial_production.py` runs (fermion-bag), **which was superseded on 2026-04-02 by HS+RHMC** (see Phase6_Roadmap line 30, 63: "fermion-bag hits O(V⁴) percolation wall"). The current production path is `scripts/run_rhmc_epochs.sh --l 8` using `run_rhmc_production.py` (Rust-accelerated via `sk_eft_rhmc`). L=8 state as of 2026-04-13: only 2 couplings completed (g=0.5, g=2.0 from Apr 10); needs full coupling scan to resolve vestigial phase. Any new MC production for Paper 6 must use the HS+RHMC path, not the legacy fermion-bag path.
- **Lean 4.29 build errors in 3 files (Uqsl2AffineHopf, Uqsl3Hopf, TetradGapEquation)**: Tracked in parallel Lean session (Phase 5s Wave 8, Uqsl3Hopf F01 closure). Not duplicated here.
- **Mathlib PR process** (Phase 5g Wave 4+): Independent track, out of scope.
- **arXiv voucher / paper submissions** (Phase 5g Wave 7+): Depends on Tier A items (Wave 1, Wave 3) completing first.

---

*Phase 5u roadmap. Created 2026-04-13. All items trace to IndependentVerification-02.md. Follows [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
