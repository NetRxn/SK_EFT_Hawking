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

### Wave 1 — Table 1 regeneration [Pipeline: Stages 1, 2, 6, 7, 10]

**Problem:** Paper 1 Table 1 values were computed against a pre-correction parameter set. Current pipeline produces:

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

**Deliverables:**
- [ ] Rerun `uv run python -c "from src.core.transonic_background import ...; ..."` — regenerate Table 1
- [ ] Update `papers/paper1_first_order/paper_draft.tex` Table 1 (lines 247–251)
- [ ] Update inline `a_s` text (search for `109 a₀` / `5.77`)
- [ ] Rerun `scripts/review_figures.py` for fig1–fig4
- [ ] Copy regenerated PNGs to `papers/paper1_first_order/figures/`
- [ ] Add main-text note: κ profile-dependence (tanh=4.8 s⁻¹ vs Steinhauer's published step=290 s⁻¹, 60× factor) — currently only in caption
- [ ] Re-run `physics-qa:claims-reviewer` against Paper 1
- [ ] Re-run `physics-qa:figure-reviewer` on regenerated figures

**Estimated LOE:** 3–5 hours
**Risk:** Low — purely computational
**Depends on:** None (no Lean or MC blocker)

### Wave 2 — Paper 1 Son:2002 framing [Pipeline: Stage 10]

**Problem:** Paper 1 describes Son:2002 (hep-ph/0204199) as "Galilean-invariant / nonrelativistic", but the paper is titled *"Low-Energy Quantum Effective Action for **Relativistic** Superfluids"*.

**State:** Bibitem already extended to include Endlich et al. 2013 as co-citation (fixes partial attribution). Body text NOT yet rewritten.

**Deliverables:**
- [ ] Paper 1 lines 57, 69, 130 — clarify Son:2002 provides symmetry/EFT structure; non-relativistic adaptation follows Son-Wingate 2005 / Endlich et al. 2013
- [ ] Paper 2 line 448 — add Endlich co-citation to bibitem (matching Paper 1)

**Estimated LOE:** 30 minutes
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
- [ ] Paper 3 line 114 — either change "Z₂ × Z₂" → "Z₂" (if referring to SO(4k)), OR change "SO(4k)" → "Spin(4k)" (if referring to the spin group)

**Estimated LOE:** 5 min
**Risk:** None

### Wave 8 — Paper 10 "time-reversal" for ℤ₁₆ [Pipeline: Stage 10]

**Problem:** Paper 10 lines 197–198 say "topological superconductors with time-reversal symmetry have a ℤ₁₆ classification". Class D has NO time-reversal (particle-hole only). Kitaev's ℤ₁₆ (16-fold way) is specifically for 2D class D free-fermion ℤ reduced to interacting ℤ₁₆.

**Deliverables:**
- [ ] Paper 10 lines 197–198 — "2D topological superconductors in class D (particle-hole symmetry, **no time-reversal**), where anyonic excitations of the p+ip phase form a ℤ₁₆ classification (Kitaev's sixteenfold way)"
- [ ] Add `[FidkowskiKitaev2010]` bibitem (arXiv:0904.2197, PRB 81, 134509) — this is the correct reference for interacting ℤ₁₆ reduction; Kitaev 2009 alone gives ℤ (free)

**Estimated LOE:** 20 min
**Risk:** Low (textbook-level correction)

### Wave 9 — Paper 10 "16 = 8 × 2" numerology [Pipeline: Stage 10]

**Problem:** Paper 10 presents "16 = 8 × 2, where 8 is the Bott period and 2 is the Pfaffian factor" as the unifying physical insight. Bott period is 8 for π_n(O) (real K-theory) — correct. But "2 is the Pfaffian factor" is not a theorem; "16 = 8 × 2 connects all four 16s" is an aesthetic heuristic, not a derivation. Wang 2024 connects them via the Smith homomorphism, not via Bott × Pfaffian.

**Deliverables:**
- [ ] Paper 10 — replace with Smith homomorphism language: "Wang (2024) establishes the connection between the Rokhlin bound, ℤ₁₆ anomaly, and SM fermion count via the string bordism ℤ₂₄ class and Smith homomorphism. The relationship to the Kitaev ℤ₁₆ classification is suggestive but has not been formalized here."

**Estimated LOE:** 15 min

---

## Track D — Paper 10 Bibliography

### Wave 10 — Bibliography errors [Pipeline: Stage 10]

**Problem:** Paper 10 bibliography has multiple verifiable errors.

**Deliverables:**
- [ ] Paper 10 line 343 — ABP1967 page 256 → **271** (correct first page of Anderson-Brown-Peterson, *Structure of the spin cobordism ring*, Ann. Math. 86)
- [ ] Paper 10 line 334–335 — Stolz1993 (Math. Ann. 296, 685): verify this citation exists; if not, replace. The Stolz paper actually relevant to A(1) Ext / Rokhlin is NOT this one. Options:
  - (a) Remove Stolz1993 entirely (ABP1967 + Beaudry-Campbell cover the algebraic topology)
  - (b) Replace with correct Stolz citation (Ann. Math. 136, 511, 1992 — PSC work, if actually relevant)
- [ ] Paper 10 line 345 — BeaudryCampbell page 1 → **89** (reviewer claim; verify against Contemp. Math. 718)
- [ ] Paper 10 line 331 — Kitaev2009 bibitem: add end page `22–30`
- [ ] Paper 10 Rademacher citation for Casimir/24: add `[diFrancesco1997]` *Conformal Field Theory* (Springer, 1997) for physical interpretation of `c/24`
- [ ] Add `[FreedHopkins2021]` for framing anomaly context (Wang 2024 cites this extensively)

**Estimated LOE:** 30 min (or 1 h if primary-source verification needed)
**Risk:** Low

### Wave 11 — Paper 3 Adler page [Pipeline: Stage 10]

**Problem:** Paper 3 line 339 cites Adler et al. 2024, Nature 636, **87**. Correct first page per DOI 10.1038/s41586-024-08188-0 is **80** (pp. 80–85).

**Deliverables:**
- [ ] Paper 3 line 339 — change `87` → `80`

**Estimated LOE:** 1 min

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
- [ ] Either (a) Strengthen the theorem by adding a non-trivial Kitaev/bordism term connecting to one of the other 16s, OR
- [ ] (b) Add a docstring comment clearly disclosing: "This theorem records the four appearances of 16 but does NOT prove their equivalence. The physical connection is established conditionally via Wang 2024's Smith homomorphism (not formalized here)."
- [ ] Update Paper 10 to describe this theorem as "formally recorded" rather than "formally verified convergence"

**Estimated LOE:** 30 min (option b) / 2+ h (option a, requires Kitaev formalization)
**Risk:** Low (option b), Medium (option a)

### Wave 13 — `dai_freed_spin_z4` Equiv.refl placeholder [Pipeline: Stages 3, 10]

**Problem:** `Z16AnomalyComputation.lean:39` — theorem statement is `∃ (φ : ZMod 16 ≃ ZMod 16), Function.Bijective φ`. Proves nothing about Dai-Freed spin bordism groups; just that a bijection exists on a finite set (trivially true via `Equiv.refl`).

**Deliverables:**
- [ ] Add explicit docstring: "PLACEHOLDER. The actual cobordism computation Ω₅^{Spin^{Z₄}} ≅ ℤ₁₆ (Dai-Freed 1994) is beyond current Mathlib scope and remains an external hypothesis. This theorem only records that a bijection on ZMod 16 exists."
- [ ] Papers 9, 10 text update: "Lean-verified Dai-Freed theorem" → "Lean-formalized consequence of the Dai-Freed theorem (cobordism computation taken as external hypothesis)"

**Estimated LOE:** 15 min
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

| Wave | Scope | LOE | Priority |
|------|-------|-----|----------|
| Wave 1 | Paper 1 Table 1 regeneration | 3-5 h | 🔴 A (blocks PRL submission) |
| Wave 2 | Paper 1 Son:2002 framing | 30 min | 🟡 B |
| Wave 3 | Falque κ resolution (primary source read) | 1-2 h | 🔴 A (blocks Paper 12) |
| Wave 4 | Paper 12 c_s framing | 1 h | 🟡 B |
| Wave 5 | Paper 12 "programmable" | 30 min | 🟡 B |
| Wave 6 | Paper 12 "inside horizon" | 5 min | 🔵 C |
| Wave 7 | Paper 3 SO(4k) center | 5 min | 🟡 B |
| Wave 8 | Paper 10 ℤ₁₆ class D | 20 min | 🟡 B |
| Wave 9 | Paper 10 "16 = 8 × 2" | 15 min | 🟡 B |
| Wave 10 | Paper 10 bibliography | 30 min | 🟡 B |
| Wave 11 | Paper 3 Adler page | 1 min | 🟡 B |
| Wave 12 | sixteen_convergence_full | 30 min | 🟡 B |
| Wave 13 | dai_freed_spin_z4 | 15 min | 🟡 B |
| Wave 14 | claims-reviewer Layer 2 ext | 2 h | 🔵 C |
| Wave 15 | claims-reviewer Layer 4 ext | 4 h | 🔵 C (HIGH VALUE) |
| Wave 16 | claims-reviewer Layer 3b | 2 h | 🔵 C |
| Wave 17 | claims-reviewer Layer 5 ext | 3 h | 🔵 C |
| Wave 18 | Cross-LLM provenance | 2 h | 🔵 C (HIGH VALUE) |
| Wave 19 | Constants-source fidelity | 2 h | 🔵 C |
| Wave 20 | Invariant 11 + hook | 1 h | 🔵 C (HIGH VALUE) |

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
