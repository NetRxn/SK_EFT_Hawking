---
paper: E2
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-05-06T00:00:00Z
readiness_gates_version: 1
scope: cross-bundle propagation verification post Session-3 D1 fabricated-bibitem fixes
---

# Adversarial Review — E2 (cross-bundle propagation r1)

## Summary

Verdict: **GREEN — no blockers, no required findings.** Both fixed bibitems
(Geurs2025, Majumdar2025) verified against arXiv with exact title and
author-prefix match. The narrative attribution at E2 line 169
(η/s ≈ 4 × ℏ/(4π k_B) attributed to Majumdar2025) is **correctly grounded**
— the prior-task hypothesis that this conflated η/s with the universal
σ_Q ≈ 4 e²/h is wrong: the Majumdar abstract explicitly reports BOTH
η/s within-factor-of-four of KSS AND σ_Q ≈ 4 e²/h AND the >200×
Wiedemann-Franz violation. E2 ↔ D1 §7 cross-bundle bibitem coordinates
agree exactly. Three RECOMMENDED hygiene items below; none gate-impacting.

## Findings

### 1.1 — Cache-verifiable — Geurs2025 bibitem ↔ arXiv:2509.16321

- **Gate:** CitationIntegrity
- **Location:** `papers/E2/paper_draft.tex:398–401`
- **Observed (E2):** `J.~Geurs et al., "Supersonic flow and hydraulic jump in an electronic de Laval nozzle," arXiv:2509.16321 (2025).`
- **Evidence (WebFetch arXiv:2509.16321):**
  - Title: "Supersonic flow and hydraulic jump in an electronic de Laval nozzle" (exact match)
  - First author: Johannes Geurs (matches "J.~Geurs")
  - Co-authors include Watanabe, Taniguchi, Basov, Hone, Lucas, Pasupathy, Cory R. Dean (consistent with "Dean-Kim-Lucas team" framing in body)
  - Abstract demonstrates "compressible electron flow in bilayer graphene through an electronic de Laval nozzle"
- **Verdict:** `match`. Submission-clean. Cross-bundle agreement with `D1:808-812` confirmed (identical title + arXiv ID + author prefix).

### 1.2 — Cache-verifiable — Majumdar2025 bibitem ↔ arXiv:2501.03193

- **Gate:** CitationIntegrity
- **Location:** `papers/E2/paper_draft.tex:403–407`
- **Observed (E2):** `A.~Majumdar et al., "Universality in quantum critical flow of charge and heat in ultra-clean graphene," Nature Physics 21, 1374 (2025), arXiv:2501.03193.`
- **Evidence (WebFetch arXiv:2509.03193 → 2501.03193):**
  - Title: exact match
  - First author: Aniket Majumdar (matches "A.~Majumdar")
  - Abstract explicitly: "the effective dynamic viscosity (η_th) in the thermal regime approaches the holographic limit η_th/s_th → ℏ/4πk_B within a factor of four in the cleanest devices"
  - Abstract: "σ_Q converges to ≈ (4±1)×e²/h"
  - Abstract: "giant violation of the Wiedemann-Franz law where the effective Lorentz number exceeds the semiclassical value by more than 200 times"
- **Verdict:** `match`. Cross-bundle agreement with `D1:814-818` confirmed.

### 5.1 — 🟢 NARRATIVE-CONSISTENT — η/s attribution at E2:169 is correctly grounded

- **Gate:** NarrativeGrounding
- **Location:** `papers/E2/paper_draft.tex:168–169` and `:64–69`
- **Observed (E2 §3):** "With Majumdar et al.'s [Majumdar2025] η/s ≈ 4 × ℏ/(4π k_B) and T ≈ 150 K..."
- **Observed (E2 §1):** "...with η/s within a factor of four of the Kovtun-Son-Starinets bound [KSS2005]..."
- **Pre-task hypothesis:** Reviewer was asked to flag if the η/s claim conflated η/s with the universal conductivity σ_Q ≈ 4 e²/h reported as the headline KSS-style "4±1" universality.
- **Evidence:** The Majumdar abstract reports THREE distinct universality claims:
  1. σ_Q ≈ (4±1) × e²/h (universal conductivity)
  2. >200× Wiedemann-Franz violation
  3. η_th/s_th → ℏ/(4π k_B) within a factor of four (in cleanest devices, thermal regime)
  E2 cites (1) at lines 38, 66, 220, 258, 274 (correctly as σ_Q), (2) at line 67 (correctly as Wiedemann-Franz), and (3) at line 169 (correctly as η/s). No conflation.
- **Verdict:** `narrative-consistent`. NO finding — flagged in this section so the next reviewer does not re-litigate the pre-task hypothesis.
- **Caveat (RECOMMENDED, not BLOCKING):** Majumdar's η/s within-factor-of-four claim is for the **thermal-regime effective dynamic viscosity** (η_th) in the **cleanest devices**, not necessarily the Dean-nozzle device used by Geurs2025. E2 implicitly transports the bound across devices. This is a defensible (and publishable) modeling assumption — both the Geurs and Majumdar samples are bilayer-graphene Dirac-fluid in the high-mobility hBN-encapsulated regime — but the prose elides the device-equivalence assumption. **Suggested clarification (one sentence at E2:168):** "Adopting Majumdar et al.'s thermal-regime η/s bound for the Dean-equivalent ultra-clean bilayer-Dirac-fluid regime..." would close the inferential gap.

### 4.1 — 🟢 CROSS-BUNDLE-CONSISTENT — E2 ↔ D1 §7 graphene anchor

- **Gate:** CrossPaperConsistency
- **Location:** `papers/E2/paper_draft.tex` vs `papers/D1/paper_draft.tex:567–700`
- **Observed:** Both papers cite Geurs2025 (D1:808, E2:398) and Majumdar2025 (D1:814, E2:403) with identical bibitem text, identical arXiv IDs, identical Nature Physics venue for Majumdar.
- **Cross-claim consistency check:**
  - T_H ≈ 2.4 K — D1:572 vs E2:29 — **agree**
  - δ_disp ≈ −2.8% — D1:632 vs E2:32, 163 — **agree**
  - δ_diss ∼ 10⁻¹³ — D1:632 vs E2:32, 175 — **agree**
  - Closed-form noise PSD ΔS_I = 2ℏω σ_Q Γ(ω) n_H(ω) — D1:644-646 vs E2:215-216 — **identical**
  - σ_Q ≈ 4 e²/h — D1 (implicit via cross-ref to E2) vs E2:38, 66, 220 — **consistent**
  - >200× Wiedemann-Franz — D1:661-662 vs E2:67-68 — **agree**
  - 92% Lean theorem reuse — D1:599 vs E2:120 — **agree** (E2 says "~92%" approximating D1's precise 109/119)
  - Greybody Γ₀ ≈ 0.99994 — D1:654 vs E2:43, 238 — **agree**
- **Verdict:** `cross-consistent`. NO finding.

### 1.3 — 🔵 RECOMMENDED — Falque2025 not part of this propagation but should be noted

- **Gate:** CitationIntegrity
- **Location:** `papers/E2/paper_draft.tex:385-388`
- **Observed:** `K.~Falque et al., Phys. Rev. Lett. 135, 023401 (2025) [arXiv:2311.01392].` — bibitem has arXiv ID and PRL coordinates but no title.
- **Verdict:** Per task brief, this bibitem was UNCHANGED in Session-3 (already had correct K.~Falque + PRL coordinates). It is **not used in E2 §1 or §2 prose** — grep shows no `\cite{Falque2025}` in E2 body. The bibitem is therefore a dangling registry entry in E2's bibliography. **Recommendation:** either add a single body citation (e.g., in §1 alongside Steinhauer2016/deNova2019 as a third BEC analog-Hawking observation prior-art reference) OR remove the dangling bibitem. Severity 🔵 RECOMMENDED — not gate-impacting; cosmetic-bibliography hygiene.

### 5.2 — 🔵 RECOMMENDED — Zhao2023 lacks publication coordinates

- **Gate:** NarrativeGrounding (low-severity)
- **Location:** `papers/E2/paper_draft.tex:413–416`
- **Observed:** `Y.~Zhao et al., "Direct measurement of the Dirac-fluid sound speed c_s = v_F/√2 via hydrodynamic plasmon spectroscopy (2023)."` — no arXiv ID, no journal, no DOI.
- **Evidence:** Zhao2023 is cited at E2:71 as the load-bearing source for c_s = v_F/√2. The bibitem has no verifiable coordinates.
- **Verdict:** 🔵 RECOMMENDED. Not in the explicit Session-3 fix scope, but represents a residual citation-hygiene issue for E2. Suggest the next bibitem-verification pass add an arXiv ID or DOI. Out of scope for the cross-bundle propagation r1 task; flagging for next-session backlog.

### 5.3 — 🔵 RECOMMENDED — "first electronic sonic horizon" first-claim (E2:60)

- **Gate:** NarrativeGrounding
- **Location:** `papers/E2/paper_draft.tex:60-62`
- **Observed:** "...demonstration of supersonic electron flow through a de Laval nozzle in bilayer graphene created the **first electronic sonic horizon**..."
- **Verdict:** This is a Geurs2025-attributed first-claim, not an E2-author-original first-claim, so it is the source paper's claim and E2 is reporting it. The Geurs abstract supports it ("compressible electron flow... accelerates carriers past the speed of sound, resulting in shock phenomena"). 🔵 RECOMMENDED only as a marker that E2's chain-of-attribution rests on Geurs2025's own first-claim — not E2's responsibility but inherited. No action needed.

## Cross-bundle propagation summary

| Bibitem | E2 Status | D1 §7 Status | Cross-bundle agreement |
|---|---|---|---|
| Geurs2025 | Fixed Session-3, arXiv:2509.16321 + exact title | D1:808-812 same | ✅ identical |
| Majumdar2025 | Fixed Session-3, arXiv:2501.03193 + Nature Physics 21:1374 + exact title + corrected first author A.~Majumdar | D1:814-818 same | ✅ identical |
| Falque2025 | Unchanged — PRL+arXiv but unused in E2 body | (not cited in D1 §7) | ✅ no inconsistency |

E2 stage9/10/13 readiness post-Session-3 fixes is **GREEN-confirmed** with respect to the 2 fixed bibitems and the η/s narrative attribution. No blockers reopen. The 3 RECOMMENDED items above are hygiene-level and do not reopen any readiness gate.

## QI Candidate (optional)

**QI-1 (RECOMMENDED, low-severity):** Cross-bundle propagation verification of Session-3 D1 fixes worked correctly for E2 — both fixed bibitems propagated cleanly because the bibliography-edit was applied symmetrically to both bundles in Session-3. Suggest adding a `scripts/validate.py --check cross_bundle_bibitem_consistency` that for each shared bibkey across `papers/*/paper_draft.tex` parses the bibitem text and asserts exact match (or normalized title+arXiv-ID match). This would automate the manual cross-bundle audit performed here and catch single-bundle bibitem fixes that miss companion bundles.

**QI-2 (RECOMMENDED, narrative-discipline):** The pre-task hypothesis "Majumdar's '4 ×' is the universal conductivity, NOT η/s" turned out to be incorrect — Majumdar reports BOTH a "4 ×" σ_Q AND a "within factor of four" η/s bound. The latter was easy to miss because the abstract's headline universality is σ_Q. Suggest the abstract-grep step in `claims-reviewer` capture all "universal" / "factor-of-four" / "approaches the bound" claims, not just the lead claim.
