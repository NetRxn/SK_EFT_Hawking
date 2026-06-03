# Phase 6AJ — Fidelity-domain data processing (MOONSHOT E, public)

**Status:** PLANNED (opened 2026-06-02). Public-only. Lifts the general-state network monotonicity
from the trace-distance domain (shipped: `traceDist_applyChain_le`) into the **fidelity** domain, so
a downstream chain certificate can live in fidelity, not only trace distance.

**The target.** Uhlmann's monotonicity / data-processing inequality for fidelity: for any CPTP map
`Φ` and density operators `ρ, σ`,
`F(Φρ, Φσ) ≥ F(ρ, σ)`  (equivalently `sqrtFidelity(Φρ,Φσ) ≥ sqrtFidelity(ρ,σ)`),
and then the chain corollary mirroring `traceDist_applyChain_le`:
`sqrtFidelity(applyChain K ρ, applyChain K σ) ≥ sqrtFidelity(ρ, σ)` (fidelity is non-decreasing along
a CPTP network — the opposite monotone direction from trace distance).

**Why it's a moonshot.** Fidelity DP is genuinely harder than trace-distance DP. The standard proofs
go through (i) Uhlmann's theorem (fidelity = max overlap over purifications) + Stinespring, or (ii) an
integral / variational representation of fidelity, or (iii) operator-concavity / joint concavity of
fidelity (Lieb). Pinned Mathlib likely lacks all three packaged. We DO have, as scaffolding: the
Uhlmann `sqrtFidelity` definition + `sqrtFidelity_eq_traceNormOf` (`F = ‖√σ√ρ‖₁`), the trace-norm
machinery, CPTP/Kraus model, and trace-distance DP (`traceDist_krausMap_le`).

**Invariants:** kernel-pure; **NO new project-local axiom without explicit user sign-off**;
fence-discipline (interactive lean4 scouting + written blocker for any new fence). If the full DP
inequality is unreachable, a strictly-weaker-but-honest deliverable (e.g. fidelity DP for the
restricted unital / mixed-unitary case, or a joint-concavity lemma) is acceptable and must be labeled
as the restricted result, not the general one.

---

## Wave 6AJ.0 — Mathlib scouting (interactive lean4 skill, NOT deep research)
Via `lean_local_search`/`lean_leansearch`/`lean_loogle`: search for purifications, Uhlmann's theorem,
Stinespring dilation, joint concavity of fidelity, operator concavity (`OperatorConcave`/Löwner),
`√` operator-monotonicity (Ando), and any fidelity monotonicity already in Mathlib's quantum-info /
matrix-analysis corner. Output: present/absent table with exact names. This decides the route.

## Wave 6AJ.1 — Route selection + core inequality
Pick the most-supported route:
- **(a) Operator-monotone / Ando route:** if `√` operator-monotonicity + a Kraus-map Löwner argument
  are reachable, prove DP directly on `F = ‖√σ√ρ‖₁` via the trace-norm contraction already used for
  `traceDist_krausMap_le` (the pos/neg-part / dual-norm keystone may transfer).
- **(b) Block-matrix / joint-concavity route:** prove joint concavity of `(ρ,σ) ↦ F(ρ,σ)` (Lieb) and
  derive DP from concavity + the channel as an average of unitaries (for the mixed-unitary subclass)
  or via the Choi/dilation if reachable.
- **(c) Uhlmann-purification route:** only if Stinespring/purification is reachable in pin (likely not).
Headline `sqrtFidelity_krausMap_ge` (CPTP fidelity DP), with hypotheses honestly scoped to whatever
subclass the chosen route supports.

## Wave 6AJ.2 — Chain corollary + symmetry with trace-distance
`sqrtFidelity_applyChain_ge` mirroring `traceDist_applyChain_le`; note the monotone-direction duality
(trace distance ↓, fidelity ↑) consistent with FvdG. Recommend (do not scope) the private chain cert
gain a fidelity-domain branch.

## Wave 6AJ.3 — Consolidation
Headline(s) + D6 §6 + preprint update; Stage-13.

---

## Phase exit (two acceptable outcomes)
EITHER (a) general (or honestly-scoped restricted) fidelity DP `sqrtFidelity_krausMap_ge` + the chain
corollary, PROVEN kernel-pure; OR (b) a fence with an interactive-lean4-verified written blocker and
the partial deliverable (e.g. joint concavity, or the restricted-subclass DP) clearly labeled. NO
axiom without sign-off. Counts/docs/memory synced.

---

## OUTCOME (2026-06-02, autonomous /goal) — PARTIAL: reversible-channel fidelity DP SHIPPED + general CPTP FENCED

**Wave 6AJ.0 scout (interactive lean4 on Mathlib v4.29.1).** PRESENT: operator-monotone
`CFC.monotone_sqrt`. ABSENT (verified — leansearch/loogle): joint concavity of fidelity, operator
convexity of `t⁻¹` (Choi's inequality), Lieb concavity, purification / Stinespring dilation. ⟹ the
general-CPTP and mixed-unitary Uhlmann-monotonicity routes all lack a ready theorem.

**SHIPPED (constructive, the reachable toehold):** `FidelityDataProcessing.lean` (root-imported,
kernel-pure) — fidelity is exactly invariant under unitary conjugation, i.e. data processing for the
*reversible* (unitary-channel) subclass as an EQUALITY:
- `posSemidef_unitary_conj`: `U M Uᴴ ⪰ 0`.
- `psdSqrt_unitary_conj`: `√(U M Uᴴ) = U √M Uᴴ` (via `posSemidef_eq_of_mul_self_eq` — NO CFC
  conjugation lemma needed, dodging the Mathlib gap).
- `absOp_unitary_conj`: `|U A Uᴴ| = U |A| Uᴴ`.
- `traceNorm_unitary_conj`: `‖U A Uᴴ‖₁ = ‖A‖₁` (modulus conjugation + trace cyclicity).
- `sqrtFidelity_unitary_conj`: **`F(UρUᴴ, UσUᴴ) = F(ρ, σ)`** — the headline reversible-channel DP.

**FENCED (no axiom):** the general CPTP Uhlmann monotonicity `F(Φρ,Φσ) ≥ F(ρ,σ)` and the
mixed-unitary subclass — blocked at this pin without joint concavity / operator-convex inverse /
purification. Recommendation for a future phase: formalize joint concavity of fidelity (unlocks
mixed-unitary directly from the shipped unitary case), or operator-convexity of `t⁻¹` + the
variational form `F = inf_X ½(tr Xρ + tr X⁻¹σ)` (the elementary route to full CPTP monotonicity).
