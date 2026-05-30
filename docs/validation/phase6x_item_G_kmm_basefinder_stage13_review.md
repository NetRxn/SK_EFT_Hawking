# Phase 6x Item G — `cliffordTBaseFinder_kmm` (KMM base finder, ρ_CliffT picture) — Stage 13 review

**Date:** 2026-05-30  **Verdict:** ✅ **GREEN** (advisory closed)
**Reviewer:** fresh-context adversarial agent (read-only), per Wave Execution Pipeline Stage 13.

## Scope reviewed

`lean/SKEFTHawking/FKLW/RossSelinger/CliffordTBaseFinderKMM.lean` (commit `30ea3d9`) — the KMM-derived
Clifford+T base finder lifted into the Solovay-Kitaev headline's `ρ_CliffT` / `FreeGroup (Fin 2)`
picture via the phase bridge. Shipped declarations: `H_SU_mat_sq`, `coe_ρ_CliffT_fgH_sq`,
`signCorrect`, `coe_ρ_CliffT_signCorrect` (keystone), `signCorrect_kmmReduce_resynth`,
`cliffordTBaseFinder_kmm`, `cliffordTBaseFinder_kmm_approx`, `cliffordTBaseFinder_kmm_headline`.

## Findings

All seven adversarial checks passed with **no soundness defects**:

1. **Vacuity/triviality** — NONE. No tautology/identity-wrapper. Hypotheses (`ht`, `h00`, `h10`)
   jointly satisfiable (`gridFindT` is a genuine bounded Diophantine search; `h00` is dischargeable
   via `compileColumn_approx`). The `∃ w` is the honest `signCorrect (gridSynthWord …)`, the `2ε`
   bound a real `linftyOpNorm` bound.
2. **Sign-correction correctness** — NONE. The keystone closes in BOTH `phaseProd = ±1` branches
   (live goal `[]`); `H_SU_mat_sq` is genuinely `−I` (if `+I`, the `−1` branch would not close); the
   `neg_one_smul, neg_mul_neg, Matrix.mul_one` step yields `+toComplexMat`. `phaseProd_eq_one_or_neg_one`
   genuinely consumes `det = 1`.
3. **det-1 dependency** — NONE. `hconstr` (`normSq u + normSq t = ⟨0,0,0,2^k⟩`) honestly derived
   from `ZOmega.diophantineSearch_sound ht` (definitional `gridFindT` unfold) + `ring`; feeds
   `det_assembleUnitary`. No circularity.
4. **Norm identity** — NONE. `‖·‖` is `Matrix.linftyOpNorm` (the SK-headline norm) via the local
   instance; `approx_assembleUnitary` applied with matching hypotheses.
5. **Axiom hygiene** — NONE. `coe_ρ_CliffT_signCorrect` closes over `{propext, Classical.choice,
   Quot.sound}` only; `_headline`/`_approx`/`_resynth` add exactly the 4 pre-existing KMM
   `native_decide` box-cores (already allowlisted) — **no new axiom, no `sorryAx`, no `sorry`, no
   `maxHeartbeats`, no `axiom` declaration**.
6. **Honest-scope framing** — ADVISORY (cosmetic, now CLOSED). Framing verified accurate, not
   overclaiming: `_approx`/`_headline` carry the column-approximation hypotheses as genuine
   ASSUMPTIONS (soundness); the lightweight-finder unconditional headline claim cross-checks against
   `RossSelingerLightweight.lean:264`. The advisory: the `_headline` docstring's summary line could
   mislead a skimmer into thinking the length conjunct bounds the `FreeGroup` word `w` rather than
   the underlying `List CliffordTGate` gate word. **Closed** by tightening the docstring to name each
   conjunct's object explicitly (error → `w`; length → `gridSynthWord …` gate count).
7. **Compile gate** — NONE. `lean_diagnostic_messages` returns zero items.

## Disposition

GREEN. The lift is kernel-clean, the sign-correction algebra is verified in both phase branches, the
det-1 constraint is honestly derived, the norm is the real `linftyOpNorm`, and the scope is honestly
framed as SOUNDNESS — correctly deferring unconditionality over all `U` to the parked grid-completeness
piece, with the fully-unconditional 3-conjunct headline shipping via the lightweight density finder.
The sole (cosmetic) advisory was substantively closed by the docstring tightening.

Build clean (8986 jobs); counts 9773 theorems / 0 axioms / 0 sorry / 737 modules;
`axiom_closure_allowlist` + `counts_fresh` + `graph_integrity` all PASS.
