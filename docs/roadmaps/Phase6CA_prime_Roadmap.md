# Phase 6CA′: D11-FHS Finite-Lattice Chern — the Adopted Fable-Targets Lane

## Technical Roadmap — July 2026 (follow-on; the D11/Phase-6CA lane's in-repo status ledger)

*Prepared 2026-07-20 at the Q1–Q2 checkpoint. The DETAILED execution authority remains the
scouted packet `temporary/working-docs/brainstorm/Fable-Targets/D11-FHS/` (README + roadmap +
audits) — this file is the in-repo status ledger + gate record, per the `Phase6o_prime_Roadmap.md`
follow-on convention. Portfolio context: `Fable-Targets/REMAINING_PRIORITY_PORTFOLIO.md`
(D11-FHS = "bounded proof lane; run branch-cut feasibility gate first"). Original authorization:
the D11 bundle row (comp-chem→D10 / topological-metamaterial→D11, Phases 6CA–6CE, authorized
2026-06-29 per `PAPER_STRATEGY.md`).*

**Project rules (inherited):** no PM/time estimates (task-count reference classes only);
kernel-purity `{propext, Classical.choice, Quot.sound}`; preemptive-strengthening + non-vacuity
pins on every carrier; the portfolio gates (current-HEAD re-validation at each wave launch;
statement semantics frozen before fan-out; data-level vs continuum claims strictly separated).

---

## Status ledger

| Gate/Wave | Status | Evidence (all merged to main, headliners `#print axioms`-pure) |
|---|---|---|
| **Packet validation** (current-HEAD drift check) | ✅ 2026-07-20 | All load-bearing audit claims verified; ONE favorable refutation: the feared 200–300-LOC `arg_mul_eq_add_arg_iff` crux is unnecessary — Mathlib's `Real.Angle` arg-homomorphism API carries it. No settled-fork/no-go collisions (the 5qH Arf/Rokhlin forks are unrelated). |
| **KILL-FAST SPIKE** (branch-cut / `Complex.arg` feasibility) | ✅ **GO** 2026-07-20 | `TopologicalBand/PrincipalBranch.lean`: `principal`/`branchIndex` (+`toIocDiv` sign FROZEN — the definitional choice), `arg_mul_branch_correction` (the `fieldStrength_decomp` primitive, ~4 lines), **`arg_plaquette_eq_principal_rawCurl`** (the exact 4-fold plaquette shape). |
| **Q0 freezes** | ✅ 2026-07-20 | Sign: `latticeChern := −∑ plaquetteBranch` so `∑ plaquetteArg = 2π·latticeChern`; orientation: CCW `U₀(k)U₁(k+ê₀)U₀(k+ê₁)⁻¹U₁(k)⁻¹`; `Circle`-coercion spike GREEN (zero friction — `Circle.coe_mul/inv/ne_zero/exp` all present). |
| **Q1 — finite torus + links** | ✅ 2026-07-20 | `TopologicalBand/FiniteTorus.lean`: `Torus := ZMod N₁ × ZMod N₂`, `shift` equivs, `shift_comm`, `sum_shift`, `sum_forwardDiff_eq_zero` (the telescoping engine). |
| **Q2 — latticeChern + INTEGRALITY + gauge invariance** | ✅ 2026-07-20 | `TopologicalBand/FHSLatticeGauge.lean`: **`sum_plaquetteArg_eq_two_pi_mul_latticeChern : ∑ k, plaquetteArg = 2π·(latticeChern : ℝ)`** + `latticeChern_gaugeInvariant` (telescoping cancellation, `Circle` commutativity). Non-vacuity (`FHSExamples.lean`): **`latticeChern 2 2 Uwit = 1`** (single −1-link flux quantum; exact per-vertex branch algebra, no native_decide; honest in-module caveat: the witness phases sit at the branch endpoint π — a LATTICE-integrality witness, not a continuum-Chern claim) + the negative fixture `latticeChern (trivial) = 0`. |
| **Q4 — Bloch-frame adapter** | ⏳ NEXT (dispatched 2026-07-20) | Connect the existing `BlochBundle.lean` substrate to the `Circle`-generic `latticeChern`: admissible link fields from sampled band frames. The integrality/gauge apex is already model-independent — the adapter only constructs links. |
| **Q4-Lane-C — QWZ `C = ±1`** | 🚧 **GATED** (own feasibility spike required) | The transcendental value-evaluation problem — ORTHOGONAL to the integrality mechanism; the Q2 GO does NOT leak here (spike report's explicit fence). |
| **Continuum bridge / D11 bundle lift** | 🚧 GATED (post-Q4; separate claims per the portfolio's data-level/continuum separation) | — |

## Wave 1a′-style discipline notes
- The lane's statements are **data-level (finite `ZMod` lattice)** claims; every docstring says so.
  No continuum-Chern claim is made anywhere until the continuum bridge clears its own gate.
- The recurring project lesson held here twice: the packet's own crux estimate and the audit's
  missing-lemma fear were both **more banked than claimed** (Mathlib `Real.Angle` API).
  Validate-first remains mandatory at every wave launch.
