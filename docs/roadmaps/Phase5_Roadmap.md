# Phase 5: Conditional Extensions

## Technical Roadmap — Updated March 2026

*Originally prepared 2026-03-25. Updated 2026-03-27 after Phase 4 completion and Wave 5 quality hardening.*

---

## Execution Process

**All Phase 5 work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** 12 stages in strict order. No skipping. Consult the [Inventory Index](../../SK_EFT_Hawking_Inventory_Index.md) before making changes.

---

## 0. Entry State (Phase 4 Actual Results)

Phase 4 is complete. These are the actual results, not projections:

| Item | Result | Implication for Phase 5 |
|------|--------|------------------------|
| **Vestigial gravity (Paper 6)** | Numerically confirmed. Three-phase structure: pre-geometric (G/G_c < 0.8), vestigial (0.8-1.0), full tetrad (>1.0). Curvature-based criterion. | Vestigial phase is real. ADW route to gravity has a concrete intermediate phase. |
| **Fracton Layer 2** | Formalized. Fracton hydro retains exponentially more UV information than standard hydro. Binomial charge counting verified. | Alternative to gauge erasure — fracton Layer 2 preserves more structure. |
| **Fracton-gravity bootstrap** | DOF gap = d-1 for all d ≥ 2. Bootstrap diverges at n ≥ 2. 4 structural obstacles identified. | Gravity connection exists but is incomplete — obstacles are real, not artifacts. |
| **Non-Abelian fracton** | **Negative result.** All fracton gauge types are YM-incompatible. 4 independent obstructions. | 5E is cancelled. Non-Abelian fracton route is closed. |
| **Backreaction** | Acoustic BHs cool toward extremality (opposite Schwarzschild). Cooling timescales computed for 3 platforms. | Extremality approach is universal. Strengthens experimental feasibility. |
| **Chirality wall** | TPF evades 2/4 GS conditions (translation invariance, ancilla fields). Wall status: **conditional** — not blocked, not open. | 5A trigger is partially met. Breach is conditional on remaining 2 conditions. |
| **Experimental predictions** | Platform-specific spectral tables for Steinhauer, Heidelberg, Trento. κ-scaling test identified as most accessible. | Ready for comparison when data arrives. |
| **He-3 analogy** | GL phase diagram complete. A-phase unstable, B-phase stable. 4D Lorentzian gravity analogous to B-phase. | Analogy is concrete and testable. |

**Verification state at entry:** 216 theorems + 1 axiom (zero sorry, 56 Aristotle-proved), 822 tests, 14/14 validation checks, 45 figures, 6 papers, 16 notebooks.

---

## 1. Conditional Work Items

### 5A. Gu Topological Supergravity Completion [LLM + Lean]

**Trigger:** TPF 4+1D gapped interface conjecture is proven (remaining 2 GS conditions resolved).

**Phase 4 update:** The chirality wall analysis showed TPF evades 2 of 4 GS no-go conditions. The remaining 2 (Lorentz invariance and on-site symmetry) are active research problems in the SMG community. The wall is **conditional**, not blocked — progress on either remaining condition would narrow the gap.

**Goal:** If chiral fermions can be produced on a lattice, formalize the full UV-complete path: string-net → chiral fermions → ADW tetrad → Einstein gravity. This would be the first complete emergent gravity program from a bosonic starting point.

**The calculation:**
1. Start from Fang-Gu (2023) topological supergravity construction
2. Replace fundamental fermions with TPF lattice chiral fermions
3. Check: does the ADW mechanism still produce tetrad condensation?
4. Check: does Vergeles's unitarity proof extend to this setting?
5. If yes to both: complete UV-to-IR chain with formal verification

**Estimated LOE:** Very High (multiple sessions)
**Risk:** Very High — depends on unproven conjecture, may hit new obstructions
**Status:** `conditional` — 2/4 GS conditions evaded, waiting on remaining 2

---

### 5B. Monte Carlo eta/s for Emergent SU(2) [Numerical Simulation]

**Trigger:** Access to HPC resources (cluster computing) for lattice simulation.

**Goal:** Compute the shear viscosity-to-entropy ratio eta/s for a Walker-Wang model producing emergent SU(2) gauge theory at finite temperature. Test whether Svetitsky-Yaffe universality holds for emergent (not fundamental) gauge theories.

**The calculation:**
1. Define Walker-Wang Hamiltonian on a 3+1D lattice
2. Finite-temperature Monte Carlo simulation
3. Measure energy-momentum tensor correlators → extract eta
4. Compute entropy density s from thermodynamic relations
5. Compare eta/s to KSS bound (hbar/4pi) and to fundamental SU(2) lattice results

**Significance:** If eta/s matches fundamental SU(2), universality holds — the gauge erasure theorem applies identically to emergent gauge theories. If it differs, there is a loophole.

**Estimated LOE:** Very High (computational demands, specialized methods)
**Risk:** High — Walker-Wang at finite T is computationally demanding
**Status:** `blocked` — waiting on HPC access

---

### 5C. Wallstrom Resolution via Distributional Approach [Mathematical Analysis]

**Trigger:** Breakthrough in Reddiger-Poirier distributional framework or equivalent.

**Goal:** If the distributional approach succeeds in resolving the Wallstrom objection (single-valuedness of the wavefunction from Madelung variables), formalize the result in Lean and connect it to the fluid architecture's quantum-mechanical foundation.

**Estimated LOE:** Very High (5-10 year mathematical program)
**Risk:** Very High — may be unsolvable in current frameworks
**Status:** `blocked` — fundamental open problem

---

### 5D. Independent BEC Hawking Replication Response [Pipeline]

**Trigger:** Heidelberg, Trento, or Paris polariton group publishes independent Hawking radiation measurement.

**Goal:** Compare experimental results against our spectral predictions (Papers 1+4, prediction tables). Update predictions if needed. Publish comparison paper.

**The response (follows Wave Execution Pipeline):**
1. Extract measured spectrum from publication
2. Fit to our model: thermal + dispersive + dissipative + noise floor
3. Extract transport coefficients from the fit
4. Compare to platform-specific predictions in `src/experimental/predictions.py`
5. Update formulas.py if needed → re-verify Lean → regenerate figures → publish comparison

**Estimated LOE:** Medium (response to published data)
**Risk:** Low (straightforward comparison)
**Status:** `blocked` — waiting on experimental publication

---

### ~~5E. Non-Abelian Fracton Hydrodynamics Extension~~ [CANCELLED]

**Original trigger:** Phase 4 item 3B produces a positive result (non-Abelian fracton is Yang-Mills compatible).

**Phase 4 actual result:** **Negative.** All fracton gauge types (scalar, vector, symmetric tensor) are YM-incompatible. 4 independent obstructions: derivative order mismatch, gauge parameter dimension mismatch, Jacobi identity failure, representation constraint. Formally verified in `FractonNonAbelian.lean` (14 theorems, 2 Aristotle-proved).

**Status:** `cancelled` — trigger condition definitively not met. The non-Abelian fracton route to circumventing gauge erasure is closed. The Abelian fracton Layer 2 (5A above, via information retention) remains viable.

---

## 2. Monitoring Items (No Active Work, Track External Developments)

| Item | What to Monitor | Sources | Impact if Triggered |
|------|----------------|---------|-------------------|
| TPF remaining 2 GS conditions | Lorentz invariance + on-site symmetry proofs | arXiv hep-lat, cond-mat.str-el | Unblocks 5A (upgrades from conditional to go) |
| SMG chiral gauging | Demonstration of chiral (not vector-like) SMG | arXiv hep-lat | Strengthens chirality route |
| BEC replication | Heidelberg K-39 or Trento spin-sonic Hawking measurement | arXiv cond-mat.quant-gas | Unblocks 5D |
| Fracton experiments | Fractonic phases in cold atoms or metamaterials | Nature, Science, PRL | Validates fracton Layer 2 |
| Wallstrom progress | Distributional resolution publications | arXiv math-ph | Unblocks 5C |
| Polariton Hawking | Carusotto group polariton black hole | arXiv cond-mat | New platform for 5D |

---

## 3. Infrastructure & Process

**All work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** The pipeline defines:
- 12 stages with gates (no skipping)
- Pipeline invariants (formulas.py canonical, constants.py canonical, etc.)
- Aristotle workflow (read [reference doc](../references/Theorm_Proving_Aristotle_Lean.md) first)
- Stage 12 Inventory Maintenance Protocol

### Quick Reference Commands

```bash
cd SK_EFT_Hawking

# Validation
uv run python -m pytest tests/ -v                    # All tests
uv run python scripts/validate.py                    # 14 cross-layer checks
uv run python scripts/review_figures.py              # Generate figures + structural checks
cd lean && lake build                                 # Lean build (zero sorry)

# Aristotle (read docs/references/Theorm_Proving_Aristotle_Lean.md first!)
uv run python scripts/submit_to_aristotle.py --priority 1 --integrate
uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate

# Deep Research
# Drop prompts in Lit-Search/Tasks/. Results go to Lit-Search/Phase-5/.
```

---

*Phase 5 roadmap. All items are conditional — this phase activates when triggers are met, not on a fixed timeline. Updated 2026-03-27 with Phase 4 actual results.*
