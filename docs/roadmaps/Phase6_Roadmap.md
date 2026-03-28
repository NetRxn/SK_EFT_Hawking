# Phase 6: Collaboration + HPC (Deferred)

## Items Requiring External Resources

*Prepared 2026-03-28 | Items deferred from Phase 5 because they require HPC access, experimental collaboration, or external triggers.*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/CLAUDE.md`](../../../CLAUDE.md) — project conventions, build commands, mandatory references
> 2. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md) — 12-stage execution process, pipeline invariants, no skipping
> 3. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`](../../SK_EFT_Hawking_Inventory_Index.md) — module map, Lean map, current counts

---

## Execution Process

**All Phase 6 work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** 12 stages in strict order.

---

## 1. HPC-Dependent Items

### 6A. Vestigial MC Production (Phase 2-3 of MC Roadmap)

**Trigger:** Phase 5 Wave 2 pilot shows interesting phase structure (vestigial phase detected or rich coupling landscape).

**What:** 4D simplicial lattice production runs at 8⁴-12⁴ equivalent (~50K-250K simplices). Systematic finite-size scaling. Precision critical exponents. Continuum-limit extrapolation at 16⁴ if warranted.

**Resources:** ~100,000 core-hours modest HPC allocation. ALCC-scale.
**Scoping:** `Lit-Search/Phase-5/Monte Carlo simulation of vestigial gravity in ADW lattice models.md`

---

### 6B. Walker-Wang Z₂ Transport Program (Strategy A)

**Trigger:** HPC access.

**What:** First computation of any transport coefficient (eta/s) for any emergent gauge theory. 3D toric code (Z₂ Walker-Wang) via ParaToric QMC + T^{mu nu} correlator construction. Tests Svetitsky-Yaffe universality at transport level.

**Resources:** ~500K GPU-hours over 3 years. ALCC-scale allocation (64-128 A100/H100 for 18 months). 2-3 FTE code development.
**Scoping:** `Lit-Search/Phase-5/Walker-Wang finite-temperature eta-s simulation.md`

---

### 6C. Walker-Wang TRG for Non-Abelian (Strategy B)

**Trigger:** Strategy A successful + INCITE-scale allocation.

**What:** Tensor renormalization group for SU(2)_k Walker-Wang. Targets thermodynamic observables (critical exponents) rather than transport. Sign-problem-free but computationally demanding.

**Resources:** 2-5M GPU-hours. INCITE-scale.

---

## 2. Collaboration-Dependent Items

### 6D. BEC Experimental Engagement

**Platforms (ranked by EFT testing capability):**
1. **Trento spin-sonic** (Carusotto-Ferrari) — Best for EFT testing. Two-branch dispersion control. ERC funded (QFIELBS, 2026). Timeline: 2028-31.
2. **Paris polaritons** (Bramati-Jacquet) — Most active. Stimulated Hawking possible 2026-27. Driven-dissipative corrections complicate comparison.
3. **Heidelberg K-39** (Oberthaler) — Best apparatus for kappa-scaling test (Feshbach + DMD). Not currently pursuing Hawking. Would need redirection.

**Action:** Share prediction tables, kappa-scaling analysis, polariton Tier 1 predictions. QSimFP consortium and JILA Heising-Simons provide funding frameworks.

---

### 6E. Polariton Tier 2-3 EFT Predictions

**Trigger:** Polariton stimulated Hawking observed + Tier 1 predictions validated.

**What:** Full non-equilibrium SK-EFT with complex coupling constants (SBD framework). Independent noise vertex. Requires rewriting scattering theory, not just patching. Needed when Gamma_pol/kappa ~ O(1).

**Scoping:** `Lit-Search/Phase-5/Extending Schwinger-Keldysh EFT to driven-dissipative polariton condensates.md`

---

## 3. Trigger-Dependent Items (from Phase 5 conditional)

| Item | Trigger | Status |
|------|---------|--------|
| Emergent gravity UV completion (5A) | TPF gapped interface proven | `conditional` — chirality wall cracking |
| BEC replication response (5D) | Independent Hawking measurement | `blocked` — earliest ~2026-27 (Paris stimulated) |
| Wallstrom resolution (5C) | Distributional breakthrough | `blocked` — Reddiger pivoted |

---

*Phase 6 roadmap. All items require resources beyond the LLM + Lean + Aristotle pipeline. Prioritize based on Phase 5 results and resource availability. Prepared 2026-03-28.*
