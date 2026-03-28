# Phase 5: Conditional Extensions

## Technical Roadmap — Updated March 2026

*Originally prepared 2026-03-25. Updated 2026-03-28 after deep research on all trigger areas.*

---

## Execution Process

**All Phase 5 work follows the [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).** 12 stages in strict order. No skipping. Consult the [Inventory Index](../../SK_EFT_Hawking_Inventory_Index.md) before making changes.

---

## 0. Entry State (Phase 4 Actual Results)

Phase 4 is complete. These are the actual results, not projections:

| Item | Result | Implication for Phase 5 |
|------|--------|------------------------|
| **Vestigial gravity (Paper 6)** | Numerically confirmed. Three-phase structure: pre-geometric (G/G_c < 0.8), vestigial (0.8-1.0), full tetrad (>1.0). Curvature-based criterion. | Vestigial phase is real. ADW route to gravity has a concrete intermediate phase. |
| **Fracton Layer 2** | Formalized. Fracton hydro retains exponentially more UV information than standard hydro. Binomial charge counting verified. | Alternative to gauge erasure — fracton Layer 2 preserves more structure. Now partially validated by experiment (Adler et al., Nature 2024). |
| **Fracton-gravity bootstrap** | DOF gap = d-1 for all d ≥ 2. Bootstrap diverges at n ≥ 2. 4 structural obstacles identified. | Gravity connection exists but is incomplete — obstacles are real, not artifacts. |
| **Non-Abelian fracton** | **Negative result.** All fracton gauge types are YM-incompatible. 4 independent obstructions. | 5E is cancelled. Non-Abelian fracton route is closed. |
| **Backreaction** | Acoustic BHs cool toward extremality (opposite Schwarzschild). Cooling timescales computed for 3 platforms. | Extremality approach is universal. Strengthens experimental feasibility. |
| **Chirality wall** | TPF evades 2/4 GS conditions (not-on-site symmetries, ancilla fields). Wall status: **conditional** — not blocked, not open. | 5A trigger is partially met. Breach is conditional on remaining 2 conditions. |
| **Experimental predictions** | Platform-specific spectral tables for Steinhauer, Heidelberg, Trento. kappa-scaling test identified as most accessible. | Ready for comparison when data arrives. Heidelberg assessment revised (see 5D). |
| **He-3 analogy** | GL phase diagram complete. A-phase unstable, B-phase stable. 4D Lorentzian gravity analogous to B-phase. | Analogy is concrete and testable. |

**Verification state at entry:** 216 theorems + 1 axiom (zero sorry, 56 Aristotle-proved), 822 tests, 14/14 validation checks, 45 figures, 6 papers, 16 notebooks.

---

## 1. Conditional Work Items

### 5A. Emergent Gravity UV Completion [LLM + Lean]

**Trigger:** TPF 4+1D gapped interface conjecture is proven (remaining 2 GS conditions resolved).

**Phase 5 research update (2026-03-28):** Deep research revealed three critical corrections to the original 5A plan:

1. **Fang-Gu is not ADW.** The Fang-Gu topological supergravity (arXiv:2312.17196, Fang & Gu, CUHK) uses *loop condensation* from BF-type gauge theory with the vierbein itself as the condensing order parameter. This is fundamentally different from the ADW mechanism where a *fermion bilinear* condenses. They are separate programs, not links in a chain.

2. **No known mechanism generates the ADW 4-fermion coupling from topological order.** In Diakonov's formulation (arXiv:1109.0091), the 4-fermion interaction is the fundamental starting point. In Einstein-Cartan theory, it arises from integrating out torsion — which already presupposes gravity. Closing the loop to a purely bosonic starting point requires a new theoretical insight that does not yet exist.

3. **TPF → ADW is unexplored.** No published work connects TPF lattice chiral fermions to emergent gravity or tetrad condensation. The rotor degrees of freedom extend the physical Hilbert space, and effective fermion bilinears may couple nontrivially to the rotor sector at short distances.

**Chirality wall status (2026-03-28):** No movement since March 23. Gapped interface conjecture unproven. GS and TPF have not directly engaged. Chiral gauging of SMG undemonstrated. Next likely movement: June 2026 workshops (SCGP "Paths to QFT," Dresden "Emergent Gauge Theories"). Key technical tension: GS smoothness condition may be violated by TPF's discontinuous nearest-integer disentangler; GS completeness condition may not apply to TPF's fermion+rotor Hilbert space.

**Revised goal:** If chirality wall is breached, investigate whether TPF chiral fermions can be substituted into the Vladimirov-Diakonov simplicial lattice framework (arXiv:1208.1254, PRD 86, 104019), which is the closest existing lattice gravity formulation to ADW. Vergeles's unitarity proof (arXiv:2506.00036, PRD 112, 054509, 2025) covers this framework with fundamental fermions; the question is whether it extends to TPF chiral fermions.

**Revised calculation:**
1. Verify TPF boundary chiral fermions reduce to standard chiral fermions at low energy (rotor sector decoupled)
2. Embed TPF fermions in Vladimirov-Diakonov simplicial lattice (not Fang-Gu)
3. Check: does the 4-fermion interaction generate tetrad condensation with TPF fermion content?
4. Check: does Vergeles's lattice unitarity proof extend to this setting?
5. If yes: formalize the UV-to-IR chain; if no: characterize the obstruction

**Open question:** What generates the 4-fermion coupling? Volovik (arXiv:2312.09435, JETP Lett. 119, 330, 2024; arXiv:2602.21243, 2026) argues it arises from integrating out torsion in Einstein-Cartan theory — but this is top-down. A bottom-up derivation from topological order does not exist.

**Estimated LOE:** Very High (multiple sessions)
**Risk:** Very High — depends on unproven conjecture, may hit new obstructions at each step
**Status:** `conditional` — chirality wall cracking but intact; calculation chain has 3 identified gaps

**Key references (corrected):**
- Fang & Gu, arXiv:2312.17196 (topological supergravity — distinct from ADW)
- Diakonov, arXiv:1109.0091 (ADW: tetrad as fermion bilinear)
- Vladimirov & Diakonov, PRD 86, 104019 (2012) (simplicial lattice formulation)
- Vergeles, PRD 112, 054509 (2025) (lattice unitarity proof)
- Wetterich, PRD 70, 105004 (2004) (spinor gravity — NOT PRD 90, 024028)
- Volovik, JETP Lett. 119, 330 (2024) (coined "ADW gravity," vestigial phase)
- Thorngren, Preskill, Fidkowski, arXiv:2601.04304 (TPF disentangler)

---

### 5B. Transport Coefficients for Emergent Gauge Theory [Numerical Simulation]

**Trigger:** Access to HPC resources (cluster computing).

**Phase 5 research update (2026-03-28):** Deep research revealed the original plan is **not feasible** with current methods. Three compounding obstacles:

1. **Intrinsic sign problem.** Golan, Smith, and Ringel (PRR 2, 043032, 2020) proved that Walker-Wang models with modular SU(2)_k input (k > 1) have an uncurable sign problem — no local basis change renders the Hamiltonian stoquastic. The F-symbols contain irrational phases, creating a full phase problem (complex weights, not just negative).

2. **No WW construction for emergent continuous SU(2).** SU(2)_k Walker-Wang models are modular — the bulk is trivially gapped with confined excitations. Only the Z_2 (toric code) input produces deconfined bulk gauge theory. Emergent continuous SU(2) from Walker-Wang does not exist in the literature.

3. **No energy-momentum tensor T^{mu nu} defined** for Walker-Wang or any topological lattice model. Required for the Kubo formula.

**Revised plan — three strategies ordered by feasibility:**

**Strategy A (recommended, feasible):** Z_2 Walker-Wang (3D toric code) transport program.
- Sign-problem-free; existing QMC code (ParaToric, Linsel & Pollet, arXiv:2510.14781)
- Finite-T transition already known to be 3D Ising (Svetitsky-Yaffe for Z_2)
- Novel contribution: first computation of eta/s for ANY emergent gauge theory
- Tests universality at transport level, not just critical exponents
- Resources: ~500K GPU-hours over 3 years, 2-3 FTE code development
- Minimum: 64-128 A100/H100 GPUs for 18 months (ALCC-scale allocation)

**Strategy B (medium-term):** TRG for non-Abelian models.
- Tensor renormalization group is sign-problem-free
- Demonstrated for 3D Z_2 gauge theory (Kuramashi et al., JHEP 2019, N_sigma=4096)
- Extending to SU(2)_k requires complex tensors with bond dimension k+1
- Targets thermodynamic observables (critical exponents), not transport
- Resources: 2-5M GPU-hours (INCITE-scale)

**Strategy C (long-term):** Quantum simulation hardware.
- Most natural for sign-problematic Hamiltonians
- Current devices too noisy/small; viable on 5-10 year timescale

**Expected accuracy:** eta/s to 30-50% via Euclidean correlators + analytic continuation. Critical exponents to ~1% via finite-size scaling. Distinguishing emergent from fundamental requires ~25% precision (at outer edge of achievable).

**Implicit evidence for universality:** The 3D toric code — an emergent Z_2 gauge theory — already shows 3D Ising universality at its deconfinement transition, exactly as Svetitsky-Yaffe predicts for fundamental Z_2. But this has only been tested for critical exponents, not transport.

**Significance (unchanged):** If eta/s matches fundamental gauge theory, universality holds and gauge erasure applies identically to emergent theories. If it differs, there is a loophole.

**Estimated LOE:** Very High (3-year program with dedicated HPC)
**Risk:** Medium for Strategy A (technically tractable); Very High for B/C
**Status:** `blocked` — waiting on HPC access. Now with concrete resource estimate.

**Key references:**
- Golan, Smith, Ringel, PRR 2, 043032 (2020) (sign problem proof)
- Linsel & Pollet, arXiv:2510.14781 (ParaToric QMC)
- Kuramashi et al., JHEP 08, 023 (2019) (TRG for 3D Z_2)
- Braguta & Kotov, JHEP 09, 082 (2015) (fundamental SU(2) eta/s)
- Meyer, PRL 100, 162001 (2008) (fundamental SU(3) eta/s)
- Svetitsky & Yaffe, NPB 210, 423 (1982) (universality conjecture)

---

### 5B'. Vestigial Metric Correlator Simulation [Numerical, potentially workstation-tractable]

**Trigger:** None — this is actionable now, pending scoping research results.

**Motivation:** Our Paper 6 confirmed vestigial gravity at mean-field level. The Tier 2 "fermion bootstrap" research identified the vestigial metric correlator simulation as a "concrete, doable calculation" that could test Volovik's proposal beyond mean-field. This is distinct from 5B (Walker-Wang eta/s) — it targets a different question with a different model.

**Goal:** Monte Carlo simulation of g_{mu nu} = eta_{ab}<E^a_mu E^b_nu> in the disordered-tetrad phase of a lattice model with ADW-type 8-fermion interaction. Tests whether the vestigial phase survives beyond mean-field or is an artifact.

**Status:** `scoping` — deep research submitted to determine feasibility, sign problem status, and resource requirements. The Diakonov model is purely fermionic (no gauge kinetic term), which may avoid the sign problem that blocks Walker-Wang. If workstation-tractable, this could proceed without HPC allocation.

**Key question:** Does the vestigial phase (our mean-field prediction: 0.8 < G/G_c < 1.0) survive in full Monte Carlo?

---

### 5C. Wallstrom Resolution [Mathematical Analysis]

**Trigger:** Breakthrough in Reddiger-Poirier distributional framework or equivalent.

**Phase 5 research update (2026-03-28):** Reddiger has **pivoted** from proving Madelung-Schrodinger equivalence to building a provably distinct theory:
- Reddiger (Quantum Stud. 13, 2026): Kolmogorov-probability-based quantum theory, explicitly not equivalent to standard QM
- Reddiger & Poirier (Quantum Stud. 12, 2025): Born rule generalized to curved spacetime without Madelung decomposition
- The distributional framework from Reddiger-Poirier (J. Phys. A 56, 193001, 2023) has not been extended

This shifts the question from "can we derive QM from fluid mechanics?" to "can we build a physically adequate theory from fluid-mechanical principles, and where does it differ from QM?" The Wallstrom objection becomes a signpost toward genuinely new physics rather than a fatal obstacle.

No other approach has gained traction. Derakhshani's zitterbewegung proposal remains "arguable." No cohomological or topological resolution has appeared. The objection is still treated as serious by all active researchers.

**Goal:** If a distributional resolution appears, OR if Reddiger's distinct-theory program produces testable predictions that differ from QM, formalize the result in Lean and connect it to the fluid architecture's foundation.

**Estimated LOE:** Very High (5-10 year mathematical program)
**Risk:** Very High — the problem itself may be shifting from "solve" to "build around"
**Status:** `blocked` — fundamental open problem; leading researcher has pivoted strategy

---

### 5D. Independent Analog Hawking Replication Response [Pipeline]

**Trigger:** Paris polariton, Trento spin-sonic, or other group publishes independent Hawking radiation measurement.

**Phase 5 research update (2026-03-28) — critical corrections:**

1. **Heidelberg has the best apparatus but is not pursuing Hawking.** The Oberthaler group's K-39 BEC (BECK experiment) currently pursues analog cosmology (expanding spacetimes via Feshbach tuning), not Hawking radiation. However, their K-39 Feshbach tunability + DMD potential shaping is the single best apparatus for the kappa-scaling test — the most decisive experimental test available. Transitioning from temporal quenches to spatial flow profiles would be needed (significant but achievable reconfiguration). No public indication they plan to do this. Downgraded from primary trigger to potential collaboration target.

2. **Paris polaritons are the most active program.** Bramati-Jacquet group (LKB, Sorbonne) achieved tunable acoustic horizons with observable negative-energy modes (Falque et al., PRL 135, 023401, July 2025). Stimulated Hawking scattering possible 2026-27; spontaneous measurement 2027-29. EU-funded QuESHeFol project explicitly targets Hawking entanglement.

3. **Trento spin-sonic is best for EFT testing** but further out. Berti et al. (Comptes Rendus Physique 25, 2025) provides experimental blueprint. S_2 quadrature offers orders-of-magnitude stronger signal than Steinhauer's density-density correlations. Two branches (density + spin) enable independent measurement of dispersion. Ferrari's 5-year ERC grant (QFIELBS, Feb 2026) funds the platform. Timeline: stimulated 2028-29, spontaneous 2029-31.

4. **Steinhauer has plateaued.** No new experimental BEC data since PRD 2022. Theoretical pivot (ringdown, QNMs). Key collaborators dispersed. kappa-scaling test never attempted.

5. **No existing data can test ~3% EFT corrections.** The spectral dynamic range of all existing data is insufficient for percent-level deviation analysis.

**Platform assessment:**

| Platform | Status | Hawking Timeline | EFT Testing Capability |
|----------|--------|-----------------|----------------------|
| **Paris polaritons** (Bramati-Jacquet) | Most active; horizons demonstrated | Stimulated: 2026-27; Spontaneous: 2027-29 | Complicated by driven-dissipative corrections |
| **Trento spin-sonic** (Carusotto-Ferrari) | Blueprint published; ERC funded | Stimulated: 2028-29; Spontaneous: 2029-31 | Best prospect — two-branch dispersion control |
| **Steinhauer** (Technion) | Plateau; theoretical pivot | Unknown | Not with existing data |
| **Heidelberg** (Oberthaler) | Best apparatus (K-39 Feshbach + DMD); not currently pursuing Hawking | Possible if redirected | Best for kappa-scaling test |
| **Weinfurtner** (Nottingham/Manchester) | Superradiance/QNMs in superfluid He-4 | Hawking: 2029+ | Unlikely in foreseeable future |
| **Fiber-optic** (Konig, St Andrews) | QNMs only; signal 4+ orders below noise | Unclear | No |

**Action items (do not require trigger):**
- Add Paris polariton platform to prediction infrastructure (driven-dissipative EFT needed)
- Prepare kappa-scaling test predictions (most accessible near-term test; Heidelberg K-39 is best apparatus if redirected)
- Assess whether driven-dissipative corrections in polaritons can be distinguished from EFT corrections
- Maintain Heidelberg K-39 predictions — their apparatus is the best match for kappa-scaling even though they're currently doing cosmology

**The response (when triggered, follows Wave Execution Pipeline):**
1. Extract measured spectrum from publication
2. Fit to our model: thermal + dispersive + dissipative + noise floor
3. Extract transport coefficients from the fit
4. Compare to platform-specific predictions in `src/experimental/predictions.py`
5. Update formulas.py if needed -> re-verify Lean -> regenerate figures -> publish comparison

**Estimated LOE:** Medium (response to published data)
**Risk:** Low (straightforward comparison, once data exists)
**Status:** `blocked` — no independent measurement exists. Earliest plausible data: Paris stimulated Hawking ~2026-27. First data capable of EFT testing: Trento ~2030.

---

### ~~5E. Non-Abelian Fracton Hydrodynamics Extension~~ [CANCELLED]

**Original trigger:** Phase 4 item 3B produces a positive result (non-Abelian fracton is Yang-Mills compatible).

**Phase 4 actual result:** **Negative.** All fracton gauge types (scalar, vector, symmetric tensor) are YM-incompatible. 4 independent obstructions: derivative order mismatch, gauge parameter dimension mismatch, Jacobi identity failure, representation constraint. Formally verified in `FractonNonAbelian.lean` (14 theorems, 2 Aristotle-proved).

**Status:** `cancelled` — trigger condition definitively not met. The non-Abelian fracton route to circumventing gauge erasure is closed. The Abelian fracton Layer 2 (information retention) remains viable.

---

## 2. Monitoring Items (No Active Work, Track External Developments)

| Item | What to Monitor | Sources | Impact if Triggered | Current Status (2026-03-28) |
|------|----------------|---------|---------------------|---------------------------|
| TPF gapped interface | 4+1D symmetric gapped interface proof | arXiv hep-lat, cond-mat.str-el | Unblocks 5A | Unproven. Shirley et al. found 2D obstruction (H^2(G,Q+)) but it may trivialize for infinite-dim rotor spaces |
| GS-TPF compatibility | Direct engagement or third-party analysis | arXiv hep-lat, conference proceedings | Resolves 5A scope | No direct engagement. Next: June 2026 workshops |
| SMG chiral gauging | Demonstration of chiral (not vector-like) SMG | arXiv hep-lat | Strengthens chirality route | Untouched. 16-Weyl SMG confirmed but all vector-like |
| Paris polariton Hawking | Bramati-Jacquet stimulated/spontaneous measurement | arXiv cond-mat.quant-gas | Unblocks 5D | Horizons demonstrated (PRL 2025). Stimulated possible 2026-27 |
| Trento spin-sonic Hawking | Carusotto-Ferrari BEC measurement | arXiv cond-mat.quant-gas | Unblocks 5D (best for EFT) | Blueprint published. ERC funded. ~2028-31 |
| Fracton experiments | Fractonic phases in cold atoms or metamaterials | Nature, Science, PRL | Validates fracton Layer 2 | **Subdimensional dynamics observed** (Adler et al., Nature 2024). LLL fracton hydro protocol proposed (Zerba et al., 2025). UV memory retention untested |
| Wallstrom progress | Distributional resolution or distinct-theory predictions | arXiv math-ph | Unblocks 5C | Reddiger pivoted to distinct Kolmogorov-based theory. Distributional approach stalled |
| Fracton-Wallstrom connection | UV memory retention as mechanism for quantization conditions | arXiv math-ph, cond-mat | Could connect 5C to fracton program | Speculative; not explored in literature |

---

## 3. Deep Research Log

All prompts in `Lit-Search/Tasks/submitted/`. Results in `Lit-Search/Phase-5/`.

| Task | File (results) | Completed | Key Finding |
|------|---------------|-----------|-------------|
| Chirality wall update | `The chirality wall- still cracking, still not broken.md` | 2026-03-28 | No movement since March 23. GS-TPF not engaged. Chiral gauging untouched |
| Fang-Gu -> ADW chain | `Emergent gravity from topological order- a technical reference assessment.md` | 2026-03-28 | Fang-Gu != ADW. No mechanism for 4-fermion coupling from topological order. TPF->ADW unexplored |
| BEC Hawking replication | `Independent replication of analog Hawking radiation remains blocked.md` | 2026-03-28 | Heidelberg has best apparatus but not pursuing Hawking. Paris most active. Trento best for EFT. No data can test ~3% corrections |
| Walker-Wang Monte Carlo | `Walker-Wang finite-temperature eta-s simulation- technical scoping assessment.md` | 2026-03-28 | Intrinsic sign problem for SU(2)_k. Z_2 toric code is feasible alternative. ~500K GPU-hrs for Strategy A |
| Fracton & Wallstrom | `Fractons and Wallstrom- 2024-2026 monitoring scan.md` | 2026-03-28 | Fractonic excitations observed experimentally (Nature 2024). Wallstrom: Reddiger pivoted to distinct theory |
| Polariton SK-EFT | — | `submitted` | What modifications does our KMS-based framework need for driven-dissipative polariton platforms? |
| Vestigial MC scoping | — | `submitted` | Feasibility, methods, and resource estimates for vestigial metric correlator simulation |

---

## 4. Infrastructure & Process

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
# Drop prompts in Lit-Search/Tasks/submitted/. Results go to Lit-Search/Phase-5/.
```

---

*Phase 5 roadmap. All items are conditional — this phase activates when triggers are met, not on a fixed timeline. Updated 2026-03-28 with deep research results on all 5 items, cross-validated against Tier 1/2 research corpus. Heidelberg assessment nuanced (capability vs intent). Vestigial simulation added as 5B'. Two additional research tasks submitted (polariton EFT, vestigial MC scoping).*
