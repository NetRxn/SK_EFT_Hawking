# Phase 5: Conditional Extensions

## Technical Roadmap — March 2026

*Prepared 2026-03-25 | Conditional on Phase 4 results and external developments*

---

## 0. Entry State (Expected at Phase 5 Start)

**What Phase 4 will have established (projected):**
- Vestigial gravity: numerical evidence for or against (2A)
- Fracton Layer 2: formalized SK-EFT chain, information retention comparison (2B)
- Fracton-gravity: Kerr-Schild linearized equivalence, bootstrap gap assessment (3A)
- Non-Abelian fracton: Yang-Mills compatibility verdict (3B)
- Backreaction: acoustic BH cooling timescales (2C)
- Chirality wall: TPF vs GS formal compatibility analysis (1B)
- Experimental predictions: platform-specific tables for engagement (1A)
- He-3 analogy: Ginzburg-Landau phase classification (1C)

**Phase 5 is conditional.** Each item has a specific trigger — an external development or Phase 4 result that must occur before the work becomes tractable or impactful. Items are listed in order of likelihood of being triggered.

---

## 1. Conditional Work Items

### 5A. Gu Topological Supergravity Completion [LLM + Lean]

**Trigger:** TPF 4+1D gapped interface conjecture is proven (chirality wall falls).

**Goal:** If chiral fermions can be produced on a lattice, formalize the full UV-complete path: string-net → chiral fermions → ADW tetrad → Einstein gravity. This would be the first complete emergent gravity program from a bosonic starting point.

**The calculation:**
1. Start from Fang-Gu (2023) topological supergravity construction
2. Replace fundamental fermions with TPF lattice chiral fermions
3. Check: does the ADW mechanism still produce tetrad condensation?
4. Check: does Vergeles's unitarity proof extend to this setting?
5. If yes to both: complete UV-to-IR chain with formal verification

**Estimated LOE:** Very High (multiple sessions)
**Risk:** Very High — depends on unproven conjecture, may hit new obstructions
**Status:** `blocked` — waiting on TPF proof

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

### 5D. Independent BEC Hawking Replication Response [LLM Pipeline]

**Trigger:** Heidelberg, Trento, or Paris polariton group publishes independent Hawking radiation measurement.

**Goal:** Compare experimental results against our spectral predictions (Paper 4, item 1A prediction package). Update predictions if needed. Publish comparison paper.

**The response:**
1. Extract measured spectrum from publication
2. Fit to our model: thermal + dispersive + dissipative + noise floor
3. Extract transport coefficients from the fit
4. Compare to our platform-specific predictions
5. Publish comparison (positive or negative)

**Estimated LOE:** Medium (response to published data)
**Risk:** Low (straightforward comparison)
**Status:** `blocked` — waiting on experimental publication

---

### 5E. Non-Abelian Fracton Hydrodynamics Extension [LLM + Lean]

**Trigger:** Phase 4 item 3B produces a positive result (non-Abelian fracton is Yang-Mills compatible).

**Goal:** If non-Abelian fracton gauge theories are compatible with Yang-Mills, develop the full Layer 2 chain: string-net → non-Abelian fracton → fracton hydro → emergent SU(N). This would circumvent the gauge erasure theorem by using fracton hydro (which preserves more information) rather than standard Navier-Stokes.

**Estimated LOE:** Very High
**Risk:** Very High — depends on 3B outcome
**Status:** `blocked` — waiting on Phase 4 Wave 3

---

## 2. Monitoring Items (No Active Work, Track External Developments)

| Item | What to Monitor | Sources | Impact if Triggered |
|------|----------------|---------|-------------------|
| TPF 4+1D proof | Publication proving the gapped interface conjecture | arXiv hep-lat, cond-mat.str-el | Unblocks 5A |
| SMG chiral gauging | Demonstration of chiral (not vector-like) SMG | arXiv hep-lat | Strengthens chirality route |
| BEC replication | Heidelberg K-39 or Trento spin-sonic Hawking measurement | arXiv cond-mat.quant-gas | Unblocks 5D |
| Fracton experiments | New fractonic phases in cold atoms or metamaterials | Nature, Science, PRL | Validates fracton Layer 2 |
| Wallstrom progress | Distributional resolution publications | arXiv math-ph | Unblocks 5C |

---

## 3. Infrastructure Notes

All infrastructure from Phase 4 carries forward unchanged:

### Build & Validation

```bash
cd SK_EFT_Hawking
uv sync
uv run python -m pytest tests/ -v
uv run python scripts/validate.py
uv run python scripts/review_figures.py
cd lean && ~/.elan/bin/lake build
```

### PR Submission Checklist (REQUIRED)

Same as Phase 4 — all items must pass before PR.

### Aristotle Workflow

```bash
export ARISTOTLE_API_KEY=$(grep ARISTOTLE_API_KEY .env | cut -d= -f2)
uv run python scripts/submit_to_aristotle.py --priority 1
uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate
```

### Deep Research

```bash
Lit-Search/Tasks/<prompt_name>.txt    # Prompts
Lit-Search/Phase-5/<result_name>.md   # Results
```

### Visualization Workflow (Figures-First)

Same 7-step workflow from Phase 3/4.

### Key Conventions

Same as Phase 4. All conventions carry forward.

### Document Sync Checklist

Same as Phase 4. All sync requirements carry forward.

---

*Phase 5 roadmap prepared 2026-03-25. All items are conditional — this phase activates when triggers are met, not on a fixed timeline.*
