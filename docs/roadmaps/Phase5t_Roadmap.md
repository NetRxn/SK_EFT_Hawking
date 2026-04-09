# Phase 5t: Doubloon Geometric Gate — Symmetry-Protected Two-Qubit Logic

## Technical Roadmap — April 2026

*Prepared 2026-04-09 | Follows Phase 5s: extract the finite-dimensional core first, defer heavy analysis until the exact matrix structure is closed.*

**Current state:** 131 Lean modules, 2237+ theorems, 1 axiom, 11 sorry. The repo already has strong finite-dimensional Hamiltonian infrastructure via `PauliMatrices.lean`, `BdGHamiltonian.lean`, `GTCommutation.lean`, and `FKGappedInterface.lean`, plus a complete topological-quantum-computation chain through `IsingGates.lean` and `FibonacciUniversality.lean`. What does **not** exist yet is a formalization of an experimentally current **symmetry/geometric protected gate** in a neutral-atom / Fermi-Hubbard setting.

**Entry state:** The TQC chain already gives the mathematically strongest protection story in the codebase: Ising = Clifford, Fibonacci = universal, with MTC/ribbon/modularity structure machine-checked. Phase 5t is not a replacement for that chain. It is a complementary hardware-facing case study: a finite-dimensional Fermi-Hubbard doublon gate whose protection comes from dark-state structure, fermionic exchange antisymmetry, and Hamiltonian symmetries rather than braiding/topological order.

**Motivation:** The ETH paper `arXiv:2507.22112` gives a timely experimental target: a geometric SWAP gate in a dynamical optical lattice with loss-corrected amplitude fidelity ~99.9%, built from doublon states in a Fermi-Hubbard dimer. Formalizing the idealized gate mechanism would:
- give the project a second quantum-computing entry point besides anyons
- showcase the Lean + Aristotle workflow on a near-term hardware-relevant gate
- support methodology / positioning claims about “protected logic from structure” without overstating topological overlap
- create a lower-risk, shorter-cycle formalization target than the remaining q-Serre/Hopf blocker

**Scope boundary:** Phase 5t should start with the **finite-dimensional exact model only**. Do **not** begin by trying to formalize the full adiabatic theorem, experimental fidelity extraction, or noise plateaus. The target is the algebraic core of the gate mechanism. If that closes cleanly, later waves can strengthen the phase and robustness story.

---

## Track A: Effective Fermi-Hubbard Dimer (Most Tractable)

### Wave 1 — Deep Research: Exact Dimer Model + Basis Conventions [MANUAL — John]

**Task:** `Lit-Search/Tasks/submitted/Phase-5t_effective_Hubbard_dimer_basis_and_symmetries.md`

**Goal:** Extract the exact 6-state Hamiltonian, the singlet/triplet basis change, fermionic sign conventions, and the minimal theorem set needed for a Lean formalization.

**Why first:** The main risk in this phase is not abstract mathematics. It is convention drift: basis ordering, normal ordering, doublon signs, and which symmetry statements survive at `U = 0` versus `U ≠ 0`.

**Status:** Prompt written. Ready for asynchronous deep research.

---

### Wave 2 — `FermiHubbardDimer.lean` [Pipeline: Stages 1-5]

**Goal:** Define the doublon-gate Hamiltonian in the site basis and prove the block decomposition into triplet and singlet sectors.

**Deliverables:**
- [ ] `lean/SKEFTHawking/FermiHubbardDimer.lean` — 6×6 Hamiltonian in the ordered basis
- [ ] Explicit basis change from site basis to `{t+, t0, t-, D+, D-, s}`
- [ ] Triplet/singlet block decomposition theorem
- [ ] Triplet decoupling theorem from fermionic antisymmetry
- [ ] Import added to `lean/SKEFTHawking.lean`

**Target theorem types:**
- structural matrix equalities
- basis-change conjugation identities
- exact decoupling of triplet from singlet/doublon sector

**Estimated LOE:** 2-4 days
**Risk:** Low

---

### Wave 3 — Reduced 3×3 Singlet Block [Pipeline: Stages 1-5]

**Goal:** Isolate the `S = {D+, D-, s}` sector and prove it matches the effective Hamiltonian used in the paper.

**Deliverables:**
- [ ] `singletBlock` definition for the 3×3 reduced Hamiltonian
- [ ] Exact identification of the `U`, `Δ`, `t` dependence
- [ ] Computational-space embedding theorems: how `|↑,↓⟩`, `|↓,↑⟩` map into `|t0⟩`, `|s⟩`
- [ ] Optional Python cross-check script stub for eigenvalues / basis sanity

**Estimated LOE:** 2-3 days
**Risk:** Low

---

## Track B: Dark State and Symmetry Protection

### Wave 4 — Dark State at `U = 0` [Pipeline: Stages 1-5]

**Goal:** Prove the existence of the exact dark state in the singlet sector and its zero eigenvalue.

**Prerequisites:** Wave 3 + deep research on the `θ` parametrization.

**Deliverables:**
- [ ] `DoublonDarkState.lean` or extension of `FermiHubbardDimer.lean`
- [ ] Definition of the dark state `|ψ(θ)⟩ = cos(θ/2)|s⟩ + sin(θ/2)|D-⟩`
- [ ] Theorem: `H^S(U=0) |ψ⟩ = 0` when `cot(θ/2) = -Δ/t`
- [ ] Bright-state gap theorem in the exact or minimal usable form
- [ ] Trig-identity reduction documented cleanly in docstrings

**Estimated LOE:** 3-5 days
**Risk:** Low to medium (mostly trigonometric simplification)

---

### Wave 5 — Symmetry Layer: Real Path + Chiral Constraint [Pipeline: Stages 1-5]

**Goal:** Prove the symmetry structure that makes the dark-state path geometrically constrained.

**Deep research:** `Lit-Search/Tasks/submitted/Phase-5t_geometric_phase_formalization_scope.md`

**Deliverables:**
- [ ] Definition of the chiral operator for the `U = 0` Hamiltonian
- [ ] Anticommutation theorem `Γ H Γ⁻¹ = -H` in the reduced sector
- [ ] Zero-mode pinning theorem for the odd-dimensional singlet block
- [ ] Real-Hamiltonian / conjugation-invariance statement sufficient to justify “real meridian path” language
- [ ] Decision memo in comments: what is formalized exactly versus left to later analytic work

**Important boundary:** Anti-unitary time-reversal can become an implementation tarpit. The first target is not full anti-unitary infrastructure. The first target is the exact matrix statement needed for the gate story: real symmetric path + chiral symmetry at `U = 0`.

**Estimated LOE:** 4-7 days
**Risk:** Medium

---

## Track C: Logical Gate Action

### Wave 6 — Geometric SWAP on the Computational Subspace [Pipeline: Stages 1-5]

**Goal:** Show that a relative sign flip on the singlet component induces SWAP on the computational qubit subspace.

**Why this matters:** This is the core theorem that makes the module worth doing. Without the logical action, Phase 5t is just another small Hamiltonian exercise.

**Deliverables:**
- [ ] Computational basis definitions in the two-site qubit space
- [ ] Change-of-basis theorem from computational basis to `{t0, s}` sector
- [ ] Exact theorem: singlet phase `-1` with triplet reference fixed gives SWAP
- [ ] Matrix form of the idealized swap operator in the computational space
- [ ] Optional theorem: `φ = π/2` gives entangling partial-SWAP family in the idealized reduced model

**Estimated LOE:** 4-6 days
**Risk:** Low to medium

---

### Wave 7 — Direct Exchange vs. Superexchange [Pipeline: Stages 1-5]

**Goal:** Formalize the cleanest scaling comparison between the direct-exchange and superexchange regimes.

**Deep research:** `Lit-Search/Tasks/submitted/Phase-5t_direct_exchange_superexchange_formalizable_claims.md`

**Deliverables:**
- [ ] Reduced-model derivation of the direct-exchange scaling in the weak-interaction regime
- [ ] Reduced-model derivation or carefully stated perturbative theorem for superexchange scaling
- [ ] Minimal formal theorem expressing the qualitative advantage: direct exchange depends linearly on `U` while superexchange inherits stronger `t` sensitivity
- [ ] Strongly worded comments separating exact statements from perturbative regime statements

**Estimated LOE:** 3-6 days
**Risk:** Medium

**Scope boundary:** Do **not** turn this wave into a full noise-analysis program. The formal target is the scaling distinction, not a fully rigorous fidelity plateau theorem.

---

## Track D: Phase Quantization and Robustness Boundary

### Wave 8 — Minimal Geometric Phase Theorem [Decision Gate]

**Goal:** Decide how far the project should go on geometric phase.

**Two possible targets:**

**Target A — Recommended minimal target**
- [ ] Formalize the closed-path sign / phase statement in the idealized reduced model
- [ ] Prove the logical gate is geometric in the sense that the dark state remains at zero energy for the `U = 0` cycle, so no dynamical phase accumulates in the reduced model
- [ ] State the phase result in the weakest exact form needed for Wave 6

**Target B — Strong target (defer unless deep research says cheap)**
- [ ] Aharonov-Anandan or Berry phase formalization for a parameterized finite-dimensional Hamiltonian
- [ ] Adiabatic following theorem strong enough to justify the entire cycle in Lean
- [ ] Gauge-fixed phase computation over the loop

**Decision rule:** If deep research says Target B requires substantial analysis infrastructure, stop at Target A. Phase 5t should remain a finite-matrix success, not become an analysis sink.

**Estimated LOE:**
- Target A: 2-4 days
- Target B: 2-6 weeks, high variance

---

## Track E: Pipeline Integration and Hardware-Facing Outputs

### Wave 9 — Python Cross-Validation + Visualization [Pipeline: Stages 1-12]

**Goal:** Add a lightweight Python layer for spectrum plots and reduced-model sanity checks if the Lean core lands cleanly.

**Deliverables:**
- [ ] `src/experimental/doublon_gate.py` or `src/quantum/doublon_gate.py` — exact diagonalization of the 6×6 / 3×3 model
- [ ] `tests/test_doublon_gate.py` — basis checks, dark-state eigenvalue, swap action sanity
- [ ] `fig_doublon_gate_spectrum` in `src/core/visualizations.py`
- [ ] Optional `fig_exchange_vs_superexchange_scaling`
- [ ] Documentation sync in inventory + overview if the module is actually built

**Estimated LOE:** 2-4 days after Lean core closes
**Risk:** Low

---

## Dependencies

```text
Wave 1 (dimer research) → Wave 2 (6×6 Hamiltonian) → Wave 3 (3×3 block)
Wave 3 → Wave 4 (dark state) → Wave 5 (symmetry layer)
Wave 4 + Wave 5 → Wave 6 (logical SWAP theorem)
Wave 3 → Wave 7 (exchange vs superexchange scaling)
Wave 4 + Wave 6 → Wave 8 (minimal phase theorem)
Wave 2-8 → Wave 9 (Python/tests/figures)
```

**Critical path:** Waves 2 → 3 → 4 → 6

**Non-critical but useful:** Wave 7, then Wave 9

---

## Timeline

| Wave | Scope | LOE | Dependencies | Priority |
|------|-------|-----|--------------|----------|
| 1 | Exact dimer research | 1-2 days async | None | Highest |
| 2 | 6×6 Hamiltonian + basis change | 2-4 days | Wave 1 | Highest |
| 3 | Reduced 3×3 singlet block | 2-3 days | Wave 2 | Highest |
| 4 | Dark state theorem at `U = 0` | 3-5 days | Wave 3 | Highest |
| 5 | Symmetry layer | 4-7 days | Wave 4 + research | High |
| 6 | Logical SWAP theorem | 4-6 days | Wave 4 + 5 | Highest |
| 7 | Direct vs superexchange scaling | 3-6 days | Wave 3 + research | Medium |
| 8 | Minimal geometric phase theorem | 2-4 days (Target A) | Wave 4 + 6 | Medium |
| 9 | Python/tests/figures | 2-4 days | Lean core closed | Medium |

**Total realistic LOE for the high-value core (Waves 2-6):** ~2-3 weeks

**Total realistic LOE including scaling + minimal phase + Python layer:** ~3-5 weeks

**Do not budget Target B geometric-phase formalization into the core estimate.** That is a separate escalation path.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Exact dimer Hamiltonian + basis conventions | `Lit-Search/Tasks/submitted/Phase-5t_effective_Hubbard_dimer_basis_and_symmetries.md` | **READY** |
| 2 | Geometric phase formalization scope in Lean 4 | `Lit-Search/Tasks/submitted/Phase-5t_geometric_phase_formalization_scope.md` | **READY** |
| 3 | Direct exchange vs superexchange formalizable claims | `Lit-Search/Tasks/submitted/Phase-5t_direct_exchange_superexchange_formalizable_claims.md` | **READY** |

---

## Citation Guide: `arXiv:2507.22112`

### What the citation is good for

- Use it as **hardware-motivation evidence** that symmetry- and geometry-protected two-qubit gates are experimentally live in neutral-atom / Fermi-Hubbard platforms.
- Use it to justify Phase 5t as a **complement** to Chain 3: our current TQC stack formalizes topological protection; this paper motivates a second, non-topological protected-gate case study.
- Use it in overview / methodology / discussion text to support the broader claim that the field values gate mechanisms derived from global structure rather than pulse fine-tuning.

### What the citation is **not** good for

- Do **not** cite it as evidence for quantum groups, modular tensor categories, anyon braiding, Muger triviality, or the Chain 3 formal results directly.
- Do **not** cite it in support of the chirality wall, Z₁₆ anomalies, gapped interfaces, or any Chain 4 claims.
- Do **not** present it as experimental confirmation of our formally verified TQC chain. It is adjacent in theme, not evidentiary overlap.

### Safe wording

- “Recent neutral-atom experiments demonstrate that two-qubit gates can inherit meaningful robustness from symmetry and quantum geometry in finite-dimensional Hubbard-type systems, complementing the stronger topological protection mechanisms formalized in our anyonic gate pipeline.”
- “The doublon geometric SWAP gate is not a realization of our quantum-group/MTC chain, but it provides a timely hardware-facing example of protected logic derived from exact structure rather than control fine-tuning.”
- “We cite `arXiv:2507.22112` as experimental motivation for a complementary protected-gate formalization, not as validation of our topological quantum computation results.”

### Best placement in our documents

- `docs/RESEARCH_STATUS_OVERVIEW.md` — Chain 3 implication/discussion paragraph, if we add a “complementary hardware directions” sentence
- Paper 11 discussion / outlook — to show adjacent hardware relevance for protected gates
- Paper 15 methodology / outlook — as a case for why finite-dimensional exact-gate formalization is worth doing

### Places to avoid

- Papers 7/8 chirality wall discussion
- Any section arguing for anomaly or cobordism conclusions
- Any sentence that would read as “this experiment supports our anyon/topological claims”

---

## Strategic Assessment

**What Phase 5t would strengthen most:**
- the project’s methods story
- hardware-facing quantum-computing relevance
- the claim that the repo handles more than one kind of protected-gate mechanism

**What it would strengthen least:**
- the core mathematical foundation of Chain 3
- any active blocker in the q-Serre / Hopf closure work
- any Chain 4 load-bearing claim

**Recommendation:** Pursue Waves 2-6 if and only if the phase is treated as a **bounded finite-Hamiltonian case study**. If the work starts drifting into full adiabatic-analysis machinery, stop at the exact algebraic core and publish the smaller result.

---

*Phase 5t roadmap. Created 2026-04-09. Positioned as a complementary protected-gate case study: finite-dimensional, hardware-relevant, and explicitly non-competitive with the higher-leverage q-Serre/Hopf closure work. Deep-research prompts written and placed in `Lit-Search/Tasks/submitted/`. The recommended success criterion for this phase is a closed idealized geometric SWAP theorem in Lean, not a full reproduction of the experimental control stack.*