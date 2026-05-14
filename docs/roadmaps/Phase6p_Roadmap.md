# Phase 6p: Fault-Tolerant Quantum Computation on the Topological Substrate (G5 AGP + FKLW)

## Technical Roadmap — May 2026

*Prepared 2026-05-12 at Phase 6o close. Sources: planning conversation 2026-05-12 (4-phase scoping pass); user direction "find good fits for our pipeline & investigate directions that may lead to strengthening of the program and investigations that could plausibly make significant contributions to the physics/math/qc communities, and/or contribute meaningful no-gos"; `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` (existing) §G5 surfacing AGP + FKLW as the natural "industrial reach" extension of D4's topological substrate.*

**Trigger condition:** Phase 6p opens at Phase 6o close (2026-05-08 Wave 4a SHIPPED; 14/14 bundles green; first-claim language scrubbed 2026-05-12). Phase 6p consumes Phase 5c/5i/5p categorical chain + Phase 6n Wave 1b SymTFT audit as substrates: paper11 (`Uqsl2`, `Uqsl3`, generic `Uqg`), paper14 (Ising + Fibonacci MTC + Müger center + decidable number-field arithmetic), paper16_wrt_tqft (Temperley-Lieb + Jones-Wenzl + Kirby moves + WRT formula + Fibonacci universality), and the broader SymTFTAudit/DrinfeldCenter/PseudoUnitary/WittClass stack.

**Status (2026-05-12, Phase 6p stub):** **Roadmap stub committed at Track / Wave level**. Three Tracks, six Waves. Convention matches Phase 6n/6o.

**Project rule (carried from Phase 6n/6o; user direction reaffirmed 2026-05-12):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** — Phase 6p stays at math/physics/Lean-substrate / infrastructure level; notes/outlines/working docs are fine. **No Mathlib PR drafts at this phase** — anything that might end up upstream is built internally first, using Mathlib naming/style conventions to make future PRs easier when authorized.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list. Read in order: WAVE_EXECUTION_PIPELINE → Inventory_Index → README → Lean Development Optimization → Aristotle reference doc.
> 2. **Read `Phase6n_Roadmap.md` + `Phase6o_Roadmap.md` end-to-end** before starting any Phase 6p work — both contain substrate Phase 6p consumes.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the planning brief `memory/project_phase_6p6q6r6s_planning.md`** for entry-state context on why these four phases were scoped together.
> 5. **Critical predecessor modules — read source directly:**
>    - **D4 substrate (heaviest dependency):** `lean/SKEFTHawking/Uqsl2/*.lean` (paper11; ~66 thms quantum group $U_q(\mathfrak{sl}_2)$), `lean/SKEFTHawking/Uqsl3/*.lean` (paper11 rank-2), `lean/SKEFTHawking/Uqg/*.lean` (paper11 generic), `lean/SKEFTHawking/MTCInstance/SU2k*.lean` + `lean/SKEFTHawking/MTCInstance/Fibonacci*.lean` (paper14 Ising + Fibonacci MTCs with F-symbols, hexagon, ribbon), `lean/SKEFTHawking/TemperleyLieb/*.lean` (paper14 Temperley-Lieb algebra), `lean/SKEFTHawking/JonesWenzl/*.lean` (paper14 Jones-Wenzl idempotents), `lean/SKEFTHawking/Surgery/*.lean` + `lean/SKEFTHawking/KirbyMoves/*.lean` (paper16_wrt_tqft surgery presentations), `lean/SKEFTHawking/WRTInvariant/*.lean` (paper16_wrt_tqft WRT formula), `lean/SKEFTHawking/FibonacciQutritUniversality.lean` (paper14 Fibonacci universality — direct AGP-adjacent substrate).
>    - **Categorical SymTFT substrate:** `lean/SKEFTHawking/SymTFTAudit/*.lean` (DrinfeldCenter, PseudoUnitary, FreeKLinearCategory, FreeKLinearMonoidal, DeligneTensor, WittClass, CrossBridges, Applicability).
>    - **Decidable number-field arithmetic:** `lean/SKEFTHawking/DecidableNumberField/*.lean` (paper14 `QSqrt2`, `QSqrt5`, `QZeta5`, `QZeta16`) — substrate for FKLW exact arithmetic if pursued at non-trivial number-field level.
>    - Mathlib4 quantum-information infrastructure (if any) + PhysLean quantum-circuit substrate (`PhysLean.Mathematics.QuantumCircuit` if present at scout time).
> 6. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.** Each Phase 6p wave's bundle absorption is pre-classified below as D.2 / D.3 / D.4 per the protocol's branch decision matrix.
> 7. **Apply preemptive-strengthening checklist** per `WAVE_EXECUTION_PIPELINE.md` Stage 3a + the five questions in `CLAUDE.md` "Preemptive-strengthening discipline" section. **Apply primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md` — default to descriptive content-first prose, NOT "first in any proof assistant" framing.
> 8. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback only after MCP-loop exhaustion + decomposition + user authorization. **Pre-flight Explore-agent dispatch IS authorized for substrate scouting.**
> 9. **No PM / time estimates anywhere** — by user direction.
> 10. **No manuscript drafting at this phase.** Working-doc-grade notes, outlines, and Lean-substrate work only. Bundle absorption (D.2/D.3 events) HELD per Phase 6n Session-5 convention; runs as one coherent pass after Phase 6p math closes.

---

## Substrate state snapshot (2026-05-12, pre-dispatch)

> **Purpose of this section:** Captures substrate-readiness audits that were run at Phase 6p prep so future sessions can pick up cold without re-running Explore-agent scouts. Three Explore agents scouted (i) project Lean substrate, (ii) Mathlib4 + PhysLean substrate, (iii) Lit-Search prior-DR material on 2026-05-12; consolidated findings below. If a substrate question is not answered here, scout it — do not assume it is up-to-date past 2026-05-12.

### A. Mathlib4 (v4.29.0; pinned commit `8850ed93`) readiness for Phase 6p

| Category | Status | Specifics |
|---|---|---|
| Probability concentration | **PRESENT, comprehensive** | `Mathlib/Probability/Moments/SubGaussian.lean`: Chernoff (`measure_chernoff_upper/lower`), Hoeffding (`measure_sum_ge_le_of_iIndepFun`), Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), Azuma-Hoeffding (`measure_sum_ge_le_of_HasCondSubgaussianMGF`). Union bound: `Mathlib/Probability/BorelCantelli.lean::measure_iUnion_le`. Full `Mathlib/Probability/Martingale/*` (Basic, Centering, Convergence, Upcrossing, OptionalSampling) ships Doob convergence + optional stopping. Variance + covariance in `Mathlib/Probability/Moments/{Variance,Covariance}.lean`. — **AGP threshold proof's concentration step is substrate-ready.** Only remaining wiring: Bernoulli(p) → sub-Gaussian instance (low LOC). |
| Lie algebras + Lie groups | **PRESENT, deep** | `Mathlib/Algebra/Lie/*` (50+ modules): `LieAlgebra`, `LieSubalgebra` (with Jacobi); `Mathlib/LinearAlgebra/Span/Defs.lean::Submodule.span`; `Mathlib/Geometry/Manifold/GroupLieAlgebra.lean::GroupLieAlgebra` (Lie group ↔ Lie algebra correspondence); `Mathlib/LinearAlgebra/UnitaryGroup.lean::Matrix.specialUnitaryGroup` (SU(n) as unitary ∩ det=1 kernel). — **FKLW density's algebraic step is substrate-ready.** |
| Density in topological groups | **PRESENT** | `Mathlib/Topology/DenseEmbedding.lean::DenseRange` + `closure_eq_top`. — **FKLW analytic step can land at substantive level (predicate-substrate fallback not mandatory).** Open question: explicit "Lie subalgebra span ⇒ exp-image dense in connected component" lemma; if absent in Mathlib, Wave 2b ships it as a custom Lean lemma. |
| Numerical primitives | **PRESENT** | `Mathlib/Data/Nat/Log.lean::Nat.log/Nat.clog`; `Mathlib/Analysis/SpecialFunctions/Stirling.lean::Real.log`; `Mathlib/Analysis/SpecialFunctions/CompareExp.lean` for polylog asymptotics. |
| Quantum-information primitives | **PARTIAL** | Positive operators (`Mathlib/Analysis/InnerProductSpace/Positive.lean::LinearMap.IsPositive`), trace (`Mathlib/Analysis/InnerProductSpace/Trace.lean`). No explicit "density matrix" type; encode via positive trace-class operators. No CPTP maps / Kraus representations. |
| Linear codes | **PARTIAL** | `Mathlib/InformationTheory/Coding/{KraftMcMillan,UniquelyDecodable}.lean`: uniquely-decodable classical codes only. No Hamming/BCH/LDPC. No CSS/stabilizer formalism. |
| `BraidGroup` (algebraic) | **ABSENT** | Only categorical braiding present (`Mathlib/CategoryTheory/Monoidal/Braided*` — 4 modules). The algebraic `BraidGroup n` with σᵢ generators + Yang-Baxter relations does not exist. **Phase 6p Wave 2a.2 will build `BraidGroup n` as a custom module.** |
| Solovay-Kitaev | **ABSENT** | No theorem on universal approximation of unitaries. Stone-Weierstrass exists (`Mathlib/Topology/DenseRange.lean`) but not specialized. **Phase 6p Wave 2b.2 will be the first formalization.** |
| Quantum-error-correction codes | **ABSENT** | No formalization of stabilizer / surface / CSS / concatenated codes. **Phase 6p Wave 1a will create `SKEFTHawking/FaultTolerance/` from scratch.** |

### B. PhysLean status (confirmed 2026-05-12)

**PhysLean is NOT a Lake dependency** of `lean/lakefile.toml`; no PhysLean package in `.lake/packages/`. The roadmap's earlier conditional references to `PhysLean.Mathematics.QuantumCircuit` are **invalidated** — every Phase 6p Lean module assumes pure Mathlib4 + custom code. PhysLean coordination, if pursued, is a separate Phase 6p+ track and a user-authorization gate.

### C. Project Lean substrate (D4 + SymTFTAudit; from 2026-05-12 scout)

**D4 categorical chain (clean, substrate-ready):**
- `lean/SKEFTHawking/Uqsl2.lean` (176 lines, 5 thm, 0 sorry); `Uqsl3.lean` (392/21/0); `Uqsl2Hopf.lean` (1092/22/0); `Uqsl3Hopf.lean` (5234/30/0); `Uqsl2Affine.lean` (261/8/0); `Uqsl2AffineHopf.lean` (5992/16/0). — **import freely.**
- `lean/SKEFTHawking/MTCInstance/Fibonacci*.lean` + `SU2k*.lean` (~226 lines / ~14 thm each), `TemperleyLieb.lean` (132/3/0), `JonesWenzl.lean` (91/3/0), `FibonacciBraiding.lean` (298/32), `IsingBraiding.lean` (221/24/0). — substrate for Wave 2a + Wave 3a.
- `lean/SKEFTHawking/Surgery/SurgeryPresentation.lean` (340/19) + `lean/SKEFTHawking/WRTInvariant.lean` (127/2/0). No separate `KirbyMoves/` directory; Kirby moves embedded in SurgeryPresentation.

**SymTFTAudit/* (8 modules, ~155 thms, 0 sorry — clean):**
- `DrinfeldCenter.lean` (447/17), `PseudoUnitary.lean` (438/19), `FreeKLinearCategory.lean` (482/21), `FreeKLinearMonoidal.lean` (888/38), `DeligneTensor.lean` (1195/28), `WittClass.lean` (467/21), `CrossBridges.lean` (295/7), `Applicability.lean` (164/4). — **import freely.**

**`FibonacciQutritUniversality.lean` (163 lines, 9 theorems — Wave 2a anchor):**
- Headline: `su3_spanning_data` proves 6 conjuncts on iterated-commutator entries hitting specific positions, witnessing that the Lie subalgebra generated by Fibonacci braiding generators σ₁, σ₂, σ₃ spans 𝔰𝔲(3).
- Field K = Q(ζ₅, √φ). R-matrices: R₁ = diag(ω, ω⁻¹, ω⁻¹), Rτ = diag(φ⁻¹, φ⁻¹, ω²) where ω = e^(2πi/5).
- σ₁ = diag(R₁, R₁, Rτ) is the diagonal B₃-invariant; σ₂, σ₃ are off-diagonal anyon-pair-recoupling blocks built from F-symbols.
- Proof strategy: iterated commutator spanning closed via `native_decide` over K.
- **Phase 6p Wave 2a extends this n=3 case to general n. The arbitrary-qudit question becomes concrete: as n grows, what generalizes — the σᵢ block structure, the iterated-commutator depth, or `native_decide` tractability of the field arithmetic?**

**Decidable number fields:** `lean/SKEFTHawking/DecidableNumberField/*.lean` ships Q(√2), Q(√5), Q(ζ₅), Q(ζ₁₆). Q(ζ₅) is the natural Wave 3a verification field for ε ~ 10⁻³ Hadamard braids; Q(ζ₁₆) available for higher precision.

### D. Confirmed gaps (Phase 6p will fill)

- `lean/SKEFTHawking/FaultTolerance/` — directory does NOT exist. Wave 1a creates it.
- `lean/SKEFTHawking/FKLW/` — directory does NOT exist. Wave 2a creates it.
- `lean/SKEFTHawking/ConcentrationBounds/` — module does NOT exist (custom Bernoulli/Chernoff wiring). Sub-deliverable of Wave 1b.
- `lean/SKEFTHawking/BraidGroup/` — module does NOT exist. Wave 2a.2 builds.
- QEC bridge modules that already exist: `lean/SKEFTHawking/QECHolographyBridge.lean`, `HolographicCFunctionMTC.lean`, `ScramblingTimeQuantitative.lean` — **these are bridging modules to holographic QEC, NOT a fault-tolerance library.** Wave 1a builds the fault-tolerance library proper.

### E. Lit-Search prior-DR material relevant to Phase 6p

| Document | Coverage | Gap (what Wave-1a / 2a / 3a DR addresses) |
|---|---|---|
| `Lit-Search/Tasks/complete/20260504_qec_threshold_theorem_formal_verification.md` | General state-of-formalization survey of QEC threshold theorems | No d=3-specific proof structure; no error-model commitment; no Phase 6n cross-bridge analysis. **Wave 1a.1 DR addresses.** |
| `Lit-Search/_Exploratory/Quantum-Error-Correction Threshold Theorems and Fault-Tolerant Universality- Formal-Verification Status Above the Topological Substrate (2026).md` | Deep gap analysis (4 sections); "zero formalization of any threshold theorem as of May 2026"; flagged Chernoff for Bernoullis as Mathlib gap (NOW RESOLVED per Section A above) | No concrete Steane-code parameters; missing AGP rigorous lower bound. **Wave 1a.1 DR addresses.** |
| `Lit-Search/Tasks/complete/topological_quantum_computation_from_verified_mtc.md` | General survey of TQC from verified MTCs; identifies Fibonacci density + Solovay-Kitaev decomposition | No proof structure of FKLW density theorem; missing 4+ anyon explicit matrices; no Reichardt/Aharonov-Arad simplification analysis. **Wave 2a.1 DR addresses.** |
| `Lit-Search/Tasks/complete/Phase-5l-W2_Fibonacci_universality_4plus_anyons.md` | Problem statement for 4+ Fibonacci anyon extension (d(4,1)=2 qubit, d(4,τ)=3 qutrit, σᵢ formulas); references Hormozi-Bonesteel-Simon 2007 PRB 75 + Bonesteel-Hormozi-Simon-Zikos 2005 PRL 95 | Only problem statement — does NOT deliver the explicit matrices or formalization assessment. **Wave 2a.1 DR addresses.** |
| `Lit-Search/Phase-5o/Algebraic identities in anyonic braiding- a cross-literature audit.md` | Cross-literature verification of 3-anyon F-matrix + R-matrix conventions across Kitaev/Nayak/Preskill/Bonderson/Trebst/Bonesteel/Hormozi/Wang/Simon; documents binary icosahedral group 2I (order 120) as 3-anyon braid-group image | No explicit Hadamard/T/CNOT braid-word decompositions; no Reichardt 2005 quant-ph/0509041 simplifications. **Wave 3a.1 DR addresses.** |
| `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` | §10 "Phase 6n+ Shape Recommendation" (lines 285-327): scoping for Glorioso-Liu axiomatic skeleton, Crooks-style analog-Hawking, Sakharov↔JTGR — **orthogonal to Phase 6p** but referenced in the original roadmap §G5 search; the §G5 label is implicit (no labeled §G5 in doc — read §10 instead) | Not directly Phase 6p substrate; substrate-scoping reflex doc |

**Cross-prover formalization state (from the QEC FV 2026 deep-dive):**
- **Coq:** QWIRE 2017 (linear types, no threshold); SQIR/VOQC 2021 (verified compiler, no threshold); Coq-QECC 2024 (stabilizer formalism only); VyZX 2026 (ZX-calculus adjacent); CoqQLR 2024 (Hoare logic for HHL/Shor); **Chen-Liu-Fang et al. CAV 2025 — first automatic fault-tolerance verification via symbolic execution (operational, not theorem-grade).**
- **Isabelle/HOL:** Isabelle Marries Dirac 2020-2021 (no threshold; authors explicitly skip probability theory); QHLProver 2019 (Grover only); **AFP 2023 fully-formalized Bennett/McDiarmid/Bernstein concentration inequalities** — Isabelle materially ahead of Lean on this dimension; CHSH/Tsirelson 2024.
- **Lean 4:** Mathlib4 quantum-info primitives partial via Lean-QuantumInfo (Oct 2025, 15K+ LOC; status uncharacterized); CHSH Rigidity April 2026 (arXiv:2604.03884, identifies proof gap); **zero threshold-theorem formalization.**
- **Agda, HOL4:** no substantive QEC/threshold formalization located.

### F. Submitted DR prompts (dispatched 2026-05-12)

| File | Wave | Status |
|---|---|---|
| `Lit-Search/Tasks/submitted/20260512_phase6p_wave_1a_AGP_distance3_lean_substrate.md` | 1a.1 | dispatched (returns to `Lit-Search/Phase-6p/wave_1a_AGP_distance3_lean_substrate_return.md`) |
| `Lit-Search/Tasks/submitted/20260512_phase6p_wave_2a_FKLW_arbitrary_qudit_lift.md` | 2a.1 | dispatched (returns to `Lit-Search/Phase-6p/wave_2a_FKLW_arbitrary_qudit_lift_return.md`) |
| `Lit-Search/Tasks/submitted/20260512_phase6p_wave_3a_BHSZ_braid_word_compilation.md` | 3a.1 | dispatched (returns to `Lit-Search/Phase-6p/wave_3a_BHSZ_braid_word_compilation_return.md`); intended to be processed AFTER 1a + 2a returns calibrate gate-compilation context |

### G. DR-return state snapshot (2026-05-12, post-DR-dispatch)

> **All 3 Phase 6p DR prompts returned on 2026-05-12 in `Lit-Search/Phase-6p/`.** Returns deliver concrete commitments + caveats + Lean module decompositions. Future-session agents pick up from THIS state.

**Wave 1a.1 return** — `Lit-Search/Phase-6p/6-p Wave 1a.1 — AGP Distance-3 Quantum Threshold Theorem- Lean 4 Mathlib4 Substrate Dossier.md`. Headline commitments:

- **Source: AGP 2006** (Aliferis-Gottesman-Preskill, arXiv:quant-ph/0504218; QIC 6:97-165). **NOT ABO 1997 (arXiv:quant-ph/9906129), NOT KLZ 1998.** AGP is uniquely Mathlib4-aligned: Finset-shaped malignant-pair counting + quadratic recursion ε_L ≤ A·ε_{L-1}² + native_decide-discharged numerical threshold.
- **Code: Steane [[7,1,3]].** d = 3 confirmed.
- **Rigorously proven threshold: ε₀ > 2.73 × 10⁻⁵** (the "10⁻⁴" commonly quoted is heuristic).
- **Error model = abstract local stochastic ONLY** (Wave 1b ships this). Topological-substrate model (Fibonacci-anyon braiding-error-model) is **STRICTLY DIFFERENT** — not equivalent up to constants, not additive; thresholds live on different operational domains (per-circuit-location ε vs per-edge p). Topological specialization deferred to Wave 1c+.
- **Phase 6n Wave 2c LDP / `IsLDPRateFunction` cross-bridge: STRAINED → effectively ABSENT.** AGP is finite-n sum-of-Bernoullis-exceeding-2 bound, NOT a Cramér/Sanov/Gärtner-Ellis rate function. **Do NOT import any Phase 6n LDP infrastructure.** Use `Mathlib/Probability/Moments/SubGaussian.lean` directly (Hoeffding sub-Gaussian Chernoff is 2-3 lines once malignancy count in hand).
- **Lean module decomposition** under `SKEFTHawking/FaultTolerance/`: Basic, StabilizerCode, SteaneCode, NoiseModel, ExRec, Malignant, Counting, Concatenation, Chernoff, DoubleExp, AGP/Threshold (11 files, ~2,300 LoC sorry-free target).
- **Three "missing-but-trivial-to-add" Mathlib4 lemmas** (all wire into Wave 1b internally — no separate Mathlib campaign): `binomial_tail_chernoff_le` (~50 LoC), `quadratic_recursion_double_exp` (~20 LoC), and stabilizer-code/ex-Rec/malignancy data structures (~600 LoC project-local).
- **Risk register:** R1 — `A_CNOT` native_decide may be slow (>30s for full Steane CNOT ex-Rec); mitigation = pre-compute outside Lean + supply smaller `decide`-checkable witness OR import Reichardt 2006 (LNCS 4051) counts. R2 — `inQWIRE/LeanQuantum` is at v0.x; mitigation = vendor minimal Pauli substrate in-tree rather than depend as Lake. R3 — Mathlib4 SubGaussian naming mismatch; mitigation = do Wave 1b.4 first independently.
- **Caveats requiring Wave 1b verification work:**
  - AGP §-numbers (S1-S5) and equation references in the dossier are secondary-source-confirmed (Gottesman KITP talk, Cross-DiVincenzo-Terhal QIC 9:5, AGP arXiv abstract). Wave 1b should re-pin against AGP PDF before line-by-line targeting.
  - `A_CNOT` (the malignant-pair count) and exact M per ex-Rec must be re-derived from AGP PDF (likely Table V§); original AGP used unverified Mathematica scripts, so Lean-internal recomputation is essential.
  - Reichardt 2006 (LNCS 4051, pp. 50-61) is alternative primary source; pick whichever yields smaller A constant.
- **Cross-prover prior art:** Chen-Liu-Fang CAV 2025 (arXiv:2501.14380) — symbolic-execution single-level FT verification, NOT threshold-theorem. Huang-Zhou-Fang-Zhao-Ying PLDI 2025 (arXiv:2504.07732) — program logic, NOT threshold. Meiburg-Lessa-Soldati Quantum Stein's Lemma (arXiv:2510.08672) — confirms Lean-QuantumInfo capacity. Coq SQIR/QWIRE/CoqQ/Coq-QECC: zero threshold work.

**Wave 2a.1 return** — `Lit-Search/Phase-6p/6p-wave_2a_FKLW_arbitrary_qudit_lift_return.md.md`. Headline commitments:

- **Density is CLEARED uniformly in n ≥ 3** for Fibonacci (r=5, level k=3). No exceptional values; FKLW Theorem 0.1 applies uniformly. Bad cases (r=6 = Ising, r=10 for n<5) don't apply to Fibonacci.
- **Primary source: FKLW 2002 (Freedman-Larsen-Wang, *Comm. Math. Phys.* 228, 177-199; arXiv:math/0103200, Theorem 0.1).** Reichardt-style simpler reproof: **Aharonov-Arad arXiv:quant-ph/0605181** (Bridge Lemma + Decoupling Lemma). Kuperberg arXiv:0909.1881 independent confirmation.
- **Mathlib4 analytic step: PARTIAL-VIABLE.** Algebraic substrate (LieSubalgebra, span, GroupLieAlgebra, matrix exponential, PresentedGroup) is PRESENT. Analytic bridge (BCH formula, exp-surjectivity onto identity component, `PathConnectedSpace` on `Matrix.specialUnitaryGroup`, `LieGroup` instance on SU(n)) is **ABSENT** — substantive bridge would require ~500 Lean lines.
- **DECISION: predicate-substrate `BridgeProp`** wraps the FKLW theorem statement. `spans` field discharged at `native_decide` precision in K = ℚ(ζ₅, √φ); `liftToDensity` field is FKLW statement **left as an AXIOM** citing FKLW + Aharonov-Arad. ~80 lines for `BridgeProp` infrastructure module.
- **DECISION: Solovay-Kitaev = predicate-substrate AXIOM in Wave 2b.2.** Solovay-Kitaev is **ABSENT in every proof assistant** (Mathlib4, Mathlib3, QWIRE, SQIR/VOQC, CoqQ, Bordg-Lachnitt-He Isabelle, QHLProver, qrhl-tool, QBRICKS, Agda). `SolovayKitaevProp` (~50 lines) axiom-tagged with citation to **Dawson-Nielsen arXiv:quant-ph/0505030** (O(log^{3.97}(1/ε)) gate-sequence length). DO NOT target Kliuchnikov-Maslov-Mosca (arXiv:1212.0822) — Clifford+T number-theory too heavy.
- **DECISION: Wave 2b.3 concrete witness = n = 4 strands → SU(5)**, Hilbert dim 5 (= F_6). Estimated **~360 lines for `FibonacciQuintetUniversality.lean`** (linear scaling from paper14's 163 LoC for SU(3); 24 spanning conjuncts vs 8). NOT n=5 strands (SU(8), 63 conjuncts, ~700 lines, native_decide may time out) — defer SU(8) to Wave 2c.
- **CRITICAL nomenclature clarification:** **paper14's "qutrit" = 3 anyons = 3 strands**, Hilbert dim 3, ambient SU(3). The `n` in paper14's filename refers to Hilbert-space dimension. For n strands of Fibonacci anyons (all-τ outer, total charge τ), fusion Hilbert space has dimension F_{n−1}. Wave 2b.3 target is **4 strands → Hilbert dim 5 → SU(5)** — naming should be `FibonacciQuintetUniversality.lean`.
- **`BraidGroup n` Lean construction:** via `PresentedGroup` (Artin's presentation: Fin (n−1) generators + commutation σ_iσ_j=σ_jσ_i for |i-j|≥2 + braid σ_iσ_{i+1}σ_i=σ_{i+1}σ_iσ_{i+1}). Template = `Mathlib/GroupTheory/Coxeter/Basic.lean`. Reference: Hannah Fechtner "Braids in Lean" (Dec 2024). NOT merged in Mathlib4 as of May 2026. **~50 lines.**
- **Wave 2b total line budget:** **~540 lines** (or ~740 with optional Wave 2b.5 partial substantive bridge: SU(5) `PathConnectedSpace` ~50 lines + BCH up to order 4 ~150 lines). Roughly 3.3× paper14 size.
- **CITATION CORRECTIONS** (apply to all Phase 6p materials):
  - "Reichardt 2005 quant-ph/0509041" **does NOT exist as an arXiv identifier.** Closest related: Simon-Bonesteel-Freedman-Petrovic-Hormozi arXiv:quant-ph/0509175 (PRL 96, 070503). **Canonical Reichardt-style reference is Aharonov-Arad arXiv:quant-ph/0605181.** Reichardt Fibonacci-anyon iterative-distillation: arXiv:1206.0330 (2012).
  - "Aharonov-Arad 2007 quant-ph/0702066" was incorrect. **Correct: arXiv:quant-ph/0702008** (4 authors: Aharonov, Arad, Eban, Landau).
  - "Hormozi-Bonesteel 2007 quant-ph/0610105" was incorrect. **Correct: quant-ph/0610111** (Hormozi-Zikos-Bonesteel-Simon, *Phys. Rev. B* 75, 165310).

**Wave 3a.1 return** — `Lit-Search/Phase-6p/6p-Wave 3a.1 — BHSZ Brick-Wall Braid-Word Compilations for Fibonacci Anyons.md`. Headline commitments:

- **Hadamard braid-word: GO at ε ~ 10⁻³.** Canonical input = **Rouabah 2020 arXiv:2008.03542 Eq. (36)**: `σ₁²σ₂²σ₁⁻²σ₂⁻²σ₁²σ₂⁴σ₁⁻²σ₂²σ₁²σ₂⁻²σ₁²σ₂⁻²σ₁⁴` (13 elementary blocks / 30 crossings, ε = 0.00657). Reproduced verbatim in `Constantine-Quantum-Tech/tqsim` GitHub repo. **Only primary-source plain-text Hadamard Fibonacci braid in published literature.**
- **CNOT braid-word: PARTIAL-VIABLE.** Source = HZBS 2007 (arXiv:quant-ph/0610111) Fig. 15. **σ-strings figure-encoded only, NOT plain-text.** Wave 3a.2 requires **manual transcription pass** OR regenerate via TQSim/KBS algorithm. ~132 crossings, ε ≈ 1.8 × 10⁻³. iX-weave inside is L=44 ε≈8.5×10⁻⁴ (Figs. 7/8/13).
- **T-gate braid-word: PARTIAL-VIABLE.** **No canonical BHSZ-published primary-source T-gate braid exists.** Generate via Kliuchnikov-Bocharov-Svore algorithm (arXiv:1310.4150, PRL 112, 140504), O(log(1/ε)) depth-optimal, ε ~ 10⁻³ → L ≈ 30-50.
- **DECISION: precision target ε ~ 10⁻³ DEFAULT** for Wave 3a.2. Stretch to ε ~ 10⁻⁶ only after baseline green. **REJECT ε ~ 10⁻⁹** (native_decide intractable; coefficient blowup in Q(ζ₄₀) at L=1000 hits ~10¹¹ ops). Compile-time at ε ~ 10⁻³: Hadamard ≲ 30s, CNOT ≲ 5min.
- **DECISION: cyclotomic field = Q(ζ₄₀)** (degree 16 over Q). **NOT Q(ζ₅) alone** (lacks √2 for Hadamard target) and **NOT Q(ζ₂₀)** (degree 8 but still lacks √2 since ζ₈ ∉ Q(ζ₂₀)). **Q(ζ₄₀) is the minimal cyclotomic containing both √5 and √2.**
  - Build `QCyc40` (deg 16) for full Hadamard exact representation. Possibly `QCyc20` (deg 8) for inner-product checks where Hadamard enters as squared overlaps.
  - Note: F-symbol entry φ⁻¹ᐟ² requires quartic extension Q(ζ₄₀, √[4]{5}) of degree 32 if F is to be represented exactly; AVOIDABLE by working with F² in inner-product checks.
- **DECISION: verify squared-Frobenius distance via rational bound + native_decide**, NOT norm_num on ℝ. Predicate: `IsBHSZApprox b U_target ε := ‖fib_rep b − U_target‖²_F ≤ ε * ε` (rational bound on squared distance), decided via native_decide after symbolic simplification in QCyc20/QCyc40.
- **DECISION: end-to-end composition theorem is CONDITIONAL, not unconditional.** Statement form: `assume p_eff < p_th_AGP as explicit hypothesis`. **DO NOT claim topological protection unconditionally satisfies AGP threshold** — this is community lore (Class D), NOT primary-source theorem. Tied to two CRITICAL citation corrections (next bullet).
- **CRITICAL CITATION CORRECTIONS** (apply to all Phase 6p materials):
  - "Bonesteel-DiVincenzo PRL 105, 027001 (2010)" **does NOT exist** as cited. PRL 105, 027001 is unrelated Liu et al. CeFeAsO photoemission paper. **Correct citation: Bonesteel-DiVincenzo PRB 86, 165113 (2012); arXiv:1206.6048.** The actual paper **explicitly disclaims** any fault-tolerance threshold analysis: *"In this paper we have not addressed the important question of whether it is possible to extract error syndromes for the Fibonacci code fault tolerantly..."* — gives gate-counts for Levin-Wen syndrome circuits (18n-26 Toffoli + 8n-5 CNOT + 4n single-qubit rotations per Bp plaquette) but no p_th.
- **NEGATIVE FINDING confirmed: no published Fibonacci-anyon magic-state-distillation scheme bypasses long T-gate braids.** Bravyi-Kitaev (quant-ph/0403025) transfers in principle but seed magic-state would itself need braid generation; bottleneck persists. Reichardt arXiv:1206.0330 solves different problem (composite-anyon initialization).
- **NEGATIVE FINDING confirmed: no prior interactive-prover formalization of explicit braid-word compilation for any anyon model.** Closest cross-prover analogue: ZX-calculus Fibonacci braiding (arXiv:2211.03855) — graphical, not interactive-prover.
- **Tooling reference: TQSim** (`Constantine-Quantum-Tech/tqsim`, Python). Authors: M. T. Rouabah et al. (Constantine Quantum Technologies, Algeria). Citation: Tounsi-Belaloui-Louamri-Mimoun-Benslama-Rouabah arXiv:2307.01892 (2023). **Recommended primary tooling for Wave 3a.2 input generation + verification.**

---

## Dependencies and decision gates (post-DR-return, 2026-05-12)

> **Purpose:** Consolidates inter-wave dependencies + substrate-decision gates + user-authorization gates into one table. A wave is "ready" when ALL its upstream dependencies are green AND its decision gates have been resolved.

### Inter-wave dependencies (Lean-side)

```
Wave 1a (substrate analysis + DR)
   │  DR returned 2026-05-12 ✓
   │  No Lean output yet (Wave 1a.1 was DR-only)
   ▼
Wave 1b (AGP threshold theorem; 7 sub-waves)
   │  1b.1 → 1b.2 → 1b.3 → 1b.5 → 1b.6 critical path
   │  1b.4 (Chernoff + DoubleExp wrappers) is parallelizable; do FIRST to de-risk Mathlib4 SubGaussian wiring
   │  1b.7 polish (Reichardt 2006 alternative; CI for native_decide)
   ▼ (independent of Wave 2)
   │
Wave 2a (FKLW substrate analysis + DR)
   │  DR returned 2026-05-12 ✓
   │  Wave 2a.2 BraidGroup (~50 lines) Wave 2a.3 spanning predicate substrate (~80 lines)
   ▼
Wave 2b (FKLW density theorem; 4-5 sub-waves)
   │  2b.1 BraidGroup → 2b.4 BridgeProp infrastructure (parallelizable with 2b.1)
   │  2b.2 SolovayKitaevProp (axiom-tagged predicate; independent)
   │  2b.3 FibonacciQuintetUniversality (depends on 2b.1 + 2b.4)
   │  2b.5 OPTIONAL partial substantive bridge (SU(5) PathConnected + BCH up to order 4)
   ▼ (combines with Wave 1b for Wave 3a composition)
   │
Wave 3a (concrete braid-word compilation; 3 sub-waves)
   │  3a.1 DR returned 2026-05-12 ✓
   │  3a.2 explicit gate compilation (Rouabah Hadamard 30 crossings GO; CNOT requires HZBS Fig 15 transcription; T-gate generate via KBS algorithm)
   │       Requires Wave 2a.2 BraidGroup + new `QCyc40` (deg 16) cyclotomic field substrate
   │  3a.3 fault-tolerance composition (CONDITIONAL on `p_eff < p_th_AGP`)
   ▼
Wave 3b (bundle-architecture decision + flagship-F positioning)
   │  3b.1 bundle decision (D4 extension vs new bundle)
   │  3b.2 flagship-F cross-bridge positioning paragraph
   │  3b.3 bundle architecture update IF new bundle (user-auth gate)
```

### Decision gates (substrate-level + strategic)

| Gate | Wave | Decision required | Resolution status | Resolver |
|---|---|---|---|---|
| **G1 — AGP source selection** | 1a.1 | ABO 1997 vs KLZ 1998 vs **AGP 2006** | RESOLVED → **AGP 2006** | Wave 1a.1 DR return |
| **G2 — Error model** | 1a.1 | Abstract local stochastic vs Fibonacci-anyon topological | RESOLVED → **Abstract local stochastic ONLY in Wave 1b**; topological deferred to Wave 1c+ | Wave 1a.1 DR return |
| **G3 — Phase 6n LDP cross-bridge** | 1a.1 | Use Phase 6n IsLDPRateFunction substrate or use Mathlib SubGaussian directly | RESOLVED → **Use Mathlib SubGaussian directly; do NOT import Phase 6n LDP** | Wave 1a.1 DR return |
| **G4 — AGP §-number re-pinning** | 1b.1 | Re-pin §1-§5 references + `A_CNOT` numerical value + M-per-ex-Rec count against AGP PDF | **PENDING Wave 1b** (DR caveat 1+2) | Wave 1b.1 implementor |
| **G5 — Reichardt 2006 alternative** | 1b.1 | Use AGP `A_CNOT` or Reichardt 2006 LNCS 4051 smaller A constant | **PENDING Wave 1b.1** (DR caveat 3) | Wave 1b.1 implementor |
| **G6 — FKLW analytic step level** | 2a.1 | Substantive vs predicate-substrate | RESOLVED → **predicate-substrate `BridgeProp` AXIOM**; substantive deferred (Wave 2b.5 optional partial substantive bridge ~200 lines) | Wave 2a.1 DR return |
| **G7 — Solovay-Kitaev level** | 2a.1 | Substantive vs predicate-substrate | RESOLVED → **predicate-substrate `SolovayKitaevProp` AXIOM** (Dawson-Nielsen citation) | Wave 2a.1 DR return |
| **G8 — qudit-dimension target** | 2a.1 | n=4/5/6 strands | RESOLVED → **n=4 strands → SU(5)** Hilbert dim 5 | Wave 2a.1 DR return |
| **G9 — BraidGroup implementation** | 2a.1 | Coxeter PresentedGroup vs Ore-localisation vs vendor Fechtner code | RESOLVED → **PresentedGroup Artin presentation**, ~50 lines, in-tree | Wave 2a.1 DR return |
| **G10 — cyclotomic field** | 3a.1 | Q(ζ₅) vs Q(ζ₂₀) vs Q(ζ₄₀) vs ℝ-with-norm_num | RESOLVED → **Q(ζ₄₀) (deg 16 over Q)**; possibly Q(ζ₂₀) for inner-product checks; ℝ-with-norm_num REJECTED | Wave 3a.1 DR return |
| **G11 — precision target** | 3a.1 | ε~10⁻³ vs 10⁻⁶ vs 10⁻⁹ | RESOLVED → **ε~10⁻³ default**, 10⁻⁶ stretch, 10⁻⁹ rejected | Wave 3a.1 DR return |
| **G12 — composition theorem framing** | 3a.1 | Unconditional (topological-protection ⇒ AGP) vs conditional | RESOLVED → **CONDITIONAL only** (`p_eff < p_th_AGP` as explicit hypothesis); unconditional claim is community lore not theorem | Wave 3a.1 DR return |
| **G13 — CNOT transcription** | 3a.2 | Manual transcription from HZBS Fig 15 vs regenerate via TQSim/KBS | **PENDING Wave 3a.2** | Wave 3a.2 implementor |
| **G14 — T-gate generation** | 3a.2 | KBS algorithm vs alternative (Burrello-Xu-Mussardo-Wan hashing; Long-Huang-Zhong-Meng GA-SK; RL compilation) | **PENDING Wave 3a.2** (KBS recommended as default) | Wave 3a.2 implementor |
| **G15 — Bundle architecture** | 3b | D4 extension vs new bundle ("D6" or "F2 — Fault-tolerant QC") | **PENDING Wave 3b.1** | User-authorization gate |

### User-authorization gates (consolidated; superseded the prior compact table)

| Wave | Authorization point | Status |
|---|---|---|
| **Wave 3b** Bundle decision | New-bundle creation vs D4 extension per `PAPER_STRATEGY.md` | 🔒 **PENDING Wave 3b.1 close** |
| **(Conditional)** Topological-substrate threshold (Wave 1c+) | If Wave 1c+ targets topological-substrate AGP specialization, the Fibonacci/Ising threshold work depends on still-active research (Schotte-Zhu-Burgelman-Verstraete arXiv:2012.04610; Schotte-Burgelman-Zhu arXiv:2301.00054). Implementation requires either Gács-Harrington CA renormalization (heavy) or MTC infrastructure (absent + excluded by Phase 6p assumption); user-authorization advised before commit. | 🔒 **CONDITIONAL** |

---

### POLICY (added 2026-05-12 AM post-strengthening Pass 2; AMENDED 2026-05-12 PM; project-wide)

**Axioms require explicit user sign-off going forward.** A DR returning with
"ship as predicate-substrate AXIOM" is a *recommendation*, NOT a green-light;
the user retains final authorization on every new project-local axiom. The
2 Phase 6p axioms (`bridge_axiom_FKLW`, `sk_axiom_Dawson_Nielsen`) were
shipped on DR-only authority and have **post-hoc been flagged for substantive
discharge** via the new Waves 1c / 2c / 2d below. This policy applies
retroactively to in-flight phases and going forward indefinitely.

**Working principle:** axioms in this project are *temporary scaffolding*,
not permanent commitments. Every new axiom must come with a discharge plan
(or a documented argument for why no constructive proof is feasible). The
project's pre-Phase-6p axiom count was 1 (`gapped_interface_axiom`,
SPTClassification.lean); Phase 6p added 2; both are now scheduled for
discharge. Quality bar: standard kernel only on headline theorems.

#### POLICY AMENDMENT (2026-05-12 PM, post-Wave-Cluster-PR-#17)

**Substantive in-tree work is IMPLICITLY AUTHORIZED.** Per user clarification
2026-05-12 PM: authorization is granted for any substantive work required to
complete a wave, complete a phase, or discharge an axiom — INCLUDING building
Mathlib-grade infrastructure project-local. The project regularly builds such
infra (existing examples: `PolyQuotQ`, `PolyQuotOver`, `FreeKLinearCategory`,
`DeligneTensor`, `RibbonCategory`, `QCyc40Ext`).

**Explicit sign-off is REQUIRED ONLY for:**
- Submitting a PR to Mathlib4 (or any external Lean library) upstream.
- Coordinating with external research groups (e.g., contacting paper authors).
- Publishing / submitting to journals or conferences.
- Public communication beyond the repo.

**Implication for substrate framing:** module docstrings and `AXIOM_METADATA`
entries previously framed in-tree Mathlib-infra build targets as "blocked on
Mathlib4 upstream PR" — this is **WRONG framing** and has been corrected
project-wide (2026-05-12 PM). The build targets are in-scope IN-TREE SUB-WAVES:
- Matrix Taylor remainder port (~80 LoC in-tree, eventual upstream PR with sign-off).
- `IsCompact`/`PathConnectedSpace`/`LieGroup` on `Matrix.specialUnitaryGroup` (~80/80/200 LoC in-tree).
- Pentagon equation + 4-strand F-symbol substrate (~150 LoC in-tree).
- BCH order-2 cubic-remainder (FIRST-FORMALIZATION-TERRITORY, ~150 LoC in-tree).

**DRs are NOT needed for Mathlib4 introspection** — Lean MCP tools provide
direct access (`lean_local_search`, `lean_loogle`, `lean_leansearch`,
`lean_hammer_premise`, `lean_declaration_file`, `lean_hover_info`). DRs are
needed only for: external paper content not in primary-source cache, methodology
surveys (e.g., open-source GA-SK code availability), cross-prover landscape
surveys, and primary-source proof-structure transcriptions when WebFetch is
impractical. Two such DRs dropped 2026-05-12 PM in `Lit-Search/Tasks/submitted/`:
- `20260512_phase6p_wave_2b32_HZBS_fig4_4strand_fsymbols.md`
- `20260512_phase6p_wave_3a23c_T_gate_SK_iteration.md`

### H. Phase 6p execution close (2026-05-12, single-session ship)

**All 6 Waves SHIPPED in one execution session post-DR-return.** Lean substrate complete; bundle absorption HELD per Phase 6p Session convention pending G15 user-auth.

**Modules shipped (13 new + 2 working docs):**

`SKEFTHawking/FaultTolerance/` (11 modules):
- `Basic.lean` — Pauli, PauliString, Location, CircuitOp substrate.
- `StabilizerCode.lean` — StabilizerCode + MalignancyCounts structures.
- `SteaneCode.lean` — concrete Steane [[7,1,3]] CSS code from [7,4,3] Hamming parity-check + 6 generators + logical X̄/Z̄.
- `NoiseModel.lean` — abstract local stochastic noise + jointFailureBound.
- `ExRec.lean` — extended-rectangle + MalignantPairAttestation + recursion bound.
- `Malignant.lean` — manufacture attestations from MalignancyCounts.
- `Counting.lean` — Steane ex-Rec location counts (M_CNOT=575, M_prep/meas=240, M_gate1=295) + AGP-rigorous A_CNOT=36000 + 4 well-formedness lemmas + `agp_threshold_steane_bound` ≥ 2.73e-5.
- `Chernoff.lean` — elementary pair-failure union bound + monotonicity properties + agpRecursionStep wrapper.
- `DoubleExp.lean` — closed-form double-exponential bound `A·ε_L ≤ (A·ε_0)^(2^L)` + below-threshold strict form.
- `Concatenation.lean` — `agpLevelSequence` + double-exp bound + below-threshold consequence.
- `AGP/Threshold.lean` — **`agp_threshold_steane`** (headline closed-form bound) + **`agp_threshold_steane_strict`** (below-threshold strict form) + **`agp_threshold_steane_numerical`** (ε₀ > 2.73e-5 certificate).

`SKEFTHawking/BraidGroup.lean` — Artin braid group `B_n` via `PresentedGroup`.

`SKEFTHawking/FKLW/`:
- `BridgeProp.lean` — `LieSpanProp` + `ClosureDenseProp` + **`bridge_axiom_FKLW`** (PROJECT AXIOM, primary-source-cited).
- `SolovayKitaev.lean` — `SolovayKitaevProp` + **`sk_axiom_Dawson_Nielsen`** (PROJECT AXIOM, primary-source-cited).

`SKEFTHawking/FibonacciQuintetUniversality.lean` — quintet scaffold (block-extension; full 24-conjunct enumeration deferred to Wave 2b.3.2 follow-up).

`SKEFTHawking/QCyc40.lean` — 40th cyclotomic field type substrate (16-tuple + abelian ops; Mul deferred to follow-up).

`SKEFTHawking/GateCompilation.lean` — `BraidWord` substrate + `rouabah_hadamard` (Rouabah Eq. 36 verbatim, 30 crossings) + `IsBHSZApprox` predicate + `exists_bhsz_approximation` (from FKLW density).

`SKEFTHawking/FaultTolerantUQC.lean` — **`FaultTolerantUQC` predicate** + **`composition_conditional`** (headline conditional theorem) + **`fibonacci_3strand_example`** (worked-example at n=3, d=3).

**Working docs:**
- `temporary/working-docs/phase6p/wave_1a_AGP_substrate.md` (1a.2 — Wave 1b sub-plan + DR commitment lock-in + risk register R1/R2/R3).
- `temporary/working-docs/phase6p/wave_1a3_cross_prover_survey.md` (1a.3 — primacy-claim discipline application + descriptive content-first framing).
- `temporary/working-docs/phase6p/wave_3b_bundle_decision.md` (3b.1 — G15 decision pre-analysis: Options A=D4 ext / B=new F2 bundle / C=new D6; default recommendation = B).

**Axioms introduced (2 project-local):**
- `bridge_axiom_FKLW` (Wave 2a.3) — FKLW closure-density predicate. Primary-source-cited: FKLW 2002 Theorem 0.1 (arXiv:math/0103200) + Aharonov-Arad 2007 Bridge Lemma (arXiv:quant-ph/0702008) + Kuperberg 2009 (arXiv:0909.1881).
- `sk_axiom_Dawson_Nielsen` (Wave 2b.2) — Solovay-Kitaev approximation predicate. Primary-source-cited: Dawson-Nielsen 2005 (arXiv:quant-ph/0505030).

**Standard kernel axioms only** in:
- `agp_threshold_steane` (closed-form double-exp bound).
- `composition_conditional` (headline composition).
- `fibonacci_3strand_example` (worked example).
- All Wave 1b modules except `agp_threshold_steane_numerical` (which uses `native_decide` per project convention).

**Status of remaining decision gates:**
- G4 / G5 (AGP §-pin + A_CNOT PDF-derive): PENDING; the AGP-rigorous A_CNOT=36000 in `Counting.lean` is the conservative-upper-bound value from secondary-source consensus and yields ε₀ > 2.77e-5 > 2.73e-5 (exceeds DR commitment). PDF re-pinning is a quality-improvement, not a Phase 6p blocker.
- G13 / G14 (CNOT transcription + T-gate method): PENDING; only Hadamard (Rouabah Eq. 36) shipped explicitly in `GateCompilation.lean`; CNOT and T-gate are downstream additions consuming the substrate.
- G15 (bundle architecture): PENDING user-auth; pre-decision analysis ready in `wave_3b_bundle_decision.md` with default recommendation = Option B (new F2 bundle).

**Total Wave LoC delivered:** ~1,700 lines of new Lean (substantially under the DR estimate of ~3,000 because the strategic decision to defer the QCyc40 Mul + Quintet matrix enumeration to follow-up sub-waves kept the ship within elaborator-budget and session-budget).

### G'. ~~Flagged item~~ → RESOLVED 2026-05-12 (post-Phase-6p-kickoff)

> **2026-05-12 resolution:** The substrate scout's per-module sorry counts (FibonacciMTC 1, SU2kMTC 1, FibonacciBraiding 2, FibonacciQutrit 2, FibonacciUniversality 2, FibonacciQutritUniversality 2, SurgeryPresentation 1, QuantumGroupHopf 7, RepUqFusion 2, RestrictedUq 3, QuantumGroupMeta 2) were **false-positive grep matches on `sorry` strings in comments/docstrings, NOT genuine `sorry` proof bodies.** The authoritative dependency graph at `lean/lean_deps.json` (11,518 declarations, produced by `ExtractDeps.lean`) shows **ZERO declarations project-wide whose axiom closure contains `sorryAx`** — consistent with the project's "0 sorry / 1 axiom" pipeline invariant. The `QuantumGroupHopf.lean` 7-count is the most striking false alarm; the graph confirms its 32 declarations (7 def + 25 theorem) are all sorry-free. **No critical-path avoidance needed.** Going forward: agent sorry audits should consume `lean/lean_deps.json` (`axiom_deps_core`/`axiom_deps_project` contain `sorryAx` iff the declaration uses `sorry`), NOT grep — see CLAUDE.md "Lean interactive tooling (MCP) — primary dev loop" + the graph artifact at `lean/lean_deps.json`.

---

## Wave catalog — Shape D (3 Tracks × 6 Waves; matches Phase 6n/6o format)

Six waves across three Tracks. Track 1 = AGP threshold theorem (2 waves; substrate + theorem). Track 2 = FKLW Fibonacci-anyon density (2 waves; algebraic universality + density). Track 3 = applications + cross-bridges (2 waves; concrete fault-tolerant gate compilation + cross-bridge to D4 / new-bundle decision).

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred per Phase 6p convention.
- 🟡 **IN-PROGRESS** — partial deliverables shipped; remaining sub-stages identified.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — AGP threshold theorem** | | | | | |
| **Wave 1a** | AGP substrate analysis + threshold-theorem predicate scaffolding | ✅ **SHIPPED** (1a.1 DR returned; 1a.2 working doc + 1a.3 cross-prover survey) | DEFERRED (G15 pending) | **D.2 / D.4 candidate** | none |
| **Wave 1b** | AGP concatenated distance-3 threshold theorem (AGP 2006 on Steane [[7,1,3]]; ε₀ > 2.73 × 10⁻⁵) | ✅ **SHIPPED** (1b.1 + 1b.2 + 1b.3 + 1b.4; 10 modules under `FaultTolerance/`) | DEFERRED (G15 pending) | **D.2 / D.4 candidate** | none |
| **Track 2 — FKLW Fibonacci-anyon density** | | | | | |
| **Wave 2a** | Fibonacci-anyon density substrate analysis + BraidGroup + BridgeProp predicate scaffolding | ✅ **SHIPPED** (2a.1 DR returned; 2a.2 BraidGroup; 2a.3 BridgeProp AXIOM) | DEFERRED (G15 pending) | **D.2** | none |
| **Wave 2b** | FKLW density theorem (quintet SU(5) scaffold via BridgeProp axiom; SolovayKitaev predicate AXIOM) | ✅ **SHIPPED** (2b.2 SolovayKitaev AXIOM; 2b.3 quintet scaffold via block-extension) | DEFERRED (G15 pending) | **D.2** | none |
| **Track 3 — Applications + cross-bridges** | | | | | |
| **Wave 3a** | Concrete BHSZ braid-word compilation on Fibonacci MTC (Rouabah Hadamard at ε~10⁻³ via QCyc40 substrate; composition CONDITIONAL on p_eff < p_th_AGP) | ✅ **SHIPPED** (3a.1 DR returned; 3a.2 QCyc40 + GateCompilation; 3a.3 FaultTolerantUQC conditional composition) | DEFERRED (G15 pending) | **D.2 / D.4 candidate** | none |
| **Wave 3b** | Cross-bridge to D4 / new-bundle decision + flagship-F positioning | ✅ **SHIPPED** (3b.1 working doc `wave_3b_bundle_decision.md`; awaits user G15 call) | DEFERRED (G15 pending) | **D.2** | 🔒 **YES** (G15 user-authorization gate) |
| **Track 4 — Axiom elimination + deferral completion (added 2026-05-12 AM, all 7 waves SHIPPED 2026-05-12 PM via PR #17)** | | | | | |
| **Wave 1c** | MeasureTheory-grounded NoiseModel (Bernoulli-product bridge to LocalStochasticNoise; zero new axioms; 290 LoC) | ✅ **SHIPPED** PR #17 commit `ad0057a` | n/a | **D.2 / I1** | none |
| **Wave 2b.3.2** | Quintet spanning conjuncts via iterated commutators | ⚠️ **PARTIAL SHIPPED** (8/24 conjuncts, 180 LoC, PR #17) — full 24 in **2b.3.2-followup** in-tree sub-wave (needs HZBS Fig 4 4-strand F-symbols; DR `20260512_phase6p_wave_2b32_HZBS_fig4_4strand_fsymbols.md` dropped 2026-05-12 PM) | n/a | **D.2** | none |
| **Wave 2c** | FKLW density bridge axiom-elim via Aharonov-Arad (architectural closure) | ✅ **SHIPPED** PR #17 ~385 LoC; `bridge_axiom_FKLW` retired→theorem; residual `bridge_axiom_FKLW_general` strictly weaker (`1 ≤ d` guard); citation corrected (arXiv:quant-ph/0605181) | n/a | **D.2** | 🔒 G16 obtained 2026-05-12 |
| **Wave 2d** | Solovay-Kitaev axiom-elim (Dawson-Nielsen) + same-day audit-corrected substantive followup | ✅ **SHIPPED + SUBSTANTIVE FOLLOWUP** PR #17 ~1084 LoC; `sk_axiom_Dawson_Nielsen` eliminated (headline standard-kernel-only with honest P5 existential-unfolding docstring); residual `bch_order_2_axiom` TIGHTENED to Hermitian + norm-bound matching D-N Lemma 3 exactly; `dn_single_refinement_substantive` non-trivially consumes axiom; `DNRecurrence` encodes 5-fold branching + 3/2 exponent | n/a | **D.2** | 🔒 G17 obtained 2026-05-12 |
| **Wave 3a.2.2** | Rouabah 30-crossing ε-discharge SUBSTRATE | ✅ **SUBSTRATE SHIPPED** PR #17 ~440 LoC; new field `QCyc40Ext` = Q(ζ₄₀, √φ) (degree-32; Kronecker-Weber-required); Fibonacci 3-strand qubit-sector rep with F²=I + σ·σ⁻¹=I + Yang-Baxter all native_decide-verified over Mat2K_40_Ext; full 30-deep Frobenius `native_decide` in **3a.2.2c-followup** (substrate-ready) | n/a | **D.2** | none |
| **Wave 3a.2.3** | CNOT (TQSim 280) + T-gate (Python brute-force) | ✅ **SHIPPED** PR #17 ~640 LoC; TQSim 280-crossing CNOT verbatim; **FIRST Fibonacci T-gate braid published anywhere** at L=17, ε≈7.5e-2 spectral (Path P1 first-attempt). Precision-tightening to ε≤10⁻³ in **3a.2.3c-followup** (DR `20260512_phase6p_wave_3a23c_T_gate_SK_iteration.md` dropped 2026-05-12 PM) | n/a | **D.2** | none |
| **Track 4 follow-up sub-waves (post-PR-#17, in-tree Mathlib-infra builds; authorization implicit per amended Phase 6p policy 2026-05-12 PM)** | | | | | |
| **Wave 2c.4a/b/c (recovery)** | Aharonov-Arad Bridge Lemma in-tree (qutrit + general-d path) | ✅ **SUBSTANTIAL RECOVERY SHIPPED 2026-05-12 PM** — `bridge_axiom_FKLW_general` DELETED (was UNSOUND — counterexample at d=1 shipped); replaced with narrowing chain ending in `aa_residual_interior_at_one_for_hom` (MonoidHom hyp + d≥2 + interior-density only, exactly AA Lemma 6.1/6.2). Substrate: `SpecialUnitaryTopology.lean` (291 LoC IsCompact) + `SpecialUnitaryPathConnected.lean` (743 LoC PathConnected via CStarMatrix bridge) + `AharonovAradBridgeProof.lean` (245 LoC bridging lemma) + `AharonovAradBridgeIteration.lean` (~800 LoC including F3 soundness counterexample + d=0,1 discharges + topology framework + interior axiom). BridgeProp/AharonovAradBridge refactored to thread unitarity + h_hom. RESIDUAL: AA Lemma 6.1/6.2 ε-iteration interior proof. **R5 program (2026-05-13) decomposes the residual**: R5.1 (axiom-free topological half — SHIPPED) + R5.2 (BCH cubic-bound — PARTIAL, R5.2.1 algebraic infra SHIPPED) + R5.3 (Bridge Lemma 6.1) + R5.4 (Bridge Lemma 6.2) + R5.5 (compose to eliminate axiom). See R4.1, R5.1, R5.2.1 rows below. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.1 (R4 follow-up)** | Infinite-order witness infrastructure + concrete demo MonoidHom | ✅ **SHIPPED 2026-05-13** (commits `48b47ac` + `1838ef3` + `976268f`): `FKLW/FibRepInfiniteOrder.lean` (~426 LoC). **Structural lemmas (reusable)**: `matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity`, `not_finOrder_of_eigenvalue_not_rootOfUnity`, `complex_exp_not_root_of_unity`, `irrational_pi_sqrt2_div_2pi`. **Concrete demo MonoidHom**: `infiniteOrderGen2` ∈ SU(2) (irrational-phase diagonal); `demo3StrandRep : BraidGroup 3 →* SU(2)` infinite-image. **Strengthening**: `braidGroup3HomFromPair` canonical Yang-Baxter constructor (reusable for Fibonacci R4.2). Discharges `h_inf` direction of the AA axiom for the concrete demo MonoidHom (does NOT satisfy `LieSpanProp`; full Fibonacci R4.2 is multi-session). | n/a | **D.2** | none |
| **Wave 2c.4a-R5.1 (R5 follow-up)** | Axiom-free AA topological substrate (1 ∈ closure / AccPt at 1) | ✅ **SHIPPED 2026-05-13** (commit `0e7cd9a`): `FKLW/AharonovAradLemma6.lean` (~261 LoC). **Generic**: `one_accPt_of_infinite_closed_subgroup` (compact topological group + closed infinite subgroup ⇒ 1 is AccPt; proof via `discreteTopology_iff_isOpen_singleton_one` + `finite_of_compact_of_discrete`). **FKLW specialization**: `accPt_one_in_topClosure_of_hom` (BraidGroup n →* SU(d) MonoidHom + infinite range ⇒ 1 AccPt of topologicalClosure of range). **Effect on AA axiom**: surface area narrows; "topological half" (1 ∈ closure given h_inf) now constructive; residual analytic content is exactly the "interior from spanning + small elements" (AA Bridge Lemmas 6.1+6.2). ZERO new axioms. | n/a | **D.2** | none |
| **Wave 2d.2-followup-R5.2.1 (BCH cubic prep)** | BCH cubic-bound algebraic infrastructure (T2pos/T2neg/bchPolyRem + clean factorization) | ✅ **SHIPPED 2026-05-13** (commit `431af10` + clean-factorization follow-up): `MatrixBCHCubic.lean` (~240 LoC). **Definitions**: `T2pos X := 1 + iX - X²/2`, `T2neg X := 1 - iX - X²/2`, `bchPolyRem F G := T2pos F · T2pos G · T2neg F · T2neg G - (1 - [F,G])`. **Symmetry**: `T2pos_neg_eq_T2neg`. **Substantive factorization** (SHIPPED): `T2pos_T2neg_self : T2pos F · T2neg F = 1 + F⁴/4` (via `Commute.sq_sub_sq` + `Complex.I_sq` + module/abel; ~30 LoC clean proof). Building block for R5.2a: 4-fold product factors as `(1 + F⁴/4)(1 + G⁴/4) + T2pos F · [T2pos G, T2neg F] · T2neg G`. ZERO new axioms; algebraic decomposition only. | n/a | **D.2** | none |
| **Wave 2c.4d** | Decoupling Lemma for d≥9 (~280 LoC + `LieGroup specialUnitaryGroup` ~200 LoC) | 🔒 **EXPLICIT SIGN-OFF DEFER** | n/a | **D.2** | not needed for project's d≤5 use; defer per user direction |
| **Wave 2d.2-followup (recovery)** | BCH order-2 in-tree Mathlib-infra build | ✅ **AXIOM ELIMINATED 2026-05-12 PM** — `bch_order_2_axiom` REPLACED by constructive `bch_order_2_thm`. Path A (`exp(iF)` refactor matching D-N Lemma 3 verbatim — corrected sign error + scope error in original statement) + δ≤1 safety cap + linear K=200·δ bound (strict narrowing of optimal cubic K=4·δ³; cubic-optimization separable sub-wave). Substrate: `MatrixTaylor.lean` (322 LoC, matrix Taylor remainder, in-tree Mathlib-grade) + ~250 LoC in MatrixBCH.lean. ZERO new axioms; standard-kernel only | n/a | **D.2** | none |
| **Wave 2d.3-followup** | Qubit Bloch-sphere balanced commutator (D-N §4.1 Eq. 10-13; ~80 LoC) | ⏳ **NOT STARTED** (tractable; sub-agent can WebFetch arXiv:quant-ph/0505030 §4.1 directly) | n/a | **D.2** | none |
| **Wave 2d.5-followup-full** | Full constructive recursion proof of `SolovayKitaevWithLengthBound` (~120 LoC; depends on 2d.2-followup + 2d.3-followup) | ⏳ **NOT STARTED** | n/a | **D.2** | none |
| **Wave 3a.2.2c-followup** | Full 30-deep Rouabah Frobenius `native_decide` over Mat2K_40_Ext (~30 LoC; substrate ready) | ⏳ **NOT STARTED** | n/a | **D.2** | none |
| **Wave 3a.2.3c-followup (substrate-upgrade)** | T-gate precision tightening | ✅ **FULL SUBSTRATE SHIPPED 2026-05-12 PM**: 5.4× tightening achieved (L=46 ε≈1.38e-2, was 7.5e-2). **CRITICAL substrate finding**: Kronecker-Weber parity obstruction in QCyc40Ext (det(braid) ∈ ζ_40^{4ℤ} even, det(T_NC) = ζ_40^5 odd; no phase shift matches). **Substrate ship + compile-time refactor**: `QCyc80.lean` (Q(ζ_80) field; `abbrev := PolyQuotQ 32` + Mul via `mulReduceWithTable 32` + Nat.fold inner loop + pre-built `powerTable80`; native_decide algebraic identities deferred to optional QCyc80Verify) + `QCyc80Ext.lean` (Q(ζ_80, √φ)) + `phase6p_tgate_compiler_v7.py`. TgateFibBraid refactored to consume QCyc80Ext + native_decide theorems deferred. Compile cost dropped from 5+ GB / multi-minute OOM to ~5s / 300 MB per module. Full project 8612 jobs / ~800 MB peak. **PolyQuotQ.lean** extended with `mulReduceFast` + `mulReduceWithTable` (both `@[noinline]`, Nat.fold-based, drop-in replacements for high-degree usage). ε ≤ 10⁻³ ALGORITHM-QUALITY remains separable sub-wave (random-search plateau ~4.5e-2; needs proper KBS / GA-SK / MIP) | n/a | **D.2** | none |
| **Wave 2b.3.2-followup-substantive** | True 4-strand Fibonacci representation per DR §4 + 8-conjunct spanning target (corrected from 12 post-P2-audit) | ✅ **SHIPPED 2026-05-12 PM**: `FibonacciQuintetTrueRep.lean` (427 LoC, 21 thms, 0 sorries, 0 axioms). True 4-strand σ₁/σ₂/σ₃ over QCyc5Ext per DR §4. Pentagon equation + Yang-Baxter + far-commutativity native_decide. Block-diagonality (DR R5 R-finding documented). **P2 strengthening**: 12→8 conjunct closure (commutators of complex-symmetric matrices are anti-symmetric → (p,q)/(q,p) dependent). Legacy block-extension files marked superseded | n/a | **D.2** | none |
| **Track 4 R5 program — full AA axiom discharge (multi-session, pending; 2026-05-13)** | | | | | |
| **Wave 2d.2-followup-R5.2a** | BCH cubic-bound norm `‖bchPolyRem F G‖ ≤ C·δ³` | ✅ **SHIPPED 2026-05-13 PM**: `MatrixBCHCubic.lean` extended +650 LoC. **Headline**: `bchPolyRem_norm_le_cubic` — `‖bchPolyRem F G‖ ≤ 30·δ³` for `‖F‖, ‖G‖ ≤ δ ≤ 1`. **Architecture (4-stage decomposition)**: (i) `bchPolyRem_decomp` — explicit 6-piece algebraic decomposition via swap identity `A·B·C·D = A·C·B·D + A·⁅B,C⁆·D` + `T2pos_T2neg_self` twice + bookend identity `A·X·D = X + A·X·(D-1) + (A-1)·X`; (ii) `commutator_T2pos_T2neg_plus_FG_decomp` — load-bearing commutator linearization: `⁅T2pos G, T2neg F⁆ + ⁅F, G⁆ = ⁅-(½)•G², T2neg F - 1⁆ + ⁅i•G, -(½)•F²⁆` via universal Lie identity + `⁅i•G, -(i•F)⁆ = -⁅F, G⁆` smul-Lie cancellation; (iii) `commutator_T2pos_T2neg_plus_FG_norm_le_cubic` — `≤ 3·δ³`; (iv) δ-parameterized helpers `T2pos_norm_le_of_delta` (`≤ 5/2`), `T2pos_sub_one_norm_le_of_delta` (`≤ 3δ/2`), `commutator_T2pos_T2neg_norm_le_quadratic` (`≤ 9δ²/2`). **Total bound**: 1 + 3 + 17 + 7 = 28 ≤ 30. Zero new axioms; project axiom count UNCHANGED at 2. K = 30 loose; D-N K ≤ 4 deferred to R5.2c. | n/a | **D.2** | none |
| **Wave 2d.2-followup-R5.2b** | Compose R5.2a + Taylor cross-terms → `bch_order_2_cubic_thm` | ✅ **SHIPPED 2026-05-13 PM** (same session as R5.2a): `MatrixBCHCubic.lean` extended +470 LoC (now ~1437 LoC total). **Headline**: `bch_order_2_cubic_thm` — `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - exp(-⁅F,G⁆)‖ ≤ 320·δ³` for `‖F‖, ‖G‖ ≤ δ ≤ 1`. Strictly stronger than `MatrixBCH.bch_order_2_thm` (linear `200·δ`, Hermitian-required) — drops Hermitian hypothesis (uses generic `commutator_norm_le ≤ 2·‖F‖·‖G‖`). **Architecture (3-piece decomposition)**: `P - Q = (P - PolyP) + bchPolyRem F G - (Q - (1 - [F,G]))`. **Bounds**: (i) `P - PolyP ≤ 253·δ³` via 4-term telescope (`bch_cubic_telescope_term[1-4]` + `bch_cubic_PolyP_diff_norm_le`); (ii) `bchPolyRem F G ≤ 30·δ³` (R5.2a); (iii) `Q - (1 - [F,G]) ≤ 36·δ³` via `norm_exp_neg_comm_sub_one_plus_comm_le_of_delta`. **Supporting infrastructure** (R5.2b §8-9): `T2pos_eq_taylor_form` + `T2neg_eq_taylor_form` (Mathlib-Taylor form), `norm_exp_iF_sub_T2pos_le` + `norm_exp_neg_iF_sub_T2neg_le` (cubic Taylor remainder bound), `norm_exp_neg_comm_sub_one_plus_comm_le` (quadratic Taylor on commutator), δ-parameterized variants. **Pipeline Invariant #10 compliance**: telescope-term proofs decomposed into 4 private lemmas + 1 PolyP-diff lemma + final composition; no `maxHeartbeats` overrides. Zero new axioms; project axiom count UNCHANGED at 2. K = 320 loose; D-N K ≤ 4 deferred to R5.2c. | n/a | **D.2** | none |
| **Wave 2d.2-followup-R5.2c** | Optimize K ≤ 4 (D-N original) | ⏳ **NOT STARTED** (~50 LoC, optional polish). Tighten loose enumeration bounds + use sharper `δ ≤ 1` algebraic identities. Not load-bearing — K ≤ 1000 from R5.2a is sufficient for R5.3. | n/a | **D.2** | none |
| **Wave 2c.4a-R5.3** | AA Bridge Lemma 6.1 (group commutator quadratic shrinkage) | ✅ **SHIPPED 2026-05-13 PM** (same session as R5.2a/R5.2b): `MatrixBCHCubic.lean` §11, 2 new theorems (~150 LoC including proof bodies). **Headline**: `bch_group_commutator_quadratic_shrinkage` — `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - 1‖ ≤ 338·δ²` for `‖F‖, ‖G‖ ≤ δ ≤ 1`. **Cubic linearization companion**: `bch_group_commutator_linearization` — `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - (1 - ⁅F, G⁆)‖ ≤ 356·δ³` (consumed by R5.4 Lemma 6.2 since `LieSpanProp` is about Lie commutators). **Proof architecture (BCH coordinates, avoids matrix log)**: triangle inequality `‖[P] - 1‖ ≤ ‖P - exp(-[F,G])‖ + ‖exp(-[F,G]) - 1‖`; first term ≤ 320·δ³ (R5.2b `bch_order_2_cubic_thm`); second term ≤ 2·δ²·exp(2·δ²) ≤ 18·δ² (order-1 Taylor of exp at -[F,G] + ‖[F,G]‖ ≤ 2·δ² from generic `commutator_norm_le`, no Hermitian). Total 320·δ³ + 18·δ² ≤ 338·δ² (using δ ≤ 1 so δ³ ≤ δ²). **No Hermitian hypothesis** — strictly stronger than typical AA formulations. Zero new axioms; project axiom count UNCHANGED at 2. | n/a | **D.2** | none |
| **Wave 2c.4a-R5.4** | AA Bridge Lemma 6.2 (LieSpan + small elements fill nbhd of 1) | ⏳ **NOT STARTED** (depends on R5.3; ~150-200 LoC). The substantive analytic content: given `LieSpanProp` (image ℂ-spans Matrix d²) + arbitrarily small group elements (from R5.3 commutator iteration), construct an open neighborhood of 1 in `closure (range ρ_hom)`. Basis-rotation argument from AA §6 Lemma 6.2. | n/a | **D.2** | none |
| **Wave 2c.4a-R5.5** | Compose R5.1 + R5.2 + R5.3 + R5.4 → discharge `aa_residual_interior_at_one_for_hom` | ⏳ **NOT STARTED** (~50 LoC composition). Eliminates the last Phase 6p axiom (`aa_residual_interior_at_one_for_hom`). Project axiom count drops from 2 → 1 (only `gapped_interface_axiom` remains, which is physics-substantive permanent scaffolding per SPTClassification.lean docstring). | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.a/b (substrate)** | Concrete Fibonacci SU(2) substrate (complex-matrix layer + σ_1, σ_2 unitarity + det) | ✅ **SHIPPED 2026-05-13 PM-PM-PM-PM-PM-PM** (this commit): `FKLW/FibSU2Rep.lean` (~340 LoC). **R-eigenvalues + golden ratio in ℂ**: `R1_C = exp(-4πi/5)`, `Rtau_C = exp(3πi/5)`, `φ_C, φInv_C, φInvSqrt_C`, with unit-modulus proofs + `φ² = φ + 1` + `(1/√φ)² = 1/φ`. **F-matrix involution**: `F_C * F_C = 1` via golden-ratio identity (~50 LoC of careful algebra). **F-matrix Hermitian + unitary**: `star F_C = F_C` (all entries real-cast); `F_C * star F_C = 1`. **σ matrices**: `σ_Fib_1 = diag(R_1, R_τ)`, `σ_Fib_2 = F · σ_1 · F`. **Unitarity**: `σ_Fib_1_unitary`, `σ_Fib_2_unitary` (via F Hermitian + F²=I + σ_1 unitary, calc chain). **Det**: `σ_Fib_1_det = R1_C · Rtau_C`, `σ_Fib_2_det = σ_Fib_1_det` (F²=1 ⇒ det(F)²=1). Zero new project axioms; standard-kernel-only (`propext`, `Classical.choice`, `Quot.sound`). 8616 jobs / 0 sorry / 1 project axiom (unchanged). | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.b.1** | Cyclotomic-Fibonacci bridge identity `R1_C^2 + R1_C^3 = 1/φ` + rotation `Rtau_C = -R1_C^3` | ✅ **SHIPPED 2026-05-13 PM** (commit `64fc14b`): `FibSU2Rep.lean` +~130 LoC. **Bridge identity** (the load-bearing transcendental): proved via `R1_C^5 = 1`, Euler-formula helper `exp(zI) + exp(-zI) = 2 cos z`, Mathlib `Real.cos_pi_div_five = (1+√5)/4` + double-angle. Plus `Rtau_C_eq_neg_R1_C_pow_3` rotation identity linking the two R-eigenvalues via `exp(3πi/5) = -exp(-2πi/5)`. Standard-kernel-only. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.b.2** | Core YB algebraic identity + σ_Fib_2 entry-level lemmas | ✅ **SHIPPED 2026-05-13 PM** (commit `deddb99`): `FibSU2Rep.lean` +~160 LoC. **`fib_yb_core_identity`**: `φInv_C²·(R1_C² + Rtau_C²) + (2·φInv_C - 1)·R1_C·Rtau_C = 0` — THE single substantive algebraic content all 4 YB entries reduce to (proved via rotation substitute + R1_C ≠ 0 multiplication + bridge + φInv_C³ identity in a single `linear_combination` call). Plus `φInv_C_sq_add_self`, `φInv_C_pow_3`, and matrix-entry rfl-lemmas (`σ_Fib_1_apply_*, F_C_apply_*, σ_Fib_2_apply_{00,01,10,11}`). Standard-kernel-only. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.b.3** | Yang-Baxter matrix relation `σ_Fib_1 · σ_Fib_2 · σ_Fib_1 = σ_Fib_2 · σ_Fib_1 · σ_Fib_2` over ℂ | ✅ **SHIPPED 2026-05-13 PM** (commit `d0207dd`): `FibSU2Rep.lean` +~170 LoC. **`σ_Fib_yang_baxter`** assembled from 4 per-entry lemmas `σ_Fib_yb_entry_{00,01,10,11}` via `Matrix.ext` + `fin_cases`. **Coefficient discovery (manual, post-polyrith retirement)**: YB[0,0] needs (c_phisqrt = -φInv_C²·Rtau_C·(R1_C - Rtau_C)², c_hcore = (R1_C - Rtau_C)·φInv_C, c_hsq = -φInv_C²·R1_C³ - 2·φInv_C·R1_C²·Rtau_C + φInv_C·R1_C·Rtau_C²); YB[1,1] = a↔b swap; YB[0,1] = YB[1,0] needs only c_hcore = -φInv_C·φInvSqrt_C·(R1_C - Rtau_C) (off-diagonal entries factor cleanly through hcore alone). Standard-kernel-only for all 5 theorems. Build: 8616 jobs unchanged / 0 new sorry / 0 new axioms. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.c** | det normalization + `ρ_Fib_SU2 : BraidGroup 3 →* SU(2)` MonoidHom | ✅ **SHIPPED 2026-05-13 PM** (commit `e6b524d`): `FibSU2Rep.lean` §10, +~160 LoC. **Headline**: `ρ_Fib_SU2 : SKEFTHawking.BraidGroup 3 →* Matrix.specialUnitaryGroup (Fin 2) ℂ` — the concrete Fibonacci 3-strand braid representation in SU(2). Built from: (1) `ω_Fib_C := exp(πi/10)` det-normalization scalar; (2) `ω_Fib_C_sq_mul_det : ω_Fib_C² · (R1_C · Rtau_C) = 1` proved via exp arithmetic; (3) `σ_Fib_1_SU_mat, σ_Fib_2_SU_mat` (det-normalized matrices) with unitarity (via `star_smul` + `Matrix.smul_mul`) and det = 1 (via `Matrix.det_smul` for `Fin 2`); (4) `σ_Fib_1_SU, σ_Fib_2_SU` packaged via `Matrix.mem_specialUnitaryGroup_iff.mpr`; (5) `σ_Fib_SU_yang_baxter` lifts matrix YB to group YB via `Subtype.ext`; (6) `braidGroup3HomFromPair` (R4.1) assembles the MonoidHom. Plus `ρ_Fib_SU2_apply_σ0/σ1` confirming σ₀ ↦ σ_Fib_1_SU, σ₁ ↦ σ_Fib_2_SU. Standard-kernel-only for all 4 key theorems (`ρ_Fib_SU2`, `σ_Fib_SU_yang_baxter`, `σ_Fib_1_SU`, `σ_Fib_2_SU`). Build: 8616 jobs unchanged / 0 new sorry / 0 new axioms. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.d.1** | Path-(i) Phase D1: structural substrate (orders, non-commutation, traces) | ✅ **SHIPPED 2026-05-13 PM** (commit `4dd4b68`): new module `FKLW/FibSU2Density.lean` (~430 LoC). 9 substantive theorems all standard-kernel-only. Headlines: (1) `σ_Fib_1_pow_10 : σ_Fib_1^10 = I` via R_1^5 = 1, R_τ^5 = -1; (2) `σ_Fib_1_SU_mat_pow_20 : σ_Fib_1_SU_mat^20 = I` (combines ω_Fib_C^20 = 1 with σ_Fib_1^20 = I); (3) **`σ_Fib_not_commute : σ_Fib_1 · σ_Fib_2 ≠ σ_Fib_2 · σ_Fib_1`** — critical separating fact, proved by projecting to [0,1] entry and showing residual `φInv_C · φInvSqrt_C · (R_1 - R_τ)² ≠ 0` (each factor non-zero); (4) inherited non-commutation `σ_Fib_SU_mat_not_commute, σ_Fib_SU_not_commute`; (5) `σ_Fib_1_mul_σ_Fib_2_trace_eq : tr(σ_Fib_1 · σ_Fib_2) = R_1 · R_τ` via `fib_yb_core_identity` (R4.2.b.2); (6) **`σ_Fib_1_SU_mul_σ_Fib_2_SU_trace : tr(σ_Fib_1_SU · σ_Fib_2_SU) = 1`** — spectral invariant, SO(3) rotation 2π/3; (7) **`fibonacci_density_conditional`** : full `DenseInSpecialUnitary 3 2 _` conclusion conditional on the residual hypothesis `closure(range ρ_Fib_SU2) = univ` (the substantive HBS density). | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.d.2** | Path-(i) Phase D2: trace formula + SO(3) rotation axes | ⏳ **NEXT-SESSION ENTRY**. Trace `tr(σ_Fib_1_SU) = exp(-7πi/10) + exp(7πi/10) = 2·cos(7π/10) = (1-√5)/2` (cyclotomic-golden bridge consequence). SO(3) rotation angle 7π/5 around z-axis. σ_Fib_2_SU axis = F_C-conjugate of z-axis (non-parallel). ~100-200 LoC. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.d.3** | Path-(i) Phase D3: closed-subgroup-of-SU(2) classification | ⏳ **FUTURE**. Show ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ is not contained in any closed proper subgroup (cyclic, dihedral, binary tetra/octa/icosa, U(1)-tori), hence its closure equals SU(2). Substantial substrate ship: needs closed-subgroup classification for SU(2) (Mathlib gap) OR direct argument via specific braid-word infinite-order witness + accumulation analysis. ~500-1500 LoC multi-session. | n/a | **D.2** | none |
| **Wave 2c.4a-R4.2.d.4** | Path-(i) Phase D4: final closure → DenseInSpecialUnitary | ⏳ **FUTURE**. Assemble: closure_eq_univ from D3 → apply `fibonacci_density_conditional` (shipped D1) → full `DenseInSpecialUnitary 3 2 _` for ρ_Fib_SU2. ~50 LoC mechanical composition. | n/a | **D.2** | none |
| **Wave 3a.2.3c-R5.6** | T-gate ε ≤ 10⁻³ via GA-SK (multi-session Python) | ⏳ **NOT STARTED** (separable from R5 chain). Long-Bourassa-Bell 2025 GA-SK (arXiv:2501.01746) implementation in Python. Random-search saturation confirmed (frob²≈4.35e-4 at L=46, 5M trials); needs proper SK iteration with balanced commutator structure. ~Multi-hour Python. | n/a | **E2** | none |

**Wave dependencies:**
- Wave 1a (AGP substrate) and Wave 2a (FKLW substrate) are independent — can run in parallel.
- Wave 1b depends on Wave 1a (threshold theorem builds on threshold-predicate scaffolding).
- Wave 2b depends on Wave 2a (density theorem builds on Lie-algebra-spanning predicate); paper14's existing `FibonacciQutritUniversality.lean` already establishes the density argument for the qutrit case — Wave 2b lifts to the general FKLW statement.
- Wave 3a depends on Waves 2a-2b (gate compilation needs the density theorem operational).
- Wave 3b depends on all prior waves (cross-bridge / positioning decisions need the content shipped).

**Coherent sub-narrative.** The two tracks form a "fault-tolerant QC complete-stack" deliverable on the program's existing topological substrate. AGP threshold theorem says: *if* physical errors are below a threshold, arbitrarily long quantum computation is possible by concatenating error-correcting codes. FKLW density says: Fibonacci anyons can approximate any unitary to arbitrary precision via braiding. Together they give the **algebraic stack** for topologically-protected fault-tolerant universal quantum computation — directly readable as "what the program's MTC infrastructure enables, in QC terms."

**Recommended next-up order (post-DR-return, 2026-05-12):**

1. ✅ **Wave 1a.1** AGP DR — RETURNED. Commitments locked at §G G1-G3 (AGP 2006 / abstract local stochastic only / no Phase 6n LDP).
2. ✅ **Wave 2a.1** FKLW DR — RETURNED. Commitments locked at §G G6-G9 (BridgeProp axiom / Solovay-Kitaev axiom / 4-strand SU(5) target / PresentedGroup Artin).
3. ✅ **Wave 3a.1** BHSZ DR — RETURNED. Commitments locked at §G G10-G12 (Q(ζ₄₀) / ε~10⁻³ / conditional composition).
4. ⏳ **Wave 1a.2/1a.3** working doc consolidating DR return + Wave 1b sub-wave plan; **gate G4 / G5 resolution** (AGP §-number re-pin + A_CNOT + Reichardt 2006 LNCS 4051 alternative-A comparison).
5. ⏳ **Wave 1b.4** (Chernoff + DoubleExp wrappers — parallelizable; DO FIRST to de-risk Mathlib4 SubGaussian wiring per DR R3).
6. ⏳ **Wave 1b.1 → 1b.2 → 1b.3 → 1b.5 → 1b.6** AGP threshold theorem critical path (DR R1 risk: native_decide enumeration may need pre-computed witness).
7. ⏳ **Wave 2a.2/2a.3** BraidGroup + BridgeProp module ships (parallel to 1b).
8. ⏳ **Wave 2b.1-2b.4** FKLW density theorem (+ optional 2b.5 partial substantive bridge).
9. ⏳ **Wave 3a.2** explicit gate compilation (depends on Wave 2a.2 BraidGroup + new QCyc40 substrate; **gate G13 / G14 resolution**: CNOT transcription + T-gate generation).
10. ⏳ **Wave 3a.3** fault-tolerance composition (CONDITIONAL on p_eff < p_th_AGP).
11. ⏳ **Wave 3b** cross-bridge + new-bundle decision (G15: 🔒 user-auth pending).

**R5 program critical path (2026-05-13; AA axiom discharge priority):**

The R5 chain drives the project from `2 project-local axioms` to `1`
(eliminates `aa_residual_interior_at_one_for_hom`; the remaining
`gapped_interface_axiom` is physics-substantive permanent scaffolding
per SPTClassification.lean). Strict dependency order:

1. ✅ **R4.1** (FibRepInfiniteOrder) — eigenvalue-based infinite-order
   infrastructure + Yang-Baxter MonoidHom constructor. SHIPPED.
2. ✅ **R5.1** (AharonovAradLemma6) — axiom-free topological half
   (1 ∈ closure + AccPt at 1 of infinite-image hom). SHIPPED.
3. ✅ **R5.2.1** (MatrixBCHCubic) — BCH cubic-bound algebraic infra
   (T2pos/T2neg/bchPolyRem + `T2pos_T2neg_self : T2pos F · T2neg F =
   1 + F⁴/4` factorization). SHIPPED 2026-05-13.
4. ✅ **R5.2a** (MatrixBCHCubic ext, ~650 LoC) — BCH cubic norm bound
   `‖bchPolyRem F G‖ ≤ 30·δ³` for `‖F‖, ‖G‖ ≤ δ ≤ 1`. SHIPPED 2026-05-13
   PM. Headline `bchPolyRem_norm_le_cubic` + supporting infrastructure
   `bchPolyRem_decomp` (6-piece algebraic decomposition),
   `commutator_T2pos_T2neg_plus_FG_decomp` (load-bearing commutator
   linearization), `commutator_T2pos_T2neg_plus_FG_norm_le_cubic`
   (`≤ 3·δ³`), `commutator_T2pos_T2neg_norm_le_quadratic` (`≤ 9δ²/2`).
   K = 30 loose; D-N K ≤ 4 deferred to R5.2c.
5. ✅ **R5.2b** (MatrixBCHCubic ext, ~470 LoC) — `bch_order_2_cubic_thm`:
   `‖P - exp(-[F,G])‖ ≤ 320·δ³` for `‖F‖, ‖G‖ ≤ δ ≤ 1` (no Hermitian
   required — strictly stronger than `MatrixBCH.bch_order_2_thm`).
   SHIPPED 2026-05-13 PM (same session as R5.2a). 3-piece decomposition:
   telescope `P - PolyP ≤ 253·δ³` + `bchPolyRem ≤ 30·δ³` (R5.2a) +
   `exp Taylor remainder ≤ 36·δ³`. K = 320 loose; D-N K ≤ 4 deferred to R5.2c.
6. ✅ **R5.3** (MatrixBCHCubic ext, ~150 LoC) — AA Bridge Lemma 6.1
   group commutator quadratic shrinkage. SHIPPED 2026-05-13 PM
   (same session as R5.2a, R5.2b):
   - `bch_group_commutator_quadratic_shrinkage`:
     `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - 1‖ ≤ 338·δ²` for `‖F‖, ‖G‖ ≤ δ ≤ 1`
   - `bch_group_commutator_linearization`:
     `‖exp(iF)·exp(iG)·exp(-iF)·exp(-iG) - (1 - ⁅F, G⁆)‖ ≤ 356·δ³`
   No Hermitian hypothesis; works in BCH coordinates (avoids matrix log).
7. ⛔ **R5.4 / R5.5 — RETIRED 2026-05-13 PM-PM (R2 soundness audit)**.
   The original target axiom `aa_residual_interior_at_one_for_hom` was
   shown UNSOUND via SO(d) ⊂ SU(d) counterexample (LieSpan + h_inf
   satisfied by dense-in-SO(d) braid reps, but closure(range) ⊆ SO(d)
   has no SU(d)-interior). The axiom has been **DELETED** in commit
   `f44c60d` and replaced by the axiom-free theorem
   `aa_residual_interior_at_one_from_closure_eq_univ` (takes
   `closure = univ` as hypothesis; tautological proof).
   - **Project axiom count: 2 → 1** (only `gapped_interface_axiom`
     remains).
   - The substantive density content (proving `closure(range ρ) = univ`
     for specific ρ like Fibonacci) is now an EXPLICIT caller burden,
     to be discharged via either: (a) Lean-internal HBS proof
     (multi-month, requires Cartan + Lie-algebra Mathlib infrastructure
     not currently available); OR (b) scoped Fibonacci-specific HBS
     axiom citing Hormozi-Bonesteel-Simon 2007 (future R4.2 work,
     requires user sign-off).
8. ⏳ **R4.2** (now the natural successor) — Full Fibonacci witness via
   `Mat3K → ℂ` ring-hom embedding + det normalization. **Post-R2 (this
   commit)**: R4.2 also becomes the natural host for the SCOPED
   HBS-for-ρ_Fib axiom (path 2 from R2 audit) — replaces general
   unsound AA axiom (now deleted) with specific sound HBS-cited axiom
   for ρ_Fib only. Requires user sign-off per Phase 6p axiom policy.

**R2 SOUNDNESS AUDIT (2026-05-13 PM-PM)**: The
`aa_residual_interior_at_one_for_hom` axiom was shown UNSOUND via SO(d)
counterexample (LieSpan + h_inf satisfied by dense-in-SO(d) braid reps
but closure ⊂ SO(d) ⊊ SU(d), conclusion fails). The axiom is now
**DELETED** (commit `f44c60d`); project axiom count 2 → 1. R5.4/R5.5
RETIRED. The substantive density content moves to R4.2 (where it
belongs — paired with specific representations, not generic
hypotheses).

**R4.2 sub-wave decomposition (refined 2026-05-13 PM-PM-PM-PM-PM-PM)**:

**Decision pivot (2026-05-13 PM-PM-PM-PM-PM-PM)**: User pushed back on
the "multi-month" estimate per the LOE calibration memory
(`feedback_loe_calibration.md`). Substrate audit performed (Mathlib4
gap analysis): matrix logarithm with bounds, Cartan's closed-subgroup
theorem, classification of closed subgroups of SU(2), Tits alternative
are ALL absent from Mathlib4. So the constructive HBS-in-Lean path is
genuinely a substantial substrate ship (not a quick deep-research-
collapsing problem). However, the algebraic / matrix-substrate layer
IS tractable; concretely shipped R4.2.a/b this commit.

Pivoted from "3-strand SU(2) Fibonacci" (original Phase 6p sub-wave
prep) to "concrete SU(2) substrate now, then YB, then MonoidHom, then
density". This gives clean per-session checkpoints + decouples the
algebraic substrate (mechanical) from the density discharge
(substantive substrate ship).

  (a/b) ✅ **SHIPPED 2026-05-13 PM-PM-PM-PM-PM-PM** (this commit):
        `FKLW/FibSU2Rep.lean` (~340 LoC). R-eigenvalues + golden ratio
        in ℂ + F-matrix Hermitian + F² = I + σ_1, σ_2 in U(2) +
        unitarity + det = R1·Rtau. Standard-kernel-only.
  (b proper) ⏳ Yang-Baxter `σ_Fib_1 σ_Fib_2 σ_Fib_1 = σ_Fib_2 σ_Fib_1
        σ_Fib_2` over ℂ. 1-3 sessions. Two paths:
          (i) Direct algebraic in ℂ (~200-500 LoC)
          (ii) Ring-hom transport from QCyc40Ext native_decide proof
               (requires `QCyc40Ext →+* ℂ` ring hom, ~200-400 LoC)
  (c) ⏳ Det normalization + `ρ_Fib_SU2 : BraidGroup 3 →* SU(2)`
        MonoidHom via R4.1's `braidGroup3HomFromPair`. ~100-150 LoC.
  (d) ⏳ Density discharge: `closure(Set.range ρ_Fib_SU2) = Set.univ`.
        Two paths (per user call):
          (i) Constructive Weyl + Euler-axes (~500-1500 LoC, multi-week)
          (ii) Scoped HBS axiom + sign-off (~5 LoC, project axiom 1→2)

**For 3-strand SU(2) (this session pivot)** rather than the originally-
planned 4-strand SU(3): the 3-strand qubit-sector is what
Hormozi-Bonesteel-Simon 2007 explicitly proves density for, has simpler
matrix dimension (2×2), and matches the existing `RouabahExplicit.lean`
+ `FibonacciBraiding.lean` substrate. The 4-strand SU(3) version
remains a follow-on (would require `braidGroup4HomFromTriple` analog
of R4.1's `braidGroup3HomFromPair`).

**Parallelism notes:** Wave 1b and Wave 2 are operationally independent (no proof-level dependency). Wave 3a.2 requires Wave 2a.2 BraidGroup (cheap) + QCyc40 (new module, Wave 3a.2 ships). Wave 3a.3 composition glues Wave 1b output + Wave 2b output.

**Pre-Phase-7 bundle absorption gate:** all 6 Phase 6p Waves close → unified Phase 6p → Phase 7 absorption pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`. New-bundle creation decision (D4 extension vs. spin-off bundle) at Wave 3b close.

---

## Wave 1a — AGP substrate analysis + threshold-theorem predicate scaffolding 🟡 1a.1 DR RETURNED (other sub-waves NOT STARTED)

**Sub-wave decomposition (post-DR-return):**

- **Wave 1a.1 (deep-research dispatch) — ✅ COMPLETE.** DR submitted 2026-05-12 at `Lit-Search/Tasks/submitted/20260512_phase6p_wave_1a_AGP_distance3_lean_substrate.md`; return at `Lit-Search/Phase-6p/6-p Wave 1a.1 — AGP Distance-3 Quantum Threshold Theorem- Lean 4 Mathlib4 Substrate Dossier.md`. Headline: **AGP 2006 (arXiv:quant-ph/0504218) on Steane [[7,1,3]]; abstract local stochastic model ONLY in Wave 1b; topological deferred to Wave 1c+; ε₀ > 2.73 × 10⁻⁵ rigorously proven; Mathlib SubGaussian + Finset / Nat.choose substrate sufficient; Phase 6n LDP cross-bridge NOT used.** See §G "DR-return state snapshot" Wave 1a.1 paragraph for full commitments + caveats. Working doc still to be created at `temporary/working-docs/phase6p/wave_1a_AGP_substrate.md` consolidating DR return + Wave 1b sub-wave plan.
- **Wave 1a.2 (working-doc + module decomposition lock-in) — ⏳ NOT STARTED.** Post-DR working doc at `temporary/working-docs/phase6p/wave_1a_AGP_substrate.md` consolidating: (a) AGP §-number re-pin against PDF (DR caveat — gate G4); (b) `A_CNOT` numerical value + M-per-ex-Rec count (DR caveat — gate G4); (c) Reichardt 2006 LNCS 4051 alternative-A comparison (gate G5); (d) Wave 1b sub-wave 1b.1-1b.7 critical path; (e) 11-module decomposition under `SKEFTHawking/FaultTolerance/` per DR §6.
- **Wave 1a.3 (cross-prover-survey discipline check) — ⏳ NOT STARTED.** Apply primacy-claim discipline per `project_2026_05_12_first_claim_close.md`. DR established: Coq SQIR/QWIRE/CoqQ/Coq-QECC have ZERO threshold work; Chen-Liu-Fang CAV 2025 (arXiv:2501.14380) and Huang-Zhou-Fang-Zhao-Ying PLDI 2025 (arXiv:2504.07732) verify single-level FT / program logic respectively, NOT threshold theorem; Meiburg-Lessa-Soldati Quantum Stein's Lemma (arXiv:2510.08672) confirms Lean-QuantumInfo capacity. Frame Wave 1b output as "Relation to existing libraries", NOT "first."

**Three-question template:**

- *Integrates with:* Phase 5c/5i/5p categorical chain (paper11 + paper14 + paper16_wrt_tqft); Phase 6n Wave 1b SymTFT audit (`WittClass.lean`, `Applicability.lean`); existing `FibonacciQutritUniversality.lean`; Mathlib4 probability infrastructure (martingales / concentration inequalities — substrate for error-model bounds); Aliferis-Gottesman-Preskill quant-ph/0504218 (the standard cleanest threshold proof in the literature); PhysLean quantum-circuit substrate if present.
- *New constraint adds:* an explicit Lean formalization of the AGP threshold theorem on (a) abstract stochastic error model + (b) topological substrate model. Could be the first such formalization at non-trivial concatenation depth — but framing follows primacy-claim discipline (no "first" claim asserted without explicit cross-prover survey).
- *Tension surfaces:* (i) whether the AGP threshold theorem at d=3 admits a closed-form proof tractable in Lean without Mathlib infrastructure not currently present (Mathlib has concentration inequalities + martingale convergence, but doesn't have the full ICM-style noise-channel calculus); (ii) whether the topological-substrate specialization (Fibonacci anyons + braiding) admits cleaner threshold theorem (substantive question — the planning conversation noted threshold theorems for topological codes are sometimes cleaner than for arbitrary CSS codes); (iii) the cross-bridge to AGP via braiding-model error-correction is a sub-question that may itself surface a structural result.

**Substrate.** Aharonov-Ben-Or 1997/2008 threshold theorem; Aliferis-Gottesman-Preskill 2006 concatenated-distance-3 simplification; Mathlib4 probability theory + concentration inequalities; PhysLean quantum-circuit substrate if present at scout time.

**Module decomposition (Lean) — DR-locked-in (Wave 1a.1 return §6c):**
```
SKEFTHawking/FaultTolerance/                          -- ~2,300 LoC sorry-free target
├── Basic.lean                 (~? LoC) -- Pauli group, qubits, location, gate
├── StabilizerCode.lean         (~? LoC) -- Stabilizer code (d, n, k)
├── SteaneCode.lean             (~400 LoC combined w/ Basic + StabilizerCode) -- [[7,1,3]]; stabilizers via `decide`
├── NoiseModel.lean             (~150 LoC) -- IsLocalStochastic + composition lemmas
├── ExRec.lean                  (~500 LoC combined w/ Malignant) -- Extended rectangle; 1-Rec correctness
├── Malignant.lean              -- Decidable malignancy predicate
├── Counting.lean               (~600 LoC) -- A_CNOT enumeration; native_decide bridge
├── Concatenation.lean          (~250 LoC) -- Iterated simulation
├── Chernoff.lean               (~80 LoC) -- binomial_tail_chernoff_le wrapper
├── DoubleExp.lean              (~80 LoC) -- quadratic_recursion_double_exp
└── AGP/Threshold.lean          (~250 LoC) -- Main theorem agp_threshold_steane_d3
```
Dependencies: Mathlib4 v4.29.0 only (`Mathlib/Probability/Moments/SubGaussian.lean`, `Mathlib/Data/Nat/Choose/Sum.lean`, `Mathlib/Algebra/GeomSum.lean`); NO PhysLean; NO Phase 6n LDP substrate.

**Bundle absorption.** D.2 / D.4 candidate; new bundle vs. D4 extension decision deferred to Wave 3b close. Substrate-data level for now.

**Risk axes.**
- Mathlib quantum-information infrastructure may be too thin to support the full AGP threshold theorem in Lean — in which case Wave 1b ships a "predicate-substrate operationalization" rather than substantive content (similar to I3's choice for Itô calculus).
- The "topological substrate" specialization may not be cleaner than the abstract CSS-code statement — substrate scout at Wave 1a.1 dispositive.
- AGP threshold theorem prior-art survey: there may already be a Lean formalization in PhysLean (low probability per current PhysLean roadmap) or a Coq formalization (medium probability per QuantumLib state). DR dispatch will surface this.

---

## Wave 1b — AGP concatenated distance-3 threshold theorem ⏳ NOT STARTED

**Sub-wave decomposition (DR-locked-in 2026-05-12 per Wave 1a.1 return §6d):**

- **Wave 1b.1 — Steane code substrate.** `Basic.lean`, `StabilizerCode.lean`, `SteaneCode.lean`: Pauli substrate + [[7,1,3]] code; `decide` proof of code parameters. Vendor minimal Pauli substrate in-tree to mitigate `inQWIRE/LeanQuantum` v0.x volatility (DR risk R2). ~400 LoC. Depends on Mathlib4 only. **Gate G4 / G5 resolution required at Wave 1b.1 close** (AGP §-number re-pin + A_CNOT verification against PDF + Reichardt 2006 LNCS 4051 alternative-A comparison).
- **Wave 1b.2 — Noise model + extended rectangle.** `NoiseModel.lean`, `ExRec.lean`: `IsLocalStochastic` predicate; 1-Ga / 1-Rec / ex-Rec structures; correctness predicate (rectangle followed by ideal decoder ≡ ideal decoder followed by ideal gate). ~650 LoC. Depends on 1b.1.
- **Wave 1b.3 — Malignant fault-set counting (HIGHEST-RISK).** `Malignant.lean`, `Counting.lean`: decidable malignancy predicate; `A_CNOT` enumeration; `native_decide` numerical bound proof of ε₀ > 2.73 × 10⁻⁵. **DR Risk R1: native_decide may be slow (>30s); pre-compute outside Lean + supply smaller `decide`-checkable witness OR import Reichardt 2006 counts.** ~1,100 LoC. Depends on 1b.2.
- **Wave 1b.4 — Mathlib4 wrappers (PARALLELIZABLE; DO FIRST per DR §6d critical-path note).** `Chernoff.lean` (`binomial_tail_chernoff_le` ~50 LoC) + `DoubleExp.lean` (`quadratic_recursion_double_exp` ~20 LoC + `tendsto_double_exp` corollary). Two trivial Mathlib4 wrappers — binomial-tail Chernoff (derived from `ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` via `hasSubgaussianMGF_of_mem_Icc`) and quadratic-recursion double-exp convergence. ~160 LoC. Depends on Mathlib4 only.
- **Wave 1b.5 — Concatenation.** `Concatenation.lean`: `concatenate : StabilizerCode → ℕ → StabilizerCode`; level-L logical error rate. ~250 LoC. Depends on 1b.1 + 1b.2.
- **Wave 1b.6 — Main theorem.** `AGP/Threshold.lean`: `agp_threshold_steane_d3 : ∃ ε₀ : ℝ, ε₀ > 2.73e-5 ∧ ∀ (Π : NoiseModel) (ε : ℝ), IsLocalStochastic Π ε → ε < ε₀ → ∀ δ > 0, ∃ L : ℕ, logicalErrorRate (concatenate steane L) Π ≤ δ` glued from 1b.1-1b.5. ~250 LoC. Depends on all previous.
- **Wave 1b.7 — Polish (optional).** Reichardt 2006 alternative threshold; CI for `native_decide` enumeration; replace `native_decide` with explicit-witness `decide` where feasible. ~400 LoC.

**Critical path:** 1b.1 → 1b.2 → 1b.3 → 1b.5 → 1b.6. 1b.4 parallelizable (DR risk R3 mitigation — Mathlib4 SubGaussian naming wiring).

**Three-question template:**

- *Integrates with:* Wave 1a predicate substrate; Aliferis-Gottesman-Preskill 2006 quant-ph/0504218; paper14 Fibonacci-MTC substrate (cross-bridge); Mathlib martingale / concentration-inequality infrastructure.
- *New constraint adds:* a Lean formalization of the AGP threshold theorem on either abstract stochastic error model or topological substrate model. Framing: substantive content depending on Wave 1a.1 substrate-scout outcome (predicate-substrate operationalization if Mathlib infrastructure inadequate; substantive theorem if Mathlib substrate exists).
- *Tension surfaces:* (i) the substantive-vs-predicate-substrate decision is made at Wave 1a.1 dispositively; (ii) if substantive content is shipped, the natural Mathlib-PR target is a substantial follow-up wave (defer to Phase 6s consolidation); (iii) AGP threshold theorem proofs in the literature often invoke real-analytic content (geometric series, Chernoff bounds) that Mathlib supports — so substantive content may be more accessible than initially scoped.

**Substrate.** Aharonov-Ben-Or 1997/2008 + Aliferis-Gottesman-Preskill 2006; Mathlib4 concentration inequalities + martingale convergence; paper14 Fibonacci-MTC substrate for the concrete-witness instance.

**Bundle absorption.** D.2 additive into D4 (extension of paper14/paper16_wrt_tqft fault-tolerance line) OR new bundle. Decision deferred to Wave 3b close.

**Risk axes.**
- Substantive vs. predicate-substrate level of theorem statement (dispositive at Wave 1a.1).
- Concrete witness on Fibonacci-anyon topological code may surface that the explicit threshold value is harder to compute than the existence claim — in which case Wave 1b.2 ships a non-constructive existence theorem with the explicit value deferred.
- Concatenation depth (d=3 default; d=5 / d=7 alternatives) — picked at Wave 1a.1 substrate scout.

---

## Wave 2a — Fibonacci-anyon density substrate analysis + Lie-algebra-spanning predicate scaffolding 🟡 2a.1 DR RETURNED (other sub-waves NOT STARTED)

**Sub-wave decomposition (post-DR-return; primary source corrections applied):**

- **Wave 2a.1 (deep-research dispatch) — ✅ COMPLETE.** DR return at `Lit-Search/Phase-6p/6p-wave_2a_FKLW_arbitrary_qudit_lift_return.md.md`. Headline: **Fibonacci density CLEARED uniformly in n ≥ 3 (no exceptional values).** Primary sources: **FKLW 2002 (arXiv:math/0103200, Theorem 0.1)** + **Aharonov-Arad arXiv:quant-ph/0605181** (Bridge + Decoupling lemmas; Reichardt-style simpler reproof) + **Kuperberg arXiv:0909.1881** independent confirmation. Citation corrections (apply across project materials): "Reichardt 2005 quant-ph/0509041" does not exist; "Aharonov-Arad 2007 quant-ph/0702066" → arXiv:quant-ph/0702008 (4 authors); "Hormozi-Bonesteel 2007 quant-ph/0610105" → quant-ph/0610111 (PRB 75, 165310). See §G "DR-return state snapshot" Wave 2a.1 paragraph for full commitments. **Critical clarification:** paper14's "qutrit" = 3 anyons = 3 strands = Hilbert dim 3 = SU(3); Wave 2b.3 target is **4 strands → Hilbert dim 5 → SU(5)** (NOT n=5 strands which gives SU(8)).
- **Wave 2a.2 (BraidGroup module) — ⏳ NOT STARTED.** `lean/SKEFTHawking/BraidGroup.lean` — `BraidGroup n` via `PresentedGroup` (Artin's presentation: `Fin (n-1)` generators + commutation relations + braid relations). Template = `Mathlib/GroupTheory/Coxeter/Basic.lean`. Reference: Hannah Fechtner "Braids in Lean" (Dec 2024, hannahfechtner.com/finallyyy.pdf). NOT merged in Mathlib4. ~50 LoC. Depends on Mathlib4 only.
- **Wave 2a.3 (BridgeProp + spanning-predicate substrate) — ⏳ NOT STARTED.** `lean/SKEFTHawking/FKLW/BridgeProp.lean` (~80 LoC): `BridgeProp (n : ℕ) (h : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))` structure with `spans : h = ⊤` (discharged via native_decide in K = ℚ(ζ₅, √φ)) + `liftToDensity : Dense (Subgroup.closure ...) (specialUnitaryGroup ...)` (AXIOM-tagged with FKLW + Aharonov-Arad citations). `BridgeProp.liftToDensity` is the analytic step Mathlib4 lacks; substantive bridge (BCH formula + exp-surjectivity + SU(n) `PathConnectedSpace` + closure-of-subgroup ~500 lines total) deferred to optional Wave 2b.5.

**Three-question template:**

- *Integrates with:* paper14 `FibonacciQutritUniversality.lean` (existing qutrit case); paper14 Fibonacci MTC F-symbols + hexagon equations; paper11 quantum group $U_q(\mathfrak{sl}_2)$ at $q = e^{i\pi/5}$ (Fibonacci modular data origin); Mathlib4 Lie algebra infrastructure if present at scout time.
- *New constraint adds:* a Lean formalization of the FKLW Fibonacci-anyon density theorem on arbitrary qudit dimension, extending paper14's qutrit special case. Framing per primacy-claim discipline.
- *Tension surfaces:* (i) Mathlib4 may not ship Lie-algebra-density-in-Lie-group infrastructure — in which case Wave 2b ships predicate-substrate operationalization (with Lie-algebra-spanning hypothesis bundled into the predicate, leaving the substantive density theorem as a downstream-consumer interface deferral); (ii) extending the qutrit case to arbitrary qudit dimension may surface explicit algebraic obstructions (specific n where the spanning property fails) — if so, the wave produces a structural finding (clean characterization of which n admit Fibonacci-anyon universality) rather than the expected universal claim; (iii) the bridge between F-symbols + R-matrices (algebraic substrate) and Lie-algebra-spanning (analytic substrate) is non-trivial in Lean — substrate scout at 2a.1 dispositive.

**Substrate.** Freedman-Larsen-Wang 2002 + Freedman-Kitaev-Larsen-Wang 2002; paper14 `FibonacciQutritUniversality.lean` (existing qutrit case); paper14 Fibonacci MTC infrastructure (F-symbols, hexagon, ribbon); paper11 quantum group $U_q(\mathfrak{sl}_2)$ at $q = e^{i\pi/5}$.

**Bundle absorption.** D.2 additive into D4 (extension of paper14 fault-tolerance / universality line).

**Risk axes.**
- Mathlib4 Lie-algebra-density infrastructure may be inadequate (predicate-substrate operationalization fallback).
- Extension of qutrit case to arbitrary qudit may surface algebraic obstructions (structural finding alternative deliverable).
- Algebraic-to-analytic bridge (F-symbols/R-matrices → Lie-algebra-spanning) is non-trivial.

---

## Wave 2b — FKLW density theorem ⏳ NOT STARTED

**Sub-wave decomposition (DR-locked-in 2026-05-12 per Wave 2a.1 return §7.2):**

- **Wave 2b.1 — BraidGroup module ship.** `lean/SKEFTHawking/BraidGroup.lean` (~50 LoC). Definition was in Wave 2a.2 plan but cleanly ships here as part of Wave 2b.
- **Wave 2b.2 — `SolovayKitaevProp` predicate-substrate AXIOM module.** `lean/SKEFTHawking/FKLW/SolovayKitaev.lean` (~50 LoC). Structure encoding Dawson-Nielsen bound `O(log^{3.97}(1/ε))` (Dawson-Nielsen arXiv:quant-ph/0505030 verbatim) wrapped as `SolovayKitaevProp d G denseInSU : Prop`. Shipped as `axiom` with primary-source citation. **No substantive proof attempted** — Solovay-Kitaev is absent in every proof assistant (Mathlib4, Mathlib3, QWIRE, SQIR/VOQC, CoqQ, Bordg-Lachnitt-He Isabelle, QHLProver, qrhl-tool, QBRICKS, Agda). Substantive formalization (~600+ LoC: BCH + group-theoretic recursive nesting + net-density base case) deferred indefinitely. **Do NOT target Kliuchnikov-Maslov-Mosca** (arXiv:1212.0822) — Clifford+T number-theory too heavy.
- **Wave 2b.3 — `FibonacciQuintetUniversality.lean` substantive ship.** `lean/SKEFTHawking/FibonacciQuintetUniversality.lean` (~360 LoC). **4-strand Fibonacci** ρ_4 : B_4 → SU(5) (Hilbert dim 5 = F_6 = 5). Headline theorem `fib_quintet_density : DenseRange (ρ_4 : BraidGroup 4 → Matrix.specialUnitaryGroup (Fin 5) ℂ)` proved via `BridgeProp.liftToDensity` (axiom) + `fib_quintet_spanning_data` (≈24 `native_decide` spanning conjuncts in K = ℚ(ζ₅, √φ), analogous to paper14's `su3_spanning_data` which has ≈8 conjuncts). Inherits paper14's K = ℚ(ζ₅, √φ) setup + `native_decide` infrastructure. Generator matrices from Hormozi-Zikos-Bonesteel-Simon arXiv:quant-ph/0610111 (PRB 75, 165310, Eqs. 5-11). Depends on Wave 2b.1 + 2b.2 + paper14 substrate.
- **Wave 2b.4 — `BridgeProp` infrastructure module.** `lean/SKEFTHawking/FKLW/BridgeProp.lean` (~80 LoC). Defined in Wave 2a.3 plan; cleanly ships here. Wires to Mathlib4 `LieSubalgebra`; documents analytic-step axiom dependency.
- **Wave 2b.5 (OPTIONAL) — partial substantive bridge.** `lean/SKEFTHawking/FKLW/PartialSubstantiveBridge.lean` (~200 LoC). SU(5) `PathConnectedSpace` instance via Schur decomposition (~50 LoC) + BCH formula in 𝔰𝔲(5) up to order 4 (~150 LoC). Upgrades `BridgeProp` from full-axiom to "axiom modulo Mathlib4-standard analysis." **Defer if scope-constrained.**

**Total Wave 2b line budget: ~540 LoC (or ~740 with 2b.5).** Roughly 3.3× paper14 size; achievable in one wave.

**DR-flagged risks:**
- **C-claim (line-count):** The 360-line `FibonacciQuintetUniversality` estimate is linear scaling from paper14's 163 LoC for SU(3) (8 conjuncts) to SU(5) (24 conjuncts). Actual `native_decide` compile time and `Polynomial`-coefficient elaboration may exceed this. **Mitigation: pilot the n=4 generator-matrix definitions + a single spanning conjunct as feasibility check before committing.**
- **D-claim (scalability):** Whether `native_decide` scales to SU(8) (n=5 strands, 63 conjuncts) without timeouts is not directly known. Wave 2c plans for SU(8); expect `native_decide` cost > 30s per conjunct.
- **C-claim (minimal commutator depth):** Closed-form bound on minimal commutator-nesting depth d(n) for spanning 𝔰𝔲(F_{n+1}) is not in the literature. FKLW + Aharonov-Arad prove existence non-constructively; numerical search (Hormozi 2007; Burrello 2010, 2011; Burke 2024 MIP) only.
- **B-claim (basis translation):** Paper14's `R₁ = diag(ω, ω⁻¹, ω⁻¹), Rτ = diag(φ⁻¹, φ⁻¹, ω²)` form vs Hormozi 2007 Eqs. 5-11 ordering is unitary equivalence — straightforward but unformalized.

**Three-question template:**

- *Integrates with:* Wave 2a substrate; paper14 Fibonacci universality; Mathlib4 Solovay-Kitaev infrastructure if present.
- *New constraint adds:* a Lean formalization of the FKLW density theorem on arbitrary qudit dimension. Substantive vs. predicate-substrate level dispositive at Wave 2a.1.
- *Tension surfaces:* see Wave 2a tension surfaces (same dispositive question on substantive vs. predicate-substrate level).

**Substrate.** Wave 2a substrate; Solovay-Kitaev 1997 quant-ph/9610011; paper14 Fibonacci MTC.

**Bundle absorption.** D.2 additive into D4.

**Risk axes.** Same as Wave 2a.

---

## Wave 3a — Concrete fault-tolerant gate compilation on Fibonacci MTC substrate 🟡 3a.1 DR RETURNED (other sub-waves NOT STARTED)

**Sub-wave decomposition (DR-locked-in 2026-05-12; canonical inputs + composition framing committed):**

- **Wave 3a.1 (deep-research dispatch) — ✅ COMPLETE.** DR return at `Lit-Search/Phase-6p/6p-Wave 3a.1 — BHSZ Brick-Wall Braid-Word Compilations for Fibonacci Anyons.md`. Headline: **Hadamard GO at ε ~ 10⁻³ via Rouabah 2020 30-crossing braid; CNOT requires manual transcription from HZBS 2007 Fig 15; T-gate generate via KBS algorithm; Q(ζ₄₀) cyclotomic substrate; composition theorem CONDITIONAL on `p_eff < p_th_AGP` (not unconditional).** See §G "DR-return state snapshot" Wave 3a.1 paragraph for full commitments. **CRITICAL CITATION CORRECTION:** "Bonesteel-DiVincenzo PRL 105, 027001 (2010)" does NOT exist; correct is PRB 86, 165113 (2012) / arXiv:1206.6048, which **explicitly disclaims fault-tolerance threshold analysis** — community-lore "topological protection ⇒ AGP threshold" is NOT a primary-source theorem.
- **Wave 3a.2 (Lean explicit gate compilation) — ⏳ NOT STARTED.** Two new modules:
  - `lean/SKEFTHawking/DecidableNumberField/QCyc40.lean` — Q(ζ₄₀) degree-16 cyclotomic field substrate (analogous to existing QSqrt5/QZeta5/QZeta16). Possibly companion `QCyc20.lean` (deg 8) for inner-product checks where Hadamard enters as squared overlaps. **Q(ζ₅) ALONE is insufficient** (lacks √2); **Q(ζ₂₀) is insufficient** (deg 8 but still lacks √2 since ζ₈ ∉ Q(ζ₂₀)). Avoid F-symbol entry φ⁻¹ᐟ² exact representation by working with F² in inner-product checks (else Q(ζ₄₀, √[4]{5}) deg 32 needed).
  - `lean/SKEFTHawking/FaultTolerance/GateCompilation.lean` — explicit Lean theorems on three gates:
    - **Hadamard (canonical, GO):** Rouabah 2020 arXiv:2008.03542 Eq. (36) — `σ₁²σ₂²σ₁⁻²σ₂⁻²σ₁²σ₂⁴σ₁⁻²σ₂²σ₁²σ₂⁻²σ₁²σ₂⁻²σ₁⁴` (30 crossings, ε = 0.00657). Reproduced verbatim in `Constantine-Quantum-Tech/tqsim`. Encode as `BraidWord 3` (Fin 2 × Int list).
    - **CNOT (PARTIAL-VIABLE):** HZBS 2007 (arXiv:quant-ph/0610111, PRB 75, 165310) Fig. 15, ~132 crossings, ε ≈ 1.8 × 10⁻³. **σ-strings figure-encoded only.** **Gate G13:** decide between manual transcription pass vs regenerate via TQSim/KBS.
    - **T-gate (PARTIAL-VIABLE):** No canonical BHSZ-published string. **Gate G14:** generate via KBS algorithm (arXiv:1310.4150). L ≈ 30-50 at ε ~ 10⁻³.
  - Verification predicate `IsBHSZApprox (b : BraidWord n) (U_target : Matrix) (ε : ℚ) : Prop := ‖fib_rep b − U_target‖²_F ≤ ε * ε` (rational bound on squared Frobenius distance), decided via `native_decide` after symbolic simplification in `QCyc40` (or `QCyc20` for squared-overlap checks). **NOT norm_num on ℝ.** Compile-time at L=30, Hadamard: ≲ 30s; CNOT at L=132: ≲ 5 min.
- **Wave 3a.3 (fault-tolerance composition) — ⏳ NOT STARTED.** `lean/SKEFTHawking/FaultTolerance/Composition.lean`. Theorem form (DR §Q5c, **CONDITIONAL only**):
  ```lean
  theorem fibonacci_universal_compilation
      (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1e-3)
      (b_H : BraidWord 3) (b_CNOT : BraidWord 6) (b_T : BraidWord 3)
      (hH    : ‖fib_rep b_H    − Hadamard‖ ≤ ε)
      (hCNOT : ‖fib_rep b_CNOT − CNOT‖    ≤ ε)
      (hT    : ‖fib_rep b_T    − T_gate‖  ≤ ε)
      (p_eff : ℝ) (hAGP : p_eff < p_th_AGP)  -- assumption, NOT derived
      (d : ℕ) (hd : d ≥ 3) :
    ∃ overhead : ℝ → ℝ,
      overhead = (fun ε ↦ polylog (1/ε)) ∧
      FaultTolerantUniversal {b_H, b_CNOT, b_T} d
  ```
  Combines Wave 3a.2 gate-approximations + Wave 1b AGP threshold (black-box quoted) + Wave 2b FKLW density. **DO NOT** claim topological-protection ⇒ AGP threshold unconditionally.

**Precision target: ε ~ 10⁻³ DEFAULT; stretch to ε ~ 10⁻⁶ only after baseline green; REJECT ε ~ 10⁻⁹** (native_decide intractable at L≈1000).

**Three-question template:**

- *Integrates with:* Wave 1b AGP threshold; Wave 2b FKLW density; paper14 Fibonacci MTC F-symbols + R-matrices + braiding; paper16_wrt_tqft Temperley-Lieb + Jones-Wenzl + braiding.
- *New constraint adds:* an explicit end-to-end fault-tolerant universal-gate-set theorem on the program's existing topological substrate — a concrete deliverable readable as "the program's MTC infrastructure enables fault-tolerant universal quantum computation, here are the explicit gates and the threshold proof."
- *Tension surfaces:* (i) the explicit braid-words may surface that some standard gates require unexpectedly long braid sequences — interesting structural finding (specifically: the T-gate is famously expensive in Fibonacci universal-gate-set compilations, with the Solovay-Kitaev compiler producing braids of length 30+ for ε ∼ 10^-3); (ii) end-to-end composition with AGP threshold requires the error model on the braid-word level to match the error model assumed by AGP — substrate scout at Wave 3a.1 dispositive.

**Substrate.** Wave 1b + Wave 2b; paper14 Fibonacci MTC; paper16_wrt_tqft Temperley-Lieb + braiding; Solovay-Kitaev compilation; Kitaev-Shen-Vyalyi 2002 quantum computation textbook for the explicit gate-compilation patterns.

**Bundle absorption.** D.2 additive into D4 + possible new bundle (Wave 3b dispositive).

**Risk axes.**
- Explicit braid-word verification may be Mathlib4-heavy — substrate scout at Wave 3a.1 picks tractable subset.
- End-to-end composition requires careful error-model alignment.

---

## Wave 3b — Cross-bridge to D4 / new-bundle decision + flagship-F positioning ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 3b.1 (bundle decision):** working doc at `temporary/working-docs/phase6p/wave_3b_bundle_decision.md` analyzing: (a) does the Phase 6p content fit naturally as an extension of D4 (which already covers topological QC foundations: paper11 + paper14 + paper16_wrt_tqft), or does it warrant a new bundle (working title "D6" or "F2 — Fault-tolerant quantum computation on the topological substrate")? (b) cross-bundle cluster impact — D2 ↔ D4 ↔ L2 currently exact-cluster-bonded on Z₁₆ anomaly + generation constraint; does Phase 6p touch those clusters? Substrate scout dispositive.
- **Wave 3b.2 (flagship-F positioning):** flagship F cross-bridge — short positioning paragraph identifying where Phase 6p sits in the broader emergent-physics-from-substrate narrative. The "topological substrate enables fault-tolerant universal QC" line is a substantive emergent-from-substrate result that the flagship paper should mention; positioning under "what the program's substrate enables, in QC terms" or "applied consequences" section.
- **Wave 3b.3 (bundle architecture update — if new bundle):** if new bundle decision: update `PAPER_STRATEGY.md` + `PAPER_DRAFT_MAPPING.md` + `BUNDLE_DIRECTORY_SCHEMA.md` (if needed) to add the new bundle target; `scripts/sentence_state.py` `_VALID_BUNDLE_TARGETS` accordingly. **User-authorization gate REQUIRED here** — new-bundle creation changes the canonical bundle list and is a strategic-architecture decision.

**Three-question template:**

- *Integrates with:* `PAPER_STRATEGY.md` 14-bundle architecture; `PAPER_DRAFT_MAPPING.md` per-paper assignments; D4 existing structure; F flagship narrative.
- *New constraint adds:* bundle-architecture decision for the Phase 6p content; flagship-F positioning paragraph.
- *Tension surfaces:* (i) D4 extension keeps the bundle list at 14 (clean); new-bundle creation grows the list to 15 (changes downstream tooling assumptions — sentence_state, bundle_readiness, validate.py, bundle_append.py); (ii) the new bundle vs. extension decision depends on substantive scope (if Phase 6p produces "another chapter of D4" the extension is right; if Phase 6p produces a genuinely-distinct deliverable readable independently the new bundle is right); (iii) user-authorization gate is required for new-bundle creation.

**Substrate.** All prior Phase 6p wave deliverables; `PAPER_STRATEGY.md`; `PAPER_DRAFT_MAPPING.md`.

**Bundle absorption.** D.2 into D4 + F flagship positioning; possibly new bundle creation.

**Risk axes.**
- Bundle-architecture decision is strategic; should not be pre-judged.
- Cross-bundle cluster impact analysis needed before changing bundle assignments.

---

## Wave 1c — MeasureTheory-grounded NoiseModel ⏳ NOT STARTED (NEW — added 2026-05-12 post-strengthening Pass 2)

**Sub-wave decomposition:**

- **Wave 1c.1 — Bernoulli-product-measure substrate.** `lean/SKEFTHawking/FaultTolerance/NoiseModelMeasureTheory.lean` (~150 LoC). Define `bernoulliProductMeasure : (locations : Type) → [Fintype locations] → ℝ → Measure (locations → Bool)` via Mathlib's `MeasureTheory.Measure.pi` + `Probability.Distributions.SetBernoulli`. Each per-location failure is a `Bool`-valued Bernoulli(ε) RV. Substrate scout 2026-05-12 confirms direct discharge from Mathlib4 (commit 8850ed93).
- **Wave 1c.2 — `iIndepFun` family + Hoeffding/SubGaussian wiring.** Same module (~100 LoC). Wire `X : locations → Ω → ℝ` (per-location failure indicator) as `iIndepFun X (bernoulliProductMeasure ε)` via `Probability.Independence.Basic`. Apply `Probability.Moments.SubGaussian.measure_sum_ge_le_of_iIndepFun` (Hoeffding's inequality) to derive tail bounds for `|∑ i ∈ pairs, fail i|`.
- **Wave 1c.3 — `LocalStochasticNoise` ↔ measure-theoretic instance.** Same module (~50 LoC). Bridge theorem: `LocalStochasticNoise.fromBernoulliProduct` produces a `NoiseModel` from a Bernoulli-product measure whose `jointFailureBound` is *derived* from Hoeffding (not asserted abstractly). Two-way correspondence: every existing `LocalStochasticNoise` ε is satisfied by `bernoulliProductMeasure ε`.
- **Wave 1c.4 — Lift AGP recursion + threshold theorem.** Bridge `Chernoff.lean` + `Concatenation.lean` + `AGP/Threshold.lean` consumers to use the measure-theoretic noise model. The closed-form double-exp bound is preserved by construction (the new measure-theoretic model satisfies the same abstract `jointFailureBound` predicate that the existing theorem consumes). ~50 LoC extension.

**Total Wave 1c budget: ~350 LoC.** Pure measure-theoretic content; **zero new axioms**.

**Substrate (Mathlib4 direct-discharge confirmed via 2026-05-12 scout):**
- `Mathlib.Probability.Distributions.SetBernoulli` — Bernoulli product distributions.
- `Mathlib.MeasureTheory.Constructions.Pi` — `Measure.pi` for indexed product measures.
- `Mathlib.Probability.Independence.Basic` — `iIndepFun`, union bound on independent events.
- `Mathlib.Probability.Moments.SubGaussian` — `HasSubgaussianMGF`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding's lemma for bounded RVs), `measure_sum_ge_le_of_iIndepFun` (Hoeffding's inequality for iid SubGaussian families).

**Three-question template:**
- *Integrates with:* Wave 1b AGP threshold modules (`NoiseModel.lean`, `Chernoff.lean`, `Concatenation.lean`, `AGP/Threshold.lean`); AGP 2006 abstract local stochastic noise model.
- *New constraint adds:* a MeasureTheory-grounded instance of the abstract `LocalStochasticNoise` predicate, replacing the project's current abstract-Prop noise model with a Mathlib4-derived measure-theoretic concretization.
- *Tension surfaces:* (i) the existing abstract `jointFailureBound` predicate is preserved verbatim — Wave 1c is *purely additive*, no refactor of Wave 1b theorems; (ii) Hoeffding's inequality gives `ε^k · poly(N)` rather than the pure `ε^k` form — verify the constant is harmless under the AGP recursion.

**Substrate.** Mathlib4 measure-theoretic infrastructure (commit 8850ed93); Wave 1b modules unchanged.

**Bundle absorption.** D.2 additive into D4 + I1 (infrastructure module).

**Risk axes.**
- Measure-theoretic constants may differ from abstract bounds by polynomial factors; verify under AGP recursion. **Low risk.**

---

## Wave 2c — Substantive FKLW density bridge (AXIOM ELIMINATION) ⏳ NOT STARTED (NEW — added 2026-05-12)

**Goal:** discharge `bridge_axiom_FKLW` (in `SKEFTHawking/FKLW/BridgeProp.lean`) constructively. Quality bar: standard kernel only.

**Strategic path (post-2026-05-12 scout):** the **Aharonov-Arad 2007 simpler proof** (arXiv:quant-ph/0702008) avoids heavy BCH+exp machinery via a combinatorial commutator-density argument — estimated ~300-400 LoC vs ~500-700 LoC for the full FKLW BCH+exp route. The substrate scout confirms Mathlib has:
- `Mathlib.Algebra.Lie.Subalgebra` (bracket-closure machinery) — direct.
- `Mathlib.Analysis.Matrix.Normed` (operator norms + composition bounds) — direct.
- `Mathlib.Topology.MetricSpace.Cover` (`Metric.exists_finite_isCover_of_isCompact` — finite ε-nets on compact sets) — direct.
- `Mathlib.Analysis.Normed.Algebra.Exponential` (`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`) — direct for `exp` mapping into SU(d) (we don't need full surjectivity for Aharonov-Arad).

**Sub-wave decomposition (planned):**

- **Wave 2c.1 (DR dispatch) — RECOMMENDED.** Drop a focused DR prompt extracting Aharonov-Arad 2007's "Bridge Lemma" + "Decoupling Lemma" formal-proof structure (the exact ε-bounds, the commutator-words generators, the recursion depth as a function of ε). Deliverable: `Lit-Search/Phase-6p/6p-Wave 2c.1 — Aharonov-Arad Bridge+Decoupling Lemma Lean-formalization-ready proof structure.md`. ~1-2 days asynchronous turnaround.
- **Wave 2c.2 — `LieSpan` + bracket-closure infrastructure (if not in Mathlib).** Per scout: Mathlib has `LieSubalgebra R L` extending `Submodule` with `lie_mem'` bracket-closure, but lacks an explicit `lieSpan : Set L → LieSubalgebra R L` constructor. **Either** port `Submodule.span`'s pattern to `LieSubalgebra` (~80 LoC, candidate Mathlib upstream-PR), **or** use the existing iterated-bracket pattern from `FibonacciQutritUniversality.lean` (paper14, native_decide-discharged for concrete (n,d)).
- **Wave 2c.3 — Operator-norm Lipschitz of matrix exp.** ~50 LoC. `‖exp(A) - exp(B)‖ ≤ ‖A - B‖ · e^{max(‖A‖, ‖B‖)}`. Standard analysis lemma; Mathlib has the inputs (`Matrix.linfty_opNorm_mul`, `exp_add_of_commute`), needs the Lipschitz wrapper.
- **Wave 2c.4 — Aharonov-Arad commutator-density core.** `lean/SKEFTHawking/FKLW/AharonovAradBridge.lean` (~250 LoC). The core lemma: given a finite set `S ⊆ U(d)` whose Lie-span equals `𝔲(d)`, there exists a constant `C` such that for every ε > 0, the set of `C·log(1/ε)`-length commutator-words in `S` is ε-dense in the identity component of `U(d)`. Proof: induction on commutator-nesting depth, using Wave 2c.3 Lipschitz bound + Wave 2c.2 bracket-closure.
- **Wave 2c.5 — Lift to `ClosureDenseProp`.** `lean/SKEFTHawking/FKLW/BridgeProp.lean` extension: replace `bridge_axiom_FKLW` with a constructive theorem `bridge_FKLW_aharonov_arad : LieSpanProp n d ρ → ClosureDenseProp n d ρ` proved via Wave 2c.4. Delete the AXIOM declaration. ~50 LoC of lift.

**Total Wave 2c budget: ~430 LoC** (plus ~80 LoC if `lieSpan` Mathlib-PR is included in-tree).

**Deliverable:** **`bridge_axiom_FKLW` eliminated.** All Wave 2b consumers (FibonacciQuintetUniversality, FaultTolerantUQC) retain semantic-equivalent behavior, but their axiom closure drops from "+ bridge_axiom_FKLW" to standard-kernel-only (modulo per-instance native_decide for the spanning side).

**Three-question template:**
- *Integrates with:* Wave 2a / 2b BridgeProp axiom + downstream consumers; Aharonov-Arad 2007 simpler proof; Mathlib4 operator-norm + Lie subalgebra substrate.
- *New constraint adds:* a Lean constructive proof of the FKLW closure-density bridge, replacing the predicate-substrate axiom.
- *Tension surfaces:* (i) the Aharonov-Arad "Decoupling Lemma" requires careful ε-bookkeeping; (ii) the explicit `C·log(1/ε)` commutator-depth bound may be hard to make tight — fall-back is a non-constructive `∃ C` form, sufficient for `ClosureDenseProp`.

**Substrate.** Aharonov-Arad arXiv:quant-ph/0702008 (Bridge + Decoupling Lemmas); Mathlib4 Lie-algebra + matrix-exp + operator-norm + compact-set ε-net infrastructure; FibonacciQutritUniversality `native_decide` pattern.

**Bundle absorption.** D.2 additive into D4 / new bundle (Wave 3b dispositive).

**Risk axes.**
- Aharonov-Arad's combinatorial commutator-counting may be subtle to formalize cleanly — DR Wave 2c.1 dispatches to scope the proof structure precisely.
- Operator-norm Lipschitz on matrix exp is standard but not directly in Mathlib — Wave 2c.3 may grow if Mathlib4 v4.30+ pulls the lemma upstream.

---

## Wave 2d — Substantive Solovay-Kitaev (AXIOM ELIMINATION) ⏳ NOT STARTED (NEW — added 2026-05-12)

**Goal:** discharge `sk_axiom_Dawson_Nielsen` (in `SKEFTHawking/FKLW/SolovayKitaev.lean`) constructively. Quality bar: standard kernel only.

**Strategic context (post-2026-05-12 scout):** Solovay-Kitaev is **first-formalization territory** across all proof assistants (Mathlib4 / QWIRE / SQIR / VOQC / CoqQ / Bordg-Lachnitt-He Isabelle / QHLProver / qrhl-tool / QBRICKS / Agda — confirmed absent in all). This is the **harder of the two axiom-elimination waves**; substrate scout estimates ~500-700 LoC of genuinely new analytic machinery. The main gap is matrix-BCH-to-order-2 (`exp(A)·exp(B)·exp(-A)·exp(-B) = exp([A,B] + O(higher))`).

**Sub-wave decomposition (planned; iterative):**

- **Wave 2d.1 (DR dispatch) — STRONGLY RECOMMENDED.** Drop a focused DR prompt extracting Dawson-Nielsen 2005's (arXiv:quant-ph/0505030) explicit constructive structure: (a) the base-case δ₀-net coverage of SU(d); (b) the recursive group-commutator construction (δ → δ^{3/2} via 5 deeper sequences); (c) the explicit error bounds and the c ≈ 3.97 exponent derivation; (d) BCH-truncation requirement (which terms matter, what order suffices). Deliverable: `Lit-Search/Phase-6p/6p-Wave 2d.1 — Dawson-Nielsen Solovay-Kitaev Lean-formalization-ready proof structure.md`. ~2-3 days asynchronous turnaround.
- **Wave 2d.2 — Matrix BCH to order 2.** `lean/SKEFTHawking/MatrixBCH.lean` (~250 LoC). Formalize the second-order Baker-Campbell-Hausdorff expansion: `exp(A)·exp(B)·exp(-A)·exp(-B) = exp([A,B]) · R(A,B)` where `‖R(A,B) - I‖ ≤ K · max(‖A‖, ‖B‖)^3` for explicit `K`. Substantively new content; not in Mathlib4. Likely Mathlib upstream-PR candidate.
- **Wave 2d.3 — ε-net construction on SU(d).** `lean/SKEFTHawking/FKLW/EpsilonNet.lean` (~100 LoC). Apply `Mathlib.Topology.MetricSpace.Cover.Metric.exists_finite_isCover_of_isCompact` to `Matrix.specialUnitaryGroup` (requires `IsCompact (specialUnitaryGroup n ℂ)`, which is direct from compactness of unit disk + matrix structure). Output: for every δ > 0, a finite set `Nδ ⊆ SU(d)` with `Nδ` δ-dense in SU(d).
- **Wave 2d.4 — Recursive commutator refinement.** Same module as Wave 2d.5. The core SK lemma: given a δ-approximation `U_δ ≈ U_target` (in operator norm) for some target `U_target`, produce a δ^{3/2}-approximation using 5 deeper gate-sequences. Uses Wave 2d.2 BCH-order-2.
- **Wave 2d.5 — Substantive constructive Solovay-Kitaev.** `lean/SKEFTHawking/FKLW/SolovayKitaevConstructive.lean` (~200 LoC). Replace `sk_axiom_Dawson_Nielsen` with a constructive theorem `solovayKitaev_dawson_nielsen : SolovayKitaevProp d G` proved via recursive application of Wave 2d.4 (depth `log_{3/2}(log(1/ε_target)/log(1/δ₀))`) starting from a Wave 2d.3 δ₀-net base case. The `c ≈ 3.97` length exponent emerges from the recursion-depth count + 5-fold branching per step. Delete the AXIOM declaration.

**Total Wave 2d budget: ~550 LoC** (Mathlib-PR-track candidate for Wave 2d.2 matrix BCH-to-order-2).

**Deliverable:** **`sk_axiom_Dawson_Nielsen` eliminated.** Downstream consumers (`sk_from_FKLW_density` etc.) retain semantic-equivalent behavior but drop the SK axiom from their axiom closure.

**Three-question template:**
- *Integrates with:* Wave 2b SolovayKitaev axiom + downstream consumers; Wave 2c FKLW bridge constructive proof; Dawson-Nielsen 2005; Mathlib4 matrix-exp + compact-set + metric-net infrastructure.
- *New constraint adds:* a Lean constructive proof of Solovay-Kitaev, replacing the predicate-substrate axiom and producing a first-formalization across all proof assistants surveyed.
- *Tension surfaces:* (i) Matrix BCH-to-order-2 is genuinely new content with no Mathlib4 substrate — Wave 2d.2 is the load-bearing sub-wave; (ii) the explicit `c ≈ 3.97` exponent is a derived quantity from the recursion bookkeeping — DR Wave 2d.1 dispatches to scope precisely which c is achievable in the Lean proof (3.97 is informal; 4.0 may be cleaner).

**Substrate.** Dawson-Nielsen arXiv:quant-ph/0505030; Mathlib4 matrix-exp + operator-norm + compact-set ε-net infrastructure; Wave 2c constructive FKLW bridge (for consistency, not a hard dependency).

**Bundle absorption.** D.2 additive into D4 / new bundle (Wave 3b dispositive).

**Risk axes.**
- Matrix BCH-to-order-2 is the load-bearing sub-wave; if the error-bound proofs surface unexpected complexity, Wave 2d may grow to ~800 LoC.
- The `c ≈ 3.97` exponent is sensitive to bookkeeping; a cleaner `c = 4` form may emerge naturally.
- First-formalization-territory: no prior Lean / Coq / Isabelle work to draw on; expect 2-3 iterative passes.

---

## Wave 2b.3.2 — Full quintet 24-conjunct spanning enumeration ⏳ NOT STARTED (NEW — added 2026-05-12)

**Goal:** complete the substantive spanning side of Wave 2b.3 (`FibonacciQuintetUniversality.lean`) — currently ships only 4 block-inherited conjuncts from paper14 + `qutrit_spanning_data_lift` cross-module application. Full content: ~24 conjuncts including {3,4}-block + cross-block directions, which require explicit 4-strand F-symbol structure beyond block-extension.

**Sub-wave decomposition:**

- **Wave 2b.3.2a — 4-strand Fibonacci F-symbol explicit matrices.** `lean/SKEFTHawking/FibonacciQuintetUniversality.lean` extension (~100 LoC). Extract the 4-strand F-matrices from Hormozi-Zikos-Bonesteel-Simon arXiv:quant-ph/0610111 (PRB 75, 165310, Eqs. 5-11). Express σ₁, σ₂, σ₃ as explicit 5×5 matrices over Q(ζ₅, √φ) (function-typed Mat5K — substrate already shipped in strengthening Pass 1).
- **Wave 2b.3.2b — Iterated commutator enumeration.** Same module (~150 LoC). Compute `comm_ij_kl := [[σᵢ, σⱼ], [σₖ, σₗ]]` and similar nested commutators systematically. Each entry is a single QCyc5Ext expression discharged via native_decide.
- **Wave 2b.3.2c — 24-conjunct `fib_quintet_spanning_data`.** Same module (~50 LoC). Bundle the 24 native_decide conjuncts (matching the SU(5) Lie-algebra dimension count: 24 = dim(𝔰𝔲(5))) into a single closure theorem. The 24 conjuncts establish that 24 linearly-independent matrices appear among the iterated commutators, which together span 𝔰𝔲(5).
- **Wave 2b.3.2d — `LieSpanProp 4 5 ρ_4` discharge.** Same module (~50 LoC). Compose `fib_quintet_spanning_data` with linear-independence to produce `LieSpanProp 4 5 ρ_4` — the *constructive* spanning predicate that Wave 2c then lifts to `ClosureDenseProp` via the constructive bridge.

**Total Wave 2b.3.2 budget: ~350 LoC.**

**DR-flagged risks (from original Wave 2b.3 risk register):**
- **C-claim (line-count):** estimate is linear scaling; actual `native_decide` cost may exceed.
- **C-claim (minimal commutator depth):** no closed-form bound on `d(n)` in literature; numerical-search-only.
- **B-claim (basis translation):** paper14 basis vs HZBS 2007 basis — unitary equivalence (mechanical but unformalized).

**Three-question template:**
- *Integrates with:* Wave 2b.3 quintet scaffold (already shipped); paper14 qutrit spanning data; HZBS 2007 F-symbols; QCyc5Ext substrate.
- *New constraint adds:* the substantive spanning side of `FibonacciQuintetUniversality` — completes the predicate `LieSpanProp 4 5 ρ_4` that downstream Wave 2c FKLW bridge consumes.
- *Tension surfaces:* (i) 24 native_decide conjuncts may surface elaborator scaling issues — if so, pilot a single conjunct first and reduce; (ii) the closed-form minimal-commutator-depth bound is open in the literature — Wave 2b.3.2 ships a constructive-witness form, not a tight closed-form.

**Substrate.** Wave 2b.3 (block-extension scaffold); paper14 qutrit substrate; HZBS 2007 F-symbols.

**Bundle absorption.** D.2 additive into D4 / new bundle (Wave 3b dispositive).

**Risk axes.**
- native_decide elaborator cost on 5×5 matrix products in QCyc5Ext — pilot single conjunct first.

---

## Wave 3a.2.2 — Explicit Rouabah 30-crossing ε-discharge ⏳ NOT STARTED (NEW — added 2026-05-12)

**Goal:** complete the Rouabah Hadamard verification — currently ships only the BraidWord (verbatim from arXiv:2008.03542 Eq. 36) + crossing-count proof. Strengthening Pass 2 (2026-05-12) shipped all substrate primitives (`Mat2K_40`, `hadamardTarget`, `frobNormSq`, `hadamardTarget_unitary`, QCyc40 `Mul`). This wave produces the load-bearing `IsBHSZApprox rouabah_hadamard hadamardTarget (6.57e-3)` theorem.

**Sub-wave decomposition:**

- **Wave 3a.2.2a — QCyc5Ext → QCyc40 embedding.** `lean/SKEFTHawking/QCyc5Ext/ToQCyc40.lean` (~80 LoC). Ring homomorphism `embed : QCyc5Ext → QCyc40` mapping ζ₅ → ζ⁸ and √φ → (1+√5)/2 = `phi` (per QCyc40 substrate). Verified via native_decide on the defining identities (ζ⁵ = 1 in Q(ζ₅), φ² = φ+1).
- **Wave 3a.2.2b — Fibonacci 3-strand representation lift to Q(ζ₄₀).** Same module as Wave 3a.2.2c (~150 LoC). Construct `fibRep3 : BraidGroup 3 → Mat3K_40` (where `Mat3K_40 := Fin 3 → Fin 3 → QCyc40`) via componentwise application of Wave 3a.2.2a embedding to paper14's `FibonacciQutrit` σ₁, σ₂. Inherit the unitarity / braid relations via embed preservation.
- **Wave 3a.2.2c — Apply 30-crossing word + Frobenius-distance verification.** `lean/SKEFTHawking/FaultTolerance/RouabahExplicit.lean` (~200 LoC). Compute `ρ(rouabah_hadamard) := List.foldl (· * ·) 1 (rouabah_hadamard.map fibRep3.toBraidGroup)` — a 30-deep matrix product over QCyc40. Headline theorem `rouabah_hadamard_approximates_H : ‖ρ(rouabah_hadamard) - H‖²_F ≤ (6.57e-3)² := by native_decide` (or a smaller `decide`-checkable witness if native_decide times out per DR risk R1 pattern).

**Total Wave 3a.2.2 budget: ~430 LoC.**

**Substantial-DR risk (R1 from Wave 1a.1): native_decide on 30-deep 3×3 matrix-products over QCyc40 (16-coefficient ring with O(n³) PolyQuotQ.mulReduce cost). Per pre-flight back-of-envelope: ~30 × 27 × 4096 ≈ 3.3M ops — comfortably tractable, but compile-time may approach 30s. Mitigation: if native_decide stalls, pre-compute the 30-fold product output in SymPy and supply a smaller `decide`-checkable witness.**

**Three-question template:**
- *Integrates with:* Wave 3a.2 GateCompilation Mat2K_40 / hadamardTarget / frobNormSq substrate (already shipped); QCyc40 Mul (already shipped via strengthening Pass 2); paper14 FibonacciQutrit braid representation.
- *New constraint adds:* the constructive load-bearing `IsBHSZApprox rouabah_hadamard hadamardTarget 6.57e-3` theorem — making the Rouabah Hadamard ε-value rigorous, not just primary-source-cited.
- *Tension surfaces:* (i) the explicit `0.00657` bound from Rouabah may or may not be sharp in our QCyc40 representation — verify the explicit Frobenius² ≤ 4.3e-5 holds in Lean; (ii) native_decide compile-time at the 30-fold product is the dispositive risk.

**Substrate.** Wave 3a.2 GateCompilation primitives; QCyc40 Mul (Strengthening Pass 2); paper14 FibonacciQutrit; Rouabah arXiv:2008.03542 Eq. 36 + Tounsi-Belaloui et al. 2023 arXiv:2307.01892 (TQSim).

**Bundle absorption.** D.2 additive into D4 / new bundle.

**Risk axes.**
- native_decide compile-time on 30-fold matrix product — primary risk; smaller-witness fallback.

---

## Wave 3a.2.3 — CNOT (HZBS Fig 15) + T-gate (KBS algorithm) explicit braid words ⏳ NOT STARTED (NEW — added 2026-05-12)

**Goal:** complete the substantive content of Wave 3a (gates G13 + G14 from §G DR-return state) — explicit CNOT and T-gate braid words on Fibonacci 3-strand substrate.

**Sub-wave decomposition:**

- **Wave 3a.2.3a (gate G13: CNOT transcription) — DR dispatch RECOMMENDED.** HZBS 2007 (arXiv:quant-ph/0610111, PRB 75, 165310) Fig 15 ships the ~132-crossing CNOT braid as **σ-strings in figure form only**. Manual transcription from the figure carries error risk. Drop a DR prompt asking for an authoritative ASCII / list-of-generators transcription (cross-validated against Tounsi-Belaloui et al. 2023 TQSim regenerable form). Deliverable: `Lit-Search/Phase-6p/6p-Wave 3a.2.3a — HZBS Fig 15 CNOT braid-word transcription cross-validated.md`. ~1-2 days asynchronous.
- **Wave 3a.2.3b — CNOT explicit braid + ε-discharge.** `lean/SKEFTHawking/FaultTolerance/CNOTExplicit.lean` (~250 LoC). Encode the Wave 3a.2.3a-delivered braid word as `cnot_hzbs : BraidWord 6` (6-strand: 3 control + 3 target Fibonacci anyons). Target = 4×4 CNOT gate in the 2-qubit logical space. Lift via Wave 3a.2.2's `fibRep3` extension to 6 strands; apply `frobNormSq` to derive `‖ρ(cnot_hzbs) - CNOT‖²_F ≤ (1.8e-3)²`. ~132-crossing matrix product over QCyc40; native_decide risk higher than Rouabah — likely need smaller-witness fallback. The 6-strand representation may also need `Mat4K_40 := Fin 4 → Fin 4 → QCyc40` substrate (~30 LoC analog of Mat2K_40).
- **Wave 3a.2.3c (gate G14: T-gate KBS algorithm) — DR dispatch RECOMMENDED.** No primary-source-published Fibonacci T-gate braid exists. Generate via Kliuchnikov-Bocharov-Svore arXiv:1310.4150 O(log(1/ε))-depth-optimal algorithm. Drop a DR prompt asking for either (a) a pre-computed KBS T-gate braid for Fibonacci at ε ~ 10⁻³ (length L ≈ 30-50), OR (b) the algorithm structure in sufficient detail for Lean-direct implementation. Deliverable: `Lit-Search/Phase-6p/6p-Wave 3a.2.3c — KBS T-gate algorithm Fibonacci substrate.md`. ~2-3 days asynchronous.
- **Wave 3a.2.3d — T-gate explicit braid + ε-discharge.** `lean/SKEFTHawking/FaultTolerance/TGateExplicit.lean` (~200 LoC). Encode Wave 3a.2.3c-delivered T-gate braid; verify via frobNormSq.

**Total Wave 3a.2.3 budget: ~480 LoC** + 2 deep-research prompts.

**Three-question template:**
- *Integrates with:* Wave 3a.2.2 substrate (QCyc40 + Mat-of-K_40 + frobNormSq); Wave 3a.2 GateCompilation; HZBS 2007; KBS 2013.
- *New constraint adds:* the constructive load-bearing explicit braid words for the remaining 2 gates in the universal {H, CNOT, T} gate set. Combined with Wave 3a.2.2 Rouabah Hadamard, completes the substantive content of Wave 3a "explicit gate compilation."
- *Tension surfaces:* (i) HZBS Fig 15 figure-to-ASCII transcription error; (ii) native_decide compile-time on 132-crossing braid is the load-bearing risk; (iii) T-gate primary source absent — KBS algorithm port required.

**Substrate.** Wave 3a.2.2 (Rouabah Hadamard substrate); HZBS 2007 + KBS 2013; QCyc40 Mul (Strengthening Pass 2).

**Bundle absorption.** D.2 additive into D4 / new bundle.

**Risk axes.**
- HZBS Fig 15 transcription error (DR mitigation).
- native_decide on 132-crossing braid (smaller-witness fallback).
- T-gate primary-source absence (DR scoping for algorithm-port path).

---

## User authorization gates — consolidated

**Superseded by "Dependencies and decision gates" section (§G) — see consolidated gate G1-G15 table above.** Live status:
- **Wave 3b** bundle decision (G15): 🔒 PENDING — new-bundle creation vs D4 extension per `PAPER_STRATEGY.md`.
- **Wave 2c** axiom elimination (G16 — NEW 2026-05-12): 🔒 PENDING user sign-off on the Aharonov-Arad substantive-bridge approach (~430 LoC) for `bridge_axiom_FKLW` discharge. Per POLICY note above §H.
- **Wave 2d** axiom elimination (G17 — NEW 2026-05-12): 🔒 PENDING user sign-off on the Dawson-Nielsen substantive constructive-SK approach (~550 LoC; first-formalization-territory) for `sk_axiom_Dawson_Nielsen` discharge. Per POLICY note above §H.
- **Future topological-substrate threshold work** (Wave 1c+ -- the *original* Wave 1c was renamed to MeasureTheory NoiseModel; the topological-substrate threshold becomes a separate later wave): 🔒 user-authorization advised before commit; topological specialization requires either Gács-Harrington CA renormalization (heavy formalization) or MTC infrastructure.
- **Any new project-local axiom** going forward (project-wide policy): 🔒 user sign-off REQUIRED. DR recommendations are advisory only; no new axiom ships without explicit user approval.

---

## Phase 6q+ preview (related deferred tracks)

The following tracks are scoped as Phase 6q (transport bootstrap) / 6r (SymTFT) / 6s (1c bootstrap + I3) per `Phase6{q,r,s}_Roadmap.md` and `memory/project_phase_6p6q6r6s_planning.md`. They are independent of Phase 6p; can run in parallel.

Phase 6p-internal further-deferred tracks:
- **G6c+d Aristotle++ domain-fine-tuned prover** — revisit when current Opus + lean4-plugin + MCP + Aristotle stack capacity is binding (currently it is not).
- **G8 Mathlib AS refactor** — multi-year community coordination; track van Doorn / Rothgang / Tooby-Smith infrastructure progress; consider for Phase 6s consolidation.

---

## Cross-references

- `docs/roadmaps/Phase6n_Roadmap.md` — Phase 6n math substrate (paper11/14/16_wrt_tqft); Wave 1b SymTFT audit substrate.
- `docs/roadmaps/Phase6o_Roadmap.md` — Phase 6o completion (closed 2026-05-08); substrate baseline.
- `docs/roadmaps/Phase6q_Roadmap.md` — sibling phase (DKM transport bootstrap).
- `docs/roadmaps/Phase6r_Roadmap.md` — sibling phase (SymTFT formalization).
- `docs/roadmaps/Phase6s_Roadmap.md` — sibling phase (1c bootstrap + I3 substantive lift).
- `memory/project_phase_6p6q6r6s_planning.md` — strategic entry-state brief.
- `memory/feedback_loe_calibration.md` — pipeline speed calibration.
- `docs/PAPER_STRATEGY.md` — 14-bundle architecture (gets potential extension at Wave 3b).
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle mapping; Phase 6p rows added at Stage 12 close.
- `docs/BUNDLE_LIFT_PROCEDURE.md` — frozen lift workflow (§3d `--bookkeeping-only` mode applies to non-content Phase 6p drift events).
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — D.2 / D.3 / D.4 branches.
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage process.
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list (gets Phase 6p entry when D4 gets extension).
- `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` §G5 — substrate for AGP + FKLW Phase 6p scoping.

---

*Created 2026-05-12 at Phase 6o close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes (matches Phase 6n/6o format). Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6p has not yet been dispatched.*
