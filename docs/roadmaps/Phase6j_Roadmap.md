# Phase 6j: Holographic Correspondence Deepening

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **Continuation phase** — natural follow-up to Phase 6c Waves 4–5 (`QECHolographyBridge.lean` shipped 2026-04-27; `RTCasiniHuertaBounds.lean` shipped 2026-04-29). Sources: Phase 6c.5 deferral note ("bulk minimal-surface construction (Lewkowycz-Maldacena replica trick) and full universal-CFT-bound derivation (modular Hamiltonian / replica trick) out-of-scope per roadmap §A"); Phase 6a.3 `BHEntropyMicroscopic.lean` Kaul-Majumdar SU(2)_k closed form; `Lit-Search/Phase-6c/RT and Casini-Huerta as External Bounds.md` (round 1 deep research).*

**Trigger condition (light gate):** Phase 6c Waves 4–5 must be SHIPPED with their tracked-hypothesis bundles `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` consumable as inputs. Wave 1 of Phase 6j *replaces* `H_RT_Formula_Valid` with a derived theorem; Wave 2 *replaces* `H_CasiniHuerta_Bound_Valid` similarly. Tracked-hypothesis bundles in `RTCasiniHuertaBounds.lean` are not deleted but get a downstream consumer module that re-exports them as theorems.

**Status (2026-04-28):** Phase 6c.4 + 6c.5 SHIPPED. Phase 6j is **OPEN** for Wave 1 dispatch on user authorization.

**Entry state (2026-04-28 Inventory_Index snapshot):** ~187 active modules, ~4,385 theorems, 0 sorry, 1 axiom (`gapped_interface_axiom`). Phase 6c CLOSED at 5 of 5 waves shipped (W2 EWBaryogenesisChiralityWall is on the Phase 6c.W2-followup track, not blocking 6j).

**Anchors carried forward into Phase 6j:**
- `BHEntropyMicroscopic.lean` (Phase 6a.3) — Kaul-Majumdar SU(2)_k closed form; horizon-MTC tracked hypothesis `H_HorizonBoundaryCondition`; abelian-MTC F2 falsifier; bridge from MTC counts to BH entropy (Outcome-3 tracked-hypothesis mode).
- `QECHolographyBridge.lean` (Phase 6c.4) — Hayden-Preskill structural QEC; code distance `d_C := log d_max`; scrambling time `t_scr := log D²`; Fibonacci/Ising/SU(3)_2 concrete D² values.
- `RTCasiniHuertaBounds.lean` (Phase 6c.5) — knife-edge biconditional `rt_eq_kaulMajumdar_iff_trivial_reduced_area`; tracked Props `H_RT_Formula_Valid` + `H_CasiniHuerta_Bound_Valid`.
- `MugerCenter.lean` + `D2Formula.lean` (Phase 5p) — global dimension D² = Σ (dim V)² formula; Frobenius-Perron dimensions as fusion-matrix eigenvalues.
- `IsingBraiding.lean`, `FibonacciMTC.lean`, `SU3kFusion.lean` — concrete MTC instances usable as substrate witnesses.

**Thesis.** The horizon-MTC substrate established in Phase 6a Wave 3 + the Hayden-Preskill QEC bridge in Phase 6c Wave 4 + the knife-edge RT/Kaul-Majumdar biconditional in Phase 6c Wave 5 constitute structural infrastructure where the universal holographic-correspondence formulas (RT minimal surface, Casini-Huerta modular Hamiltonian) are tracked-hypothesis Props. Phase 6j *derives* these formulas on the MTC substrate where the project's tools apply — promoting two tracked-hypothesis Props to derived theorems and producing the project's first holographic-correspondence theorem from microscopy. Wave 4 sharpens the scrambling-time bound from structural ("≥ log D²") to quantitative ("= log D² + O(1) for natural-MTC families").

**Correctness-push framing.** Phase 6j's correctness-push anchors are quantitative and substrate-anchored:
1. (Wave 1) RT replica-trick derivation ↔ Phase 6a.3 Kaul-Majumdar `S = A/(4G_N) − (3/2) log(...)` should reproduce the same area-law leading + −3/2 log subleading on the SU(2)_k horizon substrate, OR else identify the precise discrepancy as an explicit non-universality witness (analog of Sen 2013 4D Schwarzschild +1.71 vs Kaul-Majumdar −3/2).
2. (Wave 2) CH modular Hamiltonian `K = −log ρ_A` derived from MTC substrate ↔ free-CFT Casini-Huerta 2009 universal bound; the bound saturates on toric-code (abelian) substrate and is strict on Fibonacci/Ising (non-abelian) substrate — a falsifiable concrete prediction.
3. (Wave 3) Hayden-Preskill exact `t_scr = log D²` ↔ project-internal computation of `D²(Fibonacci) = (5+√5)/2 ≈ 3.618` and `D²(Ising) = 4` should match the universal scrambling-time formula to closed-form precision; deviations identify O(1) subleading corrections from the MTC-specific F-symbol structure.
4. (Wave 4) Holographic c-function `c(t)` from MTC F-symbol data — the Zamolodchikov c-theorem analog under RG flow on the horizon-MTC substrate; falsifiable against `c(IR) ≤ c(UV)` monotonicity.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap (CLAUDE.md §"Mandatory References"):**
>    - `CLAUDE.md`
>    - `SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`
>    - `SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`
>    - `SK_EFT_Hawking/README.MD`
>    - `temporary/working-docs/brainstorm/20260413-context-lean-dev/Lean-Development-Optimization.txt`
>    - `SK_EFT_Hawking/docs/references/Theorm_Proving_Aristotle_Lean.md`
> 2. Read this roadmap end-to-end before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly (not via subagent):**
>    - `lean/SKEFTHawking/BHEntropyMicroscopic.lean` (Phase 6a.3) — the Kaul-Majumdar SU(2)_k closed form is the comparison anchor for Wave 1.
>    - `lean/SKEFTHawking/QECHolographyBridge.lean` (Phase 6c.4) — the QEC structural bounds + scrambling-time consumers.
>    - `lean/SKEFTHawking/RTCasiniHuertaBounds.lean` (Phase 6c.5) — `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` definitions.
>    - `lean/SKEFTHawking/D2Formula.lean` (Phase 5p) — total quantum dimension D² formula.
>    - `lean/SKEFTHawking/IsingBraiding.lean`, `FibonacciMTC.lean`, `SU3kFusion.lean` — concrete substrate instances.
> 4. **Critical deep-research dossiers (read directly, not via subagent):**
>    - `Lit-Search/Phase-6c/RT and Casini-Huerta as External Bounds.md` (round 1) — establishes the universal-bound landscape.
>    - `Lit-Search/Phase-5e/Verlinde Formula and Modular Tensor Categories.md` — Verlinde formula on horizon-MTC substrate.
>    - `Lit-Search/Phase-5p/Muger Center and Modular Tensor Category Modularity.md` — Muger triviality + global dimension.
>    - **NEW deep-research dossier required** (file under `Lit-Search/Tasks/`): `Phase6j_W1_replica_trick_on_MTC.md` — request a deep-research synthesis of Lewkowycz-Maldacena replica trick (JHEP 2013 1308:090) restricted to 2+1D Chern-Simons / WZW boundary CFT, with focus on the SU(2)_k horizon-MTC substrate.
>    - **NEW deep-research dossier required**: `Phase6j_W2_modular_hamiltonian_from_MTC.md` — request synthesis of Casini-Huerta 2009 (CMP 2011 305:281) + Calabrese-Cardy 2004 + Holzhey-Larsen-Wilczek 1994, with focus on extension from free CFT to anyonic / topologically-ordered boundary.
> 5. **Apply the preemptive-strengthening checklist** (CLAUDE.md "Preemptive-strengthening discipline" + WAVE_EXECUTION_PIPELINE.md Stage 3 checklist) before writing each Lean theorem statement.
> 6. **Do not delegate Lean theorem proving to subagents.** Phase 6j has hard categorical-trace machinery (Wave 1 replica trick, Wave 2 modular Hamiltonian); subagents lose tactic-level detail per CLAUDE.md.
> 7. **User authorization gates:** Gate J.1 (Wave 1 start) — confirms scope and the deep-research request for Lewkowycz-Maldacena MTC restriction. Gate J.2 (Wave 2 start) — same for Casini-Huerta MTC extension. Waves 3–4 run autonomously after the W1+W2 deep research returns.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6j:**
- Lewkowycz-Maldacena replica-trick formalization restricted to the horizon-MTC substrate (Chern-Simons / WZW boundary CFT, finite anyon content), promoting Phase 6c.5 `H_RT_Formula_Valid` to a derived theorem on this substrate class.
- Casini-Huerta modular Hamiltonian derivation on MTC substrate (Holzhey-Larsen-Wilczek 1994 universal bound + Calabrese-Cardy 2004 entropy formula extended via anyonic-substrate corrections), promoting `H_CasiniHuerta_Bound_Valid` to a derived theorem.
- Hayden-Preskill quantitative scrambling-time `t_scr = log D² + O(1)` for natural-MTC families (Fibonacci, Ising, SU(N)_k), with explicit computation of the O(1) subleading correction from F-symbol data.
- Holographic c-function `c(t)` as a Zamolodchikov-c analog under RG flow on the horizon-MTC substrate; falsifiability against `c_IR ≤ c_UV` (Wave 4).
- Bridge theorems linking the new derived RT / CH formulas back to Phase 6a.3 Kaul-Majumdar entropy + Phase 6c.4 HP code-distance bounds.
- One paper (target: PRD or JHEP): "Holographic Correspondence on the Horizon-MTC Substrate."

**OUT OF SCOPE for Phase 6j:**
- Bulk classical-gravity geometry (Schwarzschild, Kerr metrics) — Phase 6f.4 territory; this phase operates on the boundary CFT / horizon-MTC side only.
- AdS/CFT in arbitrary dimensions — Phase 6j restricts to 2+1D Chern-Simons / 1+1D rational CFT boundary.
- Tensor-network models (MERA, holographic codes) — adjacent literature; Phase 6j does not formalize these.
- Black-hole information paradox direct address — structurally adjacent (Hayden-Preskill is a partial answer); Phase 6j sharpens the scrambling-time bound but does not derive page curves.
- Generalized holographic c-functions in d > 2 (Wave 4 restricts to 1+1D boundary CFT).

**Phase 6c relationship:** Phase 6j is Phase 6c.4 + 6c.5's natural deepening. Phase 6c shipped the *structural* bounds; Phase 6j produces the *derived* formulas on the MTC substrate where the project's quantum-group + MTC + Verlinde infrastructure applies. The Phase 6c tracked-hypothesis Props are not retired — they are re-exported as theorems-on-substrate via Phase 6j Wave 1+Wave 2 consumer modules.

**Phase 6a relationship:** Phase 6a.3 Kaul-Majumdar SU(2)_k closed form is the load-bearing comparison anchor. Phase 6j Wave 1 is *required* to reproduce or precisely identify the discrepancy.

**Phase 5p relationship:** `MugerCenter.lean` + `D2Formula.lean` provide the total-quantum-dimension infrastructure that Wave 3 (HP scrambling) and Wave 4 (c-function) consume.

---

## Wave 1 — `RTReplicaTrickOnMTC.lean` [6j.1] [Pipeline: Stages 1–13]

**Goal.** Formalize the Lewkowycz-Maldacena replica trick (JHEP 1308:090, 2013) restricted to a 2+1D Chern-Simons / WZW boundary CFT realizing a fixed Modular Tensor Category C. Derive the Ryu-Takayanagi formula `S(A) = Area(γ_A) / (4 G_N)` on this substrate, recovering the Kaul-Majumdar SU(2)_k closed form (Phase 6a.3) as the SU(2)_k specialization. Promote `H_RT_Formula_Valid` (Phase 6c.5 tracked hypothesis) to a derived theorem on the MTC substrate.

**Prerequisites:**
- Deep-research dossier `Lit-Search/Tasks/Phase6j_W1_replica_trick_on_MTC.md` returned (filed at user authorization Gate J.1; expected ~1 week turnaround per CLAUDE.md asynchronous protocol).
- Phase 6a.3 `BHEntropyMicroscopic.lean` Kaul-Majumdar closed form available as comparison.
- Phase 5p `MugerCenter.lean` + `D2Formula.lean` for global-dimension manipulation.

**Module structure:**
- `lean/SKEFTHawking/RTReplicaTrickOnMTC.lean` — new module, ~30 substantive theorems target, 0 sorry, 0 new axioms.
- `src/holography/replica_trick.py` — numerical replica computation for Fibonacci + Ising + SU(2)_k k=1,2,3 substrates; reproduces Kaul-Majumdar closed form numerically.
- `tests/test_replica_trick.py` — golden-identity tests vs Kaul-Majumdar; 18+ tests target.
- `figures/fig_rt_replica_substrate_comparison.{png,html}` — RT(MTC) vs Kaul-Majumdar(SU(2)_k) for k = 1..5; non-universality witnesses for non-SU(2)_k MTCs.

**Headline theorems:**
1. `replica_partition_function_n_sheeted_factorizes` — n-sheeted replica partition function on MTC substrate factorizes as `Z_n = (Σ_a S_{0a}^{2−2n})` where S is the modular S-matrix (Verlinde formula consumer).
2. `entanglement_entropy_from_replica_limit` — `S(A) = lim_{n→1} (1/(1−n)) log Z_n` derives entanglement entropy as the n→1 analytic continuation.
3. `rt_formula_on_mtc_substrate` — derived theorem replacing `H_RT_Formula_Valid`: `S(A) = Area(γ_A) / (4 G_N) + O(c_top)` where the O(c_top) correction depends on the substrate's chiral central charge `c_− = (c/12) · (mod 24)`.
4. `rt_recovers_kaulMajumdar_on_SU2k` — correctness-push: on SU(2)_k substrate, RT formula reproduces `S = A/(4 G_N) − (3/2) log(A/(4 G_N)) + c_0` with the −3/2 coefficient coming from Verlinde's S-matrix Gaussian-saddle limit.
5. `rt_falsifies_abelian_mtc` — abelian MTC (toric code, ℤ_n) gives RT correction = 0 (constant area-law only); reproduces Phase 6a.3 F2 falsifier.
6. `rt_subleading_correction_on_fibonacci` — concrete witness: Fibonacci-substrate RT correction is `(c_top/24) · log(A/(4 G_N))` with `c_top(Fib) = 14/5`, falsifiable against future numerical lattice work.

**Strengthening checklist (preemptive):**
- (P2 bundle redundancy): does each theorem add a substantive conjunct, or is `rt_recovers_kaulMajumdar_on_SU2k` redundant given `rt_formula_on_mtc_substrate`? — answer: substantive, since the SU(2)_k specialization is the falsifiability anchor (the universal formula could match other MTCs but disagree at SU(2)_k).
- (Quantitative-content): every theorem about a coefficient must have `norm_num`-backed comparison to Kaul-Majumdar (target precision: closed-form symbolic, then `decide` after rationalization).
- (P5 trivial-discharge): `rt_subleading_correction_on_fibonacci` could collapse to `0 = 0` if `c_top(Fib)` were defined as the discrepancy — instead, derive `c_top(Fib) = 14/5` from the Verlinde S-matrix independently and check that `S(A)_RT − S(A)_KaulMajumdar` matches.

**Aristotle (Stage 4):** No expected sorry gaps if Wave 1 ships clean. The replica-trick computation is symbolic; the harder content (Verlinde formula, S-matrix unitarity) is already shipped in Phase 5e/5p.

**Stage 13 anchors:**
- Lewkowycz, Maldacena, JHEP 1308 090 (2013), arXiv:1304.4926 — primary source for replica-trick gravitational-entropy derivation.
- Kaul, Majumdar, gr-qc/0002040 — primary source for SU(2)_k Verlinde + −3/2 log derivation (already cached for Phase 6a.3).
- Verlinde, Nucl. Phys. B 300, 360 (1988) — primary source for S-matrix fusion-rule formula (cached for Phase 5e).
- Faulkner, Lewkowycz, Maldacena, JHEP 1311 074 (2013), arXiv:1307.2892 — quantum corrections to RT (subleading log term origin).

**Deliverables.** `RTReplicaTrickOnMTC.lean`; numerical replica module; figure suite; section in flagship paper.

---

## Wave 2 — `CasiniHuertaModularHamiltonianMTC.lean` [6j.2] [Pipeline: Stages 1–13]

**Goal.** Derive the Casini-Huerta universal entropy bound via the modular Hamiltonian `K_A = −log ρ_A` for an interval / disk subregion in a 1+1D / 2+1D rational CFT realizing a fixed MTC. Promote `H_CasiniHuerta_Bound_Valid` (Phase 6c.5 tracked hypothesis) to a derived theorem on this substrate. Establish the falsifiable concrete prediction: the bound saturates on abelian MTCs (toric code, ℤ_n) and is strict on non-abelian MTCs (Fibonacci, Ising), with closed-form expressions for the strict-bound tightness.

**Prerequisites:**
- Deep-research dossier `Lit-Search/Tasks/Phase6j_W2_modular_hamiltonian_from_MTC.md` returned (filed at user authorization Gate J.2).
- Wave 1 `RTReplicaTrickOnMTC.lean` SHIPPED (Wave 2 consumes the replica-trick infrastructure for the modular Hamiltonian construction).
- `Lit-Search/Phase-5e/Verlinde Formula...md` for Verlinde-formula-derived modular Hamiltonian.

**Module structure:**
- `lean/SKEFTHawking/CasiniHuertaModularHamiltonianMTC.lean` — new module, ~22 substantive theorems target, 0 sorry, 0 new axioms.
- `src/holography/modular_hamiltonian.py` — numerical modular-Hamiltonian computation for Fibonacci + Ising + toric-code substrates; reproduces Holzhey-Larsen-Wilczek 1994 universal bound numerically.
- `tests/test_modular_hamiltonian.py` — saturation test (abelian-MTC) + strict-bound test (non-abelian-MTC); 14+ tests.
- `figures/fig_ch_bound_saturation_abelian_strict_nonabelian.{png,html}` — bound saturation across MTC families.

**Headline theorems:**
1. `modular_hamiltonian_from_density_matrix` — `K_A = −log ρ_A` is well-defined for the boundary-CFT vacuum reduced to interval A; reduces to local boost generator in CFT vacuum.
2. `casini_huerta_bound_on_mtc_substrate` — derived theorem replacing `H_CasiniHuerta_Bound_Valid`: `S(A) ≤ (c_LR / 6) · log(L_A / ε)` where `c_LR = c_L + c_R` is the total central charge, recovering Holzhey-Larsen-Wilczek 1994.
3. `bound_saturates_on_abelian_mtc` — toric code, ℤ_n: bound is saturated (no strict inequality); concrete witness via `D²(toric) = 4` and `c_L = c_R = 1`.
4. `bound_strict_on_fibonacci` — Fibonacci substrate: bound is strict, tightness `S(A) − (c_LR/6) log(L_A/ε) = c_top · O(1)` where `c_top(Fib) = 14/5`.
5. `bound_strict_on_ising` — Ising substrate: bound is strict, tightness `S(A) − (c_LR/6) log(L_A/ε) = c_top · O(1)` where `c_top(Ising) = 1/2`.
6. `ch_bridge_to_rt_on_mtc` — cross-wave bridge: `S(A) = Area(γ_A) / (4 G_N) + Δ_CH(A)` where `Δ_CH(A)` is the Casini-Huerta strict-bound correction (zero on abelian MTC, non-zero on non-abelian MTC).

**Strengthening checklist:**
- (P2 bundle redundancy): drop `bound_strict_on_ising` if `bound_strict_on_fibonacci` already demonstrates strict-bound — answer: keep both, since Ising ↔ SU(2)_2 ↔ free Majorana CFT is the closest connection to the standard Casini-Huerta 2009 free-CFT result (cross-validation), while Fibonacci ↔ G_2 1 ↔ no free-CFT analog (genuinely interacting witness).
- (Numerical content): `c_top(Fib) = 14/5` and `c_top(Ising) = 1/2` should be `norm_num`-derivable from the F-symbol data already in `IsingBraiding.lean` + `FibonacciMTC.lean`.

**Aristotle (Stage 4):** Modular-Hamiltonian construction is technical; expected 1–2 sorry gaps for `density_matrix_logarithm_well_defined` requiring specific operator-algebraic infrastructure. Decompose into ≤12-term sub-lemmas before submitting.

**Stage 13 anchors:**
- Casini, Huerta, CMP 305:281 (2011), arXiv:0901.0016 — primary source for the universal-bound formulation.
- Holzhey, Larsen, Wilczek, Nucl. Phys. B 424, 443 (1994) — primary source for the c-log universal entropy.
- Calabrese, Cardy, J. Stat. Mech. P06002 (2004) — primary source for entanglement-entropy in CFT.

**Deliverables.** `CasiniHuertaModularHamiltonianMTC.lean`; numerical modular-Hamiltonian module; figure suite; section in flagship paper.

---

## Wave 3 — `ScramblingTimeQuantitative.lean` [6j.3] [Pipeline: Stages 1–13]

**Goal.** Sharpen the Hayden-Preskill scrambling-time bound from Phase 6c.4's structural `t_scr ≥ log D²` to the quantitative `t_scr = log D² + Δ_F(C)` where `Δ_F(C)` is an explicit O(1) subleading correction depending on the substrate MTC's F-symbol data. Compute closed-form `Δ_F` for Fibonacci, Ising, and SU(N)_k families; verify against a project-internal Heisenberg-evolution numerical benchmark.

**Prerequisites:**
- Phase 6c.4 `QECHolographyBridge.lean` shipped (consumes `t_scr := log D²`).
- Phase 5p `D2Formula.lean` shipped (consumes total-quantum-dimension formula).
- Phase 6j Waves 1–2 SHIPPED (consumes `RTReplicaTrickOnMTC` for OTOC computation; consumes `CasiniHuertaModularHamiltonianMTC` for entropy-evolution comparison).

**Module structure:**
- `lean/SKEFTHawking/ScramblingTimeQuantitative.lean` — new module, ~14 substantive theorems target, 0 sorry, 0 new axioms.
- `src/holography/scrambling_time.py` — numerical OTOC (out-of-time-ordered correlator) computation for Fibonacci + Ising + SU(2)_k k=1,2,3,4,5 + SU(3)_k k=1,2; closed-form `Δ_F` extraction.
- `tests/test_scrambling_time.py` — closed-form `Δ_F` vs numerical OTOC; 12+ tests.
- `figures/fig_scrambling_time_otoc_substrate.{png,html}` — t_scr vs log D² for natural-MTC families with subleading correction visible.

**Headline theorems:**
1. `scrambling_time_quantitative_form` — `t_scr(C) = log D²(C) + Δ_F(C) + o(1)` where `Δ_F(C)` is closed-form derivable from F-symbol data.
2. `delta_F_fibonacci_closed_form` — `Δ_F(Fib) = log φ` where `φ = (1+√5)/2`, derived from Fibonacci F-symbol structure.
3. `delta_F_ising_closed_form` — `Δ_F(Ising) = (1/2) log 2`, derived from Ising F-symbol structure.
4. `delta_F_su2k_general` — `Δ_F(SU(2)_k) = log(d_max(k))` where `d_max(k) = 2 cos(π/(k+2))` is the maximal quantum dimension.
5. `scrambling_time_bridge_to_qec_holography` — cross-wave bridge: tightens `QECHolographyBridge.code_distance_scaling_iff_admissible_class` with the closed-form `t_scr` value, retiring the `O(1)` ambiguity in HP scrambling-time exposition.
6. `scrambling_time_falsifies_abelian_mtc_universality` — abelian-MTC: `Δ_F = 0` (no F-symbol non-triviality to contribute); the structural bound is saturated. Witness: toric code `Δ_F(toric) = 0`.

**Strengthening checklist:**
- (P3 trivial-multiplication): does `delta_F_fibonacci_closed_form` reduce to `Δ_F = log φ` as a definitional unfolding? — no, since `Δ_F` is defined operationally via the OTOC asymptote and `log φ` is the closed-form value computed from F-symbols (substantive identification).
- (Quantitative-content): every closed-form `Δ_F` must `decide`/`norm_num` against the numerical OTOC benchmark.

**Stage 13 anchors:**
- Hayden, Preskill, JHEP 0709 120 (2007), arXiv:0708.4025 — primary source for scrambling-time conjecture.
- Sekino, Susskind, JHEP 0810 065 (2008), arXiv:0808.2096 — `t_scr ≈ log D²` first explicit form.
- Maldacena, Shenker, Stanford, JHEP 1608 106 (2016), arXiv:1503.01409 — chaos bound + scrambling-time refinement.

**Deliverables.** `ScramblingTimeQuantitative.lean`; OTOC numerical module; figure suite; section in flagship paper.

---

## Wave 4 — `HolographicCFunctionMTC.lean` [6j.4] [Pipeline: Stages 1–13]

**Goal.** Construct the holographic c-function `c(t)` for RG flows on the horizon-MTC substrate as a Zamolodchikov-c analog (1+1D boundary CFT). Prove monotonicity `c(IR) ≤ c(UV)` under unitary RG flow; identify substrate cases where the bound is saturated vs strict; produce the project's first formally verified Zamolodchikov-c-theorem analog.

**Prerequisites:**
- Phase 6j Waves 1–3 SHIPPED.
- Phase 5e `IsingBraiding.lean` + `FibonacciMTC.lean` for concrete c-function evaluation.
- Phase 5p `D2Formula.lean` + `MugerCenter.lean` for Frobenius-Perron dimension extraction.

**Module structure:**
- `lean/SKEFTHawking/HolographicCFunctionMTC.lean` — new module, ~16 substantive theorems target, 0 sorry, 0 new axioms.
- `src/holography/c_function.py` — numerical c-function under RG flow Fibonacci → trivial, Ising → trivial, SU(2)_k → SU(2)_{k−1} (level-rank-style flow).
- `tests/test_c_function.py` — c-monotonicity tests; 10+ tests.
- `figures/fig_c_function_rg_flow_mtc.{png,html}` — c(t) trajectories for natural-MTC RG flows.

**Headline theorems:**
1. `c_function_definition_on_mtc_substrate` — `c(C) = ∑_a (d_a)² · log(d_a)² / D²(C)` is well-defined for any unitary MTC (Frobenius-Perron entropy of the fusion category).
2. `c_function_monotonic_under_anyon_condensation` — anyon-condensation RG flow `C → C/A` (for A a connected etale algebra in C) satisfies `c(C/A) ≤ c(C)`; first machine-verified Zamolodchikov-c-theorem analog on MTC substrate.
3. `c_function_recovers_zamolodchikov_on_minimal_models` — minimal-model substrate `M(p, q)` recovers `c = 1 − 6(p−q)²/(pq)`, reproducing Zamolodchikov 1986.
4. `c_function_saturates_on_abelian_mtc` — abelian MTC: `c = log D²(C)` saturates; no strict-monotonicity content.
5. `c_function_strict_on_fibonacci_to_trivial` — Fibonacci → trivial flow: `c(Fib) − c(triv) = log φ²` strictly positive; concrete witness.
6. `c_function_bridge_to_rt_replica_trick` — cross-wave bridge: connects `c(C)` to the chiral-central-charge subleading RT correction from Wave 1.

**Strengthening checklist:**
- (P5 structural-tautology): is `c_function_strict_on_fibonacci_to_trivial` falsifiable? — yes, the numerical c-value can be checked against the F-symbol-derived closed form; if they disagreed, the theorem would fail.
- (Quantitative): every concrete c-value must be `norm_num`-derivable from the existing F-symbol modules.

**Stage 13 anchors:**
- Zamolodchikov, JETP Lett. 43, 730 (1986) — primary source for c-theorem.
- Friedan, Konechny, J. Phys. A 37, 8651 (2004), arXiv:hep-th/0312197 — boundary g-theorem (analog).
- Affleck, Ludwig, PRL 67, 161 (1991) — anyon-condensation entropy on MTC substrate.

**Deliverables.** `HolographicCFunctionMTC.lean`; c-function numerical module; figure suite; section in flagship paper.

---

## Paper deliverable

**Paper 42** (target: PRD or JHEP): "Holographic Correspondence on the Horizon-MTC Substrate: Replica Trick, Modular Hamiltonian, Scrambling Time, and the c-Function." 8–12 pages. Anchors:
- §2 Replica trick on MTC substrate (Wave 1)
- §3 Casini-Huerta modular Hamiltonian (Wave 2)
- §4 Quantitative scrambling time (Wave 3)
- §5 Holographic c-function (Wave 4)
- §6 Cross-bridges to Phase 6a.3 BH entropy + Phase 6c.4 QEC + Phase 6c.5 RT/CH structural bounds
- §7 Falsifiable predictions: abelian-MTC saturation witnesses + non-abelian strict-bound witnesses

**Submission readiness:** target Stage 13 closure ~6–8 weeks post-Wave 4.

---

## Cross-phase impact

- **Phase 6c.5** `RTCasiniHuertaBounds.lean` — Wave 1 + Wave 2 of Phase 6j re-export the previously tracked-hypothesis Props as derived theorems on the MTC substrate. The Phase 6c.5 module is *not* deleted; its tracked hypotheses become substrate-conditional theorems.
- **Phase 6a.3** `BHEntropyMicroscopic.lean` — Wave 1 of Phase 6j *must* reproduce the Kaul-Majumdar SU(2)_k closed form. If the replica-trick derivation gives a different log coefficient on SU(2)_k, this is a research-grade discrepancy that triggers a Phase 6j.5 reconciliation wave.
- **Phase 6c.4** `QECHolographyBridge.lean` — Wave 3 of Phase 6j tightens the structural HP scrambling-time bound to a quantitative formula; Phase 6c.4 module benefits from a downstream consumer addition.
- **Phase 5p** `D2Formula.lean` + `MugerCenter.lean` — Phase 6j Waves 3–4 are heavy consumers; this validates Phase 5p infrastructure as load-bearing for downstream holographic theorems.

---

## Total LOE estimate

- Wave 1 (RT replica trick): 4–6 PM Lean + 2–3 PM derivation/numerical
- Wave 2 (CH modular Hamiltonian): 3–5 PM Lean + 2 PM derivation/numerical
- Wave 3 (scrambling time): 2–3 PM Lean + 1 PM numerical
- Wave 4 (c-function): 3–4 PM Lean + 1 PM numerical
- Paper 42 drafting: 2–3 PM
- **Total: 17–25 PM** (~4–6 months at full intensity)

---

*Last updated: 2026-04-28. Status: OPEN, awaiting Wave 1 deep-research dispatch + user authorization Gate J.1.*
