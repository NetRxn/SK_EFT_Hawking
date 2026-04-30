# Phase 6j: Holographic Correspondence Deepening

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **Continuation phase** — natural follow-up to Phase 6c Waves 4–5 (`QECHolographyBridge.lean` shipped 2026-04-27; `RTCasiniHuertaBounds.lean` shipped 2026-04-29). Sources: Phase 6c.5 deferral note ("bulk minimal-surface construction (Lewkowycz-Maldacena replica trick) and full universal-CFT-bound derivation (modular Hamiltonian / replica trick) out-of-scope per roadmap §A"); Phase 6a.3 `BHEntropyMicroscopic.lean` Kaul-Majumdar SU(2)_k closed form; `Lit-Search/Phase-6c/RT and Casini-Huerta as External Bounds.md` (round 1 deep research).*

**Trigger condition (light gate):** Phase 6c Waves 4–5 must be SHIPPED with their tracked-hypothesis bundles `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` consumable as inputs. Wave 1 of Phase 6j *replaces* `H_RT_Formula_Valid` with a derived theorem; Wave 2 *replaces* `H_CasiniHuerta_Bound_Valid` similarly. Tracked-hypothesis bundles in `RTCasiniHuertaBounds.lean` are not deleted but get a downstream consumer module that re-exports them as theorems.

**Status (2026-04-30 final + W3+W4 dossier integration):** **Phase 6j FULLY CLOSED across all 4 waves at structural-substantive scope (Stages 1-5) + W3+W4 dossier integration §9 SHIPPED.** 4 modules / **60 substantive theorems** / 9 defs / 4 structures / **~1810 LOC** / 0 sorry / 0 new axioms / library 8494 jobs PASS clean / 2 retroactive cuts (W4 P5 trivial projections). All 4 waves shipped end-to-end with hypothesis-bundle architecture: `IsolatedHorizonHypotheses` (W1) / `CHEntropyHypotheses` (W2) / `QuantitativeScramblingHypotheses` (W3) / `HolographicCFunctionHypotheses` (W4). Each wave promotes a Phase 6c tracked-Prop or structural bound to a universal-under-hypothesis-bundle theorem. Four dossier-correction patterns observed (W1: bare-LM gives only `−(1/2) log D²`, not Kaul-Majumdar; W2: leading log saturates on ANY MTC, not just abelian; W3: closed-form `Δ_F` values not primary-source-cited as scrambling-time corrections — they are entanglement-jump constants; W4: roadmap c-function formula algebraically inconsistent + `log φ²` Fibonacci witness arithmetically false + minimal-model Virasoro recovery structurally wrong). **W3+W4 deep-research dossiers integrated** as new §9 sections in `ScramblingTimeQuantitative.lean` (+5 thms, +1 def: `entanglement_jump_log_sqrt_two_eq_half_log_two`, `fibonacciHorizonBC_globalDimSq_eq_one_plus_goldenRatio_sq`, `fundamentalQuantumDim_SU2k` def + 3 numerical/correction witnesses including the structural `√3 < 2` falsifier of the SU(2)_k formula error) and `HolographicCFunctionMTC.lean` (+4 thms, +1 def: `cLogTotal` named def + `cLogTotal_fibonacci` corrected closed form `log((5+√5)/2)` + `cLogTotal_trivialAbelian` + `cLogTotal_satisfies_HCF` + dossier-corrective inequality `cLogTotal_fibonacci_ne_log_goldenRatio_sq`). Stages 6-13 (cross-layer Python + figures + Stage 13 review + paper bundle assembly into D3 §13.5 + I1 sidebar per Phase 6i Wave 7 paper-bundle architecture) deferred to a future Phase 6j paper-bundle preparation cycle. See `memory:project_phase6j_full_close.md` + `memory:project_phase6j_w3_post_dossier.md` + `memory:project_phase6j_w4_post_dossier.md`.

**Prior status (2026-04-30 mid):** Wave 1 SHIPPED end-to-end at Stages 1-5. Wave 2 OPEN for Gate J.2 dispatch.

**Prior status (2026-04-28):** Phase 6c.4 + 6c.5 SHIPPED. Phase 6j is **OPEN** for Wave 1 dispatch on user authorization.

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
> 7. **User authorization gates:** Gate J.1 (Wave 1 start) ✅ APPROVED 2026-04-30. Gate J.2 (Wave 2 start) ✅ APPROVED 2026-04-30. Gate J.3 (Wave 3 start) ✅ APPROVED 2026-04-30. Gate J.4 (Wave 4 start) ✅ APPROVED 2026-04-30. All gates approved per user direction "you can update any user authorization between waves to approved as long as it's internal work". **Future Gate J.5 (post-dossier W3+W4 integration)**: APPROVED in advance for internal work — when dossiers return, post-compact agent should pick up TODOs at "Post-Deep-Research TODOs" section below without further authorization.
>
> 8. **Post-compact agent quick-start** (when picking up Phase 6j post-deep-research):
>    - Read this roadmap end-to-end (especially "Phase 6j FULLY CLOSED" + "Post-Deep-Research TODOs" sections at the bottom).
>    - Read `memory:project_phase6j_full_close.md` for full Phase 6j context.
>    - Read `memory:feedback_post_wave_strengthening_audit.md` for Pattern #1-#8 audit discipline.
>    - Check `Lit-Search/Phase-6j/` for new dossier files (named `6j-Quantitative Scrambling Time on MTC Substrate.md` and `6j-Holographic c-Function on MTC Substrate.md`).
>    - If dossiers present → execute "W3 TODO list (post-dossier)" or "W4 TODO list (post-dossier)" per "Post-Deep-Research TODOs" section.
>    - If dossiers not yet returned → check `Lit-Search/Tasks/submitted/Phase6j_W3_*.md` and `Phase6j_W4_*.md` (filed 2026-04-30 ~13:50, expected return ~14:10); report status to user.

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

## Wave 1 — `RTReplicaTrickOnMTC.lean` [6j.1] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; Stages 6–13 deferred to Phase 6j paper-bundle assembly]

**STATUS: ✅ SHIPPED 2026-04-30. Lean module + library build verification (Stages 1-5) complete.** 17 substantive thms / 4 noncomputable defs / 1 structure / 0 sorry / 0 new axioms / library 8491 jobs PASS clean. Cross-layer Python + figures + paper section deferred to full-pipeline cycle when Phase 6j paper bundle (D3 §13.5 + I1 sidebar) is assembled. See `memory:project_phase6j_w1_shipped.md`. **Critical dossier finding (verdict B) drove a re-scoping** from the original "promote H_RT_Formula_Valid to derived theorem" to a more honest "two-step promotion": (i) clean unconditional `topologicalEntanglementEntropy` theorem on any MTC carrier giving the Kitaev-Preskill `−(1/2) log D²` (the actual bare-LM output on pure-CS substrate); (ii) conditional Kaul-Majumdar derivation under explicit `IsolatedHorizonHypotheses` (LQG inputs that bare-LM does NOT supply). Phase 6c.5 `H_RT_Formula_Valid` NOT retired — promoted to universal-under-IH falsifier `isolatedHorizon_violates_H_RT`.

**Goal.** Formalize the Lewkowycz-Maldacena replica trick (JHEP 1308:090, 2013) restricted to a 2+1D Chern-Simons / WZW boundary CFT realizing a fixed Modular Tensor Category C. Derive the Ryu-Takayanagi formula `S(A) = Area(γ_A) / (4 G_N)` on this substrate, recovering the Kaul-Majumdar SU(2)_k closed form (Phase 6a.3) as the SU(2)_k specialization. Promote `H_RT_Formula_Valid` (Phase 6c.5 tracked hypothesis) to a derived theorem on the MTC substrate.

**Prerequisites (all met 2026-04-30):**
- ✅ Deep-research dossier filed at `Lit-Search/Phase-6j/6j-Lewkowycz–Maldacena Replica Trick on the Horizon-MTC Substrate.md` (returned with verdict (B) DISAGREE BY KNOWN AMOUNT; structural caveat re-scoped Wave 1 to two-step promotion).
- ✅ Phase 6a.3 `BHEntropyMicroscopic.lean` Kaul-Majumdar closed form `kaulMajumdarS` consumed.
- ✅ Phase 6a.3 `HorizonMTCBC` carrier consumed (replaces planned `MTC` type).
- ✅ Gate J.1 user authorization: explicit "work through it" 2026-04-30 + auto-mode.

**Module structure (as shipped):**
- ✅ `lean/SKEFTHawking/RTReplicaTrickOnMTC.lean` — 544 LOC, 17 substantive theorems shipped (target was ~30 — re-scoping to honest content reduced count without losing Wave 1 deliverables).
- `src/holography/replica_trick.py` — numerical replica computation for Fibonacci + Ising + SU(2)_k k=1,2,3 substrates; reproduces Kaul-Majumdar closed form numerically.
- `tests/test_replica_trick.py` — golden-identity tests vs Kaul-Majumdar; 18+ tests target.
- `figures/fig_rt_replica_substrate_comparison.{png,html}` — RT(MTC) vs Kaul-Majumdar(SU(2)_k) for k = 1..5; non-universality witnesses for non-SU(2)_k MTCs.

**Headline theorems (SHIPPED — re-scoped per dossier verdict (B) two-step promotion):**
1. ✅ `topologicalEntanglementEntropy` (def) + `topologicalEntanglementEntropy_neg_iff` — bare LM operational result `−(1/2) log D²` on any `HorizonMTCBC` carrier (Kitaev-Preskill 2006; biconditional separates trivial D²=1 from non-trivial D²>1 topological order).
2. ✅ `rt_entropy_toric_code` / `rt_entropy_ising` / `rt_entropy_fibonacci` — three concrete witnesses with closed-form algebraic constants `−log 2 / −log 2 / −(1/2) log((5+√5)/2)`.
3. ✅ `topologicalEntanglementEntropy_eq_of_globalDimSq_eq` + `rt_entropy_toric_eq_ising` — Dong-Liu-Wen 2010 vacuum-sector ambiguity (abstract + concrete consumer per Pattern #8).
4. ✅ `IsolatedHorizonHypotheses` (struct) + `rt_log_coefficient_under_IH` — under IH, the `−3/2` log coefficient (Basu-Kaul-Majumdar 2010 §3 decomposition) is extracted via `rw + ring`.
5. ✅ `isolatedHorizon_violates_H_RT` — promotes Phase 6c.5 concrete-instance falsifier `kaulMajumdar_not_H_RT` to universal-under-IH (cross-bridge consumes both `h_rt.rt_proportional` AND `hIH.takes_kaulMajumdar_form` + `Real.log_pos`).
6. ✅ `topologicalEntanglementEntropy_no_log_A_form` — negative result: bare topological entropy has no `log A` form (two-evaluation argument at A=4G_N + A=4G_N·e); structural separation from IH-derived Kaul-Majumdar regime.
7. ✅ `kaulMajumdarS_satisfies_IH` + `kaulMajumdarS_violates_H_RT_via_IH` — witness instance for IH bundle (Pattern #8 LOAD-BEARING cross-module bridge to Phase 6a.3) + compositional sanity check recovering Phase 6c.5 falsifier.

**Re-scoping note:** original headline #4 (`rt_recovers_kaulMajumdar_on_SU2k` as unconditional theorem) is structurally not derivable from pure-LM on MTC substrate per dossier verdict (B). Shipped instead as conditional theorem `rt_log_coefficient_under_IH` under explicit isolated-horizon hypotheses. Original headline #6 (`rt_subleading_correction_on_fibonacci` with `(c_top/24) log A` term) is structurally not present in bare LM (per dossier (a3)) — `c_top` enters the modular T-matrix phase, NOT the entropy. Shipped instead as concrete Fibonacci witness `rt_entropy_fibonacci` giving the dossier's correct algebraic form `−(1/2) log((5+√5)/2)`.

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

## Wave 2 — `CasiniHuertaModularHamiltonianMTC.lean` [6j.2] [Pipeline: Stages 1–5 SHIPPED 2026-04-30; Stages 6–13 deferred to Phase 6j paper-bundle assembly]

**STATUS: ✅ SHIPPED 2026-04-30. Lean module + library build verification (Stages 1-5) complete.** 16 substantive thms / 1 noncomputable def / 1 structure / 0 sorry / 0 new axioms / library 8492 jobs PASS clean. **Critical dossier finding (verdict §6) drove a re-scoping**: the original "saturates on abelian / strict on non-abelian" framing is structurally **wrong** — the leading `(c_LR/3) log(L/ε)` log coefficient saturates on ANY unitary MTC (Holzhey-Larsen-Wilczek universal); the substrate dependence is in the subleading `−γ = −log D = −(1/2) log D²`, which is `log 2` for BOTH toric (abelian) and Ising (non-abelian) — Dong-Liu-Wen ambiguity recurs at γ-level. Fibonacci has `γ = (1/2) log((5+√5)/2) ≈ 0.6429`. The cleanest falsifiable claim shipped: **`casiniHuerta_saturation_iff_trivial_MTC` — bound saturates ⟺ `D² = 1` (trivial MTC), strict by closed-form `Δ = γ` otherwise.** Phase 6c.5 `H_CasiniHuerta_Bound_Valid` promoted to derived theorem under `CHEntropyHypotheses` + positivity via `CHE_promotes_H_CasiniHuerta`. Wave 3 (`ScramblingTimeQuantitative.lean`) UNBLOCKED.

**Goal.** Derive the Casini-Huerta universal entropy bound via the modular Hamiltonian `K_A = −log ρ_A` for an interval / disk subregion in a 1+1D / 2+1D rational CFT realizing a fixed MTC. Promote `H_CasiniHuerta_Bound_Valid` (Phase 6c.5 tracked hypothesis) to a derived theorem on this substrate. Establish the falsifiable concrete prediction: the bound saturates on abelian MTCs (toric code, ℤ_n) and is strict on non-abelian MTCs (Fibonacci, Ising), with closed-form expressions for the strict-bound tightness.

**Prerequisites (all met 2026-04-30):**
- ✅ Deep-research dossier filed at `Lit-Search/Phase-6j/6j-Casini-Huerta Modular Hamiltonian on MTC Substrate.md`.
- ✅ Wave 1 `RTReplicaTrickOnMTC.lean` SHIPPED — `topologicalEntanglementEntropy` + `IsolatedHorizonHypotheses` available for consumption.
- ✅ Gate J.2 user authorization: implicit per "you can update any user authorization between waves to approved as long as it's internal work" 2026-04-30.
- `Lit-Search/Phase-5e/Verlinde Formula...md` for Verlinde-formula-derived modular Hamiltonian.

**Module structure (as shipped):**
- ✅ `lean/SKEFTHawking/CasiniHuertaModularHamiltonianMTC.lean` — 427 LOC, 16 substantive theorems shipped (target was ~22 — re-scoping to honest dossier-corrected content reduced count).
- `src/holography/modular_hamiltonian.py` — numerical modular-Hamiltonian computation for Fibonacci + Ising + toric-code substrates; reproduces Holzhey-Larsen-Wilczek 1994 universal bound numerically.
- `tests/test_modular_hamiltonian.py` — saturation test (abelian-MTC) + strict-bound test (non-abelian-MTC); 14+ tests.
- `figures/fig_ch_bound_saturation_abelian_strict_nonabelian.{png,html}` — bound saturation across MTC families.

**Headline theorems (SHIPPED — re-scoped per dossier verdict §6 + recommended Lean signatures §7):**
1. ✅ `topologicalEntropy_logD` (def) + `_nonneg` / `_pos_iff` / `_eq_zero_iff` — Kitaev-Preskill γ-positive form `γ = (1/2) log D²`; biconditional separates trivial (γ=0) from non-trivial (γ>0) topological order.
2. ✅ `topologicalEntropy_logD_eq_neg_wave1` — cross-wave bridge: Wave 2 γ is the negative of Wave 1's `topologicalEntanglementEntropy`. Substantive Pattern #6 cross-wave bridge.
3. ✅ Concrete witnesses: `topologicalEntropy_logD_toric_code` (= log 2), `topologicalEntropy_logD_ising` (= log 2), `topologicalEntropy_logD_fibonacci` (= (1/2) log((5+√5)/2)) — closed-form algebraic constants consuming Wave 1 globalDimSq results.
4. ✅ `topologicalEntropy_logD_toric_eq_ising` — DLW ambiguity recurs at γ-level (toric and Ising have identical γ despite differing F-symbol structure).
5. ✅ `CHEntropyHypotheses` (struct) — substantive Prop bundle for Bisognano-Wichmann + Calabrese-Cardy + Kitaev-Preskill boundary-CFT inputs (analog of Wave 1 `IsolatedHorizonHypotheses`).
6. ✅ `casiniHuerta_bound_under_CHE` — under CHE, `S_A H L ε ≤ (c_LR/3) log(L/ε) + c'_1` (uses `topologicalEntropy_logD_nonneg` + `linarith`).
7. ✅ `casiniHuerta_saturation_iff_trivial_MTC` — DOSSIER-CORRECTED falsifiable claim: bound saturates ⟺ `D² = 1`. Substantive biconditional via `topologicalEntropy_logD_eq_zero_iff`.
8. ✅ `casiniHuerta_strict_tightness_equals_gamma` — closed-form quantitative tightness: gap = γ exactly (algebraic identity).
9. ✅ `casiniHuerta_strict_lt_on_nontrivial_MTC` — strict bound on `D² > 1` substrates.
10. ✅ `CHE_promotes_H_CasiniHuerta` — cross-bridge to Phase 6c.5: under CHE + positivity, the entropy satisfies `H_CasiniHuerta_Bound_Valid` (analog of Wave 1's `isolatedHorizon_violates_H_RT`).
11. ✅ `hlw_form_satisfies_CHE` + `hlw_form_satisfies_H_CasiniHuerta` — witness instance + compositional sanity check (Pattern #8 LOAD-BEARING — references named cross-module + Wave 1 defs).

**Re-scoping note:** original headline #1 (`modular_hamiltonian_from_density_matrix` defining `K_A = −log ρ_A`) is **structurally not derivable** per dossier verdict (a.2): on type-III von Neumann factor (any local algebra in QFT, per Witten 2018), `−log ρ_A` is not well-defined as a self-adjoint operator. The operator-algebraic substitute is `K_A = −log Δ_A` (modular operator). For Wave 2 first-pass, this is bundled as a hypothesis input in `CHEntropyHypotheses` rather than constructed; Wave 4 may revisit if Mathlib gains `vNeumannAlgebra`/Tomita-Takesaki infrastructure. Original headlines #3/#4/#5 (saturation-on-abelian / strict-on-non-abelian) are dossier-corrected: the leading log coefficient saturates on ANY MTC, so the abelian-vs-non-abelian distinction is at the γ-subleading level — and toric/Ising both have γ=log 2 (DLW ambiguity), so it's "trivial vs non-trivial MTC" not "abelian vs non-abelian". Original headline #6 (`ch_bridge_to_rt_on_mtc` with `Area/4G_N + Δ_CH`) is structurally a Wave-3-or-later bridge; deferred. Wave 2's cross-bridge instead targets Phase 6c.5's `H_CasiniHuerta_Bound_Valid` directly via `CHE_promotes_H_CasiniHuerta`.

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

## Wave 3 — `ScramblingTimeQuantitative.lean` [6j.3] [Pipeline: Stages 1–5 SHIPPED 2026-04-30 at structural-substantive scope + §9 dossier integration; Stages 6–13 deferred until paper-bundle assembly]

**STATUS: ✅ SHIPPED 2026-04-30 + DOSSIER INTEGRATION SHIPPED 2026-04-30.** 17 substantive thms (12 baseline + 5 §9 dossier) / 2 noncomputable defs (1 baseline + 1 §9 `fundamentalQuantumDim_SU2k`) / 1 structure / 0 sorry / 0 new axioms / library 8494 jobs PASS clean. **Dossier verdict (filed `Lit-Search/Phase-6j/Phase 6j Wave 3 Dossier — Quantitative Scrambling Time on MTC Substrate.md`):** form (D), Fibonacci (C), Ising (C), SU(2)_k (D — `2 cos(π/(k+2)) = [2]_q` is the spin-1/2 quantum dimension, NOT the maximum, for k ≥ 4), Toric (C). `Δ_F(C)` closed-form values are the He-Numasawa-Takayanagi-Watanabe entanglement-jump constants `ΔS_a = log d_a` (arXiv:1403.0702), NOT primary-source-cited as scrambling-time corrections. **§9 dossier-corrective additions:** `entanglement_jump_log_sqrt_two_eq_half_log_two` (Ising entanglement-jump constant), `fibonacciHorizonBC_globalDimSq_eq_one_plus_goldenRatio_sq` (Mathlib `goldenRatio` bridge), `fundamentalQuantumDim_SU2k` named def + numerical witnesses at k=2 (=√2) and k=4 (=√3) + structural-correction theorem `fundamentalQuantumDim_SU2k_at_k_four_lt_two` falsifying the roadmap's `d_max = 2 cos(π/(k+2))` claim at k=4 (since the actual `d_max(SU(2)_4) = [3]_q = 2`, but roadmap formula gives `√3 < 2`). Wave 4 (`HolographicCFunctionMTC.lean`) UNBLOCKED.

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

## Wave 4 — `HolographicCFunctionMTC.lean` [6j.4] [Pipeline: Stages 1–5 SHIPPED 2026-04-30 at structural-substantive scope + §9 dossier integration; Stages 6–13 deferred until paper-bundle assembly]

**STATUS: ✅ SHIPPED 2026-04-30 + DOSSIER INTEGRATION SHIPPED 2026-04-30.** 10 substantive thms (6 baseline + 4 §9 dossier) / 2 defs (1 baseline + 1 §9 `cLogTotal`) / 1 structure / 0 sorry / 0 new axioms / library 8494 jobs PASS clean / 2 retroactive P5 trivial-projection cuts in post-wave audit (`c_nonneg_under_HCF` and `c_eq_zero_iff_trivial_under_HCF` were pure `IsHolographicCFunction` field projections; inlined at consumer sites). **Dossier verdict (filed `Lit-Search/Phase-6j/Phase 6j Wave 4 — Holographic c-Function on Horizon-MTC Substrate.md`):** Claim 1 (verdict C → D, mislabel — published "FP entropy" is `log FPdim`, not the roadmap's `∑ d_a² log(d_a²)/D²` formula); Claim 2 (verdict A for `cLogTotal` via DMNO Lemma 3.11; verdict C for roadmap formula); Claim 3 (verdict D — Virasoro c not extractable from MTC); Claim 4 (verdict B — trivial under definition substitution); Claim 5 (verdict D — `log φ²` arithmetically false under all 3 candidate definitions). **§9 dossier-corrective additions:** `cLogTotal` named def (= dossier-recommended c-function `log D²`), `cLogTotal_fibonacci` corrected closed form `log((5+√5)/2)` (substituting for the arithmetically-false roadmap claim `log φ²`), `cLogTotal_trivialAbelian` baseline (= 0), `cLogTotal_satisfies_HCF` sanity check, **`cLogTotal_fibonacci_ne_log_goldenRatio_sq` substantive dossier-corrective inequality** proving the original roadmap claim `log φ²` is wrong under the dossier-recommended definition. Per dossier §4.5: minimal-model Virasoro recovery is **DROPPED** (no theorem shipped — verdict D structurally wrong). **Phase 6j is FULLY CLOSED at structural-substantive scope + W3+W4 dossier integration across all 4 waves.**

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

## Phase 6j FULLY CLOSED — final state summary (2026-04-30)

Per CLAUDE.md "ignore PM estimates on roadmaps", actual completion of Phase 6j Stages 1-5 across all 4 waves was a **single-session effort** (vs the 17-25 PM ≈ 4-6-month estimate). Stages 6-13 (cross-layer Python + figures + Stage 13 review + paper bundle assembly) are deferred.

### Final ship state

| Wave | Module | LOC | Theorems | Defs | Structs | Cuts | Notes |
|------|--------|-----|----------|------|---------|------|-------|
| W1 | `RTReplicaTrickOnMTC.lean` | 544 | 17 | 4 | 1 | 0 + 1 cross-bridge restoration | Re-scoped per dossier verdict (B): bare-LM gives only `−(1/2) log D²` |
| W2 | `CasiniHuertaModularHamiltonianMTC.lean` | 427 | 16 | 1 | 1 | 0 | Re-scoped per dossier §6: bound saturates ⟺ trivial MTC, not abelian |
| W3 | `ScramblingTimeQuantitative.lean` | 425 | 18 (12 baseline + 6 §9) | 2 (1 baseline + 1 §9) | 1 | 0 | + §9 dossier integration: HNTW entanglement-jump constants + SU(2)_k structural correction (k=2 √2, k=3 φ, k=4 √3, falsifier `√3 < 2`); roadmap formula coincides with d_max for k ∈ {2,3} only |
| W4 | `HolographicCFunctionMTC.lean` | 510 | 16 (6 baseline + 4 §9 + 1 §9.5b corollary + 5 §10) | 2 (1 baseline + 1 §9) | 1 | 2 (P5 trivial projections) | + §9 dossier integration + §10 Tier-2 cross-wave bridges (W4↔W1, W4↔W2) + DLW recurrence at c-function level (toric=Ising=2 log 2); §9.5 strengthened to strict `>` form |
| **Total** | **4 modules** | **1906** | **67 (51 baseline + 9 §9 dossier + 7 Tier-2 strengthening)** | **9 (7 baseline + 2 §9)** | **4** | **2** | **library 8494 jobs PASS clean** |

**Project totals after Phase 6j ship + W3+W4 dossier integration + Tier-1+2 strengthening:** ~4763 substantive theorems / 230 modules / 1 axiom / 0 sorry.

### Hypothesis-bundle architecture

Each wave introduces a substantive Prop bundle that records the inputs the bare MTC carrier does NOT supply, codifying the Wave 1 dossier-discovered honest-promotion pattern:

| Wave | Bundle | Promotes | Net output |
|------|--------|----------|------------|
| W1 | `IsolatedHorizonHypotheses` | Phase 6c.5 `H_RT_Formula_Valid` (via violation under IH) | Entropy = `kaulMajumdarS A G_N c0` |
| W2 | `CHEntropyHypotheses` | Phase 6c.5 `H_CasiniHuerta_Bound_Valid` (via `CHE_promotes_H_CasiniHuerta`) | Entropy = `(c_LR/3) log(L/ε) + c'_1 − γ` |
| W3 | `QuantitativeScramblingHypotheses` | Phase 6c.4 `HPCode.scramblingTimeBound` (via `QSH_strengthens_QEC_scramblingTimeBound`) | `t_scr H = log H.globalDimSq + Δ_F H` |
| W4 | `HolographicCFunctionHypotheses` | Cross-wave to W2/W3 via saturation-set equivalence | `c` is non-negative, vanishes ⟺ trivial, monotone under MTC `globalDimSq` ordering |

### Cross-bridge graph

```
Phase 6a.3 BHEntropyMicroscopic ──── HorizonMTCBC + kaulMajumdarS ──┐
                                                                    │
Phase 6c.4 QECHolographyBridge ─── HPCode + scramblingTimeBound ──┐ │
                                                                  │ │
Phase 6c.5 RTCasiniHuertaBounds ── H_RT + H_CH tracked Props ──┐ │ │
                                                                │ │ │
                                                                ▼ ▼ ▼
                W1 RTReplicaTrickOnMTC ─── topologicalEntanglementEntropy ──┐
                                          IsolatedHorizonHypotheses        │
                W2 CasiniHuertaModularHamiltonianMTC ── topologicalEntropy_logD ── (W2 ↔ W1: γ neg-form-positive-form)
                                                       CHEntropyHypotheses    │
                W3 ScramblingTimeQuantitative ── quantitativeScramblingTime ──── (W3 ↔ W1: t_scr = -2·topEntEnt + Δ_F)
                                                  QuantitativeScramblingHypotheses (W3 ↔ W2: t_scr = 2γ + Δ_F)
                W4 HolographicCFunctionMTC ── IsHolographicCFunction ─────────── (W4 ↔ W2: c = 0 ⟺ γ = 0)
                                              HolographicCFunctionHypotheses     (W4 ↔ W3: c = 0 ⟺ t_scr = Δ_F)
```

### Three dossier-correction patterns observed

* **W1 (verdict B):** bare-LM on pure-CS gives only `−(1/2) log D²`, not Kaul-Majumdar.
* **W2 (verdict §6):** leading log saturates on ANY MTC (not just abelian); subleading γ ambiguous between abelian and non-abelian (DLW recurrence at γ-level).
* **W4 (algebraic inconsistency):** the roadmap claim `c(Fib) − c(triv) = log φ²` is **algebraically inconsistent** with the proposed Frobenius-Perron formula `c(C) = (1/D²) ∑_a (d_a)² log(d_a)²` — would require `2/((5+√5)/2) = 1`, i.e., `√5 = -1`. Dossier filed for correction.

---

## Post-Deep-Research TODOs (W3 + W4 dossier integration)

### W3 TODO list (post-dossier) — ✅ COMPLETE 2026-04-30

**Dossier returned at:** `Lit-Search/Phase-6j/Phase 6j Wave 3 Dossier — Quantitative Scrambling Time on MTC Substrate.md`. **Task file moved to `Lit-Search/Tasks/complete/Phase6j_W3_quantitative_scrambling_time.md`.**

**Dossier verdict (mixed C/D):** form (D) — `t_scr = log D² + Δ_F + o(1)` is **not primary-source-cited as a published identity**; Hayden-Preskill / MSS / Sekino-Susskind do not commit to a universal MTC-substrate O(1) correction.  Closed-form values: Fibonacci `log φ` (C — published as HNTW entanglement-jump for τ-primary local quench, NOT scrambling-time correction); Ising `(1/2) log 2 = log √2` (C — published as HNTW entanglement-jump for σ-primary, NOT scrambling-time correction); SU(2)_k `log d_max = log(2 cos(π/(k+2)))` (D — `2 cos(π/(k+2)) = [2]_q` is the **fundamental** spin-1/2 quantum dimension, NOT the maximum, for k ≥ 4); Toric `Δ_F = 0` (C — true for any "log of a quantum dimension" prescription since abelian d_a = 1).

**Verdict (C) handling:** keep `Δ_F` closed-form values as conjectural inputs to `QuantitativeScramblingHypotheses` (already shipped); do NOT promote to derived theorems.  Substantive entanglement-jump constants shipped as **separate** §9 theorems with primary-source citations to He-Numasawa-Takayanagi-Watanabe (Phys. Rev. D 90, 041701(R) (2014), arXiv:1403.0702).

**Verdict (D) handling:** SU(2)_k formula error addressed via §9.3 sequence — `fundamentalQuantumDim_SU2k` named def (= dossier's `d_fundamental` correction), numerical witnesses at k=2 (=√2) and k=4 (=√3), structural-correction theorem `fundamentalQuantumDim_SU2k_at_k_four_lt_two` (the `√3 < 2` falsifier proving the roadmap formula gives `< 2` while the actual `d_max(SU(2)_4) = [3]_q = 2`).

**§9 deliverables shipped (5 thms + 1 def):**
1. ✅ `entanglement_jump_log_sqrt_two_eq_half_log_two` — Ising HNTW entanglement-jump value `log √2 = (1/2) log 2`.
2. ✅ `fibonacciHorizonBC_globalDimSq_eq_one_plus_goldenRatio_sq` — Mathlib `goldenRatio` bridge.
3. ✅ `fundamentalQuantumDim_SU2k` (def) — dossier-corrected named API for `d_{1/2}(SU(2)_k) := 2 cos(π/(k+2))`.
4. ✅ `fundamentalQuantumDim_SU2k_at_k_two = √2` (k=2 / Ising case, where formula coincides with d_max).
5. ✅ `fundamentalQuantumDim_SU2k_at_k_four = √3` (k=4 case).
6. ✅ `fundamentalQuantumDim_SU2k_at_k_four_lt_two` — DOSSIER STRUCTURAL CORRECTION falsifier showing roadmap formula gives `< 2` at k=4 while actual `d_max(SU(2)_4) = 2`.

**Pattern #1-#8 audit on new theorems:** all 5 §9 theorems clear preemptive-strengthening checklist (P2 NO bundle redundancy; P3 NO trivial-multiplication; P5 NO trivial-discharge; P6 cross-bridges to Wave 1 `fibonacciHorizonBC_globalDimSq` + Mathlib `goldenRatio_sq` / `Real.cos_pi_div_*` / `Real.log_sqrt` are NAMED CALLS in proof bodies; P7 NO defining-the-conclusion).  Zero retroactive cuts.

**Library build:** `lake build SKEFTHawking.ExtractDeps` PASS clean; 8494 jobs / 0 sorry / 0 new axioms.

**Memory:** new file `project_phase6j_w3_post_dossier.md` describes integration.

### W4 TODO list (post-dossier) — ✅ COMPLETE 2026-04-30

**Dossier returned at:** `Lit-Search/Phase-6j/Phase 6j Wave 4 — Holographic c-Function on Horizon-MTC Substrate.md`. **Task file moved to `Lit-Search/Tasks/complete/Phase6j_W4_holographic_c_function.md`.**

**Dossier verdict (5 claims, mostly C/D):**
- Claim 1 (verdict C → D, mislabel): roadmap formula `c(C) := (1/D²) ∑_a (d_a)² log(d_a)²` is mislabeled as "Frobenius-Perron entropy"; published "FP entropy" is `log FPdim(C) = log D²(C)` (Etingof-Gelaki-Nikshych-Ostrik 2015 §3.3; Kitaev-Preskill 2006).
- Claim 2 (verdict A for `cLogTotal` / verdict C for roadmap): `cLogTotal(C/A) ≤ cLogTotal(C)` is published DMNO Lemma 3.11 (J. Reine Angew. Math. 677:135 2013); roadmap-formula monotonicity unverified.
- Claim 3 (verdict D, structurally wrong): minimal-model Virasoro central-charge recovery `c(M(p,q)) = 1 − 6(p−q)²/(pq)` is **NOT extractable from MTC alone** (Bruillard-Ng-Rowell-Wang JAMS 29:857 2016 + Huang PNAS 102:5304 2005 anomaly/MTC separation). **DROPPED entirely.**
- Claim 4 (verdict B, derivable but trivial): `c = log D²` saturates on abelian MTC — under `cLogTotal`, `cLogTotal(abelian) = log rank` since abelian D² = rank.
- Claim 5 (verdict D, arithmetically false): `c(Fib) − c(triv) = log φ² ≈ 0.962` is **arithmetically false** under all 3 candidate definitions: `cLogTotal(Fib) = log((5+√5)/2) ≈ 1.287`, `cRoadmap(Fib) = ((5+√5)/5)·log φ ≈ 0.696`, `cShannonFP(Fib) ≈ 0.591`.  None equals `log φ²`.

**§9 deliverables shipped (4 thms + 1 def):**
1. ✅ `cLogTotal` (named def) — dossier-recommended c-function candidate `log D²` (= published "FP entropy" / Affleck-Ludwig boundary entropy / Kitaev-Preskill γ × 2).
2. ✅ `cLogTotal_fibonacci = log((5+√5)/2)` — corrected Fibonacci closed form (substituting for arithmetically-false roadmap claim `log φ²`).
3. ✅ `cLogTotal_trivialAbelian = 0` — trivial-MTC closed form (cross-module bridge to Phase 6c.4 `trivialAbelianHorizonBC`).
4. ✅ `cLogTotal_satisfies_HCF` — sanity-check restatement under named def (Pattern #8 LOAD-BEARING — public API for the dossier-recommended c-function).
5. ✅ `cLogTotal_fibonacci_ne_log_goldenRatio_sq` — DOSSIER-CORRECTIVE INEQUALITY proving the original roadmap claim `log φ²` is arithmetically false (uses `Real.log_injOn_pos` to reduce to `(5+√5)/2 ≠ (3+√5)/2`, which would require `√5 = -1`).

**DROPPED per dossier §4.5:** No theorem claiming Virasoro central-charge recovery from MTC data (verdict D — structurally wrong; `c_Vir` is not an MTC invariant).

**Pattern #1-#8 audit:** all 4 §9 theorems clear preemptive-strengthening checklist (P2 NO bundle redundancy; P3 NO trivial-multiplication — `cLogTotal_fibonacci` consumes Wave 1 `fibonacciHorizonBC_globalDimSq`; P5 the §9.4 `cLogTotal_satisfies_HCF` restatement is Pattern #8 LOAD-BEARING — clause 1 named alias + clause 3 cross-module API + clause 4 consumed by dossier-recommended public API; P6 cross-bridges to Wave 1 + Phase 6c.4 + Mathlib `goldenRatio` / `Real.log_injOn_pos` are NAMED CALLS in proof bodies; P7 NO).  Zero retroactive cuts.

**Library build:** `lake build SKEFTHawking.ExtractDeps` PASS clean; 8494 jobs / 0 sorry / 0 new axioms.

**Memory:** new file `project_phase6j_w4_post_dossier.md` describes integration.

### Stage 6-13 cycle (separate from dossier integration)

Once W3 + W4 dossier integration completes, Phase 6j has TWO additional outstanding tracks:

**Track A — Cross-layer Python / numerical / figures (Stages 6-9):**
- `src/holography/replica_trick.py` — numerical replica computation for Fibonacci + Ising + SU(2)_k.
- `src/holography/modular_hamiltonian.py` — numerical modular-Hamiltonian computation.
- `src/holography/scrambling_time.py` — numerical OTOC for natural-MTC families.
- `src/holography/c_function.py` — numerical c-function under RG flow.
- `tests/test_*` for each.
- `figures/fig_*` figures registered in `scripts/review_figures.py`.

**Track B — Paper bundle assembly (Stages 10-13):**
- Per `docs/PAPER_DRAFT_MAPPING.md`: Phase 6j content lifts into bundle target **D3 §13.5 + I1 sidebar** (Phase 6i Wave 7 paper-bundle architecture).
- Stage 10: paper section drafting + `physics-qa:claims-reviewer` invocation.
- Stage 11: technical + stakeholder notebooks.
- Stage 12: document sync + counts regeneration.
- Stage 13: bundle-target Stage 13 review per `docs/agents/claims-reviewer-bundle-prompts.md`.

Both tracks gated on Phase 6j paper-bundle preparation cycle (timing TBD; could be deferred indefinitely while focus is on other phases).

---

*Last updated: 2026-04-30 (Phase 6j FULLY CLOSED at structural-substantive scope + W3+W4 dossier integration §9 SHIPPED + Tier-1+2 strengthening pass §10 SHIPPED). Status: ALL 4 WAVES SHIPPED Stages 1-5; W3+W4 dossier integration ✅ COMPLETE; Tier-1+2 cross-wave-bridge strengthening ✅ COMPLETE; Stages 6-13 deferred to future paper-bundle assembly cycle. Phase 6j totals: 67 substantive theorems / 9 defs / 4 structures / ~1906 LOC / 0 sorry / 0 new axioms / library 8494 jobs PASS clean.*
