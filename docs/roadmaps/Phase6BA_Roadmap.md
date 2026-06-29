# Phase 6BA — Verified Quantum Transport (NEGF / Landauer–Büttiker)

**Status: COMPLETE (W1–W3 shipped 2026-06-29; fresh-context adversarial review 0 BLOCKER/0 MAJOR).** To our knowledge, the first machine-checked non-equilibrium Green's-function (NEGF) steady-state transport: retarded/advanced Green's functions, the Landauer–Büttiker / Meir–Wingreen conductance, and a certified conductance-quantization bound. To our knowledge, no NEGF Green's-function / Landauer-*conductance* transport exists in any proof assistant (prior-art search to be run via `research-scout` before any D10 paper-lift). One of the public substrate-breadth phases scoped 2026-06-29 (companion chemistry phases 6BB–6BD; materials phases 6CA–6CE); the PhysLib unbounded-operator resolvent makes the new transport layer MODERATE, not greenfield-expensive. Distinct double-letter phase in the `6B*` (computational-chemistry) series, independent of the unrelated `6A`/`6b`.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP `loogle`/`leansearch`):**
- **Reuse (exists):** PhysLib `…/Operators/SpectralTheory/Basic.lean` — `resolvent (T : H →ₗ.[ℂ] H) (z) := (T - z • 1).inverse` (unbounded-operator resolvent on Mathlib `LinearPMap`) + `defectNumber`/numerical-range API; project `GrapheneNoiseFormula.lean` — `hawkingNoisePSD`, `johnsonNyquistPSD`, `snrPerBin` (the existing Keldysh + Landauer–Büttiker *noise* spectrum the conductance result ties into); project `QuantumNetwork/NumericalBounds.lean` `expNeg_enclosure` (rational enclosure).
- **Absent → build (confirmed):** NEGF Green's functions + Landauer *conductance* — 0 hits in Mathlib, PhysLib, and the project (the project's only Landauer–Büttiker content is the noise PSD above, **not** the Green's-function conductance).
- **New content:** `G^{R/A}`, spectral function `A`, transmission `T(E)=Tr[Γ G^R Γ G^A]`, conductance — on PhysLib `resolvent` + Mathlib finite-dim `Matrix`.
- **Correction (was a planning miss):** `DKMBootstrap/` is **not** a brick — it is an SK-EFT SDP transport *bootstrap* (`IsDKMSpectralFunction` predicate, `horizon_transport_uniqueness_graphene_witness_one_half`, `sharpened_no_go_super_factorial`) with **no** NEGF broadening/Green's-function machinery; at most a thematic SK-EFT transport cross-bridge, not load-bearing here.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target **D10** (authorized 2026-06-29 in `PAPER_STRATEGY`) — record it; the `papers/D10/` + `_VALID_BUNDLE_TARGETS` scaffolding is created at **first content-lift** (`BUNDLE_LIFT_PROCEDURE` step 2), not before. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)** — DR "ship as axiom" is advisory; use a disclosed tracked-Prop. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** the broadening matrices `Γ` and all NEGF Green's functions are built **fresh** on PhysLib `resolvent` — `DKMBootstrap` is **not** a brick (see Substrate).

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` in proof bodies (#10); preemptive-strengthening checklist before each statement; decompose-before-asserting-walls; never push. **Two-layer honesty:** the transport *formulas* are Lean-verified; the device/material identification stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens) — a chunking heuristic, not a time estimate (PM/time estimates remain banned). Frame purely as physics (dual publication + flagship scope).

**Bundle target:** **D10** (authorized 2026-06-29) — "Kernel-Verified Foundations of Computational Quantum Chemistry & Open-System Dynamics" *(provisional)*, shared with 6BB/6BC. Roster-expansion mechanics (`PAPER_STRATEGY` roster, `_VALID_BUNDLE_TARGETS`, `papers/D10/` scaffold) execute at **first content-lift** per `BUNDLE_LIFT_PROCEDURE` — not at planning time (avoids standing up an empty bundle).

---

## Wave 1 — NEGF Green's-function substrate ✅ COMPLETE (2026-06-29)
- **Goal:** `G^{R/A}(E) = (E − H ± iη)⁻¹`; self-energy `Σ`; spectral function `A = i(G^R − G^A)`; sum rule `∫ A dE/2π = 1`. **Verdict: reachable** — resolvent on existing operator substrate.
- **Why:** the load-bearing object every transport quantity is built from.
- **Bricks:** PhysLib `SpectralTheory.Basic.resolvent` (on `H →ₗ.[ℂ] H`); Mathlib `LinearPMap`; finite-dim `Matrix`. (Broadening matrices `Γ` are defined here — new, not from DKMBootstrap.)
- **Architecture decision (2026-06-29):** built on **finite-dim `Matrix m m ℂ`** (Mathlib nonsingular inverse), NOT PhysLib's `LinearPMap.resolvent` — the latter is for *unbounded* operators on infinite-dim Hilbert space and carries no trace, but the headline transport observables (W2 `Tr[Γ_L G^R Γ_R G^A]`, W3 `G = n·G₀`) are inherently finite-dimensional. PhysLib `resolvent` stays a thematic spectral bridge, not load-bearing. (Matches the W1 brick list's "finite-dim `Matrix`".)
- **Done (AC / `/goal` condition):**
  - [x] `NEGFGreenFunction.lean` builds clean — 0 sorry, kernel-pure (`lean_verify` on the headlines = `{propext, Classical.choice, Quot.sound}`), no new project-local axiom; full `lake build` green (9449 jobs); imported into root `SKEFTHawking.lean`
  - [x] `G^{R/A}`/`Σ`/`Γ`/`A` defined; `negf_spectral_sum_rule` (`∫A dE/2π = 1`, entrywise) + `A ⪰ 0` (`spectralFn_posSemidef`) proven; strengthening checklist applied first-pass
- **Shipped declarations (`lean/SKEFTHawking/NEGFGreenFunction.lean`, 24 decls):** defs `retardedArg`/`advancedArg`/`gRetarded`/`gAdvanced`/`spectralFn`/`selfEnergy`/`broadening`; `retardedArg_isUnit` (invertibility via `G^R·G^A = η²·1+B²` PosDef); `advancedArg_eq_conjTranspose`/`advancedArg_isUnit`; `gAdvanced_eq_conjTranspose`; `spectralFn_eq_two_mul_eta` (`A = 2η·G^R(G^R)ᴴ`); **`spectralFn_posSemidef`** (`A ⪰ 0`); `lorentzian_integral_inv` (`∫1/((E−λ)²+η²)=π/η`); `resolvent_diag`/`gRetarded_diag`/`gAdvanced_diag`/`spectralFn_diag` (spectral-theorem diagonalization); **`negf_spectral_sum_rule`**; `broadening_isHermitian`; `selfEnergy_broadening` (`Γ=2η·1`); `spectralFn_eq_gR_broadening_gA` (fundamental NEGF relation `A = G^R Γ G^A`); `retardedArg_eq_sub_selfEnergy` (Dyson form).
- **Still open at phase level (deferred to phase close, not W1-blocking):** Stage-12 sync (`update_counts.py`, Inventory), Stage-13 strengthening review of new statements, D10 §transport first-lift staging.

## Wave 2 — Landauer–Büttiker conductance ✅ COMPLETE (2026-06-29)
- **Goal:** transmission `T(E) = Tr[Γ_L G^R Γ_R G^A]` (Caroli/Meir–Wingreen); `G = (2e²/h)∫ T(E)(−∂f/∂E) dE`. **Verdict: reachable** — trace formula over W1.
- **Why:** the headline observable.
- **Bricks:** W1 Green's functions; broadening matrices `Γ`; Mathlib `Matrix.trace`.
- **Done (AC / `/goal` condition):**
  - [x] `LandauerConductance.lean` builds clean — 0 sorry, kernel-pure (`lean_verify` `{propext, Classical.choice, Quot.sound}`), no new axiom; imported into root; full `lake build` green
  - [x] `T(E)=Tr[Γ_L G^R Γ_R G^A]` (`transmission` + `transmission_eq_gAdvanced`) + `landauer_conductance_def` + the linear-response limit (`landauerConductance_const_transmission`: constant `T₀` ⟹ `G=G₀·T₀`, given Fermi-window normalization) proven
- **Shipped (`lean/SKEFTHawking/LandauerConductance.lean`):** `transmission`, `transmission_eq_gAdvanced`, **`transmission_isReal`** (real observable), `transmissionReal`/`transmissionReal_ofReal` (scalar↔matrix bridge), `fermi`/`fermiWindow`, `landauerConductance`, `landauer_conductance_def`, **`landauerConductance_const_transmission`** (linear-response limit, conditional on Fermi-window normalization).
- **Strengthenings COMPLETE (2026-06-29, both formerly-deferred items now proven, kernel-pure):** (a) **`transmission_nonneg`** (`0≤T` for PSD leads — "transmission probability"), via the new reusable `posSemidef_exists_mul_conjTranspose` (hand-built spectral √, sidestepping the matrix C⋆-norm instance diamond) + PSD congruence; (b) **`fermiWindow_integral_eq_one`** (`∫(−∂f/∂E)=1` for β>0, via the improper FTC + logistic `HasDerivAt`/limits + exp-dominated integrability) ⟹ the **unconditional** linear-response limit **`landauerConductance_const_transmission'`** (`β>0 ⟹ G=G₀·T₀`, no normalization hypothesis).

## Wave 3 — certified transport bound ✅ COMPLETE (2026-06-29)
- **Goal:** steady-state current; conductance-**quantization theorem** `G = n·G₀` for n open channels + falsifier (`G > n·G₀ ⇒ ⊥`); resolvent-bound envelope. **Verdict: reachable.**
- **Why:** the falsifiable, certificate-grade result.
- **Bricks:** W1+W2; `expNeg_enclosure`-style enclosure.
- **Done (AC / `/goal` condition):**
  - [x] `NEGFTransportCertificate.lean` builds clean — 0 sorry, kernel-pure (`lean_verify` `{propext, Classical.choice, Quot.sound}`), no new axiom; imported into root; full `lake build` green
  - [x] **`conductance_quantization`** (`G = n·G₀`, n fully-open channels) + the `norm_num`-backed falsifier (**`conductance_quantization_falsifier`** `n·G₀ < G ⇒ ⊥` + concrete `two_channel_no_three_quanta` via `norm_num`/`nlinarith`) proven
- **Shipped (`lean/SKEFTHawking/NEGFTransportCertificate.lean`):** `channelConductance` (`G=G₀·∑τ_i`), **`channelConductance_le_quantum`** (`G ≤ n·G₀` certificate bound), **`conductance_quantization`**, **`conductance_quantization_falsifier`**, `two_channel_no_three_quanta` (concrete norm_num witness), `channelConductance_eq_landauer` (bridge to the W2 conductance functional).

## Phase status
W1 + W2 + W3 all COMPLETE + both W2 strengthenings closed (2026-06-29). Counts after phase: 14224 thm / 1134 mod / **0 axiom / 0 sorry**; `lake build` + `lake build SKEFTHawking.ExtractDeps` clean; `validate.py` 45/45 ALL CHECKS PASSED. Two fresh-context adversarial reviews passed (core: 0 BLOCKER/0 MAJOR/3 MINOR all fixed; strengthenings: 0 BLOCKER/0 MAJOR/0 MINOR/2 NIT all fixed). Remaining phase-close item: D10 §transport first-lift staging (deferred to first content-lift per BUNDLE_LIFT_PROCEDURE).

## Sequencing
W1 (substrate) → W2 (conductance) → W3 (certified bound). W1 unblocks all. 6BA is independent of 6BB/6BC/6BD.

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + `lake build SKEFTHawking.ExtractDeps` clean; `validate.py` green; counts + Inventory refreshed; root `SKEFTHawking.lean` imports; Stage-13-style strengthening review of new statements; D10 §transport row staged for first-lift; roadmap status updated.
