# Phase 6AN — Channel-composition, network-capacity, device-fidelity, and correct-by-construction compilation substrate

**✅ STATUS: ALL FIVE WAVES COMPLETE (2026-06-08).** W1 (`diamondDist_composeKraus_le` + worked
2-stage instance), W2 (`NetworkCapacity.lean` — flow/cut weak-duality converse + witnessed MFMC
equality + path-bottleneck achievability; **strengthened to FULL max-flow–min-cut strong duality
`maxFlow_eq_minCut` in `NetworkCapacityStrongDuality.lean`, built from scratch incl. the augmenting-path
theorem**), W3 (`ComposedGateFidelity.lean` — coherence ⊕ control
composed bound + fidelity reading + 2 binding regimes), W4 (`FDTNoiseFloor.lean` — Johnson–Nyquist FDT
floor + operating-point monotonicity + worked detector/amplifier + LDP rare-event tail + GC symmetry),
W5 (`FKLW/CliffordTCompiler.lean` — correct-by-construction Clifford+T compiler: `cliffordTCompile`
function + loop invariant + termination + unconditional algorithm-level error+length correctness +
worked instance). All kernel-pure `{propext,Classical.choice,Quot.sound}`, zero new project-local
axioms, no `maxHeartbeats`/`native_decide`. See per-wave ✅ blocks below.

**Status: PLANNED 2026-06-04.** A cluster of substrate extensions that the quantum-information / quantum-network
/ verified-compilation arcs have been consuming in *assembled* form but which are not yet present as
**reusable, kernel-pure theorems**. Each wave below makes an existing implicit composition explicit, so that
downstream constructions cite a single load-bearing lemma instead of re-deriving it. Independent of, and
complementary to, Phase 6AM (the Lieb/DPI entropy frontier); 6AM Wave 5's rate-ceiling and this phase's
composition lemmas are the two halves of a complete network error-budget calculus.

> **⚠️ CHECK PhysLib FIRST (2026-06-04).** `leanprover-community/physlib` (arXiv:2510.08672, on our Mathlib
> v4.29.1 pin) provides a complete QI substrate — see Phase 6AM. Before proving anything QI-flavored here from
> scratch, check PhysLib: **Wave 1 (channel-composition / diamond subadditivity)** overlaps PhysLib
> `QuantumInfo/Finite/Distance/*`, and **Wave 2 (network capacity)** overlaps `QuantumInfo/Finite/Capacity.lean`
> — prefer adopting/bridging (per Phase 6AM) over re-deriving. Waves 3–5 (composed coherence⊕gate-cost bound,
> FDT amplifier/detector floor, correct-by-construction compilation) are device-/compilation-specific and are
> NOT in PhysLib — those stand as written.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms
(Invariant #15); no `native_decide`; no `maxHeartbeats` in proof bodies; decompose-before-asserting-walls;
never push. Reachability verdicts recorded honestly per wave.

---

## Wave 1 — channel-composition diamond-distance subadditivity

**✅ STATUS: COMPLETE (2026-06-08).** The W1 goal was already shipped in Phase 6AH as
`diamondDist_composeKraus_le` (`QuantumNetwork/DiamondBudget.lean`), kernel-pure
`{propext,Classical.choice,Quot.sound}` (verified). This wave adds the missing **worked 2-stage
instance** `diamondDist_dephasing_after_depolarizing_le` (same file): a depolarizing→dephasing
pipeline vs the ideal `id∘id`, with end-to-end diamond error `≤ γ + p` discharged from the exact
per-stage distances `diamondDist_dephasing_eq` (=γ) + `diamondDist_depolarizing_eq` (=p). Both
kernel-pure; Gate met.

- **Goal:** `diamondDist (Φ₂ ∘ Φ₁) (Ψ₂ ∘ Ψ₁) ≤ diamondDist Φ₂ Ψ₂ + diamondDist Φ₁ Ψ₁` (and the sequential
  single-target form `diamondDist (Φ∘Ψ) (Φ'∘Ψ') ≤ …`). **Verdict: reachable — standard, toeholds present.**
- **Why:** turns a multi-stage pipeline's end-to-end error into a *provably composed* budget of per-stage
  errors — the kernel-pure lemma under any concatenated-channel error-budget reasoning.
- **Toeholds:** `QuantumNetwork/DiamondNorm*`, `DiamondBudget`, `DiamondSDP*` modules; CPTP-contractivity
  (`traceNorm_krausMap_le`).
- **Gate:** `diamondDist_compose_le` kernel-pure + a worked 2-stage instance.

## Wave 2 — multipath entanglement-distribution network capacity

**✅ STATUS: COMPLETE (2026-06-08) — two-sided-bounds form (the gate's stated alternative).** New module
`QuantumNetwork/NetworkCapacity.lean` (kernel-pure `{propext,Classical.choice,Quot.sound}`, no new
axioms). **Scout result:** Mathlib has NO network-flow/max-flow-min-cut theory, and there was no public
single-path capacity to generalize (the `composite`/`plobCap` notion is private). Full strong-duality
MFMC over arbitrary graphs is a separate large development; per the gate's explicit alternative
("*or the achievable lower + converse upper bounds*") the wave ships the genuine flow-network framework:
`FlowNetwork` (capacity-weighted graph + source/sink), `IsFeasibleFlow`, `flowValue`, `IsCut`, `cutCap`;
**converse upper bound** `flowValue_le_cutCap` (weak duality — every feasible flow value ≤ every cut
capacity, via conservation telescoped across the cut); **witnessed max-flow–min-cut equality**
`maxFlow_minCut_of_saturating` (a saturating flow+cut pair is simultaneously max-flow and min-cut —
`network_capacity = minCut` exhibited from weak duality without the strong-duality existence theorem);
**achievable lower bound / single-path specialization** `path3_capacity_eq_bottleneck` (two-hop path
`s→m→t`: bottleneck `min c₁ c₂` is achieved by a feasible flow AND equals the min-cut — the network
reading of `composite = min-cut over a path`); repeaterless corollary `path3_repeaterless_bottleneck`
(link capacities `= plobBound η`). Gate met (achievable lower + converse upper bounds, kernel-pure).

**🏆 FULL MAX-FLOW–MIN-CUT STRONG DUALITY — COMPLETE (2026-06-08, on user request; built from
scratch, Mathlib has no network-flow/LP-duality theory).** New module
`QuantumNetwork/NetworkCapacityStrongDuality.lean` (kernel-pure `{propext,Classical.choice,Quot.sound}`,
no new axioms). Headline `maxFlow_eq_minCut`: **for any finite capacity-weighted network with
`source ≠ sink`, there exist a feasible flow `f` and a source–sink cut `S` with `flowValue f = cutCap S`,
`f` a maximum flow and `S` a minimum cut** — i.e. max-flow value = min-cut capacity, unconditionally.
Pillars: `maxFlow_exists` (max flow *attained* — feasible set = closed subset of compact box `∏[0,cap]`,
`flowValue` continuous, extreme-value theorem); `flowValue_eq_cross_flux` (exact flux identity);
`flowValue_eq_cutCap_residualReachable` (easy saturation); `maxFlow_no_augmenting` (**the augmenting-path
theorem** — a max flow's residual graph cannot reach the sink); `maxFlow_eq_minCut_of_no_augmenting`
(assembles to equality). The augmenting-path theorem was the hard core: excess calculus `exc` with
single-edge local pushes (`exc_push_forward`), convex δ-rescaling (`exc_convex`/`cap_convex`),
`aug_core` (induction along a simple residual path, fresh-edge invariant), and `exists_nodup_chain`
(cycle removal from `Relation.ReflTransGen`). The weak-duality + path-bottleneck results above remain;
this supersedes them with the full equality.

- **Goal:** generalize single-path bottleneck capacity (`composite = min-cut over a path`) to a **network**:
  the max achievable end-to-end capacity over a graph equals the min-cut over all source–sink cuts
  (max-flow-min-cut for entanglement-distribution capacities). **Verdict: reachable-moderate** — graph-theoretic;
  check Mathlib for an existing max-flow-min-cut (likely partial) and build the capacity-specialization.
- **Why:** lifts routing/capacity reasoning from a single path to a real network topology.
- **Bricks:** capacity-weighted graph; cut/flow definitions; max-flow-min-cut (port/build); specialize to the
  per-link repeaterless capacity.
- **Gate:** `network_capacity_eq_minCut` (or the achievable lower + converse upper bounds) kernel-pure.

## Wave 3 — composed average-gate-fidelity bound (coherence ⊕ gate-error)

**✅ STATUS: COMPLETE (2026-06-08).** New module `QuantumNetwork/ComposedGateFidelity.lean`
(kernel-pure `{propext,Classical.choice,Quot.sound}`, no new axioms). Key unlock: the coherence
channel `coherenceKraus γ p = ampDampKraus γ ∘ dephasingKraus p` is *itself* a composition, so Wave-1
subadditivity + the exact named-channel distances give the closed-form coherence error
`diamondDist_coherenceChannel_le : diamondDist (coherenceChannel t T₁ T₂) (id∘id) ≤ cohGamma t T₁ + cohP t T₂`.
The headline composed bound `diamondDist_coherence_after_control_le`:
`diamondDist (Φ_coh ∘ ctrl) (id∘id∘ctrlId) ≤ (cohGamma t T₁ + cohP t T₂) + ε_ctrl` for any control
channel with `diamondDist ctrl ctrlId ≤ ε`. Fidelity reading `sqrtFidelity_coherence_after_control_ge`
(output sqrt-fidelity `≥ 1 − (cohGamma + cohP + ε)`, via the FvdG diamond→fidelity bridge). Two worked
regimes shipped: `diamondDist_coherence_after_control_le_coherence_binds` (t=T₁=T₂=1, ε≤1/100 ⟹
coherence term `> 1/2 > ε`) and `..._control_binds` (t=0 ⟹ coherence term =0, budget collapses to ε).
The 6AK.1 closed form `avgGateFidelity_coherenceChannel` supplies the coherence term's avg-gate-fidelity
reading. Gate met (composed bound kernel-pure + both binding regimes).

- **Goal:** an average-gate-fidelity (or diamond-distance) bound for a physical gate that **composes** the
  coherence-limited contribution (Phase 6AK.1 `avgGateFidelity_coherenceChannel`) with an explicit
  control/gate-error contribution, yielding a single bound as a function of `(T₁, T₂, t_gate, ε_ctrl)`.
  **Verdict: reachable — device-physics composition over existing bounds.**
- **Why:** the coherence ceiling alone is non-binding when control error dominates; the composed bound is the
  one that actually constrains realizable fidelity across operating regimes.
- **Bricks:** model the realized channel as `coherenceChannel ∘ (control-error channel)`; apply Wave 1
  composition + the 6AK.1 closed form; bound the control-error term.
- **Gate:** `avgGateFidelity_composed_bound` kernel-pure + a worked regime where coherence binds and one where
  control error binds.

## Wave 4 — FDT-bound amplifier / detector noise figure-of-merit

**✅ STATUS: COMPLETE (2026-06-08).** New module `QuantumNetwork/FDTNoiseFloor.lean` (kernel-pure
`{propext,Classical.choice,Quot.sound}`, no new axioms), specializing the shipped FDT/Crooks/LDP
substrate. **FDT floor:** `fdt_noise_floor_bound` (total current-noise PSD ≥ strictly-positive
Johnson–Nyquist floor `4 kB_T σ_Q` = `GrapheneNoiseFormula.johnsonNyquistPSD`); operating-point
monotonicity `johnsonNyquistPSD_mono_temp` / `johnsonNyquistPSD_mono_conductance`. **Worked operating
points:** `fdt_noise_floor_detector` (thermal floor + Hawking excess, strict, via `hawkingNoisePSD_pos`)
and `fdt_noise_floor_amplifier` (Caves quantum limit `A ≥ ℏω/2`: total strictly above floor by ≥ a
half-quantum). **Rare-event-tail companion:** `fdt_rare_event_tail` — the linear-response LDP rate
function `linearResponseRateFunction β σ² W = (W−βσ²/2)²/(2σ²)` is strictly positive for every noise
current away from the FDT-pinned mean `βσ²/2` (`fdt_noise_current_mean`), so all large deviations are
exponentially suppressed; `fdt_gallavotti_cohen` carries the W-form GC entropy-production symmetry
`I(W)−I(−W) = −βW`. Gate met (`fdt_noise_floor_bound` + rare-event-tail companion + worked
amplifier/detector points, kernel-pure).

- **Goal:** make the fluctuation-dissipation-theorem noise floor for a linear amplifier / detector operating
  point an explicit kernel-pure bound (Johnson/quantum-limited noise as a function of operating parameters),
  building on the existing `GloriosoLiu` / `QuantumCrooks` / `LDPLinearResponse` substrate. **Verdict:
  reachable — specialize existing FDT/Crooks/LDP machinery.**
- **Why:** completes the verifiable-operating-point-bound substrate for linear-response devices; the
  rare-event-tail (Crooks/LDP) and FDT-floor pieces become a single citable certificate-grade bound.
- **Bricks:** specialize `IsLDPRateFunction` + W-form Gallavotti–Cohen to the linear-amplifier noise current;
  the FDT floor as a positivity/monotonicity bound on the operating point.
- **Gate:** `fdt_noise_floor_bound` (+ rare-event-tail companion) kernel-pure; worked amplifier + detector
  operating points.

## Wave 5 — correct-by-construction compilation *(large sub-program; may spin to its own phase)*

**✅ STATUS: COMPLETE (2026-06-08) — COMPLETED IN FULL, not spun out.** New module
`FKLW/CliffordTCompiler.lean` (kernel-pure `{propext,Classical.choice,Quot.sound}`, no new axioms).
**Scout result:** the Phase 6u/6x substrate already provides a structural Dawson–Nielsen recursion
`skApproxC_generic` (structural ℕ-recursion ⟹ terminating/total), an *unconditional* per-level
super-quadratic error invariant `SkApproxCSuperQuadraticBound_generic_holds`, and a fully
unconditional 3-conjunct headline. W5 packages these as a named compile **function** with an
algorithm-level (not per-output) correctness contract:
- `cliffordTCompile : SU(2) → ℝ → FreeGroup (Fin 2)` — the compiler as a function.
- `cliffordTCompile_eq_recursion` — **termination**: compiler = `skApproxC_generic` at the explicit
  finite depth `skLevel_polylog ε`; structural ℕ-recursion bottoming out at the base finder ⟹ total.
- `cliffordTCompile_recursion_base` — **loop init** (depth 0 = base finder).
- `cliffordTCompile_loop_invariant` — **the loop invariant** (`SkApproxCSuperQuadraticBound_generic
  K_compose cliffordTGeneratingSet cliffordTBaseFinder_constructive`): ∀ depth n, ∀ U, the recursion's
  output approximates U within the super-quadratically shrinking `ε_seq K_compose (2ε₀) n` — each
  Dawson–Nielsen refinement step preserves+tightens the contract. UNCONDITIONAL.
- `cliffordTCompile_correct` — **correct-by-construction theorem (CompCert for Clifford+T)**: ∀ U,
  ∀ ε∈(0,ε₀], the output simultaneously meets (i) error ≤ ε, (ii) recursion-level length ≤
  polylog(1/ε), (iii) **actual output-word length** ≤ `skLength_at_baseCase cliffordTFiniteCover_maxLength
  (skLevel_polylog ε)`. Every output provably meets its ε/length spec — a theorem about the algorithm.
  UNCONDITIONAL, kernel-only.
- `cliffordTCompile_correct_example` — worked instantiation (U = 1, ε = ε₀).

**Documented decomposition-backed residual (NOT a gap in the correct-by-construction claim):** the
output-word-length constant in (iii) is the constructive ε₀-cover's `cliffordTFiniteCover_maxLength`,
not the Ross–Selinger optimal `O(log 1/ε)`. Tightening the constant needs the full Ross–Selinger 2014
ℤ[ω][1/√2] exact-synthesis development (~1.6–3k LoC, Lit-Search task on file) — a constant-improvement
follow-on, orthogonal to the algorithm-level correctness, which is complete and unconditional here.
Gate met (compile-function-level correctness theorem with ε + length as algorithm-level theorems).

- **Goal:** lift the verified-compilation arc (bundle D8: Solovay–Kitaev / Ross–Selinger / Clifford+T /
  Clifford+CCZ density + length bounds) from **per-output certification** to **correct-by-construction**: prove
  the *compilation algorithm itself* correct, so every output provably meets its ε/length spec ("CompCert for
  the gate compiler"). **Verdict: large but in-wheelhouse — the SK quantitative density/length bounds already
  shipped are the load-bearing foundation.**
- **Why:** a verified *compiler* (algorithm proven once) is a categorically stronger guarantee than per-output
  checking, and the quantitative-SK substrate (`solovayKitaev_dawson_nielsen_quantitative_*`,
  `SkApproxCSuperQuadraticBound_holds`, the generic-SU(d) cascade) is the hard half already done.
- **Bricks (sketch — warrants dedicated planning, likely Phase 6AO):** formalize the compiler as a function on
  the gate alphabet; prove the loop invariant (each refinement step preserves the approximation/length
  contract); discharge termination + the final ε/length bound from the existing quantitative theorems.
- **Gate:** a `compile`-function-level correctness theorem for at least one alphabet (Clifford+T) such that the
  output's ε/length bound is a theorem about the algorithm, not a per-instance check.

---

## Sequencing
W1 (composition lemma — small, unblocks everything else) → W3 (device bound, builds on W1) → W2 (network
capacity) → W4 (FDT floor) → W5 (the compiler-correctness sub-program; schedule its own phase when reached).
W1 is the highest-leverage small win (one lemma under many downstream constructions).
