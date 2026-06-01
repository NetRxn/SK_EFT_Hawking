# Formally Verified Fidelity Envelopes and Operational Metrics for Entanglement-Based Quantum Networks

**John G. Roehm**
*NetRxn Foundation*
`jgroehm@gmail.com`

**Bridging preprint draft — SK_EFT_Hawking bundle D6 §6 (Phases 6AA–6AD).**
*Status: draft. Kernel-only Lean 4 / Mathlib4 substrate (pin `leanprover/lean4:v4.29.1`,
Mathlib `5e932f97`); all theorems verified with axioms ⊆ {propext, Classical.choice,
Quot.sound} — no `native_decide`, no project-local axioms. Source:
`lean/SKEFTHawking/QuantumNetwork/`. Numerics, figures, and a cross-validation gate:
`src/core/formulas.py`, `src/core/visualizations.py`, `scripts/validate.py --check
quantum_network`.*

## Abstract

We present a machine-checked Lean 4 / Mathlib4 substrate of fidelity-composition
results for entanglement-based quantum-network protocols, culminating in a
*model-independent end-to-end fidelity envelope* for entanglement-swap chains.
Working entirely in the Bell-diagonal / Werner fidelity-parameter representation —
explicit real-parameter expressions rather than density-matrix machinery — every
result is a kernel-checked theorem requiring no `native_decide` and no project-local
axioms. The headline is `swapChain_fidelity_envelope`: for a chain of `k`
entanglement swaps of Werner links with per-link fidelity `F ∈ [1/4, 1]`, the
end-to-end fidelity provably lies in `[1/4, 1]`, monotone in `F` and antitone in
chain length. To our knowledge this is the first formally verified protocol-level
fidelity bound for quantum networks. On this substrate we further verify the
operational network metrics — the BB84 secret-key rate (with the positive-key
crossover proven via the intermediate-value theorem rather than hardcoded), the
multipartite W₃-versus-GHZ₃ randomization advantage, and the Horodecki teleportation
fidelity `(2F+1)/3` whose sole analytic input, the Haar–Pauli integral
`∫_{S²}(⟨ψ|σ_k|ψ⟩)² dμ = 1/3`, is itself proven in the Bloch picture — so the
teleportation results are unconditional and axiom-free.

## 1. Motivation

Quantum-network simulators (e.g. QuISP, SeQUeNCe) are the standard tools for
predicting entanglement-distribution performance, and cross-validation studies
(Chung, Hajdušek, Van Meter et al., arXiv:2504.01290) have found quantitative
disagreements between them — on *connection-model-dependent timing*, while the
*fidelity* predictions agree under matched error parameters. A machine-checked,
model-independent envelope on the fidelity therefore provides a deductive
reference: any computed end-to-end fidelity falling outside the proven interval is
provably inconsistent with the Werner-swap-chain model. This complements the
exact W-state QFT measurement primitive of bundle D6 §6, on which it builds.

## 2. Substrate (`lean/SKEFTHawking/QuantumNetwork/`, 14 kernel-only modules)

- **Channels.** `fiberTransmission_eq_exp_neg_attenuationNp`: the
  dB↔Np attenuation identity `10^(−α_dB·L/10) = exp(−α_Np·L)`,
  `α_Np = α_dB·ln 10/10` (adopting dB as the engineering primitive, Np as
  derived; "0.046" is Np/km = 0.2 dB/km). Range + monotone-loss lemmas for the
  fiber-transmission and memory-coherence factors.
- **NumericalBounds.** Kernel-only two-sided enclosures of the `exp(−x)` loss
  factors via Mathlib's Bernoulli/Taylor exponential lemmas — no external
  interval library.
- **Swapping.** Werner swap fidelity `F_out = F₁F₂ + (1−F₁)(1−F₂)/3`
  (Briegel–Dür–Cirac–Zoller) with monotone composition.
- **Distillation.** The BBPSSW distillability flagship `bbpsswRecurrence_gt`:
  on `F ∈ (1/2,1)` purification strictly increases fidelity, the entire
  statement reducing to the single cubic `(1−F)(2F−1)(4F−1) > 0`; the DEJMPS
  analogue with the corrected diagonal `(00,11)=(I,Y)` Pauli-error pairing.
- **WStateRate.** The Fortescue–Lo finite-round W-state random-pair yield
  `D/(D+1)`, proved to surpass the single-copy specified-pair bound `2/3` for
  `D ≥ 3` (the `=1` asymptotic equality is an open conjecture and is *not*
  claimed).
- **EndToEnd.** The Werner-iterated end-to-end fidelity `(1+3wᵏ)/4`,
  `w = (4F−1)/3`, proved to satisfy the one-more-link swap recurrence
  (the swap is multiplicative in the Werner parameter).

## 3. The envelope theorem (capstone)

`swapChain_fidelity_envelope (F : ℝ) (k : ℕ) (hlo : 1/4 ≤ F) (hhi : F ≤ 1) :`
`  1/4 ≤ endToEndFidelity F k ∧ endToEndFidelity F k ≤ 1`,
together with monotonicity in per-link fidelity and antitonicity in chain
length. The proof is pure real analysis on the Werner parameter `w ∈ [0,1]`
(`wᵏ ∈ [0,1]`), with no density matrices, partial trace, trace norm, or diamond
norm — none of which are needed for the Bell-diagonal protocol class.

## 3a. Phase 6AB extensions (decay-inclusive + breadth)

The envelope is generalized along three kernel-only axes, all still in the
real-parameter representation:

- **Decay-inclusive envelope (`DecayEnvelope.lean`).** `memoryDegradedFidelity`
  applies the SeQUeNCe depolarizing memory model `F(t)=F·e^(−2t/τ)+(1−e^(−2t/τ))/4`,
  which **multiplies the Werner parameter by `e^(−2t/τ)`**; `decayInclusive_fidelity_envelope`
  then bounds the end-to-end fidelity of a `k`-swap chain of memory-degraded links in
  `[1/4,1]` for `F∈[1/4,1]`, `t≥0`, `τ>0` — the realistic-network generalization.
- **General Bell-diagonal swap (`BellDiagonalSwap.lean`).** The Klein-4
  (`ℤ₂×ℤ₂`) convolution map `bellDiagSwapA–D` with normalization (state→state),
  nonnegativity, the `[0,1]` target-fidelity envelope, and the `bellDiagSwapA_werner`
  bridge to the Werner swap.
- **Repeater breadth (`RepeaterChain.lean`).** The BDCZ nesting-doubling identity
  `endToEndFidelity_nest_double`; the teleportation-usefulness threshold
  `endToEnd_teleportation_useful` (`F_e2e>1/2 ⟺ wᵏ>1/3`, Horodecki); and the
  end-to-end QBER with monotone growth in chain length (the positive-key region left
  parametric — no hardcoded binary-entropy crossover).

A representative tight transcendental bound (`expNeg046_tight`, degree-5 Taylor
squeeze) certifies the fiber-loss factor numerically, kernel-only.

## 3b. Phase 6AC extensions (operational metrics: key rate, multipartite, teleportation)

Three operational network metrics are layered on the fidelity substrate, all
kernel-only and still in the real-parameter representation.

- **BB84 secret-key rate (`SecretKeyRate.lean`).** The Shor–Preskill asymptotic
  rate `bb84KeyRate e = 1 − 2·h₂(e)` (Shor & Preskill, Phys. Rev. Lett. 85, 441 (2000)), with the bits-renormalized binary entropy
  `binEntropyBit p = binEntropy p / log 2` (Mathlib's `Real.binEntropy` is in nats),
  so `r(0)=1`. The positive-key crossover is **proven, not hardcoded**:
  `bb84KeyRate_pos_iff_binEntropy_lt` states positivity as `h₂(e) < 1/2`,
  `bb84KeyRate_strictAntiOn` gives strict decrease in the error rate,
  `bb84_crossover_exists` produces a genuine `e* ∈ (0,1/2)` with `r(e*)=0` via the
  intermediate-value theorem, and `bb84_positiveKey_fidelity_threshold` composes this
  with the Phase-6AB end-to-end QBER (positive key iff `F_e2e > 1−e*`). The decimal
  `e* ≈ 0.11` is never asserted — it is the implicit root of `h₂(e)=1/2`.
- **Multipartite GHZ-vs-W (`MultipartiteComparison.lean`, Fortescue–Lo Thm 3.5).**
  `w3_beats_ghz_randomization_advantage` proves the W₃ randomization advantage over its
  specified-pair single-copy bound `2/3` is strictly positive (reducing to the shipped
  `fortescueLoYield_gt_two_thirds`), whereas GHZ₃'s is the cited modeling input `0`;
  `w3_asymptotic_specified_lt_one` shows the W₃ asymptotic specified rate `H₂(1/3) < 1`
  (via Mathlib's `binEntropy_lt_log_two`); and `fortescueLoYield_tendsto_one`
  (`D/(D+1) → 1`) matches the GHZ₃ rate asymptotically (optimality of `1` is the open
  Fortescue–Lo conjecture and is *not* claimed).
- **Horodecki teleportation (`Teleportation.lean`).** `teleportAvgFidelity F c = F + (1−F)·c`
  is the structural skeleton; the entanglement-utility threshold `teleport_beats_classical_iff`
  (`f_avg > 2/3 ⟺ F > 1/2`, Massar–Popescu) composes over the chain in `teleport_useful_over_chain`.

## 3c. Phase 6AD extensions (Haar integral discharged; Tier-1 anchors; general DEJMPS)

The Horodecki proof's one analytic step — the Haar–Pauli quadratic integral — is now
**proven**, and three reference-richness items are added, all kernel-only.

- **Haar–Pauli integral discharged (`HaarPauli.lean`).** Working in the Bloch picture
  (an explicit `Fin 2 → ℂ` spinor and `2×2` Pauli matrix, no density matrices), we prove
  the spinor identity `⟨ψ|σ_z|ψ⟩ = cos θ` (`pauliExpZ_blochKet`) and the spherical integral
  `∫_{S²}(⟨ψ|σ_z|ψ⟩)² dμ = 1/3` (`haarPauliZSqAverage_eq`, via the fundamental theorem of
  calculus on `∫₀^π cos²θ·sinθ = 2/3` and the solid-angle normalization). Mathlib at our pin
  lacks this integral; we prove it rather than assume it. Consequently the Horodecki theorems
  become **unconditional** — `teleportAvgFidelity_horodecki_unconditional` (`f_avg = (2F+1)/3`)
  and `teleport_beats_classical_iff_unconditional` hold with **no hypothesis and no axiom**.
- **W1′ Tier-1 anchors (`Rate.lean`).** The Calsamiglia–Lütkenhaus linear-optics Bell-state-
  measurement bound (`bsmSuccessProb_le_half_of_linearOptics`, success `≤ 1/2` vs the
  deterministic-BSM `= 1`) and the physics-only elementary-link rate `τ = L/(c·p_link)`
  (`linkRate`), with the expected-attempts factor `1/p` *derived* as the geometric-distribution
  mean (`geometric_expected_attempts`). Both are model-independent; handshake-inclusive link
  times remain model-dependent (Tier-3) and are deliberately not bounded.
- **General Bell-diagonal DEJMPS (`DEJMPSConvergence.lean`).** The full Klein-4 map with
  normalization, nonnegativity, and the pure-target fixed point; a monotone single-step increase
  on the phase-flip-only sub-basin (`dejmps_increase_phaseFlipOnly`); and a verified
  non-monotonicity witness (`dejmps_single_step_can_decrease`, `(3/5,0,0,2/5) → 13/25 < 3/5`)
  showing that `λ₀₀ > 1/2` does *not* guarantee a single-step increase — the full asymptotic
  basin rests on Macchiavello's (non-monotone) argument and is cited, not formalized.

## 4. Figures

Three figures (generated by `src/core/visualizations.py`, regression-checked by
`scripts/review_figures.py`) summarize the operational metrics:

- **Fig. 1** (`fig_qnet_bb84_key_rate`) — the BB84 secret-key rate `r(e) = 1 − 2·h₂(e)`
  versus end-to-end QBER, with the positive-key crossover `e* ≈ 0.11` located as the
  proven root of `h₂(e) = 1/2` (not hardcoded).
- **Fig. 2** (`fig_qnet_swap_chain_envelope`) — end-to-end fidelity of a `k`-swap Werner
  chain for several per-link fidelities, inside the kernel-proven `[1/4, 1]` envelope band.
- **Fig. 3** (`fig_qnet_w_vs_ghz`) — the Fortescue–Lo W₃ random-pair yield `D/(D+1)`,
  surpassing the specified-pair bound `2/3` for `D ≥ 3` and approaching the GHZ₃ rate `1`.

## 5. Relation to D6 and outlook

This substrate is absorbed into bundle D6 §6 (W-state QFT) as the protocol-level
extension of the exact cyclotomic W-state measurement primitive. The decay-inclusive
envelope, the general Bell-diagonal Klein-4 swap map, the repeater-recursion/QBER
breadth, the BB84 secret-key rate, the multipartite comparison, and the Horodecki
teleportation fidelity (with its Haar integral discharged) are all now in hand. The
substrate is finite-dimensional and Bell-diagonal by design; the genuinely remaining
extensions are (i) the full asymptotic DEJMPS convergence basin (Macchiavello's
non-monotone argument), and (ii) a general density-matrix / trace-distance / diamond-norm
layer for arbitrary-state certification — neither needed for the protocol-level fidelity
envelopes presented here.

## References

1. K. Chung, M. Hajdušek, R. Van Meter et al., "Quantum network simulator
   cross-validation," arXiv:2504.01290 (2025).
2. C. Zang, X. Chen, A. Kolar, A. Chung, M. Suchara, T. Zhong, R. Kettimuthu,
   "Entanglement distribution in quantum repeaters with optimized buffer time,"
   arXiv:2305.14573 (2023).
3. W. Dür and H. J. Briegel, "Entanglement purification and quantum error correction,"
   Rep. Prog. Phys. **70**, 1381 (2007) [arXiv:0705.4165].
4. C. H. Bennett, G. Brassard, S. Popescu, B. Schumacher, J. A. Smolin, W. K. Wootters,
   "Purification of noisy entanglement and faithful teleportation via noisy channels,"
   Phys. Rev. Lett. **76**, 722 (1996).
5. D. Deutsch, A. Ekert, R. Jozsa, C. Macchiavello, S. Popescu, A. Sanpera, "Quantum
   privacy amplification and the security of quantum cryptography over noisy channels,"
   Phys. Rev. Lett. **77**, 2818 (1996).
6. C. Macchiavello, "On the analytical convergence of the QPA procedure," Phys. Lett. A
   **246**, 385 (1998).
7. S. Fortescue and H.-K. Lo, "Random-party entanglement distillation in multiparty
   states," Phys. Rev. Lett. **98**, 260501 (2007); Phys. Rev. A **78**, 012348 (2008).
8. M. Horodecki, P. Horodecki, R. Horodecki, "General teleportation channel, singlet
   fraction and quasi-distillation," Phys. Rev. A **60**, 1888 (1999).
9. S. Massar and S. Popescu, "Optimal extraction of information from finite quantum
   ensembles," Phys. Rev. Lett. **74**, 1259 (1995).
10. P. W. Shor and J. Preskill, "Simple proof of security of the BB84 quantum key
    distribution protocol," Phys. Rev. Lett. **85**, 441 (2000).
11. J. Calsamiglia and N. Lütkenhaus, "Maximum efficiency of a linear-optical Bell-state
    analyzer," Appl. Phys. B **72**, 67 (2001).
12. N. Sangouard, C. Simon, H. de Riedmatten, N. Gisin, "Quantum repeaters based on atomic
    ensembles and linear optics," Rev. Mod. Phys. **83**, 33 (2011).
