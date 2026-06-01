# Formally Verified Fidelity Envelopes for Entanglement-Based Quantum Networks

**Bridging preprint draft — Phase 6AA (SK_EFT_Hawking / bundle D6 §6).**
*Status: draft. Kernel-only Lean 4 / Mathlib4 substrate; all theorems verified
with axioms ⊆ {propext, Classical.choice, Quot.sound}.*

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
fidelity bound for quantum networks.

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

## 2. Substrate (`lean/SKEFTHawking/QuantumNetwork/`, 8 kernel-only modules)

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
- **Horodecki teleportation (`Teleportation.lean`, probe-gated).** Mathlib at our pin
  provides the sphere-Haar machinery but not the Pauli-quadratic integral
  `∫_{S²}(⟨ψ|σ_k|ψ⟩)² dμ = 1/3`. Rather than introduce a project-local axiom we carry the
  value as the explicit hypothesis `HaarPauliConstant` and prove the algebra around it:
  `teleportAvgFidelity F c = F + (1−F)·c` is the structural skeleton,
  `teleportAvgFidelity_horodecki` recovers `(2F+1)/3` under the hypothesis, and the
  entanglement-utility threshold `teleport_beats_classical_iff` (`f_avg > 2/3 ⟺ F > 1/2`,
  Massar–Popescu) is composed over the chain in `teleport_useful_over_chain`. **Zero** new
  project-local axioms.

## 4. Relation to D6 and outlook

This substrate is absorbed into bundle D6 §6 (W-state QFT) as the protocol-level
extension of the exact cyclotomic W-state measurement primitive. Natural
extensions (deferred): the fidelity-under-continuous-decay envelope (composing the
transcendental loss bounds with the swap chain), the general Bell-diagonal Klein-4
swap map, and the Horodecki teleportation fidelity (which requires a Haar-integral
lemma). The substrate is finite-dimensional and Bell-diagonal by design; arbitrary
mixed-state certification would require the general density-matrix layer.
