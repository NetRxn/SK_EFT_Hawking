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

## 4. Relation to D6 and outlook

This substrate is absorbed into bundle D6 §6 (W-state QFT) as the protocol-level
extension of the exact cyclotomic W-state measurement primitive. Natural
extensions (deferred): the fidelity-under-continuous-decay envelope (composing the
transcendental loss bounds with the swap chain), the general Bell-diagonal Klein-4
swap map, and the Horodecki teleportation fidelity (which requires a Haar-integral
lemma). The substrate is finite-dimensional and Bell-diagonal by design; arbitrary
mixed-state certification would require the general density-matrix layer.
