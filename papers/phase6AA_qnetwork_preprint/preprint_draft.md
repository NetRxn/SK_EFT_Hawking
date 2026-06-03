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

## 2. Substrate (`lean/SKEFTHawking/QuantumNetwork/`, 17 kernel-only modules)

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

## 3d. Phase 6AE–6AF: a general mixed-state / channel layer

Beyond the Bell-diagonal/Werner protocol class, we have begun the general
density-matrix layer for *arbitrary-state* certification, built concretely on
`Matrix (Fin n) (Fin n) ℂ` (no Stinespring, no abstract C\*-algebra detour).

- **Trace norm and trace distance (`MixedState.lean`).** `IsDensityOperator`
  (positive-semidefinite, unit trace); `traceNorm A = ∑ √eigenvalues(AᴴA)` (Schatten-1
  norm) with nonnegativity, negation-invariance, and `traceDist ρ σ = ½‖ρ−σ‖₁`
  (nonnegative, symmetric, vanishing on equality).
- **The PSD→trace bridge (linchpin), PROVEN.** `traceNorm_posSemidef`:
  for positive-semidefinite `A`, `‖A‖₁ = tr A`. Proved kernel-pure with no continuous-
  functional-calculus instance, via `trace_cfc` (trace of `cfc f` = `∑ f(eigenvalues)`),
  the squaring identity `A·A = cfc(·²)A`, and a characteristic-polynomial / root-multiset
  argument (`{eigenvalues(AᴴA)} = {(eigenvalues A)²}`). Hence `traceNorm_density_eq_one`:
  every density operator has trace norm `1`.
- **Channel structure (`DiamondNorm.lean`).** The explicit `partialTrace` (with
  `trace_partialTrace`: `tr(partialTrace M) = tr M`) and the `choiMatrix`
  (Choi/Jamiołkowski channel–state duality) — the substrate the diamond norm builds on.

**Phase 6AF: the analytic core, discharged (kernel-pure).** The metric, fidelity, and
data-processing layer 6AE deferred is now proven — bypassing the machinery the 6AE note
flagged as absent (no von Neumann / Ky Fan / polar decomposition needed):

- **Trace-norm triangle.** `traceNorm_hermitian_triangle` (Hermitian case, via the
  positive-eigenvalue-sum decomposition `‖H‖₁ = 2·∑max(λᵢ,0) − tr H` plus a projection
  bound) and the *general* non-Hermitian `traceNorm_triangle` (via the Hermitian dilation
  `[[0,A],[Aᴴ,0]]` reindexed to `Fin(n+n)`, whose singular values double `A`'s — proven
  through the fact that the trace norm is a function of the characteristic polynomial alone).
  Hence `traceDist` is a genuine **metric** (`traceDist_triangle`) in `[0,1]` (`traceDist_mem_Icc`).
- **Operator modulus.** `absOp A = √(AᴴA)` with `‖A‖₁ = tr|A|` (`traceNorm_eq_trace_absOp`).
- **Uhlmann fidelity.** `sqrtFidelity ρ σ = ‖√σ·√ρ‖₁ = tr√(√ρ σ √ρ)` (the trace-norm form
  proven equal to the literal Uhlmann expression), with `F(ρ,ρ)=1` and symmetry.
- **CPTP data processing (`CPTPChannel.lean`).** For a Kraus channel `Φ(ρ)=∑ₖ Kₖ ρ Kₖᴴ`
  with `∑ₖ Kₖᴴ Kₖ = 1`: trace-norm contractivity `‖Φ(A)‖₁ ≤ ‖A‖₁` and **trace-distance
  contractivity** `D(Φρ,Φσ) ≤ D(ρ,σ)` (`traceDist_krausMap_le`, via the positive/negative-part
  split, no dual norm), plus density-operator preservation.
- **Choi positivity.** `choiMatrix_krausMap_posSemidef`: the Choi matrix of a Kraus channel
  is positive semidefinite (the channel–state-duality direction of Choi's theorem).
- **Diamond distance (`DiamondNormSup.lean`).** `diamondDist Φ₁ Φ₂ = sup_ρ D((Φ₁⊗id)ρ,(Φ₂⊗id)ρ)
  = ½‖Φ₁−Φ₂‖_◇`. After generalizing the trace-norm/CPTP layer to an arbitrary finite index
  (so it instantiates on the doubled space `Fin n × Fin n` for free) and proving the stabilized
  channel `Φ⊗id` is again CPTP (`isKrausChannel_tensorKraus`, via the Kronecker mixed-product
  identities), the supremum is well-defined from **boundedness alone** (`Real.sSup` needs no
  attainment; each term ∈ `[0,1]` since the stabilized outputs are density operators). Proven
  nonnegative, `≤ 1`, symmetric, zero on the diagonal, **and satisfying the triangle inequality**
  (`diamondDist_triangle`) — hence a genuine `[0,1]`-valued distinguishability *metric* on channels.
- **Fidelity range and Fuchs–van de Graaf lower bound (`FidelityBounds.lean`).** `F ≤ 1`
  (`sqrtFidelity_le_one`, an elementary double-Cauchy–Schwarz column assembly bypassing the absent
  Schatten-2 / matrix-Hölder layer) and the **Fuchs–van de Graaf lower bound** `1−F ≤ D`
  (`one_sub_sqrtFidelity_le_traceDist`, a Powers–Størmer argument routed through a matrix dual-norm
  bound `Re tr(H·R) ≤ ‖H‖₁` for the sign operator and the positive/negative-part identity
  `tr(√ρ·P) ≥ tr P²` — the non-commuting `|S| ≤ √ρ+√σ` Loewner step *removed*, not assumed).

- **Diamond-distance attainment (`DiamondNormAttainment.lean`).** The `diamondDist` supremum is
  proven **attained** by an optimal input density operator (`exists_diamondDist_eq`) — a genuine
  maximum. The binding ingredient is **trace-norm continuity** (`continuous_traceNorm`), via the
  Lipschitz bound `|‖A‖₁−‖B‖₁| ≤ ‖A−B‖₁ ≤ √n·‖A−B‖_F` (reverse triangle + Cauchy–Schwarz on the
  singular values, sidestepping the discontinuity of individual eigenvalues); the density-operator
  set is closed + bounded, hence compact in the finite-dimensional Frobenius normed space, and the
  extreme value theorem (`IsCompact.exists_sSup_image_eq`) delivers the optimizer.

- **Choi / maximally-entangled primal bound (`DiamondNormChoi.lean`).** `diamondDist_ge_maxEntangled`:
  the maximally-entangled (Choi) state `Ω = (1/n)|Ω⟩⟨Ω|` is a density operator
  (`isDensityOperator_maxEntangled`), and `le_diamondDist` at it gives `diamondDist Φ₁ Φ₂ ≥
  D((Φ₁⊗id)Ω,(Φ₂⊗id)Ω)` — the primal (one-sided) half of the Watrous Choi-SDP characterization, at
  its canonical primal feasible point, no SDP duality required.

- **Fuchs–van de Graaf UPPER bound (`FidelityUpperBound.lean`).** `traceDist_le_sqrt_one_sub_sqrtFidelity_sq`:
  `D ≤ √(1−F²)`, proven **purification-free** via Holevo–Helstrom + classical FvdG (no Uhlmann
  purification). The engine is the sharp **Schatten-2 Cauchy–Schwarz** `‖A·B‖₁ ≤ ‖A‖_F·‖B‖_F`
  (`traceNorm_mul_le`) — built with no Schatten/polar/SVD: a determinant-based polar unitary for
  invertible matrices + the matrix-CS keystone, extended to all matrices by a charpoly-roots
  perturbation. At the optimal Helstrom projector, `F ≤ √(p₀q₀)+√(p₁q₁)` (`sqrtFidelity_le_proj_bc`)
  and the classical `D²+BC²≤1` close `D²≤1−F²`. Both FvdG bounds + `F≤1` are now proven.

- **Choi operator-norm UPPER bound (`DiamondNormChoiUpper.lean`).** `diamondDist_le_choi_opNorm`:
  `diamondDist Φ₁ Φ₂ ≤ n·‖J(Φ₁)−J(Φ₂)‖_∞` (sharp constant `d=n`, the ℓ²-operator norm). With the
  primal lower bound this **sandwiches** the diamond distance by the Choi matrix — the formalizable
  content of the Watrous Choi-SDP characterization, no conic strong duality. Purification- and
  SDP-free: the difference output `T=(Δ⊗id)ρ` is **traceless** (trace-preservation of both channels),
  so `‖T‖₁ = 2·eigPosSum(T) = 2·tr(P₊T)`; a **vectorization identity** `tr(W·T)=tr(J·M(W,ρ))` moves
  the pairing onto the Choi matrix against a dual contraction `M(W,ρ)` (PSD via an explicit `N·Nᴴ`
  factorization through the PSD square roots of `W,ρ`), with `tr M(P₊,ρ)=tr(P₊(1⊗ρ_X)) ≤ n`; the
  operator-norm step `tr(J·M)≤‖J‖_∞·tr M` uses only the Loewner bound `J ≤ ‖J‖_∞·1`.

**Remaining frontier (honestly documented, no `sorry`/axiom).** The **full** primal=dual diamond-norm
Choi-SDP (Watrous) **equality** (needs conic strong duality; Mathlib has cone-dual definitions but no
zero-gap/Slater theorem at pin — both one-sided sandwiching bounds above are proven). Documented in
`Phase6AF_Roadmap.md`.

## 3e. Phase 6AG: operational quantum-network certification layer

The 6AE/6AF layer supplies functional-analytic *bricks*; Phase 6AG makes them *operational*.

- **Two-sided Choi sandwich (`DiamondNormChoiUpper.lean`).** `diamondDist_ge_choi_traceNorm`:
  `diamondDist K₁ K₂ ≥ (1/2n)·‖J(Φ₁)−J(Φ₂)‖₁`. Paired with the operator-norm upper bound this
  brackets the diamond distance by the Choi matrix in both directions,
  `(1/2n)‖J₁−J₂‖₁ ≤ ‖·‖_◇ ≤ n‖J₁−J₂‖_∞` — the formalizable content of the Watrous Choi-SDP
  characterization, with no conic strong duality. Proven via the maximally-entangled primal point
  (`(Φᵢ⊗id)Ω = (1/n)J(Φᵢ)` up to the trace-norm-invariant tensor-factor swap), plus a reusable
  PSD-square-root uniqueness lemma (elementary trace argument, no CFC instance) and trace-norm
  homogeneity.

- **General-state network monotonicity (`GeneralStateNetwork.lean`).** `traceDist_applyChain_le`:
  for ARBITRARY density-matrix states (not just Werner/Bell-diagonal), the trace distance between an
  end-to-end state and a target reference does not increase under any chain of CPTP channel steps
  (entanglement swaps / LOCC distillation / memory channels) — the data-processing inequality lifted
  to the network level, removing the uniform-Werner restriction.

- **Named single-qubit noise channels (`NamedChannels.lean`).** Kraus representations + CPTP proofs
  (`IsKrausChannel`) for the depolarizing, dephasing, and amplitude-damping channels operators
  benchmark against, with diamond-norm bounds to the identity for all three. For the
  Pauli-covariant channels the maximally-entangled input is optimal and the bound is *exact*:
  `diamondDist (dephasingKraus γ) (id) ≥ γ` (from `‖J(Φ_γ)−J(id)‖₁ = 4γ`) and
  `diamondDist (depolarizingKraus p) (id) ≥ p` (Choi-difference singular values `{2/3,2/3,2/3,2}`
  via the minimal-polynomial identity `B² = (4/3)(1−B)` ⟹ `|B| = 1 − ½B = ½·1 + (3/8)·BᴴB`,
  manifestly PSD, so `‖J−J‖₁ = 4p`). Amplitude damping is *not* Pauli-covariant, so the Choi input
  is not optimal; `diamondDist (ampDampKraus γ) (id) ≥ γ/2` is the certified lower bound from the
  Hermitian dual-norm keystone with a diagonal Loewner contraction aligned with the `±γ` diagonal
  Choi entries (`‖J−J‖₁ ≥ 2γ`).

- **Fidelity ↔ diamond-distance bridges (`GateFidelityBridge.lean`).** Composing the shipped
  Fuchs–van de Graaf state bound with the diamond least-upper-bound property:
  `1 − √F((Φ₁⊗id)ρ, (Φ₂⊗id)ρ) ≤ diamondDist(Φ₁,Φ₂)` for every stabilized input ρ — a small diamond
  distance certifies uniformly high input–output fidelity, and conversely.

- **General-`d` average-gate = entanglement-fidelity identity (`GateFidelity.lean`).**
  `avgGateFidelity_eq`: for every CPTP (Kraus) channel `Φ` on a `d`-dimensional system,
  `F_avg(Φ) = (d·F_e(Φ) + 1)/(d+1)`, where `F_avg = (1/|S^{2d−1}|)∫_S ∑ₖ|⟨ψ|Kₖ|ψ⟩|² dσ` is the
  Haar-average pure-state overlap and `F_e = (1/d²)∑ₖ|tr Kₖ|²` is the entanglement fidelity. This is the
  bench-data→worst-case bridge: it converts an averaged benchmark (e.g. a randomized-benchmarking
  fidelity) into the entanglement fidelity feeding the diamond-distance certificate above. Previously
  flagged as deferred pending Weingarten / unitary-2-design moment formulas absent from the pinned
  Mathlib, it is instead proven **constructively** — no twirl machinery — by computing the degree-(2,2)
  complex sphere moment `∫_S ψ̄_p ψ_q ψ̄_r ψ_s dσ = (δ_pq δ_rs + δ_ps δ_qr)·|S^{2d−1}|/(d(d+1))`
  (`complexSphereTensor`) along the Gaussian→sphere route (1-D Gaussian moments → multivariate
  Wick/Isserlis tensor → homogeneous polar reduction → `ℂ^d ≅ ℝ^{2d}` realification), contracting it
  against the Kraus matrices (`sphere_braKet_normSq`), and collapsing the dimension factor through trace
  preservation `∑ₖ tr(KₖᴴKₖ) = d` (`kraus_normSq_sum`). The unitary-2-design second moment is obtained
  as a theorem rather than imported. At `d = 2` the identity reduces to the single-qubit form
  `F_avg = (2·F_e + 1)/3`, consistent with — though not formally derived from — the separately-shipped
  teleportation result `teleportAvgFidelity_horodecki_unconditional` (which carries the same `(2x+1)/3`
  shape for the teleportation singlet fidelity, a distinct quantity).

- **Watrous weak-dual upper bound (`DiamondNormDual.lean`).** `diamondDist_le_dual_witness`: for any
  Hermitian witness `W ≥ 0` with `W ≥ J(Φ₁)−J(Φ₂)` (Loewner order),
  `diamondDist(Φ₁,Φ₂) ≤ ‖Tr₂ W‖_∞`. This is the *weak*-duality direction of the Watrous SDP — it
  needs **no** conic strong duality (no Slater/minimax/Fenchel), unlike the primal=dual equality
  (genuinely blocked at this Mathlib pin). The shipped `n‖J₁−J₂‖_∞` bound is the trivial witness
  `W = ‖C‖·1` (so `Tr₂ W = n‖C‖·1`); a non-trivial witness is strictly tighter. The **optimal**
  witness closes the envelope to the **exact** diamond distance for the covariant channels, with no
  twirl machinery: `diamondDist_dephasing_eq = γ` (witness `γ·v vᵀ`, `v = e₀₀−e₁₁`) and
  `diamondDist_depolarizing_eq = p` (witness the positive-part projector `C₊ = (2p/3)P₊`), both giving
  `Tr₂ W = γ·1` resp. `p·1`. Amplitude damping (non-covariant) gets the correct-direction two-sided
  bracket `γ/2 ≤ diamondDist(Φ_γ,id) ≤ γ + 1 − √(1−γ)` (`diamondDist_ampDamp_le`).

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
general density-matrix / trace-distance layer for arbitrary-state certification has since
been built (Phase 6AF, §3d): the trace-distance metric, operator modulus, Uhlmann fidelity,
CPTP trace-distance contractivity, and the diamond distance `½‖Φ₁−Φ₂‖_◇` are all proven
kernel-pure. The genuinely remaining extensions are (i) the full asymptotic DEJMPS convergence
basin (Macchiavello's non-monotone argument), and (ii) a few quantitative analytic items — the
Fuchs–van de Graaf bounds and the attainment/triangle/SDP properties of the diamond distance —
none needed for the protocol-level fidelity envelopes presented here.

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
