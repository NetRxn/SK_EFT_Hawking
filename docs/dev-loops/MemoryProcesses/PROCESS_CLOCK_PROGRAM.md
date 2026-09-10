# Finite processes, coherent interventions and clocks

Status: authorized for supervised execution; exact scientific packages undergoing admission review. Builds on locally accepted calibrated-memory/coarse-graining increment bbdbe40d. Root owns integration and notebook; public changes stay local, with reviewed feature-branch integration only.

## Parallel scope

1. General finite realized process-and-intervention framework, with a coherent-interaction example as a consumer. Explicit state validity, instrument normalization, ordering/causality and non-vacuous operational claims. Do not claim a full comb representation theorem without proving it.
2. Bounded finite Gibbs/modular-flow comparison with Heisenberg evolution. State signs, units, faithfulness and degeneracies explicitly; no physical horizon identification by naming convention.
3. Absorb accepted memory results into D9 using the existing manuscript review and repair graph. Gate the changed claims; unrelated old paper failures remain outside scope.

Each package begins with source-grounded theorem/claim admission and an independent review. Existing ADR-008 global slots limit simultaneous proof work. Root admits slots, integrates, builds, audits complete new axiom closures and synchronizes evidence. Workers receive explicit ownership and notebook references and report rather than writing the shared notebook. No extra harness, public push, CUDA or commercial release is authorized by this plan. CUDA remains conditional on a required CPU simulation exceeding ten hours.

## Closure

Exact package acceptance criteria and evidence will be added after admission. Distinguish implemented science, reviewed manuscript changes and publication readiness. Independent reviews and actual gates close each package; no proposed work is complete merely because it appears here.

## Finite clock contract (independently admitted)

For an arbitrary nonempty finite index type, Hermitian H, real beta>0 and hbar>0, construct the matrix exponential exp(-beta H). Define real Z=Re(trace(exp(-beta H))), prove positive Z and that the complex trace is its real embedding. Define rho=Z^-1 exp(-beta H), prove positive definiteness and trace one, and prove the existing spectral matrixLog(rho)=-beta H-log(Z)I. Define modular conjugation by exp(i s matrixLog(rho)) and physical Heisenberg conjugation by exp(i t H/hbar) independently. Prove sigma_s=alpha_(-beta*hbar*s), complex linearity, identity/multiplication/adjoint preservation, group and inverse laws. beta has inverse-energy units, hbar energy*time, s dimensionless.

Non-vacuity: for H=diag(0,Delta),Delta>0, E01 acquires phase exp(i beta Delta s); at s=pi/(beta Delta), E01 and PauliX change sign. Degenerate energy blocks fixed, scalar H yields maximally mixed state and trivial flow, energy shift H+cI leaves rho andboth flows unchanged. Periodicity means parameter comparison is not globally unique clock readout. Faithfulness is necessary; log-zero convention does not justify singular-state modular claims. No infinite modular/KMS analyticity/Lindblad/horizon identification claimed.

Proof ownership: new QuantumNetwork/FiniteGibbsClock.lean, with a separate helper file only if source dependencies justify it. Source-inspected reuse: MixedState spectral calculus, QuantumRelativeEntropy matrixLog, Mathlib matrixexponential. GibbsVariational does not already construct Gibbs states. Independent admission confirmed the sign, real partition definition and non-vacuity; kernel admission remains a separate step.

## Finite instruments and processes (independently admitted)

Finite outcome-indexed Kraus families with total sum K-adjoint*K=I define an instrument. Branch states remain unnormalized, including impossible zero branches. Prove PSD/linearity, complete positivity by explicit finite spectator lifts, trace inequalities and totaltrace preservation. Lift a system instrument with identity on an arbitrary finite environment, not only equal dimensions. A finite depth-indexed tree applies a normalized joint evolution and then a local system instrument, allowing outcome-dependent later subtrees. Prove history weights nonnegative and normalized and that summing any normalized future subtree recovers its prefix probability. Derive no-future-signaling from these actual maps; do not assume it as a field.

Proof ownership: QuantumNetwork/FiniteInstrument.lean and FiniteInterventionProcess.lean sequentially in one slot. Subsequent CoherentMemoryProcess.lean must consume those APIs. With U=(3/5)I-i(4/5)SWAP and initial|10>, two coherent steps have finalsystemone probability49/625. A local Zinstrument between the two steps gives table[[144,256],[144,81]]/625 and probability337/625, contrast288/625. Earliermarginals16/25,9/25 remain fixed when laterU is changed toidentity. Reset only S between U steps yields history contrast256/625 with equal reset S states; reset-E control removes it. The interference comparison is required because the reset contrast alone matches an incoherent mixture. Neither example certifies quantum-only memory against all classical models.

CPU follows a frozen protocol API, using exact rational complex components, subnormalized branch states and weights, explicit invalid-dimension/normalization checks and zero/adaptivecases. Full tree leaf enumeration is exponential in the worst case; no general speedup claim. Root owns canonical formulas integration and aggregate imports.

## D9 admission boundary

Current D9 has prior Stage9/10/13 pending and Stage 13 redo; existing late-absorption D.0 requires restoring readiness before inserting new manuscript content. Owner excludes preexisting corpus repairs. Accordingly this track first prepares a source-backed section/figure brief and fixes the affected destination mapping to current stable labels: sec:params for characterization, sec:worked for counts and power, sec:protocol for suffix bounds; limits and related work link sec:breaks/sec:related. Actual append remains separately gated and must not be represented as complete. No silent corpus cleanup or bypass of D.0.

Independent statement review reproduced all coherent-model constants. Acceptance additionally requires a zero-probability branch and a genuinely outcome-dependent continuation. Prefix comparisons fix the earlier operations and initial state and sum over every future outcome; postselecting future outcomes is a different statement. Every reachable feedback continuation must be trace preserving. The concrete example must use the tree evaluator, not merely adjacent matrix identities.
