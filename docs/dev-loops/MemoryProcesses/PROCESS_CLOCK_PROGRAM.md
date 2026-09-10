# Finite processes, coherent interventions and clocks

Status: implementation and independent component reviews complete; the full aggregate Lean build passed at `5238bafc`. Final extraction and substrate gate passed; independent integrated acceptance review remains in progress. This program extends the locally accepted calibrated-memory/coarse-graining increment `bbdbe40d`.

Root owns integration, slot admission and the primary notebook. Public changes remain local on the reviewed feature branch; no public push or main merge is included. Existing ADR-008 slots, continuity packets, planners and review writers govern execution. Workers read notebooks and report; they do not write the shared record.

## Delivered components and acceptance boundary

| Component | Reviewed candidate | Integrated source | Evidence |
|---|---|---|---|
| Finite instruments and realized process trees | `18d2e694` | `4adc216a` | Independent scientific review; aggregate build; initial complete dependency audit |
| Faithful finite Gibbs state and clock comparison | `c4dc26f2` | `8c04fca2` | Independent scientific review; aggregate build; initial complete dependency audit |
| Coherent process and reset witness | `3b10dbc7` | `1abbd043` | Independent scientific review; matching-slot diagnostics and capstone axiom checks; aggregate build |
| Exact process/coherent CPU models and floating clock diagnostic | `92c760d4` | `843a359c`, provenance update `b76a711f` | Independent 353-test run plus additional feedback, rational-coefficient and randomized-clock cases; executable code unchanged by provenance edit |
| D9 absorption preparation | Source-backed briefs and mapping | Local documentation | Independent preparation review; actual manuscript insertion remains behind D.0 |

Component reviews and builds do not by themselves close the final acceptance gate. Final evidence is recorded in the program audit. The source files must remain identical to the reviewed candidates through integration, and all new declaration closures must be audited after canonical extraction.

## Finite instruments and realized processes

Finite outcome-indexed Kraus families satisfying total normalization define instruments. Branch states remain unnormalized, including impossible outcomes. The implementation proves positivity, linearity, trace inequalities and total trace preservation. Complete positivity is represented by explicit finite spectator lifts. The system and environment may have different finite dimensions.

A fixed-depth, fixed-arity tree applies a normalized joint evolution followed by a local instrument. Later subtrees may depend on the observed outcome. History weights are nonnegative and normalized. Summing every normalized future continuation recovers its prefix probability; no-future-signaling follows from the actual maps rather than an assumed field. The concrete feedback fixture has two reachable outcomes and different subsequent preparations.

The source is `QuantumNetwork/FiniteInstrument.lean` and `FiniteInterventionProcess.lean`. This is a realized finite-process framework, not a general comb representation theorem. The exact rational CPU evaluator validates the entire protocol before evaluation. Full history enumeration is exponential in depth and also depends on matrix dimensions and rational bit lengths; no computational speedup follows from the framework alone.

## Coherent interaction consumer

For `U = (3/5) I - i (4/5) SWAP` and initial system/environment state `|10>`, two uninterrupted interactions give final system-one probability `49/625`. A resolved local computational-basis measurement between them gives the history table `[[144,256],[144,81]]/625`, final probability `337/625`, and contrast `288/625`. Changing the later interaction to identity preserves the earlier probabilities `16/25` and `9/25` when all future outcomes are summed.

Resetting only the system between interactions gives final probabilities `0` and `256/625` for the two initial histories, despite identical reset-system states. Resetting the environment removes the signal. The common-system-model exclusion consumes the existing binary separation theorem with a common normalized continuation and common binary effect.

`CoherentMemoryProcess.lean` uses the general tree evaluator. Explicit readout-equivalence theorems connect singleton paths with external binary readout to padded binary-outcome trees. Impossible outcomes and the generic feedback fixture are covered. Python clears both factors in its control; Lean clears the environment, which agrees on these already system-reset inputs. This does not establish equivalence on arbitrary inputs.

The coherent Lean constants cover the stated default coefficients. Other rational coefficient choices accepted by Python are separately tested computational instances. The reset contrast alone also has an incoherent-mixture realization; neither the interference comparison nor reset witness excludes every classical hidden-state explanation.

## Finite Gibbs clock comparison

For an arbitrary nonempty finite Hermitian Hamiltonian, construct the matrix exponential, its real positive partition function and a faithful trace-one Gibbs state. Prove the existing spectral matrix logarithm equals `-beta H - log(Z) I`. Independently defined modular and Heisenberg conjugations then agree at `t = -beta*hbar*s` for positive `hbar`. The mathematical construction permits real `beta`; the positive-temperature interpretation specializes to positive `beta`.

The source is `QuantumNetwork/FiniteGibbsClock.lean`. It proves linearity, identity/product/adjoint preservation, group and inverse laws, a nontrivial two-level phase/sign example, fixed degenerate blocks, trivial scalar-Hamiltonian flow and energy-shift invariance. Here `beta` has inverse-energy units, `hbar` has energy-times-time units, and `s` is dimensionless. Periodicity prevents treating the parameter relation as a globally unique clock readout. Faithfulness is essential; the logarithm-at-zero convention does not justify singular-state claims.

The CPU function reconstructs the density logarithm independently and reports floating residuals. It refuses numerical rank loss and nonfinite outputs. These diagnostics are not certified numerical error bounds or proofs of the input model. No infinite-dimensional modular, KMS-analytic, Lindblad, horizon or physical-clock identification is asserted.

## Publication and parallel follow-ons

D9's existing pending reviews and Stage 13 redo select the late-absorption protocol's D.0 prerequisite. The owner excludes pre-existing corpus repairs. Accordingly the delivered publication work is preparation: current section destinations, claim-to-source links and a figure specification. The manuscript and readiness verdicts remain unchanged. Follow `PUBLICATION_MAP.md` and `D9_ABSORPTION_BRIEF.md` when D.0 clears; do not treat these documents as a waiver.

The finite-clock result remains a separate physics follow-on until a substantive bridge to the memory/certification argument is established. The general process framework does not automatically extend the earlier calibration or suffix-approximation guarantees to arbitrary adaptive protocols. Broader horizon and noise applications remain future work.

CPU work stays on the ordinary workstation. CUDA is deferred unless a required simulation cannot complete in an overnight run of about ten hours; long runs must remain asynchronous and off unrelated work's critical path. No new harness, hardware integration, commercial release or publication submission is included.
