# Finite processes, coherent interventions and clocks

Status: implementation and independent component reviews complete; the full aggregate Lean build passed at `5238bafc`. Final extraction, substrate gate and fresh independent integrated review passed. Root accepts this bounded increment locally. This program extends the locally accepted calibrated-memory/coarse-graining increment `bbdbe40d`.

Root owns integration, slot admission and the primary notebook. Reviewed feature history is checkpointed remotely and exposed through draft integration PRs. Main merge and publication acceptance require their separate gates. Existing ADR-008 slots, continuity packets, planners and review writers govern execution. Workers read notebooks and report; they do not write the shared record.

## Delivered components and acceptance boundary

| Component | Reviewed candidate | Integrated source | Evidence |
|---|---|---|---|
| Finite instruments and realized process trees | `18d2e694` | `4adc216a` | Independent scientific review; aggregate build; initial complete dependency audit |
| Faithful finite Gibbs state and clock comparison | `c4dc26f2` | `8c04fca2` | Independent scientific review; aggregate build; initial complete dependency audit |
| Coherent process and reset witness | `3b10dbc7` | `1abbd043` | Independent scientific review; matching-slot diagnostics and capstone axiom checks; aggregate build |
| Exact process/coherent CPU models and floating clock diagnostic | `92c760d4` | `843a359c`, provenance update `b76a711f` | Independent 353-test run plus additional feedback, rational-coefficient and randomized-clock cases; executable code unchanged by provenance edit |
| D9 absorption preparation | Source-backed briefs and mapping | Local documentation | Independent preparation review; actual manuscript insertion remains behind D.0 |

Component reviews and builds do not by themselves close the final acceptance gate. Final evidence is recorded in [the program audit](../../audits/2026-09-10-finite-process-clocks.md). The source files must remain identical to the reviewed candidates through integration, and all new declaration closures must be audited after canonical extraction.

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


## Continuous growth and field integration

The earlier adaptive robustness module remains accepted: one common complete
feedback tree bounds full-history total variation and event errors by initial
trace distance without a depth factor. Its actual collision/SWAP-feedback
consumer is retained. The new `FiniteGibbsHistoryPreparationBounds.lean`, source
`5a2a7ee9`, connects that bound to actual reflected Gibbs histories.

The perturbed kernel is defined by the same chronological process started from
an arbitrary density state. Complex pairing error is at most twice the initial
trace distance times the two coefficient sup norms, without a history-count
factor. Stationary positivity bounds the real quadratic defect and imaginary
part; it does not make the perturbed kernel positive. Actual Gibbs reset warm-up
reduces trace distance exactly by its exponential retention.

A nonuniform three-level example has strictly unequal transposed entries after
every finite warm-up. It remains non-Hermitian and cannot define the proposed
positive quotient. Stationary input, zero waiting/rate and repeated-time guards
are proved. All 64 authored declarations and 73 namespace names have original
ordinary-axiom audits and independent source review. Canonical extraction retains
69 of those namespace names plus four generated equations for existing history
index equivalences, adding 73 records. Combined public-cycle reconciliation and
validation are recorded in `docs/audits/2026-09-11-finite-positive-kernel.md`.

The source and original evidence pass independent review. The combined public
cycle passes aggregate builds, inventory reconciliation, independent integrated
review and the substrate gate at `6bf92d2f`; root accepts the bounded increment
locally. Closing documentation and final build receipts are checked separately.
Publication and D9 absorption prerequisites remain unchanged.

`FiniteAdaptiveMapPerturbation.lean` now implements the actual-map perturbation
contract, including retained joint-memory branch distance, changed-input control,
full-history variation, independent Kraus mixtures and the exact feedback error
`1-(1-p)^m`. The equal-history/unit-memory-distance witness prevents replacing
joint-state control with outcome probabilities. Original proof evidence and
independent source review pass. The combined finite-depth field and adaptive
increment is locally accepted at `c00e8974` after the aggregate build, inventory
reconciliation, independent integrated review and substrate gate. See
`docs/audits/2026-09-11-finite-positive-kernel.md` for scope and gate details.

`FiniteAdaptiveMixtureSurvival.lean` now constructs positive remainders for
actual independently mixed evolution and instrument maps. Its changed-input
bound is `w*traceDist(X,Y) + 1-w`, where w is the product of the surviving
ideal weights. The retained-memory consumer has exact distance `p+q-p*q`,
while history variation is q; arbitrary-depth feedback attains `1-(1-p)^m`.
A coherent-channel witness excludes a positive ideal component for every
positive weight, keeping the mixture mechanism's scope explicit.

`FiniteNontracialPauliReflection.lean` now supplies the fixed faithful qubit
state, actual normalized replacement instrument and four-event reflection
identity. Its quotient uses the Q-sandwich Hilbert-Schmidt feature, with rank
four at positive central retention and rank one at complete central reset.
Literal outer marginals, centered complex modes and the two original failure
witnesses are proved. It does not extend arbitrary-depth tracial consistency
to arbitrary nontracial schedules.

Both sources pass independent source/evidence review and are included in the
aggregate build at `8124e489`. Independent inventory reconciliation and the
substrate gate pass; existing paper-corpus failures remain. The final controller build at inventory revision `8865dade` passes.
Independent integrated review passes and root accepts the bounded
implementation cycle locally. No diamond norm,
postselection, unmodeled ancilla, continuum reconstruction, physical-clock
identification or publication acceptance is asserted.

## Attained readout discrimination and retained-memory advantage

`QuantumNetwork/FiniteAdaptiveReadoutDiscrimination.lean` now supplies the
attained binary discrimination theorem for the actual joint history and
terminal-memory branch families. For equal priors, the optimum over every
history-dependent binary effect is `(1-distance)/2`. Realized normalized
readouts include zero-probability branches, unequal history masses and complex
state examples. Positivity and total normalization are derived for the actual
finite process tree.

The depth-two correlation witness has equal history distributions and equal
unconditional terminal states. History-only classifiers and a constant terminal
effect have error one half, while a joint history/memory readout has error zero.
Its physical computational-basis measurement can be fixed, with history used
only to relabel the classical result. The witness certifies retained correlation
and does not establish a need for adaptive physical measurements.

Actual mixture consumers give attained joint and universal randomized
history-only optima, including the strict quarter-rate gap `9/32 < 3/8`.
Arbitrary-depth noisy feedback attains error `(1-p)^m/2`; zero depth, zero noise
and full noise endpoints are included. This is an equal-prior finite-model
readout result with explicit dimensionless rates, not a physical-clock or
quantum-advantage claim.

Independent complete source and original-evidence review pass. The normal
source integration and authoritative aggregate build at `68a07163` include the
separate readout module. Root canonical reconciliation and independent integrated
source/inventory review pass. Quiet-state full substrate validation passes with
paper-corpus failures reported. The canonical Python suite has 7,273 passed and
32 failed; all-tests and complete-pipeline acceptance remain open. See
`docs/audits/2026-09-11-finite-positive-kernel.md` for the combined finite-field
integration and evidence boundary. D9 absorption and publication prerequisites
remain unchanged.

## Robustness of attained readouts under actual map perturbations

`QuantumNetwork/FiniteAdaptiveReadoutRobustness.lean` bounds the change of
attained equal-prior readout error by half the sum of the two retained
joint-branch family distances, comparing each hypothesis with its own
perturbation. History-only optima are bounded by half the sum of the two
corresponding full-history total-variation distances. Both bounds consume the actual normalized finite process maps, and apply
to changed initial density states and independently mixed evolution and
instrument maps. The mixture survival product controls the error without
replacing retained joint memory by outcome probabilities.

The module includes unequal history masses, normalized sign readouts, zero
branches, complex qubit mixtures and the endpoint guards of the perturbation
estimate. Complete source and original-evidence review pass for this bounded
component. Its source is integrated at `8e8250a4`; the authoritative aggregate
build passes after the import-placement repair at `69e0bcc6`. Canonical
extraction retains all 92 authored names, six generated namespace helpers and
one generated congruence helper attributed to the existing discrimination
module, adding 99 records. All 45,482 previous full inventory records are
unchanged. The new records have only the allowed core axiom closures. Independent
review verifies this bounded imported-source, inventory, counts and atlas
checkpoint.

The robustness module now also implements the noisy correlation and mixed-memory
consumers, including physical readout tables and the distinction between fixed
and reoptimized symmetric readouts. For symmetric mixing, the fixed rule has
error `r`, while reoptimization attains `min(r,1-r)`; the endpoint guards and
normalized physical rules are proved. The source-present consumers therefore
extend the earlier generic estimate with concrete margins.

`QuantumNetwork/FiniteAdaptiveGibbsReadout.lean` supplies the finite Gibbs
spectator warm-up classifier. Its actual warm-up maps have exact retained
distance, and concrete two- and three-level measurements attain the stated
all-effect and randomized-classifier bounds. Warm-up readout discrimination
does not establish positivity of the perturbed reflected kernel.
No quantum advantage, physical-clock identification or continuum claim follows.

The latest measured canonical Python run, before this component's integration,
has 7,285 passed, 23 failed, seven skipped and 92 deselected. Fresh quiet full
validation of the candidate at `69e0bcc6` measures 89 checks: 71 pass and 18
fail, with 1,147 warning details and no check errors. The measured Lean build,
source, zero-sorry, axiom, counts, graph and atlas checks pass. The same 18 failed
check names recur; this does not establish identical diagnostics or waive any
failure. Fresh all-tests acceptance, the full pipeline, D9 absorption and
publication prerequisites remain open.

## Chronological field evolution and retained environment memory

`QuantumNetwork/FiniteNontracialSchedule.lean` constructs actual chronological
Kraus composition for arbitrary finite lists of nonnegative rates and durations.
The reset dose `G` and dephasing dose `D` yield population retention `exp(-G)`
and coherence retention `exp(-(G+D))`. The closed action is proved for every
complex matrix, with reverse observable pullback and trace duality. Its generator
is tied to actual jump operators; the physical derivative at zero is one-sided.
Empty schedules, zero rates, zero durations and a distinct two-rate numerical
example are included. Complete source and original-evidence review pass.

`QuantumNetwork/FiniteNontracialEnvironmentLift.lean` constructs the actual
second-factor lift `I_S tensor K_E`. Its identities hold for arbitrary joint
matrices, including correlated inputs. Environment-only evolution preserves the
literal system partial trace; identical system-local instrument branches
propagate equality of that marginal. Actual Gibbs reset, computational dephasing
and the primitive two-rate action are proved. Distinct stationary system
preparations have joint trace distance one, excluding strict global contraction;
a local-reset/SWAP counterexample guards later noise cuts. Complete scoped-core
source and original-evidence review pass.

The bounded foundations passed authoritative builds, imported inventory and
independent integrated review. The schedule specializes the environment lift
to arbitrary joint matrices. For Hermitian inputs with equal system marginals,
trace distance contracts by population retention. The same premise is required
at every history branch for the retained-family distance and all-effect error
bound. Literal system-local instruments and environment-only channels propagate
the premise. A shared normalized continuation earns ordinary contractivity;
another retention factor requires a separately verified later noise cut.
Complete M2 source, original evidence, imported inventory and canonical metadata
passed independent integrated review. Acceptance retains the branchwise premise
and the distinct downstream noise-cut requirements.

`FiniteNontracialScheduleTransfer.lean` constructs the chronological observable
pullback on the accepted weighted history quotient. Actual central and split
Kraus steps realize the scheduled kernel and three distinct effects. Halving
every duration gives square-root retention coefficients. The inserted-kernel
norm equals the half-schedule transfer norm, while the full transfer retains
squared decay factors. Exact mode norms, complete central reset, and
state/observable and metric distinctions are proved. The assigned mathematical
bridge passed complete source, original-evidence, imported inventory, canonical
metadata and independent integrated review within its mathematical scope.

`QuantumNetwork/FiniteNontracialMemoryReadout.lean` derives the actual depth-two
Keep/Flip branches, including impossible histories, and their normalized
correlation-readout tables. Retained distance is population retention; the named
physical readout attains error `(1-alpha)/2` and the all-effect optimum.
History-only and common terminal-only consumers have error `1/2`. Their
restriction is blindness to the retained correlation, whose readout has a
computational-basis implementation.

`QuantumNetwork/FiniteNontracialCoherentReadout.lean` derives the actual schedule,
SWAP and complex projective observation of the noncommuting qubit preparations.
Independent upper and lower arguments give retained distance and history
variation `beta/sqrt(2)`. The physical decision attains error
`(1-beta/sqrt(2))/2`, with separate all-effect and randomized-history optima.
The same preparations, schedule and SWAP followed by computational observation
have identical branch families and error `1/2` for every permitted readout.
Assigned complex controls include zero-dose identities, exact logarithmic
witnesses, a genuine full environment Gibbs reset, system-only preparation and
identical inputs.

Both consumer packages passed complete independent source and original-evidence
review and normal source absorption. Their aggregate imports compile through the
registered build. Exhaustive actual imported inventory, canonical metadata and
both complete consumer scopes passed independent integrated review. Canonical
metadata preserves the prior full records and the existing producer's kind and
type-rendering distinctions. Final committed closing review and the registered
build passed at `8191023d` within this consumer component's scope.

`QuantumNetwork/FiniteNontracialMemoryScheduleControls.lean` adds actual empty,
zero-rate, zero-duration and logarithmic controls with complete physical tables,
normalized laws and attained optima. A normalized environment reset after the
Flip intervention erases the retained distinction; system-only preparation after
the first recorded measurement preserves it. Identical stationary inputs use the
same tree. Both normalized intervention orders have exact distance
`7*(1-alpha)/25`, positive for positive population dose. Literal non-Hermitian
state, observable, GKSL and effect identities retain their distinct domains.

`FiniteNontracialOperationalCompatibility.lean` connects the independently proved
physical readout values to actual weighted-history transfer and mode norms.
Actual ordinary, scheduled and half-duration trees realize three distinct
effects. Half-time insertion retains a single damping factor in squared norms;
full-time transfer retains its square. The negative quotient generator is tied
to actual primitive GKSL duality. Positive-dose physical witnesses coexist with
the independent central-reset quotient endpoint; side-reset, carrier, metric and
state/observable guards preserve the separate constructions.

Both additions passed complete independent source, mathematics and original
evidence review, followed by normal source commits and controller integration.
Their production imports compile through the registered aggregate build. Exhaustive
actual imported inventories, full canonical records and all six derived metadata
files passed independent whole integration review. Normal metadata commit
`47e2e4a6` preserves the reviewed candidate bytes. The complete original two-rate
contract retains its chronological, branchwise and Hermitian premises and all
zero-dose, reset, ordering, metric, half-time and non-Hermitian controls.
Shared decay factors do not identify the distinct carriers or their norms, and
finite dose sums do not identify physical or modular clocks. The final registered
build and independent committed closing verification passed at `046a3387` for
the complete bounded finite two-rate target. Broader project, scientific, paper,
publication and apex gates remain separate; existing failures are retained without
waiver.

The next complete finite growth target has independent enabling-design review.
`QuantumNetwork/FiniteNontracialThermalPhase.lean` supplies its complete thermal
and chronological evolution foundation. The existing faithful reference equals
an independently constructed Gibbs state for a non-scalar diagonal Hamiltonian.
The same normalized unitary-after-noise family equals the actual nonzero-Hamiltonian
GKSL propagator on arbitrary complex matrices. Forward state and reverse observable
phases have opposite signs. Literal timed schedules, separate free pulses and
unchanged spectator marginals retain their explicit scale, periodicity, zero-dose
and Hermitian norm premises.

The entire source and proof originals passed independent whole review, and normal
source commit `c8600589` preserves the reviewed bytes. Aggregate import registration
makes the module reachable by the canonical build. The registered build, exhaustive
actual imported inventory, canonical metadata and independent integration review
remain required. Source acceptance alone does not accept the complete growth target.

The remaining consumer work connects phase-sensitive retained-memory observations
to the accepted weighted history metric. Fixed and co-rotated instruments owe
separate complete laws and attained optima. The target includes actual reflected-kernel
nonpositivity under phase; dissipative positivity does not transfer to a
unitary-composed map. Group and inverse laws belong to the phase isometry; the
damped transfer retains its normality and adjoint obligations. The current two-rate
contract, separately typed recursive-time contract and broader gates remain distinct.
