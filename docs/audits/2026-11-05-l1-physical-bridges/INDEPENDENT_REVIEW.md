# Independent L1 bridge inventory

Read-only review of candidate `8b6da1c2fd87f07b3dde29e68e590ca324887d42`, branch `codex/l1-physical-bridges-20261105`, 2026-11-05. No builds, runtime probes, leases, source edits, shared-notebook writes, or external contact. Read project AGENTS, CLAUDE and wave stages; inspected relevant roadmap passages, exact theorem bodies and the current publication notebook's scientific/ownership sections. This is an inventory review, not independent execution of the physics or an acceptance review of the parent's unwritten roadmap.

## Roadmap scope corrections

The lexical screen is a breadth aid, not the dependency closure. `L1` also names a topological tower level, dashboard zoom level, and path length; Phase5qG and Phase5v hits do not establish a publication-L1 dependency. Shared bootstrap references in Phase6EA–EE do not make the metrology series a prerequisite.

Additional actual connections worth carrying in the successor:

* **Phase6o Wave1b:** explicit Kerr-Schild/BCJ map to L1, D3 section6, F section6, and E1 ringdown; roadmap lines604 and623. The mapping calls this alternative substrate context, not a repair of L1's speed law. It requires a scoped context/consumer pass.
* **Phase6r and Phase6r-prime Wave4:** additive APS-eta/inflow content explicitly targets L1 alongside D2; held unified absorption is recorded in Phase6r-prime lines415 and1148. Do not infer that this anomaly/inflow layer supplies tensor dynamics. Respect its absorption ownership and source-held status.
* **Phase6c Wave3 / Phase5x:** matter coupling and EP comparison share `VestigialGravity` and classification. Phase5x explicitly says the eta magnitude is supplied externally, not derived from gap-equation parameters. Its 2026-10-17 overlay retains the same physical ADW correspondence gap and independent D5 cosmology obligations. A new universal matter/light coupling result could affect these consumers, but L1 does not need a complete dark-sector cosmology fit.
* **Phase6b Wave3:** vestigial inflation consumes susceptibility and linearized gravity. Audit as a downstream assumption consumer if susceptibility/state changes; do not add inflation as a prerequisite to L1.
* **Phase6f:** concrete tetrad/metric algebra is reusable for tensor matching. It does not itself derive the tetrad from the microscopic action.
* **Phase6g:** the lexical screen did not flag it, but propagator/wavepacket work should inspect `WaveEquation1D.lean` and `CauchyProblem.lean`. Their limited existing scope is important: explicit scalar wave solutions / structural well-posedness predicates, not full tensor hyperbolicity, nonlinear Fourès-Bruhat, or L1 retarded transport.
* **Phase6q:** the screen's generic placement hit understates actual toolkit relevance. `DKMBootstrap/Predicates.lean` contains a retarded imaginary-correlator API and positivity/analyticity assumptions; it is worth source/type review before building new response abstractions. It supplies no physical L1 tensor identification.
* **Phase6i, Phase7/7a and AttributionContentSweep:** publication absorption/claims machinery and stale readiness claims; use current canonical reviews instead of historical green headers.

Core ownership remains Phase5y/6a/6e current overlays, Phase5d plus Phases3/4/5 foundations. This review does not claim every portfolio roadmap was depth-read: it checked the provided full-corpus screen and followed the above substantive interfaces in source.

## Concrete reusable Lean substrate and limits

* `SKEFTHawking.QuantumNetwork.IsDensityOperator` (`QuantumNetwork/MixedState.lean:36`) is concrete `Matrix` positivity plus unit trace. `psdSqrt`, `psdSqrt_posSemidef`, `psdSqrt_isHermitian`, `psdSqrt_mul_self` in that file provide the finite positive square-root carrier. Existing proof bodies use Mathlib spectral calculus rather than posited physical fields.
* Pinned local Mathlib `LinearAlgebra/Matrix/PosDef.lean`: `Matrix.PosSemidef.submatrix`, `dotProduct_mulVec_nonneg`, `conjTranspose_mul_mul_same`, `mul_mul_conjTranspose_same`, `trace_nonneg`; `Analysis/Matrix/PosDef.lean`: `Matrix.PosSemidef.trace_eq_zero_iff`, `det_nonneg`, `re_dotProduct_nonneg`. These suffice for finite Gram positivity and a zero-diagonal/nonzero-off-diagonal obstruction without inventing another PSD type.
* `SKEFTHawking.VestigialSusceptibility.W6Ext.chi_RPA_closed_form` and `chi_RPA_sign_stable` prove algebra conditional on a bare response and coupling. `KuboViscosity.ζ_pos` is a structure field; `kubo_zeta_pos` unpacks it. Neither is a microscopic physical state/Kubo derivation, and stable positivity does not derive a bounded [0.1,10] interval.
* `GravitationalWaves.c_GW_match_iff_chi_close_to_one` is reusable conditional tolerance algebra. The module currently imports `LinearizedEFE`; claims that it imports no other project module are false at this candidate. Its susceptibility/speed definition still does not derive a physical response. Import presence alone does not prove a microscopic theorem is used by the scalar constraint.
* `TetradFormalism.tetradInducedMetric` and `tetradInducedMetric_symm` supply concrete algebra. `LinearizedEFE.trace_reverse_involutive`, `linEinstein_linear`, and `linEinstein_trace_eq` are reusable linearized algebra, not actual microscopic pole/polarization construction.
* `DKMBootstrap.Correlator`, `DKMParameters`, `dkmImGRetarded`, `IsDKMTransportCorrelator` supply a scalar transport model. In `KMSConsistency.kms_replaces_unitarity_thm`, the body is `link.positivity_of_reflection h_refl`; the KMS hypothesis is unused. This theorem cannot be cited as constructing a positive physical state from KMS or as closing the L1 spectral interface. The separate action-correlator link is load-bearing and must be established for any consumer.

## Earliest independent substantive package

Recommend a **finite thermal Gram and scoped transfer-obstruction formalization** before more abstract bridge declarations. It can proceed after native admission without duplicating the publication lead's live k4 computation:

1. Use the existing finite `Matrix`/density carrier. For PSD `S` and a finite family `O_i`, define `G_ij = Tr(S O_i† S O_j)`. Prove it is the Hilbert–Schmidt Gram matrix of `B_i = sqrt(S) O_i sqrt(S)` by cyclicity, hence PSD. For a thermal realization use `S = exp(-aH)` and retain the positive partition normalization and centered operators explicitly; the finite matrix lemma alone is not a Gibbs/continuum realization.
2. Prove the exact `Fin 2` matrix with zero diagonal and equal nonzero real off-diagonal is not PSD, preferably via the existing `trace_eq_zero_iff` or a two-vector witness. Also prove PSD restriction to principal submatrices and congruence consequences by calling existing lemmas, not merely citing them in docstrings.
3. Connect the *specified* four-site source response matrix only through independently verified exact coefficient inputs and source/time/contact matching. The accepted manual spectral interface states off-diagonal `(-3113/27648) g2^6/Z` times the squared real source factor and zero diagonals. A faithful thermal representation is excluded for that literal channel at nonzero real g2, real finite nonzero Z and nonzero real match. Z=0 makes normalization undefined. Source-basis changes preserving the span do not repair it; projection discarding a direction changes the tested physical source and needs independent derivation.
4. Independent physics review must verify which sources, time reflection, contact terms and transfer/state assumptions make this Gram test applicable. Independent proof review must inspect exact theorem hypotheses, axiom closure and source matching. This is a scoped obstruction, not a generic L1 no-go or evidence that every later curvature-dressed source fails.

This package preserves a settled negative route in machine-checkable form. It does **not** choose the positive source/state that L1 still needs. The next physical branch-selection report should compare the existing curvature-dressed source against the literal-channel obstruction and identify a prospectively justified state/regulator/projector. A new type with positivity or the speed law as fields would restate the missing physics.

## Notebook and execution boundaries

The current primary publication notebook records manual acceptance, negative routes, live k4 controls and the 234/272 selected-word boundary; none establishes full normalization, B3, tensor mode or transport completion. Its source and source-mixing/positive-spectrum obstructions are also preserved in tracked `L1_RETARDED_SPECTRAL_INTERFACE.md`. `L1_CLOSED_COMPOSITE_DIAGONAL_REPLAY.md` independently records the literal/closed diagonal coefficients and keeps continuum susceptibility open. The exact conditional transport memo distinguishes attenuation from real dispersion and requires microscopic tensor plus wavepacket matching.

No current slot status is inferred from notebook history. Primary admission and independent review are still prerequisites for execution. The research package can be specified now, but the new session must not claim it has proved, run or integrated it.

## Complete successor-design review

Read the entire candidate `docs/roadmaps/L1_Physical_Bridges_Roadmap.md` after its creation. Overall: coherent research sequence, preserves active lead ownership, avoids overstating selected coefficient coverage, and explicitly separates manual physics, native proof, numerical qualification and publication. W1–W4 interfaces cover the central missing physics. Conditional/source-level feasibility may be parallelized; actual physical claims remain serially dependent. No blanket physics acceptance follows from this review.

Mandatory corrections before treating the plan as a settled dispatch authority:

1. **Exact declaration name:** the reusable RPA theorem is `SKEFTHawking.VestigialSusceptibility.W6Ext.chi_RPA_sign_stable`, not `VestigialSusceptibility.chi_RPA_sign_stable`. The Kubo carrier is in the same `W6Ext` namespace. Use exact names so dispatch does not point to nonexistent declarations.
2. **Disposition authority:** replace the ambiguous “owner's specific disposition” for an alternative [0.1,10] outcome with the original **operator's specific evidence-backed disposition**. A scientific reviewer/agent owner may accept a calculation; it cannot quietly authorize a changed original scientific acceptance requirement. Evidence can show failure of that requirement without pretending it was met.
3. **Ready next package:** W1 currently leaves filenames and carrier entirely for later selection. Add the bounded supporting package above, with exact existing Matrix/IsDensityOperator/PSD-square-root carriers, the literal finite matrix input and independent physics/proof contracts. Mark it **prepared for admission, not launched/accepted**, until path ownership and ADR-008 controller are reconciled. This is the earliest useful Lean package that can be rejected independently and does not need the live k4 class to finish.

Recommended completeness improvements:

* Add Phase6q scalar response toolkit and Phase6g scalar wave/Cauchy scope to the reusable-substrate row or linked inventory. Both were missed or understated by the lexical screen. Their abstraction limits matter as much as their names.
* Make the initial physical branch-selection report a coherent W1 deliverable: compare existing curvature-dressed source, allowed regulator/state changes, source projection and negative controls before admitting new large coefficient work. This prevents continued term completion from becoming an implicit research direction.
* W3 consumes static W2 susceptibility but must explicitly establish why its kinetic/gradient ratio is determined by that *same* susceptibility; the draft already requires this and should retain it. W4's distinction between phase/group/pole/arrival observables is appropriate.
* W0's checked boxes describe source reading and planner execution only; its pending ownership and independent review boxes correctly prevent source-wave admission. Keep that distinction in any status report.

Proof-package numerical input is the zero-diagonal `Fin 2` half-period matrix from `L1_RETARDED_SPECTRAL_INTERFACE.md` section “Positive transfer test for the literal four-site plus channel”, using `d=(-3113/27648)g2^6/Z` times the squared common real source factor. Its carrying exact source is `L1_OFFDIAGONAL_HESSIAN.md`; `L1_CLOSED_COMPOSITE_DIAGONAL_REPLAY.md` distinguishes literal `-3113/27648` and closed `-1171/1024` diagonal-separation numerators. Do not substitute one ordering's coefficient into the other source/action contract. The abstract Gram theorem should not hardcode either coefficient; a separately reviewed concrete corollary consumes the exact matched matrix. If the actual project's current physical source has changed, that corollary remains a historical scoped no-go, not a verdict on the new source.
