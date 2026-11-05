# Proposed wt1 package: finite Gram support and scoped source obstruction

Status: proposed for publication-controller review; no lease/startup/worker authority.

Owner requested: publication remains controller; successor supplies one proof worker and independent review only after admission. Primary base must be the actual primary branch and its current matching epoch, not the documentation branch or a literal SHA base-ref. Preserve wt2 READY_TO_ABSORB, wt3 QUARANTINED and all current coefficient work.

## Exact owned path and scope

Worker writes and commits only `lean/SKEFTHawking/L1ThermalGram.lean` in the actual controller-prepared public wt1 worktree. This path does not exist in the primary or publication delivery checkpoint. No existing `.lean`, aggregator import, formula, constants, registry, notebook, pipeline or cache path is assigned to the worker. Publication retains subsequent aggregator registration/integration/build/extraction/registry ownership in a separately confirmed window.

This is bounded supporting mathematics for W1, subordinate to the reviewed physical background/matter matching programme. It preserves a settled finite negative control. It does not build the physical state, derive the metric source or susceptibility range, reproduce any integral coefficient, or close W1/B3/mode/transport/publication.

## Reuse and source pins

Import `SKEFTHawking.QuantumNetwork.MixedState` and relevant Mathlib matrix trace/PSD modules already pinned by the project. Primary and delivery copies of MixedState, `lean-toolchain` and `lake-manifest.json` are byte-identical at the readback.

Use existing `SKEFTHawking.QuantumNetwork.psdSqrt`, `psdSqrt_isHermitian`, `psdSqrt_mul_self`; Mathlib `Matrix.posSemidef_conjTranspose_mul_self`, `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle`, `Matrix.PosSemidef.smul`, and existing PSD restriction/trace lemmas. Search actual declarations again with the matching MCP endpoint before creating helpers. Do not create a second density or PSD type.

Physical-source reading: `L1_RETARDED_SPECTRAL_INTERFACE.md`, sections “Positive transfer test for the literal four-site plus channel” and “Linear composite-metric source on the closed action”; `L1_CLOSED_COMPOSITE_DIAGONAL_REPLAY.md`; corrected branch-selection report `47d65955b7d562cf6e076696bce01363e0dc960023200b2d4953a1a0744a945b` and independent review `1360b392d8e8aedc8fe3578ef5fc34ca38dde71bc3e47bd9a70952845a1e2767` in PR115. The selected source controls and their integral identities remain manual/independently reviewed inputs, not newly kernel-derived coefficients.

## Exact mathematical interface

Namespace `SKEFTHawking.L1ThermalGram`. Explicitly add `open scoped ComplexOrder` (the imported file's local scope is not inherited) and `open Matrix`. Bind `{I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]`. Scalars are complex and matrices use conjugate transpose. State weight `R : Matrix I I ℂ`, operators `A : J → Matrix I I ℂ`.

1. `thermalGram R A : Matrix J J ℂ`, entry `(i,j) = Matrix.trace (R * (A i)ᴴ * R * A j)`.
2. `thermalGram_eq_hsGram`: for `hR : R.PosSemidef`, set `S = QuantumNetwork.psdSqrt hR`, `B i = S * A i * S`. Prove the entry equals `Matrix.trace ((B i)ᴴ * B j)` by actual matrix identities and trace cyclicity.
3. `thermalGram_posSemidef (hR : R.PosSemidef) : (thermalGram R A).PosSemidef`. Use existing `Matrix.vec` and `Matrix.star_vec_dotProduct_vec` from `Mathlib.LinearAlgebra.Matrix.Vec`: set `V : Matrix (I × I) J ℂ` by `V p j := Matrix.vec (B j) p`. Matrix.vec has column-first product indexing, `vec M (col,row)=M row col`. Identify `Vᴴ * V` with the trace Gram and call `Matrix.posSemidef_conjTranspose_mul_self`. Do not create a custom flatten helper or use a transpose in place of conjugate transpose. Do not package the conclusion in an assumed field.
4. `normalized_thermalGram_posSemidef`: for real `Zthermal > 0`, prove `((1 / Zthermal : ℝ) • thermalGram R A).PosSemidef` by calling the preceding theorem and existing scalar positivity.
5. `twoSiteOffDiagonal (d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, (d:ℂ); (d:ℂ), 0]`.
6. `twoSiteOffDiagonal_not_posSemidef (hd : d ≠ 0) : ¬ (twoSiteOffDiagonal d).PosSemidef`, using a real quadratic witness or the existing PSD trace-zero theorem. Retain the nonzero hypothesis.
7. `no_normalized_thermal_match`: instantiate J as `Fin 2`. Given `hR`, `0 < Zthermal`, `d ≠ 0` and the explicit equality `(1/Zthermal:ℝ) • thermalGram R A = twoSiteOffDiagonal d`, prove False by consuming the preceding results. This is conditional on the concrete source-matrix match, not a new physical representation theorem.
8. Two exact arithmetic corollaries for `d = (-3113/27648:ℝ) * g2^6 / Zsource * alpha^2` and `d = (-1171/1024:ℝ) * g2^6 / Zsource * alpha^2`, assuming real `g2 != 0`, `Zsource != 0`, `alpha != 0`. Show their two-site matrices are not PSD by proving d nonzero and calling theorem 6. Zsource means the FULL source partition denominator, not the coefficient Z8. Zsource and Zthermal must remain distinct.

The last corollaries only formalize arithmetic consequences of the reviewed pure-g2 (g1=0) coefficient identities. They do not assert those identities for arbitrary couplings. The exact literal and closed orderings must remain separate in names/docstrings. Do not claim an all-coupling no-go, positive thermal reconstruction, or derived background. Do not infer a covariance no-go from the full affine/exponential Hessian sign contrast, which includes different contacts.

## Native acceptance and resource contract

Before dispatch, publication reviews these paths/targets and records the controller and client-drain/startup disposition. Fresh complete capacity, both-role target quiescence and independently drained client requests are required under ADR008/LO5. Targeted proxy1 startup uses existing root internals under target-slot then lifecycle locking, without touching peer leases or using a global restart. No source edit or configuration/security change is proposed.

Normal sequence after admission: primary controller acquire wt1 on actual primary branch; prepare against matching epoch; confirm ACTIVE/public/codex lease and healthy matching proxy/backend; then launch a worker whose available tool surface includes `mcp__skeft_wt1__*`. A newly started runtime must use existing worker restrictions/configuration; no bypass flags, security edits or unleased direct backend calls.

Worker's first action is its source-bound continuity check and primary read-only lease check. Use only the matching wt1 MCP for outline/goals/multi-attempt/diagnostics/verification. No shell builds, cleans, cache/dependency repair, integration or shared writes. Publication controller maintains the lease heartbeat unless it explicitly delegates that authority to this successor. Stop and report any lease/endpoint/identity mismatch.

Required evidence that the worker actually ran: its native task/session identifier, successful matching MCP tool calls, outline/goal/diagnostic receipts for the assigned module and at least one kernel-checked declaration. Completion additionally needs all assigned declarations, no sorry/heartbeat/native-decide regressions, kernel axiom audit limited to the standard allowlist, exact owned-path commit and independent proof review. Primary integration/authoritative build and final wave gates remain separately owed and controller-owned.

No Aristotle submission, new axiom, additional physical assumption or change to the original [0.1,10] acceptance requirement is authorized. If the target is already available in the project/Mathlib, reuse it and report the actual residue rather than duplicating it.
