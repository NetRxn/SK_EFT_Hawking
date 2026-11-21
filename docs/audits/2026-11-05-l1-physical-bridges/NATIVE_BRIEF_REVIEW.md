# Independent target/type review — proposed L1 thermal Gram package

Reviewed `/tmp/l1-wt1-first-proof-brief.md`, initial SHA256 `91bc0c4a8670339f337e720e186132c1ea933ecb3b18abacd3320cc3ed78cd73`, against the current project and installed Mathlib source. Assigned `l1-wt1-brief-review-r1.json` continuity check completed first, exit 0, `fresh:true`, no changed inputs.

**Initial verdict: the bounded mathematical target is sound and source-feasible, subject to the two instruction corrections below.** No compilation or native admission is established by this review. The only proposed worker path is the absent `lean/SKEFTHawking/L1ThermalGram.lean`; no existing source, aggregator, registry, notebook or lifecycle path is assigned to the worker.

**Final verdict: ACCEPT the corrected brief at target/type/source-review scope.** Corrected `NATIVE_WT1_BRIEF.md` SHA256 is `6a1aa26c37fdb4b9cf486550c51b51b7bb708365121c2a5c0903b5e2c1ace46b`. The initial correction record below is preserved. This acceptance does not grant native admission or claim successful elaboration, compilation, proof execution or physical W1 completion.

## Mandatory instruction corrections

1. **Open the complex-order scope in the new module.** Require `open scoped ComplexOrder` before statements using `Matrix.PosSemidef` over complex scalars. `MixedState.lean` opens it locally; importing that file does not open the scope in the new module. Installed `Analysis/Complex/Order.lean` explicitly makes the complex partial order scoped, and `Analysis/RCLike/Basic.lean` supplies scoped `StarOrderedRing`/ordered-module instances. The normalized PSD proof also needs the real-to-complex scalar-order machinery. `open Matrix` is a useful notation convenience; bind `[Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]` explicitly as the brief already requests in prose.

2. **Name the controller as heartbeat owner.** Replace “Root maintains the lease heartbeat” with “the publication controller maintains the lease heartbeat unless it explicitly delegates that authority.” Publication remains controller and has not delegated native authority; the successor's ROOT must not infer a lifecycle mutation grant from an ambiguous label. This wording correction does not itself authorize heartbeat, startup, acquisition or dispatch.

## Exact carrier and algebra assessment

The proposed entries `Tr(R A_i† R A_j)` have the correct conjugation and index orientation. For PSD R, the existing positive square root S is Hermitian and obeys S*S=R. Then `B_i=S A_i S` gives `B_i† B_j=S A_i† R A_j S`; cyclicity yields the proposed trace identity. No commutation of R with A_i is needed, and no invalid noncommutative ring normalization is implied. R may be semidefinite rather than invertible for this algebraic theorem.

Use the already-installed vectorization instead of writing a second flattening helper:

- `Matrix.vec : Matrix m n R → (n × m → R)` has **column-first** index order: `vec M (c,r)=M r c`.
- `Matrix.star_vec_dotProduct_vec A B` proves `star(vec A) ⬝ᵥ vec B = trace(Aᴴ * B)`.
- Set the rectangular matrix `V : Matrix (I × I) J ℂ` by `V p j = Matrix.vec (B j) p`. Its row index p follows the column-first convention. Then `(Vᴴ*V) i j` is the desired Hilbert–Schmidt Gram entry. Calling `Matrix.posSemidef_conjTranspose_mul_self V` supplies actual Gram positivity.

Both row-first and column-first enumerations produce equivalent finite sums if used consistently, but the existing vec identity avoids a sum-order/transpose mismatch. The new result's substantive residue is the weighted trace-to-Gram correspondence, not a fresh generic Gram-positivity theorem. Installed `Analysis/InnerProductSpace/GramMatrix.lean` also supplies `Matrix.gram` and `Matrix.posSemidef_gram`; the rectangular route avoids introducing extra inner-product-space carriers just to recover this existing fact.

Normalization by `(1/Zthermal : ℝ)` is correct with `Zthermal>0`; call `Matrix.PosSemidef.smul` with real nonnegativity. Do not silently replace this with division by an arbitrary complex or signed source partition. The finite algebraic proof needs no Gibbs, unit-trace, KMS or equilibrium assumption. A later thermal application must separately construct the positive exponential, thermal denominator and source/time matching. `IsDensityOperator` is an available concrete carrier, not a necessary additional assumption for the general weighted Gram lemma; do not add trace-one solely to match a physical label.

## Obstruction and source-corollary assessment

For real nonzero d, the matrix `!![0,(d:ℂ);(d:ℂ),0]` is Hermitian with zero trace and is nonzero. Existing `Matrix.PosSemidef.trace_eq_zero_iff` immediately contradicts PSD after identifying its `(0,1)` entry. Alternatively the existing quadratic-form theorem works. There is no need to build an eigensystem or duplicate general principal-minor theory.

The proposed `no_normalized_thermal_match` consumes an explicit equality to that matrix and the independently proved Gram PSD statement. This equality is a physical correspondence assumption, not a reconstructed state. Its explicit appearance and the nonzero hypotheses prevent the theorem from claiming that the microscopic integral has been formalized.

Both source fractions are correctly separated: literal `-3113/27648` and closed `-1171/1024`. With real nonzero g2, full source denominator Zsource and source match alpha, each displayed d is nonzero. Its non-PSD arithmetic consequence is valid for either sign of Zsource. Keep `Zsource` distinct from `Zthermal` and from the coefficient Z8. The physical pure-g2/g1=0 applicability belongs in names/docstrings and the source-correspondence contract; these arithmetic expressions do not prove the integral identities or extend them to arbitrary g1/g2-squared. No conclusion follows for an undefined normalized source at Zsource=0 or for alpha=0.

The brief correctly excludes inferring a covariance obstruction from the affine/exponential **full** Hessian sign contrast, where quadratic contacts differ. It also preserves source ordering, the finite source-span restriction and the independently reviewed dressed-source research direction. Formalizing this historical negative control does not derive a positive source/state, the B3 interval, tensor polarizations, matter/light coupling, transport, or publication acceptance.

## Source inspection and duplication limits

Checked actual project declarations in `QuantumNetwork/MixedState.lean`: namespace `SKEFTHawking.QuantumNetwork`, `IsDensityOperator`, `psdSqrt`, `psdSqrt_isHermitian`, `psdSqrt_mul_self` and positivity. Read installed Mathlib `LinearAlgebra/Matrix/Trace.lean`, `PosDef.lean`, `Vec.lean`, relevant `Analysis/Matrix/PosDef.lean`, `Analysis/Complex/Order.lean`, `Analysis/RCLike/Basic.lean` and `Analysis/InnerProductSpace/GramMatrix.lean` declarations. Source confirms the trace-cycle/commutation, PSD scaling, rectangular Gram and trace-zero tools named above.

Bounded project/Mathlib searches found generic Gram/vectorization/PSD support, but no matching `thermalGram`, normalized thermal-source match or `L1ThermalGram` declaration. A negative text search is not proof of absence; the admitted worker must repeat exact source/MCP searches before adding helpers. Do not reimplement Mathlib's generic Gram, vectorization, trace-zero PSD or density types. Reconfirmed the assigned target file is absent in this delivery checkout. Primary equality/absence and toolchain synchronization remain the controller's separately reported preflight; no slot state was probed by this reviewer.

## Readiness and execution boundary

This target/type review can support publication's path/target decision after correction. It cannot grant native admission. Publication still owes its controller decision, current matching source/epoch, client-drain/quiescence and targeted startup disposition, normal acquisition/preparation, active lease and a healthy matching endpoint. The worker's first continuity/lease checks and matching wt1 MCP diagnostics are required evidence of actual execution. Source-level proof feasibility is not elaboration success, and a single checked declaration is not completion of the whole package.

The proposed worker restriction to one new module is appropriate. Aggregator registration, authoritative build/extraction, any registry or formula work and integration remain separately controller-owned. No new axiom, sorry/native-decide/heartbeat override, Aristotle submission, physical assumption or alteration of the original [0.1,10] requirement is authorized.

Only this assigned review report was written. No Lean file edit, MCP proof call, build, scientific coefficient evaluation, controller/process probe, lease operation, registry/notebook edit, security/configuration change or external contact occurred.

## Corrected-brief final readback

The refreshed `l1-wt1-brief-review-r2.json` check completed first with exit 0, `fresh:true`, no changed inputs. Read the complete corrected brief in this audit directory. It explicitly adds `open scoped ComplexOrder`, `open Matrix` and finite/decidable binders; uses `Matrix.vec` and `Matrix.star_vec_dotProduct_vec` with the correct column-first indexing and conjugate transpose; and assigns heartbeat authority to the publication controller unless it explicitly delegates. These resolve the two mandatory corrections and the exact-reuse recommendation. The source-match, denominator, pure-g2 and physical-scope limits remain intact.

Independently verified the corrected file's SHA256 against the value above and confirmed byte equality with the updated `/tmp/l1-wt1-first-proof-brief.md`. No further source re-audit or execution was needed for this bounded wording/interface change. No remaining mandatory correction was identified at this review scope. Publication's explicit admission, current client-drain/startup checks and normal controller/lease/endpoint steps remain pending outside this acceptance.
