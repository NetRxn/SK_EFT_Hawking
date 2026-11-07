# Independent prospective actual Grassmann/coframe B1 scope review r1

Verdict: **REVISE** — correct one impossible compact-link control. Other prospective scope, source and mathematical checks pass.

First action checked the exact publication-grassmann-scope-review-r1.json packet: exit0, fresh=true, changed=[]. This review is prospective only. No implementation, actual Lean elaboration/kernel result, slot admission or physical/publication completion is certified.

## Required correction

The scope's controls include “zero/identity/special links”. The actual link type is SU(2)L x SU(2)R represented by block-diagonal unitary matrices. The zero matrix is not a group link: its dagger product is zero rather than identity, and its determinant is zero rather than one.

Replace this with zero-COFRAME/generator-combination controls plus identity/special ACTUAL group-link controls. A one-site periodic torus with identity links does give a zero coframe by cancellation of all four quarter terms; it is a valid zero-coframe case, not a zero-link case. Zero matrices may be tested in an explicitly separate generic-coefficient bilinear lemma, never as an instance of the actual compact-link theorem.

ROOT confirmed this intended distinction and requested preservation of R1 REVISE before issuing corrected R2. No other necessary source/math/scope revision found. The correction changes no source convention, model or required scientific acceptance boundary.

## Independent reading and primary-source inspection

I read the complete new B1 scope, frozen ROOT notebook, the accepted full Eq4/Eq7 design and my complete prior independent prospective review, original98-line Eq1–11 construction, existing positive exterior/Fock coverage, complete43-line literal-versus-closed replay and relevant exact carrying-source correspondence passages.

I directly inspected the held Diakonov2011.pdf pages11–15 both as extracted text and as rendered page images. Rendering used pdftoppm captured in memory and forwarded directly; no image or PDF artifact was written. Source PDF SHA256132d63150a678ef17bfbbc04978a8cab9c9801f03556982a6aa67c11d3fbc4da. PDF skill was used for read-only primary inspection. No internet source or presumed alternate version was substituted.

## Gamma, link and index correspondence

Primary page11 Eq14 gives gamma_A=[[0,sigma_A^-],[sigma_A^+,0]], with sigma_A^+=(+i*tau1,+i*tau2,+i*tau3,I2) and sigma_A^-=(-i*tau1,-i*tau2,-i*tau3,I2). Thus the explicit Fin4 order0,1,2,3 represents source labels1,2,3,4, and q=(-i*sigmaX,-i*sigmaY,-i*sigmaZ,I2) is correct. Hermitian Pauli matrices give q_C dagger as the lower block; conjugation belongs here in link/matrix dagger, not in the independent barred Grassmann generator or auxiliary polynomial coefficient.

With this ordered gamma tuple, gamma0*gamma1*gamma2*gamma3=diag(I2,-I2): using tau1*tau2=i*tau3, the first two gamma product blocks are i*tau3, the product with gamma2 has off-diagonal blocks I2,-I2, and multiplication by gamma3 yields the stated diagonal. This is consistent with the primary page14 Eq24 positive epsilon/trace normalization. B1 must keep this explicit ordering rather than importing an unrelated “gamma0 is the identity-off-diagonal matrix” convention. Future temporal/world-index identifications remain separate from this source-label reindexing.

Primary page11 Eq16 explicitly gives independent SU(2)L and SU(2)R blocks in the direct-sum Dirac representation. The proposed block-diagonal reindexing to Fin4 matches; tensor (2,2), real Majorana identification and a Hilbert adjoint on psi/bar are not introduced. Concrete index equivalences and matrix definitions still require actual implementation proof.

## Four source coframe terms

Primary page13 Eq23 has alpha/(2a) times the forward bracket and -(1-alpha)/(2a) times the backward bracket. At alpha=1/2 and T=a*ehat this is exactly1/4 times:

1. barpsi_x gamma_C U_(x,mu) dagger psi_(x+mu);
2. minus barpsi_(x+mu) U_(x,mu) gamma_C psi_x;
3. minus barpsi_x gamma_C U_(x-mu,mu) psi_(x-mu);
4. plus barpsi_(x-mu) U_(x-mu,mu) dagger gamma_C psi_x.

All matrix ordering, anchors and +,-,-,+ signs in B1 match. Gamma cannot be commuted through U to “simplify” reverse terms. Positive torus extents give actual neighbor permutations. Periodic specialization is explicitly scoped; it does not prove arbitrary twists. Extent>=3 is a sound diagnostic for separating forward/backward neighboring-site coefficients, while universal statements must also include small extents and their legitimate cancellations.

Primary pages14–15 state eight independent Grassmann integration variables per site and the full multifermion cosmological/EHC action. B1 preserves the independent four psi/four barpsi generators and does not manufacture a quadratic propagator or positive state.

## Actual exterior construction and proof scope

The proposed G=ExteriorAlgebra Complex (Gen->Complex), Gen=Lambda x(Fin4 sum Fin4), is a genuine global8V-generator algebra with independent named coordinates. Actual finite torus and actual block-link/gamma quarter coframes are required, so the assignment is not a toy conditional carrier.

Every displayed coframe is a finite linear combination of generator pairs and therefore lies in grade2. Exterior anti-commutation gives four-swap commutation of generator pairs, then scalar linearity gives all coframes commuting across all sites. The actual subalgebra generated by coordinate bilinears is a correct commutative target for polynomial aeval, with proved membership and injective inclusion; full G remains noncommutative and must never acquire a false CommRing instance.

A product of n coframes lies in grade2n. Exterior degree above8V vanishes by the finite exterior basis/finrank choose formula. Thus n>4V implies zero, uniformly in mixed sites, overlaps and repeated coframes. Monomial nilpotence must be derived from this GLOBAL statement, not from per-variable powers. The actual subalgebra version follows by injectivity.

Named-generator independence, odd swap/square-zero, disjoint and overlapping bilinears, nonzero square of a sum of two disjoint bilinears, generic top-degree sharpness, cross-site monomials and explicit hopping-coefficient controls are appropriate. In particular (theta1theta2+theta3theta4)^2=2theta1theta2theta3theta4 is nonzero on distinct basis coordinates. Generic4V disjoint pairs reach the nonzero top8V basis vector; that does not promise every actual coframe configuration saturates the bound.

Existing source positively provides GoltermanShamir.FermionicFockSpace k as the actual exterior algebra on Fin k->Complex, its public Module.Finite instance, creation_anticommute and pauli_exclusion. The finite-grade-zero proof pattern is private and cannot be imported. B1's named Gen representation can be related via a finite-index equivalence or use the underlying Mathlib APIs directly. Existing Fock-space naming does not supply or authorize a physical Hilbert/state interpretation. Project Pauli definitions were also inspected as reuse leads. Live matching LSP statement/type/import search is still required after admission; static source misses do not establish absence.

## Printed-versus-closed source-functional boundary

Primary page12 Eq17 literally prints A B C-dagger D-dagger with its specified four anchors. Page13 Eq21 transforms U_xy as V_y U_xy V_x dagger. For these endpoint conventions the explicitly gauge-closed based product is D-dagger C-dagger B A. B1 correctly labels these separately and does not infer equivalence from trace cyclicity.

The existing replay documents different full finite coefficients: literal diagonal plus numerator -3113/27648 versus closed -1171/1024 at raw g2^6, with distinct residual subtotals. It is evidence for the scoped functional distinction, not an approved equivalence dictionary or universal impossibility. Accepted later carrying results explicitly use the closed order while retaining the same quarter coframes and q convention.

Therefore excluding EHC action definition/identification and any functional-order equality from B1 is necessary and sound. It does not reduce the full accepted B/C target: ROOT explicitly retains B2 source-action correspondence, with literal/closed labels and no silent plaquette/gamma/coupling replacement, and C actual G-valued Eq7 with genuine integrability and actual premise discharge. Universal ordinary compensation A is unaffected. Neither B1 completion nor a conditional evaluation hom can close those downstream obligations.

## Parallel admission and residual obligations

B1's one-new-module ownership is coherent and independent of ordinary compensation A after index/degree interfaces are pinned. It should reuse existing positive coverage, leave the accepted complex module unchanged, and perform actual admitted LSP discovery before proof. No aggregate, registry, action definition or runtime change is part of B1. ROOT owns admission, builds/importability, independent implemented review, absorption and full gates.

No actual admission or implementation was performed by this review. Full Eq4/source-specific Eq7, B2 correspondence, source matrix/Berezin/determinant/link/Haar/Fubini, Eq11, normalized Z, phase/positive sampling, physical source/state/adjoint/B3/calibration/mode/matter/transport/limits and publication remain open at their original scopes.

Only the assigned /tmp report and JSON were written; no repository/notebook/source edits, Git operations, MCP, tests/builds, slots/controllers/process/cache/dependency actions occurred. Required R1 correction is solely the impossible “zero links” control wording.

Final identical R1 packet check: exit0, fresh=true, changed=[].
