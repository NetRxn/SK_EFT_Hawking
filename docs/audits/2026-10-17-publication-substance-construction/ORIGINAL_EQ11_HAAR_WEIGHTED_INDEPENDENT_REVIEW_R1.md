# Independent Eq11 weighted Haar transfer source review R1

**ACCEPT exact source commit `7e1cd960c0f3842358803d8b0c6ce8fb06639138`
for the weighted Haar increment.** Its parent
`0736fda2ecf6e737a3a5ce978f92065d4f0135ae` registers the reviewed
scalar Stein module. The commit adds only
`lean/SKEFTHawking/ADW/GaussianHaarPolynomialStein.lean`. Its SHA256
`55fb2ad2c04e2855e1761a84bdafc88d9cc32c03acc6e768aee14d4307a0e64c`
matches the live leased file. The exact diff passed the Git whitespace
check.

The declarations use the existing `HaarPolynomial L` carrier,
`MvPolynomial (Auxiliary L) C(Links L, ℂ)`, and
`haarPolynomialEvaluation` on the original links and real Gaussian
coordinates. All transfer and integrability statements use
`(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)`.
`linkHaar L` is the same original normalized Haar measure as Eq10.
The only analytical hypotheses are positive real σ and exact variance
`(v : ℝ) = σ ^ 2`. The algebraic adjoint composition requires neither.
The weight W and polynomial P are arbitrary in the actual carrier.
No nonzero-weight, nonzero-partition, positivity, or coordinate
distinctness assumption is added.

The unweighted helper justifies both Fubini rewrites with
`haarPolynomial_integrable`. At a fixed link it uses the true ring
homomorphism `coefficientEvaluation L U`; `pderiv_map` and
`eval₂_eq_eval_map` specialize the partial derivative in the actual
polynomial. The accepted scalar centered Stein theorem then applies at
the same variance. The private integral subtraction helper invokes
joint integrability of both polynomial evaluations before subtracting
their integrals. The public first and second integrability results
explicitly cover both sides under the original joint measure.

For q = σ⁻², the weight adjoint is A_a W = q X_a W − ∂a W.
The first transfer expands ∂a(WP) and moves only the polynomial
derivative. The second starts at W ∂a(∂b P), transfers a first and
then b, and ends at A_b(A_a W)P. Expanding this composition produces
`(q² X_a X_b − δ_ab q)W − q X_a ∂bW − q X_b ∂aW + ∂b(∂aW)`.
The negative contact is present when a=b and the two gradient terms
both survive. In the mixed case, the `pderiv_X_of_ne` premise is
oriented correctly for ∂b X_a and the contact vanishes. No
commutation of partial derivatives is silently assumed. This matches
the approved weighted design and its diagonal, mixed and zero-Z
controls.

No new axioms, admissions or placeholder declarations appear in the
module. This was a complete read-only source review. ROOT's reported
exact Lean diagnostics are separate evidence and ROOT owns axiom
queries, aggregate registration, build and absorption. The actual
shifted determinant and original printed and closed Grassmann
insertions, their correspondence, and final Eq11 wrappers remain
separate proof increments.

## Continuity readback

The first packet check returned SAME. The first final check returned
`changed=["source"]`, with no owned-file or authority change. I
preserved that receipt. A read-only reconciliation found the same
HEAD, clean worktree, and exact packet index and status hashes. A
subsequent check of the same packet returned SAME, byte-for-byte with
the first. The transient mismatch cause is unestablished. The reviewed
commit and source bytes are exact, and ROOT owns the live disposition.
