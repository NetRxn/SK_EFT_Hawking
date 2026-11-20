# N16 full-normalization and physical-image certificate contract

Actual source-level reduction and proposed next certificate contract, for
independent mathematical and physics/source review. Parent: accepted temporal
identity 7f8cf17b443e23fd253ab59be3047bb23c69c60e, exact source82197710.
No evaluation, nonzero denominator, positive state or negative numerical witness
is reported. The original N4 full tensor remains independently OPEN and owed.

## 1. Literature and existing substrate: retain the actual hypotheses

[Diakonov 2011 v1](https://arxiv.org/abs/1109.0091v1), section V, equations
(23)-(28), supplies the composite coframe, two microscopic interactions and
finite Haar/Berezin functional. Its discussion of loop organization and an
infrared regime does not supply our normalized N16 state. Preserve the already
accepted closed-order correspondence; do not silently mix literal plaquette
coefficients into it. Held primary: `Lit-Search/Phase-5d/primary-sources/Diakonov2011.pdf`.

[Vergeles 2025 v2](https://arxiv.org/abs/2506.00036v2), sections II-IV, treats
Minkowski evolution on simplicial lattices with conserved degrees of freedom,
contour continuation and a gauge treatment. Equations (4.3)-(4.8) use an
orthonormal basis, normalizability, finite matrix elements and a complete
real-eigenvalue basis for the Hermitian evolution generator. Section VI,
equation (6.1), explicitly extends the discussion to composite tetrads; it
must not be dismissed as exclusively an independent-tetrad model. The modified
model still retains the stated gauge/noncompact-volume issues. Applying this
result here requires an action, contour, boundary, observable and state-map
correspondence to our periodic Euclidean hypercubic functional. None is supplied
by its title or a shared composite-tetrad label. Held primary:
`Lit-Search/Phase-5d/primary-sources/Vergeles2025.pdf`.

[Jaffe and Janssens, Reflection Positive Doubles v1](https://arxiv.org/html/1607.07126v1),
introduction (I.2)-(I.3), VIII.1 and IX.3, distinguishes graded reflection
conventions; its coupling criterion V.10 has explicit factorization, positivity
and reflection-invariance premises and concerns all nonnegative inverse
temperatures. Their QCD result is for its specified action. These are useful
comparison contracts, not a theorem already matching our S4/action/source or
periodic fermion signs. On our gauge-invariant even algebra the odd-sector
phase issue is absent; the actual involution and sources remain those explicitly
derived in the parent. No theta(S2)-invariance premise is assumed or manufactured.

Existing `ADW_EXACT_AUXILIARY_IDENTITY.md` equations (7)-(10), the full-source
temporal identity, actual compact Haar moments and exact polynomial joins are
reusable. `FermionBag4D.fermion_bag_weight_positive` assumes positive factors;
`metric_correlator_nonneg` assumes its moment inequality. QuantumNetwork
`IsDensityOperator` and `psdSqrt` require a supplied density/PSD witness. Their
actual source types do not derive the signed interacting state by themselves.
No theorem absence, LSP elaboration or Lean admission is inferred from this
source reconciliation. The new target below is the whole physical image, not
another selected action-word campaign or an inherited no-sign-problem claim.

## 2. Fixed same-model target

Keep the original closed action, periodic2^4 regulator,128 Grassmann generators,
64 independent Spin(4) links, signed fullS4 Hermite weight, +S convention,
original coframe quarter and oriented top coefficient. Keep the SAME physical
J and prescribed C2 coframe j family, its first/mixed-second contacts, fixed
measure and regulator from the parent. Auxiliary h is not physical J or a
metric background. No source/state/temporal twist, matter determinant, positive
B0, projection, coupling or normalization is chosen to force a sign or interval.

Use the parent's geometric anti-involution theta and full even gauge-invariant
slice0 polynomial algebra A_+. Its64 Grassmann generators and24 spatial
Spin(4) links have192 real quaternion coordinates. Relations of SU(2) matrices
are retained; no independent-coordinate sampling replacement is made. Evenness
is not a favorable projection: the uniform central element(-I,-I) at every
slice site fixes all spatial links and flips every spinor generator, so an odd
gauge-invariant polynomial is zero. Any further physical constraint quotient
must be derived from the intended model, not selected after a negative result.

At source zero let Z=I[exp(S_g)] and

    H(F,G)=I[exp(S_g) theta(F) G]/Z,     F,G in A_+,

only WHERE full Z is nonzero. The parent explicitly constructs its signed
boundary kernel. No theta(S2) noninvariance alone proves H fails; a direct
functional correspondence, actual observable witness or complete positivity
certificate is required. Positivity of a few minors or a link moment Gram
does not prove positivity on all A_+.

## 3. Exact auxiliary annihilator: global Hermite degree64

The parent product W=product_x W_x has local Hermite truncations64. Let
Pi_H,64 retain only tensor Hermite modes of TOTAL auxiliary degree<=64.
Define Wbar=Pi_H,64 W. Equivalently, apply the SAME256-variable Hermite map to

    [exp(sum_x s_x(Y;J,j)) exp(-sigma^2 sum_i Y_i^2/2)]_(total degree<=64).

This equivalence follows because per-site truncation cannot alter a coefficient
of global degree<=64. No interaction or physical observable is omitted.

For fixed links, and ANY physical polynomial insertion O independent of h,

    P_O(h,U)=I_Berezin[exp(h.T) O]

is a polynomial in h of total degree<=64. In a homogeneous insertion sector
of Grassmann degree r its possible nonzero degree is(128-r)/2<=64; impossible
sectors vanish. Tensor Hermite polynomials of total degree>64 are orthogonal
under the positive auxiliary Gaussian to EVERY polynomial of degree<=64.
Therefore, coefficientwise before link integration,

    integral dmu_sigma (W-Wbar) P_O=0.                             (A)

This includes O=theta(F)G for arbitrary half-local polynomial F,G and all full
source jets: differentiation changes the Hermite coefficients but not their
orders, while h.T is fixed. Gaussian/Haar exchanges remain finite-polynomial
ones as in the parent. Sigma is arbitrary fixed positive and source independent.

Replacing W by Wbar therefore preserves the ENTIRE physical inserted/source
functional, not just normalization or a selected Gram span. It does NOT assert
pointwise equality of old and new boundary kernels. Auxiliary high modes can
alter an ambient kernel while annihilating every physical insertion; they
cannot be used to infer or remove a physical negative direction. This is an
exact representation identity, not a physical-state projection or approximation.

Wbar has total h degree<=64 and total link-coordinate degree<=128: each S2
contributes coframe degree2 and at most4 link coordinates; S4 and the formal
Q source have no link coordinates before substituting actual T. A coframe-
degree64 term has at most32 S2 factors. The prescribed A(j) and all its source
jets do not change this bound. Wbar remains signed/complex.

## 4. Complete finite image of the original infinite polynomial algebra

Use Wbar in the parent's K, then the SAME S inverse/reflection formula for
the unnormalized kernel B0, so H=the associated pairing divided by Z. The
bridge minors contain ONLY temporal links. After all temporal Haar moments,
B0 is a finite polynomial in the two half variables and has spatial-link
degree<=128 in either half. The reflection kappa is linear in quaternion
coordinates and does not increase degree. All boundary indices are retained.

Expand this polynomial kernel in a finite REAL monomial list p_alpha(z)
(ordinary real auxiliary/quaternion coordinates; all needed degrees included).
With a combined boundary/monomial index m, define actual linear functionals

    ell_m(F)=integral dnu(z) p_alpha(z) f_0,A(F;z).

For a completely specified finite coefficient matrix C(g1,g2), with entries
from the full signed Wbar/moments and original exterior reflection matrix,

    I[exp(S_g) theta(F) G]=ell(F)^dagger C ell(G).                 (F)

The entries of C need not be Hermitian or positive. This is the finite
polynomial expansion of the derived kernel, not a fitted response matrix.
The list and map ell are fixed independently of a favorable state/coupling.
Mixed source derivatives differentiate C and preserve the same finite carrier.

To identify its ACTUAL physical image, write

    F=sum_D xi_D F_D(U_spatial).

In f_0,A(F), the coefficient of F_D uses at most32 powers of the spatial
bilinear E0, each linear in spatial links. Integrating the auxiliary h against
p_alpha leaves a coefficient polynomial in spatial links of degree<=128+32=160.
Consequently every ell_m depends on F_D ONLY through Haar pairings with link
polynomials of degree<=160. This polynomial space is closed under complex
conjugation: a linear pairing integral R F_D is the auxiliary Hilbert pairing
with conjugate(R), so orthogonal projection preserves it. No assumption about the sign of the action enters.

Define V160 as the finite vector space of all even Grassmann monomials with
coefficient link polynomials of total degree<=160, considered as actual
functions on the compact link groups. For the proof only, equip coefficient
functions with the AUXILIARY positive inner product

    (F,G)_aux=sum_D integral dHaar_spatial conjugate(F_D) G_D.

This is NOT the physical state. Quotient Haar-null polynomial relations and
take the orthogonal projection P160 onto V160. The preceding coefficient
bound proves

    ell(P160 F)=ell(F),         H(P160 F,P160 G)=H(F,G).           (P)

Gauge transformations act unitarily on this auxiliary space: endpoint action
on link quaternion coordinates preserves Haar and degree, and Dirac/dual
spinor actions induce unitary exterior actions. V160 is gauge invariant, so
P160 commutes with the compact slice gauge group. Therefore it sends a
gauge-invariant F to a gauge-invariant polynomial. Even parity is retained.
This is not a posthoc projection of a negative physical observable: EVERY
original pairing is identical by (P).

Let R_G be the normalized compact slice-gauge average. An explicit, possibly
very overcomplete, finite list is

    F_(D,alpha)=R_G[xi_D u^alpha],
          |D| even, |alpha|<=160.                               (L)

The gauge average preserves degree. These span the invariant part of V160:
apply R_G to its full monomial spanning list. Equations (P),(L) imply

    ell(A_+)=span{ell(F_i)}.                                    (I)

Thus the list spans the WHOLE adopted physical image, not a selected positive
subspace. It includes1. No linear independence is assumed; relations give
exact zero rows/columns as appropriate. The space V160 is only a finite TEST
space, not an algebra truncation: products can exceed degree160 and are
projected again only inside the proved functional identity. P160 is not claimed
multiplicative and does not itself construct physical operators.

The bound160 is a safe uniform mathematical bound, not a tractable-size claim
or an instruction to enumerate the list. Any smaller carrier requires an
equally complete, independently proved annihilator/image argument. The parent
kernel and its original archives are unchanged by this equivalent description.

## 5. Exact normalization/Gram/witness certificate

On the full finite list define ORIGINAL-action numbers/functions

    N_ij=I[exp(S_g) theta(F_i) F_j],      F_0=1,       Z=N_00.

With no presumed sign and only where Z!=0, (I) gives the exact equivalence

    H is positive semidefinite on ALL A_+
          iff the complete overcomplete matrix N/Z is Hermitian PSD. (G)

Indeed any F has an image expressed by the finite list, and conversely every
linear combination of the list is an actual gauge-invariant half observable.
Redundant list coordinates do not create false witnesses: their observable
relations annihilate the exact matrix. This is the required physical-image
correspondence, beyond a PSD test on an arbitrary ambient coefficient space.

Acceptable normalization evidence: a complete exact nonzero Z, a full-functional
good-prime nonzero certificate with ALL denominator invertibility proved, or
a rigorous analytic/signed-remainder bound on a prospectively named domain.
If Gaussian-rational coefficients are used, the finite-field embedding and
both real/imaginary conventions must be fixed exactly. A zero residue is
inconclusive. Such a nonzero certificate proves no positive state or sign.
Selected terms, determinant norms and incomplete action-sector coverage do
not certify full Z. The original orientation and phases are never discarded.

Acceptable reflection evidence is either a complete exact/rigorous-domain
certificate for (G), or an ACTUAL matched witness. A negative witness supplies
explicit list coefficients c, the observable F=sum_i c_i F_i, the source/coupling
domain and nonzero normalization evidence, and proves c^dagger(N/Z)c<0.
A demonstrated non-Hermitian pairing on actual listed observables also defeats
this positive-reflection representation. A conditional witness must give a
proved nonempty normalized domain; failed computation is not zero, and a
negative coefficient vector outside the image is not a physical witness.

Neither thetaS2 noninvariance nor a few positive minors supplies this evidence.
An actual obstruction defeats only the specified model/source/reflection/domain,
not all Lorentzian states or original B3 claims. A successful (G) is a complete
reflection-form certificate on A_+, not automatically a thermal/real-time model.

## 6. What an ACTUAL state certificate must additionally establish

The adopted physical goal is stronger than a formal positive matrix. For a
positive-state claim supply a reconstruction/representation that identifies
the original normalized functional and its required sources with actual
operators and state data. In particular:

- Identify the physical adjoint/reflection and retained observable algebra,
  gauge/constraint relations and ALL required source insertions. Derive any
  additional quotient before using it to remove a direction.
- From the positive form construct its null-space quotient and prove the
  desired operator/translation insertions preserve that null space and have
  their claimed adjoints. Finite test projection is not multiplicative, so it
  cannot establish this by itself.
- Supply the positive normalized state/density or appropriate reconstruction
  data, stationarity/transfer premises and nontrivial normalization required
  by the specific claim. If an equilibrium trace or Gibbs transfer is claimed,
  show its full source/action correspondence with the periodic fermion
  functional; a possible graded trace or a boundary twist cannot be replaced
  silently by an ordinary positive thermal trace.
- Reproduce the original complete physical J/j response through the required
  first/mixed-second order including contacts. Temporal Q and dressed crossing
  vertices must be represented by their actual boundary insertion maps, not
  assumed to be time-local Hermitian operators because a scalar pair passed.

If these are not supplied, record only normalization/reflection-form progress;
do not record a physical thermal state. Regulator/continuum/source-selected
limits, same-background microscopic matter matching, and later tensor/transport
claims still need their original evidence. No generic transfer or Gram theorem
is a substitute for these correspondences.

## 7. Ownership, next substantive step, review and authority

Executor owns this bounded original-action certificate construction; Publication
ROOT retains all ordinary L1 readiness, source consistency, manuscript/Visser
repairs, canonical findings/queue and integration. Existing PR115 W1/W2 and
the primary L1FixedControls notebook remain the continuity route; this document
is a scientific contract, not a second scheduler or disposition ledger.

Next source-level acceptance step: independent math review of (A),(P),(I),(G),
all degree and gauge-equivariance arguments, and independent physics/source
review of the actual-action/image/reflection and literature correspondences.
Then return the exact reviewed certificate target and any necessary physical
fork to Publication. A coupling/state/source domain not fixed by original
physical input requires early ROOT/operator clarification; do not choose one
after inspecting positivity or the desired chi range. This does not cancel
the still-open N4 full tensor assignment or reduce original acceptance.

Only AFTER this independent review may a separate evaluation proposal be
considered. It must choose a complete analytic/certificate representation,
specific resource limits and consumed-source/result verification; current
controller/slot/native authority must be reconciled separately. This contract
admits no brute-force enumeration, cap increase, blind retry, job, Lean worker,
test/harness change or code implementation. No computational feasibility is
promised by finiteness or the lower safe bound.

Even a successful finite certificate cannot establish the original B3
Lambda-squared normalization and [0.1,10] range, a spin-2 pole/common matter-light
cone, causal spectral/transport matching, or full W1/publication readiness by
itself. Pureg2 literal G=B=0 at finiteN wherever normalized remains in force.
All original scientific requirements and final human approval remain intact.
