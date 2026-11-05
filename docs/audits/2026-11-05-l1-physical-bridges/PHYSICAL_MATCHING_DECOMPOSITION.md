# L1 physical matching: collective metric, dressed source and units

Status: author research construction for independent review, not physical closure.
Parent construction: `b804fb426d722d3597b06f821e91d22b67c8d6f7`.
The clean parent branch is preserved pending publication-owned absorption.
This follow-on remains scratch until the checkpoint transition is reconciled.

## 1. What the inspected original sources define

[Diakonov 2011 v1](https://arxiv.org/pdf/1109.0091v1), section V, defines the
lattice links/plaquette (13),(17), composite coframe (23), actions (24),(25),
Berezin/Haar integrals (26),(27) and partition (28). Its lattice spacing cancels
from the displayed action after substituting the composite. The couplings in
(28) are dimensionless. These equations specify the regulated zero-source theory;
they do not specify our independent scalar field or its polynomial metric family.

[Volovik 2023 v2](https://arxiv.org/html/2312.09435v2), section III, (18)–(22),
proposes a vestigial metric as the expectation of the tetrad pair with vanishing
one-tetrad expectation, and discusses bosonic matter actions on that metric.
Its collective metric is an ordinary expectation, not an unintegrated nilpotent
configuration metric. This section supplies no lattice scalar determinant or
matching coefficient for the parent candidate.

[Volovik 2020 v2](https://arxiv.org/pdf/2003.00915v2), sections II and IV, especially
(5), uses inverse-length coframes, inverse-length-squared covariant metric, and
dimensionless scalar field and mass parameter. Its scalar effective action is a
comparison on a nondegenerate metric. The conversion to conventional metric/field
units therefore requires an explicit scale map; the scalar parameter is not
already a mass in conventional energy units.

These are scoped readings of specific equations, not a claim that the entire ADW
literature lacks any other matter formulation. Historical research notes are
directional inputs, not independent verification of their claimed phase, sign,
mode-counting or coefficient bounds. The source definitions above do not by
themselves establish those claims.

## 2. Exact collective-metric response decomposition

Use the fixed finite regulator and regularity/denominator assumptions of the
parent common-source construction. This is its Euclidean comparison; no physical
Lorentzian continuation or positive state is inferred from the original metric
notation. Let Q_i be the symmetric tetrad-pair composite
in a fixed independent tensor/site basis, with all chosen cell weights absorbed
in source coordinates J_i. For multiple tensor indices, this convention avoids
silently counting off-diagonal entries twice. Write

`Z(J,j)=I_g exp[S_g(j) + sum_i J_i Q_i(j)]`,
`W(J,j)=log[Z(J,j)/Z(0,0)]`, `G_i=W_{J_i}`.

J is a linear composite source introduced for the collective response, not an
assertion that it is the physical metric background. j is the specified dressed
coframe strain with all its action contacts. If the observable is held fixed in
the reference coordinates, set Q_i(j)=Q_i; if it is coframe transported, keep
Q_i(j) and its derivatives. At J=j=0 put X=S_g,j. Exact differentiation gives

`G_i=<Q_i>`,
`A_ik=W_{J_i J_k}=Cov(Q_i,Q_k)`,
`B_i=W_{J_i j}=<Q_i,j> + Cov(Q_i,X)`,
`D=W_jj=<S_g,jj> + Cov(X,X)`.

All covariances are in the same normalized functional. They may be signed. If a
source-dependent measure/regulator is present, its specified logarithmic/action
contributions enter X and its derivative as in the parent; they are held fixed in
the displayed gravity-only specialization. For the parent finite-lambda joint
theory the same block identities apply with its full effective L and normalized
weight in place of S_g and the pure-gravity weight.

Assume A is nonsingular on explicitly retained physical coordinates in a source
neighborhood; this is an additional requirement to establish, not a consequence
of a positive scalar two-time dressed pair. Any gauge/constraint quotient must
be derived before choosing those coordinates. Then the inverse function theorem
gives a local J=J(G,j). Define the partial Legendre transform

`Gamma(G,j)=J(G,j).G-W(J(G,j),j)`.

At the matching point its exact Hessian blocks are

`Gamma_GG = A^-1`,
`Gamma_Gj = -A^-1 B`,
`Gamma_jj = -D + B^T A^-1 B`.

Proof: differentiate G=W_J at fixed G to obtain J_j=-A^-1 B;
Gamma_G=J and Gamma_j=-W_j then give the three displayed blocks. No convexity or
positive-state property follows for the signed finite functional. This is a
local transform, not a global convex effective action theorem.

Consequently the dressed scalar response D alone determines neither the metric
covariance A nor its inverse kernel. The tangent map from strain to the
collective metric is B; if Q is transported by A_frame(j), B contains that
kinematic variation as well as its connected response. The previously reviewed
Legendre transform of the dressed conjugate variable W_j is a different
transform unless a correspondence to this G is proved.

The actual missing calculation is therefore identifiable: the same-regulator
collective body G, its composite-composite kernel A, its dressed-composite kernel
B (including kinematic contacts), and the full dressed block D, on the actual
retained observable/state domain. An arbitrary positive projection or change of
source normalization cannot replace those kernels. No four-site A or D is
silently assigned to the sixteen-site scalar example.

## 3. Why the polynomial body is not automatically the collective metric

The parent exact Gaussian construction uses the configuration family
`M=gbar+lambda Q`, where gbar is a positive real body input and Q has zero body.
The proposed physical metric of source (19), by contrast, is `G=<Q>` after
integration. Matching mean metrics would require

`<M>=gbar+lambda G=G`, hence `gbar=(1-lambda)G`,

in the SAME chosen measure. Changing lambda generally changes that measure
through the matter determinant, so using a pure-gravity G for every lambda is
not this equation's solution. A centered family can be written

`M=G+lambda(Q-G)=(1-lambda)G+lambda Q`.

If G is positive definite, its body is `(1-lambda)G`, positive only for lambda<1
for real lambda. At lambda=1 it is the zero-body composite itself, so the parent
inverse/determinant construction loses its positive body. This is a concrete
application of the existing zero-body inverse boundary, not a newly settled
microscopic no-go. The finite polynomial regulator does not justify that endpoint
or a uniform limit to it. At lambda=0 matter sees the collective metric with no
configuration-level fluctuation coupling.

Thus neither matching the mean nor adding a positive body derives the microscopic
matter coupling. A collective effective matter action on G is another possible
construction, distinct from configuration-level scalar integration. If one
proposes `Gamma_total[G]=Gamma_g[G]+Gamma_m[G]`, with
`Gamma_m=(1/2) log(det K[G]/det K_ref)`, its stationary equation is

`delta Gamma_g/delta G_i + (1/2) Tr(K[G]^-1 K[G]_{,i})=0`.

This supplies a concrete coupled saddle equation to solve on a justified
collective domain. It is NOT asserted to be the exact Legendre transform of the
microscopic joint theory: integrating metric fluctuations can introduce additional
terms, and avoiding double counting needs a specified matching/approximation.
No solution, positive body, large-volume limit or physical state is constructed
by writing this equation.

## 4. Explicit conventional-unit conversion

Let the source's dimensionful covariant metric be mathfrak G, with length^-2
units. Choose a positive CONSTANT conversion scale mu and write

`mathfrak G = mu^2 g`, `phi = mu Phi`, `m_phys = mu M`.

Here g is conventionally dimensionless, phi has conventional mass dimension one,
and Phi,M are the dimensionless scalar field/parameter of source (5). Constant
rescaling gives

`sqrt(det mathfrak G)=mu^4 sqrt(det g)`,
`mathfrak G^-1=mu^-2 g^-1`.

With a fixed common scalar-action convention, substitution yields

`(1/2) integral d^4x sqrt(det mathfrak G)
 [mathfrak G^-1(dPhi,dPhi)+M^2 Phi^2]`
` = (1/2) integral d^4x sqrt(det g)
 [g^-1(dphi,dphi)+(mu M)^2 phi^2]`.

Similarly `R(mathfrak G)=mu^-2 R(g)`, so a dimensionless coefficient kappa of
`integral sqrt(det mathfrak G) R(mathfrak G)` becomes `kappa mu^2` in conventional
units. This is a conversion identity, not a computation of kappa, mu or the B3
response. A position-dependent mu would add gradient terms and is outside this
constant conversion.

Four-dimensional Maxwell density is unchanged under this common constant metric
rescaling because its volume and two inverse metrics cancel the powers of mu.
It can constrain a cone but cannot by itself calibrate that common scale. An
independently normalized massive observable could calibrate mu only after its
dimensionless model parameter M and physical identification are established.

Changing mu while transforming g, phi and masses consistently is a change of
conversion convention, not a physical fitting parameter. Dimensionless predictions
cannot be moved into [0.1,10] by that change. A physical statement relating a
cutoff in external energy units to the emergent metric needs a calibrated map.
The parent mass-four static-strain and possible mass-two gradient coefficient
distinction remains conditional on this conventional field/source convention.

## 5. What follows and what is still owed

The inspected original equations supply the composite expectation definition and
effective matter comparison, but they do not identify the parent's configuration
family with that collective metric. The precise decomposition above exposes the
required mixed/collective kernels, body/saddle equation, and unit conversion.
It does not establish that every physical completion is underdetermined, or that
another original construction cannot supply the matching. The absence claim is
restricted to the inspected equations and parent extension.

Next physical matching must choose or derive, prospectively from the intended
regulated theory, how matter samples the collective or configuration metric,
which source implements it, and which normalized response coefficient B3 means.
Then compute or bound the actual G,A,B,D and denominator/physical-state domain,
using existing accepted kernels where their regulator/source contracts match.
If a collective approximation is used, derive its error/limit and feedback terms.
No favorable path sign, fitted source factor, selective observable span or assumed
positive state can stand in for those inputs.

Original B3 normalization and range, tensor dynamics/matter-light correspondence,
causal reconstruction and controlled observational propagation remain open.
This construction does not authorize reduced scope, deferral, finding closure,
Lean admission, harness change or publication qualification.
