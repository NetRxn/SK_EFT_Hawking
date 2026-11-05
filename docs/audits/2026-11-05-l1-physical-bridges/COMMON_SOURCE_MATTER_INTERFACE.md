# L1 common-source gravity and scalar-matter interface

Status: author construction for independent mathematical and physics review.
Publication parent: `425324077b03d7de1db9f4a342f5a760bf7af001`.
Executor owns this bounded interface; publication retains L1 acceptance and integration.
This is source-level research, not an accepted positive state, microscopic matching,
Lean proof, completed pipeline wave, derived B3 interval or tensor/transport result.

## Purpose and reused inputs

The reviewed successor roadmap in PR115 selects background/matter matching of the
existing closed curvature-dressed source. This construction composes existing
ingredients into one finite-regulator functional and derives its complete source
vertices. It does not repeat the selected-word campaign or claim its terms sum a
partition function.

Reuse [the spectral interface](../2026-10-17-publication-substance-construction/L1_RETARDED_SPECTRAL_INTERFACE.md),
specifically “Candidate curvature-dressed operator from coframe shear”, “Metric
amplitude and the linear-path contact”, “Polynomial scalar coupling about a
nondegenerate background”, and the joint-response construction preceding it.
Those records already supply the gravity variations, nilpotent scalar coupling,
determinant expansion and first-order factorized mixed-response identity.
Reuse [the regulated scalar bubble](../2026-10-17-publication-substance-construction/L1_REGULATED_SCALAR_BUBBLE.md)
for its explicitly dimensionless two-propagator integral. None is newly certified here.

The additional composition is the all-orders finite-algebra joint functional,
its explicit metric-to-kernel first/second variations, and its common-source
path-contact identity including matter. The dimensional matching below specifies
which coefficient a future microscopic calculation must actually derive.

## 1. Finite-regulator domain

Fix a finite periodic lattice, a finite real Grassmann algebra, and the original
closed-order gravity action `S_g(T,U)` with exponent convention `exp(+S_g)`.
Use its normalized product Haar and fixed oriented Berezin integration `I_g`.
All metric and action insertions below are even, so their coefficient algebra is
commutative although their world-index matrices need not commute.

Require C² source dependence of every coefficient of the action, metric family,
measure factor and any varied regulator/difference maps on a common source
neighborhood. Require a uniform strictly positive lower bound for the scalar
body kernel there. Coefficientwise integrands and their source derivatives through
order two must admit a common integrable envelope for the fixed Haar/Berezin
coefficient integrals and the ordinary scalar Gaussian integral. These hypotheses
justify the differentiations below; pointwise positivity and nilpotence alone
do not. For a finite lattice, smooth polynomial link/composite data on compact
Haar groups and the analytic source paths of section 5, one can shrink to a
compact source neighborhood: coefficient derivatives are bounded, the body gap
is uniform, and a polynomial in phi times a fixed decaying Gaussian supplies
the envelope. A proposed moving-domain prescription must establish its own bounds.

Let theta denote finitely many ordinary real external source coordinates. On a
neighborhood of zero set

`M_x(theta,lambda) = gbar_x(theta) + lambda Q_x(theta)`.

Here gbar is a real symmetric positive-definite body metric and Q is a symmetric
positive-Grassmann-degree tensor, built from the existing composite when that
candidate is used. Lambda is an ordinary real matching coefficient; it is not
fixed by this definition. The finite positive-degree ideal is nilpotent. Thus
`M^-1` and `rho = sqrt(det M)` exist exactly by terminating expansions around
the positive body. Matrix nilpotence follows from that common ideal, not from
assuming arbitrary matrices with individually nilpotent entries are nilpotent.

Fix the lattice difference maps, cell weights and a positive scalar mass. Assemble
the real symmetric scalar kernel from the action

`S_m = (1/2) sum_x w_x [sum_mu,nu (D_mu phi)_x F_x^{mu nu}
                       (D_nu phi)_x + m^2 rho_x phi_x^2]`,
`F_x = rho_x M_x^-1`.

The exponent is `-S_m`; any factors of one half are in this convention. Its body
kernel is positive definite. Gaussian integration against its positive body,
followed by the finite nilpotent expansion, defines the scalar integral exactly.
This does not supply positivity for the subsequent signed gravity integral.

For possible source-dependent measures, write a specified smooth invertible
measure factor as `exp J(theta)` on a fixed reference domain. Moving regulator,
link or difference-map effects must be pulled back and differentiated too;
they cannot be represented by an unspecified J and silently omitted. The concrete
comparison in section 5 holds all those structures fixed and takes J=0.

## 2. One normalized functional and exact scalar elimination

Choose a source-independent positive reference kernel K_ref. Define

`Z(theta,lambda) = I_g integral dphi/(Gaussian reference normalization)
                  exp[S_g(theta) + J(theta) - phi^T K(theta,lambda) phi/2]`
`                = I_g exp[S_g(theta) + J(theta)]
                  det(K(theta,lambda)/K_ref)^(-1/2)`.

The determinant ratio means `det K / det K_ref`; matrix quotients are not needed.
The real logarithm of its positive body and the terminating nilpotent logarithm
define the half power unambiguously. One must still establish `Z(0,lambda) != 0`
for the full gravity integral. Conditional on this, continuity gives a source
neighborhood of constant nonzero sign. Set

`W(theta,lambda) = log[Z(theta,lambda)/Z(0,lambda)]`.

The ratio is positive locally even if both Z values are negative. All source
derivatives here hold lambda fixed. No positive probability interpretation is
implied. Write

`L = S_g + J - (1/2) log(det K / det K_ref)`, `C = K^-1`,
`<O> = I_g(O exp L) / Z`.

For source labels a,b, differentiation of the finite expansion and convergent
body Gaussian gives

`V_a = L_a = S_g,a + J_a - (1/2) Tr(C K_a)`,
`Q_ab = L_ab = S_g,ab + J_ab
                    + (1/2) Tr(C K_b C K_a) - (1/2) Tr(C K_ab)`,
`W_a = <V_a>`,
`W_ab = <Q_ab> + <V_a V_b> - <V_a><V_b>`.

Proof: `C_b = -C K_b C`, the trace log derivative is `Tr(C K_a)`,
and differentiating any normalized expectation gives
`partial_b <O> = <O_b> + <O V_b> - <O><V_b>`.
Trace cyclicity makes Q_ab symmetric. These are algebraic connected expressions,
not positivity assertions for the signed functional.

The term `Tr(C K_b C K_a)/2` is the scalar connected contribution conditional
on a fixed geometry. It is distinct from the outer connected gravity average.
`-Tr(C K_ab)/2` is the scalar action contact. Matter also changes the gravity
weight and both first vertices. Adding an isolated matter covariance to an
unchanged pure-gravity covariance generally misses all these effects.
At lambda=0, if K is independent of geometry and J factorizes, the functional
factorizes and W_ab is the sum of the two full Hessians, each with its contact.
The previously reviewed first-order mixed-response convolution is a special
factorized perturbative test, not the full finite-lambda result.

## 3. Explicit metric-to-kernel first and mixed-second vertices

At each site write `B=M^-1`, `H_a=M_a`, `H_ab=M_ab`,
`s_a=tr(B H_a)`, with lower-case trace over world indices.
There is no assumption that B and H commute. Direct differentiation gives

`rho_a = rho s_a/2`,
`rho_ab = rho [s_a s_b/4 - tr(B H_b B H_a)/2 + tr(B H_ab)/2]`,
`F_a = rho_a B - rho B H_a B`,
`F_ab = rho_ab B - rho_a B H_b B - rho_b B H_a B
        + rho B H_b B H_a B + rho B H_a B H_b B - rho B H_ab B`.

Insert F_a,F_ab and rho_a,rho_ab in the SAME lattice quadratic form to obtain
K_a,K_ab. In particular H_ab includes the second derivative of Q as well as
of the body metric. These identities hold exactly over the finite even algebra;
they require no unjustified inverse of a zero-body composite.

They reproduce the existing first-order density at M=gbar and the existing
affine `I+tP` second-order density for trace-free Frobenius-unit P. This reuse
does not determine gbar, lambda, the physical source path, or the observable algebra.

## 4. Required correspondence with the dressed gravity vertex

For a prescribed coframe family `T(theta)=A(theta)T`, fixed holonomies and measure,
write the curvature bilinear as the already symmetrized `B_g(T,T)` to distinguish
it from the inverse metric B above. Its source derivatives are

`S2_a = 2 B_g(A_a T,T)`,
`S2_ab = 2 B_g(A_ab T,T) + 2 B_g(A_a T,A_b T)` at A=I.

Multiply these by g2 in the gravity exponent, and retain variations of S4 unless
the chosen family is demonstrably determinant one. For the earlier shear
`A=exp(jE)`, these specialize to the reviewed dressed operator and contact.
The metric-source conversion is `h=2 sqrt(2) j` for `P=E/sqrt(2)`.

A common source must specify M(theta,lambda) along with A(theta), not merely use
the same letter h. Internal gauge covariance alone leaves source admixtures and
normalization free. The first gravity vertex in section 2 is the dressed source
only if the chosen background extension gives this S_g,a; the full joint vertex
also contains the matter trace term and any specified J_a.

## 5. A concrete common deformation and its contact discriminator

This is an explicit candidate comparison family, not a derived microscopic match.
Take gbar=I at zero source and Q a symmetric composite world tensor. Define

`M0=I+lambda Q`, `T(h)=A(h)T`, `M(h)=A(h) M0 A(h)^T`.

Thus the positive body and nilpotent tensor transform together. It is not the
prescription that strains gravity but leaves the scalar background fixed.
Keep the scalar coordinates, difference maps, reference kernel, holonomies and
measure fixed. Take the reviewed diagonal unit plus tensor
`P=diag(0,0,1,-1)/sqrt(2)` and compare

`A_exp(h)=exp(hP/2)`, `A_aff(h)=sqrt(I+hP)`.

Both have A(0)=I and A'(0)=P/2, but
`A_exp''(0)=P^2/4`, `A_aff''(0)=-P^2/4`.
They give identical M_a, gravity first vertices and full V_a at h=0, for every
lambda where the normalized functional exists. Their outer connected term in
W_hh is therefore identical. If `mathcal W(A,lambda)` is the common normalized
log functional with independent A, the chain rule gives the exact joint identity

`W_aff''(0,lambda)-W_exp''(0,lambda)
       = -(1/2) D_A mathcal W(I,lambda)[P^2]`.

Its right side includes the scalar determinant and its gravity reweighting.
The pure-gravity dilation moment cannot replace it at finite lambda. Transverse
exchange flips P but preserves P², so a vanishing shear one-point function does
not eliminate this dilation response. Neither full-Hessian sign selects a state.

An explicit matrix check is available: with `B0=M0^-1`, `rho0=sqrt(det M0)`,
the exponential path has constant rho and

`F_exp' = -rho0(P B0+B0 P)/2`,
`F_exp'' = rho0(P^2 B0+2P B0 P+B0 P^2)/4`.

The affine path has `rho_aff''=-rho0/2` and

`F_aff'' = rho0[3(P^2 B0+B0 P^2)/4 + P B0 P/2 - B0/2]`.

Their difference is `rho0[(P² B0+B0 P²)/2-B0/2]`, as also obtained by the
dilation chain rule in section 3. The mass term keeps its rho_aff'' contact.
These are noncommuting-matrix identities; Q need not be diagonal.

At lambda=0, for the free periodic scalar with unit body metric,
`K0(p)=sum_mu phat_mu^2+m^2`, both first derivatives are
`K'(p)=(phat_3^2-phat_2^2)/sqrt(2)`, while

`K_exp''(p)=(phat_2^2+phat_3^2)/2`,
`K_aff''(p)=phat_2^2+phat_3^2-K0(p)/2`.

The scalar Hessian is `sum_p[(K'/K0)^2-K''/K0]/2`, not its first term alone.
This recovers the existing affine contact control and supplies a direct
zero-coupling check of the joint path comparison, without a geometry contraction.

## 6. Dimensional matching and the original B3 scale

Use four-dimensional natural units only for this dimensional check. If a uniform
source h has mass dimension d_h and beta V has dimension mass^-4, then

`[ (beta V)^-1 W_hh ] = mass^(4-2 d_h)`.

For dimensionless metric strain this is mass^4. A Fourier kernel H(p) defined by
`W^(2)= (1/2) integral d^4p/(2pi)^4 h(-p) H(p) h(p)` also has dimension mass^4.
If a controlled derivative expansion exists, its p² coefficient has dimension
mass². No such expansion, analyticity, tensor projection or locality is assumed
proved here. A static zero-momentum Hessian is not automatically that coefficient.
For a dimensionful effective field the source-to-field map changes this accounting
and must be derived explicitly.

The inspected bubble has measure dimension four and two scalar propagators of
dimension minus two each, hence dimension zero. An actual numerator of dimension
n makes that integral have dimension n before matching coefficients and
subtractions. A dimension-two numerator or derived dimensional matching factors
could yield a dimension-two quantity; metric stress vertices can instead give a
dimension-four response whose momentum-expansion coefficient is dimension two.
These are alternatives to distinguish by the microscopic derivation, not allowed
choices for forcing the original scale.

Before comparing any result with `O(Lambda_UV²/(16 pi²))`, specify which projected
response or effective-action coefficient carries that scale, the physical h/field
normalization, regulator, units, subtractions and controlled approximation.
Then derive the dimensionless chi and its stable domain. The original [0.1,10]
requirement remains a result to obtain or seek explicit disposition for; this
construction supplies no range or reduced acceptance criterion.

## 7. Acceptance boundary and next discriminating input

The candidate in section 5 is a concrete common-source finite lattice extension.
It does not derive the positive body, lambda, why this extension is the intended
physical background, positivity of the retained observable algebra, or a transfer
state. A full joint partition denominator remains required; selected positive
terms cannot supply it. No four-site gravity coefficient is silently combined
with a sixteen-site scalar kernel.

The immediate physical matching task is to determine from the intended regulated
action and matter construction whether the same M and A really are sourced, which
observable directions remain physical, and which coefficient B3 intends to
normalize. A prospective physical source prescription or a well-supported
underdetermination result must be independently reviewed. One may not select the
affine/exponential path, lambda, source admixture or projected direction after
seeing which yields a favorable sign or target range.

W3 still requires constrained tensor dynamics and the same-background matter/light
cone. W4 still requires real-time or justified reconstruction information and a
controlled propagation regime. No static scalar identity here proves either.

Verification owed: independent mathematical review of finite-algebra Gaussian
elimination, ordered matrix derivatives and the joint chain rule; independent
physics review of correspondence, units and acceptance scope. Supporting Lean
targets require project/Mathlib/type/dependency reconciliation and controller
admission after those reviews. No new formula API, axiom, settled no-go, source
claim closure, slot use or infrastructure change is introduced by this report.

## 8. Author verification and review correction

The frozen first draft (SHA256
`8b30768c41d90b542f4d776f726833a9ee248ed1d0995f302ae2490cf8239bc2`)
received a mathematical BLOCK for missing explicit regularity/interchange
hypotheses; physics review agreed this correction was necessary and found no
additional physical error. Section 1 now states the C², uniform body-gap and
coefficientwise domination conditions. Without them, even the positive body
`gbar(h)=diag(1+|h|,1,1,1)` on a single-site periodic scalar lattice can give
`W(h)=-(1/4) log(1+|h|)` with no derivative at zero. This is a countercontrol
for the general inference, not a microscopic no-go or a new settled-fork claim.
Final revised-source acceptance is to be recorded in separate reviewer artifacts.

An author stdlib Fraction sum over the sixteen unit-mass/unit-spacing scalar
momenta checks section 5 at lambda=0: the shared connected variance is
`193312/342225`; the exponential full Hessian is `-6288976/5817825`; the affine
full Hessian is `7407044/5817825`. Their difference is `7804/3315`, also obtained
from the dilation formula as `4-5456/3315`. The independent mathematical reviewer
reproduced these sums. These compare scalar contacts only, with no geometry
integral, physical source selection, or new selected-word/coverage result.

Reused source pins at the publication parent: spectral interface SHA256
`6066a81c480080d825d1b8403eb92c97753e0ef366c188533c0df210473213ec`;
regulated scalar bubble SHA256
`9ad73436a0ae121725b60c12e39b856dbad6f58cf832176f984f6654d2b69053`.
