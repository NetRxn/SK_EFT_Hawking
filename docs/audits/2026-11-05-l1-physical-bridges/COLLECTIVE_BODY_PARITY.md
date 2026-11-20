# Finite pure-g2 collective metric: exact body/source parity diagnostic

Status: author calculation for independent mathematical and physics review.
Parent matching decomposition: `e79d6aa8c638032486eddb6d9f7c766f4c415df5`.
This is a concrete finite-regulator evaluation, not a new universal no-go or
kernel-verified settled fork. It reuses the accepted Pin/degree parity rule
in the spectral interface, “Stability under a small second action coupling”.

## Fixed prospective contract

Use a finite periodic lattice with N sites and eight independent Grassmann
generators per site, normalized product Haar on both Spin(4) chiral link factors,
and the fixed oriented Berezin top extraction of degree 8N. The boundary and
link measures must be invariant under simultaneous exchange of the two chiral
factors. Use the existing closed gravity action

`S=g1 S4 + g2 S2`, `deg S4=8`, `deg S2=4`.

There is no matter determinant (lambda=0), no external composite source (J=0),
no extra mass/kinetic/higher-derivative action term, and no source-dependent
measure or moving cutoff. Couplings and coframe sources are dimensionless lattice
coordinates. The positive scalar body of the previous polynomial matter candidate
is NOT inserted here. This test asks whether gravity itself supplies that body.

Let `Q_mu nu(x)=sum_a T_mu^a(x) T_nu^a(x)` in the Euclidean convention, or a
specified real linear combination of these components. Q is homogeneous degree
four and invariant under internal orthogonal reflections. Use the symmetrized
tensor if needed; the T coefficients are even and commute. This is the literal
tetrad-pair collective metric, not the curvature-dressed action derivative.

A fixed-link world coframe family `T(j)=A_frame(j)T` is allowed, with analytic
ordinary A_frame near I. Define Q(j) by transporting both coframes, or hold Q
fixed as the reference observable. The family changes neither Grassmann degree
nor the internal reflection character. For comparison with the accepted dressed
shear, take `A_frame(j)=exp(jE)`, `E=diag(0,0,1,-1)`.

## 1. Measure and action transformation

Take the Euclidean gamma convention of `l1_full_action_reference.py`. Set
`R=gamma_3=[[0,I2],[I2,0]]`, with `R^2=I4`, `det R=1` and
`R gamma5 R=-gamma5`. Apply at every site and link

`psi -> R psi`, `barpsi -> barpsi R`, `U -> R U R`.

On a chiral link `U=diag(U_L,U_R)`, conjugation exchanges U_L and U_R. Product
normalized Haar is unchanged. The site Berezin Jacobian is
`(det R)^(-1) (det R)^(-1)=1`; it preserves the recorded top orientation.
Both forward/backward parallel transports in the composite coframe transform
consistently. Internal vector components transform with
`O=diag(-1,-1,-1,+1)`, so O is orthogonal and det O=-1.

Every plaquette, in either fixed product ordering, transforms by conjugation.
For the closed action in this contract the chirality trace then gives

`S2 -> -S2`, `S4 -> -S4`, `Q -> Q`.

World coframe deformation commutes with this internal transformation, so these
identities hold for the entire prescribed A_frame(j) family. This is a change of
integration variables; it is not an asserted Spin(4) gauge transformation or
invariance of the fixed-g2 action by itself.

## 2. Raw collective numerator at g1=0

Top extraction of `Q exp(g2 S2)` can receive a contribution only from

`Q (g2 S2)^(2N-1)/(2N-1)!`.

Under the measure-preserving reflection this entire integrand changes sign:
Q is even and the number of S2 factors is odd. Consequently its Haar/Berezin
integral is exactly zero for EVERY component and every specified j:

`N_Q(j;0,g2)=I_g[Q(j) exp(g2 S2(j))]=0`.

This raw polynomial identity needs no denominator assumption. If the full
partition `Z(j;0,g2)` is nonzero on a neighborhood of j=0, normalized collective
metric G(j)=N_Q/Z is identically zero there. Thus

`G(0)=0`, `partial_j G(0)=0`.

Equivalently the mixed block of the previous decomposition obeys

`B_i=<Q_i,j>+Cov(Q_i,X)=0`, `X=g2 S2,j`.

One can check the latter directly: Q_i,j is another reflection-even quartic
insertion; Q_i X is degree eight and reflection odd, while saturation needs an
even number 2N-2 of ordinary S2 factors. The Q one-point subtraction is zero.
This direct proof also covers Q held fixed, for which Q_i,j=0.

Neither the composite-composite kernel A nor the dressed Hessian D is forced
to vanish: two Q insertions have even reflection character and even ordinary
S2 count; two action derivatives have the appropriate total even character.
The accepted positive dressed scalar pair is therefore compatible with this
zero collective body and zero mixed tangent. Its positivity cannot supply them.

For the accepted closed four-site pure-g2 normalization, N=4 and

`Z(0;0,g2)=g2^8 * 1252309350145403/2123366400 > 0` for real g2!=0.

Here the normalized G=0 and B=0 statements apply directly, using the existing
accepted denominator, not a new contraction. For the sixteen-site geometry the
raw numerator identity holds too, but its full nonzero denominator is NOT
established by this calculation or by selected-word coverage.

## 3. General coupling parity and the prospective next calculation

An action monomial with m S4 factors, n S2 factors and k literal Q insertions
can survive top extraction only if

`2m+n+k=2N`.

Its reflection character is `(-1)^(m+n)`, so measure invariance additionally
requires m+n even. Combining the two gives `m=k (mod 2)`. This is the previously
reviewed four-site rule applied with the actual lattice volume N.
It yields Z even in g1; every component of N_Q odd in g1; and the raw two-Q
numerator even in g1. Where normalization is defined, G and B are odd in g1,
while composite connected A and the fixed coframe-source dressed D are even.

For fixed g2!=0 put x=g1/g2^2. Homogeneity gives

`Z=g2^(2N) z(x)`, `N_Q=g2^(2N-1) q(x)`,
`G=g2^-1 q(x)/z(x)`,

where z is even and q is odd. Thus a nonzero finite-volume body on this family
requires leaving g1=0 or changing another stated assumption. This statement does
not predict its sign, nondegeneracy, physical stability or parameter range.
The actual leading body coefficient q'(0), and the corresponding mixed tangent
coefficient, are meaningful next SAME-regulator calculations. They must be
computed or bounded for the full component tensor; a traceless shear mean being
zero by spatial exchange is not an evaluation of its trace or positive body.
No arbitrary g1 value or favorable eigenvalue is selected by this result.

## 4. Physical interpretation and retained boundaries

This calculates an actual G/B diagnostic on the prescribed finite pure-g2
family. It identifies why the accepted positive dressed scalar result alone
does not reconstruct the metric expectation of the original vestigial proposal.
It does not assume the positive body or replace it with a unit matrix.

The conclusion is restricted to finite N, zero external composite source and
the stated uncoupled action/measure. A source-selected thermodynamic phase can
involve noncommuting limits in N and J; no uniform bound, phase selection or
limit interchange is established here. Matter determinant backreaction introduces
new degree/vertex terms, so the uncoupled calculation is not a result for the
finite-lambda joint theory. Other microscopic actions, constraints, source or
boundary choices require their own transformation analysis.

Source and field units remain those prospectively fixed above and in the parent
unit-conversion decomposition. This produces no scale calibration, positive state,
physical tensor propagator, chi interval or observational transport. It records
no operator deferral, reduced requirement or canonical settled no-go. Manual
acceptance, formal theorem admission/proof, and publication qualification remain
separate. Existing symmetry/source records are reused rather than reclassified
as a new numerical ensemble or coverage increment.
