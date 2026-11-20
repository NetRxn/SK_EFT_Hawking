# Original N16 transfer operators, trace and metric-source insertions

Manual constructive candidate for independent mathematical and physics review.
This builds actual operators and source vertices from the unchanged original
finite action. Its Hilbert space is an AUXILIARY coefficient/Haar space. It
does not supply a positive physical state, physical adjoint, CAR dictionary,
nonzero partition or continuum/thermal interpretation. No scientific evaluator,
CAS/matrix/Haar test, contraction, native/Lean or slot job has been run.

## 1. Original fields and exact three-slice locality

Keep the original closed exp(g1 S4+g2 S2), literal metric sources J and
prescribed C2 world-frame sources j of N16_TEMPORAL_BOUNDARY_IDENTITY.md.
All original endpoint terms, full curvature plaquettes/internal channels and
physical source contacts remain. This is the Diakonov(23)-(28) benchmark;
its higher-term ellipsis is not added. Existing physical matching and the
separate original normalization/N4 obligations are unchanged.

One spatial layer has eight sites. Denote its data by q_t=(u_t,xi_t):
u_t contains the24 spatial and8 temporal directed Spin(4) links ANCHORED in
that layer; xi_t contains its64 Grassmann generators in the original
bars-before-psis orientation. Let G be the compact product of these32 link
groups, dh its normalized Haar, Theta_t its Grassmann top and I_t its
coefficient extractor. Keeping temporal links in u_t is just a regrouping
of the SAME64 independent links. They are not gauged away or identified.

Before periodizing the time direction, a coframe at t uses fields at t and
t+/-1 and temporal anchors t,t-1; a spatial coframe uses only t. A temporal
plaquette based at t uses temporal anchors t and spatial links t,t+1. A
spatial plaquette uses only t. Thus the FULL source-deformed density based
at t has the precise locality

    s_t=s_t(q_(t-1),q_t,q_(t+1);J,j),      w_t=exp(s_t).

This includes Q00/Q0i and frame families mixing time with space. Those may
cross the cut, but require no additional layer. All s_t are Grassmann-even,
of positive degree (4 or8 for this source contract), and all w_t are finite
Grassmann polynomials with polynomial functions of the compact links as
coefficients. Source dependence is C2. No inverse kernel is introduced.

For t=0,1 write independent formal layers a,b,c,d in time order. For the
original PERIODIC two-cycle the exact full density is

    w_1(b,a,b) w_0(a,b,a),

with b identified as layer0 and a as layer1. Periodization substitutes
the same vertex fields at both temporal endpoints, while their directed
links remain distinguished: the base link is in b, the backward anchor in
a (and conversely for w1). This is precisely the original Nt2 geometry.
Substitution in an exterior polynomial automatically handles repeated fields;
independent copies are not integrated as if they were different physical sites.

## 2. A concrete bounded transfer operator on adjacent slice pairs

Use the positive auxiliary Hilbert space

    H=L2(G x G,dh dh) tensor Lambda(C^128),

with the exterior monomials orthonormal and the SAME normalized bare Haar.
This positive norm is coefficient bookkeeping, not gravity-state positivity.
Identify the128 formal pair generators as (xi_a,xi_b), each block oriented
as above. A wavefunction Phi(a,b) is an L2 coefficient function of those
compact links, valued in that exterior algebra. Define, EXACTLY,

    (T_t Phi)(b,c)=integral dh_a I_a[ w_t(a,b,c) Phi(a,b) ].       (T)

Outputs use pair order(b,c). Input and output copies are relabeled by the
fixed identification of their layer coordinates; the shared b variables are
literally the same variables during this operation. Each I removes64
generators, an even number. Together with even w_t this makes T_t parity
preserving on the pair exterior space. Full compact link integration of a
and the displayed Grassmann contraction specify every matrix coefficient;
no physical CAR or favorable basis/projection is selected.

Boundedness: w_t has finitely many exterior coefficients, each bounded on
the compact link groups. Multiplication in a fixed finite exterior space
has a finite operator-norm bound in the coefficient norm. Cauchy-Schwarz
for the normalized a-Haar integral, followed by b,c integration, therefore
bounds ||T_t Phi||_H by a finite constant times ||Phi||_H. This defines T_t
on all H, not only polynomial wavefunctions. Source derivatives through
order2 satisfy the same bounds on a compact source neighborhood.

Compose (T) WITHOUT averaging or factorizing a weight prematurely:

    ((T_1 T_0)Phi)(c,d)
       =integral dh_a dh_b I_a I_b[
          w_1(b,c,d) w_0(a,b,c) Phi(a,b)].                       (K)

Both extractors have even degree and commute. The weights are even, so their
order introduces no exterior sign. In the displayed kernel, output order is
(c,d) and input order(a,b); rewriting to that order includes all ordinary
Grassmann reordering signs. Denote this actual operator by K=T1 T0.

K is FINITE RANK: its kernel is a finite polynomial in exterior variables
and actual compact-link coordinate functions of all four formal layers.
Expand its ordinary coefficient functions into finite sums of output-only
times input-only polynomials. Each term is a rank-one L2 kernel, tensored
with a finite exterior matrix. No cutoff, physical projection or approximation
has been imposed; the action's finite Grassmann expansion itself gives the
finite polynomial kernel. T_t alone need not be finite rank because one layer
is shared. K and its source derivatives have legitimate finite-rank traces.
No rank value, coefficients, positivity or feasible evaluation cost is asserted.

## 3. Derive the periodic trace sign instead of assuming a Gibbs trace

Here is the exact coefficient calculation. For any even finite polynomial
pair kernel, put output variables xi before input variables eta, N=128, and
write

    k(xi,eta;u,v)=sum_(I,L) k_(I,L)(u,v) xi_I eta_L.

The input top extraction of eta_L eta_J is epsilon(L,J) if L=J-complement
and zero otherwise. Hence the operator kernel matrix in the orthonormal
exterior basis is

    [K_(I,J)](u,v)=k_(I,Jc)(u,v) epsilon(Jc,J).

For a finite-rank continuous polynomial kernel its ordinary trace is the
integral of its diagonal matrix entries. Define Gamma xi_I=(-1)^|I| xi_I,
acting trivially on link coefficients. Since N is even,

    epsilon(Ic,I)=(-1)^|I| epsilon(I,Ic).

Therefore, EXACTLY,

    Str K := Tr(Gamma K)
       =integral dh_u I_xi[k(xi,xi;u,u)],
    Tr K=integral dh_u I_xi[k(xi,-xi;u,u)].                     (trace)

The second line uses (-1)^|Ic|=(-1)^|I|. Gamma is fixed by the original
Berezin/top convention; it is not a positive-sector projection or a chosen
physical fermion-parity interpretation. K is even and commutes with Gamma.

A manual two-generator sign control makes this explicit: the identity
operator has kernel

    k_id(x,y)=y1 y2-x1 y2+x2 y1+x1 x2.

It extracts f(y) to f(x). At y=x the top coefficient is0, the supertrace
of identity on Lambda(C^2); at y=-x it is4, its ordinary trace. This is
an algebraic sign check, not a new physical model or evaluator run.

Apply (trace) to (K), setting(c,d)=(a,b) on the diagonal and retaining
every original link occurrence before Haar integration. The exact original
partition and full source functional are

    Z(J,j)=Str[T1(J,j) T0(J,j)].                               (Z)

The Grassmann top is Theta_a Theta_b; exchanging its two64-generator
blocks to the original layer0/layer1 order has positive sign. Link Haar is
the SAME64-factor product. Thus there is no free orientation or trace sign.

For comparison only, the ordinary trace in (trace) closes the pair with
output fields=(c,d) and input fields=(-c,-d). Identifying b as time0 and c
as time1 gives weights w1(b,c,-b) w0(-c,b,c): this is exactly ANTIPERIODIC
temporal fermions, with all links periodic and independent. This establishes
the compared trace closure, not adoption of a new physical boundary. Neither
trace is certified positive/thermal. The auxiliary exterior parity need not
be the physical fermion-number operator of an original quantization.

## 4. Original metric insertions: an actual operator/source dictionary

For a literal SPATIAL metric combination Q_f at layer0, fixed at j=0, it
depends only on b. Let M_f^(2) be its actual wedge-multiplication operator
on the SECOND member of the input pair(a,b), and M_f^(1) the corresponding
operator on the FIRST member of an output pair(b,c). They are bounded
because their exterior space is finite and link coefficients are bounded.
Directly from (T), without division or an assumed quantization,

    T0(J_f=t,j=0)=T0(0,0) exp(t M_f^(2)),
    T0 M_f^(2)=M_f^(1) T0.

Thus its full literal-source functional and all its insertions are ACTUALLY
represented by

    Z_f(t)=Str[K exp(t M_f^(2))],
    Z_f^(n)(0)=Str[K (M_f^(2))^n].                            (insert)

This is a source-derived operator formula for the original Grassmann
observable, not an operator chosen to fit positivity. M_f is nilpotent:
the spatial-half bound is (M_f)^17=0. Under the POSITIVE AUXILIARY coefficient
norm, multiplication by an elementary generator has exterior contraction
as its adjoint, not multiplication by another generator. Likewise the
Hermitian adjoint of M_f is determined by that norm and is NOT declared to
be the physical adjoint of a metric observable. A nonzero bounded nilpotent
operator cannot be self-adjoint, so a nonzero M_f cannot simply be named
the physical self-adjoint metric. This observation states the unfinished
physical correspondence; no new nilpotent-moment no-go is inferred.

Q00/Q0i and other crossing insertions have a different exact dictionary:
they occur inside w_t(a,b,c), so their source vertices are the integral
operators (T_t)_,a derived by inserting the original s_t,a into (T). They
are not falsely factored as half-local multiplication operators. For any
prescribed source coordinates a,b, with measures and links held fixed,

    (w_t)_,a=w_t s_t,a,
    (w_t)_,ab=w_t(s_t,a s_t,b+s_t,ab).                         (jets)

This constructs (T_t)_,a and (T_t)_,ab concretely by the SAME integral (T).
In particular the transported metric/source variation Q_,j and original
S_,jj contacts are retained. No inverse of w_t, T_t or K is taken.

Differentiating the actual trace, including a source that acts on both base
layers, gives the complete first/mixed-second source identities

    Z_,a=Str[(T1)_,a T0+T1 (T0)_,a],
    Z_,ab=Str[(T1)_,ab T0+(T1)_,a (T0)_,b
                        +(T1)_,b (T0)_,a+T1 (T0)_,ab].        (Zjets)

Weights/derivatives have a common finite polynomial support and bounded
coefficients on compact source/link neighborhoods, so these exchanges are
justified in a fixed finite-rank coefficient space. The log-normalized
response, WHERE full Z!=0, is still Z_,ab/Z-Z_,a Z_,b/Z^2. No contact or
cross-layer term has been replaced by an ordinary-power identification.

## 5. Exact algebraic density and the physical state that remains unconstructed

There is now a concrete raw trace object on H, fixed by the action:

    D_raw=Gamma T1 T0,        Tr D_raw=Z.

Where Z!=0 its algebraic normalization D_alg=D_raw/Z has ordinary trace1,
and for the spatial insertion in (insert), Z_f^(n)(0)/Z equals
Tr[D_alg M_f^n]. These are actual original-source representation identities.
No ordinary density/state is claimed: D_alg need not be Hermitian or PSD,
and M_f need not be a physical self-adjoint observable. Tr1 alone is not
IsDensityOperator. Positivity or a physical reinterpretation cannot be
obtained by choosing a positive part, absolute weight or favorable subspace.

This construction explains concretely why the fixed positive one-mode
control of METRIC_OPERATOR_DICTIONARY_ATTEMPT.md does not identify bare
Grassmann multiplication with physical operator product. Here the actual
auxiliary source/trace is derived rather than an arbitrary CAR model; the
source-derived representation still has to be connected to an actual physical
boundary Hilbert space, constraints, adjoint and state. No control contact
prescription is imported to gravity.

Vergeles2506.00036v2, III-IV(3.9),(4.1)-(4.10), motivates looking for an
actual boundary transfer, but uses its Minkowski simplicial gauge/ONB/
normalizability/eigenbasis hypotheses. Its VI(6.1) composite extension is
retained, not dismissed. None of those hypotheses is silently used to make
the above auxiliary D positive or identify its trace with a Gibbs state.
The present construction keeps the original compact hypercubic model exactly.

The accepted full-symbol reflection obstruction remains in force. A physical
map preserving its entire original pairing cannot produce a positive pullback.
This operator trace does not bypass that theorem or certify a metric-only
state. Conversely no original physical impossibility follows merely from
its auxiliary wedge product or parity insertion. Actual original constraint/
boundary-state/adjoint/metric-source and controlled regulator/continuation
correspondence remains the substantive W1 construction, now with explicit
transfer operators and source vertices available as input.

Full Z/c0 nonvanishing, N4 tensor, B3 normalization/range, tensor/matter/light
and causal transport stay OPEN and owned. No evaluation, spectral/PSD value,
temperature, Hamiltonian, physical state, model or boundary choice is made.
No Lean proof task or runtime admission is inferred from this manual source
construction. Publication ROOT retains every ordinary L1 readiness, consumer,
manuscript/claims/repair/review/gate/integration and operator responsibility.

Independent math review must verify three-layer support, boundedness, even
integration signs, finite-rank kernel, trace/supertrace/top/closure formulas,
all original source vertices and contacts. Independent physics/source review
must check unchanged action/link/source custody, constructive-versus-physical
state distinction, original boundary interpretation and no favorable product/
state/quotient selection. This is a finite original-source operator construction,
not completion of the physical state or final publication/human acceptance.
