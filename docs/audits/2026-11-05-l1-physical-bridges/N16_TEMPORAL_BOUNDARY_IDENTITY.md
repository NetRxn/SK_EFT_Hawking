# Same-action N16 temporal-boundary identity

Source-level manual construction for independent mathematical and physics/source
review. Parent contract: 942c50adb, adopted by Publication ROOT in 0d45d43d3.
No kernel evaluation, positive-state certificate, resource/Lean admission or
publication closure is asserted. Original N4 full tensor remains separately OPEN.

## 1. Fixed source, orientation and independent variables

Use the original closed gravity action and equation (1) coframes of
`ADW_EXACT_AUXILIARY_IDENTITY.md`, with its equations (7)-(10) signed Hermite
representation. No microscopic term or boundary condition is changed. Sites
are x=(t,r), t in Z/2, r in (Z/2)^3. Time is axis0. The periodic forward links
U_(x,mu)=diag(U_L,U_R) are independent at EVERY directed anchor: in particular
V_t(r)=U_((t,r),0) for t=0,1 are two independent variables, not inverse copies.
Normalized product Haar integrates all64 Spin(4) variables (48 spatial,16
temporal). There are four independent psi and four barpsi generators/site,
128 total. The exponent is +S with original dimensionless g1,g2 and coframe
quarter. No physical scale, source amplitude or coupling is fitted.

Let Y_x,mu,A denote the256 commuting formal coframe coordinates. Prescribe a
C2 world-frame family A_x(j), A_x(0)=I, at each base, before evaluating signs.
Put Y(j)_x,mu,A=sum_nu A_x(j)_mu,nu Y_x,nu,A. Its first/mixed-second jets are
part of the source contract, not selected by a positive result. The identity
below holds for ANY such prescribed family; it does not identify which family
microscopic matter physically sources. In particular it includes the already
specified affine/exponential paths with their distinct contacts, without
equating or selecting them. Holonomies, Haar/Berezin measure and regulator are
fixed. No compact-link deformation is silently substituted.

Write the ORIGINAL polynomial at base x as

    s_x(Y;U,J,j)=g1 S4_x(Y(j)) + g2 S2_x(Y(j),U)
                 + sum_(mu<=nu) J_x,mu,nu Q_x,mu,nu(Y(j)),
    Q_x,mu,nu(Y)=sum_A Y_x,mu,A Y_x,nu,A.

S2 uses all original ordered world indices, closed plaquette and quarters;
S4 keeps its internal epsilon determinant. Off-diagonal J occurs once. Smeared
source bases follow by a fixed linear map of these independent coordinates.
This is transported Q(j); a reference-held Q alternative would be a distinct
specified source, not this formula. At J=j=0 it is precisely the original
closed zero-source action, including S4. No matter determinant or B0 is added.

Choose the original oriented top coefficient. Regroup site blocks by time,
and then put all32 bars before all32 psis within each time slice. These changes
have positive sign: swapping two eight-generator site blocks costs (-1)^64,
and moving a four-psi block through a later four-bar block costs (-1)^16.
Let xi_t=(barpsi_t,psi_t), with64 entries in that order; Theta_t is its top
monomial and I_t its coefficient extractor. The original extractor is I_0 I_1
with Theta_0 Theta_1; no arbitrary global orientation sign is introduced.

## 2. Reuse the full-S4 weight; split the actual fermion matrix

Fix any source-independent sigma>0. In the already accepted Hermite identity
take total coframe-degree truncation M=64, and define at EACH site

    P_x(Y;s)=[exp(s_x(Y;s)) exp(-sigma^2 sum_i Y_i^2/2)]_(degree<=64),
    W_x(h_x,U;s)=sum_alpha p_x,alpha(U;s) sigma^(-|alpha|)
                                      He_alpha(h_x/sigma).

Here s abbreviates (J,j); dmu_sigma is the normalized real Gaussian for all16
h_x coordinates. W_x is signed/complex and is never replaced by an absolute
value. The chosen sigma cancels from the full identity; it is not a physical
parameter. Degree64 is safe because more than64 fermion bilinears vanish.
The source extension is allowed because the accepted identity is an algebra
identity before Berezin integration, and Q is polynomial in the same coframes.

Define the actual64x64 fermion matrix by h.T=barpsi M(h,U) psi, retaining all
four original endpoint terms. Its TIME split is

    M = [ M00  M01 ; M10  M11 ],
    E_t=barpsi_t Mtt psi_t,
    V=barpsi_0 M01 psi_1 + barpsi_1 M10 psi_0.

Mtt contains the spatial hoppings and is generally NONZERO. This is not the
checkerboard split used by the earlier squared-norm determinant control. No
inverse or nonsingularity of Mtt is required anywhere below.

At each spatial r, write D=V0(r)^dagger-V1(r), E=V1(r)^dagger-V0(r).
The cross blocks are diagonal in r, with exact4x4 spinor blocks

    M01(r)=1/4 sum_A [h_(0,r),0,A gamma_A D
                                  +h_(1,r),0,A D gamma_A],
    M10(r)=1/4 sum_A [h_(0,r),0,A E gamma_A
                                  +h_(1,r),0,A gamma_A E].

These follow by collecting T0 at BOTH temporal bases in equation (1): the
forward and backward endpoint coincide as a vertex on a two-cycle but their
anchored links remain independent. For real h and unitary links E=-D^dagger,
so M10=-M01^dagger. This is an auxiliary hopping identity, not positivity of
the integrated action or a new thermal Hamiltonian.

## 3. Exact fermionic bridge with its exterior sign

In xi_0-before-xi_1 order put

    C = [ 0  M01 ; -transpose(M10)  0 ],
    V=sum_(a,b) C_ab xi_0,a xi_1,b.

The minus in the lower-left block moves psi_0 past barpsi_1. For sorted
subsets A,B of {1,...,64}, of equal size k, define

    d_AB=(-1)^(k(k-1)/2) det(C[A,B]);       d_empty,empty=1.

Then the COMPLETE finite bridge identity is

    exp(V)=sum_(k=0..64) sum_(|A|=|B|=k) d_AB xi_0,A xi_1,B.       (B)

Proof: in V^k/k!, grouping all xi_0 before all xi_1 makes k(k-1)/2 swaps;
antisymmetrizing the two independently ordered index lists gives the minor
determinant. The factorial cancels the ordering multiplicity. This proof uses
all crossing fermionic channels, with no selected gamma/chirality slice.
All E_t and V are Grassmann-even, so their exponentials commute. For any
even half-local polynomial F_t set

    f_t,A(F_t;z_t)=I_t[exp(E_t) xi_t,A F_t].

Odd k entries vanish for even F_t by degree parity, but (B) retains the full
identity; odd intermediate factors must not be deleted before multiplication.
In particular F=1 returns the full determinant after all boundary subsets sum.

## 4. Complete bosonic kernel and same-source identity

Let z_t contain all128 h coordinates at time t and its24 spatial Spin(4)
links; dnu_t is their Gaussian/Haar product. Let v contain all16 temporal
Spin(4) links, with dnu_v their product Haar. Define

    W(z0,z1,v;s)=product_x W_x(h_x,U;s),
    K_AB(z0,z1;s)=integral dnu_v W(z0,z1,v;s) d_AB(z0,z1,v).        (K)

This is an explicit finite polynomial kernel, with coefficients defined by
normalized compact-group moments. Crucially a W_x based at time0 can depend
on spatial links at time1 through a time-space plaquette, and conversely.
Thus W is NOT assumed to be two independent half-amplitudes or a norm square.
All16 temporal links are integrated jointly in (K), after their occurrences
in EVERY W_x and in d_AB. No individual minor is asserted gauge-invariant or
eligible for independent tree fixing. The complete sum retains the original
gauge contraction; all64 physical links ultimately have their original Haar.

The exact same-action/same-source identity is

    Z(s;F0,F1)=integral dnu0 dnu1
                     sum_AB K_AB(z0,z1;s) f_0,A(F0;z0) f_1,B(F1;z1). (T)

It equals I_Haar,Berezin[exp(sum_x s_x(T;s)) F0 F1]. Proof: insert the already
accepted full-S4 Hermite identity, split h.T=E0+E1+V, use (B), and extract the
two oriented top coefficients. Even F0,F1 commute across the halves. Every
sum and Grassmann series is finite; remaining h integrals are polynomial
Gaussian moments with compact-link coefficients, so exchanges are justified.
The identity is exact for all finite g1,g2, not only the pure-g2 Wick slice.

At the reference j=0, spatial T_i(x), i=1,2,3, uses only its slice's fermions
and spatial links, so spatial Q_ij is half-local. A world-frame family mixing
time with space can make even its transported spatial components cross at
nonzero j; such dependence remains in K(s). T0 and Q_0i/Q_00 generally cross the cut. Dressed
action derivatives can cross too. Their insertions are obtained by differentiating
the COMPLETE K(s) in (T); they are not declared time-local operators f_t(F).
This explicitly retains the source-to-operator matching debt.

## 5. Full first and mixed-second contacts without division by W

Let H_sigma denote the linear truncated Hermite coefficient map above.
For source coordinates a,b, with all products truncated to degree64,

    W_x,a=H_sigma[exp(s_x) s_x,a exp(-sigma^2 Y^2/2)],
    W_x,ab=H_sigma[exp(s_x)(s_x,ab+s_x,a s_x,b)
                                              exp(-sigma^2 Y^2/2)].

Differentiate the full product W: its mixed second derivative includes both
same-site W_x,ab and all ordered distinct-site W_x,a W_y,b terms, each with
the remaining W factors. No logarithmic derivative W_a/W is used at zeros.
Since M and the auxiliary variables use reference T, d_AB and f_t stay fixed;
all prescribed source dependence is in W and K. This is a representation
choice, not omission of the strained gravity/matter operator.

In particular s_Jj contains Q_j, and s_jj contains the original action's
second variation plus J Q_jj. K_ab therefore retains the quadratic source
contact and the kinematic composite variation. With F=1, differentiating (T)
gives the actual Z_a,Z_ab of the common functional. Where Z is nonzero,

    partial_ab log Z = Z_ab/Z - Z_a Z_b/Z^2.

These reproduce the G/A/B/D blocks and contacts of the accepted matching
decomposition. No denominator nonzero domain is proved here. Local C2 source
jets on a compact source neighborhood give a finite polynomial Gaussian
dominator; no new moving regulator or inverse-body assumption is introduced.

## 6. Explicit geometric reflection convention and actual boundary pairing

An algebraic reflection convention is needed before asking for a state. Here
fix the geometric lift rho(t,r)=(1-t,r), reversing the TIME direction, and
R=gamma_0 in the actual Euclidean Hermitian Clifford convention. It has R^2=I,
R^dagger=R, det R=1, and R gamma_A R=s_A gamma_A with s_0=+1, s_i=-1.
The reflected link configuration sigma U is

    (sigma U)_(x,i)=R U_(rho x,i) R,                  i=1,2,3,
    (sigma U)_(x,0)=R U_(rho x-0,0)^dagger R.

On Nt=2 this sends EACH temporal anchor V_t to R V_t^dagger R; it does NOT
swap V0,V1 as an orientation-preserving one-step translation would. Both
interfaces remain. R normalizes Spin(4) by exchange of its chiral blocks;
conjugation/inversion preserve product Haar.

Define theta antilinearly, with theta(PQ)=theta(Q)theta(P), by

    theta psi_(x,a)=sum_b barpsi_(rho x,b) R_ba,
    theta barpsi_(x,a)=sum_b R_ab psi_(rho x,b),
    theta f(U)=conjugate(f(sigma U)).

These definitions give theta^2=1. The top coefficient is preserved under
conjugation: reversal of128 generators has even sign, site-block permutation
is even, the bar/psi block exchange is even, and detR factors are1.
Thus I(theta P)=conjugate(I(P)), including Haar. This is an explicitly defined
candidate Euclidean reflection, NOT a proved physical adjoint/state map.

Direct substitution in the four original coframe endpoint terms gives

    theta T_mu^A(x)=epsilon_mu r_A T_mu^A(rho x),
    epsilon_0=-1, epsilon_i=+1, r_A=-s_A.

Consequently theta Q_mu,nu(x)=epsilon_mu epsilon_nu Q_mu,nu(rho x).
Both world and internal reflections have determinant -1, so theta S4=S4
for real g1, at zero background/source. No reflection invariance of S2 is
assumed: a forward time plaquette is reflected into a backward one, whose
anchored link variables need not equal the original forward term. The
original discretization must pass its own action/source covariance test.
Retain its exact reflected coefficient by the substitution above; do not
replace S2 with (S2+theta S2)/2, change temporal boundary signs, or infer
theta exp(S)=exp(S) from internal Pin symmetry alone.

Let A_+ be the FULL even, gauge-invariant polynomial algebra generated by
slice0 fermions and spatial-link coordinates (modulo their original algebraic
relations); do not select a positive subspace after observing signs. Theta
maps it to slice1. The scalar/spatial Q source span is included. Temporal Q
and crossed action insertions require the boundary source correspondence
above and are not falsely inserted into this half-local algebra. Further
matter/gauge-constraint quotients require physical derivation.

For clarity the pairing can be written using one half-variable space.
Let kappa act on z by U_i -> R U_i R and
h_mu,A -> epsilon_mu r_A h_mu,A. It preserves dnu. On the64 generators let

    L=[0, I8 tensor R ; I8 tensor transpose(R), 0],
    S_AB=(-1)^(k(k-1)/2) det(L[A,B]),   |A|=|B|=k.

S is the full exterior reflection matrix, including degree0; it is invertible.
Top-degree sign is +1. The same endpoint calculation gives

    conjugate(f_0,A(F;kappa z))
                           =sum_B S_AB f_1,B(theta F;z).             (R)

Use (T), (R), and change z1=kappa w. At zero physical sources, whenever full
Z=Z(0;1,1) is nonzero, the ACTUAL normalized reflection pairing is

    H(F,G)=I[exp(S_g) theta(F) G]/Z
      =integral dnu(w) dnu(z) sum_(C,A)
          conjugate(f_0,C(F;w)) B_CA(w,z) f_0,A(G;z),
    B_CA(w,z)=[K(z,kappa w;0) S^(-1)]_(A,C) / Z.                 (RP)

No complex conjugate, transpose, exterior reversal or periodic interface is
discarded in this formula. A positive state needs Hermiticity and positivity
of THIS form on the image f_0(A_+), as well as the actual source/observable
interpretation. Positivity of an ambient kernel is sufficient but stronger;
a negative ambient vector outside that physical image is not a physical
counterexample. A negative witness must supply an actual F in the required
algebra (or an actual finite Gram span), not just an unphysical coefficient
vector. A complete finite matrix certificate can prove its declared entire
image; a few sampled positive minors cannot prove a larger state algebra.

This derives the boundary form to be tested. It proves neither its positivity,
its Hermiticity, nonzero Z, a thermal transfer interpretation of the periodic
fermionic functional, nor the additional premises for real-time reconstruction.

## 7. Completion criterion and limits of this milestone

The source-level construction is complete only with independently accepted
proofs of the following correspondences, all supplied explicitly above:

1. Both Nt2 cross-hopping blocks from all four coframe endpoint terms, with
   nonzero spatial Mtt retained, and original top orientation.
2. Complete all-subset bridge (B) with its lower-left minus and exterior sign;
   full signed S4 Hermite weight, not Gaussian-only S2 or a norm square.
3. Kernel (K) and identity (T) retaining EVERY temporal/spatial link and source
   through mixed-second order, plus all last-incidence elimination conditions.
4. Explicit edge/graded involution and pairing (RP), with crossing versus
   half-local sources separated and physical image/positivity limits stated.

This is a finite exact algebraic construction, not a scalar named to satisfy
positivity. It is specified by original coframe matrices, actual Hermite
coefficients, all minors and normalized moments. For a future implementation,
completion requires all such contributions or a proved equivalent aggregation,
not coverage of selected words. No partial link/site projection before its
last incident W/minor/insertion is valid.

Safe polynomial bounds make the criterion finite without promising tractability:
each W_x has h degree<=64 and link-coordinate degree<=128 (at most32 S2 factors
per coframe-degree64 truncation, each with a four-link plaquette). All16 weights
therefore have total h degree<=1024 and link degree<=2048. A bridge minor has
degree<=64 in h and temporal link coordinates. Thus before temporal Haar the
kernel integrand has total h degree<=1088 and total link degree<=2112;
integration cannot increase degrees. Canonical quaternion coordinates include
both independent chiral blocks; exact Haar moments of ALL their joint powers
are required. These are safe overestimates, not coefficient counts or resource
admission. Redundant coordinates may be quotiented only with a proved moment
identity; half-local physical observables are not truncated by these bounds.

Later full-normalization evidence may be an exact full value, a complete good-
prime nonzero certificate with proved invertible denominator, or a rigorous
signed remainder/analytic bound. A zero residue is inconclusive. Positivity or
a scoped obstruction must use (RP) and the physical source map separately;
positive Haar moments and fixed-auxiliary determinant norms are not that test.
No evaluation proposal is admitted by this manual construction.

Even a successful finiteN16 state/normalization certificate would not supply
continuum/large-volume/source-selected limits, physical matter matching or the
original B3 interval. At pureg2 the accepted all-volume result still gives
literal G=B=0 wherever normalized. The original normalized momentum/gradient
coefficient, stable chi range, tensor poles, matter/light reference and causal
transport remain open. Fixed B0+lambdaQ retains bodyB0; the separately centered
family loses its body at lambda1; neither is derived microscopic matching here.
Publication retains all L1 readiness/ordinary authorship and integration.
