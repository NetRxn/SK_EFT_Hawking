# N16 saturation test of the adopted full half-algebra reflection form

Project-original manual construction for independent mathematical and physics/
source review. No scientific evaluator, residue, partition value, native proof
or normalized parameter-point counterexample has been computed. The target is
the SAME action, periodic2^4 regulator, geometric theta and FULL even gauge-
invariant half-local polynomial algebra A_+ of the accepted temporal/physical-
image constructions. No action, observable quotient, boundary or source is
changed to obtain the result below. It is not yet an accepted scientific claim.

## 1. Target and saturation, including all action terms

Use the original closed action exp(g1 S4+g2 S2), original oriented128-generator
top extraction and normalized Haar on ALL64 Spin(4) links. Time0/1 halves
have64 generators each. Spatial coframes remain in one half; a temporal
coframe has one field in each half, retaining BOTH independent anchored links.
At reference physical sources J=j=0 an S2 monomial therefore has half degrees

    (4,0), (3,1), (1,3), (0,4).

There is no (2,2) monomial: S2 has two DISTINCT world-direction coframes and
at most one can be temporal. S4 has one coframe in every world direction,
so its half degrees are (7,1) or (1,7), never(6,2). Curvature links add no
Grassmann degree. These are full original-action support facts, not selected
word/amplitude assumptions. They require all four directions extended, as here.

Let

    P(F,G)=I[exp(g1 S4+g2 S2) theta(F) G],     F,G in A_+.

For ANY homogeneous degree62 F, theta(F)F leaves precisely(2,2) missing
from the two tops. Only one S2 could supply the remaining total degree4,
but its half degrees cannot match. Hence EXACTLY, for all finite g1,g2,

    P(F,F)=0.                                                   (zero)

For degree62 F and degree58 G, the missing half degrees in theta(F)G are
(6,2). Total remaining degree8 permits only g1 S4 and g2^2 S2^2/2. S4
cannot match(6,2). Two S2 factors can match only by BOTH having(3,1):
both are based in time0 and contain one temporal and one spatial coframe.
No omitted higher expansion term can contribute to this matrix entry.

## 2. Explicit gauge-invariant degree62 F

Choose x=(0,r) and y=(1,r). At each site use the original8-generator oriented
top Theta_z. In the time1 site y define q_y of degree6 by its Berezin dual
to the scalar meson B_y=sum_a barpsi_y,a psi_y,a:

    I_y[q_y barpsi_y,a psi_y,b]=delta_ab,
    I_y[q_y psi_y,a psi_y,b]=I_y[q_y barpsi_y,a barpsi_y,b]=0.

Equivalently q_y is the conjugate coefficient/Berezin dual of B_y in the
canonical exterior monomial basis. Its coefficients and orientation are
completely fixed by these equations, not fitted to an amplitude. The scalar
meson and top are invariant under the unitary determinant-one Dirac/dual
Spin(4) action, hence q_y is invariant too. Set

    Fhat=(product_(z in time1,z!=y) Theta_z) q_y,
    F=theta(Fhat).

Theta is the already specified antilinear anti-involution, with theta^2=1,
gauge equivariance and preserved top orientation. Thus F belongs to A_+,
has degree62, is independent of g1,g2, and theta(F)=Fhat. All other time1
sites are saturated; no link or gamma coordinate is physically projected.

The only S2^2 terms surviving against Fhat and a degree58 insertion in time0
have both temporal coframes end at y. Consequently both vertices are based
at the SINGLE site x. A temporal coframe at another spatial base would insert
a field into an already saturated time1 site. Define the COMPLETE crossing
part of S2_x as

    X_x=sum_(i=1..3) sum_(A,B) R^i_AB T_0^A(x) T_i^B(x),
    R^i_AB=epsilon(k,l,0,i)/4 *
            Tr[(H_x,kl-H_x,kl^dagger)[gamma_A,gamma_B]gamma5],

where k<l are the two spatial axes complementary to i, and H is the original
CLOSED plaquette. Summing all FOUR ordered world permutations gives exactly
this expression, including its commutator and quarter. It is neither a tagged
source nor a single internal-index slice. Only the saturation above removes
the other vertices in this specific full matrix entry.

## 3. Exact temporal Haar/Berezin contraction

Let V0=U_(x,0), V1=U_(y,0) remain independent Spin(4) variables. At x write

    D=V0^dagger-V1,       E=V1^dagger-V0,
    T_0^A(x)=1/4[barpsi_x gamma_A D psi_y
                              +barpsi_y E gamma_A psi_x].

Normalized Haar and independence give

    integral dV0 dV1 D E = -2 I4.

The two cross terms in T0^A T0^C survive q_y. Each acquires a minus when its
y fields are put in bar_y-before-psi_y order and the x fields are grouped.
The two same-type terms have two bars or two psis at y and vanish against
q_y. Therefore, using the Clifford anticommutator,

    integral dV0 dV1 I_y[q_y T0^A T0^C]
       =1/8 barpsi_x(gamma_A gamma_C+gamma_C gamma_A)psi_x
       =delta_AC/4 * B_x,       B_x=sum_a barpsi_x,a psi_x,a.     (time)

This is a first/second compact-link identity derived by unitarity and zero
first Haar moments, not a state positivity assumption or an evaluator run.
All other time1 Grassmann tops and unused link Haar factors are1.

Define the resulting COMPLETE degree6 time0 polynomial, without couplings,

    W6(U_spatial0,xi0)
       = integral_(all temporal links and time1 spatial links)
                 dHaar I_1[Fhat S2^2/2]
       =1/8 B_x sum_A L_A^2,
    L_A=sum_(i=1..3,B) R^i_AB T_i^B(x).                         (W6)

Saturation and (time) prove the equality for the FULL original S2, not only
a selected action sector. W6 is an even gauge-invariant half-local polynomial
of Grassmann degree6 and spatial-link degree at most10: two curvatures give
at most8 link coordinates and two spatial coframes give at most2. The temporal
link moments have already been retained exactly. Invariance follows either
from the original gauge-invariant partial integral or directly from the
internal-vector contraction in (W6).

## 4. Prove W6 is nonzero as a function on the actual compact links

This is an analytic polynomial nonvanishing check, NOT a restriction of the
physical Haar integral, a gauge fixing of a component, or numerical sampling.
Let z=x+e1. At one legitimate spatial-link configuration set

    U_(x,1)=-I4,    U_(z,1)=I4,
    U_(x,2)=U_(x+e2,2)=U_(x,3)=U_(x+e3,3)=I4,
    U_(x+e3,2)=I4,  U_(x+e2,3)=H*=gamma0 gamma1 gamma5,

and all unspecified spatial links to I4. These are DISTINCT directed anchors.
In the actual gamma convention H*=-gamma2 gamma3 lies in Spin(4), is unitary
and anti-Hermitian. Both SU(2) chiral blocks remain present. The four-link
closed plaquette H_x,23 equals H*. Meanwhile T2(x)=T3(x)=0, since neither
of their actual forward/backward anchors uses U_(x+e2,3).

Here epsilon(2,3,0,1)=+1. Clifford trace gives

    R^1_01=-4,   R^1_10=+4,    other R^1_AB=0,
    T1^B(x)=1/2[barpsi_z gamma_B psi_x-barpsi_x gamma_B psi_z],
    W6=2 B_x[(T1^0)^2+(T1^1)^2].                              (point)

In the source Weyl basis let L1/R1/R2 denote the indicated internal chiral
components. The coefficient of the NONZERO ordered Grassmann monomial

    (barpsi_x,R1 psi_x,R1)
       (barpsi_x,L1 psi_x,L1)(barpsi_z,R2 psi_z,R2)

has magnitude2 in (point). To check noncancellation explicitly, gamma0 has
LR12=-i and RL21=+i, while gamma1 has LR12=-1 and RL21=-1. Each cross term
in its T1 square contributes1/2 to the latter two mesons, so their sum is1.
The displayed R1 meson in B_x is the unique remaining contribution to that
monomial; an x-right hopping pair would instead require a z-left component.
Canonical reordering can change the displayed coefficient's sign, not make
it zero. Thus W6 is not the zero coefficient function on the physical link
groups. No single coordinate summand is substituted for W6 in the witness.

## 5. Actual degree58 G and an exactly nonzero full mixed entry

For the time0 canonical64-generator basis write W6=sum_(|I|=6) w_I(U) xi_I.
Let epsilon(I,Ic) be fixed by xi_I xi_Ic=epsilon(I,Ic)Theta_0, and define

    G=D_0(W6)=sum_I conjugate(w_I(U)) epsilon(I,Ic) xi_Ic.

This is the conjugate Berezin/Hodge dual, homogeneous degree58. The compact
gauge representation on64 generators is unitary with determinant1, preserving
the top; hence this dual intertwines that action. Thus G is gauge invariant,
half-local, polynomial of spatial-link degree<=10, independent of g1,g2, and
belongs to the SAME adopted A_+. Both F and G lie in its already complete
degree160 test carrier. No physical-algebra projection is made.

By the defining exterior-dual identity and the full saturation argument,

    P(F,G)=g2^2 a,
    a=integral dHaar_spatial0 sum_I |w_I(U)|^2 >0.               (mixed)

The inequality uses only normalized bare compact Haar and the ordinary
coefficient norm, NOT positivity of the gravity functional. W6 has a nonzero
coefficient at the legitimate configuration above; continuity and full support
of product Haar make the norm strictly positive. This constructs a true
noncancellation argument for this FULL mixed observable entry. It is not a
positive selected subtotal used to infer the partition sign.

## 6. Normalization-independent incompatibility on the adopted algebra

For any finite real g1 and real g2!=0, the actual original functional has

    P(F,F)=0,       P(F,G)=g2^2 a !=0,

on two explicit fixed gauge-invariant observables in the required image.
No nonzero complex scalar lambda can make lambda P a Hermitian PSD form on
A_+: any positive sesquilinear form satisfies Cauchy-Schwarz, and a zero norm
must have zero overlap with EVERY vector. Multiplication by lambda cannot
remove this nonzero overlap. Equivalently, if the two-by-two block were
Hermitian, its determinant would be -|lambda*g2^2*a|^2<0, regardless of the
unknown G diagonal; if it is not Hermitian it already fails the target.

Consequently the TWO requirements

    full Z(g1,g2)!=0  AND  P/Z positive on the adopted A_+

cannot hold together for g2!=0. If Z=0 the normalized expectation is undefined;
if Z!=0 the same exact full functional fails this reflection-positivity test.
This is a nonvacuous algebraic incompatibility certificate: its raw mixed
moment is actually nonzero. It is NOT an evaluation of c0 or a demonstration
of a particular normalized coupling point. It must not be recorded as the
earlier certificate contract's computed normalized negative quadratic value
on a certified nonempty parameter domain; no such data are supplied. It instead
rules out ANY scalar normalization making this specified form positive.

The argument does NOT infer failure from theta(S2) noninvariance or incomplete
positive minors. It derives exact complete moments and actual observable/image
correspondence. G is a witness constructed from the original theory, not a new
source, fitted density matrix, discarded negative channel or altered action.

## 7. Scientific boundary and required independent review

The conclusion is about the FIXED periodic all-extended N16 action and the
FIXED candidate geometric theta on the FULL adopted even gauge-invariant
half-local Grassmann polynomial algebra, at reference physical sources, for
g2!=0. It supplies no conclusion at g2=0. It does not prove a metric-only or
dressed-scalar subalgebra fails, or identify these high composites with a
particular microscopic matter operator. A physical constraint quotient,
different adjoint/state/boundary/action, or a source-selected/large-volume
construction requires its own derived correspondence; it cannot be selected
afterward merely to discard this witness.

No assertion follows about all Lorentzian models, Vergeles' simplicial
Minkowski construction, a continuum limit, false original B3/luminality/gain
claims, tensor dynamics or physical transport. Full partition nonvanishing
and the N4 tensor remain OPEN. This may provide a construction breakdown of
the adopted full-algebra positive-reflection route, not publication closure,
operator deferral or reduced original requirements. Publication retains all
ordinary L1 readiness/source/manuscript/integration responsibility.

Independent math review must verify complete degree saturation, orientation/
dual signs, temporal contractions, all-source reduction and strict nonzero
polynomial/norm proof. Independent physics/source review must check the actual
action, both interfaces, ALL internal channels, physical-image membership,
and the distinction between this raw incompatibility and a certified normalized
parameter-point witness. No source evaluation, CAS/matrix test, contraction,
compile/control job, Lean/slot/controller or infrastructure action is admitted.
