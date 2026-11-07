# Original graded boundary relation, off-shell identities and C2 source audit

Manual mathematical candidate for independent RESULT review. Derived under
ROOT's explicit manual L1-L4 commission and the prospectively dual-approved
R2 brief6722bb6ea2e55e42f521f6ff137a1c358dcb9c7425b03913e66316fb52961a62.
No scientific evaluator, CAS/matrix/Haar/exterior script, test/build, Lean,
slot or controller job was run. This constructs formal original-action
relations and exact integration identities, NOT Q1-Q4 physical quantization,
a positive state, a physical adjoint, or W1 completion.

## 1. Exact action, fields and derivative convention

Reuse original transfer975ad00d, boundary452ed859, temporal82197710 and the
carrying ADW_EXACT_AUXILIARY_IDENTITY.md equations1-3. World axes are relabeled
in their inherited order as0,1,2,3, epsilon0123=+1. At a base x, write U+=U_x,mu,
U-=U_(x-mu),mu and x+=x+mu,x-=x-mu. The original coframe is

 T_x,mu^A=1/4[barpsi_x gamma_A U+† psi_x+
             -barpsi_x+ U+ gamma_A psi_x
             -barpsi_x gamma_A U- psi_x-
             +barpsi_x- U-† gamma_A psi_x].                 (1)

All bars and psis are independent odd generators in the accepted ordering.
Even coframes commute. For fixed prescribed world-frame A_x(j), put
Y_x,mu^A=sum_nu A_x(j)_mu,nu T_x,nu^A. Source coordinates are (J,j), with
J_mu,nu for mu<=nu occurring ONCE. The complete local base polynomial is

 s_x=g1 sum_(A0..A3) epsilon_(A0 A1 A2 A3) product_(rho=0..3)Y_x,rho^A_rho
   +g2/4 sum_(k,l,mu,nu,C,D)epsilon^(k l mu nu) F_x,kl^CD Y_x,mu^C Y_x,nu^D
   +sum_(mu<=nu)J_x,mu,nu sum_A Y_x,mu^A Y_x,nu^A,            (2)
 F_x,kl^CD=Tr(H_x,kl gamma_C gamma_D gamma5).

Use the ACCEPTED CLOSED order. With
 A=U_x,k, B=U_(x+k),l, C=U_(x+l),k, D=U_x,l,
 H_x,kl=D† C† B A.                                          (3)
This is the already accepted closed benchmark, not its literal-product
comparator ABC†D†. All ordered world/internal terms and the action quarter
remain in(2); no selected curvature plane or Hermitian part is substituted.
The three-slice density s_t is the sum of(2) over the eight spatial bases
in the middle slice b. Its arguments are
 (X_a,X_b,X_c;v_a,v_b), X=(spatial links,64 odd generators).
Formal forward/backward time fields c/a stay distinct until Nt2 sewing.

For a compact link, D_(ell,tau) acts by U_ell -> exp(t tau)U_ell, with tau
in the actual represented spin(4) Lie algebra, tau†=-tau. Thus DU=tau U,
DU†=-U†tau. This is a divergence-free invariant vector field; with this
pullback convention [D_tau,D_sigma]=-D_[tau,sigma]. Odd derivatives are
LEFT Grassmann coefficient derivatives. For every homogeneous derivation V
of parity |V|, V(fg)=(Vf)g+(-1)^(|V||f|)f(Vg). Covector components below
mean their evaluations on these derivations, so no ambiguous right/left
momentum reordering or physical reality convention is implicit.

## 2. Complete coframe/action component forces

Define the even derivative of(2) with respect to its commuting Y coordinates:

 H_(rho E)=g1 sum_(A0..A3)epsilon_(A0..A3) delta_(A_rho,E)
                                      product_(sigma!=rho)Y_sigma^A_sigma
  +g2/4 sum_(k,l,mu,nu,C,D)epsilon^(k l mu nu) F_kl^CD
       [delta_(mu,rho)delta_(C,E)Y_nu^D
                      +delta_(nu,rho)delta_(D,E)Y_mu^C]
  +sum_(mu<=nu)J_mu,nu[delta_(mu,rho)Y_nu^E+delta_(nu,rho)Y_mu^E],
 b_(nu E)=sum_rho A(j)_rho,nu H_(rho E).                      (4)

In particular a diagonal J contributes2J_rho,rho Y_rho^E; an off-diagonal
source occurs only once. For ANY homogeneous field/link derivation V,

 V s_t=sum_(r,nu,E)b_(r,nu,E) V T_(b,r),nu^E
   +g2/4 sum_(r,k,l,mu,nu,C,D)epsilon^(k l mu nu)
       Tr[(V H_(b,r),kl)gamma_C gamma_D gamma5]Y_mu^C Y_nu^D. (5)

This is an explicit full-action contraction, not a derivative of an
unspecified S. H and b include every determinant, EHC and metric term.
The curvature term vanishes only for fermionic derivatives, not link ones.

Writing delta_z,x for site equality and a component index i, direct LEFT
Grassmann differentiation of(1) gives

 partial_barpsi_(z,i) T_x,mu^A =1/4{
  delta_z,x[(gamma_A U+†psi_x+)_i-(gamma_A U-psi_x-)_i]
  -delta_z,x+ (U+gamma_A psi_x)_i
  +delta_z,x- (U-†gamma_A psi_x)_i},
 partial_psi_(z,i) T_x,mu^A =1/4{
  -delta_z,x+ (barpsi_x gamma_A U+†)_i
  +delta_z,x (barpsi_x+ U+gamma_A)_i
  +delta_z,x- (barpsi_x gamma_A U-)_i
  -delta_z,x (barpsi_x- U-†gamma_A)_i}.                        (6)

The minus sign when differentiating an unbarred variable comes from passing
its LEFT derivative through the preceding bar. Coincident spatial neighbors
are added, not treated as distinct generators or canceled prematurely.

For the temporal coframe at (b,r), specifically,

 T_b,0^A=1/4[barpsi_b gamma_A v_b†psi_c-barpsi_c v_b gamma_A psi_b
             -barpsi_b gamma_A v_a psi_a+barpsi_a v_a†gamma_A psi_b]. (7)

The old/new odd components of f=ds_t are therefore exactly

 f_barpsi_a,i=1/4 sum_A b_(r,0,A)(v_a†gamma_A psi_b)_i,
 f_psi_a,i=1/4 sum_A b_(r,0,A)(barpsi_b gamma_A v_a)_i,
 f_barpsi_c,i=-1/4 sum_A b_(r,0,A)(v_b gamma_A psi_b)_i,
 f_psi_c,i=-1/4 sum_A b_(r,0,A)(barpsi_b gamma_A v_b†)_i.       (8)

For the shared b fields, the temporal contributions are

 f_barpsi_b,i|time=1/4 sum_A b_(r,0,A)
                      [gamma_A v_b†psi_c-gamma_A v_a psi_a]_i,
 f_psi_b,i|time=1/4 sum_A b_(r,0,A)
                      [barpsi_c v_b gamma_A-barpsi_a v_a†gamma_A]_i.

ADD to these sum_(s,nu=1..3,A)b_(s,nu,A) times the corresponding four
spatial-neighbor terms in(6), with z=(b,r),x=(b,s). This finite displayed
sum specifies every shared component, including all eight spatial bases.
No temporal or neighboring spatial term is omitted.

For a link occurrence, the forward and backward coframe contributions are

 D_(U+,tau) T_x,mu^A=-1/4[barpsi_x gamma_A U+†tau psi_x+
                                   +barpsi_x+ tau U+gamma_A psi_x],
 D_(U-,tau) T_x,mu^A=-1/4[barpsi_x gamma_A tau U-psi_x-
                                   +barpsi_x- U-†tau gamma_A psi_x]. (9)

For a fixed physical link, ADD every occurrence of(9). Its full curvature
variation in(5) uses

 V H=(V D†)C†BA+D†(V C†)BA+D†C†(V B)A+D†C†B(V A),             (10)

with each factor varied by DU/DU† above. Repeated physical occurrences are
all retained. Equations4-6,9-10 specify every component and its ordering.
In particular f_(v_a,tau) has only the BACKWARD coframe term in(9), summed
with b_(r,0,A); f_(v_b,tau) has its FORWARD term PLUS all(10) contributions.
New-slice spatial-link forces have only(10), while shared-slice spatial-link
forces have both(9) and(10). Old-slice spatial links occur in neither the
middle-base coframes nor its forward closed plaquettes, hence

                 f_(u_a^spatial,tau)=0.                    (11)

This holds for every prescribed source value: world-frame mixing changes
coframe components, not link endpoints. No old spatial link is removed from
the original sewn Haar integral by this observation.

## 3. Typed formal relation and its explicit parametrization

Let B have boundary variables (X_a,X_b,v_a). A(B) is the algebra of actual
compact-link polynomial functions tensored with the ordered exterior algebra.
The matching base D has variables(X_a,X_b,X_c,v_a,v_b), maps
 i_in=(X_a,X_b,v_a), i_out=(X_b,X_c,v_b), and their algebra pullbacks.
Endpoint covectors p=(p_a,p_b,p_va), P=(P_b,P_c,P_vb) are INDEPENDENT
covector data over A(D). Compact-link directions use the invariant tangent
frame and its dual; odd components use evaluation on the left derivatives.
No Hilbert metric is used to identify tangent and cotangent objects.

For every allowed homogeneous variation V on D impose

               P(d i_out V)-p(d i_in V)=V(s_t).             (12)

Taking the independent a,b,c,va,vb directions gives COMPLETE equations

 p_a=-f_a, p_va=-f_va, P_c=f_c, P_vb=f_vb, P_b-p_b=f_b.       (13)

Every f here is(5)-(10), not an unspecified potential. The free covector
kappa=p_b parametrizes the relation:

 (p_a,p_b,p_va;P_b,P_c,P_vb)
       =(-f_a,kappa,-f_va;kappa+f_b,f_c,f_vb).                (14)

Algebraically, introduce formal momenta with the parities of their coordinates
in the graded symmetric endpoint-momentum algebra over A(D). The ideal(13)
is monic in the eliminated momentum components; substitution(14) identifies
its quotient with A(D)[kappa] (graded symmetric meaning exterior for odd
kappa). This establishes the parametrization without a Legendre inverse,
body-point rank assertion, radicalization or a smooth phase-image assumption.
The displayed relation equations have independent momentum columns. This
statement is about the AMBIENT GRAPH equations, not independence of all
constraints of either projected phase image.

Gauge covariance is intrinsic: the accepted endpoint gauge action preserves
s_t, maps D to itself, and its cotangent pullback preserves evaluation(12).
Equivalently f(V) transforms by the chain rule and link directions transform
with the appropriate endpoint adjoint action. The already proved Pi/center
and source identities are unchanged; covariance does not supply a norm.

Let lambda=p(dq) be the canonical evaluation one-form and omega=-d lambda.
On the relation graph(14), (lambda_out-lambda_in)=d s_t, so d^2 s_t=0 gives

            j_out^*omega_out=j_in^*omega_in.                (15)

This is an equality of formal graded pulled-back forms. In invariant link
frames d includes their noncommuting brackets; treating all link derivatives
as commuting coordinate partials would be wrong. Equation15 is not an
invertible evolution map or a theorem about a reduced physical Hilbert space.

## 4. Two-move matching and the internal-connector cut

Use s0(Xa,Xb,Xc;va,vb) and s1(Xb,Xc,Xd;vb,vc). Matching intermediate
covectors on z_bc gives, writing f^i for each action differential,

 kappa+f_b^0=-f_b^1,   kappa'=f_c^0,
                         f_vb^0+f_vb^1=0.                 (16)

Thus external momenta are

 p_a=-f_a^0, p_b=-(f_b^0+f_b^1), p_va=-f_va^0,
 P_c=f_c^0+f_c^1, P_d=f_d^1, P_vc=f_vc^1.                  (17)

Only the internal connector vb has the additional classical stationarity
relation in(16). Shared Xb and Xc are also external pair-boundary variables;
one must NOT impose f_b^0+f_b^1=0 or f_c^0+f_c^1=0 by dropping their external
momenta. Equations16-17 are the boundary variation of s0+s1 with that internal
connector relation retained. No solving for vb, stationary-phase integral,
new time extent or effective log action is used.

In contrast the ACTUAL accepted two-step quantum kernel is

 k_red=integral Haar(vb) exp[s1(Xb,Xc,Xd;vb,vc)+s0(Xa,Xb,Xc;va,vb)]. (18)

Its vb integral is OFF SHELL. Classical stationarity in(16) is not inserted
into(18). Periodic sewing Xc=Xa,Xd=Xb,vc=va integrates the original56 boundary
links plus8 intermediate connectors and128 Grassmann generators, recovering
the same Nt2 functional and both interfaces. This exact trace identity is
reused, not replaced by quantization of the stationary relation.

## 5. Exact pre/post ideals and distinct regularity results

The parametrization(14) gives actual algebra maps from the input and output
formal phase algebras into C=A(D)[kappa]:

 phi_-: (Xa,Xb,va;pa,pb,pva) -> (Xa,Xb,va;-fa,kappa,-fva),
 phi_+: (Xb,Xc,vb;Pb,Pc,Pvb) -> (Xb,Xc,vb;kappa+fb,fc,fvb).

Define I_-=ker phi_-, I_+=ker phi_+. These are exact pre/post relation ideals,
not an assumed list of independent smooth constraints. They retain nilpotents.
A complete eliminated generating set, its phase-image gradient ranks and
any smooth quotient are NOT established by merely defining these kernels.
One explicit preconstraint subfamily follows from(11): p_(u_a spatial)=0;
its separate momentum gradients are independent in the invariant frame.
It is a boundary-support fact, not an extra physical projection.

The full relation graph has the monic parametrization above. Separately,
the unresolved Legendre sector would require recovering (Xc,vb) from the
old forces at fixed input/kappa. The fermionic force coefficients have
Grassmann degrees3 or7; link force coefficients have degrees4 or8. Thus every
entry of the mixed derivative block of (fa,fva) with respect to the future
variables has positive Grassmann degree (at least2 after two odd derivatives),
or is zero. Its ordinary body is ZERO. No nonempty square block consisting
only of these entries is invertible over the same Grassmann algebra: an
inverse would descend to an inverse of zero under the body homomorphism.
The identity blocks for copied boundary variables/free kappa do not repair
this unresolved sector. This is a finite-move regular-Legendre-inversion
obstruction, not the earlier continuum limit argument.

It proves neither that the full projected constraint gradients are dependent
nor that a nonregular reduction/quantization is impossible. Nor is a complete
second-class basis or invertible bracket minor supplied. Such a construction
must use actual pre/post generators and distinguish canonical Lie-frame terms
and nilpotent coefficients. Equation15 alone gives no locally constant rank.
These are the exact missing hypotheses for applying an ordinary regular
constraint theorem, rather than a physical degree count or an all-routes no-go.

## 6. Exact quantum identities on a stated test algebra

Use finite exterior polynomials whose compact-link coefficient functions are
C2 (or the original polynomial coefficients); use C1 for single derivative
claims. This is an analytic/formal TEST domain, not a chosen physical Hilbert
completion. Compactness bounds all continuous coefficients/needed derivatives;
finite Berezin extraction justifies coefficientwise operations. The old I_a
removes64 odd generators, so it commutes with external odd differentiation
without an extra sign. Coefficient-dependent vector fields require their
actual divergence terms; they are not silently included in the primitive
zero-divergence formulas below. Prescribed source dependence is coefficientwise C2,
locally bounded on a compact source neighborhood. Haar/Berezin measures do
not vary. Let f_V=V s_t and define the concrete source vertex

             V_f(phi)=I_a integral Haar_a exp(s_t) f phi.

For a primitive, source-independent integrated old-field/link derivation D,
Haar invariance or the fact
that a Berezin top coefficient of an old odd derivative is zero gives

      L_t D phi=-V_(f_D)(phi),                              (19)
      I_a integral Haar_a exp(s_t)(D phi+f_D phi)=0.

The derivative of phi is essential. For a retained SHARED derivation D onXb,

             D_out L_t phi=L_t D_in phi+V_(f_D)(phi),         (20)

and for a NEW derivation on(Xc,vb),

                       D_out L_t phi=V_(f_D)(phi).           (21)

These include odd derivatives with the same ordering convention, since
exp(s_t) is even and I_a has even parity. Old spatial-link directions have
f_D=0, so(19) gives the actual exact identity L_t D_oldspatial=0, in accord
with their explicit preconstraint. For the internal vb in(18), its old-style
Haar identity is integral exp(s0+s1) D_vb(s0+s1)=0 with external test data
held fixed, NOT pointwise D_vb(s0+s1)=0.

For any homogeneous field derivation D, (D-M_(f_D))exp(s_t)=0. On the full
matching test algebra define C_D=D+M_(f_D), with M multiplication by the
actual force. The Leibniz rule and
 D f_E-(-1)^(|D||E|)E f_D=f_[D,E]
prove the exact differential identity

                       [C_D,C_E]_gr=C_[D,E].                (22)

The minus-sign weight annihilators likewise close. This is a concrete graded
algebra of kernel/insertion differential identities. It is NOT proof that
they are physical first-class self-adjoint constraints or that their action
integrates to the finite-dimensional unitary group required by RAQ.

Even products show why classical elimination cannot be quantized by naming
momenta. For two such primitive integrated homogeneous derivations D,E, applying(19) twice
with the ordered Leibniz rule gives

 L_t D E phi=V_( f_D f_E+(-1)^(|D||E|)E f_D )(phi).           (23)

In particular L_t D^2 phi=V_(f_D^2+D f_D)(phi) for an even D. The field-
derivative contact D f_D is absent from naive substitution of the classical
relation p_D=-f_D into p_D^2. Equation23 is an exact contact formula for the
original kernel, not an evaluated nonzero contact or a physical product choice.
It prevents promoting the entire classical ideal to quantum null relations
without an ordering/domain/kernel proof. No i,hbar,CAR or spectral exponential
has been inserted. Neither positivity nor its failure for K_g follows.

## 7. Explicit C2 contacts and variation of the ideals

Write Y_alpha=A_alpha T and Y_alphabeta=A_alphabeta T for the prescribed
world-source jets, where alpha,beta can include literal J directions. Compact
links/F are held source-independent. The determinant first derivative replaces
one of its four slots by Y_alpha; its mixed derivative is the sum of four
single-slot Y_alphabeta replacements PLUS all ordered distinct-slot
Y_alpha/Y_beta replacements. The EHC first derivative in(2) replaces its
pair product by
 Y_mu,alpha^C Y_nu^D+Y_mu^C Y_nu,alpha^D;
its mixed derivative replaces it by
 Y_mu,alphabeta^C Y_nu^D+Y_mu,alpha^C Y_nu,beta^D
       +Y_mu,beta^C Y_nu,alpha^D+Y_mu^C Y_nu,alphabeta^D.       (24)
Keep the original g1,g2/4 and all epsilon/F contractions.
For Q_mu,nu=sum_A Y_mu^A Y_nu^A the same first/pair mixed rule applies. The
metric source contributes exactly
 J_alpha Q+J Q_alpha,
 J_alphabeta Q+J_alpha Q_beta+J_beta Q_alpha+J Q_alphabeta.     (25)
For the independent literal J coordinates on straight source directions,
J_alphabeta=0. Equations24-25, including determinant slots, specify s_alpha
and s_alphabeta completely. They retain off-diagonal sources once and both
action/composite path-acceleration terms. No high-jet dictionary is assumed.

Use the even ring R=C[epsilon,delta]/(epsilon^2,delta^2). The exact C2 germ is

 s_R=s+epsilon*s_alpha+delta*s_beta+epsilon*delta*s_alphabeta,
 w_R=w[1+epsilon*s_alpha+delta*s_beta
                   +epsilon*delta*(s_alpha s_beta+s_alphabeta)]. (26)

Equal directions include the pure second jet. The fixed primitive field
derivations commute with these even source derivatives. Consequently f_D,alpha=D s_alpha and
f_D,alphabeta=D s_alphabeta. Equations12-23 extend coefficientwise toR.
For example the differentiated vertex in(19)-(21) is

 (V_fD)_alpha=V_(s_alpha f_D+f_D,alpha),
 (V_fD)_alphabeta=V_((s_alpha s_beta+s_alphabeta)f_D
        +s_alpha f_D,beta+s_beta f_D,alpha+f_D,alphabeta).     (27)

If a test insertion itself depends on sources, its first/second product
terms must also be added. The fixed test domain above does not vary.
For K=L1 L0, its mixed source derivative is exactly
 L1_alphabeta L0+L1_alpha L0_beta+L1_beta L0_alpha+L1 L0_alphabeta,
with each L_t,alphabeta carrying s_alpha s_beta+s_alphabeta.
The accepted common finite-rank support/compact bounds justify the source
trace derivatives. No temporal crossing or one of the two interfaces is lost.

The FULL relation graph has a flat source-jet presentation:
its monic elimination(13) overR still gives (A(D) tensor R)[kappa].
This is scalar extension of a complex vector space, hence free as anRmodule.
It does NOT establish flatness or source stability of the pre/post projected
phase quotients. The latter can be tested exactly, not assumed:
write phi_R=phi_0+epsilon*phi_alpha+delta*phi_beta+epsilon*delta*phi_alphabeta
for either of the parametrized phase pullbacks. A zero-source relation p0
lifts to p_R=p0+epsilon*p_alpha+delta*p_beta+epsilon*delta*p_alphabeta iff

 phi_0(p0)=0,
 phi_0(p_alpha)+phi_alpha(p0)=0,
 phi_0(p_beta)+phi_beta(p0)=0,
 phi_0(p_alphabeta)+phi_alpha(p_beta)+phi_beta(p_alpha)
                                      +phi_alphabeta(p0)=0. (28)

Here source derivatives on momenta are obtained by differentiating the
explicit substitutions(14); coefficients/configuration variables/kappa are
held fixed unless included in p_R. Thus the first actual obstruction is the
class of phi_alpha(p0) modulo im(phi_0); mixed lifting has the displayed
residual after the first lifts are chosen. No vanishing of these classes for
the COMPLETE pre/post ideals is claimed. The explicit old-spatial momentum
relations DO lift unchanged, by(11). Formula28 is the exact missing
source-quotient compatibility obligation, not an arbitrary new flatness axiom.

## 8. What is established and the remaining physical gate

Established manually: complete coframe/full-action forces and link orders;
typed formal boundary graph with explicit free shared covector; its algebraic
pre/post kernels, finite-move inverse obstruction and formal two-form identity;
two-move connector stationarity versus the actual off-shell sewing integral;
exact test-domain quantum derivative/graded-closure/contact identities; and
full prescribed C2 source/ideal-lifting conditions. Implicit kernels are not
advertised as a complete smooth constraint classification or physical quotient.

The concrete next quantum question is now narrower: do any ACTUAL pre/post
relations admit boundary-only operators on a source-compatible admissible
algebra with a derived adjoint, whose ordered kernel identities include(23)
and whose source lift satisfies(28)? This is Q1 preparation, NOT an assignment
to choose such a product/domain. The inspected Höhn/RAQ hypotheses are not
thereby met: no positive physical kinematic representation, self-adjoint
constraint family/gauge fixing/rigging form or original norm-preserving
kernel transport has been constructed. Q1-Q4 need new concrete scope before
work; no extra physical premise or favorable convention is introduced here.

Original F/G and finite trace/source results remain unchanged. No positive
state, nonzero fullZ/c0, N4 tensor, B3 normalization/[0.1,10], physical tensor/
matter/light dynamics or causal transport is certified. No all-routes no-go
or controlled-scaling conclusion follows; that alternative stays OPEN.
ROOT retains all ordinary/canonical L1 readiness and integration/operator work.
The result needs independent mathematics/critical-path and original-source
reviews, then ROOT personal intake. Future scientific execution still needs
its separately exact reviewed proposal and fresh controller canary/resource
admission; manual identities are not a canary, build or runtime certificate.
