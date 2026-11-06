# Original phase current, kinetic charge and metric/source normalization covariance

MANUAL candidate for independent actual-result review. Constructed under exact prospective R2 ed19be08841fff39e946b1dfc20e57217e926f40c15edbb162bf6bf65b4a73db, after BOTH independent APPROVE reports were fully read and freshly checked. R1 and both REVISE reports are preserved. This constructs one original symmetry/kinetic/kernel/source correspondence and its normalization covariance. It does not construct a physical metric, physical adjoint/domain, unitary or causal evolution, matter calibration or B3. ROOT retains ordinary L1 and publication delivery.

## 1. Source constraints and actual object

Diakonov1109.0091v1 I, II(1)-(3), IV(11), V(12),(23)-(28), VI defines the independent spinors/connection and composite coframe. In particular SAME-spinor S_Dirac=4 S_cosm after composite substitution, whereas the finite action has no quadratic fermion propagator. An extra unit canonical kinetic term cannot be inferred or added. Volovik2312.09435v2 III(18)-(22) defines physical tetrad and quartet operator expectations and distinguishes tetradic/full metric and fermionic/bosonic matter references; exterior multiplication is not thereby a physical operator product. Vergeles2506.00036v2 II(2.16)-(2.26), III(3.9), IV(4.1)-(4.10), VI(6.1) distinguishes formal dagger from physical scalar-product Hermiticity and assumes domain/ONB/spectral data for its simplicial Minkowski construction. Its composite extension remains, with gauge-volume/domain issues. These are not transferred to the compact Euclidean hypercubic model by notation.

Primary source bodies were read in the held versions. Sources: https://arxiv.org/abs/1109.0091v1 ; https://arxiv.org/html/2312.09435v2 ; https://arxiv.org/html/2506.00036v2 . PDF equation numbering governs. Exact held PDF pins:
Diakonov2011.pdf 270355bytes SHA132d63150a678ef17bfbbc04978a8cab9c9801f03556982a6aa67c11d3fbc4da;
Volovik2024.pdf 140946bytes SHAfae06f3bd7189f52a24fce5b612a30d2fc23ca1f2a9db43100e535d954791d9d;
Vergeles2025.pdf 1756894bytes SHAdaa334f1ad59ace58aba5afe68ec5d4909e717e626ba6fa7c0d7237c8df43eac.

Keep the exact accepted periodic Q4/Nt2 regulator:16 sites,128 independent odd coordinates,64 independent anchored Spin(4) links, original orientation and quarter coframe, closed plaquette Ddag Cdag B A, exp(+S), all determinant/EHC terms and BOTH interfaces. Use the full literal J and prescribed C2 world-frame A_x(j), not a selected spatial channel. Write

 T_xmuA=1/4[barpsi_x gamma_A U_xmu^dag psi_y
           -barpsi_y U_xmu gamma_A psi_x
           -barpsi_x gamma_A U_zmu psi_z
           +barpsi_z U_zmu^dag gamma_A psi_x],
 y=x+mu, z=x-mu,
 Y_xmuA=sum_nu A_x(j)_mu,nu T_xnuA,
 Q_xmu,nu=sum_A Y_xmuA Y_xnuA,
 S(g,J,j)=g1 S4(Y)+g2 S2(Y,U)+sum_(x,mu<=nu)J_xmu,nu Q_xmu,nu.       (1)

All bars and psis are independent. Source coordinates mu<=nu occur ONCE. A(j), all links and Haar measure are held independent of the field rescaling and phase variation below. Source derivatives retain A_alpha and A_alphabeta, all action terms and time-mixed carriers. Accepted nonzero Z, temporal response, actual coherent/Bopp/contact maps and conditional process remain inputs, not conditional hypotheses restored by old documents.

## 2. Exact full-functional and source normalization covariance

Let lambda>0, g_lambda=(lambda^8 g1,lambda^4 g2), J_lambda=lambda^4 J, and j_lambda=j. Let

 (r_lambda f)(q,U)=f(lambda^-1 q,U), q=(barpsi,psi).

This is a map from tests in primed/scaled coordinates to functions of unprimed coordinates. Direct homogeneity gives

 T(lambda^-1 q)=lambda^-2 T(q), Y likewise,
 Q(lambda^-1 q)=lambda^-4 Q(q),
 S(g_lambda,J_lambda,j;lambda^-1 q,U)=S(g,J,j;q,U).                 (2)

For each odd coordinate q'=lambda^-1 q, d q'=lambda d q: integrating q'=lambda^-1 q gives1, fixing the inverse Berezin Jacobian. All128 factors have positive real lambda, so orientation is unchanged. Compact links/independent anchors are not rescaled. With unnormalized ell and normalized omega=ell/Z, this proves for ALL original polynomial tests and permitted C2 link/source coefficients

 ell_(g_lambda,J_lambda,j)(f)=lambda^128 ell_(g,J,j)(r_lambda f),
 Z(g_lambda,lambda^4 J,j)=lambda^128 Z(g,J,j),
 omega_(g_lambda,lambda^4 J,j)(f)=omega_(g,J,j)(r_lambda f).         (3)

At a fixed literal J' on the scaled model the equivalent right argument is J=lambda^-4 J', not J'. These exact finite coefficient identities hold before dividing; normalized statements use the accepted nonzero-Z neighborhood. Where W=log Z is defined locally on the real positive neighborhood,

 W(g_lambda,J',j)=128 log lambda+W(g,lambda^-4 J',j).              (4)

Thus a fixed degree-k test has normalized expectation lambda^-k times the original at corresponding sources. A covariantly transported test f_lambda(q')=f(lambda q') has invariant expectation. For literal J derivatives, each derivative at corresponding sources contributes lambda^-4; prescribed frame derivatives have no such factor. In particular literal connected Q/Q response scales lambda^-8, including its quotient subtraction; a mixed literal J/frame derivative scales lambda^-4. Frame-only response is transported without that external source factor, with its full action and composite contacts. These are chain-rule statements for the WHOLE C2 family, not selected Taylor coefficients. Source-dependent tests transform with their first/mixed-second derivatives as in the ordinary product rule.

At zero source the already accepted temporal test f of degree12 obeys omega_lambda(f)=lambda^-12 omega(f), and its literal temporal Q response is lambda^-16 times the accepted nonzero response. This agrees with, and does not re-evaluate, the accepted certificate. The coframe and quartet means scale lambda^-2 and lambda^-4 respectively; no nonzero physical metric mean is inferred. g1/g2^2 is invariant where g2!=0, but (3) relates observables and source units as well as couplings; it does not alone declare physically calibrated models along the ray equivalent.

## 3. Original one-step kernel, cotangent graph and continuum kinetic form

For the accepted pair boundary B=(Xa,Xb,va), with64 odd coordinates on each slice, the actual reduced step is

 (L_s F)(Xb,Xc,vb)=int dHaar_a I_a exp(s_t(Xa,Xb,Xc;va,vb;s)) F(Xa,Xb,va).

I_a removes exactly64 old odd coordinates. Define R_lambda,in/out by the same lambda^-1 scaling on BOTH slices of the respective boundary; compact links are unchanged. Evaluating the scaled output at lambda^-1 q_b,c and substituting q'_a=lambda^-1 q_a gives

 R_lambda,out L_(g_lambda,J_lambda,j)
       =lambda^64 L_(g,J,j) R_lambda,in.                          (5)

The copied shared variables are scaled on both sides; no extra integral over them has been introduced. On a two-step product the intermediate pullbacks cancel, giving

 R_lambda K_lambda=lambda^128 K R_lambda.                         (6)

The original parity/supertrace, accepted gauge projectors and global-center identities commute with this field-degree scaling. Periodic sewing therefore reproduces (3), not a changed fermion boundary. All source derivative identities of (5)-(6) follow at the SAME corresponding sources, with the literal lambda^-4 factors above and all four mixed two-step placements. This is actual L_t intertwining, not the previously constructed conditional channel identified as causal transfer.

For an odd coordinate q, R M_q R^-1=lambda^-1 M_q and R partial_q^L R^-1=lambda partial_q^L. Thus independent cotangent momenta satisfy p'_q=lambda p_q, while unchanged link-coordinate momenta satisfy p'_U=p_U. This is contragredient cotangent transport. It is NOT the scaling of the independent barred coordinate, which is lambda^-1 barpsi. From (2), explicit odd forces f_q=partial_q^L s scale lambda, and link forces scale1 at transformed fields/couplings/sources. The accepted graph

 p_a=-f_a, p_va=-f_va, P_c=f_c, P_vb=f_vb, P_b-p_b=f_b

is preserved by this transformation, including its free shared kappa with odd components scaled lambda and link components unchanged. The pullback maps defining the exact pre/post kernels commute with it; their ideals are transported without radicalization or a regular-Legendre claim. The same algebra isomorphism transports the C2 lift equations with the source arguments in (3). It neither solves an unresolved projected-ideal lifting class nor makes a singular constraint system regular.

For comparison only, at ZERO metric/frame source reuse the directly derived ORIGINAL continuum polynomial velocity form

 alpha=int_space[g2 P_iAB delta omega_iAB
       +1/2 Lambda_A(barpsi gamma_A delta psi-delta barpsi gamma_A psi)],
 P_iAB=1/2 epsilon^ijk epsilon_ABCD E_jC E_kD,
 Lambda_A=g1 C_A+g2 K_A.                                         (7)

Here C is cubic in E and K linear in E with curvature. Under the same field/coupling map E'=lambda^-2 E, P'=lambda^-4 P, C'=lambda^-6 C, K'=lambda^-2 K and Lambda'=lambda^2 Lambda. Both terms of alpha pull back unchanged; its odd momentum coefficients scale lambda. In particular this is NOT a unit field-independent barpsi delta psi kinetic form. The accepted zero-body inversion obstruction remains; it is not a new result here. Equation(7) is a zero-source continuum polynomial identity and normalization comparison, not a controlled limit or quantization of the finite symmetric-time kernel. It is not the source-dependent velocity form: in particular a literal temporal J00 term can be quadratic in continuum velocities. The finite source-dependent identities below instead use the actual full forces(14) and exact L_t without assuming a first-order source deformation of(7).

## 4. The SAME Weyl dictionary must transform its contraction scale

Let W_kappa(theta_I)=kappa^(|I|/2) C_I for the previously fixed ordered Majorana coordinates theta and Clifford matrices, kappa>0. Kappa is an EXPLICIT mathematical contraction/field-normalization parameter here, not a measured hbar or new physical selection. W_1 is the accepted fixed dictionary. Its induced star product has

 theta_r star_kappa theta_s +theta_s star_kappa theta_r=2 kappa delta_rs.

For kappa'=lambda^-2 kappa, the exact identities are

 W_kappa' (f)=W_kappa(r_lambda f),
 r_lambda(f star_kappa' h)=(r_lambda f) star_kappa(r_lambda h).     (8)

They follow first on every ordered monomial from its degree factor, then on all tests by linearity and the definition of star. The fixed real factor also commutes with the accepted sharp conjugation, so adjoints transport. Equivalently, holding a unit product on both coordinate algebras does NOT make r_lambda a star-algebra isomorphism: for one repeated generator its two sides differ by lambda^-2. No physical product is selected by (8).

On the same fixed W_kappa bookkeeping Fock space, put c_r,kappa=sqrt(kappa) C_r and parity automorphism P(X)=Gamma X Gamma. The transported exterior insertion is

 W_kappa(theta_r wedge W_kappa^-1 X)
                  =[c_r,kappa X+P(X)c_r,kappa]/2.                (9)

For a monomial with or without theta_r, the Clifford anticommutation gives exactly its wedge insertion or0, proving (9); no inverse-kappa factor occurs. Trace-dual Bopp insertions and ordered composites follow by composition, and the normal/Weyl conversion is exp(-kappa Delta/2) with the inherited left-derivative Delta. Thus bilinear coframe operators carry kappa, quartic metric operators carry kappa^2, and their forced contraction/contact terms scale with those same factors. These are the accepted coherent/Bopp maps transported, not a new ordering rule or a replacement Jordan insertion.

At corresponding sources in (3), let rho_(g,kappa) denote the unique trace-dual normalized matrix for W_kappa, without assuming its positivity. Since (3),(8) give equality of its pairings with EVERY W_kappa'(f), nondegeneracy of finite matrix trace yields

 rho_(g_lambda,lambda^4 J,j;kappa')=rho_(g,J,j;kappa).             (10)

The matrix equality concerns the covariantly transported dictionary and full original tests; it requires no new positivity proof. The accepted state became close to maximally mixed by increasing lambda while keeping W_1 FIXED. That is a valid existence statement for that fixed bookkeeping product. It cannot by itself calibrate the physical contraction scale, since covariant transport instead gives (10). This does not withdraw that certificate, choose another favorable cone, or declare the ray physically redundant. Physical field/observable identification is the missing additional datum.

## 5. Explicit action-forced bond current

Fix the even site phase derivation with LEFT odd derivatives

 V_chi=i sum_(z,I)chi_z[psi_zI partial_psi_zI^L
                         -barpsi_zI partial_barpsi_zI^L],        (11)

with real fixed site chi and all links unchanged. Acting on a generator gives i chi_z psi_z or -i chi_z barpsi_z. Acting on each ordered monomial gives i times its psi-minus-bar charge, so V is an even derivation. The Berezin divergence is minus the sum of the odd coordinate derivative coefficients: the four i chi and four -i chi per site cancel. Its finite pullback has determinant1 on each site's barred/unbarred pair and preserves the oriented Berezin measure. This is a derived polynomial symmetry for CONSTANT chi, not a separately attributed physical matter theorem or a new local gauge field.

For an ORIGINAL positively directed anchor e=(x,mu), y=x+mu, define the two explicit even hopping sums

 B_e^A=barpsi_x gamma_A U_e^dag psi_y
                              +barpsi_y U_e gamma_A psi_x,
 C_e^A=barpsi_y gamma_A U_e psi_x
                              +barpsi_x U_e^dag gamma_A psi_y,
 delta_chi_e=chi_y-chi_x.                                       (12)

Gamma placement in B and C differs and is not commuted through U. Write e-=(x-mu,mu). Direct application of (11) to the FOUR terms in(1) gives

 V_chi T_xmuA=(i/4)[delta_chi_(x,mu) B_(x,mu)^A
                    +delta_chi_(x-mu,mu) C_(x-mu,mu)^A].        (13)

For example forward bar_x psi_y gains i(chi_y-chi_x), whereas its negative reverse term gains the opposite sign and therefore contributes the SAME plus hopping sum B. The backward negative bar_x psi_(x-mu) term has chi_(x-mu)-chi_x, producing the plus delta_chi_(x-mu,mu) C after reversing that difference. This checks all signs and explains the second plus. At Nt2 the neighbor labels can coincide but the two anchored U variables remain independent, so B/C are not canceled.

Here is the full original coframe force used in the new current. At each action center r, define H_r,rho,E by

 H_r,rho,E=
 g1 sum_(A0..A3)epsilon_(A0..A3) delta_(A_rho,E)
                                      product_(sigma!=rho)Y_r,sigma,A_sigma
 +g2/4 sum_(k,l,mu,nu,C,D)epsilon^(k l mu nu)F_r,kl^CD
  [delta_(mu,rho)delta_(C,E)Y_r,nu,D
                     +delta_(nu,rho)delta_(D,E)Y_r,mu,C]
 +sum_(mu<=nu)J_r,mu,nu[delta_(mu,rho)Y_r,nu,E
                                      +delta_(nu,rho)Y_r,mu,E],
 b_r,nu,E=sum_rho A_r(j)_rho,nu H_r,rho,E.                       (14)

F is the original trace of CLOSED plaquette and gamma_C gamma_D gamma5. For s_t only, set b_r=0 outside its middle-slice action centers. For full S use every center. Curvature has zero V_chi variation because links are fixed, but its entire coefficient remains in b. The source diagonal contributes twice; off-diagonal appears once as in(14).

Substituting(13) in sum_(r,nu,E)b_r,nu,E V T_r,nu,E and collecting the SAME directed anchor gives the explicit direct-convention bond current

 J_e=(i/4)sum_A[b_x,mu,A B_e^A+b_y,mu,A C_e^A],
 V_chi s_t=sum_e delta_chi_e J_e.                                (15)

Every term has now been given in original hopping, curvature, determinant, source and frame coefficients. It is not an unnamed action derivative. In s_t the zero convention for b handles all boundary edges. In S, both endpoint action centers contribute. There is no new U(1) link/probe source, selected curvature plane or improvement term. At J=0 the EHC and determinant currents have Grassmann degrees4 and8; the J contribution has degree4. Nonuniform chi produces a local divergence insertion; constant chi makes every delta_chi_e zero, proving global invariance of the FULL source action and every coframe/metric test.

The finite current need not be Hermitian under an unchosen physical adjoint: the explicit i records the algebraic phase convention. It is not a Wick-rotation, real-time current or physical matter normalization assumption.

## 6. Cotangent and continuum kinetic charge, then the actual boundary operator

On a pair boundary keep the accepted canonical evaluation momenta independent. For the phase vector field restricted to its odd coordinates, define

 mu_in,chi=p(V_in), mu_out,chi=P(V_out).

Use the same chi on the shared slice b. The accepted graph gives

 mu_out-mu_in
   =f_a(V_a)+f_b(V_b)+f_c(V_c)
   =V_chi s_t=sum_e delta_chi_e J_e.                              (16)

The kappa(V_b) terms cancel, rather than being set to zero; V does not act on va/vb, so their momentum evaluations are zero, though their dependence remains in every f and J. Equation(16) is the exact graph/kinetic-current diagram with the NEW explicit current(15). It does not identify independent barpsi with p_psi or discard the connection dependence.

Evaluating the continuum form(7) on delta psi=i chi psi, delta barpsi=-i chi barpsi, delta omega=0 gives

 alpha(V_chi)=int_space i chi Lambda_A barpsi gamma_A psi.         (17)

The two half coefficients add, since V is even. The connection momentum term evaluates to0, but Lambda retains g1 C+g2 K. Equivalently in the original continuum coframe, a local phase gives V E_muA=i(partial_mu chi)barpsi gamma_A psi: the undifferentiated phases cancel against each other, while D_mu acts on chi. Thus (17) is its actual time-current coefficient. The lattice current(15) is the finite exact hopping counterpart; equality to a controlled continuum conserved physical charge is not established. Equation(17) is a degree4/8 polynomial kinetic charge, not a field-independent occupation bilinear. Its rescaled Lambda gains lambda^2 while its bilinear loses lambda^2, so it is invariant.

On the original pair-boundary test algebra FIX

 R_chi(t)F=F(exp(i t chi)psi,barpsi exp(-i t chi),U),
 N_chi=-i V_chi.

This operator is defined without a Hilbert product. On a monomial it counts weighted psi-minus-bar occurrences. It acts only on old/shared spinors at input and shared/new spinors at output; all links are fixed. Let the explicit original vertex be

 (J_t,chi F)=int dHaar_a I_a exp(s_t)
                                      [sum_e delta_chi_e J_e] F.

Then the exact quantum identity is

 V_out L_t-L_t V_in=J_t,chi.                                    (18)

Proof: shared differentiation contributes V_b L=L V_b+vertex(V_b s). New differentiation contributes V_c L=vertex(V_c s). Old divergence zero gives L V_a=-vertex(V_a s), so subtracting that old input term supplies the remaining plus sign. Each integrand equality includes the derivative of the test; nothing imposes classical stationarity inside the quantum integral. All integrations are finite coefficientwise with compact links and the existing test regularity. This is the inherited IBP method evaluated on the NEW explicit original current, not an independent physical norm proof.

For constant chi, every difference in(15) is0, hence V_out L=L V_in and R_out(t)L=L R_in(t). The finite identity also follows by the old-variable phase substitution and its unit Jacobian. Global charge conservation is not a constraint setting that charge to zero, and is not an extra singlet projection. For two steps the current commutator is J_1,chi L_0+L_1 J_0,chi with copied generators matched. Sewing retains both interfaces. Local chi generally gives a nonzero vertex, not a new gauge symmetry.

## 7. Explicit temporal metric/current source contacts

Let alpha be the original literal coordinate J_(r,00). For a prescribed frame direction beta, A_beta and A_alphabeta are the actual supplied jets; for this literal alpha, A_alpha=0. Define C=V_chi s_t. With fixed phase derivation, C_alpha=V_chi s_alpha and C_alphabeta=V_chi s_alphabeta. Differentiation commutes coefficientwise with phase and the compact/Berezin integrals.

At j=0, s_alpha=Q_r,00=sum_A T_r0A T_r0A for an action center r. Formula(13) gives the ACTUAL local variation

 V_chi Q_r,00=(i/2)sum_A T_r0A
   [delta_chi_(r,0) B_(r,0)^A
                    +delta_chi_(r-0,0) C_(r-0,0)^A].             (19)

Only constant GLOBAL chi makes this0 by symmetry. It is not set to0 for local phases. More generally V Y_mu=sum_nu A_mu,nu V T_nu and

 V Q_mu,nu=sum_A[(V Y_muA)Y_nuA+Y_muA(V Y_nuA)].

This includes every temporal carrier introduced by a time-mixing first/mixed-second frame jet, even if the component label is spatial. No32-mode reduction is made before these operations.

For an edge e=(x,mu), the literal source derivative of(15) at j=0 is explicitly

 (J_e)_alpha=(i/2)delta_(mu,0)sum_A[
       delta_(x,r)T_r0A B_e^A+delta_(y,r)T_r0A C_e^A].            (20)

It follows by differentiating the full force(14): (b_x,mu,A)_alpha=2 delta_(x,r)delta_(mu,0)T_r0A. Summing delta_chi_e(20) gives(19), checking the diagonal factor2 and both temporal anchors. At nonzero j replace this force by 2 delta_(x,r) A_x(j)_0,mu Y_x0A. Thus the contact is a fixed original coefficient, not a fitted current prescription.

For frame beta, differentiate A and each Y slot of(14); F/links remain fixed. This means all four determinant single-slot derivatives, both EHC pair derivatives, and J Q_beta enter s_beta. Mixed frame jets include single-slot acceleration and all ordered distinct-slot replacements. For this literal alpha with independent frame beta,

 s_alpha=Q_r00(j), s_alphabeta=(Q_r00)_beta,
 C_alpha=V Q_r00, C_alphabeta=V (Q_r00)_beta.                     (21)

If beta is another literal J, s_alphabeta=0 for straight coordinates. A general curved source path instead retains its supplied J_alphabeta and A_alphabeta terms. No source contact is inferred absent from the actual path.

The first derivative of the actual current vertex in(18) inserts

 exp(s_t)[s_alpha C+C_alpha],

and its mixed derivative inserts

 exp(s_t)[(s_alpha s_beta+s_alphabeta)C
                       +s_alpha C_beta+s_beta C_alpha+C_alphabeta]. (22)

Equations(14),(19)-(21) specify the current coefficients in these terms. Differentiate (18) with fixed V_in/out to obtain the same identity for L_alpha and L_alphabeta with(22) on the right. For K=L1 L0, retain

 K_alphabeta=L1_alphabeta L0+L1_alpha L0_beta
                           +L1_beta L0_alpha+L1 L0_alphabeta.    (23)

All first/mixed-second derivatives of its current identity include these four placements and each interface's(22); none is replaced by an equal-time product or a marginal score. The fixed full two-slice coherent/Bopp insertion formulas may be applied to every displayed vertex. Their scalar/bilinear ordering contacts remain forced by the accepted map, rather than being replaced by a Jordan Q operator. This connects the current diagram to the actual microscopic metric source; it does not identify the resulting operation with a physical coincident metric measurement.

## 8. Normalized original Ward identities with all contact/quotient terms

Use now the entire periodic S and J_e from ALL action centers. On every original test f with the accepted link regularity, the phase measure change gives

 ell(V_chi f+f C)=0, C=V_chi S,
 omega(A_f)=0, A_f=V_chi f+f C.                                  (24)

This is valid for arbitrary local chi, all full sources and source-dependent tests, not only constant-neutral f=1. It follows from the zero Berezin divergence established in section5; no local gauge invariance is presumed.

For any X_s, write m_alpha=omega(s_alpha), m_alphabeta=omega(s_alpha s_beta+s_alphabeta). Direct quotient differentiation gives

 (omega X)_alpha=omega(X_alpha+X s_alpha)-m_alpha omega X,
 (omega X)_alphabeta=
 omega[X_alphabeta+X_alpha s_beta+X_beta s_alpha
                                    +X(s_alpha s_beta+s_alphabeta)]
 -m_alpha omega(X_beta+X s_beta)-m_beta omega(X_alpha+X s_alpha)
 +(2 m_alpha m_beta-m_alphabeta)omega X.                          (25)

Here X=A_f includes

 (A_f)_alpha=V f_alpha+f_alpha C+f C_alpha,
 (A_f)_alphabeta=V f_alphabeta+f_alphabeta C
                       +f_alpha C_beta+f_beta C_alpha+f C_alphabeta.

The quotient terms in(25) vanish for X=A_f ONLY after using the zeroth and both first Ward identities at the SAME source family. They have not been omitted by treating Z constant. For source-independent f and literal temporal alpha, the first identity is explicitly

 omega[(V f+f C) Q_r00+f V Q_r00]=0.                             (26)

For f=1 this is omega(C Q_r00+V Q_r00)=0, including the explicit local metric contact(19). The general f term V f is essential. With beta a frame direction and f=1, the mixed identity becomes

 omega[C(Q_r00 s_beta+(Q_r00)_beta)
          +(V Q_r00)s_beta+(V s_beta)Q_r00+V(Q_r00)_beta]=0.      (27)

The arbitrary f version is obtained from the fully displayed(25), not by dropping its derivatives. This is an actual local current/metric-response relation for the original full functional, with action, frame and normalization contacts. It is a linear Ward restriction, NOT covariance positivity or the physical metric-response normalization sought by L1.

## 9. Covariance of the constructed charge/current/operator/contact diagram

At the corresponding couplings/sources in(2), the full coframe force b gains lambda^2, while every B_e and C_e loses lambda^2. Consequently

 J_e(g_lambda,lambda^4 J,j;lambda^-1 q)=J_e(g,J,j;q),
 r_lambda C_lambda=C,
 mu'_chi=mu_chi, R_lambda V_chi=V_chi R_lambda.                   (28)

This holds separately for the determinant, EHC and J terms: their force weights are respectively lambda^8 lambda^-6, lambda^4 lambda^-2, and lambda^4 lambda^-2. Connection/link dependence remains unchanged. The cotangent charge uses one q and one p with opposite weights, hence invariant, agreeing with the continuum charge(17). Current/source derivatives in literal J acquire lambda^-4 per derivative; frame derivatives do not. The explicit metric contact(19) has degree4 and thus lambda^-4, and(20)'s literal-current derivative has the same weight. Arbitrary-test Ward identities scale with their test weight; the actual degree12 temporal-response test retains lambda^-16 after a literal J derivative as above.

The current vertex obeys the same actual kernel intertwining factor as L:

 R_out J_t,chi,lambda=lambda^64 J_t,chi R_in.                     (29)

Equations(5),(18),(28) prove the commutation of the entire normalization/current/kernel diagram; it is not merely a scaling inventory. Its C2 derivatives follow from the exact full source equality and(22),(25). No scalar response is substituted for the time-mixed metric insertions.

The phase generator counts psi-minus-bar occurrences independently of coordinate scale. It therefore constrains any future physical number/charge assignment, while leaving the contraction normalization in(8) covariant rather than fixed. Its coincidence with a chosen bare Fock number is NOT inferred: our N acts on the original boundary TEST algebra, while a physical matter number would require the physical correspondence and an actual state. Neither (17) nor (28) contains a new measured a, hbar, condensate or matter residue. This is exactly why symmetry normalization alone cannot supply B3.

## 10. The attempted physical map and its exact remaining metric/normalization equation

This is the precise successful first algebraic correspondence:
 original kinetic/cotangent phase charge --(15)-(17)--> explicit bond current
 --(18),(22)-(27)--> fixed original boundary generator and metric-source vertices,
 with the WHOLE diagram transformed by(3),(5),(8),(28)-(29).

A physical reconstruction retaining the CONSTANT global symmetry must still provide its actual domain D_phys and maps I_B, not just choose a coefficient norm. If I_B R(t)=U_phys(t) I_B on that domain and U_phys is a strongly continuous unitary group, its generator Q_phys must satisfy

 I_B N_global=Q_phys I_B,
 <Q_phys u,v>_phys=<u,Q_phys v>_phys

on the relevant domain, with the full self-adjoint/group domain specified. Local chi in(18),(24) is a current variation, not an assumed physical unitary symmetry or gauge constraint. If an actual transfer realization exists, the source-dependent equation to satisfy is

 I_out,s L_s=T_phys,s I_in,s.                                    (30)

For constant global phase it must also preserve the corresponding generator intertwining. Neither the original algebraic L nor the conditional Choi channel accepted earlier supplies I_B, its positive pairing or the physical quantum link/time adjoint. The phase diagram provides explicit equations they must consume. No auxiliary unitarity implies physical transfer unitarity here.

Crucially a physical METRIC/source map must match derivatives of(30), not just(24). Its first required identity is

 I_out,alpha L+I_out L_alpha
                  =(T_phys)_alpha I_in+T_phys I_in,alpha.        (31)

Here L_alpha is the ACTUAL Q_r00 vertex in section7; the mixed identity is obtained by differentiating every factor of(31), including the two cross terms and I_alphabeta. Physical link/time observables must retain these source contacts and the accepted coherent/Bopp ordering terms. The map must identify the resulting physical insertion with Volovik's Ehat_mu Ehat_nu in its actual physical product/state, not declare bare exterior multiplication or a score to be that observable. Equations(19)-(27) are NECESSARY original current/metric compatibility data for(31), not a solution for its unknown physical operator or its normalization.

The current construction attempts the action-forced generator and establishes(16),(18),(26)-(29), without selecting a physical domain/adjoint to make(30)-(31) hold. The precise unresolved physical identification is I_s/T_phys,s/O_phys(Q) satisfying(30)-(31), its mixed derivative and physical adjoint/product together. Original source premises do not supply those objects for this benchmark; this inspected correspondence is unmatched. This is not a theorem excluding their construction or all physical routes. Repeating the known zero-body inversion obstruction, or failing an optional CAR/Jordan/record norm, would not resolve this equation and has not been used as a new no-go.

A separate normalization equation remains even if a physical operator map is later built. At fixed a, write a proposed physical coframe and metric calibration as

 E_phys=(c_E/a) T, G_phys=c_Q Q, c_Q=(c_E/a)^2                  (32)

only when the physical operator/source map justifies these polynomial relations and units. A general nonfactorizing metric calibration need not have this tetradic form. Equation(32) is an explicit possible calibration requirement, NOT an adopted physical definition. Keeping G_phys invariant under the coordinate ray requires

 c_Q,lambda=lambda^4 c_Q,
 (c_E,lambda/a_lambda)=lambda^2(c_E/a).                           (33)

If K is a physical source conjugate to G_phys, the simple constant linear calibration would require J=c_Q K, and its connected response would contain c_Q^2 W_JJ, together with any physical volume/time/unit factors. Thus the lambda^-8 in W_JJ is exactly compensated by c_Q,lambda^2. A field normalization cannot be inferred from that suppression. Source- or field-dependent calibration would add its OWN first/mixed-second contacts and must match(31), not be inserted by hand. No absolute c_Q, a, hbar, physical temporal normalization or matter kinetic residue is fixed by this Ward construction or the cited finite action.

Where an appropriate microscopic mean is nonzero, a ratio W_JJ/(omega Q)^2 would algebraically cancel the lambda weights. This observation neither proves that mean nonzero/physical nor identifies the ratio with L1's chi, its volume/tensor projection, matter reference or required range. Volovik's tetradic and full quartet metrics may require distinct calibrations and correlators. Their physical comparison cannot be replaced by this algebraic cancellation. Original dimensionless susceptibility, B3 interval/speed and matter/light normalization remain ROOT-owned open obligations.

This gives the requested clear link: the first current/kinetic map fixes an invariant symmetry generator and exact microscopic metric-current/source contacts; (31) is the unmatched physical insertion equation; (33) is its necessary normalization covariance. A Ward identity alone cannot discharge either the operator identification or calibration. The next physical datum must arise in a controlled state/kinetic/matter construction satisfying those equations, not by selecting a favorable lambda, cone, background or source channel. No additional premise is chosen here and no alternate model/order/sector/boundary is proposed as a replacement.

## 11. Evidence and scope

This result used manual mathematical derivation, direct primary/accepted-source reading and ordinary artifact/hash/continuity bookkeeping only. No scientific evaluator/CAS/exterior/Haar/matrix/Gram script, test/build, Lean/native/slot/controller action, process/suite probe, dependency or harness change occurred. ROOT ordinary suite and publication work were untouched. There is no infrastructure blocker.

New results submitted: exact full field/Berezin/J/j/kernel/cotangent/product covariance, explicit original bond currents with their distinct anchors/full forces, kinetic phase charge, actual fixed boundary phase-generator/current intertwining, explicit temporal metric/current coefficient/contact and normalized C2 Ward identities, and exact covariance of that diagram. Their independent actual mathematical and original-source reviews and ROOT personal intake are still REQUIRED; prospective approval alone accepts none of these formulas.

Physical Hilbert domain/product/adjoint/CAR, positive quantum link/time dynamics, physical coincident metric/operator/source map, metric mean/spatial order/signature, absolute/matter calibration, controlled limits, B3/N4, tensor/matter/light/transport and publication acceptance are NOT established. Accepted original nonzero Z, temporal response and prior scoped coherent/conditional constructions remain actual. This is only one deeper physical support milestone; ROOT retains ordinary L1 roadmap/repairs/manuscripts/claims/figures/consumers/findings/gates/reviews/integration/main/operator authority. Normal owned-branch checkpoint delivery follows independent actual review, not a new source or publication closure.
