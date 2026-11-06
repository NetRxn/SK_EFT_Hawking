# Actual P0 to N0/C3 full cut/source transport — corrected r2

Status: ACTUAL MANUAL RESULT CANDIDATE awaiting independent actual mathematical and original-source reviews. Task l1-p0-n0-full-cut-transport-build-r1, owner Executor01a1ac65, parent publication ROOT01a13f67. No numerical/scientific evaluator, matrix program, Lean/build/test, backend/controller or slot was used. No positive physical reconstruction is claimed.

Revision custody: R1 remains frozen at SHA2564ed038920655a9fa48356f09c04502fe6d124db30dce989a06d8198f4b28d4b0. Both independent actual R1 reviews returned REVISE for reflected complex-coupling conjugation and an overstated noncommuting-link control. R2 corrects those formulas/domain and adds a fully specified local-gauge image with proved nonzero link commutator. Generic transport sections2–7 are unchanged. New independent actual review is required.

## 1. Authority, objects and result surface

Canonical objective P0_NUMERICAL_FULL_CUT_TRANSPORT_OBJECTIVE.md explicitly commissions this BUILD before numerical Task3 consumes the accepted physical metric/kernel certificate. Reuse unchanged accepted N16_TEMPORAL_BOUNDARY_IDENTITY §6, ORIGINAL_ONE_SLICE_SOURCE_KERNEL, ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT, ORIGINAL_METRIC_SEWING_DOMAIN_CONSTRUCTION, ORIGINAL_NONZERO_NORMALIZATION_CONSTRUCTION and the independently accepted NUMERICAL_PHYSICAL_CONVENTION_CROSSWALK. These live under docs/audits/2026-11-05-l1-physical-bridges on exact parentacb34ee7d99d55703a19dc2f7cbdeaa666e717cc. ROOT numerical planR2 is a separately declared target, not proof of the transport constructed here.

Prospective brief b8afb928bdd82a45ee3e496d8f4795fd4123d3c4c38889b6d22aaa9e13ef5ba5 received separate independent math/source ACCEPT for the bounded manual attempt. Lead read BOTH full reports and rechecked BOTH SAME packets fresh before this derivation. Prospective approval is not actual acceptance.

P is the accepted Euclidean reference with q=(-iτ1,-iτ2,-iτ3,I2), gamma5=diag(I2,-I2)=gammaP0 gammaP1 gammaP2 gammaP3, WORLD time0/RP=gammaP0. N is the numerical plan's Euclidean M_N: gammaN,A=gammaC,pi(A), pi=(3,0,1,2), fixedgamma5, WORLD time0. Its ordered gamma product is -gamma5. C has canonical q at numeric labels and WORLD time3. N is NOT Lorentz L_P; no imaginary coframe/source substitution occurs in this result.

We construct a direct SAME-WORLD P0→N0 map, then compose the reviewed N0→C3 permutation. The exact target coupling family is
 g1_N=-g1_P, g2_N=g2_P;       g1_C=-g1_P, g2_C=-g2_P.       (1)
Both original and reflected full defect-inclusive PAIR kernels, all sources/contacts and the accepted metric controls transport at these mapped inputs. No same-coupling/same-cut identification is claimed. All finite real or complex coupling inputs map; this is not selecting a favorable phase.

Keep the entire original regulator,128 independent odd coordinates,64 independent anchored compact Spin4 links, quartercoframe, exp(+S), inherited top/Haar, determinant+fullEHC, literal once-counted J, any prescribed C2 worldframe, both interfaces and original shared variables. Word w=closed D†C†BA or printed ABC†D† is held FIXED throughout each identity; the map does not equate them. Physical metric/reflection controls below concern the accepted CLOSED word only.

## 2. Explicit compact spinor transformation and chirality

Let τ1=[[0,1],[1,0]], τ2=[[0,-i],[i,0]], τ3=diag(1,-1), q0=-iτ1,
 S=diag(q0†,I2), U=(I2+iτ2)/sqrt2, B=diag(U,U)S.
Since (iτ2)†=-iτ2 and τ2²=I, UU†=(I-i²τ2²)/2=I. Explicitly U=[[1,1],[-1,1]]/sqrt2, detU=1. Also q0†=iτ1 has determinant1 and is unitary. Thus B=diag(Uq0†,U) belongs to the actual blockSU2xSU2 Spin4 representation, detB=1, and B commutes with gamma5.

Ordinary Pauli multiplication gives
 Uτ1U†=τ3, Uτ2U†=τ2, Uτ3U†=-τ1.
After conjugating gammaP by S, its upper-right blocks are (I,iτ3,-iτ2,iτ1). Conjugating further by diag(U,U) makes them (I,-iτ1,-iτ2,iτ3). Compare N's upper-right blocks (I,-iτ1,-iτ2,-iτ3). With h=(+,+,+,-), we have the COMPLETE matrix identity
 B gammaP,A B^-1=h_A gammaN,A,       B gamma5 B^-1=gamma5. (2)
Hermitian lower-left blocks give the same real h. In particular RN=gammaN0=B RP B^-1=[[0,I],[I,0]]. Producth=-1 is exactly compatible with P orderedproduct+gamma5 and N orderedproduct−gamma5. No chirality operator has been silently redefined. B is a compact spinor change; h is the separate internal orientation sign in comparing the two declared gamma lists.

## 3. Four original coframe terms and complete unsquared action

At the SAME site x/worlddirection mu and every independent anchor, define the invertible configuration map F_B by
 psiN,x=B psiP,x, barpsiN,x=barpsiP,x B^-1,
 U_N,xmu=B U_P,xmu B^-1.                                   (3)
Independent bars/psis stay independent. Both forward/backward anchors map individually, even when endpoint vertices coincide on Nt2. Because B is unitary, dagger and inverse commute with conjugation.

For the forward first term, substitution gives
 barpsiN,x gammaN,A U_N,xmu† psiN,y
 =h_A barpsiP,x gammaP,A U_P,xmu† psiP,y.
For the forward second, substitution gives
 barpsiN,y U_N,xmu gammaN,A psiN,x
 =h_A barpsiP,y U_P,xmu gammaP,A psiP,x.
The two backward terms respectively give h_A times barpsiP,x gammaP,A U_P,zmu psiP,z and barpsiP,z U_P,zmu† gammaP,A psiP,x, with z=x-mu. Therefore the four +,-,-,+ increments, noncommuting matrix orders and commonquarter are all retained:
 T_N,mu^A(F_B q)=h_A T_P,mu^A(q).                          (4)
For arbitrary SAME worldframe A(j), Y_N,mu^A=h_A Y_P,mu^A; hence Q_N,mu,nu=Q_P,mu,nu. World labels and their time/spatial meaning are unchanged in this direct step.

Every fixed plaquette word transforms by H_N^w=B H_P^w B^-1 in the SAME order. Trace covariance and(2) yield
 Tr(H_N gammaN,C gammaN,D gamma5)=h_C h_D Tr(H_P gammaP,C gammaP,D gamma5).
Together with the two h factors from Y, each COMPLETE EHC summand is unchanged. Worldepsilon and g2/4 are untouched, so BEFORE integration or squaring,
 S2_N^w(F_Bq,A)=S2_P^w(q,A).                              (5)
No diagonal trace assumption or chosen curvature plane is used. For the cosmological term, a nonzero internal epsilon uses each A once, giving producth=-1:
 S4_N(F_Bq,A)=-S4_P(q,A).                                 (6)
Consequently(1), with J_N=J_P and A_N=A_P, gives exact complete exponent equality s_N(F_Bq)=s_P(q), including all centers/fields/anchors, arbitrary finite couplings, full literal metric source and all frame-dependent action terms. Linear coframe source Lambda and auxiliary coordinates instead require Lambda_N,mu,A=h_A Lambda_P,mu,A. Original local phase chi_N=chi_P; basisB commutes with its scalar multiplication, so original current/phase derivatives transport without an added source.

These are identities of the entire original polynomial family, not just coefficients surviving a chosen saturation quotient. General prescribed complex profiles obey the algebraic identities; reality assertions are restricted to the original real domains. No Gaussian/Hermite normalization, Lorentz source phase, extra kinetic term or physical product is inserted.

## 4. Exact Haar/Berezin and auxiliary orientation

Conjugation by each fixed SU2 block is a Haar-preserving compact-group automorphism, independently on all original links/chiral factors. The odd transformation is blockB on four psi coordinates and B^-1 transposed on the four bar coordinates. Each has determinant1, so their product and inverse Berezin Jacobian are1 at each site and at every integrated cut. B is blockdiagonal on L/R and never reorders the inherited generators; any site-block ordering is the same here. Thus top extraction and productHaar are preserved, not merely up to a fitted scalar.

If the independent Hermite/Dirac route is included, change each real auxiliary h_aux,mu,A to h_A h_aux,mu,A in N. It preserves its product centered Gaussian probability and all actual odd/even moments because it is a real sign isometry. The coefficient contraction h_aux T and analogous linear source is unchanged. No i-contour or identification with the physical tetrad is involved. The whole Dirac bilinear matrix transforms by the site-block B similarity, preserving its determinant; the original W polynomial must be evaluated at the mapped couplings/coframe coordinates, not declared pointwise identical with unchanged input labels. These facts transport the exact source construction; no new numerical evaluation is performed here.

## 5. Generator-level anti-linearity: exact theta, not just R

Use exactly N16's rho0 and thetaP psi_a=sum_b barpsi_(rho x,b) RP_ba, thetaP barpsi_a=sum_b RP_ab psi_(rho x,b), and thetaP f(U)=conjugate f(sigmaP U). Let Phi act on functions by pushforward Phi f=f∘F_B^-1; this is complex-linear. To check thetaN=Phi thetaP Phi^-1 on N generators, first note Phi^-1 psiN=B psiP and Phi^-1 barpsiN=barpsiP B^-1.

Writing psi as a column and barpsi^T as its independent row transpose, anti-linearity gives
 Phi thetaP Phi^-1 psiN
  =conjugate(B) RP^T B^T barpsiN^T
  =(B RP B†)^T barpsiN^T=RN^T barpsiN^T.
The key identity is (B RP B†)^T=conjugate(B) RP^T B^T; B†=B^-1 is used. For the barred component, conjugate(B^-1)=B^T gives
 Phi thetaP Phi^-1 barpsiN,a=sum_b RN_ab psiN,(rho x),b.
These are the FULL declared transposed-index thetaN laws, with no unproved assumption that B is real. Reversal of exterior products then extends the identity from generators.

On spatial links, conjugating sigmaP through F_B gives RN U_N,(rho x),i RN. On each temporal anchor it gives RN U_N,(rho x-0),0† RN, since dagger commutes with the UNITARY B conjugation. On Nt2 EACH temporal anchor remains its own conjugate inverse; no swap or translation is substituted. Therefore for every scalar link function the actual conjugate pullback also intertwines. These identities establish
 thetaN Phi=Phi thetaP                                           (7)
on the entire actual polynomial/link function algebra. RP gammaP,A RP=s_A gammaP,A implies RN gammaN,A RN=s_A gammaN,A with s0=+1,si=-1, hence inherited r=-s is unchanged. Equation(4)'s real h commutes with these coframe signs. Nothing here identifies theta with a physical adjoint.

The direct P0/N0 full profile maps are consequently identical:
 A_circ(x)=Ew0 conjugate(A(rho0 x)) Ew0,
 boldJ_circ(x)=Ew0 conjugate(boldJ(rho0 x)) Ew0.                  (8)
BoldJ has diagonal J and half offdiagonal J, once counted. Linear coframe-source profiles include h_A on their internal component, commuting with signed conjugation because h is real. No source-family closure is inferred; any reparametrization still owes the actual first/second derivative chain conditions.

## 6. Full pair kernel, temporal defect and four typed cut maps

The field map(3) is sitewise, time-independent and invertible; it acts separately on every old/shared/new coordinate set and every original anchor. At a three-slice cut apply it ONCE to the shared middle variables, not as two independent copies. The complete local exponent equality in§3 and measure identity§4 give the full pair integral after this change of variables.

To exhibit the retained temporal defect explicitly, reuse the accepted canonical formal decomposition s=C+B.R+H00 R.R at the chosen temporal direction, with R=Rminus+Rplus and B=Bs+Bt. Equation(4) maps R_N=h R_P. The actual canonical expressions for C and H have C_N=C_P, H00_N=H00_P; comparing the complete polynomial in formal temporal coframe components gives B_N=h B_P, separately Bs_N=h Bs_P and Bt_N=h Bt_P, at the mapped couplings. Equivalently, this follows term by term from the determinant/EHC identities before substituting R. Thus
 D_N=Bt_N.Rminus_N+2H00_N Rminus_N.Rplus_N
    =Bt_P.Rminus_P+2H00_P Rminus_P.Rplus_P=D_P.                (9)
Every Bt term still uses its actual temporal-curvature anchors; no temporal link was frozen. The full factor expD, all source profiles on both endpoints, C/B/H contacts and their overlaps survive. Diagnostic D=0 restrictions are transported but NEVER substituted for the unrestricted source family. This proves a full defect-inclusive PAIR-kernel change, not a general reduced one-slice evolution.

Let Phi_minus:B_P,-→B_N,- and Phi_plus:B_P,+→B_N,+ be the function pushforwards on the ACTUAL original input/output boundary coordinate spaces. Primed Phi'_minus/Phi'_plus act on the ACTUAL reflected opposite input/output spaces. All are the restriction of(3) to their named coordinate roster, including its correct retained link variables. Unit Berezin/Haar Jacobian gives for each boundary test f
 L_N Phi_minus f=Phi_plus L_P f,
 L_N=Phi_plus L_P Phi_minus^-1.                              (10)
This follows directly by substituting each integrated old odd/link variable in the kernel, holding all retained variables fixed; no physical quotient or norm is chosen.

Because(7) respects cut reversal,
 R_N,minus Phi_minus=Phi'_plus R_P,minus,
 R_N,plus Phi_plus=Phi'_minus R_P,plus.                       (11)
The bilinear Berezin/Haar sewing pairing is preserved. If Phi on a paired space is identified with its transported counterpart, this is beta_N(Phi f,Phi g)=beta_P(f,g); on distinct dual boundary spaces it is the corresponding contragredient relation. Hence the transpose transports as
 L_N^t=Phi_minus L_P^t Phi_plus^-1,
with its transpose-domain interpretation on the reversed spaces. Combining with the typed R maps in(11), or applying(7) directly to the kernel, gives
 L_N^theta=Phi'_plus L_P^theta (Phi'_minus)^-1.                (12)
These are the four ORIGINAL/OPPOSITE cut maps required by ROOT. In particular original Ltheta=Rminus L^t Rplus^-1 remains true with the same opposite cut ordering. No auxiliary coefficient-Haar adjoint is substituted for this transpose or geometric theta.

At periodic sewing both cuts are acted on by the SAME sitewise B, so the full trace/supertrace pairing and both original temporal interfaces are preserved. Orientation/parity factors commute with the number-preserving blockB action; no antiperiodic boundary or singlet sector is selected. Existing range/constraint/annihilator relations transport by these invertible maps with their actual sidedness, not by declaring a new positive physical domain.

## 7. C2 sources, current, normalization and map derivatives

The direct field/cut maps and B,h are CONSTANT in every source parameter. Their own first/mixed-second derivatives are zero by construction, not by analogy with unknown physical intertwiners. Coupling arguments obey g1_N(q)=-g1_P(q),g2_N(q)=g2_P(q) if the supplied family varies them; hence every g1 derivative carries its minus and other parameter pullbacks follow the full chain rule. With fixed couplings and the original literal metric/frame parameters, J_N=J_P,A_N=A_P,chi_N=chi_P, and every first/repeated/mixed frame jet, including A_ab, is identical in the direct step. Source-dependent test functions/insertion operators are transported rather than assumed constant.

Differentiating(10) at corresponding inputs therefore transports L_alpha and L_alphabeta by the SAME Phi maps, with every actual derivative of s/C/B/H/D. Formula(9) implies D_alpha and D_alphabeta transport too, so derivatives of expD are expD D_alpha and expD(D_alphabeta+D_alpha D_beta), retaining all crossing/overlap terms. A product of the two actual pair factors has its four mixed placements: firstmixed-second, secondmixed-second, and BOTH cross-first placements, without identifying overlapping middle variables. Multipliers varying with parameters contribute their ordinary first/mixed-second product terms. Reflected kernels obey the differentiated(12), with full signed conjugate profiles(8), not an assumed same-profile source family.

The complete unnormalized scalar functional and numerator for ANY transported test obey Z_N(q_N)=Z_P(q_P),N_N(q_N)=N_P(q_P), by§4/periodic sewing. Their entire first/mixed jets follow the declared parameter substitution. Thus a nonzero P neighborhood maps to a nonzero N neighborhood; it is not the same numerical coupling point by renaming. In particular the accepted mathematical witness(2^1717,1,J0,A=I) maps to N(-2^1717,1,J0,A=I). Its Z>1 certificate is transported as a finite coordinate identity; it is not a physical phase selection.

Whenever that denominator is legitimately nonzero, normalized mixed jets retain
 (N/Z)_ab=N_ab/Z-(N_a Z_b+N_b Z_a+N Z_ab)/Z²+2N Z_a Z_b/Z³.    (13)
All action/insertion/frame/current/multiplier/measure contacts and BOTH denominator derivatives remain. Frozen Haar measure jets are actually zero because the fixed compact measure is unchanged, not an assumed replacement varying measure. Original physical maps30–31, if separately constructed, would still need their OWN source derivatives; they are not set to zero by these constant coordinate maps. No Lorentzian normalized functional or new physical source calibration is inferred.

## 8. Actual UNSQUARED EHC and nonzero S4 discriminators

Use exactly the COMPLETE closed-action coefficient test from accepted EHC result§5: independent bars at x, barL1=b1,barL2=b2; psi_R1=u at y=x+2 and psi_R2=v at z=x+3; all other odd coordinates, including the opposite time slice, setzero. Both temporal-anchor collections are I. Spatialj=2/k=3 linkpattern has I atorigin and -I atthematchingneighbor in BOTH times; directioni=1 at time0 isI, at time1 origin H=diag(I2,iτ3), otheranchorsI. The result controls every othercenter/worldplane/chiral/internal contribution and gives
 [b1b2uv] (g2_P S2_P)=+2i g2_P,
 [b1b2uv] thetaP(g2_P S2_P)=-2i conjugate(g2_P).                      (14)
S4 is degree8 and does not contaminate this degree4 test. The inherited reflection comparison is for finite REAL couplings, where conjugate(g2_P)=g2_P. The written formula also gives its exact complex extension by anti-linearity; the unreflected line is complex-linear in g2_P. These accepted real-domain values plus the explicit coefficient conjugation are reused, not recomputed by a program.

Push the ENTIRE test substitution through(3): every spinor column is multiplied byB, every bar row byB^-1, and every link byB conjugation. Keep b1,b2,u,v as the SAME four ordered test-algebra generators, rather than extracting the same named N spinor coefficient after mixing. Equations(5),(7) now give the TARGET UNSQUARED controls
 [b1b2uv] (g2_N S2_N at the pushed image)=+2i g2_N,
 [b1b2uv] thetaN(g2_N S2_N at that image)=-2i conjugate(g2_N).          (15)
Here g2_N=g2_P and the theta statement means reflect the action and then evaluate on the pushed configuration. The inherited ±I/H anchor pattern is pairwise COMMUTING, as is its global B image. Equation(15) alone is an actual unsquared SIGN/gamma-order control for the FULL original/reflected action, not a noncommuting-LINK control. It is not a symboliccoframe proxy or g2^4 subtotal. Section8a supplies the stronger actual link control. The term-by-term derivation(5) controls every summand and(7) its reflection, so the image test has exactly the old complete roster. Omitting the h contribution from either gamma or coframe, changing g2_N's sign or replacing Ltheta byL would violate(15).

### 8a. Explicit noncommuting-link image, with ALL incident anchors transformed

Let a=(time0,spatialorigin) and b=(time1,spatialorigin), and put K=diag(I2,iτ1). Choose actual site gauge matrices G_b=K and G_x=I4 at ALL other vertices. Transform the ENTIRE test configuration by
 U_xy^G=G_y U_xy G_x^-1, psi_x^G=G_x psi_x, barpsi_x^G=barpsi_x G_x^-1,
for EVERY anchored edge/site, not just two convenient links. All G are original compact Spin4. All nonzero old test fermions are at time0, so b1,b2,u,v values are unchanged; time1 zero fields remainzero. Every incident spatial/temporal link at b still changes by this formula.

Closed local action invariance is exact. Each original coframe bracket transforms at its base by the Spin4 vector rotation induced by G_x; its proper SO4 determinant preserves S4's epsilon. The closed holonomy based at x transforms as G_x H_x G_x^-1; gamma5 commutes with Spin4 and the vector coframe/gamma transformations cancel in the trace, preserving full S2. All world/internal sums and scalar worldframes/literal metrics remain; no integration or gauge-volume division is involved. Thus G^* S4=S4 and G^* S2_closed=S2_closed as actual polynomial identities.

The reflected action is invariant as well. Define Ghat_x=R G_(rho0 x) R. On the full original generator algebra direct N16 substitution gives theta G^*=Ghat^* theta. On psi, conjugate(G_x) R^T barpsi_rho^T equals R^T(Ghat_rho^-1)^T barpsi_rho^T because G is unitary and Ghat_rho=R G_x R; the barred rule follows similarly. On scalar links, sigma(G·U)=Ghat·sigma(U): spatial Pin conjugation has the matching endpoint matrices, and temporal inversion reverses those matrices with rho(x+0)=rho(x)-0. Each temporal anchor keeps its own inverse. Exterior reversal extends this identity. Since Ghat ranges over the same compact site gauge group, invariance of S implies invariance of thetaS. Both complete original/reflected closed coefficient functionals are therefore unchanged by this fixed test transformation, without assuming thetaS=S.

The links genuinely do not commute in the SAME actual plaquette. Its old plane(0,1) factors at a were A=I,B=H,C=I,D=I. They become
 A_G=U_a0^G=K,
 B_G=U_b1^G=H K^-1=diag(I2,iτ2), C_G=I,D_G=I.
Hence [A_G,B_G]=diag(0,-2iτ3) is NONZERO, while D_G† C_G† B_G A_G=(H K^-1)K=H. The opposite multiplication A_G B_G=K H K^-1 differs from B_G A_G=H. Every other incident anchor has already been assigned by the full G formula, so no change elsewhere in the action/reflection is omitted. This is an admissible original test configuration, not a new ensemble or printed/closed equivalence. The printed word need not be locally gauge-invariant and is not used for this inherited CLOSED control.

Gauge invariance of S and thetaS proves (14) on this FULL gauge-transformed configuration in the SAME ordered test generators. Now apply B to every field/link as in(3). The distinguished link commutator becomes B diag(0,-2iτ3) B^-1, still nonzero. Thus(15), with conjugated reflected coupling, holds at a genuinely noncommuting-link N configuration. Relabel all sites/anchors by pi for C; the same nonzero commutator and both coefficients transport. No new coefficient evaluation or partial roster replaces this full gauge/field proof.

The S4 sign is not vacuous. Accepted nonzero-normalization result proves its pure-cosmological full saturation coefficient c16>=3^16/2^47>0 on the same128-generator original carrier, with original factorial/orientation and all classes accounted for. Since c16 is proportional to ell(S4_P,total^16), the ACTUAL polynomial S4_P,total is nonzero. Equation(6) proves a MINUS for that nonzero polynomial by each internal epsilon term, not by reading an evenpower sign from c16. The positive evenpower is used ONLY to exclude a zero polynomial; it does not itself determine the minus. Thus a proposed PLUS would contradict the actual nonzero polynomial together with the explicit epsilon calculation. No new scalar coefficient is invented or evaluated.

## 9. Composition to source_C time3 and consumption of metric controls

Only now apply the accepted odd permutation N→C, pi=(3,0,1,2),Ppi_(pi(mu),mu)=1, with xC=Ppi xP. The FULL combined configuration map is
 psiC(xC)=B psiP(xP),barpsiC(xC)=barpsiP(xP)B^-1,
 U_C(xC,pi(mu))=B U_P(xP,mu)B^-1,
 T_C,pi(mu),pi(A)=h_A T_P,mu,A.                            (16)
The permutation fixes spinor/chiral components and every anchored word order. Composition gives the coupling family(1), S4_C at(16)=-S4_P and S2_C^w at(16)=-S2_P^w. This is a DIFFERENT map from identical-index uncut P=C; both identities may hold with different target inputs, cuts and tests.

Full metric/frame/current profiles are
 Q_C(xC)=Ppi Q_P(xP) Ppi^T,
 boldJ_C(xC)=Ppi boldJ_P(xP) Ppi^T,
 A_C(xC,j)=Ppi A_P(xP,j) Ppi^T, chi_C(xC)=chi_P(xP).        (17)
Linear sources/auxiliaries carry both pi and h_A. All repeated/mixed derivatives, frameacceleration and parameter chain terms transport. Permutation of degree8 siteblocks is even; Haar and both inverse anchors merely relabel. The worldrelations rho_C3 Ppi=Ppi rho_P0, Ew_C3=Ppi Ew_P0 Ppi^T hold and RN=RC=gammaC3 aftertheBstep, so thetaC F_total=F_total thetaP on actual generators/functions. Compose the four typed maps of§6 with the four reviewed N0/C3 cut maps to obtain full original/reflected C3 pair-kernel identities. Same-profile closure is still not assumed: full reflected A/J profiles transport under(17) and their actual C2 jets.

The actual pushed EHC controls in C coupling coordinates are consequently
 [b1b2uv](g2_C S2_C at combinedimage)=-2i g2_C,
 [b1b2uv]thetaC(g2_C S2_C at combinedimage)=+2i g2_C.       (18)
For complex inputs they remain +2i g2_P and -2i conjugate(g2_P) at g2_C=-g2_P; on the inherited REAL-coupling domain the conjugates may be omitted. Equation(18) holds on both the old commuting sign image and the complete noncommuting gauge image of§8a. An implementation must state which coupling/input testcoordinates it uses; calling both expressions “2i g2” would lose the required sign discriminator.

For the original metric-domain certificate use EXACT pulledback observables. DirectN has Q_N=Q_P atsameworldsites, so F60_N/G52_N are the same metricpolynomials and spatialdirectionsi=1,2,3. In C, sites map xC=Ppi xP, time0 maps toaxis3, and each spatialdirection i maps topi(i)∈{0,1,2}; matchingedges/roots and powers3/1/4 mapindividually. The compact geometric reflection and both cuts are the proved ones, not an unrelated same-coordinate timeaxis. Therefore with mu=1125/4,
 rawP_N(F,F)=rawP_C(F_C,F_C)=0,
 rawP_N(F,G)=rawP_N(G,F)=(3645/2)mu^6 g2_N^4,
 rawP_C(F_C,G_C)=rawP_C(G_C,F_C)=(3645/2)mu^6 g2_C^4.      (19)
These are consequences of the FULL map proven above plus accepted P identities, not evidence offered in place of that map. They hold at ALL finite real targetcouplings because(1) is bijective on that family. F/G remain actual nonzero functions and isotropic-not-radical; no deletion of the failed metric domain is inferred.

The separate temporal contact Q_P,(0,x),00 Q_P,(0,y),00 maps to the N sameindices and C indices33 at their mapped sites. Its two individual first rawjets remainzero, mixed raw value(6075/2)mu^6 unchanged, with EACH independent temporal anchor retained. This is a PURE Euclidean source relabeling: no -i or -1 Lorentzsource derivative phases occur. For normalized versions require the corresponding mapped nonzeroZ; use(13), not a frozen denominator. At the accepted P witness, the combined targetisC(-2^1717,-1,J0,A=I), not C(2^1717,1). Family-wide certificates allow this mappedmathematicalpoint without choosing a physicalworkingpoint.

## 10. Acceptance and remaining obligations

If independently accepted, this result discharges the specific additional coordinate/cut/source interoperability BUILD and makes explicit WHICH Task3 targetinputs/observableimages the original physical metric/kernel certificate covers. ROOT must still verify its actual numerical implementation against that map, both wordlabels, domains and unsquaredcontrols; no numerical Task3 execution or coefficientvalue is authorized here. Task1's uncut source_C builder and independent temporal_axis remain unchanged.

This result does not repair the already failed metric geometric positivity prescription; it correctly transports its bounded failure and temporal controls. It supplies no positive physical domain/product/adjoint/polarization/CAR, physical causaltransfer, Lorentzcycleequality/normalization, matter/scale, controlledlimit, B3/N4/tensor/light/transport or publication closure. The separate positive spatialmarginal construction remains research; ordinaryEq4–11/numerical/main/runtime remain ROOT-owned. No gate, resource or slot claimed.

Evidence boundary: complete manual Clifford/Pauli/field/measure/anti-linearity/cut/source derivation with inherited actual unsquaredcoefficients and nonzeroS4 input. Independent ACTUAL math+source reviews, lead full-read/fresh checks, exact checkpoint and ROOT personal intake remain required; this candidate alone does not release consumption.
