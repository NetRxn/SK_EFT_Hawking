# Numerical C / permuted Euclidean M_N / physical continuation L_P: interoperability corrected r2

Status: MANUAL INTEROPERABILITY NOTE for ROOT review, not a new physical reconstruction, reopened acceptance, or numerical execution. Owner Executor01a1ac65; parent publication ROOT01a13f67. Inputs are exact physical checkpoint e2e393b126bedd49ca114efc6ca8c8ae005e8876 and ROOT's /tmp/publication-original-coefficient-budget-r2.md, especially its section2 convention dictionary. This note compares declared mathematical conventions, not the unexecuted implementation. It does not certify that code has implemented the dictionary.

R1 custody: source review ACCEPTED but independent mathematical review required one definite matrix-identity correction. R1 and both reports remain frozen. R2 states the entrywise coincidence of the selected time matrices while preserving distinct world cuts/signatures/field maps; it also makes the four cut-space maps and defect-inclusive source boundary explicit. No accepted source/action convention is changed. R2 requires separate actual rechecks.

## 1. Three labels must remain distinct

P denotes the Euclidean carrying reference actually used in ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT section1/§4 and ORIGINAL_LORENTZ_COMPOSITE_CYCLE sections1–2: q=(-iτ1,-iτ2,-iτ3,I), gamma5=diag(+,+,-,-)=gammaP0 gammaP1 gammaP2 gammaP3, world time axis0, geometric reflection R_P=gammaP0. The accepted metric sewing certificate likewise fixes its time0 theta by reference to N16; its gamma realization must be carried with that reference, not inferred merely from the word “time-first.”

C denotes the numerical plan's canonical Euclidean code coordinates. Its displayed gamma matrices and gamma5 are exactly those of P at IDENTICAL numeric labels, so the unreflected coframes/actions agree at the same indexed fields, full profiles, word label and couplings. However C declares temporal/world axis3 and R_C=gammaC3. Therefore C and P agree as an uncut Euclidean polynomial convention while selecting DIFFERENT cuts/reflections. No permutation or coupling sign is needed for the identity comparison of their unreflected functions; their half spaces are not thereby identified.

M_N denotes ONLY the numerical plan's separately defined permuted EUCLIDEAN convention. Let pi=(3,0,1,2), with pi(mu) giving a C label from an M_N label, and define gammaM_N,A=gammaC,pi(A), gamma5M_N=gamma5C. This pi is odd, so the ordered M_N gamma product is -gamma5M_N. M_N time0 maps to C/P axis3, not P axis0. This is a legitimate declared gamma5 convention, not a Lorentz signature and not the ordered-product definition used by P.

L_P denotes ONLY the formal Lorentzian composite variables of the accepted physical continuation result. That result's letter M means L_P here. It retains the WORLD time axis P0 and changes the INTERNAL gamma basis by proper signed permutation (1,2,-3,0) plus determinant-one S. In particular Gamma_LP^0=S gammaP0 S^-1. In the chosen displayed bases this DOES coincide entrywise with gammaM_N,0=gammaC3=[[0,I],[I,0]]: the S alignment was chosen to produce that matrix. Equality of this one matrix does not identify the WORLD cuts, other gamma matrices/signature, full field maps or anti-linear real structures. Calling both “M” or both “time-first” does not supply those maps or identify their boundaries. The numerical plan adopts no Lorentzian prescription.

## 2. Exact Euclidean C ↔ M_N dictionary, including UNSQUARED action

Let Ppi be the 4x4 permutation matrix with (Ppi)_(pi(mu),mu)=1. At related lattice points xC=Ppi xN, with corresponding extents and boundary signs, define
 U_C(xC,pi(mu))=U_N(xN,mu),
 psi_C(xC)=psi_N(xN), barpsi_C(xC)=barpsi_N(xN).
The L/R blocks and spinor index order do not change. Both independent periodic anchors map individually. Then the original four-block quarter formula gives term by term
 T_C(xC,pi(mu),pi(A))=T_N(xN,mu,A).                      (1)
No noncommuting gamma/link factors are reordered.

For either fixed word label w=printed or closed, each anchor factor and inverse maps to the corresponding N factor in the SAME product order. Thus H_C,pi(k)pi(l)=H_N,kl entrywise in the related spinor representation, without converting ABC†D† into D†C†BA. In the EHC contraction the gamma and coframe entries in(1) transport directly. Only the WORLD epsilon acquires det pi=-1, since gamma5 is fixed. Therefore
 S2_C^w=-S2_N^w                                                   (2)
BEFORE squaring, Haar integration or Berezin extraction. For the cosmological density the odd world-row permutation and the odd internal epsilon permutation cancel, so
 S4_C=S4_N.                                                       (3)
Consequently the complete exponents agree at
 g1_C=g1_N,    g2_C=-g2_N.                                        (4)
This is the sign-discriminating comparison. An equality involving g2^4 alone cannot check(2) or(4). The numerical Task1 must test an actual unsquared EHC polynomial coefficient at noncommuting links and carry the literal g2/4; no selected action plane or diagonal trace can substitute.

With the same numeric labels the identity P=C for unreflected polynomials gives S2_P=S2_C=-S2_N under this SAME site/anchor/gamma substitution, and g2_P=g2_C=-g2_N. It does NOT turn N's time0 cut into P's time0 cut.

## 3. Full linear/metric/frame/current sources and normalized jets

For linear coframe source L_(mu,A), L_C(xC,pi(mu),pi(A))=L_N(xN,mu,A), with auxiliary h transforming identically; no physical source is identified with h. For literal metric sources use symmetric coefficient matrices boldJ with diagonal J_mu,mu and off-diagonal J_mu,nu/2. Then
 Q_C,pi(mu),pi(nu)=Q_N,mu,nu,
 boldJ_C(xC)=Ppi boldJ_N(xN) Ppi^T,
 A_C(xC,j)=Ppi A_N(xN,j) Ppi^T.                                 (5)
Independent off-diagonal source coordinates are relabeled and unordered pairs resorted; no additional factor2. Every first/repeated/mixed derivative of A, including acceleration A_ab, follows the SAME linear map. Parameter labels j can remain unchanged; a proposed reparametrization still needs its full first/second chain rule. General profiles are not assumed invariant under pi or under reflection. Original local phase chi is a scalar pullback chiC(xC)=chiN(xN); all current/action/metric jets follow substitution, not a new U1 coupling.

Berezin site permutation moves blocks of degree8, so each site-block interchange has sign +1. Spinor indices do not move. The plan's Theta_L Theta_R top equals all-four-bars then all-four-psis by four swaps. Thus no hidden odd orientation factor changes(2)–(5). Compact Haar is a probability product merely permuted among anchor variables; quaternion +/-i coordinate maps are independent sphere isometries and must be applied per link as the numerical plan states.

Let F be ANY legitimate unnormalized source/insertion coefficient of the complete fixed-word functional. With all inserted observables transported and with(4), the C↔N identity is a finite variable change of F. The same applies to its full first/mixed-second jets, and to normalized jets only where the corresponding original Z is nonzero. There is no new normalization certificate here. All insertion/action/measure/map derivatives and the mixed denominator terms remain; no literal-T parity filter is applied to metric/frame jets.

## 4. Reflections and BOTH kernel orientations: which cuts actually map

For a world axis a define rho_a(x)_a=1-x_a and other coordinates unchanged, and Ew_a=diag(epsilon_mu) with epsilon_a=-1 and other entries+1. The C ↔ N site permutation satisfies
 rho_C3 Ppi=Ppi rho_N0,    Ew_C3=Ppi Ew_N0 Ppi^T,
 R_C=gammaC3=gammaN0.                                           (6)
Original spinor bars/psis are unchanged by this permutation, so the transposed-index anti-linear field rules, independent temporal inverse anchors, and r=-s signs pull back exactly. This transports theta_N0 to theta_C3. It does NOT transport either to theta_P0, for which rho_P0 and R_P=gammaC0 are different.

Define Phi_b from N boundary functions to C-axis3 boundary functions by pulling back through the inverse of the above field/site map; define separate Phi_in, Phi_out and the opposite-cut versions when their domains differ. These are exact relabeling maps, not physical Hilbert intertwiners. Relabeling the actual unintegrated kernels and their finite Berezin/Haar cuts, retaining both anchors and all seam defects, gives
 L_C3(J_C,A_C;g1_C,g2_C)
    =Phi_out L_N0(J_N,A_N;g1_N,g2_N) Phi_in^-1,                  (7)
with(4)–(5), for the same fixed word and ACTUALLY DEFINED interface domains. The full unrestricted source family requires the accepted defect-inclusive PAIR kernel. A reduced one-slice evolution exists only on its proved defect-free diagnostic restriction or a separately proved reduction; equation(7) does not construct a full-source reduced one-slice evolution. All boundary coordinates are relabeled; no old-spatial constraint removes a coordinate by assumption. For the reflected kernel the corresponding relation is
 (L_C3)^theta_C3=Phi_out (L_N0)^theta_N0 Phi_in^-1,               (8)
where in/out refer to the ACTUAL reflected opposite cut spaces. Explicitly, use Phi_minus/Phi_plus on original input/output and Phi_prime_minus/Phi_prime_plus on reflected opposite input/output. Then L_C3=Phi_plus L_N0 Phi_minus^-1, R_C,minus Phi_minus=Phi_prime_plus R_N,minus, R_C,plus Phi_plus=Phi_prime_minus R_N,plus, and (L_C3)^theta=Phi_prime_plus (L_N0)^theta (Phi_prime_minus)^-1. This also transports R_minus L^t R_plus^-1 with the appropriate separate Phi on each cut, not a generic same-space similarity. Both original temporal interfaces and all four source-derivative placements/overlaps survive. These equations assert Euclidean coordinate transport, not a positive adjoint.

For the reflection profiles in each convention,
 A_circ,a(x)=Ew_a conjugate(A(rho_a x)) Ew_a,
 boldJ_circ,a(x)=Ew_a conjugate(boldJ(rho_a x)) Ew_a.              (9)
Equations(5)–(6) commute with these full profile maps and their C2 jets. The P physical theorem instead uses(9) at a=0 in the P/C numeric labels. Comparing its L_P0 and (L_P0)^theta_P0 directly to the numerical C3 or N0 cut without an ADDITIONAL explicitly derived cut/spinor/field/action map is invalid. A four-torus coordinate symmetry or a basis rotation might support such another comparison, but this note has not constructed that additional reflection intertwiner or its coupling/chirality signs. A g2^4 metric check does not provide it.

In particular, numerical tests may use the accepted metric/control formulas only after all observable/site/direction/reflection/coupling labels have actually been transported to the declared target; the bare name metric_M is insufficient. If ROOT wishes to call its target N the original accepted certificate, it must retain the explicit pullback certificate rather than replace the accepted P0 theta by notation. This is a label/consumption requirement, not a claim a previously accepted scalar coefficient is false.

## 5. Separate P → L_P continuation and its signs

The physical result retains every WORLD P label and every anchor. Its INTERNAL signed permutation is proper, with S=diag(q0†,I), q0=-iτ1, and source Euclidean gammas
 gamma'_1=S gammaP1 S^-1, gamma'_2=S gammaP2 S^-1,
 gamma'_3=-S gammaP3 S^-1, gamma'_4=S gammaP0 S^-1.
The minus and cyclic internal shift give determinant+1, so gamma5 is preserved. This is NOT the odd WORLD/internal label pi of section2. Set Gamma0=gamma'_4, GammaAlpha=-i gamma'_Alpha. Original T'_4=-i E^0 and T'_Alpha=E^Alpha, with the actual forward-minus-backward source-composite normalization, imply
 Q_P=-G_LP,   S4_P -> i det(E),
 S2_P -> -(1/4)sum epsilon Tr(H Gamma_a Gamma_b Gamma5) E^a E^b. (10)
The last minus is from the TWO composite -i Clifford-contracted coframes, not a relabeling of epsilon. The original coupling numbers g1_P,g2_P are unchanged in this rewriting. Writing i A_LP gives the derived real formal EHC coefficient +i g2_P/4 times that trace. It is incorrect to apply the numerical g2_C=-g2_N rule a second time merely because this target is also named M in another note.

Full literal sources obey boldJ_P=-i boldK_LP and A retains its WORLD profile and real C2 parameter jets. For the transported original theta_P0,
 theta_LP E_mu^a=+epsilon_mu^(0) E_(rho0 x),mu^a,
 A_circ=Ew_0 conjugate(A∘rho0) Ew_0,
 boldK_circ=-Ew_0 conjugate(boldK∘rho0) Ew_0.                    (11)
The extra K minus is anti-linearity on i. Each K derivative is -i times the corresponding P literal-J derivative, two K derivatives give -1, and K/frame gives -i. No such complex phase appears in the PURE Euclidean C↔N permutation(5). The hypothetical alternative continuation aligned to C3 would be another labeled embedding L_C3, requiring its own full cut dictionary; it is not adopted by the numerical builder or this note.

If numerical output in N coordinates is used merely to evaluate the SAME compact unreflected P polynomial at complex sources, apply the Euclidean(4)–(5) conversion first, then the P complex-source substitution. That computes a compact coefficient identity. It does not provide Lorentz Haar integrability, a physical domain, positive CAR, or either physical boundary intertwiner. The accepted bare-cycle nonintegrability is restricted as before.

## 6. Interoperability disposition

Safe now: source/Lean/numerical builder of the canonical C unreflected polynomial; exact declared C↔N source/action transformation, unsquared sign test, and C3↔N0 cut transport; physical continuation in separate P/L_P labels. Keep printed/closed words separate throughout.

Not certified by this note: identification of the accepted P0 physical cut/reflection/metric witness with N0/C3 solely by calling them time-first; physical normalization, positive reconstruction, or integration-cycle equivalence. Preserve this as an explicit additional map requirement before sharing those kernels or metric interpretations. No source code, scientific evaluator, tests, Lean/backend/controller or notebook changes were made for this check. The note needs independent source/algebra review before becoming a shared scientific convention authority.
