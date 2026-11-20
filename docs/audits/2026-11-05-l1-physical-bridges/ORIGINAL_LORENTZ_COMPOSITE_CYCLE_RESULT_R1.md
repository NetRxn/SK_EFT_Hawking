# Original composite Wick map and gauge-reduced bare Lorentz cycle

Status: ACTUAL MANUAL RESULT CANDIDATE, awaiting separate independent mathematical and original-source result reviews. Not an accepted physical continuation. Task l1-lorentzian-boundary-continuation-source-research-r1; owner Executor01a1ac65; publication ROOT01a13f67 owns ordinary L1/runtime/integration. No scientific executable, numerical experiment, Lean or backend was used.

## 1. Scope, exact inputs and proposition

Reuse unchanged accepted ORIGINAL_KINETIC_NORMALIZATION_CORRESPONDENCE, ORIGINAL_ONE_SLICE_SOURCE_KERNEL, ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT, ORIGINAL_METRIC_SEWING_DOMAIN_CONSTRUCTION and ORIGINAL_NONZERO_NORMALIZATION_CONSTRUCTION in docs/audits/2026-11-05-l1-physical-bridges. Carry the whole Q4/Nt2 regulator:16 vertices,128 independent complex odd coordinates,64 independently anchored links, normalized compact Spin4 Haar, quarter coframe, determinant plus full EHC, closed D†C†BA word, exp(+S), both interfaces, literal J once per mu<=nu, and every prescribed C2 world-frame. No microscopic replacement is adopted.

Held primary sources: Diakonov1109.0091v1 V14/16/17/20–28; Vergeles2506.00036v2 II2.6/2.16–26, III3.9, IV4.1–10, VI6.1. Source bodies were directly read through held extracts; PDFs remain in Lit-Search. Printed Diakonov17 ABC†D† is NOT identified with the accepted carrying D†C†BA. The prior closed replay explicitly gives unequal finite coefficients, so this is a labeled source-ordering discrepancy, not a cyclic rewrite. The theorem below is for the accepted carrying closed action. It does not resolve that original-source discrepancy.

Prospective brief b392bae0fd4f7001eb75e8df13d5f379879e2358f13bf99d7629a9719ec642d6 received separate independent math/source ACCEPT for this bounded manual attempt. Lead read both complete reports and checked BOTH SAME packets fresh before construction. Their approval was not theorem acceptance.

Main proposed result: the actual original composite has an explicit formal Wick/source map, with a phase different from the source's independent tetrad. For any parameter values at which the fully Berezin-integrated continued link polynomial is nonzero, its bare Lorentz real Haar prescription is NOT absolutely integrable even on a complete generic gauge slice. This includes a nonempty real-coupling scope established from the accepted compact nonzero point. The failure is in residual loop integrations, after all continuous vertex gauge directions are removed. It excludes neither distributions nor other cycles nor boundary-weighted amplitudes. No positive boundary domain, physical CAR or full Lorentzian reconstruction follows.

## 2. Explicit internal/spinor convention and composite continuation

Original chiral gamma matrices have upper-right blocks q_C=(-i tau1,-i tau2,-i tau3,I2), C=0,1,2,3; lower-left q_C†, and gamma5=diag(I2,-I2)=gamma0 gamma1 gamma2 gamma3. The latter follows directly from tau1 tau2=i tau3. Let q0=-i tau1 and S=diag(q0†,I2). Then det S=1, S gamma0 S^-1=[[0,I],[I,0]], and S commutes with gamma5.

Use source Euclidean labels 1,2,3,4 and define
 gamma'_1=S gamma1 S^-1, gamma'_2=S gamma2 S^-1,
 gamma'_3=-S gamma3 S^-1, gamma'_4=S gamma0 S^-1.
The signed permutation (1,2,-3,0) has determinant +1: the cyclic shift has sign -1 and the single minus cancels it. Therefore gamma'_1 gamma'_2 gamma'_3 gamma'_4=gamma5, with no chirality reversal. Transform vector components by the same proper signed permutation and spinors by Psi_E=S psi, barPsi_E=barpsi S^-1; transform each link U'=S U S^-1. The named time/world axis is unchanged; only the internal basis was aligned. This is not a new geometric reflection.

Set Gamma^0=gamma'_4 and Gamma^alpha=-i gamma'_alpha. Then {Gamma^a,Gamma^b}=2 eta^ab, eta=diag(1,-1,-1,-1), and i Gamma0 Gamma1 Gamma2 Gamma3=gamma5. All these identities are matrix multiplication identities, not additional physical assumptions.

Original U_xy transports x to y under U_xy->V_y U_xy V_x^-1. The source Omega_xy transports y to x; hence Omega_xy=(U'_xy)^-1, and Omega_yx=U'_xy. In all complexified formulas use inverse; dagger agrees with inverse only on the compact cycle. Write the original edge bracket
 A_xy^C=barPsi_E,x gamma'_C Omega_xy Psi_E,y
        -barPsi_E,y Omega_yx gamma'_C Psi_E,x.
For z=x-mu,y=x+mu, the original coframe is exactly T'_xmu^C=(A_xy^C-A_xz^C)/4. The backward bracket uses the independently anchored backward link, even when Nt2 identifies y,z as vertices.

Source Theta_E,xy^C=(i/2) A_xy^C. Therefore
 T'_xmu^C=(Theta_E,xy^C-Theta_E,xz^C)/(2i).                 (1)
This is the necessary extra phase relative to an independent tetrad.

Continue the complex link variables to the Lorentz real form and set barPsi_E=chi Gamma0, where chi is the independent row Grassmann coordinate interpreted only formally as Psi_M†. Write barPsi_M=chi Gamma0, Psi_M=Psi_E. Source2.18/2.20 then gives Theta_E^4=Theta_M^0, Theta_E^alpha=i Theta_M^alpha. Define the actual composite
 E_xmu^a=(Theta_M,xy^a-Theta_M,xz^a)/2.
Equation(1) gives
 T'_xmu^4=-i E_xmu^0,    T'_xmu^alpha=E_xmu^alpha.        (2)
The source's formal dagger makes Theta_M and E_M real in its Grassmann anti-involution. This is not a represented Hilbert adjoint. All four original hopping terms, their quarter and gamma/link placements have been retained.

The finite odd change of variables has determinant one: det S=det S^-1=1 and det Gamma0=1 (eigenvalues +1,+1,-1,-1). Consequently its inverse Berezin Jacobian is also one, separately at each site, with inherited ordering transported rather than reordered. No extra phase is hidden in top extraction. Independent bars and psis remain independent complex generators; no Majorana reduction occurs.

## 3. Metric, full action and literal source phases

Apply exactly the same prescribed world-frame A_x(j) on the world index, defining Ebar_mu^a=sum_nu A_mu,nu E_nu^a. It commutes with the constant internal map(2). No analytic extension of a merely C2 j-family is assumed. Put G_mu,nu=eta_ab Ebar_mu^a Ebar_nu^b. Since even bilinears commute,
 Q_E,mu,nu=sum_C Y_mu^C Y_nu^C=-G_mu,nu.                 (3)
For determinant terms, the column order (E1,E2,E3,-iE0) has determinant i det(E0,E1,E2,E3). Thus the original cosmological density continues to i g1 det(Ebar), with exactly its original epsilon normalization.

Let H be the actual closed holonomy, with each old dagger analytically replaced by inverse, and define Gamma_a=eta_ab Gamma^b. The Clifford-contracted coframe becomes sum_C gamma'_C Y_mu^C=-i Gamma_a Ebar_mu^a. Hence the FULL original EHC contraction, with its original g2/4, becomes
 S_EHC,E -> -(g2/4) sum_(klmunuab) epsilon^(klmunu)
                 Tr(H_kl Gamma_a Gamma_b Gamma5) Ebar_mu^a Ebar_nu^b. (4)
No world/internal term was removed; the antisymmetric coframe/world contraction kills the symmetric Clifford part as in the accepted curvature reduction.

To check formal reality on the Lorentz real cycle, set B_ab=Gamma_[a Gamma_b] Gamma5. Then B_ab†=Gamma0 B_ab Gamma0, while H†=Gamma0 H^-1 Gamma0. Thus conjugate Tr(H B_ab)=Tr(H^-1 B_ab). Each diagonal2x2 chiral block of B_ab is traceless (for a=b the antisymmetrization is zero; for distinct a,b the Pauli/Clifford blocks have zero trace). Cayley-Hamilton for each SL2 block gives H_block^-1=Tr(H_block) I-H_block, hence Tr(H^-1 B_ab)=-Tr(H B_ab). The contracted F_ab is purely imaginary. This is a formal coefficient/odd-star statement, not operator Hermiticity.

For real g1,g2, real frame coefficients, and real K, define
 A_M = g1 det(Ebar)
      + i(g2/4) sum epsilon Tr(H Gamma_a Gamma_b Gamma5) Ebar_mu^a Ebar_nu^b
      + sum_(mu<=nu) K_mu,nu G_mu,nu.
Then A_M†=A_M formally and the actual continued exponent satisfies
 S_E(J_E,A) -> i A_M(K,A),       J_E=-i K.                (5)
This sign of the EHC part was DERIVED from the composite phase; it was not imported from the source's independent-tetrad action or changed to improve positivity. For complex frames/couplings, equations(2)–(5) remain algebraic with the stated coefficients, but formal reality is not asserted.

Equation(5) is an equality of finite Grassmann polynomial exponentials over complexified links. It is not an equality of their compact and noncompact integrals. Real K maps to imaginary J_E; it is NOT an identification of the two real source families. Literal-J dependence is entire because the Grassmann exponential terminates. The prescribed real C2 frame parameters remain real coefficient parameters.

## 4. Exact real cycle and finite-polynomial integrand

In this Weyl basis the complex group is G_C=SL2(C)xSL2(C). Compact Spin4 is SU2xSU2. The Lorentz real form is G_R={diag(g,(g†)^-1):g in SL2(C)}, with Gamma0 offdiagonal I. Indeed the pseudo-unitarity identity H† Gamma0 H=Gamma0 is exactly g_R=(g_L†)^-1. Its real dimension6 equals the complex dimension of G_C; its Lie algebra complexifies to sl2xsl2. Inversion preserves this real form, so using Omega=U^-1 changes no cycle specification. G_R is connected, noncompact and unimodular. It is isomorphic as a real Lie group to SL2(C).

The tested measure is the product of ordinary positive Haar measures on these real link groups, after the complete vertex gauge reduction specified below. It contains NO state/boundary damping, ghost determinant, constraint projection or additional quantum measure. It is a prospective bare prescription tested for integrability, not a new physical model.

For fixed finite couplings and source coefficients the action has positive odd degree. With128 odd generators exp S terminates. Each matrix inverse in SL2 is its polynomial adjugate. After Berezin extraction, the FULL uninserted weight P and every finite literal/frame source jet are regular functions on G_C^64, polynomial in matrix entries modulo determinant-one relations. This includes all determinant/EHC terms and all saturation cancellations; it is not a selected nonzero summand. Restriction to G_R gives a continuous real-analytic matrix-entry/conjugate-entry polynomial of finite degree. There is no residual ordinary scalar exp(i phase) damping in this purely Grassmann coefficient extraction. This statement does not exclude distributional definitions of polynomial amplitudes.

Gauge invariance of P follows from original closed-loop covariance, internal determinant/contraction invariance and the unit Berezin determinant of each complex Spin4 Dirac matrix. It extends from the compact real form to the complex group by holomorphic uniqueness; alternatively each displayed contraction is algebraically covariant. The same holds for full literal-J/frame source coefficients, since they couple gauge-invariant metrics and world frames do not act on internal gauge indices.

## 5. Elementary finite-translation-span obstruction

Lemma. Let G be a noncompact locally compact group with left Haar measure, and f a nonzero continuous complex function. If the span W of all left translates L_g f, with (L_g f)(x)=f(g^-1 x), is finite-dimensional, then f is not L1(G).

Proof. Suppose f is L1. Its translates and all of W are L1. The passage from continuous functions to Haar almost-everywhere classes is injective: a nonzero continuous function is bounded away from zero on a nonempty open set, of positive Haar measure. Thus the L1 norm is a genuine norm on W. Every L_g is an invertible linear isometry of this finite-dimensional normed space. Its isometry group is compact: matrices preserving a norm and their inverses are uniformly bounded, the preservation condition is closed, and any limit still preserves the norm and is injective, hence invertible. Average any positive Hermitian inner product over that compact group to obtain an invariant Hermitian form on W.

Point evaluation at identity is a bounded linear functional on finite-dimensional W. For each w, w(x)=(L_(x^-1)w)(e); invariance of the averaged norm gives a uniform bound on w(x). Thus each member of W is bounded as well as L1 and therefore has square modulus in L1. Choose an orthonormal basis w1,...,wd. Unitary action of L_g gives h(x)=sum_i |wi(x)|² invariant under every left translation, hence constant. Some wi is nonzero, so h is a positive constant. But its integral is finite by the previous sentence, while a noncompact locally compact group has infinite Haar measure. Contradiction. The last fact follows, for example, by choosing a relatively compact positive-measure identity neighborhood and constructing infinitely many disjoint translates unless the group is covered by finitely many translates of its compact closure. This proves the lemma.

For a restriction of a regular function on G_C to G_R, finite translate span follows directly from degree bounds. Left multiplication substitutes linear combinations of matrix entries in each chiral block; inverse entries are polynomial adjugates. The finite-dimensional space of restricted coordinate polynomials up to the fixed degree is invariant. Coefficient conjugates in the real-form expression do not spoil this: conjugate matrix multiplication is still linear in the spectator's entries/conjugates. Hence the lemma applies to each nonzero spectator section of the actual P or its jets.

## 6. Tree reduction and a COMPLETE generic conjugation slice

Choose any fixed maximal tree in the actual connected16-vertex/64-directed-anchor graph. It has15 edges; periodic parallel anchors remain distinct edges. Vertex gauge transformations at all vertices except a root set those15 links to identity uniquely, by recursion along the tree. Products/inverses give the new49 loop links. In Haar coordinates this change is triangular: each eliminated tree link supplies one gauge coordinate, and each remaining link is multiplied on left/right by already determined tree gauge elements. SL2(C) is unimodular, so both left/right multiplication preserve Haar. The odd vertex change has determinant one. Therefore local measure disintegration removes these15 vertex gauge factors and leaves the product Haar on49 loops. There remains simultaneous root conjugation by G=SL2(C); omitting it would only repeat the known gauge-volume issue.

For that remaining action, use two loop variables. Let
 D(lambda)=diag(lambda,lambda^-1), lambda!=0,+1,-1,
 M(a,d)=[[a,1],[ad-1,d]], ad-1!=0.
On a chosen local eigenvalue/square-root branch consider
 Phi(k,lambda,a,d)=(k D(lambda) k^-1, k M(a,d) k^-1).      (6)
It has equal source/target real dimensions12. Its differential is nonsingular. After conjugating k to identity, variation of the first matrix is [X,D]+D'(lambda)deltaLambda. The offdiagonal part determines the two complex offdiagonal entries of X because the eigenvalue gap is nonzero; the diagonal part determines deltaLambda. Its kernel has X=t diag(1,-1), deltaLambda=0. For the second matrix this remaining X changes its upper-right entry by2t, while variations deltaA,deltaD independently supply the two diagonal tangent entries; determinant one determines the remaining lower-left tangent. Thus a zero second variation forces t=deltaA=deltaD=0. The inverse-function theorem yields a real-analytic local coordinate chart.

Existence on an open dense pair set is explicit: diagonalize a distinct-eigenvalue first matrix, write the second as [[a,b],[c,d]], and require bc!=0. A diagonal conjugation normalizes b to1 using a local square root; determinant one then fixes c to ad-1. The remaining stabilizer is the center +/-I, and swapping eigenvalues is a finite Weyl ambiguity. Choose a local branch and chart so neither creates continuous directions or affects divergence. The excluded discriminant/offdiagonal loci are proper algebraic loci; no special physical sector was selected.

Here is the required measure statement, without a formal division by infinite gauge volume. Haar measure on a Lie group has a smooth positive density. Pulling product Haar of the first two loops back through the local diffeomorphism(6) gives r(k,s) dmu_G(k) ds, with s=(lambda,a,d) and ds ordinary six-real-dimensional coordinate volume. Product Haar is invariant under simultaneous conjugation because G is unimodular. In coordinates this conjugation acts by LEFT multiplication on k and leaves s fixed. Since dmu_G is left invariant, r(gk,s)=r(k,s) whenever both charts overlap. Infinitesimally the k-direction fields span its tangent space; thus r is independent of k on a connected local chart. Write it rho(s), strictly positive and smooth. This proves an actual local disintegration, not a guessed Faddeev-Popov constant.

For the other47 loops use h_j=k z_j k^-1. At fixed k, conjugation preserves Haar on every z_j. The combined coordinate change is block triangular (first-pair coordinates depend only on k,s; spectator changes may depend on k but not conversely). Therefore its full pullback measure is EXACTLY
 dmu_G(k) rho(s) ds product_(j=3..49) dmu_G(z_j).         (7)
There is no spectator-dependent Jacobian or damping. Taking the gauge-invariant integrand in this disintegration removes the root gauge coordinate k, leaving the well-defined local bare quotient measure rho(s) ds times47 independent spectator Haar factors. Finite branch multiplicities alter only a positive constant; no integral over an infinite orbit is divided out. Formula(7) is local in pair coordinates, with all spectator variables unrestricted. It does not claim a unique global quantum gauge fixing or incorporate ghosts/secondary constraints.

Unimodularity used above is elementary here: det_C Ad_g=1 on sl2(C) (for diagonal g the eigenvalues are1,t²,t^-2; conjugacy/density or connectedness extends it). Thus the real determinant is |det_C Ad_g|²=1, so conjugation preserves left Haar and left/right Haar agree.

## 7. Nonzero scope and residual-loop divergence

First fix parameters for which the ACTUAL continued P is nonzero as a regular function. After maximal-tree fixing it remains nonzero: gauge invariance identifies every configuration with its tree-fixed representative, by an invertible gauge change. Its restriction to G_R^49 is not identically zero. Proof of the uniqueness fact used here: near identity, complex exponential coordinates identify the real-form Lie algebra with a real-linear form whose complexification is the full complex Lie algebra. A holomorphic function vanishing on a real-open subset of that form has zero Taylor series by one-variable identity successively in a real basis. It vanishes near identity, and then on the connected complex group by analytic continuation. Translate coordinates if the real-open patch is elsewhere. Hence nonzero holomorphic P cannot vanish on the whole real form.

The generic pair set used in(6) is real-open dense. A nonzero continuous real-analytic P cannot vanish on that whole dense set: continuity alone would then imply zero everywhere. Consequently some generic pair/spectator configuration has P!=0. Gauge invariance conjugates it into a slice branch, so the slice function f(s,z3,...,z49) is nonzero at some point. Freeze one spectator, say z3, at that point. By continuity there is a positive-measure open product neighborhood O of (s,z4,...,z49) on which f(s,z3_fixed,z4,...,z49)!=0. It can be chosen relatively compact in s and the other spectators, with rho bounded below by a positive constant. For every point of O the function of z3 on the ENTIRE G has nonzero finite translation span. Section5 gives
 integral_G |f(s,z3,...,z49)| dmu_G(z3)=infinity.
Tonelli applied to the nonnegative absolute value with measure(7) now makes the gauge-reduced absolute integral infinite. This is residual-loop divergence AFTER all continuous gauge directions were removed. If P does not depend on z3, a nonzero constant section gives the same conclusion. Identically zero sections/jets are expressly excluded.

Nonempty original scope is not an assumed physical point. The accepted compact certificate proves Z>1 at g1=2^1717,g2=1,J=0,A=I. Hence its COMPLETE compact Berezin-integrated link polynomial is not identically zero; otherwise its compact Haar integral would vanish. The constant internal spinor/basis change and bar-variable map in Section2 are invertible determinant-one algebraic changes, with no coupling change at zero source. They preserve nonzeroness of that holomorphic polynomial. Thus at THESE SAME real numerical couplings and zero source the continued polynomial is nonzero, and the residual-loop absolute divergence theorem applies. The point remains the accepted mathematical witness, not a calibrated physical operating point or chosen state. Other parameters are covered exactly when their full polynomial is nonzero. No claim of divergence at all couplings, no nonzero mean, and no evaluation of pure EHC c0 or a14 is made.

The same theorem applies to any nonzero finite source-jet or inserted polynomial after all gauge invariance requirements are checked; it does not assert that every individual jet is nonzero. A gauge-noninvariant insertion cannot simply be treated as a scalar function on this quotient without its own gauge-fixing prescription.

## 8. Original reflection, both kernels and full source jets

The finite algebra map C just constructed transports the ORIGINAL anti-linear reflection rather than replacing it with Lorentz Dirac dagger. In the aligned internal labels the accepted law is theta_E T_mu^C=epsilon_mu r_C T_(rho x),mu^C, with r4=+1,rAlpha=-1. Put d4=-i,dAlpha=1 in T'_C=d_C E^a and define theta_M=C theta_E C^-1 on the complexified polynomial algebra. Anti-linearity gives
 theta_M E_mu^a=epsilon_mu r_C(d_C/conjugate d_C) E_(rho x),mu^a
               =-epsilon_mu E_(rho x),mu^a.              (8)
Therefore the induced G law is theta_M G_mu,nu=epsilon_mu epsilon_nu G_(rho x),mu,nu. Equation(8) is the transported geometric reflection, not the source's formal local dagger E†=E and not a new positive adjoint. The original nonzero EHC reflection defect survives the injective algebra map; no theta S=S repair occurs.

Keep the accepted L and Ltheta=Rminus L^t Rplus^-1, and their actual source/curvature placements. At the unintegrated polynomial level C transports each integrand, both independently anchored temporal-link collections, the old/new Grassmann cuts and the existing Berezin Jacobian. Finite Berezin operations commute with C under the determinant-one change. But C is not an already supplied operator on a positive boundary Hilbert space, nor does it transform compact Haar integration into Lorentz Haar. The theorem above prevents defining the tested closed normalized Lorentz functional by an ordinary absolute Haar integral; it therefore cannot supply the required four physical boundary intertwiners or their differentiated sewing. Open kernels with special boundary factors could behave differently and have NOT been ruled out. Neither original kernel orientation has been discarded or silently equated to a spectral exponential.

For literal complex source transport on the compact side, Z_E(-iK,j) is well-defined near the accepted nonzero point and retains its full original nonzero denominator neighborhood. Each literal derivative supplies -i: partial_Ka=-i partial_Ja, partial_KaKb=-partial_JaJb, and partial_Ka jBeta=-i partial_Ja jBeta. Pure j derivatives retain BOTH A_jAlphaBeta and Hessian/product terms of the prescribed C2 family; no holomorphic j continuation is used. Source-dependent insertions/maps acquire their full first/mixed-second product-rule derivatives. Original action/coframe placements, exp(D) seam defects, all four pair-kernel derivative placements and overlap terms remain exactly as in the accepted kernel/source results, transported coefficientwise rather than dropped.

For any legitimate nonzero compact denominator, a mixed normalized derivative of N/Z remains
 N_ab/Z -(N_a Z_b+N_b Z_a+N Z_ab)/Z² +2 N Z_a Z_b/Z³,
with the above literal chain factors and all source/frame derivatives in N and Z. The separate accepted temporal contact transforms only as a complex source-jet identity of the compact functional; it is NOT reinterpreted as a convergent Lorentz expectation. The bare Lorentz prescription has no such ordinary Z, so no normalized Lorentz quotient/contact identity is asserted. In particular there is no freezing or dropping of denominator derivatives to hide a convergence failure.

## 9. Readiness disposition and remaining physical construction

The proposed manual result supplies the source-specific composite map and an exact failure of one concrete bare real-cycle ingredient beyond gauge volume. It does NOT supply the missing positive physical represented domain/product/adjoint/polarization. Formal real A_M, algebraic theta_M and actual nonzero compact Z do not create a Lorentzian Hilbert space, a contour deformation theorem or unitary transfer. The source's assumed ONB, matrix-element domain and spectral exponential remain separate hypotheses; Junker–Klauder projection cannot manufacture original CAR/adjoint input.

A next viable continuation would have to supply an original-grounded complex/distributional cycle or boundary-state measure AND show its correspondence to BOTH compact kernels, periodic sewing, constraints, full source family and C2 maps, including all denominator/overlap derivatives. Choosing arbitrary damping to defeat this polynomial Haar result does not discharge that correspondence. The result leaves such constructions and controlled Euclidean reconstruction OPEN; it is not a forced binary or a global no-go. No new physical premise is proposed for operator adoption here.

Unchanged obligations include physical metric/source maps30–31, matter and absolute scale, actual adjoint/polarization/secondary consistency, nontrivial calibrated state or controlled limit, B3/N4 and tensor/light/transport/publication criteria. Accepted metric F60/G52 and separate temporal controls are retained; a14 and K/K_R are not reevaluated. Ordinary Eq4–11, numerical backfill and publication/main gates remain ROOT-owned. This candidate requests no Lean slot or resource and adds no harness mechanism.

Verification boundary: complete manual algebra/measure argument above; no evaluator, numerical result, Lean proof, build, source implementation or new publication gate asserted. Independent ACTUAL math and source reviews, lead full-read/fresh checks, evidence checkpoint and ROOT personal intake remain required for acceptance.
