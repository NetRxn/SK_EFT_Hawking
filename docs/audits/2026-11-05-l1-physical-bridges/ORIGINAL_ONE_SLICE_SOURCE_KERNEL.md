# Original one-slice transfer, temporal defects and full C2 source kernels

Manual actual construction submitted for independent mathematical and original-source result review. Constructed under ROOT's explicit commission and the exact prospectively dual-approved brief 52081b8bd19b31865982e29bf6ce36fa8aa0747443b71a005104e19ad32c8cd1 (11264 bytes). Lead read both full APPROVE reports and freshly checked both SAME packets before construction. The rejected source-kick physical candidate remains rejected. No scientific evaluator/CAS/exterior/Haar/matrix/Gram script, Lean, build/test, slot/controller/process/dependency/harness action occurred.

This derives a genuinely reduced single-slice AUXILIARY transfer for an explicitly stated source subfamily, and the exact defects and pair-carrier jets needed for the FULL source contract. It does not derive a positive physical product/adjoint/domain, physical CAR, causal evolution, continuum limit, matter or absolute scale.

## 1. Original action and all temporal anchors

Reuse the exact original N16 contract: 16 periodic sites, 128 independent odd generators, 64 independent anchored Spin(4) links, original quarter coframe, complete determinant/EHC terms, closed plaquette Ddag Cdag B A, exp(+S), inherited bars-before-psis/top orientation. Off-diagonal literal J occurs once. A_x(j) is ANY prescribed C2 world-frame family with A_x(0)=I; links and measure do not vary with sources. No microscopic term, boundary, measure, sector, coupling or matter reference is changed.

Before periodic sewing let a,b,c be independent slices. X_t contains 24 spatial links and 64 odd generators; v_a,v_b contain the eight temporal links between a,b and b,c respectively. Write spatial coframes E_i^A=T_(b,r),i^A for i=1,2,3 at a fixed middle site (b,r). These depend only on X_b. The exact temporal coframe is R^A=R_-^A+R_+^A, where

 R_+^A=(barpsi_b gamma_A v_b† psi_c-barpsi_c v_b gamma_A psi_b)/4,
 R_-^A=(-barpsi_b gamma_A v_a psi_a+barpsi_a v_a† gamma_A psi_b)/4.       (1)

The spatial site r on the temporal neighbors is the same r. Do not impose c=a until periodization, and never identify v_a with v_b or its inverse. At Nt2 the neighboring odd coordinates coincide as prescribed, while both anchored links remain independent.

For all ordered world/internal indices, the original local density is

 s=g1 epsilon_(A0 A1 A2 A3) product_(rho=0..3)Y_rho^A_rho
  +(g2/4) sum_(k,l,mu,nu,C,D)epsilon^(k l mu nu) F_kl^CD Y_mu^C Y_nu^D
  +sum_(mu<=nu) J_mu,nu sum_A Y_mu^A Y_nu^A,
 Y_mu^A=A_mu,0 R^A+sum_i A_mu,i E_i^A,
 F_kl^CD=Tr(H_kl gamma_C gamma_D gamma5), H_kl=D†C†BA.                 (2)

Here A is the world-frame matrix; the four plaquette factors in H have their inherited distinct link labels. F with both k,l spatial depends only on X_b. F with exactly one temporal world index can depend on X_c's spatial links and v_b, besides X_b; it never depends on X_a or v_a. Both orientations of every plaquette stay in the sums. No assumption that the individual F tensor is internally antisymmetric is needed below.

## 2. Full temporal polynomial, including general frames

Define the symmetric literal-source matrix Jbold by Jbold_mu,mu=J_mu,mu and Jbold_mu,nu=J_mu,nu/2 for mu<nu, symmetrically. Set

 H=A^T Jbold A.                                                     (3)

Then the metric source is exactly sum_(m,n)H_mn sum_A T_m^A T_n^A with m,n=0..3. In particular its temporal coefficient is H00 R.R+2 sum_i H0i R.E_i. The half in Jbold is essential to once-counted off-diagonal J.

Put C=C_E+C_J and B=B_cos+B_E+B_J, where

 C_E=(g2/4)sum_(k,l,mu,nu,C,D,i,j spatial)
                  epsilon^(k l mu nu) F_kl^CD A_mu,i A_nu,j E_i^C E_j^D,
 C_J=sum_(i,j spatial)H_ij E_i.E_j,
 (B_cos)_E=g1 det(A)sum_(A1,A2,A3)epsilon_(E A1 A2 A3)E_1^A1 E_2^A2 E_3^A3,
 (B_E)_E=(g2/4)sum_(k,l,mu,nu,C,D,i spatial)epsilon^(k l mu nu)F_kl^CD
       [A_mu,0 A_nu,i delta_(C,E) E_i^D
                         +A_mu,i A_nu,0 E_i^C delta_(D,E)],
 (B_J)_E=2sum_(i spatial)H0i E_i^E.                                (4)

All link/exterior expressions in (4) are ACTUAL original functions after coframe substitution. There are no independent physical tetrad background values. Expanding (2) gives the exact identity

                         s=C+B.R+H00 R.R.                          (5)

Proof of completeness: the internally alternating determinant of Y_0,..,Y_3 is det(A) times that of T_0,..,T_3, hence is linear in R and has no R-free term because only three spatial T directions remain. The EHC term's R^C R^D coefficient contains sum_mu,nu epsilon^(k l mu nu)A_mu,0 A_nu,0=0 for each k,l,C,D. Its R-free and linear terms are exactly C_E and B_E. This argument uses antisymmetry in world mu,nu, not a false separate identity F_CC=0. Expanding (3) gives C_J,B_J,H00. This accounts for every term and original quarter in (2).

Split B_E=B_E,sp+B_E,time by k,l both spatial versus exactly one temporal index. Define B_s=B_cos+B_E,sp+B_J and B_t=B_E,time. C may contain forward temporal plaquettes; B_s depends only on X_b and the prescribed base sources, while B_t can depend on X_c spatial links and v_b. Temporal-coframe linearity therefore does NOT by itself give pair separation.

## 3. Exact forward/backward pieces and the full defect

At each middle site define

 s^- = B_s.R_-+H00 R_-.R_-,
 s^+ = C+(B_s+B_t).R_++H00 R_+.R_+,
 D   = B_t.R_-+2H00 R_-.R_+.                                       (6)

All are even, of positive Grassmann degree. Equation (5) becomes EXACTLY s=s^-+s^++D. Sum (6) over all eight spatial bases in b and denote the corresponding slice functions by the same symbols. s^- is a function of (X_a,X_b,v_a) and sources at b; s^+ of (X_b,X_c,v_b) and sources at b. D retains both the backward/forward metric cross term and any forward-curvature coefficient multiplying backward spinors. No source or frame term has been omitted.

At A=I, B_t=0: when R comes from Y_0, the EHC epsilon forces k,l spatial. Also H00=J00. Consequently at j=0 with all J00=0 the defect vanishes. This includes the initially requested spatial-J diagnostic and, by the displayed algebra, also literal J0i directions. It is only a proved SUBFAMILY: the full independent source contract is retained in D, not replaced by it. More generally a sufficient coefficient condition is B_t=0,H00=0, while the exact factorization criterion in this chosen decomposition is the actual polynomial D=0. No independent necessary conditions on B_t,H00 are inferred by treating coframes as free realizable variables.

The full arbitrary-source weight has the exact finite factorization

                   exp(s)=exp(s^+)exp(s^-)exp(D).                   (7)

Commutativity here is of even exterior polynomials; it is not a physical operator product. Before sewing there are 192 odd generators, so positive-degree exponentials and their logarithms are finite. After sewing there are the original 128 generators. All link coefficients remain actual compact polynomial functions.

## 4. An actual full-source failure of bare local slice separation

Choose a single literal J_(b,r),00=t, j=0, other sources zero. Set all compact links to the admissible identity for this coefficient test. Retain only two upper-chirality barred components at (b,r), b1,b2, one lower-chirality unbarred component a1 at (a,r), and a second lower-chirality component c2 at (c,r). Set every other odd coordinate to zero. All spatial coframes vanish. The original zero-source determinant/EHC density vanishes on this restriction, independent of g1,g2. This is a polynomial test, not a chosen physical state/background/coupling point.

Use Diakonov's chiral gamma block q_A=(-i tau_1,-i tau_2,-i tau_3,I_2); the other chiral block is its conjugate. Each det(q_A)=1. The internal-axis relabeling used for time does not change this sum. On the restriction,

 R_-^A=-(b1(q_A)11+b2(q_A)21)a1/4,
 R_+^A= (b1(q_A)12+b2(q_A)22)c2/4.

Because a1 and c2 anticommute with b1,b2,

 2sum_A R_-^A R_+^A=(1/8)sum_A det(q_A)b1 b2 a1 c2
                               =(1/2)b1 b2 a1 c2.                 (8)

Each same-sign square vanishes on this restriction (it repeats a1 or c2). Thus the restricted density and weight are exactly t b1 b2 a1 c2/2 and 1+t b1 b2 a1 c2/2. The monomial is nonzero on the independent formal three-slice exterior algebra. In inherited slice order a1 b1 b2 c2 its sign is still positive, since a1 crosses two bars.

An additive density f(X_a,X_b,v_a)+g(X_b,X_c,v_b) cannot contain this mixed a/c monomial. Hence unrestricted literal temporal sources prevent THIS bare local pair-sum separation. Equivalently, a product of normalized unit-body even local weights of these two argument sets would have additive finite Grassmann logarithm and is impossible for nonzero t on this restriction. This witness is before periodization, where a and c must remain independent for a local time-evolution construction. It does not assert that all special Nt2 identifications preserve this particular monomial, nor exclude an integrated/transformed/enlarged-memory/dilated physical one-slice realization. It supplies the required explicit unsewn local construction breakdown, not a global no-go.

## 5. Actual single-slice transfer on the defect-free diagnostic

For j=0,J00=0, or another actually established D=0 family, let s_b^± carry the independent source profile at base b. Reorganize the periodic sum as nearest-neighbor edge densities

 E_(b->c)(X_b,X_c,v_b;s_b,s_c)
                       =s_b^+(X_b,X_c,v_b;s_b)+s_c^-(X_b,X_c,v_b;s_c).
                                                                        (9)

No endpoint source is identified with the other. Each source profile contributes to TWO adjacent edges, and (9) does not have the unsupported form of a common step depending on only one endpoint source.

Let G_sp=Spin(4)^24 with normalized Haar. The AUXILIARY single-slice space is

             H_1=L2(G_sp) tensor Lambda(C^64),                     (10)

with ordered exterior monomials orthonormal for coefficient bookkeeping only. It has 64 exterior coefficient occupations, not a derived physical 32-mode CAR representation. Define the actual integrated kernel and operator by

 k_(b->c)(X_c,X_b)=integral dv_b exp(E_(b->c)),
 (T_(b->c)f)(X_c)=integral dU_b^sp I_b[k_(b->c)(X_c,X_b)f(X_b)].      (11)

Keep output variables before input variables when extracting matrix coefficients; every reordering sign is the ordinary inherited Grassmann sign. dv_b is exactly the eight original temporal-anchor Haar factors for that edge. No temporal link is fixed or averaged separately from its full edge weight. Across the two edges all 16 temporal plus 48 spatial link factors appear once.

Each k is a finite exterior polynomial and a polynomial in actual compact-link matrix elements/conjugates at its two ends, with finite source coefficients. Haar integration preserves this finite polynomial span. Expanding separates finitely many output-only and input-only compact monomials; together with finitely many exterior matrix units this makes T finite rank and bounded on (10). No physical cutoff or spectrum is introduced. The same holds for its permitted source jets, uniformly on a compact source neighborhood where the prescribed C2 coefficients are bounded.

This is an exact reduction of the accepted pair transfer in the defect-free family, not merely a new formal trace with a fitted kernel. For pair boundary B=(X_a,X_b,v_a), define the bounded even maps

 (B_b Phi)(X_b)=integral dU_a^sp dv_a I_a[exp(s_b^-)Phi(X_a,X_b,v_a)],
 (A_b f)(X_b,X_c,v_b)=exp(s_b^+)f(X_b).                             (12)

Their norm bounds follow from compact Haar, a finite exterior multiplication bound and Cauchy–Schwarz. Then the original pair transfer is L_b=A_b B_b, while

                           T_(b->c)=B_c A_b.                       (13)

This algebraic factorization transports the actual kernel and source vertices. It is not a positive physical quotient, not an invertible similarity, and not the discarded compact-link preconstraint reduction.

## 6. Periodic closure, parity and metric insertions

For an even coefficient/Berezin kernel with N=64 ordered slice generators, coefficient complement signs obey epsilon(Ic,I)=(-1)^|I|epsilon(I,Ic), because N is even. Thus the original periodic closure is its supertrace, just as derived directly for the accepted pair carrier but now with the NEW single-slice N:

 Z(s0,s1)=Str_(H1)[T_(1->0) T_(0->1)],  Str T=Tr(Gamma T),
                  Gamma xi_I=(-1)^|I|xi_I.                        (14)

Proof directly from (11): integration over the repeated intermediate slice and its temporal anchor gives both edge weights; taking the diagonal and extracting the remaining slice top gives exp(s_0^-+s_0^++s_1^-+s_1^+). In the diagnostic D=0, this is exactly exp(S_original). Exchanging two 64-generator slice blocks has positive sign. Spatial links and both temporal anchors have their original measures. Alternatively (12)–(13) and even parity intertwining give the same supertrace by finite-rank cyclicity: T is finite rank, A/B bounded, so the relevant cyclic products are trace-class; no unjustified trace of an isolated shared-coordinate identity is taken.

Each s^± is separately gauge invariant under the actual endpoint Spin(4) transformations: R and coframe coefficients transform at the middle base, F transforms by conjugation there, all internal contractions are invariant. After integrating v_b the kernel is invariant under independent endpoint gauge groups, so T=Pi_out T Pi_in on the actual spatial-link/exterior representation. For the center transformation -I at ALL eight vertices of one slice, spatial links are unchanged and all 64 odd generators change sign, hence Gamma Pi=Pi. Thus in (14) one MAY also write ordinary Tr on the already derived invariant support. This is derived gauge support, not selection of a favorable physical parity sector or a changed fermion boundary. No positive adjoint, semigroup or thermal interpretation follows from the trace.

For any even bounded-coefficient slice tests G_0,F_1, exact insertion ordering is

 ell(G_0 F_1)=Str[M_G0 T_(1->0) M_F1 T_(0->1)].                     (15)

M is exterior multiplication, not a physical observable assignment. This follows directly from (11), including tests depending on the slice's spatial links. The accepted spatial geometric reflection maps F_0 to F_1, so with the original F60,G52 and mu=1125/4, (15) reproduces the EXACT accepted coefficients

 P(F60,F60)=0,
 P(F60,G52)=P(G52,F60)=(3645/2)mu^6 g2^4.                           (16)

These are carried by equality to the original functional; the original support/Haar proof is not replaced or recounted as a new calculation. In particular (14)–(15) do not imply T is self-adjoint in (10): that would require independent adjoint identities not supplied here. The existing geometric metric-pairing failure at real g2!=0 remains unchanged, and normalized claims require Z!=0. No physical powers are identified with the exterior words.

## 7. Full source carrier and exact C2 defect kernels

Return now to EVERY literal J and ANY prescribed C2 A(j). Equations (3)–(7) are full-source identities. The full pair operator is explicitly

 (L_b(s)Phi)(X_b,X_c,v_b)=integral dU_a^sp dv_a I_a
       [exp(s_b^++s_b^-) exp(D_b) Phi(X_a,X_b,v_a)].                (17)

This recovers the original accepted pair kernel exactly, now with its complete source obstruction resolved into explicit original coefficients. When D!=0, it is NOT replaced by A_b B_b. The sum of all edge E from (9), defined now using the full s^±, is the full density MINUS sum_b D_b. Accordingly the exact full periodic weight is product_edges exp(E_edge) times product_b exp(D_b), with the original three-slice meaning of each D before sewing. This preserves the whole source family, not just its diagnostic tangent plane.

Here are explicit first/mixed-second kernels at the actual zero-source base, where D0=0. For an even insertion polynomial V define the exact map

 (J_b[V]Phi)(X_b,X_c,v_b)=integral dU_a^sp dv_a I_a
                                [exp(s_b,0^++s_b,0^-) V Phi].      (18)

Let e_b=s_b^-+s_b^+. All e,D derivatives below are obtained from the explicit sums (3)–(6), with original coframes/links fixed. Then

 L_b,0=J_b[1],
 L_b,alpha=J_b[e_alpha+D_alpha],
 L_b,alphabeta=J_b[e_alpha e_beta+e_alphabeta
              +D_alpha e_beta+D_beta e_alpha+D_alpha D_beta+D_alphabeta]. (19)

In particular

 D_alpha=(B_t)_alpha.R_-+2(H00)_alpha R_-.R_+,
 D_alphabeta=(B_t)_alphabeta.R_-+2(H00)_alphabeta R_-.R_+.           (20)

The R,E_i in (1) are bare coframes, independent of J,j; every frame derivative is already in C,B,H. These are constructive finite polynomial coefficient kernels, not names for unknown derivatives of an unspecified action. For clarity, H_alpha=A_alpha^T Jbold A+A^T Jbold_alpha A+A^T Jbold A_alpha. H_alphabeta is the sum of the NINE ordered product-rule terms for (A^T,Jbold,A), including its three factor-mixed derivatives and six cross terms. Jbold is affine in literal J, so its second derivative vanishes, but the other mixed terms and both frame acceleration matrices remain. In (4), each A_mu,i A_nu,j has mixed jet A_alphabeta,mu,i A_nu,j+A_alpha,mu,i A_beta,nu,j+A_beta,mu,i A_alpha,nu,j+A_mu,i A_alphabeta,nu,j. det(A) has its actual polynomial first/mixed jets; no zero-acceleration frame path is imposed. Curvature/link matrices have zero J/j derivative under this prescribed contract.

The edge part of (19) is equivalently A_b,alpha B_b+A_b B_b,alpha, with all four product-rule terms at mixed order; the remaining displayed D terms are the exact correction. Thus source-dependent reduction-map contacts are visible rather than silently zero. This statement concerns algebraic A/B maps, not a derived physical I map. Frame directions can produce (B_t)_alpha.R_- with forward spatial-link dependence, even when the zero-source D vanishes. Literal temporal alpha=J_(b,r),00 gives

 e_alpha=(R_-^2+R_+^2) at that site,
 D_alpha=2R_-.R_+,
 e_alpha+D_alpha=Q_(b,r),00.                                     (21)

It therefore cannot be replaced by an edge-local square alone.

For the full two-move pair product K=L_1 L_0, all placements are

 K_alphabeta=L_1,alphabeta L_0+L_1,alpha L_0,beta
                    +L_1,beta L_0,alpha+L_1 L_0,alphabeta.         (22)

The first jet has both placements. Combining (18)–(22) with the original pair supertrace gives the exact full temporal/frame C2 functional. This remains well defined when defects at both centers overlap. Any attempt to use a two-edge insertion as a one-slice multiplication must instead prove that further reduction; none is asserted. Tests depending on sources require their own first/mixed derivatives. Normalized expectations use the full quotient rule (accepted kinetic record (25)), retaining denominator first/mixed jets. Ward/current identities and field/source normalization covariance are preserved because (17) is equality of the full original kernel, not an altered source.

## 8. Separate temporal control: where all square and cross pieces go

Let X=F60_0 F60_1 and alpha=J_(0,x),00, beta=J_(0,y),00 at the accepted exceptional spatial edge. From (19)–(22), the mixed numerator is exactly ell[X Q00_x Q00_y], including all temporal squares and backward/forward cross pieces of (21). After Nt2 sewing its Grassmann degree is 60+60+4+4=128. Hence only the unit term of the original action exponential survives, independently of g1,g2. No zero-source density or partition is being approximated.

F60 contains only spatial links. For a fixed vertical site, each R_- or R_+ is linear in its own independent temporal-link fundamental/conjugate matrix elements. A term containing the cross piece R_-.R_+ therefore has a Haar factor of first degree in each of the two distinct anchors at that site. There are no other temporal-link occurrences in this saturated numerator, including the temporal insertion at the OTHER site. Such a term integrates to zero. This eliminates all terms with a cross piece only AFTER the complete insertion has been retained.

The remaining two same-anchor squares at one site have identical Haar means: after sewing a=c, substitution v_a -> v_b† in (1) sends R_- to -R_+; Haar is inversion invariant. The accepted full temporal average is E Q00=K/2, while the cross mean vanishes, so EACH E(R_-^2)=E(R_+^2)=K/4. Here K is the original invariant temporal four-form (the accepted v_chi^T C v_opposite), not the two-step transfer operator. No different K is fitted.

There are therefore FOUR surviving square choices, one sign at each x,y. Each gives, using the accepted complete spatial Q^3 moments and chirality loop,

 mu^6 (45/4)^2 (96)/16=(6075/8)mu^6.

Their sum is the required original coefficient

 ell[X Q00_x Q00_y]=(6075/2)mu^6.                                 (23)

The accepted base and first numerator jets vanish; thus the actual normalized mixed jet is (6075/2)mu^6/Z on Z!=0. Denominator derivatives cancel only for these proved vanishing lower numerators. This control shows explicitly how the single-edge square insertions and full defect formula reproduce the temporal response. It does NOT detect the defect's nonzero cross term on this saturated test: that term Haar-vanishes here. The independent unsewn mixed monomial (8) supplies bare-factorization failure. These are different pieces of evidence.

## 9. What this constructs and what remains owed

New actual objects submitted: the full general-frame temporal coefficient sums (3)–(5); exact pair pieces/defect (6)–(7); admissible actual mixed-monomial bare-factorization failure (8); diagnostic single-slice finite-rank kernel (9)–(11); explicit algebraic A/B reduction (12)–(13), periodic/gauge/metric insertion identities (14)–(16); and the full-source defect/pair-carrier C2 kernels (17)–(22) with unchanged temporal control (23). Reduced diagnostic success has not been substituted for full-source acceptance: the latter is the exact defect-inclusive original pair representation and its documented reduction boundary.

The original geometric metric pairing still fails at its accepted scope. a14 and K/K_R module calculations remain uncomputed. No physical positive representation, product/adjoint/domain, secondary consistency classification/transport, common self-adjoint step, causal/unitary dynamics, canonical CAR normalization, controlled continuum/infrared limit, metric mean/signature, matter reference, cQ/cE/hbar/lattice-time calibration, B3/N4/tensor/light/transport or publication acceptance is obtained. The physical maps I_out,s L_s=T_phys,s I_in,s and all first/mixed source-map derivatives remain owed; the algebraic A/B maps do not supply them. No coupling point, norm, positive part, state sector, source restriction or added physical prescription is adopted to make the model physical.

Independent ACTUAL mathematics and original-source/physics reviews and ROOT personal intake are required. Prospective approval accepts none of these derived formulas. ROOT owns ordinary L1/Hermite/Gaussian/source formalization, roadmap, active authoritative build, integration/main and final operator disposition. No deferral or global reconstruction no-go follows. All scientific work here was manual; artifact/hash/continuity checks are not full-wave/native/publication gates. Original PDFs remain in Lit-Search, not this result or a future evidence archive.
