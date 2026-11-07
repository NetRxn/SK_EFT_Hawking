# B4: a full graded-dual algebra, its actual source embedding and an all-degree free basis

Manual mathematical construction by the publication lead, r2 inverse-order repair after complete independent r1 review037edf65302a217db4cb05ed20173fd7a64a64a04a8252c338843701254c39c5. Complete corrected r2 has full independent mathematical acceptance by publication_b6_fdt_review, [full original independent review](reviews/B4_GLOBAL_MILNOR_BASIS.md), and lead acceptance e1d6a29083406f9124b5092dea2ce59d0316576a800c38f06ac63a376da92214 after214 exact input observations. Original r1 failure remains preserved. No native/API/build/source-installation or publication acceptance. This constructs the all-degree algebra and free witness that the preceding balanced-induction proof required. It does not postulate freeness, infer it from a finite Hilbert table, or change a noncommutative tensor to coinduction.

Primary convention: Milnor, The Steenrod Algebra and Its Dual, Annals of Mathematics 67(1),1958,150–171, university-hosted original https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Milnor-A.pdf . The lead personally inspected complete page images printed162,166,171, particularly Theorem3 and Appendix1. The p=2 polynomial generators printed zeta there are denoted xi below. The algebraic construction and freeness proof below are supplied explicitly; the primary presentation theorem supplies the conventional identification with the mod2 Steenrod algebra. This is not a new proof of its topological realization by all cohomology operations. Temporary read-only PDF/pixels are not canonical sourceholding admission or a new citation-verification date.

## 1. The full locally finite graded coalgebra, not a truncation

Work over k=F2. Let P=k[xi_1,xi_2,...] be the polynomial algebra on countably many generators; every monomial and polynomial has finite support. Set xi_0=1 and |xi_n|=2^n-1. Define the algebra homomorphism Delta:P→P tensor_k P by

 Delta(xi_n)=sum_(i=0)^n xi_(n-i)^(2^i) tensor xi_i.                 (1)

Define epsilon(xi_n)=0 for n>=1 and epsilon(1)=1. These formulas are definitions of finite polynomials, not supplied Hopf axioms. Delta preserves degrees because 2^i(2^(n-i)-1)+(2^i-1)=2^n-1. The counit identities hold on every generator and hence all polynomials. Coassociativity on a generator follows because both iterated coproducts equal

 sum_(i,j>=0,i+j<=n) xi_(n-i-j)^(2^(i+j))
                          tensor xi_j^(2^i) tensor xi_i.           (2)

For (Delta tensor1)Delta use characteristic2 Frobenius; for (1tensorDelta)Delta reindex the inner index by i and total by i+j. All sums are finite. Algebra-homomorphism uniqueness extends the equality from generators to P. Thus P is an actual connected graded commutative bialgebra. Each P_d is finite dimensional: only xi_i with 2^i-1<=d occur, each exponent is bounded by d/(2^i-1), and monomials of weighted degree d are finite in number.

Define its graded dual A=direct_sum_(d>=0) Hom_k(P_d,k), with convolution

 (ab)(p)=(a tensor b)(Delta p),      1_A=epsilon.                   (3)

A functional in A has finite graded support, rather than arbitrary completed-dual support. The finite homogeneous coproduct proves multiplication is well-defined and graded. Equation(2) proves associativity, and the counit identities prove the unit. Dualizing multiplication on P degreewise also gives the graded coproduct on A; finite type makes every homogeneous dual tensor legitimate. No infinite series is inserted into an element of A. This is the full Milnor graded-dual algebra, at all degrees.

## 2. The eight-dimensional quotient dual and the actual source basis

Let J=(xi_1^4,xi_2²,xi_3,xi_4,...) and D=P/J=k[x,y]/(x^4,y²), x=pi(xi_1), y=pi(xi_2). Its basis is x^r y^s for 0<=r<4,0<=s<2. The ideal is a coideal: Delta(xi_1^4) has only xi_1^4 tensor1 and1tensorxi_1^4; Delta(xi_2²) also has xi_1^4 tensorxi_1². For n>=3, in each middle term of (1) either xi_(n-i) has index>=3, or it is xi_2 to exponent>=2, or xi_1 to exponent>=4. Thus every term has a J factor, while the two end terms also do. Epsilon kills J. Therefore pi is an actual surjective graded bialgebra map and D inherits

 Delta_D(x)=x tensor1+1tensorx,
 Delta_D(y)=y tensor1+x²tensorx+1tensory.                            (4)

Let B0=D^vee with basis beta_(r,s) dual to these eight monomials. The dual pi^vee:B0→A is an injective graded unital algebra map, since pi is a surjective coalgebra map. For clarity, B0 is not identified with the pinned source merely by matching dimensions or names.

The full product formula in B0, with binomial coefficients in F2 and any out-of-range beta omitted, is:
- beta_(r,0) beta_(u,0) has beta_(r+u,0) coefficient binom(r+u,u) when r+u<=3; it ALSO has beta_(r+u-3,1) coefficient binom(r+u-3,u-1) if r>=2,u>=1 and0<=u-1<=r+u-3<=3.
- beta_(r,1) beta_(u,0), and beta_(r,0) beta_(u,1), are beta_(r+u,1) times binom(r+u,u) when r+u<=3.
- beta_(r,1) beta_(u,1)=0.
These follow by expanding Delta_D(x^i y^j), j=0 or1; in the extra first case the x²tensorx term forces i=r+u-3 and the right binomial index u-1. This derives all64 constants from (4).

Let B be the ACTUAL source A1sub, with basis e0,...,e7 given by Lmat. Define the linear map nu:B→B0 on that actual basis:

 e0→beta_(0,0), e1→beta_(1,0), e2→beta_(2,0),
 e3→beta_(3,0)+beta_(0,1), e4→beta_(0,1),
 e5→beta_(1,1), e6→beta_(2,1), e7→beta_(3,1).                       (5)

It is bijective: the only change from the eight ordinary monomial-dual coordinates is the invertible elementary replacement e3 by beta_(3,0)+beta_(0,1). The source multiplication constants, read from the eight COMPLETE Lmat definitions and their genuine expansion identity, are the following table; entry ij means e_i e_j, plus is in F2:

       0     1     2       3     4     5     6     7
 0     e0    e1    e2      e3    e4    e5    e6    e7
 1     e1    0     e3+e4   e5    e5    0     e7    0
 2     e2    e3    e5      0     e6    e7    0     0
 3     e3    0     e6      e7    e7    0     0     0
 4     e4    e5    e6      e7    0     0     0     0
 5     e5    0     e7      0     0     0     0     0
 6     e6    e7    0       0     0     0     0     0
 7     e7    0     0       0     0     0     0     0.                 (6)

Substituting (5) in the complete formula preceding it gives EXACTLY all rows(6). Nontrivial order controls: beta_(1,0)beta_(2,0)=beta_(3,0), while beta_(2,0)beta_(1,0)=beta_(3,0)+beta_(0,1); hence source e1e2=e3+e4 and e2e1=e3. Also (beta_(3,0)+beta_(0,1))²=beta_(3,1), its left product by beta_(2,0) is0, and its right product by beta_(2,0) is beta_(2,1), matching row2/3. Products above degree6 vanish and the displayed formula covers all remaining zero entries. Thus nu is an actual graded algebra isomorphism, with augmentation preserved since only e0 and beta00 survive epsilon. This is a finite MANUAL structure-constant proof, not a newly executed kernel or software verification.

Set iota=pi^vee nu:B→A. This is the required concrete injective unital augmented graded ring map from the CURRENT source B. In particular do NOT identify its e3 with beta_(3,0) alone; that would fail the carrying multiplication relation. The local research report's product labels are not used as premises.

## 3. Explicit coinvariants in every degree

Define the polynomial subalgebra

 C=k[xi_1^4,xi_2²,xi_3,xi_4,...] subset P.                           (7)

It is genuinely polynomial: distinct monomials in these displayed generators have distinct exponent vectors in P. Every monomial of P has a UNIQUE expression c xi_1^r xi_2^s with c a monomial of C,0<=r<4,0<=s<2, by Euclidean division of its first two exponents. Thus the standard multiplication map C tensor span{xi_1^r xi_2^s}→P is a graded vector-space isomorphism.

For the LEFT D-coaction rho=(pi tensor id)Delta:P→D tensor P,

 rho(c)=1tensorc for EVERY c in C.                                 (8)

For xi_1^4 and xi_2² this follows from (4) and Frobenius, since x^4=y²=0. For xi_n,n>=3, in a term of (1) with i<n the first projected factor vanishes: an index>=3 projects to0; index2 has exponent>=2; index1 has exponent>=4. The sole surviving term is i=n, namely1tensorxi_n. Multiplicativity of rho proves (8) for all C. This is an all-degree argument, not a verification through degree8 or a dimension-series inference.

## 4. The corrected eight lifts: a genuine comodule isomorphism

A naive choice of the eight lifts xi_1^r xi_2^s is NOT a D-comodule section at the top basis element. We construct the needed correction rather than assuming those lifts are stable. Define a graded linear j:D→P by

 j(x^r)=xi_1^r for0<=r<4,
 j(x^r y)=xi_1^r xi_2 for r=0,1,2,
 j(x³ y)=xi_1³xi_2+xi_1^6.                                       (9)

This is a linear section of pi, not an algebra section (indeed a polynomial algebra has no nonzero nilpotents mapping x's truncated relation this way). We prove

 rho j=(id_D tensor j)Delta_D.                                    (10)

For x^r the binomial expansion directly gives (10). For x^r y,r<=2 multiply rho(xi_1)^r by rho(xi_2) from(4): all right powers xi_1^(k+1) have exponent<=3 and all right xi_1^k xi_2 have k<=2, so the right factors are exactly their j-images. Terms with a left x exponent>=4 vanish in D, just as in Delta_D. At r=3 one extra actual term appears, x²tensorxi_1^4, which Delta_D omits because x^4=0 in its RIGHT factor. The remaining top term is1tensorxi_1³xi_2. Meanwhile

 rho(xi_1^6)=1tensorxi_1^6+x²tensorxi_1^4,                          (11)

since the only nonzero binomial terms after projecting the left factor have exponents0 and2 (binomial6 choose2 is1 mod2, while left exponents4/6 vanish). Adding(11) cancels the unwanted term and changes the top right factor to j(x³y). Every other right factor is one of the already checked lower lifts. This proves the last case of(10) and hence the whole comodule identity.

Now define

 Phi:C tensor D→P,          Phi(c tensor d)=c j(d).                 (12)

It is a graded vector-space isomorphism with an explicit inverse. Relative to the standard monomial decomposition in §3, all basis columns agree except

 c tensor x³y → c xi_1³xi_2 + (c xi_1^4) xi_1².

Thus the standard-coordinate change S sends c tensor x³y to itself plus(c xi_1^4)tensorx², fixes every other basis vector, and satisfies S²=id in characteristic2. It has finite support on every vector and preserves degree because6=4+2. Writing mu:C tensor D->P for the standard monomial decomposition, Phi=mu composed with S and Phi^(-1)=S composed with mu^(-1). To invert Phi, FIRST take standard monomial coordinates by mu^(-1), THEN apply the involution S. For example xi_1³xi_2 maps back to1 tensor x³y+xi_1^4 tensor x², whose Phi-image cancels the two xi_1^6 terms. No infinite triangular convergence or supplied invertibility hypothesis occurs.

Combining(8),(10),

 rho Phi(c tensor d)=sum d_(1) tensor Phi(c tensor d_(2)).           (13)

Consequently P is explicitly cofree as a left D-comodule with coefficient vector space C. This follows from actual maps and their inverses. It is not the false assertion that the original eight uncorrected lifts were a comodule subspace.

## 5. Dualizing gives actual all-degree LEFT-B freeness

For a in A and a monomial c of C define b_c(a) in B0 by

 b_c(a)(d)=a(c j(d)),    d in D.                                   (14)

Only finitely many c have a nonzero coefficient: a has finite graded support; d has degree0..6; each bounded graded range of C has finitely many monomials. Conversely any finitely supported family b_c in B0 defines a unique a in A by its values b_c(d) on the Phi-basis, with finite graded support. This proves an actual graded vector-space identification A≅direct_sum_c B0, with explicit coefficient maps and inverse.

The side of its module action is decisive. Equations(3),(13) imply, for b in B0,

 b_c(pi^vee(b) a)(d)
 =sum b(d_(1)) b_c(a)(d_(2))
 =(b b_c(a))(d).                                                  (15)

Thus these are coordinates of A as a LEFT B0-module. Let u_c in A be the unique functional with coefficient epsilon_D at c and0 elsewhere, where epsilon_D is the unit of B0. Then every a has the UNIQUE finite expression

 a=sum_c pi^vee(b_c(a)) u_c
   =sum_c iota(nu^(-1)(b_c(a))) u_c.                              (16)

This is a left-B basis witness with finite coordinate maps for EVERY actual a, exactly the correctly sided witness required to induce the source RIGHT-B resolution by (-)tensor_B A. No freeness axiom is supplied.

The u_c even have a simple direct description: u_c is the ordinary monomial-dual functional of c in P. For d=1, Phi(c' tensor1)=c'; for every nonunit basis d of D, each monomial of c'j(d) has a nonzero residual xi_1 exponent mod4 or xi_2 exponent mod2. This includes the correction xi_1^6, whose residual exponent is2. Such a monomial is never a C monomial, so the monomial-dual of c annihilates every nonunit column. Its value on c' is delta_cc', exactly the required coefficients. Thus c=xi_1^(4a)xi_2^(2b)xi_3^r3... yields a concrete homogeneous u_c. Its degree is|c|; coefficients in (16) have the corresponding degree differences, and never require a completed infinite sum.

By the explicit free-coordinate exactness proof in the preceding balanced-induction note, this actual witness proves (-)tensor_B A exact on every sequence of right B-modules. Induction also preserves projectives by the actual adjunction there. Thus the concrete ring map iota and full free witness instantiate its right-module Ext theorem, not only its Hom dimension statement.

## 6. Actual antipodes and both sides, without a new hypothesis field

For clarity we construct the needed compatible bijective anti-automorphisms instead of saying 'use an antipode' as an unfilled field. In any connected nonnegatively graded bialgebra here, put e=unit epsilon and N=id-e. In the convolution algebra of linear maps P→P define, degreewise,

 S_P=sum_(k>=0) (-N)^(star k).                                     (17)

On a homogeneous degree-d element every convolution power k>d vanishes: in an iterated coproduct the degree is a sum of k positive degrees after applying N to every factor. Thus (17) is a finite sum on each element. Convolution associativity and the finite geometric identity prove S_P star id=id star S_P=e. This constructs the two-sided antipode and preserves grading.

Because P is commutative, S_P is an algebra map. Indeed in Hom(P tensor P,P), both S_P after multiplication and multiplication after(S_P tensor S_P) are two-sided convolution inverses of multiplication: expand Delta(xy)=sum x1y1 tensor x2y2 and use commutativity to group the two antipode cancellations. Uniqueness of a convolution inverse makes them equal. Applying the algebra map S_P to its two inverse identities gives S_P² star S_P=S_P star S_P²=e. Since id is already the two-sided inverse of S_P, uniqueness gives S_P²=id.

Its anti-coalgebra identity is also a consequence of actual cancellation, not a new assumed Hopf axiom. In Hom(P,P tensor P), Delta S_P is a two-sided convolution inverse of Delta, since Delta is an algebra map. The map(S_P tensor S_P)flip Delta is another: expanding four iterated factors, its left product with Delta has terms S(p2)p3 tensor S(p1)p4. Cancel the middle antipode pair, then the remaining pair, to get epsilon(p)1tensor1. The other product similarly cancels p2S(p3) then the outer pair. Hence

 Delta S_P=(S_P tensor S_P)flip Delta.                             (18)

The same connected-graded construction yields S_D on D. The quotient map pi intertwines them: pi S_P and S_D pi are both convolution inverses of pi in Hom(P,D), so they agree. Both preserve the counit and are involutive.

Define chi_A(a)=a after S_P and chi_0(b)=b after S_D. Equation(18) makes them graded algebra ANTI-automorphisms; involutivity makes them bijective. Set chi_B=nu^(-1) chi_0 nu on the actual source B. Then

 chi_A iota=iota chi_B,     epsilon chi=epsilon.                    (19)

These are the actual compatible data for the side-conversion in the preceding note. In particular v_c=chi_A(u_c) is a RIGHT-B basis: applying chi_A to the unique left expression(16) gives a unique finite expression sum_c v_c iota(chi_B(coeff_c)). This is a derived right witness, not a silently swapped left one. It gives exactness of A tensor_B(-) on left B-modules as well.

## 7. Instantiated algebraic H2 and the precise native/topological boundary

Using the preceding note's explicit balanced quotient/adjunction/natural cochain maps and full free resolutions, the now constructed actual A,iota,left/right bases prove, for all n>=0 and the trivial compatible coefficient k,

 Ext^n_(right A)(k tensor_B A,k) ≅ Ext^n_(right B)(k,k),
 Ext^n_(left A)(A tensor_B k,k) ≅ Ext^n_(left B)(k,k).               (20)

These are isomorphisms of actual derived groups, not equal ranks. The first uses(16) directly with the actual RIGHT-B source resolution. The second follows either from the right-B basis plus the left-form adjunction, or from the explicit anti-automorphism twist in(19) and the preceding note. The induced objects are the actual quotient modules k tensor_B A≅A/(iota(B_+)A) as a right A-module, and A tensor_B k≅A/(A iota(B_+)) as a left A-module; their annihilated ideals have the stated sides. Trivial coefficients are unchanged by chi because the augmentations are compatible.

The source's finite projective prefix remains the actual right-B prefix with ranks1,2,2,2,3,4. Its correctly indexed infinite kernel/free-cover splice from the preceding note supplies a full resolution. Exactness is now preserved by the constructed free witness, rather than assumed after tensoring. Its existing dual coboundaries and dimensions in degrees0–4 may consequently feed the MANUAL instantiated ungraded comparison. Ext5 still requires its actual next differential/kernel statement; a fourth dual cokernel alone does not supply it. No new native `isoExt` is claimed.

All maps in the construction preserve grading. To obtain an internally graded Ext comparison, use actual graded modules and homogeneous free covers: take one free generator of the degree of each homogeneous element to cover any graded module, then cover the homogeneous kernel successively. These are onto in every degree, so the same explicit comparison/naturality works in each internal Hom degree. Evaluation at the degree-zero unit, multiplication, antipode and (16)'s homogeneous coordinates respect that degree. This proves the mathematical graded comparison with specified homogeneous data; it does not identify an Adams stem, collapse a spectral sequence, solve extension problems or convert an F2-vector-space into Z/16.

The primary Milnor presentation relates the explicit P/A to the conventional mod2 Steenrod algebra; this paper theorem is credited as an external mathematical identification, not newly formally derived from a cohomology-operation model. Topological H1 ko-cohomology identification, H3 spectral-sequence/convergence and H4 ABP/bordism remain the original separate obligations. Genuine existing source A1 ring/augmentation/linear maps/exactness/cohomology facts are retained. This note does not claim a generation count, phenomenological prediction or physical release.

The MANUAL original B4 algebraic construction, including full A/source-compatible inclusion/all-degree LEFT and RIGHT B-bases/compatible involutive antipodes and BOTH-sided derived/internally graded Ext comparison, now has complete independent mathematical acceptance together with the preceding accepted balanced construction. Native B4/H2 remains owed: actual polynomial/graded-dual bialgebra/finite quotient/source-basis equivalence, comodule maps/inverse, typed left/right module bases, balanced objects or direct-free route, full categorical splice/graded Ext and exact consumer statements must be built under ROOT's ordinary ADR008 admission, kernel/source reviewed and integrated. No axiom, supplied freeness field, library-absence label or source prose can replace those native constructions.

## 8. Controls, provenance and next work

Controls are actual mathematical identities: the full64 source products under(5); failure of e3→beta30 alone; failure of the uncorrected top lift with the explicit x²tensorxi_1^4 remainder; corrected involutive finite-support coordinate change; degrees including6=4+2; all-degree coaction vanishing for n>=3; distinction between left and right free bases; finite graded support versus a full completed dual; actual source-right resolution versus the left original H2 and the compatible antipodes. None was evaluated by numerical or symbolic software. The local research report's API/axiomatized-freeness recommendations are not used, and no topological theorem is obtained by an arithmetic status witness.

Complete independent algebra review has accepted every universal construction, coassociativity, quotient, all64 basis constants, corrected comodule identity and inverse, all-degree support/side, connected antipode and (20)'s actual derived/graded application, with full review linked above. Lead acceptance records that manual milestone; fresh full SOURCE review of this unapplied propagation still follows. ROOT owns actual source/native/holding/closure/main work. Native construction, original external identification/topological inputs and full publication acceptance remain separate. This work requests no scientific deferral and imposes no extra arbitrary-generalization gate.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

Current e1e2=e3+e4,e2e1=e3 are not the local report's naive standard Milnor labels. Equation(5), rather than an unproved equality of names, supplies the actual embedding. The current source has genuine eight-dimensional algebra/Hom/exactness results, but no fullA/free witness; those are explicitly built MATHEMATICALLY here at all degrees. The eight obvious polynomial lifts alone are not a stable comodule section; the top correction(9) is necessary. Finite low-degree dimension agreement is insufficient; the explicit inverse/coefficient/antipode constructions are the actual repair. None retroactively certifies native H2, cohomology-operation realization, topology, canonical closure or publication readiness.
