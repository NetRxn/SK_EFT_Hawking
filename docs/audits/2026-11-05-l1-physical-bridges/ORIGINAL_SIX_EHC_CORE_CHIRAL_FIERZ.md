# Original core local Fierz theorem and precise separator frontier

Executor01a1ac65; parent publicationROOT01a13f67/L1 physical-observable boundary.
Source1cba3341bef8cba103444dc552268986d185d21d;2026-11-20 America/Chicago.
MANUAL candidate result for independent ACTUAL mathematics and original-source
review. No execution or whole-core fit follows. The raw derivation report
/private/tmp/l1-sixehc-core-local-fierz-analysis-r1.md (19153B,
b647de26cf4bbb086a504907316837c8da0544e115ebd8b4aab57c7981ddaa59)
is preserved unchanged; this candidate adopts its full mathematics with explicit
index terminology and review boundary. Current source/authority was deliberately
reconciled as detailed below; notebook writer is Executor01a1ac65.

INDEX CONVENTION: A,B,C,D in the Fierz/Hodge formulas are INTERNAL Euclidean
gamma-vector indices. The copy labels a,b are flavour/multiplicity coordinates.
Their Hodge stars are quaternion-oriented algebraic operations; neither is a
lattice/spacetime Hodge star. Lattice world directions mu=0,1,2,3 label actual
edges, sources and the stated coframe slots. The mixed-kernel coefficient
eta=diag(1,-1,1,1) does NOT define either Hodge metric or a physical signature.
Original EHC WORLD epsilon and INTERNAL gamma5 signs remain separate and intact.

No scientific executable/import/CAS, mask/moment/Haar/tensor/network generation,
test/Lean/build/native/slot/controller/process or harness action was performed.
All new equations are manual; rank18, local zeros and separator dimensions are
not generated support inventories or a claim of any nonzero global amplitude.

## 1. Fixed original scalar and core

The accepted original aggregate is

 h12,6=8 I Haar[(Q0,22+Q4,22)(Q1,22+Q5,22) Pi*],
 Pi*=(prod_{z notin{0,1,4,5}}D_z) E0,02 E4,02 E1,12 E5,12 E1,23 E5,23.

Core sites are{0,1,3,4,5,7,9,13}; the literal core retains D3,D7,D9,D13, six unit EHC faces, sources(Q0+Q4)(Q1+Q5), twenty quarter-coframes, twelve exterior V insertions and twenty independent curved anchors. Its odd degree is20*2+12*2=64, exactly the eight-site top. All22 curvature-free mixed-pair1/8 factors have already been included in the outer coefficient. They must not reappear inside the core.

The earlier source-bound kernel uses q_A=(-i sigma1,-i sigma2,-i sigma3,I), E12=+1, gamma5=diag(I,-I), M=barR q† psiL, N=barL q psiR, B=barR q†E barL^T, P=psiL^T E q psiR, and V=(M+N,i(M-N),B-P,i(B+P)). Its actual C=diag(1,-1,1,1)/2 and t=192 determine the projected boundary weights; C is not a physical metric or the Hodge metric to use below. The six canonical core pair slots are ordered at(0,3,9)/(4,7,13), each in increasing world-slot order. The projected W has only5856 same-kappa cells and a signed Gram description. Its exact negative star coordinate is not the aggregate sign.

## 2. Exact quaternion-flavour realization

Define four-component local odd spaces by spin index i=1,2 and flavour p=1,2:

 L_(1,i)=barL_i, L_(2,i)=(psiL^T E)_i,
 R_(1,j)=(E barR^T)_j, R_(2,j)=psiR_j.

They are invertible signed permutations of the four original odd generators of each chirality, not new degrees of freedom. In order(L11,L12,L21,L22), the L block is(barL1,barL2,-psiL2,psiL1), whose top is exactly tauL with positive sign. The R block is(barR2,-barR1,psiR1,psiR2), also with positive original tauR. Thus the original tauL tauR top is unchanged. Put Wpq^A=Lp q_A Rq. Pseudoreality q†=-E q^T E and the actual odd interchange give

 (W11,W12,W21,W22)=(B,N,M,P).

Therefore the four multiplicity matrices for the actual Hermitian V basis are

 K_a=(sigma1,sigma2,sigma3,iI)=i q_a,  a=0,1,2,3,
 V_a^A=sum_(p,q,i,j) (K_a)_pq (q_A)_ij L_pi R_qj.              (1)

This fixes both internal-vector and multiplicity quaternion orientations. In particular a Lorentzian Hodge star inferred from C's signature would be the wrong operation: the complex algebraic quaternion identification(1) gives the same Euclidean oriented four-dimensional Hodge star on the a and A labels. The common factor i has no effect on its eigenspaces.

## 3. Signed local factorization and exact rank18

Let Z_ab^{AB}=V_a^A V_b^B-V_b^A V_a^B. Since V's are even, Z is antisymmetric in BOTH a,b and A,B. Its actual signed index expression is

 Z_ab^{AB}=-1/2 sum (K_a,pq K_b,rs-K_b,pq K_a,rs)
                   (q_A,ij q_B,kl-q_B,ij q_A,kl)
                   L_pi L_rk R_qj R_sl.                      (2)

The minus comes from moving the first R past the second L. The1/2 is the redundant explicit internal-vector antisymmetrization, not a source normalization. Formula(2) is a closed source-exact local kernel; it requires no generated mask table.

Each local chirality has Lambda²(C²_spin tensor C²_flavour)
 = (Sym² spin tensor Lambda² flavour)
   direct-sum (Lambda² spin tensor Sym² flavour), dimension3+3.

For example define symmetric forms

 S_L,ik=(1/2)sum_pr E_pr L_pi L_rk,
 F_L,pr=(1/2)sum_ik E_ik L_pi L_rk,

so L_pi L_rk=E_pr S_L,ik+E_ik F_L,pr, and likewise for R. Substitute in(2). The simultaneous spin/flavour symmetries kill S_L S_R and F_L F_R in the double antisymmetrization. Only S_L F_R and F_L S_R survive, each3-by3. Equivalently, with star_a and star_A using orientation0123,

 Z restricted to Lambda²_+copy tensor Lambda²_+vector =0,
 Z restricted to Lambda²_-copy tensor Lambda²_-vector =0,
 surviving domain = (Lambda²_+copy tensor Lambda²_-vector)
                    direct-sum (Lambda²_-copy tensor Lambda²_+vector).

Under the explicit quaternion identifications(1), this surviving domain maps
isomorphically to the LITERAL output image

 image Z = (S_L tensor F_R) direct-sum (F_L tensor S_R)
           within Lambda² L tensor Lambda² R.                 (3)

The surviving18-dimensional image is exact, not just an upper bound. In the spin/flavour coordinates the two mixed sectors are independent9-dimensional tensor products. Wedge projection is nonzero on each: an antisymmetric flavour pair times a symmetric spin pair produces a nonzero L two-form, and the complementary symmetric flavour/antisymmetric spin pair produces a nonzero R two-form. The invertible quaternion identifications in(1) then identify each surviving irreducible9-dimensional sector isomorphically with its output. There is no further universal local kernel absent additional source/field constraints.

For an explicit Hodge convention, self-dual canonical-pair combinations are(01+23),(02-13),(03+12); anti-self-dual ones have the opposite signs. Same-Hodge copy/internal-vector combinations vanish in(2). This identity can be used before any compact integration and before multiplication by the rest of the original even integrand.

A concrete canonical support consequence is available without generating masks. Order each chirality as(L11,L12,L21,L22), or the corresponding R order. The spin-triplet S basis uses pair masks13,24,(14+23), while the flavour-triplet F basis uses12,34,(14-23), with the displayed middle combinations carrying their defining1/2 factors. Therefore eight of the36 canonical L-pair/R-pair cells vanish strictly: both pair masks in{13,24}, or both in{12,34}. The other28 cells have ten further linear relations, leaving rank18. The actual top pairing is orthogonal between S and F subspaces: S11 S22=-tau, S12²=tau/2, F11 F22=tau, F12²=-tau/2 and all S-F wedge products vanish, in either positive-top L or R block. These are exterior bilinear pairings, not positive metrics. Hence the remaining four-field tensor at each boundary-core site can also be projected to the same18 mixed sectors before saturation. This is an actual local core filter, not just an output-shape count.

The total local degree-four space with2L+2R has36 canonical monomials. Its other18 channels are S_L S_R and F_L F_R, which a general degree-four polynomial can occupy; the present double-antisymmetric external V insertion cannot. Thus36 remains the general local support dimension and18 is the exact dimension for this specific insertion. It is not an18-mode truncation of the original field theory.

## 4. What this proves for actual EHC and D factors

For normalization, a FULL ordered antisymmetric contraction satisfies sum_AB F_AB V_a^A V_b^B=(1/2)sum_AB F_AB Z_ab^{AB}=sum_{A<B}F_AB Z_ab^{AB}. Use either convention consistently. Replacing the original insertion by a full ordered Z contraction without its1/2 would double it. The same rule applies to a D epsilon with its other two slots held fixed.

At0/4 the two external internal-vector indices belong to E0,02/E4,02 and contracts F_AB(H)=Tr[H gamma_[A gamma_B] gamma5]. In the held gamma convention, the upper chiral block has A01=-A23 while the lower block has A01=A23; analogous cyclic relations fix the remaining components. Hence H_L contributes an anti-self-dual internal two-form and H_R a self-dual one. Equation(3) proves the exact LOCAL lock:

 E0/E4 curvature L -> external copy self-dual,
 E0/E4 curvature R -> external copy anti-self-dual.            (4)

All signs of the original world epsilon and gamma5 remain. A dagger changes the actual curvature function as prescribed by the original action; it does not permit changing the paired Hodge label by guesswork. This proof uses its internally antisymmetric trace, not raw diagonal traces, which need not vanish.

At3/7/9/13 the external slots belong to one D epsilon. The same18-channel insertion identity holds, contracting the remaining two D-coframe internal indices through their actual epsilon. Both allowed Hodge sectors must be retained. This does not by itself assign those coframes to one compact chirality or eliminate a complete EHC-chirality assignment: link-dependent coefficients and remaining shared fields can carry the needed indices. In particular it is invalid to infer that all center fields have one chirality merely from a curvature's internal-vector duality.

Every external V has one L and one R generator. Its pair uses2L+2R. Therefore at EACH of the six boundary-core sites the four remaining original coframe fields must supply exactly2L+2R for local top saturation. Hubs1/5, which have no V insertions, require4L+4R. These are exact local support filters usable before Haar; their global totals are already compatible with the20 T factors. They do not prove that any surviving local support has nonzero Haar weight.

The six-copy canonical pair basis and the Hodge basis are different. A Hodge pair combines a canonical pair with its complementary pair, changing its four-bit mask by1111. Consequently a Hodge transform can mix kappa with kappa xor1111. One must transport the actual5856-cell W exactly under these transforms or keep canonical coefficients and implement(3) as a signed linear identity. Dropping a kappa block because one Hodge sector vanished would be an unjustified global projection.

## 5. A small universal kernel bound, without recommending a detour

For fixed a,A, each V has four unit-phase bilinears in the original signed-permutation L/R variables. Each canonical Z component uses at most32 ordered bilinear products. There are6*6=36 canonical input components and36 possible2L+2R output monomials. Thus a universal direct verification table has1296 possible Gaussian-integer cells and at most1152 raw products, with coefficients bounded in absolute value by32. One can instead use18 mixed-Hodge input combinations: each sums four canonical Z components, at most128 products and coefficient magnitude<=128; the normalized expansion back into canonical input uses the explicit1/4 Hodge-projector coefficient. Its18*36=648 Gaussian-integer numerator cells need2592 signed16 real/imag numeric bytes, with denominator4 retained. No table has been generated or entry evaluated by code.

These are safe finite verification bounds for(2)-(3), not a whole-core budget. The lemma is already analytic and should be independently reviewed as a proof. A fresh local-table run solely to reconfirm rank18 is not the recommended next science computation unless an actual disputed sign requires it. The full source-specific page/core remains the target.

## 6. Complete book-page separator and its concrete obstruction

The ten-edge core is a three-square book with central edge1--5 and three length-three paths:

 page0:1--0--4--5,
 page1:1--3--7--5,
 page3:1--9--13--5.

Each page has three geometric edges/six independent anchors, and the shared central edge has two more, totaling20. There are six coframes per page and two on the central edge. Page0 includes the EXACT source sum Q0+Q4 on0--4; the central edge includes Q1+Q5. Sources must remain sums with their actual endpoint gamma placements. The three pages are conditionally separable only after retaining the central compact factors, hub fields AND the original inter-page internal-vector indices.

For example page0's two side coframes on1--0 are both centered at1 and come from different EHC factors E1,12/E1,23; their internal labels later couple to different other pages. Its two side coframes on5--4 similarly couple at5. Their products are symmetric in the two internal-vector indices at each hub, leaving dimension10 per hub, not16. They cannot be replaced by a scalar delta kernel while curvature still weights those anchors.

After integrating page0's two outside sites and its six independent anchors, an exact page object may retain:

 - two external copy pairs, dimension6 each;
 - a degree-two original eight-mode exterior mask at each hub, dimension28 each;
 - one central fundamental matrix entry from each of its two face holonomies, dimension4 each;
 - their two chiral labels,2 each;
 - the two symmetric side-coframe internal-vector pairs, dimension10 each.

The naive full shape is6²*28²*4²*2²*10²=180633600 cells. Using(4), each fixed curvature chirality permits only three external copy components, reducing6² to3² and the shape to45158400. This is a conservative dense-shape domain, not a lower bound on actual sparse support or a measured join count. Even the reduced shape is far above the prior120000-row primitive domain. Holding the two chiralities, both copy Hodge coordinates and both internal-vector-pair indices fixed gives a12544-cell hub-mask/fundamental slice, but there are4*9*100=3600 such slices. This is a COMPLETE slice roster, not qualification of their construction time, entries or assembly. A proposal for one slice must not be upgraded to complete page support.

The missing indices are material: omitting the two 10-dimensional internal gamma-vector pairs would understate the page by100, and deleting central fundamental indices would break the correlated three-face integration. The source endpoint sum is not another favorable choice to discard. Joint second/fourth moments at each actual anchor are still required.

The hub exterior algebra admits a useful but insufficient exact join bound. Each page contributes a degree-two mask at each hub. Ordered disjoint pairs at one hub number28*15=420; ordered triples number28*15*6=2520, after which the central degree-two mask is the unique complement. Across two hubs there are6350400 ordered compatible three-page mask triples. Fixing the first page's mask at hub1 splits this into28 complete slices of226800 mask combinations each. This counts ONLY exterior compatibility; all compact/internal-vector/chiral/copy indices still multiply these operations and can cause cancellations. It therefore does not qualify a3-million-pair or120000-row full scientific join. It does specify a complete source-bound mask partition without re-enumerating the original44 records.

A credible next page design should recouple the weighted same-endpoint side pairs into actual scalar/adjoint/bichiral blocks, apply the18-channel local Fierz form before retaining full internal-vector labels, and derive the surviving central-index/field-mask support analytically. The original central anchors each carry three curvature occurrences plus one coframe, so their final normalized moment is degree4; pagewise independent second moments would destroy this correlation. Page side anchors carrying two curvature occurrences plus coframes may have both scalar and nonconstant representations. The old same-endpoint unweighted delta K result alone cannot eliminate them.

This is a precise obstruction to claiming a full-core fit from18 local channels or5856 output weights: the inter-page internal-vector labels and central matrix/field separator have not been bounded in a complete contraction tree. A fully specified page slice may be a decisive next proposed computation after its local edge recoupling is proven and a real operation/denominator/output bound is derived. No such slice is admitted here. Selecting one core scalar or one negative W entry cannot determine the full aggregate; all allowed components/weights must close in the original pairing.

## 7. Decision and physical scope

The substantive new analytic result is the source-exact rank18 local insertion with the actual quaternion/Hodge orientation, its curvature locks at0/4 and exact local chirality loads. It gives genuine core reductions and exposes an explicit remaining separator rather than merely recasting the bulk. Accept these as proof preparation, subject to independent ACTUAL review. Do not accept a full-core runtime request, scalar/sign claim or unproved global chirality pruning from them.

The aggregate value/sign/nonzero remains UNKNOWN, as do complete core sparse support, worst joins, exact final denominator/numerator costs, walltime and RSS. Original TT/Ward/projector/pole, physical positive boundary-product-adjoint-seam/causal transfer, matter/EM/transport/calibration/B3 and limits remain OPEN. Local Hodge/flavour representation labels are bookkeeping of original exterior fields, not new physical sectors or a new metric.

## 8. Continuity reconciliation

The FIRST command used the exact original aggregate-kernel-r1 primary packet. During this analysis the lead announced intended canonical adoption of the separately reviewed kernel/projection and a deliberate new checkpoint/packet. The original9ac source basis and all prior report hashes are preserved; expected lead-owned drift must be reconciled explicitly, not refreshed away. The old aggregate packet was explicitly checked again and returned exit1, fresh=false, changed=[owned-files,source], matching the lead-announced canonical kernel/HEAD adoption. Source-dependent finalization paused there; no packet was refreshed away.

The lead then deliberately issued PRIMARY/.codex/continuity/l1-sixehc-core-fierz-r1.json at accepted checkpoint1cba3341bef8cba103444dc552268986d185d21d. FIRST recovery check returned exit0, fresh=true, changed=[]. Read the new packet/current primary notebook entry and FULL accepted canonical ORIGINAL_SIX_EHC_MIXED_ENDPOINT_KERNEL.md plus its acceptance from the ASSIGNED CHECKOUT paths pinned by that packet. (The same relative canonical paths are not in the separate primary checkout; this was resolved by using the packet paths, without moving files.) The accepted proof is18783B SHA4d85f14d098920ca1f401f29903bfcf30e81e60db86d2a5ca8b3762237e3bfca; its acceptance SHA06689c7d68b26270bc085b968171e364b7f5a257c3dde9807234c58d7e83d7b4. The new accepted authority fixes the same H/C/t, source word, projected W and core definitions used above; this changes no original core coefficient, field/gamma/quarter/top premise or new Fierz derivation. Current independent ACTUAL review contents were not used to derive this new local result.

Final SAME check uses the NEW core-fierz-r1 packet, not the historical aggregate packet. Its result and report SHA/bytes are supplied in delivery. No runtime authority follows from either packet.
