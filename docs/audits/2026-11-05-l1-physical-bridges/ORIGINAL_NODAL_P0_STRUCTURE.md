# Nodal P0: endpoint saturation and exact Haar-projector frontier — corrected R2

Task l1-nodal-p0-structural-exploration-r1; parent publication-remediation-01a13f67/l1-positive-physical-reconstruction. Manual exploration; sole private output. R1 is preserved unchanged. This R2 corrects the fixed-direction conclusions using the lead's subsequent source-review finding; its first and final continuity checks use the same primary R1 packet. I read the accepted original nodal reduction, both independent reviews, current notebook entry, and the prior complete nonzero-normalization construction. No P0 value or sign has been obtained. The result below is a proof-ready finite contraction with an explicit additional endpoint and compact-center selection, not a claim of its evaluation.

## Original object and endpoint incidences

At the actual J=0, A=I node, retain the accepted P0(u0)=integral dU1 I1 A8(u0,U1;V1=I)^16. Every original ordered EHC contribution is retained, including g2 stripped off, epsilon world/internal signs, its 1/4, all coframe quarters, closed plaquette orientation, and both temporal-spatial curvature orders. The slice-1 spatial graph is the cube Q3: eight vertices, three undirected endpoint pairs at each vertex, and two independently anchored links per endpoint pair. The sixteen original temporal-anchor integrals were removed by the accepted absent-link/gauge change, not by setting the original temporal links equal. Flat u0=I is an admissible node, not a representative of every node.

At a center x each A vertex consists of two spatial coframes with two *distinct* direction labels i,j in {1,2,3}, and curvature in their complementary time/spatial plane. Each coframe is an even bilinear containing exactly one odd generator at x and exactly one at x+ei (even after the period-two neighbor identification); the two endpoint choices and their independent U,V links remain explicit. This statement is independent of gamma or internal-index values.

Expand A8^16 as an ordered product of sixteen original summands, without an extra factorial. Let m_x be the number centered at x, and n_(x,i) the number of coframes at x in direction i among those m_x vertices. Then necessarily

  sum_x m_x=16,   0<=m_x<=4,
  n_(x,i)>=0,   n_(x,i)<=m_x,   sum_i n_(x,i)=2m_x,
  2m_x + sum_i n_(x+ei,i)=8                     (E)

for every x. The last equation counts the exact eight original odd variables needed at x; no cancellation or Haar assumption is used. m_x<=4 follows from it. Conversely (E) is only a necessary degree condition: repeated components, internal signs and Haar invariants can still make the contribution zero. For each x the number of its vertices omitting direction i is exactly m_x-n_(x,i); in particular the possible distribution of the three omitted directions is fixed by n. These are additional exact constraints on every ordered world-index contribution, not a selection of a preferred subset.

For an undirected spatial endpoint pair e={x,y=x+ei}, define the coframe incidence k_e=n_(x,i)+n_(y,i). The complete graph has twelve such pairs and sum_e k_e=32. Unlike the earlier pure-cosmological Q4 proof, (E) does not force k_e=2: the curvature factor in each A vertex also depends on one of the pair's anchored spatial links. Thus neither the old independent two-anchor second moment 1/8 nor its K_e loop signs can be transplanted to P0.

## Center-parity rule and full chiral contraction

Fix u0=I for the following explicit compact-link simplification. In the accepted original source-to-target convention a temporal-spatial closed plaquette at V1=I is an oriented fundamental Spin(4) matrix U_a or U_a^dagger on one slice-1 spatial anchor a, with basepoint and orientation retained. For example the reviewed H_(1,x;0i)=U_(1,x,i)^dagger U_(0,x,i) reduces to U_(1,x,i)^dagger. The reverse ordered plaquette and all endpoint choices remain their own original terms; no identification of the two periodic anchors is made. Each spatial coframe summand also contains one fundamental matrix or adjoint at its selected anchor. Thus each expanded ordered A^16 summand carries precisely 32 such coframe occurrences and 16 curvature occurrences, distributed over the 24 anchors (some traces or components may themselves be zero). This is occurrence counting, not independence of the factors.

For a given anchor a and chirality chi in {+,-}, let N_(a,chi) count the actual U_chi or U_chi^dagger fundamental appearances after expanding the Dirac matrices, curvature trace, spinor components and the two coframes. Terms whose gamma blocks make a chirality assignment impossible are zero already. Each Spin(4) Haar measure is the product of normalized SU(2)_+ and SU(2)_- measures. Under the center element -I in either SU(2) factor, its fundamental and adjoint matrix entries change sign. Hence a necessary exact condition for a nonzero Haar contribution is

  N_(a,+) even AND N_(a,-) even, for every one of the 24 anchors.  (H)

In particular the total number on each anchor is even. The count includes curvature and coframes together; it is invalid to average either before accounting for their shared anchor. Condition (H) holds for nonflat fixed u0 as well, since a fixed retained matrix does not change the center parity, but the expanded curvature may contain its fixed entries between the moving factors. No claim that (E) and (H) are sufficient is made.

To expose a finite exact remaining contraction, take each original expanded monomial satisfying (E) and (H), with its actual coefficient c_s (world/internal epsilon, 1/4 and coframe quarters, gamma and fixed u0 entries), and list its 64 site-labelled odd generators in the order they appear. Let sign(s) be zero if any generator repeats, otherwise the sign of the unique permutation to the inherited product of the eight site tops. All site blocks have even size; this defines every Berezin sign without choosing an ordering of even blocks by hand. Collect all SU(2)_chi matrix entries at each anchor in their actual order. Replace each conjugate matrix by the exact pseudoreality identity U^dagger_i^j = epsilon^(j k) U_k^l epsilon_(l i), with epsilon conventions fixed consistently (equivalently leave daggers and use the mixed invariant projector). Do not treat U^dagger as an independent Haar variable.

For each anchor/chirality with N=2r, Haar integration of the 2r fundamental factors is the matrix of the orthogonal projector onto Inv[(C^2)^tensor 2r]. An explicit exact formula is

 P_(2r) = sum_(alpha,beta) |E_alpha> (G^-1)_(alpha,beta) <E_beta|,
 G_(alpha,beta)=<E_alpha,E_beta>,

where {E_alpha} is any fixed linearly independent noncrossing epsilon-pairing basis for the SU(2) invariant subspace; r=0 gives P_0=1. The Gram inverse is only the inverse of this explicit fixed SU(2) invariant-tensor Gram matrix, never a square root or positivity assumption about R_b. For odd N the projector is zero. Insert the original free matrix indices of the expanded monomial into P, including every epsilon introduced for a dagger. Then the exact finite expression is

 P0(u0)= sum_(s: E,H) c_s sign(s) product_(anchors a, chiralities chi) P_(N_(a,chi))[indices(s)].  (F)

Here s ranges over ALL sixteen ordered original vertices, all eight centers, all ordered world/internal labels, both endpoint/coframe terms, both anchor orientations, and all spin/chiral indices. Formula (F) is an equality obtained solely by linearity, Berezin top extraction and Haar projector identity. It is a signed sum, not a positive sum; there is no factor 1/16! in P0 itself. A particular monomial surviving (E),(H) is not sufficient to prove P0 nonzero, because every other s in (F) can cancel it. The exact remaining task is to evaluate or find a symmetry/sign structure for this full sum, with its c_s and sign(s); the selection rules do not fix its sign or vanishing.

## Scope and consequence

If some admissible u0 has P0(u0)!=0, then the p=0 boundary component g2^16 P0/16! is nonzero at actual g2=Lambda^4, while Tr R_b=0 at the node. Accepted Hermiticity gives a negative eigenvalue there, and continuity is needed to promote that point statement to a neighborhood. No such node has been demonstrated here. P0(I)=0, if subsequently proved, would neither imply P0 vanishes at every node nor settle the other five boundary-grade blocks. No source-family, physical CAR, transfer, or publication conclusion follows.

FIRST SAME check returned fresh=true, changed=[]. Static source reads and manual reasoning only; no scientific evaluator/CAS, exterior/Haar/Gram program, numerical test, Lean/build, controller/slot, Git or repository/notebook edit. Independent actual math and original-source review are required. Final SAME check and this report's digest are reported to lead.

## Fixed curvature direction: exact square occupation reduction

The lead proposed isolating direction 3; the following is an exact reduction of the SUM of terms whose temporal-spatial curvature plane is {0,3}, without claiming it is an isolated coefficient of the full retained-link polynomial. Such terms necessarily have coframe directions {1,2}. Therefore n_(x,1)=n_(x,2)=m_x and n_(x,3)=0. Equation (E) reduces, on each of the two x3-constant Q2 squares, to

  2m_x+m_(x+e1)+m_(x+e2)=8.

Writing m=2+v, the homogeneous system is (2I+adjacency_Q2)v=0. The square adjacency eigenvalues are 2,0,0,-2; hence its kernel is exactly the checkerboard vector. Thus on each square independently

  m_x=2+a (-1)^(x1+x2),    a in {-2,-1,0,1,2}.

The integer and 0<=m_x<=4 restrictions are included. Both squares together automatically have total multiplicity16. This proves the complete five-pattern roster per square BEFORE any Haar cancellation; it does not assume all patterns contribute.

For this restricted sum only, direction-3 U1 anchors occur in curvature factors but not in coframes. The subsequent lead/source-review inference, beyond R1, resolves both original ordered plaquettes at each center after V1=I:

 H03(x)=U1,3(x)† U0,3(x),    H30(x)=U0,3(x)† U1,3(x).

Both use the same unique direction-3 anchor based at x. This is the actual closed-word convention; see the representative original holonomy and gauge transformation in ORIGINAL_NODAL_BOUNDARY_REDUCTION_SOURCE_REVIEW_R1.md §“Exact p=0 coefficient and original temporal dependence”, and the full-cut word convention in P0_NUMERICAL_FULL_CUT_TRANSPORT.md §§1–2. The second ordered identity is the new source-review inference supplied by lead, not something R1 had established.

The independent normalized Haar change U1,3(x)=U0,3(x) W_x turns the two holonomies into W_x† and W_x. Therefore all retained U0,3 factors disappear from this sector. Each curvature vertex centered at x contributes exactly one fundamental W_x or W_x† factor in one chiral block, and no other center or coframe uses W_x. Invariance under the simultaneous Spin(4) center (-I,-I) sends every such factor to its negative. Consequently the integral vanishes unless m_x is even. The complete surviving degree candidates on EACH square are therefore a in {-2,0,2}, giving checkerboard multiplicities (0,4), (2,2), or (4,0); their coefficients can still vanish or cancel.

In particular, R1's statement that the squares remain coupled by direction-3 curvature Haar contractions or fixed U0,3 factors was false and is withdrawn. After the stated independent W_x integrations, those factors do not couple the squares; the direction-1 and direction-2 coframes and their link integrals lie within their respective squares. Their even eight-variable site blocks can be reordered without an extra sign. This structural separation does not compute the sector, isolate it from the other mixed-curvature-direction sectors, or establish any sign. At flat u0=I, other sectors can cancel it. Full P0 remains unevaluated.

No unreviewed second- or fourth-moment value is used. Independent actual mathematics and original-source review of this R2 remain required.
