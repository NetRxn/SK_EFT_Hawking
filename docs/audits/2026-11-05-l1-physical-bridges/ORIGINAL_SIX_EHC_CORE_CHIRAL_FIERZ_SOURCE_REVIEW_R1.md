# ACTUAL original-source audit — local Fierz proof R1

**ACCEPT** the exact local Fierz, Hodge lock, and separator results in
19,346-byte R1, SHA256
69c856b210ed995d750347c7ff35bce1adc9f3feee6bc7023cdd5215705dd80b,
at clean source 1cba3341bef8cba103444dc552268986d185d21d.
No material correction to the mathematical or source conclusions.
Two terminology edits for canonical prose: line 78 identifies the image via
its input Hodge sectors, whereas its literal output lies in
Lambda²L tensor Lambda²R; say “the restriction to the two opposite-Hodge
summands is an isomorphism onto the mixed exterior sectors.” At lines
134 and 136 use “internal gamma-vector pair(s)/indices” where “world”
currently describes these ten-dimensional symmetric index pairs. The edge
directions remain world indices. These edits leave the equations,
normalizations, and counts unchanged.

## Direct original definition check

Read the assigned-checkout accepted ORIGINAL_SIX_EHC_MIXED_ENDPOINT_KERNEL.md
(including gamma, C, V, t=192, and literal core) and original EHC and
coframe formulas in ORIGINAL_SIX_EHC_SUPPORT_CONSTRUCTION.md and
ORIGINAL_SHEAR14_ONE_CANDIDATE.md. The held DAG uses six unit EHC with the
complete four-placement epsilon identity and bracket 1/2, four residual D,
both original endpoint sums, and all 20 quarter T, twelve V and twenty
independent anchors. The physical free-edge factors are already in the
projected bulk factor 3^8 2^-40; overall aggregate weight remains 8. Neither
multiplicity eta nor the signs of projected W define a Hodge metric.

The L signed permutation has psi tail (−psiL2,psiL1), the R one has barred
head (barR2,−barR1), each preserving its local chirality top. The held
tauL tauR equals the full top since swapping its intermediate pairs is
even. With E12=+1 and q†=−E q^T E, W11 is the B written with L bar
first, W12=N, W22=P, and W21=psiL^T E q E barR^T. This last expression
becomes M using E q E=−(q†)^T and one interchange of two odd fields.
The resulting copy matrices are σ1,σ2,σ3,iI=i q_a, including the factors
of i in both V1 and V3. The complex algebraic orientation uses 0123 in
both quaternion bases. No replacement of the physical C or t is involved.

## Signed wedge and Hodge rank

The first R crossing the second L gives the sign in (2). Interchanging
the full paired factors in the exterior wedge permits averaging the two
internal orders, giving 1/2 in the double antisymmetrization. An independent
normalization check is summing against general F_AB=−F_BA: its ordered
contraction with the two V is one half the ordered Z contraction, or the
canonical A<B Z contraction with no half. This also applies to a D epsilon
with the other slots fixed. It is distinct from the original gamma bracket.

The two exterior decomposition terms E_pr S_ik and E_ik F_pr recover
the original pair, and S/F definitions have the displayed 1/2. With one
flavour epsilon and one spin epsilon selected on opposite ends, the two
alternating coefficients survive. With both S or both F, one of the
spin/flavour alternations contracts an unchanged symmetric product and is
zero.

In more explicit quaternion coordinates, wedging the right input spin
indices produces the alternating part of q_A E q_B^T=q_A q_B† E; wedging
left input indices gives q_A^T E q_B=E q_A† q_B. Dividing off the common
copy phase gives the same conclusion in the flavour coordinates. For the
right-wedge/left-symmetric case the 01 and 23 matrices have opposite
signs: q0 q1†=−q2, q2 q3†=q2. For left-wedge/right-symmetric they have
the same sign: q0†q1=−q2, q2†q3=−q2. Cyclic quaternion products give the
other canonical Hodge combinations. On each allowed sector the three
components 03,13,23 span the three symmetric matrices after factoring
out the epsilon. Therefore each mixed sector is the tensor product of
two rank-three isomorphisms, and the two images land in disjoint
S_L F_R and F_L S_R subspaces. The exact rank is 9+9. This proof fixes
which Hodge sign each sector uses without appealing to a rank table.

In chirality order 11,12,21,22, S uses 13,24,(14+23)/2 and F
uses 12,34,(14−23)/2. Consequently the four same-pure-S and the
four same-pure-F canonical cells vanish separately. Rank 18 in the remaining
28 cells gives exactly ten independent relations on that output. Wedge
signs give S11 S22=−tau, S12²=+tau/2, F11 F22=+tau, F12²=−tau/2.
All S-F wedge products vanish, and the two displayed three-dimensional
top pairings are nondegenerate. Hence projecting the remaining fields
onto the same mixed sectors is valid for the top contraction. It is an
exterior pairing of fixed degree, without an inner-product interpretation.

## Application to the actual source factors

The (02;13) world orientation at E_(0,02), E_(4,02) is − for each;
(12;03) and (23;01) stay +. The internal gamma5 multiplies the lower
block by −1. In the upper block A01=−q2 and A23=q2, and in the lower
including gamma5 A01=A23=q2. Thus the upper L curvature is anti-self-dual
and lower R is self-dual as internal two-forms for any actual H. Trace
linearity and the original daggered order preserve these statements.
Opposite-copy restriction is precisely L→copy self-dual and R→copy
anti-self-dual at 0 and 4. At D3/D7/D9/D13 both Hodge blocks remain.
No additional curvature-chirality or whole-source suppression follows.

Each V has one L and one R odd factor. Their pair forces the remaining
four odd fields at that site to supply 2L2R; hubs 1,5 have no external
V and require 4L4R. These are exact local exterior restrictions. Canonical
pair to Hodge basis change combines each pair with its complement and can
mix kappa with kappa xor1111. Thus the accepted projected W must be
transported or contracted in its canonical basis with the full signed
Fierz identity. A local zero does not remove a global W block.

## Page indices and quantitative boundary

The three actual retained paths are (1,0,4,5), (1,3,7,5), (1,9,13,5).
The shared edge is 1–5 on world axis 2. Each geometric path uses six
independent anchors and six quarter T, and the central edge adds two
anchors and its own two T. Q0+Q4 belongs to the inner 0–4 edge of page0;
Q1+Q5 belongs to the central edge, with the distinct original endpoint
gamma orders at both. Page0 has one single open central fundamental matrix
entry per E_(0,02) and E_(4,02) trace. Those two traces contain the actual
Ω_(1,2)† and Ω_(5,2)† respectively. No central moments may be independently
averaged. Final central parity is 3+3 curvature and requires one coframe
per anchor in surviving terms, with maximum degree four per chiral group.

Each of page0's two coframes on side edge 1–0 is centered at 1. They arise
from the different E_(1,12) and E_(1,23) frames. At hub 5 the corresponding
E_(5,12), E_(5,23) provide both coframes on 5–4. A product is symmetric
in both internal vector labels at that hub, independently of its
coefficientwise Haar weight; the actual curvature and inter-page
contractions still couple those ten-dimensional symmetric pairs. There
is no independent scalar delta reduction. Keeping degree-two exterior
masks (28 per hub), two 2×2 fundamental entries (4 apiece), two chiral
labels (2 apiece), both symmetric pairs (10 apiece), and two copy pairs
(6 apiece, or 3 apiece at fixed chiralities) gives 180,633,600 cells before
the locks and 45,158,400 after. The latter is 3,600 fixed-choice slices of
12,544 mask/spin-entry cells. It is a complete declared index shape rather
than a support census or an estimate of the contraction budget.

The two hubs give [28·15·6]^2=6,350,400 ordered disjoint page-mask
triples; the central mask is the unique complement at each hub. Fixing
one initial page mask at hub 1 gives 28 slices of 226,800. This tally covers
only wedge compatibility. It sets no bound on full compact, internal
gamma-vector, chirality, copy or other index joins. The optional universal
local verification table bounds also agree: at most 32 raw products per
canonical component, 36 such components, at most 128 products per
mixed-Hodge input, and 18·36·4=2,592 typed bytes with a separate denominator
4 for the reconstruction. No table is needed for the analytic rank.

The full core value, sign, possible zero, support and complete contraction
cost remain unqualified. Original physical TT/Ward/pole, boundary-product/
adjoint/seam/causal transfer and other downstream clauses remain open. No
scientific execution or recomputation, no repository or notebook change,
and no current peer verdict was used.

## Readback

The first pinned R2 continuity command returned SAME. Commands were
python3 scripts/codex_continuity.py check with the exact primary packet,
cat/sed/rg/tail for ordinary source and notebook text, git status/rev-parse,
and shasum/wc for byte checks. Final clean HEAD, exact candidate hash and
SAME continuity were read back before delivery.
