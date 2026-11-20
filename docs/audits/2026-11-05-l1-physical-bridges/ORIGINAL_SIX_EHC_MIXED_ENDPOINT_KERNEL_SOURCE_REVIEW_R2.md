# ACTUAL original-source review — mixed kernel and projected bulk, R2

**ACCEPT equations (1)–(15), the two original signed controls, and the complete
bulk count/bounds** at clean source 9ac8bd5680cfaa774fb4e24b79a32593b07e49bc.
R2 proof: 18,783 bytes, SHA256
4d85f14d098920ca1f401f29903bfcf30e81e60db86d2a5ca8b3762237e3bfca.
The undefined B0/B2 control references in R1 are resolved in R2.
The core value, sign and whole-core contraction resources remain unknown.


## Original source kernel and two distinct controls

Compared the accepted aggregate and normalization in
ORIGINAL_SIX_EHC_SIGNED_SECTOR_REDUCTION(_ACCEPTANCE).md,
ORIGINAL_SIX_EHC_SUPPORT_CONSTRUCTION.md, and the original coframe,
Hermitian vector and top conventions in ORIGINAL_NONZERO_NORMALIZATION_CONSTRUCTION.md.
The primary notebook binds the accepted full-source sum, 22 mixed free edges and
the two actual time-separated source edges. Equation (2) agrees with the
literal two-anchor formula at both endpoints. At y the U dagger is left of
gamma and the undaggered U right of gamma. Neither equality commutes gamma
through a link, substitutes a single anchor or chooses a gauge.

For Haar of active chirality L with two forward terms, write
q_A† at x with indices i,p, U† with p,j, U† at y with k,q, q_B with q,l.
The epsilon moment is E_pk E_jq/2. Grouping the fields into x then y permutes
one odd pair, giving exactly −B_x P_y/2. A forward/backward term has the
explicit minus and one odd interchange after regrouping, so using the mixed
delta moment gives +M_x M_y/2. Backward/forward similarly gives +N_x N_y/2.
For backward/backward, ordering the x psi_R,psi_L pair and y bar_L,bar_R pair
gives the stated −P_x B_y/2. Switching L/R interchanges the mesonic cases
and uses both bar and psi versions of determinant-one pseudoreality in the
pair cases. The two antisymmetry signs transport the same coefficients, not
two further minus signs on the whole expression. Independent chirality and
anchor means kill the mixed terms. Two same-anchor terms (inversion for V)
with the held 1/4 factors give precisely H/8.

In the mixed control at A=B=3, the coefficient of the stated odd-ordered
monomial in the bar vector and psi vector is −1 in each. Thus the coefficient
of −B_x P_y in H is −1. Its physical coefficient is −1/8 or −4 at scale 32.
This uses H rather than a delta times the same-endpoint scalar.

The fundamental obstruction (8) concerns actual Ω_(0,2)† and Ω_(4,2)†,
each first in its own H_(z,02) and independent. Their opposite endpoints
are precisely the two source centers available in the sum on that edge.
In the Qx cross term the two desired forward factors are q_A† U† and
q_A† V, multiplied by the original −2/16. For the held monomial, the
top extraction gives −E_st E_ab before the moments, with s,t the two bar
and a,b the two psi indices. The two test-matrix moments are E_pi E_aj/2
and δ_rl δ_bk/2 when the forward factors have link slots (p,a) and (r,b).
Summing q_A†_(sp) q_A†_(tr)=2E_st E_pr leaves −δ_ilδ_jk before −1/8.
The same-anchor terms have odd independent anchor degree. In Qy the selected
L group uses the other chiral endpoint fields and cannot give the monomial.
All four indices 1 give +1/8. This defeats a universal pull-through
annihilator against fundamental data, while leaving actual correlated core
transport unevaluated.

## Original top and algebraic colors

Sharp conjugates and reverses the two odd factors, giving M#=N and B#=−P.
The displayed V are accordingly Hermitian in the held sharp. Expansion
of the sign-weighted V sum gives the complete original mixed H with coefficient
matrix diag(1,−1,1,1)/2 and determinant −1/16. The physical matrix is this
divided by 8. The four copies are distinguished by local meson or bar/psi
pair support. Their copy signs are separate from physical source eta and
from internal gamma or world orientation signs.

The literal odd-order grouping for M,N,B,P is
bar_R,psi_L,bar_L,psi_R,bar_R,bar_L,psi_L,psi_R. Grouping into the held top
has odd parity and produces the four E contractions. For X=q_A†,Y=q_B,
Z=q_C†,W=q_D those contractions give Tr(X^T E Z Y E W^T). Using
det-one pseudoreality gives −Tr(q_A q_C† q_B q_D†). The quaternion products
for distinct 0,1,2,3 yield −2 times the permutation sign for the trace,
hence +48 for the epsilon contraction. The two copy changes have determinants
−2i and +2i, product 4. This yields +192 with the site bars-before-psis top
and reproduces 3^16 2^-32 N_Q4 in the original all-linear normalization.
Even bilinears and eight-mode site blocks can be regrouped without extra signs.

## Core/bulk, cross-edge orders, and Gram

The ten curved edges of the accepted six unit classes leave the eight
claimed bulk sites, with ten internal edges and twelve cross spokes.
The three paths from 10 to 14 go via (2,6), (8,12), (11,15), using outer
directions 3,1,0, respectively, plus the direct axis-2 edge. These vertices
and edge directions come from XOR by the relevant bit, with no time reflection.
Every curvature-free edge has two opposite endpoint coframes. On the four
edges where E_(0,02) or E_(4,02) supplies one, D at the bulk endpoint supplies
the other. All others have D at both ends.

Absorb the four sign matrices incident at each even bulk site 10,6,12,15.
The four determinant signs multiply to +1. Each of the six residual signs
is on a boundary leg at odd leaves 2,11,8, thus giving the product of their
three pair signs. Eight site integrals yield 192^8 and the 22 free-edge
physical coefficients yield 16^-22. This is 3^8 2^-40, with no quarter or
other mixed-kernel factor to append to a boundary slot.

Sorting external world axes and reading the hub axes in ascending order
gives the leaf permutation signs (−,+,−) for directions (3,1,0) on each
half. The lower cycle directions in order are (1,0,3,1,0,3).
Its ordered bulk pairs are (c1,c0),(c3,c2),(c4,c5) at 2,11,8, respectively.
The ordered core pairs are (c0,c5),(c1,c2),(c4,c3) at 0,3,9.
Xor4 preserves all these world directions and the pair storage order in
the upper cycle. For all six pairs (0,1), either alternating cycle coloring
gives three negative incidences overall modulo two, so R=−2. Expanding the
antisymmetric boundary components in the integer E_(a,b) matrices on both
sides is exact ordered-index reconstruction. It introduces no 2! or 1/2.

Pair parity is the XOR of the three canonical pair masks. At either half each
local epsilon contains all colors, and internal edges cancel in the XOR.
On a cross cycle each individual color is counted once at each end. Therefore
B and R preserve kappa, and the eta signs left on the three lower pairs are
constant as D_k=(−1)^(k_color1), including the negative all-ones mask.
Identical halves give T^T T in real coefficient coordinates and the complete
each-block matrix is D_k (TR)^T(TR). This is a coefficient Gram statement.

For the explicit star core column at pairs (01,02,03), its core pairs have
one 0 each. Each intervening bulk pair must avoid (0,0), so the three zeros
must meet the three bulk pairs once each, forcing the two alternating
choices of sides. The resulting bulk label orders (01,02,03) and (02,03,01)
both give R=-1. In path order (0,1,3), use p=(1,2,3),(3,1,2) for the first
column; their J products times the hub sign are −,+. For the second column
use p=(1,2,3),(2,3,1); their products are +,−. The columns' common lambda
(0;1,2,3) cancels in the sum, with the two remaining lambda entries of
opposite sign and unit magnitude. The squared norm is 2 so the signed
W_star diagonal entry is −2. This tests orientation and coordinates, while
providing no sign or nonzero result for the core component.

For the three-pair domain the even-mask counts are 24,24,28 each for the
six weight-two values. Distinct-edge triples giving mask 0 or 1111 are
triangles or stars, and a weight-two mask has 12 ordered simple-path triples
plus 16 repeated-edge triples. The lambda tuple counts 40,24,32 follow
respectively from four-equal/two-pair tuples, all-distinct tuples, and the
two odd colors appearing in patterns 3+1 or 2+1+1. Thus 5856 potentially
nonzero ordered W cells and 6912 T/G-compatible storage positions. At most
eight T choices per column, eight R raw choices per row or column, and a
unique lambda per surviving T choice give the stated construction ceilings
1728+1728+13824+187392=204672. The W term uses 40*24^2+24*24^2+6*32*28^2.
The G-column norm is ≤8sqrt(8) by the triangle inequality, so Cauchy
also bounds a sum of absolute Gram summands by 512. Signed i16 suffices
for W, signed i8 for T/G; the 25,536 typed bytes exclude storage overhead
and the bounded products exclude machine/runtime/serialization costs.

## Exact remaining original integral

The original six EHC angle traces retain the full gamma_[C gamma_D] gamma5
and ordered four-anchor H. The world epsilon on (02;13) is minus, on
(12;03) and (23;01) plus, each occurring at two centers. Their unit class
multiplicities have factorial divisor 1, with neither a second world-placement
quarter nor a new permutation factorial. In the six boundary pairs the
external order is E frames 1,3 at 0/4, D axes 0,3 at 3/7, D axes 0,1 at
9/13. F antisymmetry or the D epsilon and even bilinear commutation give
each exact core antisymmetry, even with the other shared factors held.
Four residual D supply eight curved T slots, four internal E supply eight
and the full source product supplies four. These 20 T retain original quarters
on ten edge pairs with 20 independent anchors. The other twelve factors are
V, yielding together the 64 odd slots of eight original site tops. Per-chiral
center parity on the actual central 3+3 and other 1+1/2+0 curvature copies
retains the fixed-word degree-four moment ceiling; it sets no global guard
or core join estimate.

Thus h12,6 = 8·3^8·2^-40 Σ W Ccore with the full ordered block contraction
and actual source time0 and time1. There is no omitted factorial, physical
eta, slice swap or scale. The scalar table bounds are for the bulk only.
The actual correlated core support, total join size/resources, sign and
value remain open, as do the original uncapped normalization and physical
boundary/adjoint/seam/causal/TT conditions. There was no scientific
program execution, artifact generation, or repository/notebook write.

## Readback

Opening continuity check was SAME. Commands were the pinned continuity
checker, cat/sed/head/tail/rg/jq for ordinary text and the anchored source
notebook, git rev-parse/status, and wc/shasum for byte/hash readback.

The old R2 continuity packet and the new R3 continuity packet both checked
SAME. The proof diff adds only the nine lines defining and deriving B0/B2.
All prior source and mathematical observations in this report therefore
apply to the unchanged equations.

For B0 at bulk pairs (01,01,01), every p is confined to the common
complement {2,3}. The hub epsilon requires three distinct p colors, so the
column vanishes. For B2 at bulk pairs (03,01,02), the path-order pairs
are (01,02,03) with p domains {2,3},{1,3},{1,2}. The only all-distinct
p tuples are (2,3,1) and (3,1,2). Their complements give different s
tuples in the declared path order and c=0. Each hub epsilon and each J has
unit magnitude, so their two squared entries sum to 2. These are exact
ordered-coordinate controls, with no generated table or use of peer
current verdicts.

Final readback was SAME at the clean pinned source. Both proof versions
retained their observed byte counts and SHA256 pins.
