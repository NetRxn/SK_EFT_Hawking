# L1 two-site source-only shear response

For one once-pair shear source H at either site, coupling the longitudinal direction to one of three transverse directions, the literal two-site partition polynomial is Z(H) = 3366 g₂⁴ + (45/4)g₂²H². The second derivative is (45/2)g₂². At nonzero g₂, the six-coordinate Hessian of log Z is 5/(748g₂²) times the identity. For a full-symmetric source coordinate with H = 2K the diagonal is multiplied by four.

The [exact contraction](l1_offdiag_hessian.py) gives 15 per complementary curvature direction. The three directions and the action-square factorial give the stated second derivative. Omitting an independent endpoint changes the scaled derivative to 9/2. The [support enumeration](l1_offdiag_hessian_support.py) accounts for all 36 entries. Same-site distinct shears vanish by center parity. The intersite and linear survivors contain an independent mean-zero curvature. Saturation and parity exclude the g₁ contributions.

Independent adversarial review reproduced the exact calculation and separately checked the support and normalization, including the factor of two between the quadratic coefficient and the second derivative. This is a finite static source response. Physical tensor projection, volume and vacuum limits, operator normalization and RPA matching remain open.

## Independently verified projection and normalization

Let e be the elongated axis and assume it is spatial. A nonzero shear in this block is S = e⊗w + w⊗e with w perpendicular to e. It is traceless, and Sn = e(w·n) + w(e·n) for unit propagation direction n. It is transverse precisely when both dot products vanish. The only nonzero spatial lattice momenta lie along e. The transverse projector kills this shear block at those momenta. If e is Euclidean time, the block consists of time-space shears. At zero momentum, an algebraic TT cross polarization can be selected with an externally specified transverse limiting axis.

For a Frobenius-unit symmetric shear, the once-pair coordinate of a physical source of amplitude η is H_j = 2a²Z_Qηw_j, with squared norm of w equal to 1/2. Dividing the uniform source Hessian by 2a⁴ gives the conditional density 2Z_Q²h = 5Z_Q²/(374g₂²), where h is the site-diagonal Hessian entry. This uses the matched-operator convention and leaves normalization, contact subtraction, and operator mixing to the physical construction.

The next finite tensor target uses the site-resolved sources G₂₃ and G₂₂−G₃₃, where e is direction 1 and the remaining spatial polarization plane is 2–3. For signed action terms g₁A + g₂B of degrees eight and four, the degree-sixteen top extraction gives Z_u from G_u(g₁g₂AB + g₂³B³/6) and Z_uv from G_uG_v(g₁A + g₂²B²/2). Evaluate the connected combination Z_uv/Z − Z_u Z_v/Z² before projecting the symmetric and antisymmetric lattice characters.

Independent adversarial review checked the transversality and once-pair factors. This result gives a finite static projection and specifies the missing nonzero-momentum channels.

## Independently verified transverse block

The [support enumeration](l1_transverse_support.py) excludes the linear and g₁ quadratic terms. The [exact numerator calculation](l1_transverse_top.py) gives local moments H² = 9 and D² = 21 for H = G₂₃ and D = G₂₂−G₃₃. Three opposite-site curvature squares and the action factorial multiply these moments by 54. Dividing by the finite partition function gives the site-diagonal log Hessians 27/(187g₂²) and 63/(187g₂²), respectively.

Exchange of the two selected transverse directions makes the same-site mixed coefficient odd. The only intersite cross survivor has complementary curvature links separate from the source links. Haar averaging of the longitudinal conjugations leaves a zero mixed scalar-vector moment for each independent complementary link. All other intersite terms vanish by support. Independent review checked these zero contributions and reproduced the diagonal moments.

The coincident-link frame is {γ,U†−U}/4. A separate exact spherical quadrature gives the diagonal fourth moment 75/2 and detects the earlier incorrect frame expression, which yields 15/4. The corrected block has two positive but unequal responses. Frobenius-unit cross and plus polarizations give conditional source densities 54Z_Q²/(187g₂²) and 63Z_Q²/(374g₂²) for either two-site Fourier character. Physical operator matching, contact subtraction, larger volumes and real-time continuation remain open.

## Independently verified separate-time source control

On a 2×2×1×1 torus with separate time and propagation axes, set g₁ = g₂ = 0 and anchor the unused spatial column with unit local transverse trace sources. In the active column, t and s are the two time-metric sources and h and k are the local once-pair transverse cross sources. Site saturation and independent transverse-link center flips permit only time degree four or two cross insertions at each site. The full partition function is (129/2)² times the active-column polynomial Q₄(t,s) + 81h²k²/4. The constant factor cancels in connected derivatives.

The [exact composition check](l1_time_space_source_control.py) uses the previously reviewed longitudinal Q₄, with Q₄(1,1) = 6477/32, and the exact local transverse moments. At t = s = 1 and h = k = 0, the time-separated mixed two-point derivative is zero and the mixed fourth derivative of log Z is 864/2159. A local trace-only control gives zero for both separated derivatives and 6/43 for the local second derivative. The fourth derivative is in once-pair source coordinates and is multiplied by four for Frobenius-unit cross sources.

Independent review checked factorization, saturation, the prior polynomial, and exact derivatives. This is an externally sourced, zero-interaction fourth cumulant. The interacting source-free two-point response and transport extraction remain open.

## Interacting pure-g₂ support and one-point symmetry

At zero sources and g₁ = 0, the [four-site support enumeration](l1_interacting_support.py) tracks site saturation and center charge of actual links, including repeated link occurrences. It finds 73,295,320 ordered normalization candidates at degree eight. For the degree-six cross numerator, the same-site, nearest time, nearest space, and diagonal support counts are 51,930, 0, 0, and 92,160. Empty support proves an exact numerator zero. Positive counts bound candidate support and still require coefficient evaluation.

Conjugate every link and transform both Grassmann factors by the constant Pin matrix γ₄. This exchanges chiral Haar factors and preserves the Berezin measure. The internal frame rotation has determinant −1, leaves metric sources invariant, and flips γ₅ in the conjugated action trace. Hence the odd pure-g₂ coefficients vanish even with arbitrary metric sources. In particular both degree-seven one-point numerators vanish. With g₁ present the symmetry reverses both couplings together.

Independent review reran the support enumeration and checked the Pin change of variables. The connected nearest cross response is zero wherever the full source-free normalization is nonzero. The support count alone does not establish that domain. Nonlocal surviving coefficients, full normalization and physical transport remain open.

The independently reviewed [normalization sector](l1_interacting_controls.py) selects two action insertions at each site with time-space curvature and transverse self-link frames. Local saturation gives 24 times the sum of the two chiral curvature weights. After expansion into trivial and adjoint characters, every proper nonempty subset has an exposed Haar edge. The all-adjoint contribution in either single chirality integrates to 1/81. Including the four factorials gives exactly 104978 as one contribution to the degree-eight denominator. Other signed sectors remain unevaluated, so this contribution does not establish full normalization.

The independently reviewed [nearest-plus enumeration](l1_nearest_classes.py) finds 128 unordered degree-six multisets, representing 11,520 ordered terms. In each multiset both transverse link variables are absent at one source site, as checked by actual incidence before parity reduction. At that site the two local diagonal sources have identical conditional Haar integrals, so their difference vanishes coefficientwise. The nearest-time plus numerator is therefore zero, and time-space exchange gives the same nearest-space result. The connected statement requires nonzero full normalization. Diagonal separation remains open.

The independently reviewed [diagonal support classification](l1_diagonal_classes.py) leaves 128 multisets after the unused-source Haar cancellation, in 28 symmetry orbits. The [partial evaluator](l1_diagonal_fixed_link.cpp) computes one orbit representative at rational unit link values modulo 65537. The fixed-link residue is 33007. Exact cubature of both chiral factors of link (0,0) gives residue 37858 with all other links fixed. This proves that the representative survives that partial projection. Orbit equivalence applies after all links are integrated, or when fixed link data are permuted with the orbit. The residues do not include the remaining Haar integrals or exponential multiplicities and do not establish a full numerator.

The independently reviewed [isolated transport-link pair check](l1_diagonal_edge_pair_symbolic.py) applies exact degree-two Haar averages to two isolated extended links and finds all 96 antisymmetric components zero after local saturation. This explains how the nonzero one-link residue above can vanish under a subsequent projection. The reviewed incidence classification removes 28 multisets across six orbits, leaving 100 multisets in 22 orbits for signed evaluation.

The [center boundary calculation](l1_diag_center_factor.cpp) factors a selected diagonal orbit into two centers connected through two shared singleton links. It retains 64 bilinear boundary coordinates and 784 pairs of two-form masks. The [signed quartic cubature check](l1_quartic_projection_rule.py) verifies all 330 homogeneous degree-four monomials over the rationals with 56 nodes. Independent reruns over the field of order 65537 measured rank 34 and 8440 nonzeros before projection, rank 19 and 936 nonzeros after one internal link, and rank 17 and 312 nonzeros after two links. These are ranks of the selected modular matrices. They give lower bounds for the rational ranks under valid reduction. Remaining internal links, the second center, source insertions, and the full orbit sum remain to be contracted.

The [dual-embedding support enumerator](l1_sparse_center_parity_dual.cpp) reduces one isolated center tensor from 50,176 possible boundary slices to 320 supported slices. The [exact evaluator](l1_sparse_center_dual.cpp) recovers bounded Gaussian integer action coefficients from both embeddings of the imaginary unit modulo 65537, then sums the Haar moments in integer arithmetic with common denominator 48⁴. Independent review checked the coefficient bounds and rebuilt and ran all 320 distinct support slices, each returning exact zero. This certifies the full isolated center tensor. The [incidence classifier](l1_sparse_center_cancellations.py) applies it only where no other action factor or source touches the center's four internal links. It removes 14 multisets across three orbits, leaving 86 multisets in 19 orbits. The full diagonal numerator and normalization remain open.

The next [mixed-curvature center](l1_sparse_center_mixed_dual.cpp) has [608 supported slices](l1_sparse_center_mixed_parity_dual.cpp). The [indexed projection receipt](l1_sparse_mixed_projection_indexed.txt) has 24 nonzero entries. The [Gaussian rational join](l1_mixed_center_contract.py) contracts 72 ordered slice pairs and gives 25/49152 for the representative, with zero imaginary component. The six action factors are distinct and their exponential weight is one. The two-member orbit contributes 25/24576 to the degree-six unnormalized diagonal plus numerator. Independent review reproduced the nonzero center entries and the full complex contraction. Eighteen orbits remain, so the total numerator may differ or vanish.

The independently reviewed [shifted two-center calculation](l1_shift_group_contract.py) evaluates all eleven orbits in this family. The six exact center receipts are checked by [l1_shift_receipt_verify.py](l1_shift_receipt_verify.py). Three shifted same-curvature tensors vanish on their 320 supported slices each. Three shifted mixed-curvature tensors match the reviewed base on all 608 slices each, including 24 nonzero entries. Four same-curvature orbits contribute zero. The seven mixed-curvature orbits contribute 25/1536 in total, including the previously evaluated two-member orbit. Eight orbits and 36 multisets remain. The full numerator and denominator are open.

## Full raw diagonal plus numerator

The remaining eight orbits (36 multisets) contribute `-3563/27648`.
With the shifted family, the coefficient of `g2^6` in the unnormalized
diagonal plus numerator on the pure-`g2` torus is `-3113/27648`.
The support accounting is 182 + 28 + 14 eliminated, 50 shifted, and 36
residual, for 310 multisets. The pin kills the one-point term.
Independent review rebuilt both batched families and matched every row
(16,256 same and 34,048 mixed), then checked all 432 nonzero source
covariance entries against a direct nested Haar sum. The normalized
response requires the full degree-eight denominator. Physical retarded
matching and B3 acceptance remain open.

To reproduce, set `audit` to the absolute path of this audit directory
and run from a scratch directory. The generated row tables are scratch
outputs.

```sh
c++ -std=c++20 -O3 "$audit/l1_residual_batched.cpp" -o l1_residual_batched
./l1_residual_batched 0 > l1_residual_batched_same.out
./l1_residual_batched 1 > l1_residual_batched_mixed.out
python3 "$audit/l1_residual_sparse_sources.py"
python3 "$audit/l1_residual_source_control.py"
```

## Degree-eight normalization support

Run `python3 l1_normalization_support.py` from this directory to enumerate
the denominator support. Each sorted eight-tuple has a unique sorted
four-plus-four split. Matching equal parity and complementary site degrees
leaves 6,451 multisets. Their multinomial weights reconstruct the separate
ordered count of 73,295,320. The exponential expansion weights each
multiset by the reciprocal product of its multiplicity factorials.

Translations partition the support into 1,758 orbits. The largest
polynomial degree on any one link is four in 1,267 orbits, six in 425,
and eight in 66. An evaluator for quadratic and quartic Haar moments
therefore covers the link degree requirements of the first group.
Degree six and eight moments are required for the rest. These counts
specify the integration domain and do not evaluate the signed sum.

Independent review reproduced the ordered count with a separate half-state
dynamic program, verified uniqueness of the sorted split, and checked the
translation count by Burnside's lemma using fixed counts 6,451, 185, 185,
and 211. The review checked the action orientation and exponential
multiplicity conventions. Denominator evaluation remains open.

For an integer contraction in the original link coordinates, a single
Spin(4) link admits moment scales 4, 48, 192 and 11,520 in degrees two
through eight. These are the least common multiples of products of the
two normalized quaternion moment denominators over even chiral degree
splits. Multiplying by the multiset factorials and taking the least
common multiple over the inventory gives 53,851,443,515,311,584,706,560,000.

A candidate contraction reduction is to fix an extended-link spanning
tree before expanding each multiset. For a gauge-invariant Berezin
integrand, tree link variables can be absorbed by site rotations, with
unit Berezin Jacobian and unchanged normalized Haar measures on the
remaining links. For this reduction, gauge covariance must be checked
for the individual origin-labelled frame blocks as well as the summed
action. The support enumerator profiles the 32 possible trees and
reports the smallest remaining total polynomial degree for each orbit.
The profile ranges from 30 to 42, down from 48 before fixing links.
This profile measures possible savings. It does not apply gauge fixing
or evaluate any signed integral.

Independent review obtained the same common scale by enumerating reduced
quaternion moment denominators and taking the least common multiple over
all 6,451 multisets. In the evaluator convention that absorbs 16 into
each action factor, this scale clears the scaled sum. The original sum
uses the additional factor 16⁸. A nonzero residue modulo 65537 would
certify nonzero normalization without recovering the exact signed value,
since the prime divides neither scale. Retain both imaginary-unit
embeddings when resolving complex coefficients.

The [tree covariance control](l1_tree_covariance_control.cpp) rules out
applying this shortcut multiset by multiset to the literal action.
Build with `c++ -std=c++20 -O3`. A one-site Spin(4) rotation under the
Wilson link law changes a supported multiset's top exterior coefficient
from 36,770 to 10,060 modulo 65,537. The spin change of variables has
unit Berezin determinant. The discrepancy is consistent with the
opposite link orientation used by the extended frame blocks. Continue
the signed contraction in the original link variables. This control
does not test invariance after summing the full action.

Independent review rebuilt the control and reproduced both residues.
It verified the word is in the normalization support with weight one,
the start-left/end-right Wilson link law, and the unit determinant of
the spin rotation. The conclusion concerns pointwise termwise covariance.

## Link-disjoint transport squares

The [exact sector evaluator](l1_normalization_disjoint_sector.py)
identifies 16 multisets with a squared transverse curvature factor at
each site and bijective assignments of both extended transport link
anchors. The four factors share Grassmann sites but have disjoint Haar
variables. Switching an anchor replaces the raw frame by its negative
with the link inverted, so the squared factor has the same integral.
Contracting the four degree-eight exterior tensors gives integer top
coefficient 27,252,495,206,055,936 in units of `9216^-4`. Each multiset
contributes `17/72` after its four `2!` factors. The sector adds
`34/9` to the pure-g₂ degree-eight normalization. It is distinct from
the all-local sector above. The remaining signed sectors are open.

Independent review reproduced the exact coefficient and checked the
16-word membership by link incidence and by counting the two anchor
choices for each of four extended site pairs. It also checked the
incoming and outgoing Haar second moments and the antisymmetric
curvature covariance. The exterior join retains the shared Grassmann
sites and their signs.

## Equal-extent world-axis swaps

The normalization enumerator also partitions the support under
translations and swaps within the two equal-extent axis pairs.
Reordering the curvature axes reverses the plaquette, sending the
traceless chiral curvature projection to its negative. Reordering
the frame axes exchanges the two degree-two factors and changes the
sign of the antisymmetric internal contraction. These signs cancel
the corresponding changes in the world epsilon when restoring sorted
indices. Thus a world reflection changes each action factor by the
common orientation sign. Eight factors cancel it. Link Haar variables
and whole eight-generator site blocks are merely permuted.

The resulting 652 representatives have orbit sizes 1, 2, 4, 8 and
16 with counts 5, 17, 117, 283 and 230. Independent review reproduced
the partition for every member and verified the curvature, frame, and
orientation signs.

## Opposite-site fourth powers

The [quartic sector evaluator](l1_normalization_opposed_fourth.py)
covers all 32 multisets with multiplicity profile `(4,4)`. Each is
supported on two opposite centers with disjoint Haar variables.
The degree-four quadrature and the commutator curvature moment produce
38 exterior terms per center after selecting local saturation.
The exact exterior join gives `20339/129600` per word after the two
`4!` factors, or `20339/4050` in total. Independent review reproduced the coefficient,
checked all 330 homogeneous fourth moments of the signed cubature, and
derived the needed commutator moments directly.

## Four-factor components sharing one transport link

The [component evaluator](l1_normalization_shared_transport.py)
integrates private transport links by second moments and the shared
link by its joint fourth moment. Four cached symmetry representatives
cover the 32 distinct shared components. Signed exterior joins of
the integrated components give `56/3` from 64 multisets with component
sizes `(2,2,4)` and `12` from 32 multisets with sizes `(4,4)`, for a
new contribution of `92/3`. The same assembly reproduces the two
earlier disjoint transport sectors.

Independent source review checked membership, the signed quartic rule,
the per-center scale `1/4608`, and the exterior relabeling sign.
The remaining connected sectors still require evaluation.

The independent exact rerun reproduced both new subtotals and both
previous transport sectors.

## Shared singleton curvature links

The same evaluator covers 384 additional multisets with adjacent
mixed-plane squares. For distinct singleton axes, private Haar links
make the two curvature covariances independent. For the same singleton
axis, the code conditions each curvature on the shared pair and
integrates their joint polynomial. The independent check recovered the
same- and cross-chirality norm controls `41/72` and `9/16`.

Independent evaluation and the consolidated checkpoint both give
`63369/32` from 160 mixed-only multisets and `2195447/384` from 224
same-containing multisets. The latter includes 64 with both structures
and counts them once. With the previous transport terms, the evaluator
covers 528 multisets with subtotal `2005445321/259200`. The separate
104,978 all-local contribution is outside this subtotal. The full
normalization is open.

## Repeated commutator curvature

The component evaluator covers 168 further multisets made from
four-factor components with two squared labels sharing the same
commutator curvature. It integrates the common curvature with its
fourth moment and retains a joint fourth moment for any shared
transport link. The clean consolidated run gives `188663/2700`
for these terms and `2023556969/259200` across the 696 covered
multisets. Independent review reproduced the exact subtotal, verified
the two-square multiplicities and common curvature fourth moment, and
checked the separate private and shared transport normalization factors.

## Complete two- and four-factor link components

The component evaluator adds 178 multisets with a four-distinct-label
component. It pairs the four endpoint choices at a single center by
rows and columns, or uses paired incoming and outgoing frames at
adjacent centers. Their signed contribution is `37483/240`. This
includes the 24 words that also contain a repeated-commutator component,
with each word counted once in the complete sum.

Independent review checked the component incidence, both integration
rules, the antisymmetry signs, and the exact subtotal. The complete
two- and four-factor link-component population is 874 multisets with
subtotal `2064038609/259200`. The 5,577 words with larger link components
include the previously evaluated all-local word. Evaluate the other
5,576 using the original link variables. Factor each action into its
curvature and two frame blocks to eliminate link moments before
forming large exterior products.

## Six-factor transport chains

The [chain evaluator](l1_normalization_six_transport.py) integrates
each shared link with its joint fourth moment. Eliminating the two
outer centers reduces each shared-link tensor from 3,952 exterior
terms to 336, and the middle contraction leaves 84. The
[direct moment control](l1_normalization_six_moment_control.py)
reproduces three shared-link entries coefficient by coefficient using
exact symbolic Haar moments. The 64 distinct `(2,6)` multisets
contribute `3/8` each, including factorial weights, for subtotal
`24`. Independent review checked all 64 incidences and normalization
factors. This sector is separate from the 874 smaller-component words.

## Equal-time plus benchmark

The 185 same-site support words separate by action degree on the two
local transverse source links. The populations for degrees `(0,0)`,
`(0,2)`, `(2,0)`, `(0,4)`, `(4,0)` and `(2,2)` are 1, 20, 20,
26, 26 and 92. The sole `(0,0)` word squares the time-space
curvature action at each of the other three sites. The local source
integral is 21. Each action pair gives 24 times the two chiral
curvature weights, with a factor `1/2!` from the exponential.
Every nonempty adjoint face selection is a proper subset of the
four-face tiling and has a singly exposed link. Its Haar average
vanishes. The remaining trivial curvature weight is `(3/2)^3`.
The saturated site blocks commute, giving contribution
`21 × (24/2)^3 × (3/2)^3 = 122472` to the raw equal-time numerator.
This evaluates one word. The remaining contractions and physical
contact subtraction are open.

The [benchmark script](l1_equal_time_local_benchmark.py) checks the
incidence census and all seven exposed-edge cases. Independent review
reproduced the source moment, local action pairing, and positive
site-block join sign.

The [mixed-plane chain evaluator](l1_normalization_six_mixed_chain.py)
adds 256 disjoint `(2,6)` words. It joins a pair of mixed-plane squares
to a transverse curvature square through a shared extended link. The
exact checkpoint run gives 163 from 128 same-singleton words and 162
from 128 distinct-singleton words. Independent source review verified
all incidences, shared Haar moments, and factorial weights. The signed
increment is 325.

## All-transverse-curvature transport cycle

The [cycle evaluator](l1_normalization_transport_cycle.py) contracts
all 752 words with two transverse-curvature labels per site. It
integrates the actual shared links before saturating each vertex.
The split-edge slot swaps leave one invariant parity around a fully
split cycle. The two eight-word parity classes give distinct
per-word coefficients `32/27` and `28/27`, an exact check that the
cycle pairing is retained.

The exact run gives `38842/81` across the family. The 184 smaller
component words and 64 pure six-factor chains were already counted.
The increment is 504 words with subtotal `32380/81`, disjoint from
the mixed-plane chains. Independent review reconstructed the
population from endpoint choices and checked overlap, Haar scaling,
and site elimination signs. The deduplicated subtotal including
the all-local word is `29468413009/259200` across 1,699 words.
The other 4,752 signed contributions remain open.

## Private-curvature elimination

The [incidence reduction](l1_normalization_private_curvature.py) removes
a squared curvature if an otherwise unused link occurs once in its
plaquette, making the plaquette conditionally Haar. A commutator square
can instead be integrated when both its links are private. The
[exact path contraction](l1_normalization_private_paths.py) retains
the remaining transport moments and signed Grassmann joins.
Independent review reversed the curvature elimination order, recovered
the same 1,408 words, and reran all exact contractions. The 288 overlaps
reproduce the earlier subtotals. The 1,120 new words contribute
`8071653/32`. The signed full denominator remains open.

The [paired-label extension](l1_normalization_paired_curvature.py)
also allows different frame endpoints for two factors sharing a
curvature plane. Its [ordered path evaluator](l1_normalization_paired_paths.py)
contracts 824 words. The 32 overlapping words reproduce 54. The 792
new words contribute `535869/4`, including 108 from 64 size-`(2,6)`
words and `535437/4` from 728 connected words. Independent review
reversed the Haar elimination order and verified the same selected
population, actual link incidences and factorials. The remaining
transport graphs are forests, so local slot swaps can remove pairing
flags with no closed-cycle constraint.

The deduplicated subtotal is now `129573113509/259200` over 3,611
words. The 2,840 remaining signed words can still affect the sign and
nonvanishing of the normalization.

## Correlated curvature pairs and odd commutator zeros

The [incidence classifier](l1_normalization_correlated_cases.py)
selects 1,240 additional connected words. After private-link
integration, each retains one or two isolated opposing curvature pairs.
The [ordered contraction](l1_normalization_correlated_contract.py)
keeps both ordered gamma ports of each conditional covariance, attaches
transport moments, and joins complementary exterior masks. The exact
checkpoint result is `3343619/54` for 1,072 one-pair words and
`4277609/144` for 168 two-pair words, totaling `39581779/432`.
Independent review checked the disjoint incidence, covariance symmetry
under port reversal, forest slot swaps, and rational scaling.

The [odd commutator census](l1_normalization_odd_commutator.py) selects
800 distinct pure transverse-curvature words with site counts
`(1,1,3,3)`. At any odd site, exchanging its two independent singleton
links sends the commutator to its inverse and reverses its traceless
curvature vector. The transport factors only use extended links, so
the Haar-preserving exchange negates the integrand. Each word vanishes
exactly. Independent review reproduced the population and checked
its disjointness from earlier sectors.

These increments bring the accounted population to 5,651 with signed
subtotal `153322180909/259200`. The full denominator still requires
the remaining 800 words.

The same ordered contraction covers 64 further size-`(2,6)`
words. The census excludes the 128 matching words already counted
in the mixed-plane chain family. The remaining words form one
canonical plan and contribute `163/96` each, totaling `326/3`.
Run `size_six_total()` from the contraction module to reproduce
the result. Both the scratch and checkpoint runs agree. The
remaining 736 words include four split words evaluated below.

## Reality of fixed-link top coefficients

In the literal chiral basis, let `J = diag(iσ₂,iσ₂)`. The
[symbolic control](l1_link_reality_control.py) verifies that complex
conjugation of every gamma matrix, the chirality matrix, a generic
real-coordinate Spin(4) link and its adjoint equals conjugation by
the same `J`. Trace factors therefore equal their conjugates.
Each frame bilinear with conjugated coefficient matrices is obtained
by replacing the row of barred variables by `bar ψ J` and the
column of unbarred variables by `J⁻¹ ψ`. This sitewise substitution
has unit top exterior determinant. Products of labelled action
factors and real metric sources therefore have real top coefficients
for each link configuration. The Haar integral preserves reality.
This identity leaves the signed magnitude to the contraction.

Independent review reran the symbolic control and verified the
sitewise top exterior change of variables.

## Uniform mixed-plane cycle

The [edge tensor](l1_normalization_uniform_mixed_edge.py) integrates the
degree-four curvature/transport link jointly and the curvature-only
link by its second moment. The [cycle contraction](l1_normalization_uniform_mixed_trace.py)
saturates each site against its singleton frame moments and evaluates
the signed sparse trace for both possible common singleton axes.
The run reproduces 32 words and exact subtotal `6947573/884736`.
The intermediate sparse products are bounded before signed 64-bit
arithmetic, and the final trace uses arbitrary-precision integers.
Independent review reproduced the 32 disjoint incidences from the
physical edge-anchor choices, and checked the world signs, trace
multiplicities and integer bounds. A [direct quartic control](l1_normalization_uniform_mixed_control.py)
matches all 64 exterior terms in each of four edge polynomials.
This leaves 704 unevaluated words.

The [single-link equal-time kernel](l1_equal_time_source_weights.py)
integrates the unused source link in 92 words: 40 with active link
degree two and 52 with active link degree four. Independent exact
review reproduced the eight diagonal degree-two entries, with
`(75,87,87,87)/16` in each chirality, and 36 nonzero quartic entries.
The separate chiral sphere contractions recover the lower moments
and the scalar 21. This removes the local source site from those
action contractions. Their action-dependent integrals remain open.

The [general mixed-plane cycle](l1_normalization_mixed_cycle.py)
retains the physical singleton axis on each edge port and integrates
the joint local singleton moments. Its 16 plane assignments reduce
to four symmetry classes, each summed over 16 extended-link
orientations. The uniform class reproduces the prior 32 words.
The full 256-word sum is `30943735159/764411904`, so the 224 new
words add `24941032087/764411904`. The [vertex control](l1_normalization_mixed_vertex_control.py)
checks the real and imaginary entries for both axis assignments
against direct exact quadrature.

Independent review reconstructed all 256 assignments from link
incidence and checked the signed vertex ordering and Haar scales.
The checkpoint rerun matched the exact totals and all four direct
vertex controls. The deduplicated denominator subtotal is now
`11306987999776927/19110297600` over 5,971 words. The remaining
480 words still determine the full signed result.

The [joint source kernel](l1_equal_time_joint_source_weights.py)
covers the other 92 action words, with degree two on each source
link. The local square terms use the separately integrated link
moments, and the cross term retains the signed exterior join of
the two weighted metric insertions. Exact checks give 73 nonzero
entries out of 1,296, invariance under link exchange, and the
single-link kernel after either chiral sphere contraction. The
checkpoint rerun matches the independent construction. All 184
non-benchmark words now have source tensors for their action joins.

The [checkerboard repeated mixed cycle](l1_normalization_repeated_mixed_cycle.py)
covers 64 more words, disjoint from the all-distinct mixed cycle.
For each edge it retains the joint degree-six moment when the
curvature and transport use the same physical link. The alternative
anchor factors into quartic curvature and quadratic transport
moments. Independent review reconstructed the incidence and checked
three same- and mixed-chirality projection pairs by direct symbolic
quaternion moments. The exact checkpoint trace gives
`136051531/221184` with zero imaginary component. The denominator
now has 416 unevaluated words.

The [equal-time incidence reduction](l1_equal_time_structural.py)
integrates private plaquette links before the source join. It makes
145 words source-independent, leaving 40 that still need the joint
source kernel. The [private frame-pair evaluator](l1_equal_time_private_pairs.py)
covers 33 words with six independent frame pairs. Independent
review reproduced the action factors, weights, and signed top
extraction. The subtotal is `338499/2`, including the earlier
122,472 benchmark. The 32 new words add `93555/2`. The other
112 source-independent and 40 joint-source words remain open.

## Diagonal mixed normalization sector

The [diagonal mixed evaluator](l1_normalization_diagonal_mixed.py)
handles 160 words with a private-Haar time-space square at one
corner, a transverse curvature pair at the opposite corner, and
mixed curvature pairs on the remaining corners. It integrates the
mixed centers into two boundary tensors before their signed exterior
join. The exact subtotal is `-40213/16`. This sector includes
negative contributions. The remaining 256 words require the
source-plaquette traces coupled to the mixed centers.

Independent review reproduced the subtotal and the 160 disjoint
words, with 156 connected and four split size-`(2,6)` words. It
checked the Haar scales, signed exterior joins and branch symmetry.
The four split words complete that shape population. The subtotal
over 6,195 accounted words is `11270712702218527/19110297600`.

The [one-shared-link evaluator](l1_equal_time_shared_quartic.py)
covers 48 additional words with exact subtotal `168399/2`. The
[double-shared chain](l1_equal_time_double_shared.py) covers 16
additional words with subtotal `1323`. Both retain the joint quartic
Haar weights and signed exterior complements. Independent exact
reruns reproduced the totals, the factorial weights and the disjoint
populations. The equal-time subtotal is `254772` over 97 words.
The remaining 48 source-decoupled and 40 joint-source words are open.

## Final plaquette-wire classes

The [coverage check](l1_normalization_coverage.py) partitions all
6,451 supported words and leaves four 64-word plaquette-wire
classes after the previous contractions. The
[wire evaluator](l1_normalization_plaquette_wire.py) retains both
chiral plaquette traces through each shared edge, then closes each
trace at its own curvature insertion. For the four cases run with
arguments `1 2 2 3 3`, `1 2 3 2 3`, `0 2 2 3 3`, and
`0 2 3 2 3`. Each run sums 16 edge assignments. Each plane orbit
has multiplicity four.

Independent review reproduced the orientation sums
`31543/10616832`, `55565/63700992`, zero, and zero, and verified
the four disjoint plane orbits against the residual incidence.
The weighted increment is `244823/15925248`. Adding it to the
6,195-word subtotal gives the full source-free normalization

`Z = (11270712996006127/19110297600) g₂⁸`.

This is positive for real nonzero g₂. The verified raw diagonal
plus numerator then gives connected diagonal-separation response
`-2151705600/(11270712996006127 g₂²)` in the stated lattice source
coordinates. The staggered half-period mode has the opposite sign.
The site-resolved positive-transfer obstruction remains. For the
projected mode, the equal-time contraction, contact matching, and
physical state still need verification.

The [shared-quadratic pair evaluator](l1_equal_time_shared_quadratic_pair.py)
covers 24 more words with two shared links of degree two. It uses
the exact coordinate covariance on each shared link and a signed
integer top complement. Independent reruns give `1701/16` for
each of 16 words with a remote commutator and `15309/2` for each
of eight with all three curvatures integrated privately. The
subtotal is `62937`. These words are disjoint from the prior
quartic sectors.

The [four-shared quadratic evaluator](l1_equal_time_four_quadratic_factor.py)
gives eight exact zeros. The [mixed shared evaluator](l1_equal_time_mixed_factor.py)
gives `567/8` for each of 16 words across four symmetry orbits,
totaling `1134`. Independent reruns verified both disjoint sectors
and the signed joins. Together they complete all 145 source-decoupled
words with exact subtotal `318843`. The remaining 40 words require
the joint source kernel and correlated action contraction.

The [coupled source evaluator](l1_equal_time_coupled.py) covers the
last 40 words. Four direct quaternion quadrature checks reproduce
the reduced center tensor in both scalar and vector channels
([control](l1_equal_time_center_control.py)). Independent exact
reruns give coupled subtotal `-23063/32`. The preliminary zero
receipt projected out the outer site before including both central
frames and is superseded. The full bare equal-time numerator is
`(10179913/32) g₂⁶` across all 185 words.
