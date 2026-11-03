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
16 with counts 5, 17, 117, 283 and 230. Independent verification of
this further reduction is pending.

## Opposite-site fourth powers

The [quartic sector evaluator](l1_normalization_opposed_fourth.py)
covers all 32 multisets with multiplicity profile `(4,4)`. Each is
supported on two opposite centers with disjoint Haar variables.
The degree-four quadrature and the commutator curvature moment produce
38 exterior terms per center after selecting local saturation.
The exact exterior join gives `20339/129600` per word after the two
`4!` factors, or `20339/4050` in total. Independent review is pending.
