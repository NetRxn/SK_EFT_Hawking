# Full leading collective metric: prospective exact calculation design

Status: author design for independent mathematical/physics review BEFORE execution.
Assignment owner: Executor01a1ac65; acceptance/integration: publication01a13f67.
Existing roadmap: PR115 L1 physical bridges W1/W2 and Phase6a original B3.
Parent: `6dbeeb6fd3441cad1a64b44ea63ec26af9edada2`.

## Target and regulator admission

Compute all ten independent local symmetric components, in fixed lexicographic
order `(0,0),(0,1),...,(3,3)`, of

`c_mu,nu = I_g[Q_mu,nu(0) S4 S2^5]/5! = q'_mu,nu(0)`.

Use the ORIGINAL CLOSED action, exponent `exp(g1 S4+g2 S2)`, on the original
periodic `2 x 2 x 1 x 1` four-site regulator with eight independent Grassmann
generators per site, fixed oriented degree-32 top extraction and normalized
Spin(4) product Haar. Source site0; fixed links/measure/regulator; no matter
determinant or extra action. `Q_mu,nu=sum_a T_mu^a T_nu^a` uses the actual
physical lattice frame T=(four directed blocks)/4. No slice sum or volume sum.
Each off-diagonal source coordinate couples ONCE as `J_mu,nu Q_mu,nu`, not a
double-counted symmetric contraction. The resulting tensor is completed by
Q_nu,mu=Q_mu,nu, not by assuming off-diagonal entries vanish.

The accepted FULL closed pure-g2 denominator is
`Z8=1252309350145403/2123366400`, from the complete sector/wire assembly and
scoped independent review340074356 in the spectral-interface record. It is not
the selected all-local word104978 or a selected sixteen-site sector. Reuse that
accepted denominator, source-pinned. At fixed real g2!=0,

`partial_g1 G_mu,nu|0 = c_mu,nu/(g2^3 Z8)`.

This follows because Z=g2^8 z(x), N_Q=g2^7 q(x), x=g1/g2², z even and q odd.
There is no linear denominator correction. Bare g1 remains the original
dimensionless S4 coupling, expanded symbolically about zero; no numerical g1,
sign, positive direction or phenomenological range is chosen after evaluation.

For sixteen sites the corresponding target is `I Q S4 S2^29/29!` normalized by
FULL Z32. Current accepted records do not certify nonzero full Z32. The four-site
calculation is therefore an enabling finite-regulator test, not a replacement
for that physical/extended-regulator obligation or B3.

## Source and unit convention

All calculation coordinates and g1,g2 are dimensionless lattice coordinates.
Use the previous declared candidate physical composite normalization
`mathfrak G_mu,nu = Z_G Q_mu,nu/a²`, with real Z_G left SYMBOLIC and spacing a.
The plus projection is then the previously reviewed
`Z_G(Q22-Q33)/(sqrt(2) a²)`. For a physical linear source of this dimension-two
operator, `a^4 J_phys mathfrak G = J_lat Q` has `J_lat=a² Z_G J_phys`.
No sqrt(2), extra2, source variance or coframe tag belongs in c_mu,nu.
Conventional dimensionless metric conversion, if physically matched, remains
`g=mathfrak G/mu²` from the accepted parent. Neither Z_G nor mu is fixed here.
This identifies the candidate observable and units prospectively; it does not
prove the external gravitational/matter source actually implements it.

## Complete support, source anchors and factorials

Reuse the52 S2 labels and geometry in `l1_interacting_support.py`. Reuse all16
S4 center/anchor labels in `l1_mixed_g1_support.py:determinant_terms`, whose
physical determinant is
`sum_epsilon epsilon_abcd T0^a T1^b T2^c T3^d` at that center.
There is no extra determinant24 or S4 action quarter.

For each tensor entry expand BOTH source frames over every directed physical
link anchor from `t_terms(0,mu)` and `t_terms(0,nu)`, as an ORDERED pair. Equal-axis
cross-anchor products occur twice in this expansion and must not be silently
merged without their factor2. Record their actual source degree distribution
and link-center parity. Q22/Q33 are local degree4 and parity0; extended and
mixed entries have different source signatures.

For each source branch and S4 label, enumerate every sorted five-multiset from
the52 S2 labels passing total site degree8 and EVEN total occurrence count on
each ORIGINAL physical link. Use a unique sorted2+3 split with last(prefix)
<=first(suffix). This is a complete necessary-support census, not an amplitude
or nonzero certificate. Compare with an independent ordered-state count; Q22
and Q33 must reproduce the known192 untagged determinant/word candidates per
local source branch. Do not use coframe tags, the old96 weighted words, the old
64 shear-difference cancellations, or the old mixed coefficient-15/2048.

Every sorted S2 multiset receives exactly `1/product multiplicity!`, equivalent
to the full ordered S2^5/5!. S4 occurs once. Sum every surviving source branch,
S4 label and word with exact rational weights. A zero table can certify a zero
amplitude; exceptions, caps, deadlines or incomplete traversal cannot.

## Exact factor construction, reusing the existing join

Reuse `l1_extended_offset_witness_k2.py:indexed_join` and its exact bit-mask
wedge/closing-site rules. No replacement contraction engine. Preserve its
120000 live-row and3000000 compatible-product caps. Use its existing choose
heuristic initially; it ranks admissible joins and truncates no domains. A thin
wrapper may return BOTH Gaussian integer components instead of assuming each
word's imaginary part is zero. Retain any imaginary result and require exact
zero only for the final accepted tensor entries, or report the failure.

Freeze the actual helper sources. For import-side-effect control, exact AST-bound
extraction of `fixed_frame`, `quat`, `adj`, `sparse_int`, `indexed_join`, `choose`,
`preceding_parity` and necessary constants is allowed with a complete per-source
fingerprint/AST comparison and unchanged arithmetic. Reuse the existing exact
frame/wedge/moment primitives, not an independently invented frame convention.
Extraction and new assembly require independent SOURCE review before execution.

Each T occurrence supplies a frame factor with its internal index and its own
quaternion-coordinate leg, exact ground Gaussian-integer mask coefficients,
and the correct site degree map. The source contracts equal internal indices
of its two frames. S4 uses an epsilon factor with24 entries connecting four
frame indices. Every S2 has its two complementary frame indices and the FOUR
closed plaquette coordinate occurrences. Each occurrence gets a DISTINCT leg,
even when the same physical link appears repeatedly. Each leg occurs exactly
twice in the graph; multiply incident links are never independently averaged.

For each unordered curvature plane k<l and complementary mu<nu, put
`epsilon=epsilon(k,l,mu,nu)`. With physical closed plaquette H, the unreduced
curvature coefficient is

`epsilon Tr[(H-H^dagger)(gamma_a gamma_b-gamma_b gamma_a) gamma5] /4`.

This retains the four original world-order contributions and their action
quarter. Build the numerator as Gaussian integers and keep its /4 explicitly.
For Q S4 S2^5 there are16 frame occurrences and five curvature quarters; before
Haar/factorials the total explicit divisor is `4^(16+5)`. An independent check
must derive this from the full24-world-permutation action, not just match a sign.

At each physical unfixed link, all its occurrence coordinates meet ONE joint
Haar expectation. For exponent counts c0,...,c7 its weight is the PRODUCT of
the two four-coordinate sphere moments, not an eight-sphere moment:
`moment4(c0..c3)*moment4(c4..c7)`. Use the existing exact `haar_moment`.
Use its common integer scale D_d=haar_scale(d), e.g.4,48,192,11520 for d2,4,6,8.

To avoid materializing a degree-eight joint tensor beyond the row cap, represent
this SAME moment by a count-state chain: state0 is the zero8-vector; each
occurrence with coordinate q increments its q count deterministically; the
terminal factor has weight D_d times the exact joint moment. A fixed ordered
coordinate sequence has exactly ONE state path, so summing state legs gives
exactly D_d TIMES its original moment, with no multinomial or discarded
contraction. Divide this scale out ONCE for every unfixed physical link. Thus
the complete physical target-word coefficient is its contracted integer divided
by `4^21 * product_unfixed_used_links D_degree * product_S2_labels multiplicity!`.
Gauge-fixed tree links supply the full identity rather than a Haar tensor and
contribute NO D_degree. Unused links have degree0 and scale1. In particular a
degree-two repeated coordinate has integer terminal weight1 and physical moment
1/4, not1. The scalar/normalization controls use their own actual frame and
curvature-quarter counts in place of21. All scale factors are recorded per word.
Only states whose odd-count population is <= remaining occurrences can complete
to all-even counts; this exact feasibility pruning is allowed. Every state leg
also occurs twice. Prove this factorization independently before using it.

An optional fixed Haar gauge tree may be used only after SOURCE review verifies
each complete source-anchor/S4/S2 word is gauge invariant, including the actual
endpoint frames, determinant and Q contraction. Fix prospectively the tree links
(site0,axis0),(site0,axis1),(site1,axis1), and substitute the FULL Dirac identity
(sum of both chiral scalar bases) in all their occurrences. No fixed-gamma slice.
If that word-level correspondence is not independently accepted, omit tree fixing.

## Controls, exact acceptance and resource admission

Before target data: verify all frame anchors/directions against original fixed
frame expressions; verify S4 epsilon and source internal contractions; verify the
curvature coefficient against the original full world sum; compare count-state
moments with direct joint moments for complete low-degree domains and all degree
eight multisets. Compare the capped join with direct Grassmann multiplication on
small nontrivial sign/closure cases. These are scientific implementation controls,
not changes to test infrastructure.

Run a known full eight-S2 all-local normalization WORD as an end-to-end control:
its accepted coefficient including the four repetition factorials is104978.
It tests closed curvature/frame/Haar/Grassmann/factorial conventions; it is not
recomputed as a substitute for full Z8. Independently verify the S4 factor against
the existing determinant-center exact construction on its matching domain.
Source review must name the exact control entry points and expected quantities.

Predeclare a single sequential CPU lane; no Lean job, no build/cache/harness
change. Bound control/support preparation by600seconds and the target's ENTIRE
ten-component traversal by1800seconds, with one2465second parent deadline. Arm
timers before scientific import/preparation and account for output/readback in the
whole-pass deadline. Build-time and join-time row/product caps remain explicit.
Coordinate fresh local resource ownership with publication before execution.
If a control or bound fails, preserve exact source snapshots, raw streams and
terminal metadata; stop target execution pending reviewed mathematical repair.
Do not raise caps, omit channels, retry unchanged failure or record it as zero.

Acceptance requires complete source/anchor/S4/word traversal for ALL ten entries,
every signed raw contribution and factorial, common Z8 normalization, exact
imaginary checks and source fingerprints, plus independent data/mathematical and
physics review. Peak/support/runtime observations are evidence of this run only.
No partial channel is a full tensor. Subsequent scientific repair follows a new
reviewed source revision; no harness work is authorized by a scientific failure.

## Remainder and physical boundary

At N4, q_i(x)=c_i x+d_i x³ and z(x)=Z8+z2 x²+z4 x⁴. The accepted exterior norm
argument bounds both actions below2^24. Each local tensor entry obeys
`||Q_mu,nu||_1 <=4*16² <2^24`, so the same conservative B=2^192 bounds c_i,d_i,
z2,z4 without needing the old shear projection. If0<r<=1 and
`B r²(1+r²)<=Z8/2`, then |z(x)|>=Z8/2 for |x|<=r and

`|G_i-c_i x/(g2 Z8)|
 <= 2 |x|³ [Z8 B+|c_i|B(1+r²)] / (|g2| Z8²)`.

This follows by exact subtraction of the rational functions. It is an explicit
finite-control truncation certificate, not a phenomenological coupling range or
positive physical phase. Independently review the source norm and bound.
For the physical composite multiply the result by the symbolic Z_G/a² only after
retaining its declared correspondence limitations.

The result remains an enabling finite uncoupled body slope. No chosen sign/body,
positive state, full sixteen-site denominator, continuum limit, B3 normalization
or [0.1,10] range, tensor mode/matter cone or real-time transport is supplied by
this calculation. Before opening a purported missing Lean proof, reconcile actual
statement/type/import/dependency/history via lean4/LSP under fresh ADR008 admission.
No slot is granted, no theorem absence certified, and no new axiom proposed here.
