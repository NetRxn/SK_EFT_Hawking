# ACTUAL original-source review — page0 compiler design R1

**REVISE** the exact R1 design, 22,800 bytes, SHA256
d3d1342247902da5fca9ff5a438eb26a30d23e49553bcb9de73a9f9820412ae7.
The proposed numerical endpoint basis fails covariance on the original
held L fields. Its coordinate Gram can nevertheless be correct. Therefore
the current Gram dual does not certify reconstruction of the original page,
and no schedule, integer width, or codec validation can repair that defect.
The accepted abstract covariant page dimensions and original scalar are
unchanged. Source was clean 6830c734218ed094f632092bd372ad9a263a2711.

## Necessary repair, exact counterexample and acceptance boundary

The mathematical report §2 (6) holds L1=barL and L2=psiL^T E. As
columns of components, both transform by g_L^(-T). Indeed
g_L^T E=E g_L^(-1). In contrast R1=E barR^T and R2=psiR both
transform by g_R. These are the exact original signed permutations of
the odd generators. The description “fundamental-spinor modes” in §2 does
not make their literal spin-index matrices the same.

At hub1 the matrix legs U_(r5,c1), V_(r1,c5) transform on c1 by right
multiplication g1^(-1), and on r1 by left multiplication g1. The
COEFFICIENTS of these open matrix entries therefore transform on c1 by
g1 and on r1 by g1^(-T), with the two side-vector matrices also acting.
The duality map (7) applies E to the c1 COEFFICIENT leg. Since
E g E^(-1)=g^(-T), both pulled-back coefficient slots transform by
the dual, each in its own chirality. The same conclusion holds at hub5
with the E adapter on the V column. The matrix-leg transformation identity
E(g^-1)^T=gE itself is correct. It does not justify applying the matrix
representation law to Ptilde, which carries the corresponding coefficient
legs.

Concrete noncovariance canary: choose equal LL, use fixed hub g_L =
diag(t,t^-1) for a nontrivial SU(2) phase t with t^4 ≠1, g_R=I,
and contract the side factor with the invariant δ_AB. Math (8) m6
contains Stilde_L,11 at dummy component (u,v)=(2,2), since E_12=1.
This is a nonzero exterior polynomial
Stilde_L,11=2 L_(1,1)L_(2,1). Under the ORIGINAL field action it
scales by t^-2. The required pulled-back coefficient component
(2,2) scales by t^2. Thus m6 is not the required intertwiner,
regardless of diagonal Gram or whether the unknown page happens to have
zero coefficient in that slot. This adversarial covariance test uses
only a torus phase and one allowed type, with no generated science table.

Repair requirements before adopting a new design:

- Write the coefficient transformation law on each hub, including its
  side-vector action and both inverse endpoint maps. The inverse of
  a leg conversion E uses E^T=-E with interchanged input/output indices.
- Align the literal field and central coefficient bases. One narrow route is
  to put the numerical hub L fields in column fundamental coordinates
  Lambda=E L, leaving R alone and retaining actual q/E source conversion
  signs. This is a signed spin permutation. Its degree-two map is unitary
  for the auxiliary coordinate metric, and it preserves the complete
  exterior top. A direct correction expressed in held L variables is
  also possible, but it must carry the same signs. This report does not
  review or adopt either replacement formula.
- Reprove equivariance of all eight typed formulas on both hubs in
  LL/LR/RL/RR, including S_A=q_A E and the transposed R convention,
  unequal dummy-slot exchange and the two spin couplings. Pin the actual
  field-to-basis and inverse magnetic reconstruction maps in the graph,
  numerical oracle and any closure compiler. Reprove Gram, entry/phase
  and leaf/width bounds for the exact revised graph grammar. A diagonal
  Gram calculation tests linear algebra within a chosen subspace, not
  that it is the source covariance subspace.
- Add the torus canary above, and retain independent tests of the actual
  hub transformation on open central coefficients. Preserve all original
  local, orientation, Hodge and endpoint controls. Generality is not
  established by testing normalizers or a whole page that might be zero.

## Source and grammar findings independent of that defect

The original order H(z,k,l)=Ω(z,l)† Ω(z+l,k)† Ω(z+k,l) Ω(z,k)
gives H0=c†b†Ua and H4=d†a†Vb at the page0 nodes. Central U,V
are undaggered. Source edge c,d appear daggered and remain distinct.
The side coframes use e†−a and f†−b at original centers 1 and 5,
two per hub, with distinct internal labels that couple to other pages.
The two Q polynomials use c†−d at 0 or d†−c at 4, with the actual
endpoint gamma orders. The six quarters, separate world signs −1 for each
(02;13), both full ordered antisymmetric gamma traces, lower-block
gamma5 sign, and absence of an extra EHC quarter are correct. Complete
outside even tops and hub two-forms preserve their original site order.
Ka=i q_a uses the original signed L/R choice and copy Hodge lock.
Representatives C01,C02,C03 need no half, and complement signs are
(+,−,+) times the chirality sign. Explicit Hodge sums are twice these
representatives. Thus kappa may mix by xor1111 and no extra 2^6 enters.

The direction-bit labels are side factors first, while compact moment
gathering may start with source factors because compact entries commute.
The latter never reorders the odd words. Source c,d each have one
curvature and must receive one coframe of their own curvature chirality.
A side's active anchor has two curvature copies, and the partner
none, so side coframes choose the same anchor. Equal-face side channel
count is 5 before exterior selection, different-face count 2, giving
14,848. At an equal-face Q0 source, the outer0 source fields are
opposite chi and the outer4 fields chi. Side T at hub1 and hub5 carries
its selected compact chirality at the outside end and the opposite one
at the hub. Thus side channel counts are 3 and 2 for Q0 and reversed for Q4.
Equal-face blocks have 1536 rank branches each and differing blocks 1024,
giving 5120 total. Replacing the one allowed P4's second rank term by
its four A/B pairings gives 8192 matching terms. P4 is joint and rational;
the 1122 control 1/3 fails the independent P2 pairing. Source chiral-load
zeros imply 864 per separate array and 576 in their sum in a correctly
typed basis. These are structural zeros, not evaluated coefficients.

The mathematical Gram formulas describe the written arrays as
Euclidean coordinate vectors: disjoint flavours and chirality blocks
are orthogonal, and trace removal separates scalar from (1,1) side paths.
The tilde flavour singlets have squared norms 4,2,4, and the symmetric
spin map has summed norm 12. Multiplying by the δ and E norms gives
32,16,32 per chirality, own triplet gives 48, and two symmetrizers and
two vector maps give 4·12²=576. Different-chi gives four 16 and four 576.
Thus the displayed Gram can have exactly the stated off-diagonal zeros
and denominator divisibility and still span the wrong endpoint space.
The full ordered ambient metric counts packed off-diagonal side entries
twice. This is independent of the original exterior top.

For the proposed graph route, categories at each outside site can
select at most two total copy support choices across all three
representatives. At each hub at most two basis labels, each with at
most four diagram terms, are considered. With four separate commutator
choices this gives the stated 8192·4·4·16·4=2^23 matching ceiling for
the proposed formulas. Internal vector sums are pairwise quaternion
completeness, including daggers/transposes; the nine factors of two
are a safe upper bound. The original phase on reversing a cycle edge
must be evaluated at the original row. Directed E cannot be made
symmetric. Each perfect port matching reduces to at most two seeds
per connected cycle. The 92 before simplification /128 safe factor
ceiling and associated operation envelope describe the written graph
grammar, and require rechecking for a repaired compiler.

The schedule for the written formulas clears six quarters, two
commutator halves, actual Haar denominators and two Gram norms:
4^6·4·576·576²=2^32·3^6. The total absolute contributions
with the stated bounds are below 2^175 before relying on cancellation,
so signed256 suffices conditionally. The three fully present 2304-cell
arrays occupy 442,368 numeric bytes with real and imag i256. Counters,
source labels, exact array sum, manifest/body hashes, CRC and
incomplete/refusal protections are suitable design checks; they do not
validate a mathematically incorrect coefficient map.

## Independent oracle, adverse controls and closure boundary

The original literal oracle is independent of the graph grammar:
per-group rational 24-cell quadrature, formal central matrix-unit
extraction, and tagged Pfaffian polarization on 20 fixed-order
generators. The quadrature's sign/permutation symmetries deliver
second moment 1/4, fourth moments 1/8 and 1/24 and all required odd
zeros; all 12 independent groups must be kept. Pfaffian degree 10
makes tag inclusion-exclusion isolate the ten tags once, without 10!.
The direct oracle's 24^12 per probe and complete raw magnetic scope
are intentionally non-admissible. The scaled numerator bounds remain
conditional on the repaired numerical basis having the stated norm
divisibility, pointwise bounds and exact pullbacks. A signed512 bound
for the mathematical oracle does not establish feasibility or end-to-end
equality. The frozen prior oracle section, oracle audit, and final plan
were read as distinct scopes.

The original local canaries survive: F02 is +2 at U_L=E with the
other surrounding matrices identity, and −2 if replaced by U†.
The distinct source-endpoint scalar has +1/8 from Q0, zero from Q4
with the specified monomial/entries; replacing their sum by either
doubled source gives 1/4 or 0. The held epsilon contraction gives
192 (384 if the ordered Z half is lost). Hodge sums produce their
declared factors 2 and 4. Joint P4, mixed physical −1/8, the positive
site top, overlap zeros and complete signed W controls remain binding.
None asserts that an unknown page amplitude must change under every
mutation. The new torus test is independent of those checks.

The optional G order joins the same signed kappa/lambda across both
endpoint triples and can only consume matching exact page and closure
input bases. Forced source chirality on a central anchor follows the
odd entry of its three curvature choices, not a global field
restriction. The rank product sum is (2·2+6)^2=100 across all 64
assignments. The 85,320,272,257 product ceiling remains a conditional
post-input ordering, with page1/3 and endpoint vector compilation
unqualified. It supplies no fit, no actual page result and no numerical
fallback for this defect.

No result on h12,6, A01, sign, nonzero, full-core cost or physical
TT/boundary/adjoint/seam/causal/transport/calibration is claimed.
No scientific code, import, testing, or computation occurred. This
report modifies no repo/notebook/candidate or peer file.

## Readback

Read the full combined candidate and the pinned compiler math, source
test, factorized ordering, independent oracle audit and historical
oracle section, plus governing source, notebook and commission.
Ordinary tools: continuity checker, cat/sed/jq/rg/tail, git status/rev-parse
and shasum/wc. FIRST and final review-r1 primary continuity SAME.
