# Original cross-edge sewing: explicit trace-dual seam and a Gram feasibility condition — r2

Task l1-original-cross-edge-positive-sewing-r1; parent publication-remediation-01a13f67/l1-positive-physical-reconstruction; packet HEAD 5ad2c7e0ba6f9236dd27308c609739b3b563c727. Manual research, not an independent review or positive factorization. Exact base is the design's original q*: J=0, A=I and the fixed original couplings. Retain all 24 slice-0 spatial anchors u, integrate the other 40 anchors, keep the distinct actual temporal edges, inherited 64-generator slice order, complement signs, and periodic supertrace. The accepted full action, measures and occupation/trace-dual conventions are unchanged.

## Revision custody

R1, SHA256 801f713553444e7dc4a1124076cf94ca5f01db00018ea94e45fba665ebc9b02e, is preserved unchanged. Independent actual mathematics review /private/tmp/l1-cross-edge-actual-math-r1.md found a necessary mismatch: R1 conjugated both edge features, producing t10 conjugate(t01) instead of t10 t01. This revision fixes the feature list and audits the Hermitian cross block below. No actual source-review verdict has been received in this revision. A fresh independent actual mathematics and original-source review are required. No positive factorization is claimed.

## A cross-edge construction attempt

Let P,Q,R,I range over all subsets of the 64 ordered slice generators and let |P| be their grade. Write M_I for *actual exterior multiplication* by the boundary Majorana monomial theta_I in the inherited exterior coefficient basis. In particular (M_I)_{P Q} is its coefficient from input xi_Q to output xi_P, including the complete reordering sign. It is not a physical Clifford multiplication. Let

  t01(R,P;w,u) = epsilon(P^c,P) [xi1_R xi0_(P^c)] k01,
  t10(Q,R;u,w) = epsilon(R^c,R) [xi0_Q xi1_(R^c)] k10,

where k01 and k10 are the independently integrated original E01 and E10 edge weights, w is the 24-link slice-1 spatial configuration, and each edge carries its own eight independently integrated temporal anchors. Define the *ordered seam* (before the Clifford transform)

  K_{Q P}(u) = integral dw sum_R t10(Q,R;u,w) t01(R,P;w,u).       (1)

The integrand is a cross-edge product in the physical order 01 followed by 10; there is no complex conjugation or identification of the two original edge weights. The actual periodic insertion moment is

  m_I(u) = sum_{P,Q} (-1)^|P| (M_I)_{P Q} K_{Q P}(u).              (2)

This is simply Str[M_I T10 T01] at fixed u, with the slice-1 spatial Haar sewing included in K. It follows by expanding the diagonal coefficient in the accepted supertrace formula, not by treating the coefficient basis as a physical Hilbert basis. All 128 Berezin integrations and original complement signs are present. For I empty, M_empty is the identity and (2) is the original scalar trace contraction. The boundary matrix is

  R_b(u)_{ab} = sum_{P,Q} H_{P Q;ab} K_{Q P}(u),
  H_{P Q;ab} = (1/d) (-1)^|P| sum_I sigma_I (M_I)_{P Q} (C_I)_{ab},
  sigma_I=(-1)^(|I|(|I|-1)/2), d=2^32.                           (3)

Equations (1)–(3) are the explicit cross-edge trace-dual seam operator. The sum over all I is essential: periodic parity and exterior complement are applied before the trace-dual map, not independently squared on each edge. The formula is a base diagnostic; it does not reduce the full source family to two edges.

I tried to obtain Gram rows by mixing original edge coefficients *across* the seam. Set the two feature families to x_10,QR=conjugate(t10(Q,R;u,w)) and x_01,RP=t01(R,P;w,u). Thus conjugate(x_10,QR) x_01,RP=t10(Q,R;u,w) t01(R,P;w,u), exactly the original bilinear in (1). The two families are an auxiliary feature list; conjugating a feature is not a replacement of an original edge weight. Repeated index patterns, actual compact-link identities, Haar integrations and theta/Clifford signs must all be retained. Candidate rows linear in these actual features have the form

  A_{r a}(u,w) = sum_i L_{r,i a} x_i(u,w),
  R_b(u)_{ab} ?= integral dw sum_r conjugate(A_{r a}) A_{r b}.    (4)

This differs from the previously failed separate self-pairing: each row may mix both edges, different exterior indices and occupation columns. The needed coefficient condition is the existence of a single Hermitian positive semidefinite array

  Htilde_{i a,j b}=sum_r conjugate(L_{r,i a}) L_{r,j b}

such that, for every u and a,b,

  integral dw sum_{i,j} Htilde_{i a,j b} conjugate(x_i) x_j
    = integral dw sum_{P,Q,R} H_{P Q;ab}
                         t10(Q,R;u,w) t01(R,P;w,u).               (5)

This equivalence is only for the specified finite, constant-coefficient linear-feature ansatz (4). The left side is a Gram identity if explicit L is constructed; saying Htilde exists is not a construction or an independently chosen metric. Its matrix-factor characterization is a necessary and sufficient algebraic feasibility condition for this ansatz, not an assertion that the original circuit provides such an array. Coefficient comparison must be performed in the actual quotient of compact-link functions after normalized Haar integration; equality of formal coefficients in an artificially free alphabet is stronger and may reject legitimate cancellations. Conversely, equality merely on selected sampled u, moments, or matrix entries is insufficient. More general u-dependent, nonlinear or enlarged original-factor amplitudes are not excluded by failure of (4).

To expose exactly what the cross-block observation does and does not say, put combined feature/occupation indices alpha=(10,Q,R,a), beta=(01,Rprime,P,b), and define the raw cross block B by B_(10,Q,R,a),(01,Rprime,P,b)=delta_(R,Rprime) H_(P Q;ab). Let C have B in its 10-to-01 block and zero elsewhere. For every occupation vector v, integration of z†Cz, where z_(i,a)=x_i v_a, equals v†R_b v by (3). C is generally not Hermitian. If the *integrated* original R_b is Hermitian, then C0=(C+C†)/2 has the same integrated quadratic form for all v and hence reproduces every R_b entry by polarization. This uses the original conjugate-transposed integrated contribution; it does not assert pointwise Hermiticity of the edge integrand or replace either edge. C0 has zero same-edge blocks and cross blocks B/2 and B†/2. If B is nonzero, C0 is indefinite: its quadratic value on (v,t w) is Re(t v†B w), whose sign can be reversed. This is a free-feature coefficient-space statement, not a proof of nonpositivity of the integrated R_b.

Conditionally on integrated Hermiticity, a viable (4) therefore requires an Hermitian correction N such that C0+N is PSD and integral dw sum_ij N_(i a,j b) conjugate(x_i)x_j=0 for every u,a,b. N may include same-edge as well as altered cross-edge coefficients. These are null relations in the actual compact-link/Haar quotient, not formal freedom to modify the action. If B were zero, the conditional indefiniteness statement says nothing; no nonzero value is asserted without further calculation. This is an exact feasibility condition relative to C0, not a construction of N or a proof that such null relations do or do not exist. Hermiticity must itself be justified on the relevant domain.

At a spatial-cancellation node u', the accepted scalar result gives Tr R_b(u')=0. If (4)–(5) held, each nonnegative row norm would vanish, hence A_{r a}(u',w)=0 for all r,a for Haar-almost every w. Equivalently Htilde annihilates x(u',w) tensor each occupation basis vector for a.e. w. Continuous amplitudes and full Haar support would strengthen this to every w. This implies the whole R_b(u') is zero and all m_I(u') vanish, not only m_empty. The accepted nodal reduction shows the only possibly nonzero inserted grades are 64,60,56,52,48,44, with its exact six-block expression; none of those weighted blocks has been evaluated here. For example the p=0 block contains the actual reduced integral P0 of A^16; its nonvanishing would reject a positive R_b at that node, but neither sign nor nonvanishing is established. At one fixed coupling it is the weighted block sums that must vanish, not necessarily each coupling coefficient separately.

I have not found explicit original coefficients L satisfying (5), nor proved they cannot exist. The conditional free-alphabet cross-block observation diagnoses the unmodified Hermitianized bare-cross coefficient array only. It does not exclude a null-relation repair, another cross-edge grouping, or a different original physical quantization. Nor does it inherit a no-go from the distinct geometric-theta or two-slice spatial-record pairing.

## Full-source and physical boundaries

At unrestricted literal J/frame source q, use the original pair density with exp(D0) exp(D1), D=Bt.Rminus+2H00 Rminus.Rplus, and its actual Bopp/source insertions. The above two-edge factorization is not an unrestricted source identity. A positive two-sided C2 family at a node must also have every first real source derivative of R_b vanish and every genuine directional second derivative PSD; these are not established. Actual first/mixed C2 source and frame contacts, denominator/overlap and both cross placements, all four cut maps and their source derivatives, source-stable nulls and constraint/adjoint domains, original kinetic polarization and physical product/adjoint, periodic and reflected dynamics remain obligations. For a proved R_b=A†A with positive global Z, the nontracial amplitude map is F A†/sqrt(Z), not A F. Even success of (4) alone gives no physical CAR, dynamical transfer, calibrated metric, matter reference or publication acceptance.

Sources: packet and its primary notebook/roadmap references, original positive sewing R2 and both prospective R2 reviews, one-slice kernel, coherent bridge, previous half grouping and its actual reviews, and nodal reduction. Some large combined reads were truncated; no claim of exhaustive independent source review is made. Static reading and manual algebra only. No scientific evaluator/CAS/Gram/Haar/exterior or matrix program, scientific import, tests, build, Lean, slot/controller/process or Git action; no repository/notebook edit. Only this private r2 report was written in this revision. Independent actual mathematical and original-source review are required before adoption.
