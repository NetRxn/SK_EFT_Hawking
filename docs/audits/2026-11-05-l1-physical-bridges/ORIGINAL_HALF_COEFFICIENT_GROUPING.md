# Manual original-half coefficient-norm grouping: exact breakdown

Task l1-positive-half-amplitude-build-r1; parent publication-remediation-01a13f67/l1-positive-physical-reconstruction; owner /root/positive_half_amplitude_build; notebook writer Executor01a1ac65. Candidate source 4aaebb7974e714dd49e052357b9677e9325ba141. This is an actual, bounded attempt at one expressly specified grouping, not an independent review of it. It fails. No positive factorization, physical theorem, or general factorization no-go follows.

## Fixed circuit and proposed grouping, before comparison

At the actual base q*: J=0, A=I, g*=(Lambda^8 T,Lambda^4), T=2^1717, K0=T B4+B2, M=33*3^128*(1+K0)^32, Lambda=1+M. Retain the original 16 sites, 128 odd generators and all 64 independent anchors. Write u for the 24 spatial slice-0 anchors, w for 24 spatial slice-1 anchors, and v01,v10 for the two independent sets of eight temporal anchors. Use the original normalized Haar measures. The two distinct actual even half weights are exp(E01) and exp(E10), with E01=s0+ +s1- and E10=s1+ +s0-. Neither is replaced by the conjugate of the other.

Let [K,J] mean coefficient of xi_out,K xi_in,J in the inherited order. For each directed edge e define

 k_e = integral dv_e exp(E_e),
 t_e(K,I;w,u)=epsilon(I^c,I) [K,I^c] k_e,

with output and input spatial arguments swapped in the second edge; epsilon is the actual coefficient of the inherited slice top in xi_(I^c) xi_I. All K,I range over subsets of the 64 generators, including odd indices; no parity sector is imposed. This is precisely the finite original single-edge complement contraction. The compact variables w remain an internal normalized Haar label; temporal links are independently Haar-integrated inside each actual k_e.

The concrete coefficient-norm grouping attempted here is the following, not an assertion of identity. Fix the inherited d=2^32 boundary occupation basis. For each r=(e,K,I,c,w), with e in {01,10}, K,I arbitrary and c in {1,...,d}, set

 A_(e,K,I,c,w),a(u) = delta_(c,a) t_e(K,I;w,u),
 G_ab(u)=sum_(e,K,I,c) integral dw conjugate(A_r,a(u)) A_r,b(u).

Thus G is an explicit Gram matrix from BOTH actual edge coefficient arrays, their original complement signs, independent temporal Haar factors and slice-1 spatial Haar label. There is no Cholesky, spectral square root, fitted matrix, physical CAR, or substituted conjugate half. The conjugation appearing in G is the ordinary Gram conjugation of the stated actual coefficient, as required by this particular ansatz. Its limitation is visible already in its rule: it pairs each edge coefficient with itself, instead of the original ordered cross-edge product. The coefficient-to-occupation map is explicitly the diagonal Kronecker map above, not claimed to be a derived Clifford trace-dual map. The test is whether this very choice can equal the original trace-dual R_b, not whether some different mixing can.

## Exact coefficient mismatch

Take I equal to the full set of 64 slice indices and K empty. Since I^c is empty, epsilon(empty,I)=1. Every term in E_e has positive odd degree, and the unit coefficient of exp(E_e) is 1 for every compact-link configuration and every coupling. Normalized temporal Haar gives

 t_e(empty,full;w,u) = [empty,empty] k_e = 1.

This is an exact original half-kernel coefficient, including its complement sign and Haar factor. In particular for c=a=1, the single row (e=01,K=empty,I=full,c=1) contributes exactly 1 to G_11(u), for every w and u. Every other row contributes a nonnegative modulus square. Therefore G_11(u)>=1 and Tr G(u)>=1 for every u. This bound uses a single explicit coefficient; it does not require computing any other coefficient or selecting a favorable coupling.

Now choose the accepted spatial cancellation locus u': for every one of the twelve slice-0 undirected spatial endpoint pairs, set the second retained anchor V_e=U_e^dagger. This is a point in the original 24-link domain, not a change of integration measure. At zero sources its original scalar top integral vanishes for every configuration of all other 40 anchors, by the accepted spatial-coframe and saturation argument. Consequently, with the unchanged 128-odd integration and all 40 other original Haar factors,

 Tr R_b(u';q*) = integral dw dv01 dv10 I_odd exp(s0+s1) = 0.

The identity Tr R_b=the scalar top integral is the trace-dual coefficient dictionary. Thus the proposed equality R_b=G would force 0=Tr R_b(u')=Tr G(u')>=1, a contradiction. The unmatched quantity is the positive unit-complement contribution +1 to G_11 from the specified 01 edge row; in the original scalar contraction that term cannot survive as an isolated square, since the complete signed, cross-edge exterior sewing has zero scalar coefficient at u'. The calculation does not identify a particular R_b diagonal as negative or zero; the contradiction is at the exact trace contraction. Nor does it assert that every inserted coefficient vanishes at u'.

The precise construction breakdown is therefore the proposed *coefficientwise self-pairing* at the seam: it loses the actual cross-edge complement/periodic contraction and the trace-dual transformation that can cancel this unit contribution. Retaining the original sign inside each t_e does not restore those cross terms when the matching rule makes a modulus square. Any revised grouping must exhibit how actual factors mix across edges and coefficients so that every amplitude has zero norm at u', if it claims a positive factorization there. This is a failure of the displayed rule only. It is not a proof that R_b is nonpositive, that all Gram regroupings fail, or that original quantization is impossible. The previously accepted two-slice/spatial-record negative witness does not decide this weaker R_b.

## Boundaries of a future positive result

The original exact object is R_b=d^-1 sum_I sigma_I m_I C_I, where m_I is the full 128-odd integral with theta_I inserted, followed by the other 40 anchor integrations, and sigma_I=(-1)^(|I|(|I|-1)/2). The scalar cancellation supplies m_empty=0 only. If R_b is positive at u', trace zero forces the entire R_b to vanish, hence every m_I=0; a Haar-labelled Gram family vanishes almost everywhere in its label, with pointwise vanishing requiring continuity/full-support justification. No scalar bidegree argument establishes those inserted identities. The lead handles their separate complete classification.

Even a successful identity R_b=A†A gives the sharp/operator-density pairing B(F,G)=Z^-1 integral du Tr[R_b F†G], with V(F)=F A†/sqrt(Z), not AF. It is distinct from geometric theta followed by exterior wedge; the existing theta witness cannot simply be transferred to this pairing. A positive boundary form alone supplies neither original physical time nor CAR. Full sources require the original pair weight exp(s0+s1), including exp(D0) exp(D1), its Bopp insertions and all first/mixed C2 contacts; the base D=0 edges do not replace those. Four actual cut maps, null-space and adjoint descent, graded constraint contacts and kinetic/physical normalization remain owed. No source-neighborhood positivity or common differentiable quotient is claimed.

Inputs read: full design and both frozen prospective reports; full original one-slice source kernel; relevant spatial cancellation, coherent/Bopp and process coefficient passages. This is not a complete independent source review. FIRST action was reading the SAME continuity packet; the subsequent actual checker returned fresh=true, changed=[]. Static reading and manual coefficient reasoning only; no scientific evaluator, numerical test, CAS, Lean, build, controller, slot, Git, repository or notebook edit. Only this private report was written. A final SAME check and report digest are returned separately to lead.
