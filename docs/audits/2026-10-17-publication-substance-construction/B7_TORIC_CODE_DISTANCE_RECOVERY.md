# An actual toric lattice code: logical distance, erasure recovery and entropy

17 October 2026 UTC. Independently accepted manual construction; [full original nonauthor mathematical/source review](reviews/B7_TORIC_CODE_DISTANCE_RECOVERY.md). Native and intended horizon/geometry/error-algebra B7 remain OPEN BUILD. This addresses original B7 by constructing a code and deriving its minimum nontrivial logical weight. It does not define distance as a logarithm, instantiate a carrier with an unproved distance field, establish a holographic correspondence, or complete native/publication acceptance. The task filename's 20261018 component is a preparation-label error; actual captured UTC dates govern chronology.

## 1. What is currently present, and the construction's scope

The complete current `QECHolographyBridge.lean` defines `HPCode` as horizon data plus a selected simple object. Its real-valued `codeDistance` is the existing `areaLawKappa`, hence log(d_max); `recoveryPossible` is a scalar threshold inequality. Its valid logarithm/order theorems do not construct a tensor-product codespace or a recovery channel. The current D4 manuscript explicitly says this. The complete `FaultTolerance/StabilizerCode.lean` carries n,k,d and list lengths/positive d but explicitly leaves codespace semantics unformalized; it cannot prove the minimum-weight assertion merely by populating d. `ToricCodeCenter.lean` supplies the four-label invertible fusion/braiding model, not the lattice codespace below.

We construct, for every integer L>=3, an actual qubit code on a periodic L by L square lattice. Its distance is L, it encodes two qubits, and every known erasure of fewer than L physical qubits has an explicit recovery channel. The recovery has a derived entropy consequence. The construction also tests the proposed categorical-only interpretation: the same invertible four-sector fusion data cannot by itself determine these varying distances. This is a concrete limit on that inference, not permission to abandon B7 or reduce the remaining geometric/native/holographic objectives.

## 2. Physical tensor product, stabilizers and nonempty codespace

All binary vector spaces below are over F_2. Vertices are V=(Z/LZ)^2. There are horizontal edges h(i,j) from (i,j) to (i+1,j) and vertical edges v(i,j) from (i,j) to (i,j+1), all coordinates modulo L. There are |E|=2L² edges and |F|=L² elementary square faces. The physical Hilbert space is H=(C²) tensor E, with its orthonormal computational basis |x> for x in F_2^E.

On each qubit use the actual matrices X|b>=|b+1>, Z|b>=(-1)^b|b>. For a,b in F_2^E write X(a)=product_e X_e^(a_e), Z(b)=product_e Z_e^(b_e). Their supports have ordinary cardinality, and

    X(a) Z(b)=(-1)^(a dot b) Z(b) X(a).                 (1)

At a vertex s, A_s is X on its four incident edges. At a face f, B_f is Z on its four boundary edges. Both are Hermitian involutions. A vertex and face have either zero or two common edges, hence (1) proves every A_s commutes with every B_f. Stars commute among themselves, as do faces. Let S be their generated Pauli group and define the code C as their common +1 eigenspace. Equivalently C is the kernel of the actual nonnegative Hamiltonian

    H_L=sum_s (I-A_s)/2 + sum_f (I-B_f)/2.               (2)

No assertion about a continuum thermal medium follows from this finite Hamiltonian.

There is exactly one binary relation among stars: their full product is I. Indeed the product for a selected vertex set has an X on exactly those edges with one selected endpoint. Its being empty says the selected-vertex indicator is constant across every edge. The connected lattice forces all vertices or none. The dual lattice is connected too, so the identical argument for selected faces shows exactly one relation among their boundaries: the full face product is I. The star and face groups have no further mixed identity relation because a Pauli X(a)Z(b) is scalar only when a=b=0. Each pure relation has + sign, and the commuting groups have no -I. Consequently

    rank(S)=2L²-2,   |S|=2^(2L²-2).
    P=|S|^(-1) sum_(g in S) g,    tr(P)=2^(2L²)/|S|=4.  (3)

Here P is an orthogonal projector: Hermitian and P²=P follow by averaging the finite group. Every nonidentity Pauli has zero trace, proving its stated trace. Its image is exactly C. Thus the codespace is nonempty and has dimension four; two logical qubits are produced, not assumed.

There is also a concrete encoding basis. Let D be the binary span of star supports (the cut space), of size 2^(L²-1). The computational configurations satisfying all B_f=+1 are the vectors in ker(delta), where delta takes parity around every face. The rank of delta is L²-1 by the face-relation argument. Stars are in this kernel by commutation. Thus ker(delta)/D has binary dimension (2L²-(L²-1))-(L²-1)=2. Choose one representative x_alpha for each of its four cosets, labelled by alpha in F_2². Then

    |psi_alpha>=2^(-(L²-1)/2) sum_(d in D) |x_alpha+d>.   (4)

Distinct cosets are disjoint and each has |D| terms, proving orthonormality. Face constraints hold termwise and each star permutes the summands, proving all four are in C. Equation (3) makes them a basis. The isometry U|alpha>=|psi_alpha> is an actual encoding.

## 3. All logical classes and the distance lower bound

The distance convention is the smallest support size of a Pauli that preserves C but acts nontrivially on it modulo scalar. For a stabilizer code this also detects the smallest support of an arbitrary operator with non-scalar compression P O P, because Pauli strings span each supported operator algebra; the argument below proves the scalar property for every smaller support.

A Z(b) commutes with all stars exactly when b has even incidence at every primal vertex: b is a binary 1-cycle. Face boundaries form a subspace B of these cycles. The primal incidence matrix has rank |V|-1: its transpose has kernel precisely the constant vertex labels by connectivity. Therefore

    dim(cycles)=|E|-|V|+1=L²+1,
    dim(B)=|F|-1=L²-1,
    dim(cycles/B)=2.                                    (5)

We identify these two classes without assuming a homology theorem. For each vertical cut between columns i and i+1, count modulo two the horizontal cycle edges crossing that cut. This parity is independent of the cut: summing even vertex incidence in the intervening column strip equates the two boundary parities. Face boundaries have parity zero. Define the analogous horizontal-cut parity using vertical edges. A straight horizontal wrapping loop has cut parities (1,0); a vertical wrapping loop has (0,1). These independent classes and (5) show that the two parities classify cycles modulo B: the induced map between two-dimensional spaces is onto, hence injective.

If a cycle has nonzero first parity, every one of the L vertical cuts contains at least one of its horizontal edges. These sets of edges are pairwise disjoint, so its weight is at least L. The second parity gives the same lower bound using horizontal cuts. Conversely straight wrapping loops have weight L. Thus every non-boundary primal cycle has weight at least L, attained by the displayed loops. Repeating precisely this argument on the square dual lattice proves the same statement for dual cycles modulo dual face boundaries (primal star supports).

A general Pauli i^q X(a)Z(b) commutes with all stabilizers iff b is a primal cycle and a is a dual cycle. It lies in S up to scalar iff both cycle classes vanish. A normalizing Pauli outside S modulo scalar has tr(P O)=0 by the Pauli trace rule in (3), because every g O is a nonscalar Pauli. Its restriction is unitary on the four-dimensional code, so it cannot be scalar there: a scalar unitary has nonzero trace. Every Pauli outside the normalizer anticommutes with a stabilizer and hence has P O P=0: insert that stabilizer on the two sides of the compression. A normalizing Pauli of support <L has both classes trivial by the preceding lower bounds and therefore acts as a scalar on C. Weight uses union(a,b); it is at least the weight of either component, so a mixed X/Z string cannot evade the bound.

A straight primal wrapping Z loop has weight L and has one intersection with a transverse dual wrapping X loop. Both preserve C and (1) says they anticommute. The four-dimensional C is nonzero, so the Z loop cannot be scalar on C: a scalar unitary cannot anticommute with another preserving unitary there. Therefore the lower bound is attained and

    d(C)=L,    parameters [[2L²,2,L]].                    (6)

This is a minimum over actual nontrivial logical operators. It is unrelated to assigning L to a structure field.

## 4. Recovery for known erasure and unknown errors

Let R be any specified set of physical qubits with |R|<L, B its complement. For every Pauli supported on R the preceding proof gives scalar compression. By linearity, for every operator O_R,

    P (O_R tensor I_B) P=c(O_R) P.                       (7)

This proves the erasure criterion for an entire supported operator algebra, including products of erasure Kraus operators. It uses |R|<d, not 2|R|<d; products on the same erased region still have support in R.

For completeness construct the actual finite recovery rather than merely naming a criterion. In any orthonormal basis |r> of H_R expand (4) as

    |psi_alpha>=sum_r |r> |u_(r,alpha)>.

Applying (7) to all matrix units |s><r| shows that
<u_(s,beta)|u_(r,alpha)>=C_sr delta_(alpha,beta)
for a single positive-semidefinite matrix C of trace one. Diagonalize C, changing the R basis by a unitary. In its positive-eigenvalue directions write u_(j,alpha)=sqrt(lambda_j) v_(j,alpha). The vectors v_(j,alpha) in H_B are orthonormal jointly in j,alpha. Let V_j send |alpha> to v_(j,alpha), and Pi=sum_j V_j V_j†. For any logical density matrix rho,

    tr_R(U rho U†)=sum_j lambda_j V_j rho V_j†,
    D(tau)=sum_j V_j† tau V_j
              +tr[(I-Pi)tau] |alpha0><alpha0|.            (8)

The first term is CP with Kraus V_j†. A basis of the orthogonal complement of Pi supplies Kraus |alpha0><w| for the second term. Their total adjoint products are Pi+(I-Pi)=I_B, proving D is trace-preserving on ALL inputs. Orthogonality gives D(tr_R(U rho U†))=rho because sum_j lambda_j=1. Re-encoding by U after D gives an explicit channel recovering the original code density matrix. Rank-zero eigenvalues are omitted, with no division by zero. This works also for R empty.

For arbitrary unknown Pauli errors of weight <=t, products E_a†E_b have weight <=2t. If 2t<L, their compressions are scalar and the same finite Gram-diagonalization argument gives a correction channel for any channel whose Kraus operators lie in their linear span. This does not assume independent/stochastic noise or identify an experimental noise model. Known-location erasure and unknown errors have different bounds.

The erasure bound is sharp in the worst-case support sense. Erase a complete straight wrapping loop R of L edges. That region supports the non-scalar logical Z already constructed, so (7) fails. Take normalized code eigenstates psi_0,psi_1 of this logical Z with opposite eigenvalues; they exist because the transverse logical X exchanges its eigenspaces. For Q=|psi_0><psi_1|, conjugation by the erased-region Z sends Q to -Q. Partial trace over R is invariant under that local unitary, so tr_R Q=0. The distinct orthogonal logical superpositions (psi_0+psi_1)/sqrt(2) and (psi_0-psi_1)/sqrt(2) therefore have identical reduced states on B. No channel on B can recover both different original pure states. This proves failure directly without assuming a general no-cloning or reversibility criterion. We do not assert every region of L or more edges is uncorrectable: many larger contractible regions are correctable. The statement is the uniform guarantee for every region.

## 5. An actual derived entropy relation, without a distance-as-log definition

Introduce an independent four-dimensional reference A and the pure encoded maximally entangled state

    |Omega>=1/2 sum_alpha |alpha>_A |psi_alpha>_(R B).

The matrix-unit identities giving (7) imply

    rho_(A R)=(I_A/4) tensor C_R,
    S(A)=log 4,   I(A:R)=0,
    S(B)-S(R)=log 4                  for |R|<d(C)=L.     (9)

All entropies use natural logarithms. The first identity follows by tracing B and using the same joint inner products, including alpha!=beta; C_R is a density matrix, not necessarily maximally mixed. Additivity of the tensor-product eigenvalues yields S(AR)=log4+S(R). Purity gives S(B)=S(AR), including zero eigenvalues via 0log0=0. This proves (9) directly in the actual encoded state. Equations (6)-(9) connect actual distance, exactly recoverable regions and retained logical entropy.

No area-law coefficient, topological entanglement entropy, thermal scrambling rate or boundary-radiation spectrum is computed by (9). In particular S(A)=log4 is constant as L changes while d(C)=L varies. Even the logical entropy of this family cannot determine its distance without geometric information.

## 6. Fusion data, countercontrols and the remaining original obligation

The actual string algebra supplies four excitation labels. Open primal Z strings have endpoints at star violations; open dual X strings have endpoints at face violations. Products add their endpoint parities modulo two, so the local charge labels form F_2 x F_2 with vacuum, electric, magnetic and their pair. A closed string crossing a transverse string once has the sign -1 by (1); coincident types fuse by cancelling parity. These reproduce the invertible fusion and mutual string-crossing data in the read current `ToricCodeCenter.lean`. This is a manual string/sector match, not a new constructed braided category or native equivalence with its Drinfeld center.

For any positive fusion-dimension character on this four-label group, each simple a satisfies a*a=1. Multiplicativity gives d_a²=1 and positivity gives d_a=1. Thus d_max=1 and global dimension squared is four for this fusion model, independently of L. Its log(d_max) is zero, whereas the actual code distance (6) is L>0 for every L>=3. Varying L changes distance while leaving these fusion data identical. Consequently no universal equality d=log(d_max), nor universal implication positive actual code distance => a noninvertible simple, can follow from only those data for this class of lattice quantum codes.

This does not refute the existing Lean statement, whose d is explicitly the logarithmic proxy. It refutes interpreting that definition-only statement as a general actual-code distance theorem without additional hypotheses. It does not prove absence of a useful geometry-dependent theorem for the intended horizon model, and is not an operator-approved recharter or deferral.

Countercontrols are substantive: L>=3 avoids cell degeneracy of very small quotients; rank and -I exclusion prove a genuine code; both primal and dual classes and mixed supports are controlled; actual wrapping operators attain the bound; erased-region products retain the same region; unknown errors instead require doubled weight; zero Gram eigenvalues are omitted; recovery is CP/trace-preserving on all states, not only the code image; an erased nontrivial loop violates scalar compression; entropy is computed for a specified pure encoded state rather than an unspecified boundary state.

The publication lead retains original B7. Independent nonauthor verification of all combinatorial, operator, recovery and entropy arguments is complete in the linked original review. Next: an explicit native physical-Hilbert/Pauli/projector/minimum-weight/recovery representation under ordinary authority. The intended horizon/anyon encoding still needs its actual geometry, error algebra, code construction and derived relation, or a demonstrated impossibility under explicit assumptions for the operator's decision. No full Hayden-Preskill decoder/dynamics or broad holographic charter is silently added or claimed complete. Existing canonical finding review, integration, main and final human requirements remain.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

A positive distance field or logarithm does not establish an actual code's minimum logical weight. The current code and categorical source bodies support a finite construction but do not already implement it. The explicit same-fusion/varying-distance family exhibits why extra encoding geometry is necessary. The original obligation remains open at native and intended-model scope; the finite construction has full independent manual acceptance in the linked review, without native or intended-model closure.
