# Exact curvature loop factorization: prospective design

This is a mathematical representation change for the already assigned full
four-site leading metric tensor. It changes no action, coupling, gauge tree,
Haar measure, support roster, row/product cap, deadline or acceptance boundary.
Two previous orderings reached the original row cap; improved feasibility of
this factorization is a hypothesis, not an accepted result.

## Identity and scope

For distinct Euclidean Clifford indices a,b let K=gamma[a] gamma[b] gamma5.
With H=D† C† B A, the existing reduced curvature numerator is
C_old=Tr((H-H†)[gamma[a],gamma[b]]gamma5).
For the block diagonal quaternion algebra used by the actual helper matrices,
H+H† is a scalar multiple of I2 separately in each chiral block; K is traceless
in each such block. Thus Tr(H†K)=-Tr(HK), while the Clifford commutator is
2 gamma[a] gamma[b]. Consequently C_old=4 Tr(HK).
This is a polynomial identity in real quaternion coordinates, including the
independent partial-chirality basis matrices and the full identity matrix.
For a=b the original commutator is zero: explicitly omit those entries.
Do not extend the formula to diagonal a=b or arbitrary complex block matrices.

## Factor network

Replace each high-arity curvature table by four link matrix factors and one
gamma factor. Introduce five fresh Dirac legs s0,...,s4, each of domain 0..3:

    D†[s0,s1] C†[s1,s2] B[s2,s3] A[s3,s4]
    epsilon(k,l,mu,nu) K_ab[s4,s0], a != b.

Each link factor has its original independent quaternion occurrence leg plus
its two Dirac legs; a gauge-fixed link uses the full I4 and has no quaternion
leg. Every new Dirac leg occurs exactly twice. No chiral state, internal gamma
index, occurrence, link moment or channel is selected or discarded. The same
physical repeated link occurrences still meet in the same joint Haar factor.
The unchanged indexed_join and the reviewed domain-based ordering contract
these factors. No replacement contraction engine is introduced.

## Exact normalization

The new integer Gaussian network computes C_new=C_old/4. The old curvature
quarter is therefore absorbed exactly; frame quarters remain unchanged. For
the target word, 16 frame quarters give 4^16 rather than 4^21. The eight-S2
normalization control likewise has 16 frame quarters, not its old 24 quarters.
Couplings and physical amplitudes are identical. Record curvature_vertices
separately from curvature_quarters=0 and label this representation explicitly.
Update producer assertions and independent parent Fraction readback together.
Compare old/new physical Fractions, never raw numerators alone. Haar and
multiplicity factorial divisors are unchanged. The physical remainder bound
and accepted full denominator are unchanged.

## Mandatory independent controls and execution gate

Keep the old curvature_table byte-for-byte as an unreduced reference. A local
adapter contracts just the five new curvature factors, leaving original free
quaternion legs and a,b open, using the same capped indexed_join. For all 16
fixed-link patterns compare the entire sparse open tensor: identical nonzero
key sets and 4*C_new=C_old coefficientwise, retaining both real and imaginary
parts. Fixed-pattern controls are algebra tests, not enlarged gauge fixing.

The actual curvature control must then evaluate the new representation against
the full original 24-world action and literal-order poison. All existing frame,
Haar, determinant, tiny-sign/alarm and exact 104978 normalization controls stay
mandatory. Verify new normalization metadata independently. Only after design
and source reviews plus resource admission may a changed full attempt run,
with original 600-second preparation, 1800-second whole-tensor warm window,
2465-second parent ceiling, 120000-row and 3000000-product caps. All ten tensor
coordinates and all 480 support entries remain the scope. No unchanged retry
or cap increase follows from failure.

Independent reviewers should challenge the quaternion trace identity, dagger
and trace order, diagonal exclusion, normalization change, full-index retention
and whether local controls independently exercise actual producer factors.
No claim of kernel proof, full tensor completion, collective physical body,
state/matter/tensor/transport closure or publication qualification follows.
