# Original nodal one-slice coefficient reduction — partial construction

Task l1-nodal-boundary-reduction-r1; parent publication-remediation-01a13f67/l1-positive-physical-reconstruction. Sole notebook writer Executor01a1ac65. Frozen source 4aaebb7974e714dd49e052357b9677e9325ba141. Manual mathematical result for independent actual review. No coefficient has been numerically or symbolically evaluated; no positive factorization or physical positivity theorem is claimed.

## Original object and exact scope

Keep the original P convention, periodic 2^4 sites, 128 odd generators, all 64 independent anchored Spin(4) links, quarter coframe, full determinant and closed EHC world/internal sums with their original factors, exp(+S), normalized Haar and original Berezin orientation. Base J=0, A=I only. Retain u, the 24 slice-0 spatial anchors; integrate the remaining 40 anchors v. Let

 w(u;xi0) = integral dv I_1 exp(g1 S4+g2 S2),
 ell_u(f) = I_0[w(u;xi0) f(xi0)].

The slice orders and I_0,I_1 are the inherited factorization of the original top extraction. Reordering full slices introduces no sign because their dimensions are even. The original trace-dual matrix is R_b(u), characterized by ell_u(f)=Tr[R_b(u) W_b(f)]. This is the same object as coherent-bridge section 7; it is not a new density ansatz. Finite Grassmann duality and invertibility of W_b imply R_b(u)=0 iff w(u)=0 iff ell_u(f)=0 for every f. No Weyl/exterior multiplicativity is assumed.

On the accepted spatial cancellation locus u', the two slice-0 anchors on each of the twelve endpoint pairs obey V=U†. This is evaluation of the existing link polynomial, not a change of measure. All slice-0 spatial coframes vanish at both endpoints. The accepted complete cancellation audit then eliminates every action term centered at slice 0, while the surviving slice-1 terms have bidegrees (old,new)=(0,4),(1,3),(1,7). Both temporal anchor sets stay independent.

## Complete boundary-grade classification

Define the ACTUAL sums of surviving vertices by their bidegrees, with no coupling included:

 A=(S2)_(0,4), B=(S2)_(1,3), C=(S4)_(1,7).

These are projections of the full original action at u', not independent coframe variables or fitted vertices. They retain all internal sums, all ordered world tuples, the EHC 1/4 and original coframe quarters. They are even, so

 exp(S|u')=exp(g2 A) exp(g2 B) exp(g1 C).

For A^a B^b C^c to survive I_1, new degree must be 4a+3b+7c=64. Its residual old degree is p=b+c. Hence

 4(a+c)+3p=64,
 p in {0,4,8,12,16,20},
 a=16-3p/4-c, b=p-c,
 0<=c<=min(p,16-3p/4).

Consequently the complete boundary polynomial at the node is w=sum_p w_p with

 w_p = sum_(c=0..min(p,16-3p/4))
       g1^c g2^(16+p/4-2c)
       /[(16-3p/4-c)! (p-c)! c!]
       integral dv I_1 A^(16-3p/4-c) B^(p-c) C^c.                 (1)

This includes 1,5,9,8,5,2 summands in the six degree blocks (30 total). Those are formal candidate terms, not assertions that their coefficients are nonzero. Internal or Haar identities may annihilate them. Terms with other p are identically absent by the exhaustive bidegree enumeration, not omitted for convenience.

In particular, for a homogeneous boundary Majorana test of degree k, ell_u'(theta_I) can be nonzero only if k=64-p, namely

 k in {64,60,56,52,48,44}.                                    (2)

All smaller-degree moments vanish at u'. This includes ell_u'(1)=Tr R_b(u')=0. Equation (2) concerns the inserted moment degree; it does not assert that R_b's Weyl degree equals p. The exterior integral uses complementary degrees, whereas trace-dual Clifford reconstruction uses the test degree k.

If R_b were PSD at this node, trace zero would force R_b=0, hence every full polynomial block w_p(g1,g2)=0. For a finite or Haar-labelled positive Gram grouping, its amplitudes would therefore have zero norm there (a.e. in the internal Haar label; continuity and full support are needed to strengthen to every label). This is a necessary admission condition on any proposed positive grouping, not an evaluated obstruction.

At a single fixed physical/candidate coupling one may require only the WEIGHTED sums in (1) to vanish. One cannot declare every separate coupling coefficient zero from positivity at that point. Positivity on an open coupling set would add a polynomial-identity argument. The present result makes neither positivity claim.

## The first exact coefficient frontier

The p=0 block has just one term:

 w_0(u') = g2^16/16! P0(u0),
 P0(u0) = integral dv I_1 A^16.                               (3)

A contains two spatial coframes at a slice-1 center. Its complementary curvature world indices are therefore exactly one temporal and one spatial index. By the accepted original one-slice kernel section 1, this curvature depends on slice-1 spatial anchors, the forward temporal anchors based at slice 1, and the retained slice-0 spatial anchors; it never depends on the backward temporal anchors based at slice 0. The spatial coframes also do not depend on those backward anchors. Their eight normalized Haar integrals therefore give exactly 1 in (3).

One can further integrate out the eight remaining temporal anchors without replacing the ensemble. Use the original source-to-target gauge convention U_(x,mu)'=G_(x+mu) U_(x,mu) G_x^-1. Keep G_(0,x)=I and choose G_(1,x)=V_(1,x), where V1 is the forward temporal anchor from slice1 to slice0. Then V1'=I. In the actual new integration coordinates,

 U1'_(x,i)=V1_(x+i) U1_(x,i) V1_x^-1,
 psi1'=V1 psi1, barpsi1'=barpsi1 V1^-1.

For fixed V1 this is a bijective translation of each of the 24 spatial Haar variables, with unit Haar Jacobian. Spin(4) has det=1 in the four-component spinor representation, so the Berezin Jacobian and inherited top extraction are unchanged. The original closed holonomy and internal contraction are gauge invariant; slice-0 variables and retained u0 are unchanged. The discarded slice-0 temporal anchors may transform but were already absent from A. Thus the transformed integrand is independent of V1 and those eight normalized integrals also give 1.

The exact unevaluated frontier is therefore

 P0(u0)= integral_(Spin(4)^24) dU1 I_1 [A_8(u0,U1;V1=I)]^16,    (4)

where A_8 means precisely the same full original (0,4) EHC vertex sum at the eight slice-1 centers, with its 64 odd generators and all coefficients untouched. No orientation factor is inferred by collapsing the original ordered world sum. Equation (4) is a lower-dimensional ORIGINAL coefficient integral, not a new independent-background action or a numerical algorithm. One may additionally choose flat retained u0=I as a particular admissible node; that would test only that node.

A nonzero P0 at any node with g2!=0 would imply w!=0 and therefore nonzero R_b with trace zero; given the accepted real-source Hermiticity, this would refute R_b PSD there. Continuity would then be needed to extend a strict negative eigenvalue/effect off that node. We have NOT established P0!=0 or P0=0. If P0=0, the remaining five grade blocks still need investigation. If all six vanish, this necessary nodal condition alone still does not establish positivity elsewhere.

## What has and has not advanced

New manual result: complete inserted boundary-grade reduction and exact 30-term formula; identification of the single p=0 coefficient; exact removal of 16 irrelevant/gauge temporal integrations from that coefficient. This sharpens one necessary target for a constructive amplitude grouping. It does not provide an amplitude grouping, evaluate any coefficient, or settle one-slice positivity. The separately tested coefficientwise self-pairing is a different bounded attempt and its failure is not used as proof here.

This is a zero-source/baseframe diagnostic. General source/frame derivatives can create temporal and mixed vertices outside these bidegrees. Full defect-inclusive pair kernels, both cuts, Bopp insertions, all C2 contacts, physical product/adjoint/constraints and kinetic/dynamical normalization remain required. No claim of full-source nodal vanishing or a physical Hilbert reconstruction follows.

Provenance: full accepted spatial-record result and original one-slice kernel sections 1–3, coherent-bridge section 7, plus accepted process coefficient/graded-embedding passages. Same source HEAD4aaebb. Only static reading and manual reasoning; no scientific evaluator, CAS, Lean, build, controller or slot action. Three initial packet-creation invocations were refused for schema/location mistakes before a valid team-lead packet was created in the primary local continuity directory; the valid packet's initial check was fresh=true, changed=[]. No failed packet was treated as authority. No repository/notebook edit has occurred. Independent actual mathematical and source review remain required.
