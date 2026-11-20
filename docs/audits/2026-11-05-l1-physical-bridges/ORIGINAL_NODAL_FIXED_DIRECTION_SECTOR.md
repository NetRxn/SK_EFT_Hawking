# Original nodal fixed-curvature-direction sector: exact square and local Haar reduction

Task l1-nodal-fixed-direction-sector-r1; owner/notebook writer Executor01a1ac65; parent publication ROOT01a13f67 positive reconstruction. Manual actual construction for separate mathematical/source review. Original source HEAD5ad2c7e0ba6f9236dd27308c609739b3b563c727. This computes a structural factorization of a COMPLETE specified direction sector of P0, not P0 itself and not its value/nonvanishing. Mixed-direction sectors can cancel this contribution.

## Original subtotal and both ordered holonomies

Use unchanged zero-source/baseframe nodal coefficient P0(u0)=integral_(24 spatial U1) I64 A8(u0,U1;V1=I)^16. All original action/world/internal/coframe factors remain. A8 is the EHC sum with both coframes spatial at slice1. Let A3 be its COMPLETE part with curvature world plane {0,3}, hence coframe world directions {1,2}. The internally antisymmetric F_CD(H)=Tr[H gamma_[C gamma_D] gamma5] is the accepted equivalent contraction of the raw original trace; no raw diagonal-trace-zero assumption is used.

At x on slice1 the closed holonomies are exactly

 H03(x)=U1,3(x)† U0,3(x),
 H30(x)=U0,3(x)† U1,3(x)=H03(x)^-1.                         (1)

Both orders use the SAME independently integrated based direction3 anchor, not its neighbor's second periodic anchor. F(H^-1)=-F(H) on the original compact Spin(4) group, while swapping the curvature order flips world epsilon. Swapping coframe directions 1,2 also flips epsilon and, after relabelling C,D, flips F_CD. The four ordered placements therefore cancel the original EHC quarter, as in the accepted original EHC coefficient control. With epsilon^(0312)=+1,

 A3=sum_x X_x,
 X_x=sum_(C,D) F_CD(H03(x)) E1_x^C E2_x^D,                 (2)
 E_j=T_(1,x),j at the original quarter normalization.

In this sector there are no E3 factors. Each U1,3(x) appears ONLY in the curvature at its own center, and every other factor uses direction1/2 anchors within the fixed-x3 square. The independent Haar substitution U1,3(x)=U0,3(x) W_x gives H03=W_x†, H30=W_x for every center, preserving normalized Haar. Thus ALL retained u0 dependence disappears from this sector, for any admissible u0, without assuming flat u0 or identifying any original anchors. This resolves the earlier exploratory report's conditional source question and removes its claim that these curvature anchors still couple the two squares.

## Square factorization of the complete sector

The remaining graph splits into two Q2 squares at x3=0 and x3=1. Each has four sites,32 odd generators, eight independent direction1/2 anchors, and four independent curvature variables W_x. The A3 action is A_L+A_R, with disjoint odd/link variables. Even site blocks give no sign on factorization of inherited top extraction. Each A has degree4, so the ONLY term of (A_L+A_R)^16 that saturates both32-generator square tops is its 8+8 term. The square actions and measures are identical by lattice translation. Define the real number

 sigma_Q = integral_(8 direction1/2 anchors,4 W) I32 A_Q^8.

Then the exact original sector integral is

 P_(3) := integral I64 A3^16 = binom(16,8) sigma_Q^2 >=0.     (3)

Reality follows directly from the original sharp: E_j^sharp=-E_j, the internally antisymmetric compact F is real, so X_x^sharp=X_x; the inherited square Berezin top and Haar commute with conjugation. This is a real square. It is not a sign theorem for P0, since expanding (A1+A2+A3)^16 includes other pure and all mixed-direction products. No coefficient/harmonic isolation of A3^16 from that sum has been proved. The value of sigma_Q is not evaluated.

## Exact local curvature second and fourth moments

Here the E1,E2 components are commuting even Grassmann elements, independent of W_x. Put

 D_x=(sum_C E1_C E1_C)(sum_D E2_D E2_D)
                         -(sum_C E1_C E2_C)^2.             (4)

There is no new metric convention: these are original local coframe polynomials.

For completeness, the convention-independent Clifford/Haar normalization can be checked in each chiral 2x2 block. Write W_chi=a0 I+i sum_j a_j tau_j, with (a0,a1,a2,a3) uniform on S3. Write

 (gamma_[C gamma_D] gamma5)_chi=i sum_j eta_(chi,j;CD) tau_j.

The Pauli trace and Euclidean Clifford relations give

 sum_j eta_(chi,j;CD) eta_(chi,j;EF)
   =delta_CE delta_DF-delta_CF delta_DE +/- epsilon_CDEF.     (5)

The sign depends on chirality/orientation and will cancel below. For b_(chi,j)=sum_CD eta_(chi,j;CD) E1_C E2_D, commutativity of E components makes the epsilon contraction zero, so sum_j b_(chi,j)^2=D_x. Tr(W_chi† i eta.tau)=2 a.eta; hence X_chi=2 a.b_chi and X=X_++X_- with independent chiral Haar variables.

Normalized S3 rotational invariance gives

 E[a_i a_j]=delta_ij/4,
 E[a_i a_j a_k a_l]=(delta_ij delta_kl+delta_ik delta_jl
                                          +delta_il delta_jk)/24.

The constants follow by contracting indices using sum_(i=0..3) a_i^2=1. All odd moments vanish. Thus

 E X_chi^2=D_x, E X_chi^4=2 D_x^2,
 E X^2=2 D_x, E X^4=10 D_x^2.                              (6)

The sign from using W rather than W† is harmless in these even moments. Each X_x contains exactly TWO odd generators at its center, so X_x^5=0 (there are only eight odd components there). Therefore the COMPLETE local curvature integral of the exponential is the finite identity

 integral dW_x exp(z X_x)=1+z^2 D_x+(5/12)z^4 D_x^2.          (7)

This is an exact identity over the remaining exterior algebra, not a positivity claim about D_x or a scalar approximation. The coefficient 5/12 is 10/4!, retaining original quarter coframes inside D_x.

## The resulting four-site coefficient frontier

After integrating curvature variables, the remaining square coefficient contains just direction1/2 links and the polynomials D_x. Exact degree saturation gives three patterns. If m_x counts X_x vertices, then

 2m_x+m_(x+e1)+m_(x+e2)=8.

On Q2 the solution is m_x=2+a(-1)^(x1+x2), a=-2,-1,0,1,2. Equation (7), equivalently independent center parity of each curvature Haar variable, removes odd m_x, leaving a=-2,0,2. For even vertices e1,e2 and odd vertices o1,o2 of a square, it follows that

 sigma_Q = 8! integral_(8 direction1/2 anchors) I32
   [ product_(x in Q2) D_x
       +(25/144)(D_e1^2 D_e2^2+D_o1^2 D_o2^2) ].             (8)

There is no omitted saturation pattern in (8). It includes all internal/endpoint/link contributions inside each D. It does NOT evaluate their signed Haar/Berezin contraction. Neither D nor the individual terms are called positive operators. Equations (3),(7),(8) are the new exact reduction: a nonnegative pure-direction SUBTOTAL represented by one real four-site coefficient square, and an explicit three-pattern expression for that coefficient.

Even proving sigma_Q!=0 would only show P_(3)>0, not P0!=0, because mixed-direction sectors remain. A useful future construction might organize ALL sectors into compatible squares or control their cancellations, but no such identity has been established here. No scientific run or cost admission is requested; the present expression is not a claimed complexity bound.

## Custody and limits

Exploratory lead/worker discussion preceded this frozen formal write-up. The valid task packet was created and checked fresh before the formal construction. All reasoning is manual, with static accepted-source reading and ordinary continuity/artifact bookkeeping only. No scientific evaluator/CAS, matrix/exterior/Haar/Gram program, Lean/build/test/controller/slot/GPU or repository/notebook modification occurred. Actual independent math/source review is required before adoption.

Sources: accepted ORIGINAL_NODAL_BOUNDARY_REDUCTION and its reviews, ORIGINAL_ONE_SLICE_SOURCE_KERNEL sections1–3, ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT internally antisymmetric compact trace identities and four ordered world placements, P0_NUMERICAL_FULL_CUT_TRANSPORT closed holonomy/gauge convention. The original full-source P1–P4/physical product/adjoint/domain/constraint/kinetic/dynamics and publication objectives remain open. This zero-source sector reduction supplies none of their missing intertwiners and establishes no one-slice positivity/nonpositivity.
