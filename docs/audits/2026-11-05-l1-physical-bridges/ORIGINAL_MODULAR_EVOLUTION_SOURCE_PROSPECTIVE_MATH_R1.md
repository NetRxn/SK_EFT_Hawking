# Independent prospective mathematical review — modular evolution/source R1

Verdict: **ACCEPT ATTEMPT** for the frozen bounded manual construction. This is prospective mathematical acceptance, not acceptance of an unproduced result or of physical L1. No missing design requires another permission cycle. The intended tasks below are real construction tasks, not prerequisites that must already have been proved before attempting them.

Task: l1-modular-evolution-source-r1; parent publication-remediation-01a13f67/L1-physical-dynamics-matter. Candidate source: 6f78e5b63c6866aa09b8bc48d3d6cf3946aad262. Packet: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-modular-evolution-source-r1.json. Frozen brief SHA256: 5a9021ce2e90e6b52ef884be49158bfde74d684a9242e66440adfb91757a97ea. My sole output is this private report. Executor01a1ac65 remains the notebook writer and candidate author; ROOT retains findings/gates, manuscript, physical acceptance and integration authority.

## Inputs and process

I inspected the frozen packet and brief, AGENTS.md, CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, CODEX_CONTINUITY.md and the ADR-008/017 role contracts; the referenced current Phase6a opening and notebook scientific frontier; and the actual accepted process reconstruction, its acceptance, original normalization construction and kinetic sections 7 and 10. Source pointers below are relative to docs/audits/2026-11-05-l1-physical-bridges/ in the assigned checkout. The governing context is that B3 and physical mode/transport remain OPEN BUILD; accepted finite state/channel results are retained.

Explicit initial checker command, from the assigned checkout:

    python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-modular-evolution-source-r1.json

It returned fresh=true, changed=[]. Ordering deviation: my literal first tool call read the packet, and a subsequent read located the checker command and read the brief; the explicit checker was the third tool invocation. This did not comply with the requested first-action order. It preceded substantive mathematical work and all output mutation. The final same-packet check is recorded below; I did not refresh the packet.

No repository, notebook or Git edit, scientific evaluator/CAS/Haar/exterior/Gram/matrix execution, Lean/build/test, slot/controller or process action was performed. Only static reads, continuity bookkeeping and this report write/hash are in scope. No memory-derived scientific assertion is used.

## 1. Candidate and coordinate freedom are specified sufficiently

Kinetic result equations (30)–(31) constrain an intertwining diagram, not a positive adjoint or a physical time. If invertible cut coordinate changes G_in(q), G_out(q) act on the target carriers, the transformations are I'_in=G_in I_in, I'_out=G_out I_out and T'=G_out T G_in^{-1}. Differentiate these products, including (G^{-1})_alpha=-G^{-1}G_alpha G^{-1} and the mixed inverse derivative. This supplies the actual first/mixed contact terms; neglecting them would change (31).

The chosen fixed M_d product and dagger, usual C^d Hilbert space, accepted W_b and explicit modular U_b are a concrete candidate to test. They add structure that the linear diagram alone does not select. For a general linear coordinate change the product and star must be pulled back too. If the usual product and star are held fixed and the change is a unital algebra automorphism, preserving star restricts its implementer to unitary conjugation up to a scalar. A merely positive inner product does not by itself enforce multiplicativity; transforming its metric is coordinate covariance, not a new physical prediction. The report should distinguish observables, density matrices and their dual transformations.

h=-log rho and U(t)=exp(-it h) are well defined and C2 in q on the actual positive neighborhood. The modular parameter is dimensionless; neither laboratory time nor a microscopic metric product follows. Global phase/gauge covariance must use the original Ward representation, with no imposition of singlet support on a faithful state.

## 2. Actual gap makes the candidate test decisive in both directions

ORIGINAL_TRANSFER_POSITIVE_PROCESS_RECONSTRUCTION.md sections 1–3 prove at the explicit g*=g(Lambda), Lambda=1+M, that tau>=I/(2D), tau^(T0)>=I/(2D), rho_b>=I/(2d), where d=2^32 and D=d^2. These are actual original all-coefficient bounds at that point, not a conjectural generic faithful state, and they are not being asserted at the earlier g0. Z>0 comes from accepted normalization and exact scaling.

For input b, F_b=(rho_b^T)^(-1/2) tensor I and C_b=F_b tau^(Tb) F_b. At g*,

    C_b >= [2D lambda_max(rho_b)]^{-1} I >= (2D)^{-1} I.

The reverse direction is valid because tau^(T1)=(tau^(T0))^T; full transpose preserves the positive lower bound. Reorder the two tensor factors explicitly for the reverse Choi convention. No physical reflection-adjoint assumption is used. Continuity gives a real C2 neighborhood; a uniform numerical lower bound on a smaller neighborhood must be stated with its actual continuity choice rather than silently reusing the point bound.

In the fixed convention |U>>=sum_i |i> tensor U|i>, a unitary channel has C_U=|U>><<U|. For any i != j, v=|i> tensor U|j> is unit length and orthogonal to |U>>. Thus

    <v,(C_b-C_U)v> = <v,C_b v> >= (2D)^{-1} > 0

at g*. This is a concrete failed matrix identity for every t, including t=0, and both directions. No enormous matrix evaluation is needed. The result concerns equality to a unitary conjugation on this full fixed cut algebra. It excludes neither quantum-link enlargements nor noninvertible physical cut maps; it must not be promoted to an original-model no-go.

The full-moment uniqueness and nontracial sandwich are essential: Tr[tau(A tensor B)]=Tr[B E(rho_in^(1/2) A rho_in^(1/2))], with the accepted odd/odd strings. Here E is the Schrodinger CPTP map on matrix arguments. The modular conjugation comparison must use that same map convention and filtered input, not interchange it silently with a Heisenberg dual. All ordinary products and source-dependent test jets are part of the comparison.

## 3. Complete temporal log/Duhamel contacts are feasible

Use R_b=Z rho_b, H=-log R_b. At the full pair level obtain R_alpha and R_alphabeta from the accepted Bopp insertions and actual Q_r00 in kinetic section 7, then partial trace. Both interfaces enter the two-step derivative; first mixed insertions and genuine s_alphabeta contacts are distinct. This is not W_b(Q_r00) as a marginal multiplier.

For G_u=(R+uI)^(-1), the required manual identities are

    Dlog_R[X] = integral_0^infinity G_u X G_u du,
    D2log_R[X,Y] = -integral_0^infinity (G_u X G_u Y G_u + G_u Y G_u X G_u) du.

Hence O_alpha=-H_alpha=Dlog_R[R_alpha] is Hermitian for real source directions. Its mixed contact O_alphabeta=-H_alphabeta equals Dlog_R[R_alphabeta]+D2log_R[R_alpha,R_beta]. It is not obtained by multiplying first scores. Positivity bounds justify these integrals and C2 differentiation.

The exact first Duhamel identity is

    R_alpha = integral_0^1 R^(1-u) O_alpha R^u du.

The mixed identity contains the same integral with O_alphabeta plus the integral over a+b+c=1, a,b,c>=0, of both ordered products R^a O_alpha R^b O_beta R^c and R^a O_beta R^b O_alpha R^c. The simplex measure is da db (c=1-a-b); in the scalar case each ordered term has weight 1/2. This checks the factor and signs. A first-derivative identity alone is insufficient.

Since h=H+log Z I, the normalized source operator is -h_alpha=O_alpha-(Z_alpha/Z)I. Its mixed contact subtracts [Z_alphabeta/Z-Z_alpha Z_beta/Z^2]I. Keep the numerator derivatives, these denominator derivatives, all test derivatives, the filter derivatives and actual curved-frame acceleration. For arbitrary full original test f(q), the underlying mixed integrand is exp(s)[f_alphabeta+f_alpha s_beta+f_beta s_alpha+f(s_alphabeta+s_alpha s_beta)], before normalization. The accepted section 7 current contacts and the full two-step product have additional actual vertex placements as recorded there. This supplies the requested literal-source Hamiltonian, but its identification with the physical Ehat_mu Ehat_nu product remains an independent matching test.

## 4. Adverse control and next finite construction are meaningful

A sufficient exact control is sigma(q)=diag(p(q),1-p(q)), 0<p<1, tau=sigma tensor sigma. Its actual filtered Choi matrix is I tensor sigma and its map is E(X)=Tr(X)sigma. The modular U of sigma preserves sigma, as does this reset map. Nevertheless v=|0> tensor U|1> gives the Choi discrepancy 1-p>0. Its first/mixed source jets are -p_alpha and -p_alphabeta; allowing an arbitrary supplied C2 p includes path acceleration. U's phase jets are still included when differentiating the complete witness, although its expectation reduces exactly to 1-p. Thus matching a faithful state and all its source-dependent marginal values does not establish matching evolution. This is a control, not an N16 calculation.

The actual C>0 has rank d^2=D. A Kraus representation therefore needs at least D operators, and the principal-root column construction attains D. The minimal pure Stinespring environment dimension is D, not rank(rho), d or an unexplained new species count. If S=C^(1/2),

    S S_alpha+S_alpha S=C_alpha,
    S S_alphabeta+S_alphabeta S=C_alphabeta-S_alpha S_beta-S_beta S_alpha.

The gap ensures unique solutions. This adds an exact environment/rank consequence to the already accepted conditional dilation; it does not itself identify an original microscopic environment or one-step dynamics.

## 5. Exact remaining original-kernel task

The next viable original construction is a cut-map/descent test, not another proposal to call the conditional channel physical. Specify the actual source-dependent input/output maps A_s, B_s on the original cut domains and test

    B_s L_s = E_s A_s.

Its first derivative has two terms on each side. Its mixed derivative is

    B_ab L + B_a L_b + B_b L_a + B L_ab
      = E_ab A + E_a A_b + E_b A_a + E A_ab.

Null stability requires ker A_s subset ker(B_s L_s), with the actual C2 null-section relations, not merely a zero norm at one source point. A quotient interpretation must explicitly establish the relevant cut ranges/products/adjoints. Testing each s must preserve the copied/shared variables and both periodic interfaces. The full two-step closure must recover the original graded sewn trace/all-test functional, with its unweighted Z and source jets.

Additional original kernel contractions ARE necessary to test this descent for concrete A_s,B_s: the open one-step boundary matrix elements of L_s between their actual input/output test bases, with retained original spatial/link variables as required by those maps; their literal Q_r00 first insertions; the second two-insertion and s_alphabeta/frame-acceleration contacts; and their source-dependent boundary-test contacts. Both steps and both sewings must be included. The accepted cycle-derived tau and its E alone do not supply these open one-step matrix elements or their null relations. Existing accepted symbolic L_s definitions can be reused; this is not a request for a new scientific run or arbitrary extra contraction. If the present bounded result stops after identifying these contractions, it must label descent unevaluated rather than claim an original causal realization.

## Scope and acceptance boundary

This is a coherent new bounded candidate test beyond the old optional spatial-record, Lorentz-cycle and wedge-nilpotence failures: it specifies a state-derived product/adjoint/evolution candidate, constructs its literal-source operator with complete contacts, and can compare it against a proved original-channel gap. Its negative unitary test is predictable from the accepted full rank, but its precise frozen-cut matching identity and source construction are substantive. The author must deliver the actual derivations and independent actual reviews must check them. Prospective acceptance proves none of those future deliverables by itself.

All original N16 dynamics,128 generators,64 independent anchors, quarter coframes, complete determinant/EHC action, exp(+S), literal J, prescribed frame family and both interfaces remain fixed. Quantum-link/time construction, physical tensor/matter coupling, calibration, controlled limits and original publication acceptance retain their full requirements. A modular candidate failure cannot replace those objectives or authorize a favorable state restriction.

Final same-packet explicit checker returned fresh=true, changed=[] after the report was written. No source or authority reconciliation was necessary. A further final check and report SHA256 are returned in the handoff; report contents do not claim a self-referential hash.
