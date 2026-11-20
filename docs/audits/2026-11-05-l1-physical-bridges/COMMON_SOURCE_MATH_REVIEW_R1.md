# Independent mathematical review: common source/matter interface r1

**BLOCK pending one explicit regularity/interchange hypothesis repair.** The finite-algebra elimination and displayed ordered derivative/contact formulas are mathematically correct for sufficiently regular, locally dominated source families. The frozen general sections do not state those hypotheses, and their present positive-body/nilpotence assumptions admit a concrete nondifferentiable counterexample. No algebraic sign, ordering or contact error was found in the explicit smooth section5 family. The repair is bounded and does not require a scientific contraction campaign.

Candidate: `docs/audits/2026-11-05-l1-physical-bridges/COMMON_SOURCE_MATTER_INTERFACE.md`, SHA256 **8b30768c41d90b542f4d776f726833a9ee248ed1d0995f302ae2490cf8239bc2**, read in the assigned isolated checkout at425324077b03d7de1db9f4a342f5a760bf7af001. This verdict applies only to those exact bytes.

## Required repair: state C² families and justify differentiated integrals

**Lines39–68 and81–105; also source family at142–147.** Only J is expressly called smooth. There is no explicit requirement that gbar, Q, the prescribed coframe family/S_g, regulator pullbacks and any other source-dependent coefficients be twice continuously differentiable. Nor is coefficientwise local domination given for interchanging source derivatives through Haar/scalar integration. Finite Grassmann degree makes nilpotent expansions finite; it does not make coefficient functions differentiable or integrable. Pointwise convergence of a positive-body Gaussian alone does not justify its differentiated integrals. Even the continuity invoked at82 needs regularity and integrability of the parameterized full integral.

A concrete counterexample already exists at lambda=0 without any noncommuting difficulty. Keep S_g and J source-independent with finite nonzero gravity partition Z_g, keep standard fixed positive cell weights/difference maps and mass m>0, and set

`s(h)=1+|h|`, `gbar(h)=s(h) I_4`.

Every stated body/nilpotence assumption holds. With L the ordinary positive-semidefinite lattice Laplacian and eigenvalues ell_j>=0, rho=s², F=s I and the scalar kernel is

`K(h)=s L + m² s² I`.

The matter kernel is positive definite for every h. Scalar and gravity factors separate, so with K_ref=K(0),

`W(h)=-(1/2) sum_j log[(s(h) ell_j+m² s(h)²)/(ell_j+m²)]`.

It is real, continuous, normalized and has nonzero denominator near zero, but its right derivative at0 is

`-c`, `c=(1/2) sum_j (ell_j+2m²)/(ell_j+m²)>0`,

while its left derivative is+c. Thus W_a and W_ab at0 do not exist despite satisfying the written domain conditions. This uses the stipulated nonzero gravity denominator rather than constructing or asserting one for the microscopic action. The ordinary scalar subfactor already defeats the general differentiation claim.

Recommended precise repair: require all source families to be coefficientwise C² on a common source neighborhood; for the fixed finite lattice/compact Haar domain require joint continuity/boundedness of their coefficients and source derivatives through order2, or explicitly sufficient common integrable domination. Require a locally uniform positive lower bound K_body>=kappa I, kappa>0, on a smaller source neighborhood. The original polynomial composite/action with a fixed smooth A and fixed regulator has bounded coefficients/derivatives on compact Haar times a compact source sub-neighborhood; a continuous positive body depending only on those finitely many sources/sites has the needed local gap after shrinking. Explain that the finite nilpotent expansion and its first/second derivatives are bounded coefficientwise by C(1+||phi||^d)exp(-kappa||phi||²/2), with finite d and uniform C, so Haar/Gaussian derivatives and finite Berezin extraction can be interchanged. If more general moving regulators are allowed, impose this after the specified pullback; merely naming J is insufficient. Then continuity of the real full Z and its assumed Z(0,lambda)!=0 give a smaller neighborhood bounded away from zero and the stated real local normalized logarithm. These are regularity hypotheses, not a positive-state premise.

## Independently checked mathematics, conditional on that repair

**Finite-even-algebra Gaussian elimination.** In the finite even subalgebra the coefficient ring is commutative. Write K=K_body+N with every entry of N in one common nilpotent ideal I and I^r=0. Then K_body^-1 N has rth matrix power0: each product contains r ideal entries. Its inverse expansion therefore terminates. Likewise exp(-phi^T N phi/2) terminates at r-1, leaving finitely many ordinary Gaussian polynomial moments. The ordinary positive-matrix Gaussian determinant identity extends by its finite Taylor expansion to these commuting nilpotents. This yields the exact sqrt(detK_ref/detK), with the body-positive square-root branch and finite nilpotent continuation. No arbitrary zero-body inverse or positivity of the subsequent Berezin/Haar functional is used. The notation Tr log(K/K_ref) should be read according to the candidate's explicit determinant-ratio convention, namely log detK-log detK_ref, not an assumption of commuting matrix factors.

**Normalized signed derivatives.** With L=S_g+J-(1/2)log(detK/detK_ref), C=K^-1 and fixed lambda, C_b=-C K_b C and d_a logdetK=Tr(C K_a). Consequently

`L_ab=S_g,ab+J_ab+(1/2)Tr(C K_b C K_a)-(1/2)Tr(C K_ab)`.

The quotient rule for I_g(O expL)/Z gives exactly the candidate's normalized-expectation and W Hessian formulas. Cyclicity over the commutative coefficient ring proves symmetry of the mixed trace term without commuting C,K_a,K_b. The conditional scalar covariance/contact and outer geometry connected term remain distinct. At lambda0 under the stated factorization premise, the two full logarithmic Hessians add, including their contacts. Neither signed connected expression is a positivity theorem.

**Ordered metric derivatives.** Differentiating BM=I gives B_a=-B H_a B and

`B_ab=B H_b B H_a B+B H_a B H_b B-B H_ab B`.

Differentiating rho=exp((1/2)logdetM) gives the candidate's rho_a and rho_ab with coefficient-1/2 on tr(B H_b B H_a). Applying the product rule F=rho B gives all six terms of its F_ab, with BOTH distinct orderings retained. H_ab must include the differentiated nilpotent Q contribution; no assumption of diagonal Q is needed. Inserting those derivatives into the same fixed quadratic form yields K_a,K_ab and retains the mass-density contact.

**Gravity/coframe and common path contacts.** For symmetric bilinear B_g, differentiating B_g(AT,AT) at A=I gives exactly2B_g(A_aT,T) and2B_g(A_abT,T)+2B_g(A_aT,A_bT). g2 and S4 variations are properly retained; a general affine path is not determinant one. h=2sqrt(2)j is consistent with E=sqrt(2)P and A_exp=exp(hP/2).

For P=diag(0,0,1,-1)/sqrt(2), trP=0 and trP²=1. A_exp'(0)=A_aff'(0)=P/2, while their accelerations differ by-P²/2. Thus the chain rule for the SAME normalized joint functional gives

`W_aff''-W_exp''=-(1/2) D_A mathcal W(I,lambda)[P²]`.

The common first vertices, and therefore their outer connected terms, coincide. The right side contains the scalar determinant and its geometry reweighting. A symmetry killing the P direction need not kill P².

To check the noncommuting formulas directly, use F=rho A^-T B0 A^-1. Along exp, rho=rho0 and (A^-1)'=-P/2, (A^-1)''=P²/4. Along aff, rho'(0)=0, rho''(0)=-rho0/2 and (A^-1)''=3P²/4. The product rule yields exactly the displayed exp/aff F'' and their difference, retaining PB0P separately from P²B0 and B0P². This is an ordered identity for arbitrary even symmetric nilpotent Q; no matrix commutation was inserted.

**Scalar zero-coupling controls.** At B0=I, F_exp'=-P, F_exp''=P² and F_aff''=2P²-I/2, rho_aff''=-1/2. These imply the displayed Fourier K', K_exp'' and K_aff'', including the mass term inside-K0/2. The log Gaussian Hessian is one half the sum of the squared first-kernel ratio minus the second-kernel ratio.

I independently ran a tiny stdlib-only exact Fraction enumeration over16 periodic momentum modes, mass=spacing=1 and phat_mu² in{0,4}. It obtained:

- connected scalar contribution193312/342225;
- exponential full scalar Hessian-6288976/5817825;
- affine full scalar Hessian7407044/5817825;
- affine-minus-exponential7804/3315, independently equal to4-sum_p[(phat_2²+phat_3²)/(4K0)]=4-5456/3315.

These match the separately read author artifact `/private/tmp/l1-common-source-scalar-path-check-r1.json`; the independent enumeration, rather than that artifact alone, supports this arithmetic check. It is a free scalar contact check, not a geometry contraction or a physical source match.

## Reuse, composition and acceptance limits

Previously reviewed gravity variations, determinant expansion, first-order mixed-response identity and dimensionless bubble remain reused inputs, not newly executed/re-certified coefficients. The candidate's useful new composition is the common all-orders finite-algebra functional, ordered metric-to-kernel source vertices and common affine/exponential contact identity including matter. The finite-dimensional dimensional accounting is consistent: dimensionless uniform metric strain has intensive Hessian mass dimension4; a controlled p² coefficient would have dimension2, whereas the scalar two-propagator bubble alone has dimension0. This does not derive a derivative expansion, tensor projection, microscopic normalization or the original chi interval.

No new physical source, positive body/state, lambda value, common microscopic denominator, transfer reconstruction, tensor/matter-light dynamics, retarded transport, B3 range, Lean theorem or full pipeline/publication acceptance follows. The BLOCK is the stated regularity/interchange gap; after its repair, source-pinned re-review is required. It is not a counterexample to the explicit smooth fixed-polynomial section5 comparison.

## Authority and actions

First command and final command immediately before writing this report were the assigned `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-common-source-review-r1.json` from the assigned checkout; both returned fresh:true/changed:[]. Read the packet, designated primary notebook, current Phase6a ownership/boundaries and referenced branch-selection/successor roadmap; governing primary AGENTS/CLAUDE/WAVE/ADR-008/ADR-017/continuity bytes match the earlier reviewed authorities. Candidate hash was independently computed using hashlib.

Other actions were read-only file/text inspection and the one tiny `python3 -B -` Fraction/itertools/hashlib control described above, with no project science imports. No Git, Lean/build, slots, process/harness/configuration action, scientific contraction, candidate/notebook edit or other write occurred. Only this reviewer-owned report was written.
