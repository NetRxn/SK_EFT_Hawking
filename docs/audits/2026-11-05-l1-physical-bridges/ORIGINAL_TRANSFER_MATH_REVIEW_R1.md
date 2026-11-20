# Independent mathematics review: original transfer/source operators r1

**ACCEPT the actual constructive auxiliary transfer/source representation. No necessary mathematical correction found.** Bounded transfer operators, their finite-rank two-step product, the original periodic supertrace and compared antiperiodic ordinary trace, and the literal insertion/source-contact formulas are valid. This is a concrete construction from the original finite action, not only a failed-dictionary argument. It supplies no positive physical density, physical adjoint, CAR quantization, nonzeroZ or thermal/continuum interpretation.

Frozen candidate `/private/tmp/l1-original-transfer-operator-r1.md` SHA256 **975ad00ddfdd6c646ff3d95e0e2e42bd6634f2487d43edb8b36dd4ec8e514a66**, independently confirmed using stdlib pathlib/hashlib. Parent checkpoint93338ee2490177b5f7c1d363d217fba05da68a13 remains unchanged. Only this report is written.

## Original locality and finite periodic fields

At one base layer the original symmetric coframe uses only that layer and its immediate temporal neighbors. Its temporal backward anchor is in the preceding layer, while its forward anchor is in the base layer. A temporal plaquette uses temporal links at the base and spatial links at base/next time; spatial plaquettes remain in the base slice. Linear world-frame mixing and Q(T(j)) change no underlying support. Therefore every base density has exactly the safe three-slice dependence s_t(q_(t-1),q_t,q_(t+1)); no fourth layer or inverse is hidden.

One layer has64 Grassmann variables and32 Spin(4) anchors, comprising24 spatial and8 temporal links. Two physical layers give the original128 generators and64 independently anchored links. Keeping each temporal link with its base layer does not constrain or duplicate it.

For composition, a,b,c,d are independent FORMAL layers. Periodic diagonal identification(c,d)=(a,b) produces precisely w1(b,a,b)w0(a,b,a), with b physical time0 and a physical time1. Each density then uses the same physical neighbor layer on both sides, with independent directed temporal anchors retained in its two layers. Exterior substitution handles coincident vertex fields. No independent endpoint copies remain to be integrated as physical degrees of freedom after periodization. Swapping two64-generator top blocks is sign-positive, consistent with the accepted original orientation.

## Bounded transfer and genuine finite rank

The declared H=L2(G²) tensor Lambda(C^128) has positive coefficient/Haar norm solely as an auxiliary Hilbert space. The displayed formula integrates the discarded layer a and extracts its64-generator top, keeps shared b literally common, and creates the new c variables. Exterior multiplication/top extraction are bounded linear operations in a FIXED finite-dimensional exterior space. All finitely many coefficients of w_t are continuous polynomials on compact link groups, hence uniformly bounded at fixed sources. Pointwise Cauchy-Schwarz for normalized a-Haar, followed by b,c integration, bounds the output norm by a finite constant times the input norm. Thus T_t extends to every L2 wavefunction, not merely polynomials; evaluating shared b is not an illicit L2 diagonal restriction because b is never separately integrated as two independent variables at this step.

Extracting64 generators is even, and w_t is even, so T_t preserves total pair parity. Even extractors commute and even weights can be pulled through them without sign. Substitution of the first transfer into the second therefore gives exactly

KPhi(c,d)=integral da db I_a I_b[w1(b,c,d)w0(a,b,c)Phi(a,b)].

When interpreting this as a kernel with output(c,d) before input(a,b), ordinary exterior reordering signs MUST be included, as the candidate states. This is not a factorization of averaged weights.

The original exponent is nilpotent in a finite exterior space; all its coefficient functions are polynomials in finitely many compact coordinates. Consequently the two-step kernel expands into finitely many products of an output-only polynomial and an input-only polynomial, tensored with finite exterior matrix entries. These are bounded rank-one integral kernels. K is therefore finite rank and trace class WITHOUT any degree cutoff or physical projection. T_t itself can retain an identity-like shared-coordinate dependence and need not have finite rank. C² sources have common finite polynomial/exterior support and bounded derivatives on compact source neighborhoods, so the same assertions hold for the required derivative products in a common finite-rank coefficient space.

## Independent trace and orientation derivation

With N=128 and k=sum k_(I,L)(u,v) xi_I eta_L, acting on the input monomial eta_J requires L=Jc. The input top coefficient is epsilon(Jc,J), so the coefficient-space operator matrix is exactly K_(I,J)=k_(I,Jc)epsilon(Jc,J), with no additional conjugation. Complex conjugation enters the auxiliary Hilbert adjoint/Riesz representation, not the kernel's linear action or this trace formula.

For |I|=r, exchanging the complementary input/output monomials costs(-1)^(r(N-r)). Since N is even, this equals(-1)^r. Hence epsilon(Ic,I)=(-1)^r epsilon(I,Ic). The supertrace sums(-1)^r times the matrix diagonal and becomes integral I_xi[k(xi,xi;u,u)]. Replacing input eta by -xi supplies(-1)^|Ic|=(-1)^r; its diagonal top integral is the ordinary trace. Polynomial finite-rank kernels justify integrating these diagonal matrix entries.

I manually checked the two-generator identity kernel. Integrating y1y2-x1y2+x2y1+x1x2 against1,y1,y2,y1y2 gives respectively1,x1,x2,x1x2. On y=x its top coefficient is0; on y=-x it is4. This verifies the distinction between supertrace and ordinary trace without any evaluation script.

Applying the periodic diagonal to the actual K kernel gives original w1(b,a,b)w0(a,b,a) with Theta_aTheta_b. Relabeling to time0/time1 has positive block sign. The Haar diagonal identifies coefficients at the same physical anchor variables and then integrates the original64-link product, not128 physical links. Thus Z(J,j)=Str(T1T0)=Tr(Gamma T1T0), with Gamma fixed by exterior parity, is exact.

For ordinary trace, input fields are the negatives of output fields while LINK coefficients are identified without a sign. Setting a=-c,d=-b for fermions yields w1(b,c,-b)w0(-c,b,c). These are exactly the fermionic antiperiodic conditions across Nt=2, with both periodic link-anchor families independent. The sign from flipping all64 fields of one layer is positive on its top, and exchanging the top blocks is positive. No alternative orientation/overall trace phase is being selected. This is a comparison of closures, not adoption of antiperiodic boundaries or identification of exterior parity with a physical number operator.

## Actual source/operator dictionary

At j=0 a spatial Q_f based in physical time0 depends only on the shared b layer. Its wedge multiplier M_f^(2) on input(a,b) is bounded, even and nilpotent with power17 zero. Since Q_f(b) commutes with the even weight and the a extractor,

T0(t)=T0 exp(tM_f^(2)), and T0 M_f^(2)=M_f^(1) T0.

The first-member multiplier refers to output(b,c), so the factor really acts on the same shared physical layer. Consequently the original literal source gives Z_f(t)=Str[K exp(tM_f^(2))] and all its derivatives Str[K(M_f^(2))^n]. This is derived from the original insertion; it is not an assumed self-adjoint metric operator or a fitted product dictionary.

Under the auxiliary orthonormal exterior norm, a generator's wedge adjoint is contraction. Thus the auxiliary adjoint is specified but not automatically the physical adjoint, and a nonzero bounded nilpotent multiplier cannot be self-adjoint. This describes the remaining physical correspondence rather than disproving all physical metric maps.

Crossing Q00/Q0i cannot be factored as one-half multiplication; inserting them within the original three-layer weight correctly defines transfer source vertices. For commuting ordinary source coordinates, s and its derivatives are Grassmann even, so w_,a=w s_,a and w_,ab=w(s_,a s_,b+s_,ab). Differentiating both T factors yields exactly the four second-order terms, including both layer orderings and all action/transported-Q contacts. The C² source assumptions suffice here; no higher j jets are inferred. Compact coefficient domination and common finite-rank support justify differentiation, integration and trace exchanges. The normalized logarithmic response remains conditional on fullZ!=0 and is Z_,ab/Z-Z_,a Z_,b/Z².

## Constructive result and physical limits

D_raw=Gamma K is an actual finite-rank trace object with trace equal to the original partition. If fullZ!=0, D_alg=D_raw/Z has trace1 and reproduces the spatial insertion moments Tr[D_alg M_f^n]. Neither Hermiticity nor PSD is supplied. Trace1 alone is not a positive density operator. Taking absolute weights, a positive part or a favorable projection would change this construction and is not authorized by it.

This is a new exact original-source auxiliary representation, reusing the accepted action, temporal source and contact conventions. It does not inherit Vergeles' distinct Minkowski/ONB/spectral hypotheses, supply a physical transfer Hamiltonian/temperature, import the control-mode CAR prescription or choose gauge/constraint quotient or state. The accepted entire-symbol reflection obstruction remains in force; this trace formula does not make its full pairing positive. Conversely auxiliary non-self-adjoint multipliers or Gamma do not alone establish original physical impossibility.

Physical boundary space/constraints, operator products/adjoint, positive state and source/matter/regulator correspondence remain substantive W1 obligations. FullZ/c0, normalized-point existence, N4 full tensor, B3 range/normalization, tensor/matter/light and causal transport remain OPEN. Manual construction acceptance is separate from evaluation/native/Lean/full-wave, canonical integration, publication and human acceptance.

## Actual commands and fresh continuity

FIRST action was python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-original-transfer-math-review-r1.json from /Users/johnroehm/.codex/worktrees/l1-coupled-fixed-controls/.publication-l1-checkpoint-20261103. It returned fresh:true, changed:[]. Repeated the SAME check immediately before writing this report, again fresh:true, changed:[].

Read full frozen candidate/packet, newest primary notebook, roadmap/authority context and original coframe/closed-action and temporal-source/orientation excerpts. Commands were read-only cat/sed/tail plus a stdlib pathlib/hashlib candidate digest. An initial relative notebook read found no worktree copy; the designated primary absolute notebook was then read. All mathematical contraction, sign and boundedness checks were MANUAL. No scientific evaluator/CAS/matrix/Haar/exterior script, scientific import/evaluation/contraction/job, builds/tests/Lean/LSP/slots/controller/Git/process/harness/configuration action or source/candidate/notebook/repository edit occurred. Only this report was written.
