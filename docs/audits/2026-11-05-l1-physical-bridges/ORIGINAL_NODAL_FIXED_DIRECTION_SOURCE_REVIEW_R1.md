# Independent actual source review: fixed-direction sector r1

Verdict: **ACCEPT the exact bounded original-sector reduction**. No necessary source/normalization correction identified. This accepts a nonnegative pure-direction subtotal, its square factorization and the local Haar/three-pattern identities. It does not evaluate sigma_Q or P0, isolate this sector as a retained-link coefficient, or control cancellation by mixed directions.

Full candidate read: `/private/tmp/l1-nodal-fixed-direction-sector-r1.md`, **8246 bytes**, SHA256 **23ebf969e48909917e546647545d836647c716678be4f58cef24b7ffad280bd4**. I contributed the prior based-anchor source check but did not author this new lead derivation. The full new normalization/moment/saturation argument was independently checked here. No other actual review verdict consulted. Only this report was written for this task.

## Actual source, both world orders and original quarter

The starting P0 is the accepted zero-source/baseframe nodal integral after the exact absent/gauge temporal reduction. It still uses the original closed EHC, all internal/world sums, original coframe quarters and inherited64-odd slice top. A3 is the COMPLETE curvature-{0,3} component of A8, not the full P0 action.

The original closed Ddag Cdag B A definition at a slice1 base with V1=I gives H03=U1,3 dagger U0,3 and H30=U0,3 dagger U1,3. The same independently integrated based anchor occurs in both. Compact internally antisymmetric curvature obeys F(H inverse)=-F(H), while swapping the curvature world order flips epsilon. Swapping the coframe directions flips epsilon and, after the actual C/D relabeling, flips F again. All four ordered placements therefore contribute the same term. Their sum cancels precisely the original EHC1/4. Epsilon0312=+1, yielding the displayed X_x=sum_CD F_CD E1_C E2_D. No extra world factorial, gamma trace factor or raw diagonal-trace-zero assumption is introduced.

No E3 appears. The independent Haar substitution U1,3(x)=U0,3(x)W_x removes U0,3 from BOTH orders, producing W_x dagger and W_x. It affects no direction1/2 coframe. Other retained directions do not occur in this sector. Thus the restricted integral is independent of all retained u0; this is not a claim about direction-mixed terms. All moving anchors remain distinct variables.

## Actual independent-square factorization

After that substitution, each direction1/2 coframe and its odd endpoints stay inside a single fixed-x3 Q2 square. W_x occurs only at its own base and is independently integrated. There is no shared curvature variable coupling the two squares. Each square has32 odd generators, eight original direction1/2 anchors and four independent W variables.

A_L and A_R are even degree4 actions on disjoint variables. Full64-odd saturation of their16th power requires exactly8 copies of each, so the binomial coefficient is binom(16,8). The two square actions are identical by original lattice translation. Moving even eight-generator site blocks to group the two squares changes no top sign. The unnormalized sigma_Q is I32 A_Q^8, not the corresponding exponential coefficient; this convention is correctly retained in equation(3).

Sharp maps each original E_j to -E_j, compact F is real after the legitimate antisymmetric contraction, and the square top/Haar conjugation has positive sign. Thus sigma_Q is real. Equation(3) is consequently binom(16,8) sigma_Q squared, a nonnegative subtotal. No conclusion of strict positivity follows without sigma_Q nonvanishing, and no full-P0 sign follows even if it is nonzero.

## Local Haar normalization and factorial check

The chiral Clifford generators in the antisymmetric two-form contraction have the stated unit-normalized Pauli/t'Hooft identity. Its delta part gives D_x; its chirality-dependent epsilon part vanishes because the even E1 components commute with one another, as do E2. Hence each b_chi has b_chi dot b_chi=D_x. For W_chi=a0 I+i a dot tau, tracing W_chi dagger against i eta dot tau gives2 a dot eta; no factor from the second chirality has already been included in that single-block trace.

Normalized S3 Haar has second coordinate moment1/4 and fourth tensor denominator24. It gives E X_chi^2=D_x and E X_chi^4=2D_x^2. The two chiral groups are independent. The full second moment is therefore2D_x, and the fourth is2D_x^2+2D_x^2+6D_x^2=10D_x^2. Odd moments vanish. These are polynomial identities for commuting even exterior components, not positivity statements for D_x.

Each X_x carries exactly two odd generators at its own base, so X_x^5 vanishes by the eight-generator local capacity. The exponential therefore integrates to1+z^2 D_x+(10/4!)z^4 D_x^2, giving5/12 exactly. The original coframe1/4 remains INSIDE every E and hence D; it must not be inserted or removed again during this Haar step.

## Complete three-pattern coefficient

The endpoint incidence condition on Q2 is2m_x+m_(x+e1)+m_(x+e2)=8. Its integer solutions with0<=m<=4 have checkerboard offset a in{-2,-1,0,1,2}. Curvature Haar eliminates odd m independently at every base, leaving exactly a=-2,0,2. The all-m=2 pattern contributes product D_x. The two complementary m=4/0 patterns each contribute(5/12)^2=25/144 times the appropriate same-color D squares. No other pattern can saturate the square top.

Multiplication by8! correctly changes the z^8 coefficient of the local exponential product into I32 A_Q^8. Thus equation(8), including both25/144 terms and their full internal/endpoint contractions, has the correct normalization. It remains an unevaluated signed Haar/Berezin coefficient; no term is declared a positive operator.

## Restricted significance and verification

The subtotal is exact and useful, but expanding(A1+A2+A3)^16 includes other pure and all mixed sectors. This square has not been isolated by an independent retained-link projection; its retained-link independence particularly cautions against a highest-degree isolation argument. No full P0 value/nonvanishing, one-slice R_b positivity/nonpositivity, physical product/adjoint/CAR/domain, either physical transfer map, source normalization or B3/N4/matter/scale/controlled-limit/publication closure is established. Full J/frame/Bopp/C2 and both defect-inclusive kernel orientations remain owed.

Read the complete candidate, matching packet, current notebook/roadmap context and governing accepted one-slice action/holonomy, nodal reduction, compact antisymmetric EHC and top/source conventions. Earlier primary/source readbacks are reused at unchanged scope. Exploratory discussion is distinguished from the frozen formal result; this review does not claim a new numerical or kernel verification.

FIRST and FINAL SAME command from the managed checkpoint:

```
python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-nodal-fixed-direction-sector-r1.json
```

Both exit0, `fresh:true`, `changed:[]`, task `l1-nodal-fixed-direction-sector-r1`. Final check immediately preceded this report write. Private candidate hash/bytes were separately measured. Static cat/wc/shasum and manual Clifford/Haar/source/saturation reasoning only: no scientific evaluator/import, CAS/matrix/Haar/exterior/Gram program, coefficient evaluation, tests/build/Lean/slot/controller/process/Git action or candidate/repository/notebook/other-agent edit. No other actual review verdict consulted.
