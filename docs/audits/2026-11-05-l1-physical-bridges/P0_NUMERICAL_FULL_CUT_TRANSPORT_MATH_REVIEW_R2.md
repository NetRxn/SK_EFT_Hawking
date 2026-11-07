# Independent ACTUAL mathematical review: P0 to N0/C3 full pair-cut r2

Verdict: **REVISE for one remaining displayed coefficient.** The new complete noncommuting-link gauge-image proof is sound. R1's commuting-control overclaim is corrected, the real inherited domain and complex extension are stated, and the original/reflected P/N formulas have the required conjugation. However equation18's reflected C display still reads `+2i g2_C`, contradicting its complex-input extension immediately below. Put `+2i conjugate(g2_C)` in that display (or explicitly restrict the display to real couplings). No further proof repair was found.

Reviewer `/root/lorentz_cycle_prospective_math`, task `l1-p0-n0-full-cut-actual-math-r2`. Sole output this report. I consulted no other R2 actual verdict. The lead was notified of the remaining literal-display issue while R2 stayed frozen; no candidate was edited during this review. No repository/notebook/other-agent changes, scientific program, Lean/build/controller/slot/GPU/resource action occurred.

## Candidate, full read, diff and freshness

Full-read ALL sections of `/private/tmp/l1-p0-n0-full-cut-transport-result-r2.md`, SHA256 `efce52888beca0f68a2701117f0d3d878aa1c26c8fecec9c3f35245f6e0114a3`, 28,331bytes. Complete ordinary R1/R2 diff shows title/custody changes, Section8's domain/source-pointer repair, the NEW Section8a gauge-image proof, and Section9's complex-input explanatory prose. Generic Sections2–7 are unchanged. R1 and its two independent reports remain preserved; prospective approval was not treated as actual acceptance.

NEW SAME packet `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-p0-n0-full-cut-actual-math-r2.json`: FIRST explicit check returned exit0, `fresh=true`, `changed=[]`. FINAL check below. Accepted original/N16/metric/EHC/nonzero/crosswalk inputs, notebook/roadmap and BUILD boundary remain unchanged. Packet matching grants no runtime or scientific acceptance.

## 1. Sole remaining necessary correction

R2 equation18 still displays

`[b1b2uv]thetaC(g2_C S2_C at combinedimage)=+2i g2_C`.

For complex g2_C this must be

**`[b1b2uv]thetaC(g2_C S2_C at combinedimage)=+2i conjugate(g2_C)`**.

Equivalently, put an explicit REAL-coupling restriction directly on equation18. The result permits general complex coupling inputs, and the immediately following sentence correctly gives the complex reflected coefficient as `−2i conjugate(g2_P)` at `g2_C=−g2_P`. These are equal to the corrected C expression, not to the current unqualified display. A complex example such as g2_C=i distinguishes them. The real inherited controls remain unchanged.

The unreflected C expression `−2i g2_C` is correct. Equations14 and15 now correctly conjugate their reflected P/N coupling and explicitly state the inherited real-domain scope. The accepted EHC source pointer now correctly identifies section5. No change to field maps, couplings, original certificate coefficients or the new gauge-image calculation is needed for this repair.

## 2. NEW Section8a: full local-gauge proof independently checked

This is an actual construction, not a promised noncommuting test. It specifies `G_b=K=diag(I,i tau1)` at the single time1-origin vertex and identity at every other vertex, then transforms EVERY original anchored link and odd field by the full local gauge formula. All old nonzero test spinors are at time0, so their same ordered b1,b2,u,v test-algebra values are unchanged; zero time1 fields remain zero. Every other incident anchor is determined, even when it is not one of the two displayed distinguished links.

For the closed action, forward/backward coframe brackets transform as internal vectors at their base, a proper SO4 rotation because all G_x are Spin4. Scalar world frames commute with this internal action. The determinant epsilon and metric contractions are invariant. The CLOSED based holonomy transforms by the base G_x conjugation; the two vector/coframe factors cancel its gamma-pair rotation, and gamma5 commutes with Spin4. This proves complete local S4/S2 gauge invariance without dropping a world/internal term. The proof appropriately does not claim the printed word is locally gauge invariant.

I checked the anti-linear gauge covariance rather than assuming thetaS=S. With `Ghat_x=R G_(rho x) R`, Ghat is again compact Spin4 because R normalizes that group, and the hat operation is an involution. The psi identity uses

`conjugate(G_x) R^T = R^T (Ghat_rho^-1)^T`.

Substituting `Ghat_rho=R G_x R`, unitarity of G and R^2=I gives precisely that equality. It does not require R to be real or symmetric. The barred component identity similarly reduces to the unitary inverse relation. Spatial sigma/gauge endpoint matrices match; the temporal link inverse reverses them, with rho(x+0)=rho(x)−0 giving the correct endpoints. Thus sigma(G·U)=Ghat·sigma(U), and the full conjugate pullback/odd anti-involution yields `theta G^*=Ghat^* theta`. Since Ghat spans the same site gauge group, gauge invariance of S then gives gauge invariance of thetaS, independently of action reflection invariance. This is valid with the full actual anchor roster.

The distinguished plaquette calculation is correct. At the time0-origin plane(0,1), the original factors `(A,B,C,D)=(I,H,I,I)` become `(K,H K^-1,I,I)`. Pauli multiplication gives `H K^-1=diag(I,i tau2)`, and

`[K,H K^-1]=diag(0,−2i tau3)`,

which is nonzero. The CLOSED product remains `(H K^-1)K=H`; the opposite order is K H K^-1 and differs. The gauge transformation changes other incident links as required; their complete action/reflected contribution is preserved by the proved invariances, not ignored. Therefore the inherited original/reflected unsquared coefficients hold on this truly noncommuting-link pattern in the SAME test generators.

Subsequent constant B similarity keeps the commutator nonzero and transports both complete coefficient functions. The N-to-C relabeling preserves this nonzero commutator and word order, with its already proved coupling signs. No new coefficient evaluation, selected partial action or printed/closed equivalence is smuggled in. This satisfies the substantive noncommuting-control repair from R1.

## 3. Whole result rechecked

The unchanged B/Pauli/gamma/h calculation remains correct. Both SU2 B blocks have determinant1, B preserves gamma5, the explicit gamma lists give h=(+,+,+,−), and the four original quarter-coframe blocks carry that h with their noncommuting order intact. The complete unsquared action identities S4_N=−S4_P and S2_N=S2_P give the whole-family target g1_N=−g1_P,g2_N=g2_P. The fixed-word map neither changes word order nor identifies printed and closed actions.

Unit independent Haar/Berezin Jacobians, number-preserving parity and the real auxiliary sign measure remain sound. The generator-level anti-linear calculation uses conjugate(B), the correct transposes and B†=B^-1. It transports each independent temporal inverse anchor and the world rho0, rather than replacing reflection by translation or physical dagger.

The full defect-inclusive PAIR kernel retains C/B/H, Bs/Bt, both Rminus/Rplus and invariant D with exp(D). The shared middle variables are acted on once. Four typed original/opposite cut maps and the bilinear sewing transpose give both L and Ltheta relations. No unproved full-source reduced one-slice evolution or physical adjoint is claimed. All actual source derivatives, frame acceleration, current/phase contacts, map independence, source-dependent insertions, four mixed product placements, overlaps and denominator terms remain present. Complex coefficients require conjugation under theta, which is precisely the final display issue identified above.

The S4 discriminator remains nonvacuous: accepted c16>0 proves the actual full S4_total polynomial is nonzero, while the explicit epsilon/h calculation determines its minus. The even saturation coefficient is not used to infer the sign itself.

Composition to C3 correctly gives g1_C=−g1_P,g2_C=−g2_P under the combined nontrivial field/site map, distinct from identical-index uncut P=C. Full source/profile and reflected cut maps compose accordingly. F60/G52 nonzero/isotropic-not-radical character and complete pairing identities follow from the actual map, not from a g2^4 match alone. The separate temporal contact maps Q00 to the correct C Q33 with both anchors and no Lorentz i phases. Nonzero denominator neighborhoods and the witness map to N(−2^1717,1) and C(−2^1717,−1), not the same numerical positive pair by renaming.

## 4. Scope and further acceptance

No additional mathematical proof repair was found beyond the equation18 literal coefficient/domain issue. After its correction and new SAME-packet actual review, the proof is sufficient for the stated Task3 COORDINATE/observable-input consumption boundary. ROOT still must verify the actual numerical implementation and any numerical execution. This proves no positive physical domain/product/adjoint/CAR/polarization, Lorentz integral, causal dynamics, B3/N4 or publication closure.

Preserve R1/R2 and all reports; make a new candidate/packet rather than silently editing the frozen R2. A one-line formula repair does not justify skipping the explicit new-source reconciliation. No new scientific computation or infrastructure work is requested by this review.

Verification: FIRST/FINAL SAME checks; complete R2 reading and R1/R2 diff; manual new gauge/anti-linear/commutator proof and whole bounded result review; ordinary report/hash bookkeeping only. No scientific evaluator, theorem implementation, test/build, backend/controller/process or repository mutation occurred.

FINAL SAME packet check returned exit0, `fresh=true`, `changed=[]`, task `l1-p0-n0-full-cut-actual-math-r2`. Frozen candidate/reference state remained unchanged through review.
