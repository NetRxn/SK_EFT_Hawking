# Independent mathematical interoperability review: numerical / physical conventions r1

Verdict: **REVISE for one definite matrix-identity error in Section1.** The principal Euclidean coordinate dictionary, UNSQUARED action signs, full source transport and oriented-cut identities are correct at their stated algebraic boundary. The note correctly withholds identification of the accepted P0 cut with the numerical C3/N0 cut. However it incorrectly denies an entrywise gamma-matrix equality that follows from the very S alignment it cites. Repair that sentence while preserving the essential distinction between matrix coincidence and full field/cut/real-structure equivalence.

Task `l1-convention-crosswalk-math-r1`; independent reviewer `/root/lorentz_cycle_prospective_math`. Sole output `/private/tmp/l1-convention-crosswalk-math-review-r1.md`. I authored neither the crosswalk nor the numerical plan. No other review was consulted. The concrete error was reported to the lead, who confirmed R1 preservation pending completed independent reports. No repository/notebook/other-agent edits, scientific evaluator, Lean/build/controller/slot/GPU or numerical execution occurred.

## 1. Exact inputs and freshness

Full-read candidate `/private/tmp/l1-numerical-physical-convention-crosswalk-r1.md`, SHA256 `c0fb8b9bf660dbae6845fffe56f7690ebff090990609823def3a175810b790b7`, 12,970bytes. Read numerical plan `/tmp/publication-original-coefficient-budget-r2.md` Section2 in full, especially its explicit gamma/site/anchor/source dictionary, against accepted actual EHC, N16 reflection, metric and corrected Lorentz inputs. Prior accepted physical coefficients are inputs, not newly rederived numerical data. The note does not certify an implementation and neither does this review.

SAME packet `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-convention-crosswalk-math-r1.json`. FIRST explicit check returned exit0, `fresh=true`, `changed=[]`, source checkpoint `e2e393b126bedd49ca114efc6ca8c8ae005e8876`. Current primary-local notebook entry for that physical checkpoint and referenced roadmap/authorities were consulted. FINAL check is recorded below. Snapshot freshness grants no runtime or scientific acceptance.

## 2. Necessary correction: equality of the selected time matrices

Candidate Section1, line13, says

`Gamma_LP^0=S gammaP0 S^-1. This is not gammaM_N,0=gammaC3.`

That literal matrix nonidentity is false. Accepted physical Lorentz Section2 explicitly computes, with `q0=−i tau1` and `S=diag(q0†,I)`,

**`S gammaP0 S^-1 = [[0,I],[I,0]] = gammaC3 = gammaM_N,0`.**

This can also be checked directly: both offdiagonal blocks after conjugation are `q0† q0=I`. All three displayed time matrices coincide ENTRYWISE in the selected bases.

The intended convention distinction remains essential and correct. The equality of this one matrix does not identify the world-time reflection rho_P0 with rho_C3, transport the old/shared/new boundary coordinates, supply the Lorentz real form, identify the other gamma matrices (Lorentz spatial gammas square to−I, Euclidean ones to+I), or identify the anti-linear field embeddings. Replace the denial with an explicit statement of the numerical coincidence and these remaining nonidentifications. Do not alter S or any accepted gamma/action/coupling/source convention to make the denial true. This is the sole definite algebraic correction found here.

## 3. Unreflected P=C and the genuinely different cuts

The note correctly reads the accepted physical P gammas and canonical numerical C gammas as the SAME four matrices at IDENTICAL numeric labels, with the same gamma5 and ordered product. Thus at identical indexed fields/profiles/couplings and a fixed printed/closed word, their unreflected finite coframe/action polynomial functions are identical. No hidden g2 sign is needed for that identity comparison.

P nevertheless selects world time0 and R_P=gammaC0, while C selects world time3 and R_C=gammaC3. Identical uncut polynomial formulas do not identify the corresponding half-exterior algebras, geometric pullbacks, independently anchored temporal link sets or cut kernels. The note correctly labels this gap rather than converting the numerical plan's declared M convention into the accepted metric certificate by naming alone.

The numerical plan's sentence identifying its M convention directly with the accepted metric certificate is therefore not independently certified by this review. Its M dictionary is a well-defined separate Euclidean convention, called N or M_N in the crosswalk. ROOT must retain that distinction or supply the missing P0-to-C3/N0 transport before using the accepted reflected metric witness as that target's certificate. This is a consumption boundary, not an assertion that the accepted compact scalar coefficients are false.

## 4. Euclidean permutation and UNSQUARED action signs

Let pi=(3,0,1,2), where a label in N maps to a C label, and Ppi_(pi(mu),mu)=1. This is a four-cycle of odd parity. Fixed `gammaN_A=gammaC_pi(A)` and `gamma5N=gamma5C` imply the ordered N product is **−gamma5N**, exactly as declared. That is a legitimate separate gamma5 convention. It is not the ordered-product definition retained in P, and it is not a Lorentz signature.

The displayed site, extent, fermion-boundary and anchor permutation is invertible. Spinor/chiral indices remain fixed. Direct substitution of each of the four original quarter-coframe hopping terms gives equation1, including backward anchors when periodic endpoints coincide. Dagger/matrix order never commutes through a gamma or another link. The SAME ordered plaquette word maps entrywise; the map never turns printed ABC†D† into closed D†C†BA.

I independently checked both unsquared signs:

- Cosmological density: writing the C world rows in N order introduces det(pi)=−1, and the internal epsilon permutation introduces another−1. They cancel, so **S4_C=S4_N**.
- EHC density: its ordered gamma pair and FIXED gamma5 transport entrywise, and it has no extra internal epsilon to cancel the world epsilon sign. Hence **S2_C^w=−S2_N^w** for either fixed word w, before integration, squaring or saturation.

Therefore **g1_C=g1_N and g2_C=−g2_N** produce identical complete exponents. A g2^4 coefficient cannot check that sign; the note correctly requires an unsquared complete-coefficient control. No sign correction to those equations is needed. The numeric implementation remains to be checked independently against the dictionary.

## 5. Full sources, orientations and jets

The matrix form is consistent. With rows world, columns internal, `T_C=Ppi T_N Ppi^T`. Applying `A_C=Ppi A_N Ppi^T` gives the same formula for Y. Consequently `Q_C=Ppi Q_N Ppi^T`, and the once-counted literal metric-source matrix transforms by conjugation with Ppi. Re-sorting unordered offdiagonal pairs introduces no factor2 because the coefficient matrices already carry J/2 off diagonal. Linear coframe sources and auxiliary h transform in both world/internal labels. The latter is an auxiliary variable, not a new physical coframe source.

The map is constant in the source parameters, so each first, repeated and mixed frame derivative, including A_ab, follows the same linear rule. A nonlinear parameter change would still need both derivative levels, which the note correctly retains. Scalar local phase chi pulls back by the site map; current/action/metric contacts then transport by the same finite substitution. This adds no gauge field or physical normalization.

Berezin orientation is preserved: exchanging site blocks of degree8 is even, spinor indices do not move, and the plan's chiral site top equals all-four-bars/all-four-psis by four swaps. The quaternion +/-i parameter change is applied per independent SU2 factor and preserves positive normalized Haar probability; no oriented-sphere sign is inserted. Full unnormalized coefficient and jet identities therefore follow. Normalized identities require the corresponding nonzero Z and the complete quotient derivatives; this note supplies no new Z certificate.

## 6. BOTH oriented Euclidean kernel cut maps

The geometry in equation6 is correct: `rho_C3 Ppi=Ppi rho_N0`, `Ew_C3=Ppi Ew_N0 Ppi^T`, and `R_C=gammaC3=gammaN0`. Thus it transports N0 reflection to C3 reflection, NOT to P0 reflection. The transposed odd-index rule, each separate temporal inverse anchor and r=−s all follow this relabeling.

To make the four actual cut-space roles explicit, write Phi_- and Phi_+ for maps from N original input/output test spaces to C3 original input/output test spaces, and Phi'_- and Phi'_+ for the reflected opposite input/output spaces. Then equation7 is

`L_C3 = Phi_+ L_N0 Phi_-^-1`.

The geometric reflection maps obey

`R_C,- Phi_- = Phi'_+ R_N,-`,
`R_C,+ Phi_+ = Phi'_- R_N,+`.

The Berezin/Haar sewing pairing is preserved, so its transpose is transported contragrediently, giving equation8 in its correct typed form

**`(L_C3)^theta_C3 = Phi'_+ (L_N0)^theta_N0 (Phi'_-)^-1`.**

This verifies the note's qualification that the in/out Phi in equation8 are the ACTUAL reflected opposite cut maps, rather than recycling same-space input/output operators. Both two-time interfaces and all source-derivative placements remain. The full profile maps A_circ and J_circ commute with the site/world permutation and their C2 jets, as equation9 states.

These are Euclidean coordinate identities on ACTUALLY DEFINED kernel domains. They are not physical Hilbert intertwiners, positive similarities, or equality to a spectral exponential. For clarity in downstream use, the phrase “whichever one-slice or pair-step interface” should be read with the accepted domain restriction: the full unrestricted source family uses the defect-inclusive pair kernel; a genuinely reduced one-slice kernel is available only on an actually established defect-free diagnostic or another separately proved reduction. Equation7 cannot be cited as constructing an unrestricted full-source one-slice evolution. Adding that explicit parenthetical would improve the note during its necessary revision without changing the coordinate mathematics.

No additional P0-to-C3/N0 map is supplied by these identities. The note expressly withholds it, which is necessary. A four-torus symmetry or an internal/Pin rotation would need its OWN complete action/coupling/chirality/source/cut derivation; an even-g2 metric coefficient or one coincident gamma matrix does not provide that derivation.

## 7. Separate physical continuation and consumption boundary

The P-to-L_P internal signed permutation is proper and preserves gamma5. It acts with S on spinors/links and retains all WORLD P labels, unlike the odd Euclidean pi map. Its composite phases are correctly retained: Q_P maps to−G_LP, S4_P to+i detE, and S2_P to the displayed negative quadratic trace expression. Coupling numbers in that rewriting are unchanged; the numerical C/N g2 sign is not applied a second time because both targets happened to be named M.

The corrected physical transported reflection is `theta_LP E=+epsilon^(0) E∘rho0`, with the P0 A_circ profile and extra minus in K_circ from `J_P=−iK`. Literal derivative phases−i/−1 are correctly separated from the purely real Euclidean index permutation. Evaluating the same compact P polynomial at complex literal sources may use the C/N dictionary first, then this complex-source substitution. It creates no Lorentz Haar integral, physical boundary domain, positive CAR or physical transfer intertwiner.

After repairing the false matrix-nonidentity sentence, the note gives a sound convention/consumption boundary. It does not resolve the printed/closed source discrepancy or identify P0 and N0/C3 cuts. Those limitations must remain explicit in any ROOT adoption. No previously accepted physical certificate should be silently relabeled by this interoperability note.

## Verification record

Commands: FIRST/FINAL SAME packet checks; complete candidate and numerical Section2 reads; read-only accepted-reference/notebook/sign reads; manual index/epsilon/Clifford/source/cut analysis; ordinary report/hash bookkeeping. No scientific computation, code implementation or new theorem construction ran. Separate independent source review and lead full-read/fresh reconciliation remain required before this note becomes shared convention authority.

FINAL SAME packet check returned exit0, `fresh=true`, `changed=[]`, task `l1-convention-crosswalk-math-r1`. Frozen candidate/reference state remained unchanged through this review.
