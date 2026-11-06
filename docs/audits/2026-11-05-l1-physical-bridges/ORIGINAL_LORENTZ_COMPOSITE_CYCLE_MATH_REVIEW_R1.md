# Independent ACTUAL mathematical review: original composite Lorentz-cycle result r1

Verdict: **REVISE.** The actual local composite/Wick-action calculation and the gauge-reduced residual-loop absolute-integrability argument are mathematically sound at their stated bounded scope. Section8 nevertheless has a definite inherited-reflection sign error and must state the full framed/source reflection profiles explicitly. These are necessary correctness repairs before acceptance. They do not invalidate the bare-cycle divergence argument or the accepted original compact certificates. No physical continuation/positive-domain acceptance is given.

Sole reviewer output: `/private/tmp/l1-lorentz-cycle-actual-math-r1.md`. Task `l1-lorentz-cycle-actual-math-r1`, independent reviewer `/root/lorentz_cycle_prospective_math`. I did not author this actual candidate and consulted no other actual reviewer or verdict. The lead was notified of the two necessary Section8 issues while preserving R1 unchanged; the lead acknowledged preservation pending the completed independent reports. No source/repository/notebook/other-agent edits or scientific programs, Lean, build, controller, GPU or resource actions occurred.

## 1. Candidate and continuity

Read the COMPLETE actual candidate `/private/tmp/l1-lorentz-composite-cycle-result-r1.md`, SHA256 `434c82fe2a3fa6cd196f40847ad18a2e1ef4a5626ee8d6237460117cbbc40aac`, and independently checked its load-bearing arguments. The prior prospective approval is scope evidence only and certifies none of these results. Accepted baseline definitions and coefficients were read during the preceding assignment; they remain inputs, not new independent reproofs in this review. I directly rechecked the controlling reflection signs against `N16_TEMPORAL_BOUNDARY_IDENTITY.md` section6 and `ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT.md` section1.

SAME packet `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-lorentz-cycle-actual-math-r1.json`: FIRST explicit check returned exit0, `fresh=true`, `changed=[]`; selected source HEAD `6a62061319737190f0f9889d187e1326486c1972`. Packet/reference authorities, notebook/roadmap and the accepted research objective remain the assignment boundary. FINAL explicit check is recorded below. A snapshot match is not theorem, runtime or publication acceptance.

## 2. Necessary correction R1: inherited internal r signs and equation8

Accepted N16 section6, and the accepted EHC result section1, fix

`R gamma_A R = s_A gamma_A`, `s_0=+1`, `s_i=−1`, and **`r_A=−s_A`**,

with `theta_E T_mu^A(x)=epsilon_mu r_A T_mu^A(rho x)`.

After the candidate's proper signed internal permutation `(1,2,−3,0)`, these become

**`r_4=−1`, `r_alpha=+1`**.

The real signed minus on component3 does not change its reflection eigenvalue. R1 section8 instead states `r4=+1,rAlpha=−1`, exactly the opposite values. Its displayed transport formula using `d4=−i,dAlpha=1` is otherwise correct:

`theta_M E_mu^a = epsilon_mu r_C (d_C / conjugate(d_C)) E_(rho x),mu^a`.

Consequently the corrected actual coframe law is

**`theta_M E_mu^a(x)=+epsilon_mu E_mu^a(rho x)`**, for all four a,

because `d4/conjugate(d4)=−1` and the spatial ratios are+1. The claimed `−epsilon_mu` law in equation8 is wrong. Fix both the inherited r statement and the conclusion, and inspect any repeated/coframe-level interpretations. Do not change the original theta, the internal basis, the E definition, or the source's local formal dagger to manufacture the old sign.

The bare metric law has two coframe factors and is unchanged by this correction. The determinant changes sign under the transported theta (world reflection has determinant−1), consistently with conjugation of the Wick factor i. The EHC mismatch survives the injective map as stated. No need to recompute the original compact metric witness or source contacts follows from this repair.

## 3. Necessary correction R2: framed G and literal-K reflection profiles

Section3 defines **framed** `G_mu,nu(A)` using `Ebar_mu=sum_nu A_mu,nu E_nu`. Accordingly section8's displayed `theta_M G_mu,nu=epsilon_mu epsilon_nu G_(rho x),mu,nu` must be explicitly limited to the bare frame A=I or, for the actual full contract, written with the transformed profile.

Let `Ew=diag(−1,1,1,1)` act on WORLD indices, and use exactly the accepted signed-site conjugation convention:

`A_circ,y = Ew conjugate(A_(rho y)) Ew`.

The corrected complete law is

**`theta_M G_x,mu,nu(A)=epsilon_mu epsilon_nu G_(rho x),mu,nu(A_circ)`**.

The analogous framed coframe law is `theta_M Ebar_x,mu^a(A)=epsilon_mu Ebar_(rho x),mu^a(A_circ)`. Same-profile equality requires the actual family to satisfy its closure condition; it cannot be assumed for an arbitrary prescribed C2 A(j). Retain the accepted first/mixed jet rules `A_circ,alpha=Ew conjugate(A_alpha∘rho) Ew`, `A_circ,alphabeta=Ew conjugate(A_alphabeta∘rho) Ew`, and the actual chain-rule/acceleration conditions if a parameter reparametrization is claimed. This is a profile identity, not a request to add a holomorphic j extension.

For literal sources use the once-counted symmetric coefficient matrices: diagonal entry J_mu,mu and off-diagonal J_mu,nu/2, and likewise for K. With `J_E=−i K`, inherited

`J_E,circ,y = Ew conjugate(J_E,(rho y)) Ew`

corresponds to

**`K_circ,y = −Ew conjugate(K_(rho y)) Ew`**,

because conjugation reverses the Wick i. State this minus explicitly rather than silently treating K's reflected coefficient profile as the Euclidean J profile. At the level of the full continued action, `theta_M(i A_M(K,A))=i Ahat_M(K_circ,A_circ)`, equivalently `theta_M A_M(K,A)=−Ahat_M(K_circ,A_circ)`, where Ahat carries the already accepted reflected curvature placement. These are algebraic transport identities; no physical adjoint or Lorentz integral follows.

The existing literal derivative factors `partial_K=−i partial_J`, two-K factor−1, and K/frame factor−i are correct and should remain. The normalized quotient formula is also correct. The defect-inclusive seam, both temporal anchors, all four pair-kernel derivative placements, overlap terms and denominator jets must stay as inherited. Repairing the framed/source statement is needed because the result claims the full C2 contract, not merely A=I.

## 4. Checked local algebra and formal reality (sections2–4)

I independently checked the gamma/chirality calculation. With q=(-i tau1,−i tau2,−i tau3,I), the original ordered product is diag(I,−I). `S=diag(q0†,I)` has determinant1, commutes with gamma5 and sends originalgamma0 to offdiagonal I. The signed permutation has determinant+1 and preserves chirality. `Gamma0=gamma'_4`, `GammaAlpha=−i gamma'_alpha` gives the stated Lorentz Clifford signs and `i Gamma0 Gamma1 Gamma2 Gamma3=gamma5`.

The forward/backward source-transport dictionary is consistent: source Omega_xy=U'_xy inverse, and the actual backward bracket uses its independent backward anchor. The quarter versus i/2 relation gives equation1 with its 1/(2i). Equations2 and3 then follow, including `T4=−i E0`, `TAlpha=EAlpha` and `Q_E=−G_M`. Applying a world-frame matrix commutes with this constant internal map. The determinant phase is+i: moving E0 from the last column to the first gives a minus, multiplying the explicit−i gives+i. The original epsilon normalization is preserved.

The contracted coframe is `−i Gamma_a Ebar^a`, so the two-coframe EHC term indeed acquires the explicit minus in equation4. For the internally antisymmetrized Clifford factor `B_ab=Gamma_[a Gamma_b] Gamma5`, formal dagger gives `B_ab†=Gamma0 B_ab Gamma0`. Lorentz pseudo-unitarity gives `H†=Gamma0 H^−1 Gamma0`. Thus the conjugated trace is `Tr(H^−1 B_ab)`; tracelessness of each chiral B block and determinant-one Cayley–Hamilton yield its negative. The contracted curvature is purely imaginary. This reasoning requires the antisymmetric contraction, as the text correctly states; it does not assert the raw diagonal trace is imaginary.

Consequently the displayed `A_M=g1 detE+i(g2/4)FEE+K G` is formally real at real coefficients, and `S_E(−iK,A)=i A_M(K,A)` has the right sign. Complex frames/couplings are appropriately excluded from that reality assertion. Finite odd changes have determinant1 and transport the original top without a hidden reordering. These are independent-generator algebra changes, not Majorana reduction or a physical CAR identification.

The real-cycle identification is correct: in the chosen Weyl basis, pseudo-unitarity is exactly the subgroup `diag(g,(g†)^−1)`, g in SL2C. It is a connected noncompact unimodular real form of complex SL2C×SL2C, with real dimension equal to that group's complex dimension. Finite Grassmann top extraction leaves a regular matrix-entry function; inverse entries are polynomial adjugates. No scalar damping arises by putting i in coefficients of a terminating Grassmann exponential. These assertions do not make the two cycle integrals equal, and the candidate correctly avoids that inference.

## 5. Checked finite-translation-span obstruction (section5)

The proof is complete at its stated continuous-function scope. Continuous functions inject into Haar almost-everywhere classes; finite translate span therefore inherits a true L1 norm under the contradiction assumption. Left translations are invertible isometries. Their finite-dimensional isometry group is compact, and averaging over its compact closure supplies the invariant auxiliary Hermitian form. This mathematical form is not a chosen physical scalar product.

Point evaluation is bounded in finite dimension and gives uniform boundedness of every span member. Bounded L1 functions have square modulus in L1. The sum of squared moduli of an orthonormal basis is left-invariant, hence a positive constant, contradicting infinite Haar volume. The latter standard fact can be proved by greedy disjoint translates of a relatively compact identity neighborhood, choosing the next element outside finitely many translates of its difference set. No unimodularity assumption is needed for the lemma itself.

For the actual application, fixed finite polynomial degree in each chiral matrix representation supplies a finite-dimensional invariant span under spectator left translation. Restricting to the Lorentz form introduces conjugate entries but does not destroy the finite degree bound or invariance. The argument applies only to nonzero sections; the candidate excludes zero jets as required.

## 6. Checked complete gauge reduction and density (section6)

The actual directed-anchor graph has64 independent edges and16 vertices; maximal-tree removal of15 edges leaves49 loop variables, including the independent periodic parallel anchors. The recursive gauge/tree coordinate change is triangular and uses left/right Haar invariance. The remaining root conjugation is explicitly removed rather than mistaken for physical integration.

I checked the differential of the two-loop normal form. For distinct eigenvalues of D(lambda), zero variation of `k D k^−1` forces deltaLambda=0 and X diagonal. Writing X=t diag(1,−1), zero variation of the second normal-form matrix then forces t=0 from its upper-right entry and deltaA=deltaD=0 from its diagonal entries; the determinant condition supplies the remaining tangent entry. Source and target real dimensions agree. This proves the local diffeomorphism.

Diagonalizing the first regular semisimple matrix, requiring both offdiagonal entries of the second nonzero, and using the diagonal centralizer to normalize the upper-right entry gives the displayed M(a,d). The generic irreducible-pair condition is open dense, and the remaining center/eigenvalue-order ambiguities are finite. The slice removes all continuous conjugation directions even after the spectators are included, since the pair already has only central stabilizer.

The density derivation is valid. Positive smooth Haar densities pull back to `r(k,s) dmu(k) ds`; simultaneous conjugation acts as left multiplication on k. Unimodularity of SL2C preserves the pair measure, and local invariance forces r independent of k on a connected chart. Hence rho(s)>0 is genuinely derived. Including spectators `h_j=k z_j k^−1` gives a block-triangular coordinate change; at fixed k each spectator conjugation preserves Haar, so no spectator Jacobian remains. Equation7 therefore establishes precisely a local bare quotient density times47 unrestricted spectator Haar factors. It is not a global quantum gauge measure, and the candidate appropriately says so. Locality in the pair chart does not restrict the spectator integration used later.

This is enough for the claimed local gauge-slice absolute-divergence certificate. It does not divide an infinite orbit integral by an infinity, assume a global gauge section, or leave a hidden continuous root gauge volume in the spectator argument.

## 7. Checked nonzero scope and Tonelli step (section7)

Gauge invariance and invertible maximal-tree fixing preserve nonzeroness of the complete Berezin-integrated polynomial. The real-form uniqueness argument is correct: local holomorphic exponential coordinates take a real Lie-algebra form to a maximal totally real uniqueness set, and successive one-variable identity extends zero to a complex neighborhood, then to the connected complex group. Thus a nonzero holomorphic tree-fixed polynomial is nonzero somewhere on the Lorentz real form.

The generic pair set is open dense, so the continuous nonzero locus meets it. Gauge invariance puts such a point in a local slice. Holding one spectator at its nonzero value and varying all remaining arguments in a sufficiently small relatively compact product neighborhood gives a positive-measure set of nonzero entire spectator sections. The pair density is bounded below there. Applying section5 to each section gives infinite absolute spectator integral; Tonelli for the nonnegative absolute value gives infinite gauge-reduced integral. All measures here are smooth sigma-finite Lie-group/coordinate measures, so the use of Tonelli is legitimate. An isolated nonzero point is not being substituted for the neighborhood argument.

The accepted compact Z>1 at `(g1,g2,J,A)=(2^1717,1,0,I)` makes its FULL compact link polynomial nonzero. The displayed constant basis/odd transformations are invertible determinant-one changes; the local continuation rewrites that same holomorphic polynomial with unchanged numerical g1,g2 at zero source. Hence this same real numerical pair supplies a nonempty continued nonzero scope. No physical point is selected, and the theorem remains explicitly parameterwise rather than claiming every coupling or source jet is nonzero. The accepted large-coupling certificate is an inherited input, not independently recalculated here.

## 8. Scope, re-review and verification record

The result is materially stronger than repeating the source's admitted divergent gauge volume: it derives a residual-loop L1 obstruction after a complete generic continuous-gauge slice. Its claim is limited to the specified bare ordinary positive Haar prescription. It excludes no distributional definition, other complex cycle, boundary-weighted amplitude, controlled Euclidean reconstruction or original physical model. It constructs no positive boundary polarization, represented adjoint, four physical intertwiners, causal/unitary transfer, B3 acceptance or publication gate. Both accepted compact kernels and controls remain binding.

Required R2: correct r signs/coframe equation8; write the framed A_circ and literal K_circ laws with exact once-counted matrices and chain-rule meaning; reconcile any repeated interpretation. Preserve R1 and this REVISE report. A corrected candidate needs a new matching packet and independent actual re-review; do not refresh the old packet to hide the revision. No additional derivation of the core gauge-divergence proof is required by the flaws found here, unless source review or the actual revision exposes a new issue.

Verification performed: FIRST/FINAL SAME packet checks; full candidate reading; manual algebra, differential, invariant-density, uniqueness and Tonelli review; read-only packet/reference/sign searches and ordinary report/hash bookkeeping. No scientific evaluator/CAS, Lean, build/test, controller/slot, process/GPU or repository mutation occurred.

FINAL SAME check returned exit0, `fresh=true`, `changed=[]`, task `l1-lorentz-cycle-actual-math-r1`. Candidate and frozen authorities remained unchanged during this review.
