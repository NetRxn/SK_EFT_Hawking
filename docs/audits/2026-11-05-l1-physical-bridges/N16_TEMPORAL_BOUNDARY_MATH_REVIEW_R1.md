# Independent mathematical review: same-source N16 temporal boundary r1

**ACCEPT the actual source-level finite-algebra construction. No necessary algebraic correction found.** The temporal bridge, full signed-source identity and reflected physical-image pairing are derived correctly under the declared original periodic contract. This does not evaluate kernel coefficients/fullZ, prove Hermiticity/positivity, construct a thermal state, or admit an implementation/evaluation.

Exact candidate `/private/tmp/l1-n16-temporal-boundary-identity-r1.md` SHA256 **82197710fb69018810f321dff0ef9f14f9556e47a5b8fab6725b26d1b4c58c49**. Parent/source state942c50adb2fef3633e28fff34e54c0d793854d80 and ROOT source-only adoption are packet/notebook-bound. No candidate/source/notebook/repository edit occurred.

## Actual hopping blocks and orientation

Checked against the original four endpoint coframe terms and accepted full-S4 Hermite matrix construction. At each spatial point the two periodic temporal links V0,V1 remain independent. With D=V0†-V1 and E=V1†-V0, the t0 coframe contributes bar0 gamma D psi1 and bar1 E gamma psi0; the t1 coframe contributes bar1 gamma E psi0 and bar0 D gamma psi1, each with its own h/4. Therefore

`M01=(1/4)sum_A[h0A gamma_A D+h1A D gamma_A]`,
`M10=(1/4)sum_A[h0A E gamma_A+h1A gamma_A E]`.

The noncommuting gamma/link placements are correct. E=-D† and Hermitian Euclidean gamma imply M10=-M01† for real h. Neither independent anchor nor interface is identified with the other. Spatial hoppings produce nonzero M00/M11 in the TIME split; the earlier checkerboard/chirality norm decomposition cannot set these blocks to zero. No diagonal-block inverse is used, so singular blocks cause no gap in this identity.

There are32 barred+32 unbarred generators per slice,64 of each globally,128 total, with the actual64x64 M. Each eight-generator site permutation is even; regrouping four-psi/four-bar blocks costs16 swaps per pair. Consequently xi0=(bar0,psi0),xi1=(bar1,psi1) and Theta0Theta1 preserve the recorded full top orientation. Within a slice, collecting bars first is likewise even. These are global orientation facts, not a reason to discard the local bridge signs below.

## Complete bridge coefficient and finite factorization

For xi0-before-xi1 order, bar1 M10 psi0=-psi0 M10^T bar1. Hence the lower-left block of C is EXACTLY-M10^T, with upper-right M01. Expanding V^k/k!, putting all xi0 entries before all xi1 entries crosses k(k-1)/2 pairs. Antisymmetrizing the sorted A/B lists then gives

`d_AB=(-1)^(k(k-1)/2)det C[A,B]`.

The k! ordering multiplicity cancels its exponential factorial. Degree0 has coefficient1; all k0through64/subsets are retained. No chirality/internal component is selected. E0,E1,V are even, so their exponentials commute, and the even F0/F1 can be put into their half factors without another sign. Thus the bridge gives the full determinant for F=1, without assuming any invertibility. Odd k terms happen to vanish after half top extraction for even F, but the complete bridge identity does not prematurely delete odd intermediate channels.

Reusing accepted Hermite7–10 with source polynomial s_x(Y;J,j) is legitimate because those are identities of commuting formal coframes before Berezin extraction. More than64 fermion bilinears vanish globally, so degree64 truncation at each site is safe. No new Gaussian-only replacement for S4 is made: W_x remains its actual finite signed/complex polynomial, including sources.

Each spatial E_t uses only the slice's spatial h/links and fermions. In contrast W_x temporal-spatial plaquette coefficients can depend on spatial links of BOTH slices and on the temporal links. The candidate correctly retains this dependence in W rather than factorizing W into independent conjugate amplitudes. Integrating all16 temporal Spin(4) links jointly against W*d_AB gives the stated K. Inserting the bridge and oriented half extraction then yields precisely(T), with all remaining48 spatial links and256 Gaussian auxiliary coordinates integrated. Half-local F polynomials in their own spatial links are covered. No individual minor is silently gauge-fixed or separately called a state.

The local compact/Gaussian integrability and finite coefficient operations justify these exchanges: W and minors are finite polynomials with bounded compact-link coefficients, and ordinary polynomial Gaussian moments converge. This is a genuine exact representation of the full sourced action for finite couplings, not a numerical value or tractability assertion.

## Complete source jets and contacts

The chosen representation keeps M, bridge minors and f fixed in REFERENCE coframes and places ALL prescribed A_x(j) dependence in s_x(Y;J,j), hence in W/K. This is consistent; it avoids simultaneously straining M and the action coefficients and double-counting the same variation.

The displayed Hermite derivatives follow directly from differentiating exp(s_x): first derivative exp(s_x)s_x,a, mixed second exp(s_x)(s_x,ab+s_x,a s_x,b), with the same degree truncation. Differentiating product_xW_x includes same-site second derivatives plus every ordered distinct-site first-first term. No division by W at its zeros is needed. In particular s_Jj retains Q_j, and s_jj retains both full action second variation and JQ_jj. With F=1 this produces actual full Z_a/Z_ab and, where Z!=0, Z_ab/Z-Z_aZ_b/Z², the accepted G/A/B/D contacts.

Spatial Qij is half-local at undeformed j0; T0 and Q0i/Q00 cross the cut. World deformations mixing time/spatial directions can change even transported spatial support. The candidate correctly obtains crossed source/action insertions through complete K derivatives rather than pretending they belong to an undeformed half-local F algebra. It explicitly retains the further source-to-physical-operator/matter matching obligation. The construction covers any prescribed C² local source family with bounded jets on a compact neighborhood; it selects none by a favorable sign and changes no regulator/measure.

## Antilinear reflection and its exterior matrix

For rho(t,r)=(1-t,r), the reflected positive temporal edge has anchor rho(x)-e0. At Nt2 this is the SAME temporal anchor t, giving V_t->R V_t†R, not V0/V1 translation exchange. Spatial links use R U_(rho x,i)R. Both periodic interfaces survive. R=gamma0 in the actual basis is Hermitian/unitary, R²=I and detR=1, and normalizes Spin(4); conjugation/inversion preserve normalized Haar. Its component signs are s0=+1,si=-1.

The independent barred variables are mapped with the correct row/column convention. For any bilinear bar_x A(U)psi_y, antiorder gives the reflected matrix R A(sigma U)†R at reflected reversed endpoints. Applying this to all four original terms yields exactly

`theta T_mu^A(x)=epsilon_mu(-s_A)T_mu^A(rho x)`.

Spatial terms exchange their original outgoing/incoming minus patterns with an overall-s_A; reversed temporal orientation supplies the extra epsilon0=-1. Therefore thetaQ has epsilon_mu epsilon_nu, and the determinant action has world determinant-1 times internal determinant-1, so thetaS4=S4 for real g1 at zero source. This calculation does NOT imply thetaS2=S2. The exact reflected closed plaquette/source coefficients are retained; no symmetrized action, antiperiodic seam or assumed reflection-invariant exponent is substituted.

Antilinearity gives theta²=1 using R†R=I, even though this actual gamma0 need not be a real symmetric matrix. The64-generator linear matrix is L=[[0,I8 tensor R],[I8 tensor R^T,0]]. Its exterior antiorder matrix is

`S_AB=(-1)^(k(k-1)/2)det L[A,B]`.

This row/input-index convention matches theta(xi_A)=sum_B S_AB xi_B. Top sign is+1: reversal signs at64/128 degrees, the even bar/psi and time/site block swaps, and detR factors all preserve orientation. Theta conjugates the full Haar/Berezin integral. S is invertible (the antilinear involution supplies the inverse relation with conjugation), not assumed to be an ordinary real identity matrix.

## Reflection-amplitude and RP index check

For physical F in A_+, first pull back half parameters by kappa, then take coefficient conjugation and the exterior reflection. Spatial E0(kappa z) becomes E1(z); its h signs cancel the coframe signs. The even F can cross the reflected xi_A and E1 without a graded sign. With the top sign+1 this gives EXACTLY

`conjugate f0,A(F;kappa z)=sum_B S_AB f1,B(thetaF;z)`.

Changing z1=kappa w in(T) therefore solves

`f1,B(thetaF;kappa w)=sum_C S^-1_BC conjugate f0,C(F;w)`.

The original pairing is(T) with F0=G and F1=thetaF, since both are even. Substitution yields

`B_CA(w,z)=[K(z,kappa w;0)S^-1]_(A,C)/Z`.

The inverse is on the RIGHT of K; the displayed(C,A) kernel indexing correctly transposes the input/output positions. No additional complex conjugation of K is warranted: theta acts on F, while K is the ACTUAL unsymmetrized action weight. A Hermitian kernel would be an additional state property, not part of this identity. This explicitly verifies the potentially delicate transpose/inverse/conjugation convention.

The pairing is required only on the actual image f0(A_+); positivity of a larger ambient coefficient kernel is sufficient but unnecessary. A negative vector outside that image is not a physical counterexample. A proposed negative Gram span must specify actual F, and a positive complete-basis certificate must prove it covers its stated entire image/quotient. Arbitrary favorable projection is excluded. Periodic fermions have not been identified with an ordinary positive Gibbs trace by these algebraic manipulations.

## Safe degrees and completion scope

At a single site the coframe cutoff is64. Each S2 coefficient contributes four link coordinates and costs two coframe degrees; at most32 such factors occur, so W_x link degree<=128. Hermite degree in h is<=64. For16 weights this gives h<=1024 and links<=2048. A k<=64 bridge minor adds at most k h powers and k temporal-link powers, giving the conservative kernel-integrand bounds1088/2112. Constant fixed sigma, derivatives of the prescribed C² sources and temporal Haar integration do not increase these degree bounds. They bound K's integrand, not arbitrary half-local observable polynomials; the candidate expressly does not truncate the latter. These are finiteness/normalization-sizing facts, not row counts or computational admission.

The completion criterion retains all source orders, W/minor incidences and boundary indices, with site/link elimination only after the last incident factor. It is explicit enough to define the remaining exact polynomial moments. No fullZ value, nonzero domain, actual kernel entries, Hermiticity, positivity, transfer/thermal interpretation or real-time reconstruction is established. Good-prime/full-value/remainder certificates and actual physical-image state tests remain distinct later tasks.

Accepted pureg2 finite G/B zero, N4/N16 distinctions, fixed-body versus centered-body matter families, physical normalization/B3 interval, tensor/matter/light cone and transport remain at their prior boundaries. FullN4 tensor ownership remains OPEN; no scope reduction, no new settled no-go, Lean theorem/absence/admission or publication qualification follows.

## Actual actions and continuity

First action and final action immediately before writing this report were `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-n16-temporal-boundary-math-r1.json` from the assigned worktree; both returned fresh:true/changed:[]. Read full candidate/packet, source intake, actual gamma/checkerboard source, original coframe/Hermite7–10, accepted source/matching contract and newest adoption notebook. A stdlib pathlib/hashlib read independently confirmed the exact candidate hash. Mathematical verification was manual algebra only.

No scientific/project import, code/control/test/matrix evaluation, support enumeration, compilation, contraction/job, Git/build/Lean, slot/process/harness/configuration action or candidate/source/notebook/repository edit occurred. Only this report was written. Verdict is actual source-level identity acceptance only, with state/normalization/kernel values and execution uncomputed.
