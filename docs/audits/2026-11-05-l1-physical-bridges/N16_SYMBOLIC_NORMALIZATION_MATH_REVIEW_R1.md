# Independent mathematical review: N16 symbolic normalization r1

**ACCEPT the manual denominator, height and conditional nonzero-neighborhood results and the scoped source-convention readback. No necessary mathematical correction found.** No coefficient, residue, partition value, matrix, positive state or computational feasibility is established. This review admits no evaluation or source implementation.

Frozen candidate `/private/tmp/l1-n16-symbolic-normalization-r1.md` SHA256 **8544ece0ae2dfce3b3e054cd81c17153467e9b9afb9959be0372ab406e046487**, independently confirmed using stdlib pathlib/hashlib. Parent checkpoint8440c44fe9263d0070002895b5186bca32f4f1a9 and accepted physical-image source78861d229e02055c5274a1d3e16fab933d2cac961441816a47a4b739db6e9d26 are retained. Only this report is written.

## Full partition and common denominator

With128 Grassmann generators, degree8 S4 and degree4 S2, saturation gives8m+4n=128, hence2m+n=32. Expansion of the same exponential gives exactly c_m=I[S4^m S2^n]/(m!n!), with m=0..16. The previously accepted INTERNAL Pin transformation sends both action pieces to their negatives and preserves the integration measure. Since n is even here, its sign is(-1)^m; thus odd-m coefficients vanish. This reuses that accepted parity argument, and does not assume invariance under the temporal theta of the boundary construction. It transfers no four-site cancellation to sixteen sites; c16 remains unknown at g2=0.

The actual canonical quaternion matrices and Euclidean gamma convention have coefficients in Z[i]; inverses are quaternion conjugations. The coframe's four original endpoint blocks each have quarter normalization. Four frames in S4 give4^4, and two frames plus the explicit action quarter in S2 give4^3. Thus4^(4m+3n)=4^(96-2m) divides4^96. The cosmological term uses the already accepted determinant after ordered-world normalization, with no extra factorial silently discarded. Because m+n<=32, m!n! divides32!: the quotient is a binomial coefficient times32!/(m+n)!.

Normalized S3 moments are product(2r_j-1)!!/[2^k(k+1)!] for even coordinate multiplicities and zero for any odd multiplicity. This follows from rotationally invariant sphere moments (or normalized Gaussian radial separation); k=0 gives1. Every denominator at k<=96 divides2^96*97!. The full action has link-coordinate degree at most4m+6n=192-8m<=192. There are64 independent Spin(4) links, each with two SU(2) factors. Allocating the worst permitted moment denominator to EACH of128 factors is conservative but valid, including mixed chiral terms. Therefore

D_Z=32!*4^96*(2^96*97!)^128, with D_Z*c_m in Z[i].

Every denominator prime is<=97. For p>97, a complete nonzero reduction in a specified embedding of i or its quadratic extension proves nonvanishing over Q(i). A zero residue is inconclusive, and denominator-goodness alone supplies no nonzero coefficient. The proposed rational-coupling denominator D_Z*v1^16*v2^32 is also safe, because the maximum exponents are16 and32 respectively; coupling denominator primes must additionally be excluded. No such reduction/value was evaluated.

## Actual full physical-image observables and denominators

The parent list is exactly Fi=Reynolds[xi_D*u^alpha], with d=|D|<=64 and a=|alpha|<=160. It spans the WHOLE adopted physical pairing image by the accepted projection argument. There is no replacement by a favorable set of fitted observables.

Each transformed spinor contributes one gauge quaternion coordinate and each transformed spatial link coordinate contributes at most two. Thus total gauge-coordinate degree<=d+2a<=384. Eight spatial sites have16 SU(2) gauge factors; each factor has even-moment half-degree<=192. Its moment denominator divides2^192*193!, so D_G=(2^192*193!)^16 is a safe common coefficient denominator. Gauge averaging leaves physical link degree<=160. Parent theta uses the specified signed-permutation gamma0, link quaternion conjugation and chiral exchange, so introduces no new denominators.

Two Fi factors contribute at most320 physical link powers. Action saturation can only decrease with inserted Grassmann degree; it never exceeds the unsourced degree192, action-frame quarter exponent96 or factorial bound32!. Thus physical link degree<=512, half-degree<=256 for each SU(2) factor. Consequently

D_N=32!*4^96*D_G^2*(2^256*257!)^128

clears EVERY coupling-polynomial coefficient of the original unnormalized N_ij, including all observable directions and both independent chiral factors. Primes>257 avoid these coefficient denominators. Dividing by the still unknown full Z requires a separate nonzero denominator certificate; finite-field arithmetic supplies neither real ordering nor matrix positivity.

## Independent check of the height estimate

Use coefficient l1 norm in the canonical exterior basis. It is submultiplicative under wedge, and coefficient collisions/reordering cannot increase the triangle bound. At unit links every entry of gamma U or U gamma has modulus<=1. Four blocks times16 possible bilinear entries, divided by4, give norm(T_mu^A)<=16. Coincident endpoints on the two-slice geometry cannot invalidate this upper bound.

For S4, the accepted determinant has24 internal epsilon terms, four coframes and16 base sites: norm(S4)<=16*24*16^4=24*16^5<2^25. For S2,24 ordered world terms,16 choices of the two internal indices and two coframes occur at each of16 bases. The CLOSED plaquette is unitary; gamma_A gamma_B gamma5 is unitary, so the four-dimensional trace has modulus<=4. The explicit action quarter cancels this upper-bound factor4. Hence norm(S2)<=16*24*16*16^2=24*16^4<2^25. This uses the full original trace and world sum, not a fixed-chirality or selected-word bound.

Set C=2^25 and B=C^32=2^800. Top extraction has norm<=1; normalized product compact Haar does not increase a uniform absolute bound. Each coefficient has m+n<=32 and division by positive factorials. Thus |c_m|<=B.

For Fi at any fixed physical unit links, a gauge-transformed canonical degree-d Grassmann monomial has exterior coefficient l2 norm1, since the Dirac/dual gauge action and its exterior powers are unitary. The transformed scalar quaternion monomial has modulus<=1. The normalized gauge average has l2 norm<=1 by the triangle inequality. The coefficient dimension is binom(64,d)<=2^64, giving l1 norm<=2^32 by Cauchy-Schwarz. Theta preserves this bound, since its coefficient action is unitary and its link map preserves the compact domain. Therefore the product of the two insertions has l1 norm<=2^64, and every coupling coefficient obeys |n_ij,m,n|<=2^64*C^32=2^864.

After multiplication by D_N the real and imaginary parts are integers individually bounded in absolute value by D_N*2^864. Complete coefficient reconstruction with modulus greater than twice this height is consequently unique. The dual-embedding or quadratic-extension arithmetic must actually recover both Gaussian-integer coordinates and bind the full source; a one-sided complex embedding or partial coefficient calculation would not suffice. This is only a prospective CRT height, not a PSD certificate, evaluated coefficient or practical cost estimate.

## Conditional normalization neighborhood

For real g2!=0, the algebraic chart x=g1/g2^2 gives Z=g2^32*z(x), where z has only the constant and eight possible higher EVEN powers through16. IF a future complete certificate proves c0!=0, then D_Z*c0 is a nonzero Gaussian integer, so |c0|>=1/D_Z. With R=1/(16*B*D_Z)<=1 and |x|<=R,

|z-c0|<=8*B*|x|^2<=8*B*R=1/(2*D_Z).

The middle inequality is deliberately loose but valid because |x|^2<=R for R<=1. Reverse triangle inequality gives |Z|>=|g2|^32/(2*D_Z)>0. No favorable sign, positivity, analytic logarithm or physical phase assumption is needed. The missing antecedent is explicit: no actual full c0 nonvanishing has been established. At g2=0 this chart is unavailable and the unknown raw c16 term must be considered separately. Other zeros outside the conditional domain are not excluded. This finite-regulator enabling domain supplies no B3 physical range, normalized metric body, positive state, matter/thermal/transport or continuum result.

## Conventions, reuse and acceptance boundary

The newest sole-writer notebook records symbolic normalization alongside convention diligence, and preserves all original physical requirements. The current roadmap keeps B3 normalization/range, stable domain, physical metric/source/mode/matter and transport construction OPEN. The actual chi_RPA definition and sign theorem in VestigialSusceptibility.lean require chi0>0 and gamma_star*chi0<1; there is no added gamma_star>=0 premise or supplied identification with bare g1,g2. The inspected publication snapshot treats susceptibility and speed-law inputs conditionally rather than furnishing a microscopic state map.

The held CGL source sectionI.F,(1.60) explicitly specializes to exp[-beta0(H-mu0Q)]/Z0 before the thermal KMS condition. The held Volovik source explicitly identifies T=H/pi with the de Sitter heat bath and H with its Hubble parameter. Neither readback identifies beta0 with a two-slice lattice extent or that H with a microscopic Hamiltonian. The candidate retains the original signed Diakonov finite Haar/Berezin functional and the parent's qualified Vergeles composite-extension distinction. These are bounded source-specific correspondences still to derive; they are not a claim of literature-wide absence or an operator choice. None is needed for the algebraic results proved here.

Reused accepted results are action normalization/conventions, Pin parity and whole physical-image spanning. Newly checked here are their composition into explicit D_Z,D_G,D_N, compact height bounds and the conditional normalization radius. Manual acceptance is not native Lean, positive-state, physical/L1, main or publication acceptance. Full N4 tensor remains separately OPEN and owned. No evaluated full normalization, Gram coefficient/matrix, positive state, actual negative witness, microscopic phase/domain or computational feasibility follows.

## Actual actions and fresh continuity

FIRST action: python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-n16-symbolic-normalization-math-r1.json, from /Users/johnroehm/.codex/worktrees/l1-coupled-fixed-controls/.publication-l1-checkpoint-20261103. It returned fresh:true, changed:[]. Repeated the SAME check immediately before writing this report; again fresh:true, changed:[].

Read candidate, packet, newest primary notebook, roadmap/authorities, convention intake and pinned body excerpts, actual gamma/frame/closed-action source, accepted parity and physical-image source, and actual RPA declaration. Commands were read-only cat/sed/rg/rg --files and one stdlib pathlib/hashlib candidate digest. One initial read sought the action helper under scripts/ and found no file; rg --files located its actual docs/audits path, which was then read. No scientific import/evaluation/test/control, modular computation, Grassmann/Haar contraction, code job, Git/build/Lean/LSP/slot/harness/process/config action or source/candidate/notebook/repository edit occurred. Only this report was written.
