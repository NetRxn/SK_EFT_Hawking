# Independent mathematical review: finite collective-body parity r1

**ACCEPT the exact finite-regulator parity/body calculation under its stated hypotheses. No necessary mathematical correction found.** Raw one-point vanishing requires no denominator; normalized G/B vanishing remains conditional on the full nonzero partition. This is manual finite-algebra acceptance, not a new universal no-go, settled fork, thermodynamic statement, finite-lambda result or Lean/publication acceptance.

Frozen candidate `/private/tmp/l1-collective-body-parity-20261105-r1/COLLECTIVE_BODY_PARITY.md` SHA256 **f6e624715ddbf95866064f10feb0cacd373530afd1204083808441c71690becb**. Adjacent control SHA256cf691c530216a7b523f3d384f7db5234fd65b003cd7832581a5c3e7fdb2233a1; source-pins.json SHA256ece1a6d01833ec3bec5efd9a0f026c063e8da5d397b0399e5479588c699dbaca. Parent/source state ise79d6aa8c638032486eddb6d9f7c766f4c415df5. No candidate/repository/notebook edits occurred.

## Actual matrix, Grassmann orientation and link measure

Read the actual gamma/frame/link/closed-action code in l1_full_action_reference.py and the pinned spectral parity/mixed-source passages. Its gamma3 is the real block exchange R=[[0,I],[I,0]], so R²=I, R†=R and detR=+1. Direct multiplication gives R gamma_a R=-gamma_a for a0,1,2, +gamma3 for a3, and R gamma5 R=-gamma5. Thus the induced internal vector matrix O=diag(-1,-1,-1,+1) is orthogonal with determinant-1.

It matters that barpsi is a row: barpsi'=barpsi R means its column of independent Grassmann coordinates transforms by R^T, not by an unrelated conjugation prescription. The combined site-coordinate transformation is diag(R^T,R). Its determinant is det(R^T)detR=1; the Berezin measure Jacobian is the inverse determinant, also1. In explicit bar-first/psi-second coordinate order, the site permutation is[2,3,0,1,6,7,4,5], with8 inversions and top-exterior sign+1. R performs no cross-site mixing. Therefore the full8N-generator top orientation is preserved, for any fixed choice of the global orientation. No bosonic determinant sign or extra source-order sign is introduced.

Conjugating every independent Spin(4) link by R exchanges its two SU(2) chiral blocks. Normalized PRODUCT Haar is invariant under that exchange; it does not equate opposite-directed links or replace one by an inverse. The prospective boundary/link-measure swap invariance is explicitly required. This is a Pin change of variables, not a claim that the fixed-g2 exponent is invariant under a Spin(4) gauge transformation.

## Coframe and action characters

For each of the original forward/backward coframe bilinear blocks, transformed spinors and U'=RUR reduce the gamma insertion to R gamma_a R, with the original signs and daggers unchanged. Every T_mu^a therefore acquires the same O action independently of world direction and endpoint. Since the T components are even, their products commute, and

`sum_a O_ab O_ac T_mu^b T_nu^c = sum_b T_mu^b T_nu^b`.

All tensor components Q_mu_nu, including off-diagonal components and arbitrary fixed real linear combinations, are reflection-even. No traceless-shear/spatial-exchange restriction enters this conclusion.

Every plaquette product transforms by conjugation because all intermediate R² cancel; reversing the product to its closed ordering preserves that fact. Writing the matrix coframe as That=sum_a T^a gamma_a, it transforms to R That R. In the actual closed curvature trace Tr(P That_mu That_nu gamma5), cyclicity leaves R gamma5 R=-gamma5, hence S2 is odd. The cosmological four-coframe epsilon contraction gains detO=-1, equivalently the corresponding four-coframe gamma5 trace is odd; hence S4 is odd too. The reference code's local target quotient excludes S4 by degree; that quotient is not being treated as a full S4 computation. Its full transformation follows from the original epsilon/four-coframe definition and agrees with the previously accepted Pin premise.

An ordinary world A_frame(j) acts on different indices and commutes with O. Thus reflection character and homogeneous Grassmann degree remain unchanged throughout the prescribed analytic fixed-link coframe family and for its derivatives. No gauge-field/difference-map/measure variation is silently added.

## Pure-g2 raw numerator, normalized G and mixed tangent

There are8N independent Grassmann generators and Q has degree4. In Q exp(g2S2), saturation permits only n=2N-1 factors of degree4 S2. This n is odd for EVERY finite integer N>=1. The surviving candidate integrand is reflection-odd and the full integration functional is reflection-invariant; therefore its integral equals its own negative and is0 over characteristic0. This proves the RAW identity for every component and each specified j, without assuming Z16 or any denominator.

With the additional nonzero full partition on a source neighborhood, G(j)=N_Q(j)/Z(j) is identically0 and its first j derivative is0. For the pure-g2 exponent X=g2 S2,j, the inherited exact normalized derivative is B=<Q_j>+Cov(Q,X). Its first term vanishes by the same even-quartic one-point argument. The QX insertion has degree8 and reflection character-1; the remaining saturation count is2N-2, even. Hence its raw expectation also vanishes, and the subtraction <Q><X> vanishes because <Q>=0. This proves B=0 directly, retaining the Q_j contact. Holding the observable fixed simply makes that contact identically0; the rest of the proof still applies.

No analogous selection rule forces A or D to0. Two literal Q insertions are reflection-even and require an even number of ordinary S2 factors. Two dressed derivatives each carry odd character, so their combined even character can survive. Thus the existing positive dressed scalar response is algebraically compatible with zero literal collective metric and zero mixed tangent; it cannot reconstruct a nonzero body from those zeros.

The cited closed four-site partition coefficient1252309350145403/2123366400 appears in the pinned spectral table, normalization divided by g2^8. For real nonzero g2 it supplies a strictly positive denominator at j0; analytic finite-source dependence then supplies a nonzero neighborhood. I accept this as reused existing denominator evidence, without rerunning its contraction. No full sixteen-site nonzero partition or normalized16site G is established. Only its raw numerator identity is unconditional here.

## General coupling parity and homogeneity

For m S4 factors, n S2 factors and k literal Q insertions, total degree8m+4n+4k=8N gives2m+n+k=2N. Under the same integration-variable change, the monomial picks up(-1)^(m+n); every odd-character coefficient vanishes. Combining n congruent k mod2 with m+n even gives m congruent k mod2.

It follows exactly that Z has only even powers of g1; every component of N_Q has odd powers; raw two-Q numerators have even powers. Normalized G is odd and normalized connected A is even wherever both denominators exist. Ordinary fixed coframe-source differentiation preserves these coupling parities, so B is odd and the full dressed D is even. This needs the specified source family, not a source that changes couplings, introduces new Grassmann degrees or changes the measure.

For fixed nonzero g2, each partition monomial rewrites as g2^(2N)(g1/g2²)^m and each one-Q monomial as g2^(2N-1)(g1/g2²)^m. Thus the displayed z-even/q-odd formulas and G=g2^-1 q(x)/z(x) follow. The proposed leading q'(0) calculation is meaningful and may itself vanish; no nonzero value, sign, positive-definite body or parameter range is predicted. For the prescribed finite J0/lambda0 family a nonzero body must leave pureg2 or change an explicit assumption, but that conditional finite statement is not a thermodynamic no-go.

## Reuse and scientific boundary

The spectral interface's existing four-site parity passage already derives2m+n+k=8 and m congruent k, including one-point oddness and pure-g2 vanishing. Its mixed literal/dressed passage already proves the pure-g2 mixed selection rule at distinct times. These are reused accepted results. The candidate's new useful application is the explicit all-component Euclidean metric tensor/body interpretation at arbitrary finite N, the transported Q_j contribution and collective tangent B, and the resulting same-regulator body-calculation target. It does not reclassify old coefficients as new ensemble coverage or conceal a thermodynamic/body existence assumption.

The proof depends on8 independent generators/site, action degrees8/4, no other terms, zero external composite source, no matter determinant, invariant chiral product Haar/boundaries and the prospective fixed-link coframe family. Matter reweighting at finite lambda changes the expansion and is excluded. Noncommuting N/J limits, source-selected states, phase selection, continuum bounds, physical normalization/units, tensor/matter-light dynamics, positive transfer state, B3 window and transport remain open. No canonical settled no-go, Lean admission/proof or publication qualification follows.

## Actual checks and authority

First action and final action immediately before writing this report were `python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-collective-body-review-r1.json` from the assigned checkout; both returned fresh:true/changed:[]. Read packet, new notebook entry, accepted parent decomposition and unchanged roadmap/governing-authority context. Independently checked both science source pins: reference0ad0fd402e18c7d13cc84f9d92d4820bfc7b2726033dc42aa7d79fb0bf5327b6 and spectral6066a81c480080d825d1b8403eb92c97753e0ef366c188533c0df210473213ec.

Permitted tiny control executed: `python3 -B /private/tmp/l1-collective-body-parity-20261105-r1/pin_matrix_control.py`, terminal0, matrix/reflection checks PASS,8 chiral basis checks and3168 degree-parity cases. Its import list is stdlib only. Although it uses Python complex arithmetic, all involved Gaussian-integer components and small sums/products are exactly representable, with no approximation/tolerance comparison. The actual project gamma/frame code was statically read rather than imported. A separate stdlib pathlib/hashlib/json check verified candidate/control/pin hashes and source pins; a direct8-coordinate permutation inversion count checked the site top sign. Read-only rg/sed inspected original parity/mixed passages and reused partition table.

No project science import, scientific contraction, fresh denominator calculation, Git, build/Lean, slot, process/harness/configuration action or candidate/notebook/repository edit occurred. Only this report was written.
