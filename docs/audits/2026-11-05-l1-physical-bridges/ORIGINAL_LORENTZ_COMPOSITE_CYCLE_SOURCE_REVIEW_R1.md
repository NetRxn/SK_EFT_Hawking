# Independent actual original-source/physics review r1

Verdict: **REVISE** for one necessary source-custody correction in section 8 / equation (8). The actual composite/action phases and gauge-reduced bare-cycle argument otherwise withstand this manual source/physics review. Prospective acceptance was not used as actual-result acceptance. No other actual reviewer verdict was consulted.

Full frozen candidate read: `/private/tmp/l1-lorentz-composite-cycle-result-r1.md`, **26399 bytes**, SHA256 **434c82fe2a3fa6cd196f40847ad18a2e1ef4a5626ee8d6237460117cbbc40aac**. Candidate and repository were not edited. Only this report was written.

## Necessary repair: inherited coframe reflection has the opposite sign

Section 8 says the accepted aligned internal reflection has `r4=+1,rAlpha=-1`. The actual accepted authority is N16_TEMPORAL_BOUNDARY_IDENTITY.md section 6, explicitly reused by ORIGINAL_EHC_REFLECTION_SOURCE_ADJOINT.md section 1:

```
R gamma_A R=s_A gamma_A, s_old0=+1, s_oldi=-1;
theta T_mu^A=epsilon_mu r_A T_mu^A(rho x), r_A=-s_A.
```

The candidate's proper internal permutation sends original internal 0 to source 4; the other three aligned axes remain perpendicular to it. Therefore the actual aligned values are **r4=-1, rAlpha=+1**. The signed third-axis change does not alter these eigenvalues. Section 8 has substituted s for r.

Its displayed anti-linearity calculation is otherwise correctly typed: with `T'_C=d_C E^a`, `d4=-i`, `dAlpha=1`, the factor is `r_C d_C/conjugate(d_C)`. Inserting the inherited r gives +1 for all four components. Equation (8) must consequently read

```
theta_M E_mu^a(x)=+epsilon_mu E_mu^a(rho x).
```

Correct the stated aligned r values and equation (8), and check any text relying on that coframe law. Keep the original theta, not a replacement reflection or parity twist. This is a material correction to the requested coframe/real-structure correspondence, even though its square cancels in the quadratic metric law. The subsequent metric law `theta_M G_mu,nu=epsilon_mu epsilon_nu G_mu,nu(rho x)` survives. Injective transport of the original EHC defect, the bare-cycle argument and the literal source chain factors do not rely on choosing the incorrect overall coframe sign. This narrow repair should be separately frozen and rechecked rather than changing R1 retrospectively.

## Actual algebra and original-source checks

Read every section 1–9 of the candidate. Directly reread held Vergeles2506.00036v2 II(2.16)–(2.26), VI(6.1), and the exact accepted N16/EHC reflection passages. Reuse the unchanged direct primary readback of II(2.6), III(3.9), IV(4.1)–(4.10), and Diakonov1109.0091v1 V(20)–(25) made during the immediately preceding prospective source review; this is reuse of source evidence, not acceptance inferred from the prospective verdict. Read packet/current topical notebook, current Phase6a Lorentzian objective and open B3 framing. Original extracts: `/private/tmp/l1-current-claims-review-20261105-r1/Vergeles2025.txt` and `/private/tmp/l1-Diakonov2011.txt`; no new literature-wide coverage is claimed.

The section 2 gamma basis construction is internally consistent. `S=diag(q0†,I)` has determinant one and sends original gamma0 to the off-diagonal identity matrix. The permutation `(1,2,-3,0)` is proper, preserves gamma5, and gives `i Gamma0 Gamma1 Gamma2 Gamma3=gamma5`. It aligns internal labels without moving the world time axis. The independent bar change by Gamma0 has determinant +1; together with S/S inverse this produces unit finite Berezin Jacobian with the inherited order. It does not impose a Majorana relation or eliminate independent bars.

The endpoint convention warrants Omega_xy=U'_xy inverse. Both forward and backward brackets remain; Nt2 vertex coincidence does not identify their links. Vergeles' i/2 composite and Diakonov's symmetric quarter coframe give equation (1), not the independent-tetrad rule. With the specified gamma and bar maps this yields `T'_4=-i E0`, `T'_Alpha=EAlpha`, `Q_E=-G_M`. The determinant phase +i follows from the three-column permutation moving E0 to first position and the coefficient -i. The once-counted literal source then requires `J_E=-i K`; no real-source identification is hidden.

Section 3 derives the EHC phase for the accepted closed holonomy rather than borrowing the simplicial action's phase. Clifford contraction gives `-i Gamma_a E^a`, so the two-coframe term has the stated minus sign and retains g2/4 and the full world sum. Antisymmetrization is necessary: only the block-traceless antisymmetric B_ab is used. Its pseudo-Hermiticity and Lorentz H pseudo-unitarity turn conjugation of Tr(H B_ab) into Tr(H inverse B_ab); the 2x2 determinant-one identity makes this the negative original trace. Thus the formal imaginary curvature coefficient and the stated real A_M are consistent. This remains a Grassmann/coefficient anti-involution, not a Hilbert adjoint theorem. The printed Diakonov Eq17 comparator is explicitly left unresolved and is not falsely identified with the accepted closed action.

Vergeles explicitly retains the composite extension in VI(6.1), but also its Minkowski gauge/convergence problems. II(2.26) expressly distinguishes formal Hermiticity from the scalar-product question. The candidate respects that distinction. It does not import IV's assumed ONB, finite matrix elements, normalizable domain or spectral prescription into the hypercube. Nor does it equate the (3.9) exponential kernel with the integral-action or spectral operator.

## Actual gauge-reduced obstruction

The real form `diag(g,(g†)^-1)` is compatible with off-diagonal Gamma0; its Lie algebra is a real form of the two complex sl2 factors. The action has no scalar body potential. Complete Berezin extraction therefore produces finite regular link polynomials, including all action saturation classes and source jets, not an ordinary scalar oscillatory exponential. Inverse entries are polynomial adjugates. Gauge covariance and unit odd Jacobians preserve the full polynomial.

The finite-translation-span argument is valid as written: under an assumed L1 norm the translate space is a genuine finite-dimensional normed space; its isometries admit an invariant positive auxiliary inner product. Bounded evaluation then makes the sum of squared basis functions a nonzero integrable constant on an infinite-Haar-volume group, a contradiction. This auxiliary norm is a proof tool on a hypothetical L1 function space, not a physical state norm.

Crucially section 6 goes beyond an infinite vertex orbit. The 15 tree edges and 49 loop coordinates retain parallel temporal anchors. The two-loop D(lambda), M(a,d) chart removes the remaining continuous simultaneous conjugation: the first off-diagonal tangent fixes off-diagonal X, its diagonal fixes lambda, and the second upper-right entry fixes residual diagonal X. On the stated generic set only finite ambiguities remain. Unimodularity gives the tree Haar reduction. The local first-pair density is independent of k by simultaneous-conjugation invariance, and transforming all spectator loops is block triangular and Haar preserving. The resulting positive density depends on the first-pair invariants, not the 47 spectator loops. This is the decisive distinction from the old gauge-volume inventory; it does not require a global quantum gauge-fixing construction.

Section 7's nonzero scope is appropriately conditional. The accepted compact nonzero-Z witness proves the complete holomorphic polynomial is nonzero at those numerical couplings; determinant-one coordinate changes do not change that fact. Uniqueness on the Lorentz real form prevents its restriction from vanishing identically. The generic pair locus is dense; continuity then provides a nonzero slice point and a positive-measure neighborhood of the other variables. At each such point a whole spectator-group section is a nonzero finite-span function. Tonelli applied to absolute values yields residual-loop absolute divergence with the displayed local quotient measure. Zero polynomials/jets and gauge-noninvariant insertions are excluded. No selected term, pointwise-only argument or division by a gauge-volume infinity substitutes for this step.

This establishes the intended obstruction only for the stated ordinary bare real-Haar prescription, conditional on correcting the separate coframe-reflection formula. It does not rule out conditional/distributional or complex-cycle integrals, boundary-weighted open kernels, or controlled Euclidean reconstruction.

## Sources, kernels and physical boundary

Apart from the equation (8) correction, section 8 retains both original kernel orientations, opposite cuts, independent temporal anchors, finite Berezin transport and periodic sewing. It explicitly denies a compact-Haar to Lorentz-Haar equality and supplies no physical Hilbert-space intertwiner. Literal K derivatives have factors -i, -1 and -i for first, second and mixed frame derivatives. The stated quotient rule retains both denominator derivatives, and prescribed C2 frame acceleration and insertion/map derivatives remain. A compact nonzero-denominator neighborhood is not a convergent Lorentz denominator. The separate temporal control is correctly left a compact complex-source identity.

The actual result remains useful: an explicit composite/source phase map plus residual-loop failure of one bare-cycle ingredient, not another optional positive norm test. Positive physical domain/product/adjoint, polarization and secondary constraints, original source/transfer maps30–31, calibration, matter/scale, controlled limit, B3/N4/tensor/light/transport/publication remain owed. No physical coupling point, state, action symmetrization, source reduction or new model is selected. Accepted metric F60/G52 and temporal coefficients are preserved; a14 and K/K_R are not reevaluated.

## Checks and commands

FIRST and FINAL identical command, from the managed checkpoint:

```
python3 scripts/codex_continuity.py check /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-lorentz-cycle-actual-source-r1.json
```

Both exit 0, `fresh:true`, `changed:[]`, task `l1-lorentz-cycle-actual-source-r1`. Final check immediately preceded this report write. Candidate size/hash were measured with `wc -c` and `shasum -a 256`; source reads used `cat`, `sed`, `rg`. No scientific evaluator/import, numerical calculation, matrix/Haar/exterior program, test/build/Lean/controller/slot/process action occurred. No other actual review was read. REVISE is solely the concrete inherited reflection-sign correction above, not an infrastructure or authority blocker.
