# L1 tensor and electromagnetic propagation: conditional derivation contract

Date: 2026-11-07. Scope: cloud research and written conditional analysis. **No physical L1 tensor pole, photon sector, response-to-speed correspondence, B3 normalization or observational prediction is established here.** This reference records what a derivation must supply; it does not promote scientific results, close findings or change project gates.

Coordination: [issue #121](https://github.com/NetRxn/SK_EFT_Hawking/issues/121). Consume the [reviewed intake in PR #120](https://github.com/NetRxn/SK_EFT_Hawking/blob/c31f0f596b807a8c4ed1325393fe35dedf72e8ef/docs/references/L1_CLOUD_RESEARCH_INTAKE_2026-11-07.md), rather than duplicate its W1 certificate or source-calibration assignments.

## Source pins and established inputs

The current accessible PR heads were checked on this date: PR #113 is `864f4ec25667e345b90e8a8570a00c10c17b198f`, PR #115 is `c0a775c942fc62528fec2d0b645e4dfe858ae61c`, and PR #120 is `c31f0f596b807a8c4ed1325393fe35dedf72e8ef`. These are branch snapshots, not integration of those scientific branches into main.

The [W0–W5 roadmap](https://github.com/NetRxn/SK_EFT_Hawking/blob/c0a775c942fc62528fec2d0b645e4dfe858ae61c/docs/roadmaps/L1_Physical_Bridges_Roadmap.md) makes W3 consume W1's physical state/source and W2's normalization; W4 additionally owes causal dynamics and observational-band control. Its existing planner and publication ownership remain authoritative. This note adds no worker assignment, execution admission, routing ledger or resumption instruction.

The accepted [collective-response decomposition](https://github.com/NetRxn/SK_EFT_Hawking/blob/864f4ec25667e345b90e8a8570a00c10c17b198f/docs/audits/2026-11-05-l1-physical-bridges/PHYSICAL_MATCHING_DECOMPOSITION.md) defines one normalized functional with G=W_J, A=W_JJ, B=W_Jj and D=W_jj. On a justified retained coordinate domain with invertible A, and convention Gamma=JG-W,
`Gamma_GG=A^-1`, `Gamma_Gj=-A^-1 B`, `Gamma_jj=-D+B^T A^-1 B`.
These are local algebraic identities, not positivity or a real-time reconstruction theorem. In particular, the dressed-strain scalar D alone does not fix A, its inverse, or derivative coefficients of a tensor kernel.

The [kinetic/source acceptance](https://github.com/NetRxn/SK_EFT_Hawking/blob/864f4ec25667e345b90e8a8570a00c10c17b198f/docs/audits/2026-11-05-l1-physical-bridges/ORIGINAL_KINETIC_NORMALIZATION_CORRESPONDENCE_ACCEPTANCE.md) leaves actual-result Eqs.30–31 (physical transfer/source correspondence) unmatched. It supplies neither a physical adjoint/norm nor an electromagnetic gauge field: a constant global phase symmetry and local current variation are not a constructed dynamical U(1) sector. Accepted nonzero partition normalization and temporal nontriviality do not fill these gaps. Source-specific positivity obstructions and failed reconstruction scopes remain as recorded in the intake.

## 1. Assumptions to discharge before interpreting a speed

A physical comparison needs all of the following, or an explicit statement of which are only assumptions.

1. An actual regulated action, source coupling through second order, observable algebra/product/adjoint, normalized state and physical positivity domain. Retain action, measure, reconstruction-map and regulator contacts; no favorable projected covariance substitutes for a state.
2. A background solving the appropriate sourced/saddle equations with controlled approximation, a physical Lorentzian signature and time/length calibration. Specify whether matter sees a configuration metric, collective G, or a matched effective field. The existing positive-body scalar construction does not decide this.
3. A causal real-time prescription, or a justified reconstruction with sufficient temporal/spectral information. Finitely many Euclidean coefficients do not determine an unrestricted retarded spectrum. Fix Fourier, retarded and Legendre conventions explicitly.
4. Complete fluctuations of the coframe, connection, matter and multiplier fields, with gauge transformations, constraint rank and boundary conditions. Establish physical degrees of freedom and stability before calling two components gravitational waves.
5. A nonempty regime of momentum, frequency, volume, regulator and coupling where the reduction and omitted operators have controlled errors. A finite-regulator algebraic identity alone is not a continuum or observational-band estimate.

Failure of an early condition leaves a later formula conditional. It does not prove that all physical completions fail.

## 2. Constraints and the physical kernel

Let q denote candidate propagating fluctuations and n the remaining variables, after explicitly distinguishing gauge directions from constraints. At quadratic order write the kernel in blocks K_qq, K_qn, K_nq, K_nn. If K_nn is invertible in the stated domain, solving n's linear equation gives

`K_eff = K_qq - K_qn K_nn^-1 K_nq`.

This is a conditional elimination identity. A Lagrange multiplier with zero quadratic block must instead have its constraint imposed; a singular gauge block needs a justified gauge fixing/quotient. Do not use an inverse on null directions. Zeros or poles of the eliminated block require inspection of the original system: they may signal additional modes, invalid elimination or cancellations. A frequency-dependent Schur complement can encode dynamics and is not automatically a local two-derivative action.

A TT projection before this analysis may hide constraints, scalar/vector/connection modes or mixing. In an isotropic background different rotation sectors can decouple if the full equations establish it; anisotropic backgrounds, parity violation, nonlocality or mixing require the actual matrix principal symbol and branch/polarization analysis. Count and test the additional physical sectors as well.

A determinant zero is only a candidate pole. For a physical reduced retarded matrix K_R, right and left null vectors u,v at an isolated simple root omega_p obey, locally,

`K_R^-1 ~ u v^dagger / [(omega-omega_p) v^dagger (partial_omega K_R) u]`.

This expression assumes a one-dimensional nullspace, nonzero derivative pairing and analytic local kernel. Repeated roots, branch cuts, singular constraints and defective matrices need separate treatment. In a dissipative system left and right modes need not coincide. Observable response is a source/detector contraction of this inverse, with the matched vertices and contact terms. Zero overlap can remove a candidate pole from that observable; a formal tetrad component pole alone is insufficient. [Carone–Erlich–Vaman, Sec.III, Eqs.31–46](https://arxiv.org/html/1812.08201#S3) illustrates cancellation of apparent inverse-kernel poles after external contractions in a specified large-N composite-gravity model; its action, regulator, tuning and approximation differ from L1.

Assess residue sign in the physical spectral/energy convention after the source and adjoint are fixed. In a lossless Hermitian two-derivative reduction, a positive kinetic matrix on the physical quotient is the usual no-ghost test. It is not a proof of positivity of the original signed functional. Retarded poles must have the required stability/causality properties (for exp(-i omega t), no unstable upper-half-plane physical poles). Positive gradients exclude the simplest long-wavelength gradient instability, not every finite-momentum or nonlinear instability.

## 3. Same-background tensor and photon comparison

Conditionally assume a parity-even isotropic local regime with two tensor helicities, no relevant mixing and controlled two-derivative truncation. In a local physical frame take the leading tensor action proportional to
`G_T (partial_t h_TT)^2 - F_T (spatial_gradient h_TT)^2`,
with positive overall action convention. The candidate tensor denominator can be written
`G_T (omega+i0)^2 - F_T k_phys^2`
up to an overall sign fixed consistently in the response convention.

For G_T>0 and F_T>0 its leading characteristic speed is `c_T^2=F_T/G_T`. For one canonically specified component the positive-frequency residue with this denominator is `1/(2 G_T omega_T)`; physical observable residues include vertices and normalization. This statement presupposes the physical tensor realization above. The corresponding cosmological quadratic action and positivity conditions are explicit in [Kobayashi–Yamaguchi–Yokoyama, Sec.IV.1, Eqs.34–39](https://arxiv.org/html/1105.5723v2#S4.SS1); their scalar-tensor inflationary model is a comparison method, not an L1 derivation.

Derive a dynamical electromagnetic gauge field and its constraints in the SAME state, background, clock/ruler convention and truncation. For an isotropic parity-even medium with no relevant tensor/photon mixing or additional constitutive operators, write the transverse Maxwell action as
`(1/2)[Z_E E^2 - Z_B B^2]`.
Gauss's law and gauge reduction leave transverse polarizations. For Z_E>0 and Z_B>0 the leading cone is `c_gamma^2=Z_B/Z_E`. A scalar control, massive particle group velocity or global phase current does not supply this photon kernel.

Consequently
`r := (c_T/c_gamma)^2 = F_T Z_E/(G_T Z_B)`,
and equal leading cones require
`F_T Z_E = G_T Z_B`.
A common coordinate/time rescaling changes the two coordinate speeds together and cannot impose this equality. A nonsingular field rescaling changes a sector's kinetic and gradient normalization together, leaving its speed unchanged; source/observable residues must transform with it. [Fumagalli–Mooij–Postma, Secs.3–4](https://arxiv.org/html/1610.08460v2) explains the frame/unit issue in its specified inflationary setting.

Covariance under diffeomorphisms or internal Lorentz frame rotations alone does not enforce equal cones in a state with preferred tensors. [Oost–Mukohyama–Wang, Sec.II and Appendix A](https://arxiv.org/html/1802.04303v3) derives constrained spin-2, spin-1 and spin-0 propagation in covariant Einstein-aether theory and provides a concrete comparison counterexample to that inference. It is not a claim that L1 is Einstein-aether theory.

A sufficient prospective protection mechanism would be a demonstrated common unbroken spacetime Lorentz symmetry in the relevant state and a leading physical principal operator in each sector built from the same effective metric, with healthy nonzero coefficients. Establish the actual hypotheses and radiative/limit control. General covariance of an action does not show that its background or state preserves those hypotheses. Where coefficients depend on direction, polarization or frequency, compare the actual characteristic branches rather than force the scalar r formula.

## 4. What would derive the response-to-speed map

The proposed L1 law `c_GW=c_gamma sqrt(chi_L1)` requires deriving `chi_L1=r` from the microscopic response with its independently fixed normalization. Defining chi to be r would make the law algebraic and would not identify W2's susceptibility.

An adequate derivation must:

1. Specify precisely which physical source, projector, contact prescription, connected or inverse kernel, subtraction, regulator and normalization define chi_L1/B3. Retain the original Lambda-squared/(16 pi-squared) normalization objective and [0.1,10] as a computed-result requirement; do not fit a source or coupling to enforce them.
2. Derive the full frequency/momentum collective response on that same physical domain, relate its properly reconstructed retarded inverse to the reduced tensor kernel, and match observable/source vertices. The partial Legendre identities are reusable but do not alone justify analytic continuation, constraints or collective-to-matter identification.
3. Extract temporal and spatial derivative coefficients of that kernel with their contact and mixing contributions. In a local analytic expansion about a specified point, coefficients of omega^2 and k_phys^2 are independent data unless an identity relates them. In gapless, dissipative or nonanalytic regimes, do not assume a Taylor expansion or interchange static, homogeneous and on-shell limits.
4. Derive the photon coefficients from the common matter coupling, and show by an actual dynamical or symmetry identity why the normalized W2 response equals `F_T Z_E/(G_T Z_B)`, with a controlled error if the claim is approximate.
5. Verify normalization covariance, regulator/volume limits, stability and radiative corrections; propagate errors through r and its square root on a domain bounded away from vanishing denominators. A correspondence failing near a critical point cannot establish a uniform susceptibility window.

A simple conditional non-identifiability check explains the missing information. Consider reduced candidate kernels `K=a omega^2-b k^2-m^2`, with positive a,b,m^2 and a fixed source convention. Their zero-frequency, zero-momentum inverse has the same value `-1/m^2` for every a,b, while their principal speed squared is b/a. Thus one static number does not fix a characteristic cone even within a healthy local quadratic family. This is a written illustrative comparison, not an L1 model or computed susceptibility. For a massless kernel the zero-momentum static inverse is singular; one must specify limits/subtractions instead. Matching a static k^2 coefficient can at most fix the spatial coefficient under further hypotheses; the temporal coefficient and photon reference remain owed.

Even a full justified zero-frequency response is generally insufficient to fix all time derivatives. [Moore–Sohrabi, Secs.II–III](https://arxiv.org/html/1007.5333v3#S3) separates metric-source contacts and temporal/spatial derivative responses with specified ordered limits in equilibrium conformal hydrodynamics; neither its fluid assumptions nor an identification with a gravitational inverse propagator are established for L1. Conversely, a symmetry can fix a common cone while leaving response amplitudes unconstrained. If r=1 is derived, the proposed mapping additionally requires chi_L1=1 in its independently defined normalization, or the proposed mapping fails.

## 5. Outcome and observational boundaries

| Outcome | Required evidence | Consequence for L1 |
|---|---|---|
| Equal leading cones | Healthy physical tensor and photon poles on the common state/background plus r=1 from dynamics or protection | Conditional scalar interval mathematics remains; an observable speed deviation is not produced merely by a nonunit static response |
| Unequal cones | Healthy observable poles, same-background coefficients, r different from one, controlled errors and additional-mode tests | Constrain the derived r; constrain chi only after proving its correspondence |
| No usable propagation prediction | No positive state/source bridge, no tensor or photon pole, zero relevant overlap, unstable/extra uncontrolled modes, singular reduction or uncontrolled observational band | Report the exact failure scope; do not substitute a scalar pole or label a general no-go |

Leading characteristics, finite-band phase velocity, group/packet arrival velocity and a UV front velocity are distinct objects. A low-energy derivative ratio does not automatically describe the observed band. [De Rham–Melville](https://arxiv.org/abs/1806.09417v2) gives an explicit EFT/cutoff example of frequency-dependent restoration of luminality; it does not establish that behavior in L1.

Reuse the accepted [conditional transport expansion](https://github.com/NetRxn/SK_EFT_Hawking/blob/864f4ec25667e345b90e8a8570a00c10c17b198f/docs/audits/2026-10-17-publication-substance-construction/L1_RETARDED_TRANSPORT_MATCHING.md) only after deriving the physical kernel. Its linear dissipative term gives leading attenuation, not a real linear speed shift. An arrival-time comparison additionally needs a controlled frequency/bandwidth/path regime, wavepacket distortion/attenuation, emission-delay assumptions and uncertainty, as required by W4. No GW170817 constraint is newly evaluated here.

## Review and promotion boundary

Verification for this reference is remote source readback, equation/hypothesis review and documentation scope checks. No Lean, scientific evaluator, build, notebook, harness, worktree, slot or paused-session operation is part of this research. Native/project scientific gates remain pending and are not claimed passed. Independent mathematical and physics/source review of this handoff is required before documentation merge; acceptance of this reference does not validate the microscopic bridges or promote it into canonical formulas, manuscripts, findings or publication claims.
