# L1 two-site source-only shear response

For one once-pair shear source H at either site, coupling the longitudinal direction to one of three transverse directions, the literal two-site partition polynomial is Z(H) = 3366 g₂⁴ + (45/4)g₂²H². The second derivative is (45/2)g₂². At nonzero g₂, the six-coordinate Hessian of log Z is 5/(748g₂²) times the identity. For a full-symmetric source coordinate with H = 2K the diagonal is multiplied by four.

The [exact contraction](l1_offdiag_hessian.py) gives 15 per complementary curvature direction. The three directions and the action-square factorial give the stated second derivative. Omitting an independent endpoint changes the scaled derivative to 9/2. The [support enumeration](l1_offdiag_hessian_support.py) accounts for all 36 entries. Same-site distinct shears vanish by center parity. The intersite and linear survivors contain an independent mean-zero curvature. Saturation and parity exclude the g₁ contributions.

Independent adversarial review reproduced the exact calculation and separately checked the support and normalization, including the factor of two between the quadratic coefficient and the second derivative. This is a finite static source response. Physical tensor projection, volume and vacuum limits, operator normalization and RPA matching remain open.

## Independently verified projection and normalization

Let e be the elongated axis and assume it is spatial. A nonzero shear in this block is S = e⊗w + w⊗e with w perpendicular to e. It is traceless, and Sn = e(w·n) + w(e·n) for unit propagation direction n. It is transverse precisely when both dot products vanish. The only nonzero spatial lattice momenta lie along e. The transverse projector kills this shear block at those momenta. If e is Euclidean time, the block consists of time-space shears. At zero momentum, an algebraic TT cross polarization can be selected with an externally specified transverse limiting axis.

For a Frobenius-unit symmetric shear, the once-pair coordinate of a physical source of amplitude η is H_j = 2a²Z_Qηw_j, with squared norm of w equal to 1/2. Dividing the uniform source Hessian by 2a⁴ gives the conditional density 2Z_Q²h = 5Z_Q²/(374g₂²), where h is the site-diagonal Hessian entry. This uses the matched-operator convention and leaves normalization, contact subtraction, and operator mixing to the physical construction.

The next finite tensor target uses the site-resolved sources G₂₃ and G₂₂−G₃₃, where e is direction 1 and the remaining spatial polarization plane is 2–3. For signed action terms g₁A + g₂B of degrees eight and four, the degree-sixteen top extraction gives Z_u from G_u(g₁g₂AB + g₂³B³/6) and Z_uv from G_uG_v(g₁A + g₂²B²/2). Evaluate the connected combination Z_uv/Z − Z_u Z_v/Z² before projecting the symmetric and antisymmetric lattice characters.

Independent adversarial review checked the transversality and once-pair factors. This result gives a finite static projection and specifies the missing nonzero-momentum channels.

## Independently verified transverse block

The [support enumeration](l1_transverse_support.py) excludes the linear and g₁ quadratic terms. The [exact numerator calculation](l1_transverse_top.py) gives local moments H² = 9 and D² = 21 for H = G₂₃ and D = G₂₂−G₃₃. Three opposite-site curvature squares and the action factorial multiply these moments by 54. Dividing by the finite partition function gives the site-diagonal log Hessians 27/(187g₂²) and 63/(187g₂²), respectively.

Exchange of the two selected transverse directions makes the same-site mixed coefficient odd. The only intersite cross survivor has complementary curvature links separate from the source links. Haar averaging of the longitudinal conjugations leaves a zero mixed scalar-vector moment for each independent complementary link. All other intersite terms vanish by support. Independent review checked these zero contributions and reproduced the diagonal moments.

The coincident-link frame is {γ,U†−U}/4. A separate exact spherical quadrature gives the diagonal fourth moment 75/2 and detects the earlier incorrect frame expression, which yields 15/4. The corrected block has two positive but unequal responses. Frobenius-unit cross and plus polarizations give conditional source densities 54Z_Q²/(187g₂²) and 63Z_Q²/(374g₂²) for either two-site Fourier character. Physical operator matching, contact subtraction, larger volumes and real-time continuation remain open.

## Independently verified separate-time source control

On a 2×2×1×1 torus with separate time and propagation axes, set g₁ = g₂ = 0 and anchor the unused spatial column with unit local transverse trace sources. In the active column, t and s are the two time-metric sources and h and k are the local once-pair transverse cross sources. Site saturation and independent transverse-link center flips permit only time degree four or two cross insertions at each site. The full partition function is (129/2)² times the active-column polynomial Q₄(t,s) + 81h²k²/4. The constant factor cancels in connected derivatives.

The [exact composition check](l1_time_space_source_control.py) uses the previously reviewed longitudinal Q₄, with Q₄(1,1) = 6477/32, and the exact local transverse moments. At t = s = 1 and h = k = 0, the time-separated mixed two-point derivative is zero and the mixed fourth derivative of log Z is 864/2159. A local trace-only control gives zero for both separated derivatives and 6/43 for the local second derivative. The fourth derivative is in once-pair source coordinates and is multiplied by four for Frobenius-unit cross sources.

Independent review checked factorization, saturation, the prior polynomial, and exact derivatives. This is an externally sourced, zero-interaction fourth cumulant. The interacting source-free two-point response and transport extraction remain open.
