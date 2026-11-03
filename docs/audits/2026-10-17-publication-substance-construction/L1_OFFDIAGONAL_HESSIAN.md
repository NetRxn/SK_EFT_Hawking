# L1 two-site source-only shear response

For one once-pair shear source H at either site, coupling the longitudinal direction to one of three transverse directions, the literal two-site partition polynomial is Z(H) = 3366 g₂⁴ + (45/4)g₂²H². The second derivative is (45/2)g₂². At nonzero g₂, the six-coordinate Hessian of log Z is 5/(748g₂²) times the identity. For a full-symmetric source coordinate with H = 2K the diagonal is multiplied by four.

The [exact contraction](l1_offdiag_hessian.py) gives 15 per complementary curvature direction. The three directions and the action-square factorial give the stated second derivative. Omitting an independent endpoint changes the scaled derivative to 9/2. The [support enumeration](l1_offdiag_hessian_support.py) accounts for all 36 entries. Same-site distinct shears vanish by center parity. The intersite and linear survivors contain an independent mean-zero curvature. Saturation and parity exclude the g₁ contributions.

Independent adversarial review reproduced the exact calculation and separately checked the support and normalization, including the factor of two between the quadratic coefficient and the second derivative. This is a finite static source response. Physical tensor projection, volume and vacuum limits, operator normalization and RPA matching remain open.

## Independently verified projection and normalization

Let e be the elongated axis and assume it is spatial. A nonzero shear in this block is S = e⊗w + w⊗e with w perpendicular to e. It is traceless, and Sn = e(w·n) + w(e·n) for unit propagation direction n. It is transverse precisely when both dot products vanish. The only nonzero spatial lattice momenta lie along e. The transverse projector kills this shear block at those momenta. If e is Euclidean time, the block consists of time-space shears. At zero momentum, an algebraic TT cross polarization can be selected with an externally specified transverse limiting axis.

For a Frobenius-unit symmetric shear, the once-pair coordinate of a physical source of amplitude η is H_j = 2a²Z_Qηw_j, with squared norm of w equal to 1/2. Dividing the uniform source Hessian by 2a⁴ gives the conditional density 2Z_Q²h = 5Z_Q²/(374g₂²), where h is the site-diagonal Hessian entry. This uses the matched-operator convention and leaves normalization, contact subtraction, and operator mixing to the physical construction.

The next finite tensor target uses the site-resolved sources G₂₃ and G₂₂−G₃₃, where e is direction 1 and the remaining spatial polarization plane is 2–3. For signed action terms g₁A + g₂B of degrees eight and four, the degree-sixteen top extraction gives Z_u from G_u(g₁g₂AB + g₂³B³/6) and Z_uv from G_uG_v(g₁A + g₂²B²/2). Evaluate the connected combination Z_uv/Z − Z_u Z_v/Z² before projecting the symmetric and antisymmetric lattice characters.

Independent adversarial review checked the transversality and once-pair factors. This result gives a finite static projection and specifies the missing nonzero-momentum channels.
