# L1 two-site source-only shear response

For one once-pair shear source H at either site, coupling the longitudinal direction to one of three transverse directions, the literal two-site partition polynomial is Z(H) = 3366 g₂⁴ + (45/4)g₂²H². The second derivative is (45/2)g₂². At nonzero g₂, the six-coordinate Hessian of log Z is 5/(748g₂²) times the identity. For a full-symmetric source coordinate with H = 2K the diagonal is multiplied by four.

The [exact contraction](l1_offdiag_hessian.py) gives 15 per complementary curvature direction. The three directions and the action-square factorial give the stated second derivative. Omitting an independent endpoint changes the scaled derivative to 9/2. The [support enumeration](l1_offdiag_hessian_support.py) accounts for all 36 entries. Same-site distinct shears vanish by center parity. The intersite and linear survivors contain an independent mean-zero curvature. Saturation and parity exclude the g₁ contributions.

Independent adversarial review reproduced the exact calculation and separately checked the support and normalization, including the factor of two between the quadratic coefficient and the second derivative. This is a finite static source response. Physical tensor projection, volume and vacuum limits, operator normalization and RPA matching remain open.
