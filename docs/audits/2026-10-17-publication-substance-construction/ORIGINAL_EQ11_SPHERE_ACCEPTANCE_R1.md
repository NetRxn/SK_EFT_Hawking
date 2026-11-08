# Original finite Eq11 quaternion sphere equivalence

ROOT accepts the exact homeomorphism from the Euclidean real unit
3-sphere to the actual SU(2) group and its equivariance under the
original plus-i quaternion convention. The inverse coordinates
follow from unitarity and the two-by-two adjugate. The determinant
of the arbitrary real quaternion block equals its squared Euclidean
norm, which gives an actual surjective real-linear isometry for
left multiplication. Its restriction obeys the sphere action laws.

The [independent review](ORIGINAL_EQ11_SPHERE_INDEPENDENT_REVIEW_R1.md)
accepted exact worker commit `9a5cc446332865d7440cd306da37c7e74eadb924`.
The [exact bounded controls](ORIGINAL_EQ11_SPHERE_CONTROLS_R1.zip)
matched 414 chiral blocks and 10,206 ambient left-action cases.
The same archive includes a separate check of the Python moment
formula against the normalized Gaussian ratio for 7,315 exponent
tuples through total degree 18 and 4,845 sphere identities. Those
are arithmetic controls. The proof of the actual Haar pushforward
and the all-order integrated moment identity remain due.

[Kernel replay](ORIGINAL_EQ11_SPHERE_LEAN_RECEIPT_R1.json) verified all 21
public declarations with only standard axioms and no warnings or errors.
[Native absorption](ORIGINAL_EQ11_SPHERE_NATIVE_RECEIPT_R1.json) succeeded
at `acf6e548965a521b95ef095a024dc8797cfc6871`. Built object SHA256
`831da18b18469607c2a2b7c7dd71b53b626a783c9529500f3a43993343889f19`.
The controller released wt1 and confirmed complete capacity. The
[remote source](https://github.com/NetRxn/SK_EFT_Hawking/commit/247ba051c04f79d64773e2d2a576f3cd1d0b9301)
matches the exact two-path proof and import diff.

The next Lean target is normalized sphere measure pushforward to the
existing su2Haar, followed by all-order moments and independent
anchor/chirality products. Publication and full physical response
remain open.
