# Exact closed-order diagonal composite replay

This is the pure-g₂ coefficient of the linear plus-composite
cross derivative between sites 0 and 3 on the four-site regulator.
The source and action normalization is the same as in the
[original diagonal calculation](L1_OFFDIAGONAL_HESSIAN.md).
The closed path reverses the four plaquette matrices in the
literal trace without changing their daggers, site labels, or
gamma insertion. The source-site commutator in the residual
family is likewise ordered as V†U†VU.

Run both modes with the repository Python environment and a C++20
compiler. The output directory stores the freshly enumerated
supports, exact Gaussian center receipts, and batched contractions.

```sh
python "$audit/l1_closed_composite_diagonal_replay.py" /tmp/l1-diagonal-closed closed
python "$audit/l1_closed_composite_diagonal_replay.py" /tmp/l1-diagonal-literal literal
```

The unused-source cancellation and isolated two-transport-link
antisymmetry are independent of plaquette ordering. In the latter,
the antisymmetric contraction vanishes for every curvature gamma
pair before multiplying its coefficient, and the isolated
transport links do not occur in the curvature. The isolated
same-curvature center zero is rechecked in the replay, with all
320 supported slices zero in both orders. The mixed center uses
608 supported slices. Each of its 24 nonzero entries reverses sign,
and the two signs cancel in the shifted join. The residual family
requires the closed source-site commutator kernel and a separate
exact contraction.

| Raw coefficient of g₂⁶ | Literal | Closed path |
| --- | ---: | ---: |
| Shifted two-center subtotal | 25/1536 | 25/1536 |
| Eight-orbit residual subtotal | −3563/27648 | −3563/3072 |
| Full diagonal plus numerator | −3113/27648 | −1171/1024 |

All imaginary coefficients in the joined results vanish. Dividing
by the positive closed-order normalization gives a negative
diagonal-separation response at nonzero real g₂. The result is for
the specified finite linear composite source. It leaves background
source matching and continuum susceptibility open.
