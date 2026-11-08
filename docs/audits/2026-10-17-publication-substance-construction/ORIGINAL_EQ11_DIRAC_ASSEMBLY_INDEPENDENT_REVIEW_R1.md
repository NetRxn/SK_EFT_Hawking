# Independent original finite Dirac assembly review

**ACCEPT** exact worker commit
`353d5f1f77c0b62eeae2dfca54854b049e42dc7a` against
`a09678fcd50c7bdbcf6ab5deb3a4d155e9da3f86`.
The sole path is `lean/SKEFTHawking/ADW/FiniteDiracExecutableAssembly.lean`,
218 lines, SHA256 `7cc7f0cfabdd6200dd20711ab3996cf84a7f959cc1dcf2049429d0f7cde5f281`.
Initial and terminal continuity matched. The worker diff passed
`git diff --check` and the slot worktree was clean. I did not mutate
the worktree or the lease, or perform kernel replay.

## Exact source scope

I read all 13 public theorem statements and their proofs alongside
Python's `OriginalRegulator`, `original_gamma`, `original_coframe_blocks`,
`assemble_coframe`, `assemble_dirac`, and `determinant_jet`.
No local axioms, placeholders, or proof-escape primitives appear in the
module. ROOT owns exact kernel replay and native integration.

- Forward and backward digit reductions match the executable stepping.
  The backward step wraps exactly when the preceding link anchor wraps
  forward. At unit extent both tests hold even though all endpoints
  coincide. Other digits are unchanged.
- The anchored central minus element acts on both Spin(4) fundamental
  blocks. Real signs commute with the conjugate transpose, so the four
  terms are precisely (s_f g U_f^\dagger/4),
  (-s_f U_f g/4), (-s_b g U_b/4), and (s_b U_b^\dagger g/4)
  at their original ordered endpoints. The conditional summands add
  rather than overwrite at coincidence.
- The gamma metric-to-source map is the exact permutation (3,0,1,2).
  The auxiliary relabeling leaves site and step direction unchanged.
  Reindexing uses the previously proved Python mixed-radix coordinate
  and the same spin index for rows and columns. Moving along this
  bijection leaves the determinant unchanged.
- The weighted flat matrix sums over every coframe. At fixed physical
  Spin(4) links, evaluating its (h+J) polynomial at an arbitrary
  complex assignment gives the actual original global matrix with
  shifted and relabeled coefficients. Applying determinant naturality
  and polynomial extensionality over the infinite coefficient field
  gives equality of the shifted determinant polynomials. The bitmask
  determinant identity requires no inverse. Its raw-jet application
  computes the selected first and second derivatives, including two
  positions that choose the same auxiliary coordinate.

The proof specializes links to physical Spin(4) matrices and fixes
arbitrary complex (J) while differentiating auxiliary coordinates.
It does not verify Python's `Polynomial` or `SparseMatrix` storage,
resource accounting, symbolic quaternion normalization, link derivatives,
or arbitrary accelerated source directions. The separately bounded
default (h/J/q) symbolic coefficient check cannot extend this formal
scope. This review establishes no physical or publication verdict.

## Independent composed runtime control

`PYTHONPATH=. .venv/bin/python -B composed_check.py` ran against the
two exact owned Python files. The oracle used four fixed unitary
Spin(4) matrices, including a nondiagonal quaternion block, explicit
gamma matrices, and the coincident-endpoint anticommutator
(s\{\gamma,U^\dagger-U\}/4). It did not reuse the product's scatter,
matrix multiplication, determinant, or jet operations. All arithmetic
was exact dyadic within the small bounded fixture values. Direct
Leibniz expansion of `det(M+t A+s B)` supplied the six raw coefficients,
with doubled ordinary diagonal coefficients. The test matched all 480
assembled matrix entries and all 540 raw derivative slots in 90 cases,
including 30 repeated-coordinate cases, 18 singular value cases, 216
nonzero second-order slots and 72 nonzero mixed slots. Both gamma
conventions and three patterns of boundary signs were exercised.
