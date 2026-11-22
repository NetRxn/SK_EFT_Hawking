# Independent D8 finding 1.5 source and render review R1

**ACCEPT** the exact author patch SHA256
`ac53d1a46f81b693a4d57cf3d3d69e6f402cb16783cb5580999ee1d7b7024272`
at clean focused draft `8a99bcc0e353a136b2b84595bb27aa1bfe19e16c`.
The accepted scope is the citation repair in
`papers/AutomatedReviews/2026-08-15-d8-stage10-redraft/D8.md` finding 1.5.
The exact original Verify exited 0 from that checkout and checks file custody.
First and final continuity receipts are byte-identical and fresh.

## Source correspondence

- The held Ross–Selinger arXiv:1403.2975v3 gives the grid and residual
  enumeration in Algorithm 7.6, models primality in Hypothesis 8.3, and
  estimates the expected excess over the second-optimal T-count in
  Proposition 8.8. Proposition 8.11 is the expected runtime claim.
  The candidate preserves the separate bounded residual premise used by
  Lean's `gridFindT_isSome_of_residual` and
  `rossSelinger_synth_of_residual`. Its claimed bound is on word length.
- Ross–Selinger Lemma 4.4 is the product-of-interval-widths grid criterion,
  matching `oneDim_grid_exists_product`. Appendix C.2 verifies the
  unit-square reduction. C.15–C.17 distinguish a unit-factor norm equation,
  the dyadic solvability criterion and denominator clearing. The integral
  definitions and `relNorm_iff_doublyPositive_decomposable` use
  nonnegative embeddings and a unit factor, including zero. C.19 is the
  coprime step. The corrected C.20 block separately matches the prime
  gcd construction and the explicit odd positive-p norm obstruction.
  The corrected C.21 block matches `daggerDecomposable_pow_iff_seven`,
  including positivity of p. C.23 assumes a supplied prime factorization.
- Kliuchnikov–Maslov–Mosca arXiv:1206.5236v4 Theorem 1, Algorithm 1 and
  Corollary 1 support the stated exact one-qubit synthesis characterization,
  procedure and length bound. The registry distinguishes this exact-synthesis
  source from the separately cited two-ancilla result.
- Mukhopadhyay arXiv:2401.08950v1 Theorem 3.8, Fact 3.9 and Lemma 3.16
  support the channel-row, signed-permutation and at-most-one exponent
  increment claims. Lemma 3.10 and Definition 3.13/Fact 3.14 support the
  dyadic entries and exponent rule. Conjecture 4.8 concerns the heuristic's
  intermediate-set size and survival of an optimal decomposition. The
  manuscript retains the exact-implementability premise of
  `channelSde2_le_toffoliCost` and leaves optimal cost open.

## Exact scope and visual replay

I applied the patch independently to the three HEAD files in scratch.
The resulting bytes match the author's three candidate files. AST and
JSON comparison show exactly three changed registry and sidecar entries,
plus the sidecar generation timestamp. Every PDF path resolves to the
source bytes with the stated edition stamp, size and hash. All nine cache
headers carry the explicit project-authored label by line 11. The first
scratch control used an arbitrary 400-character cutoff and missed a
valid header. Rechecking the actual header lines passed for all nine.
The manuscript retains 19 distinct citation keys, 56 labels and four
figure links. Only the C.20 and C.21 labelled formal blocks change.

A clean scratch latexmk replay produced 13 pages, as did baseline.
No unresolved citations or references remain in the final log.
The pre-existing four overfull widths and stuck-float warning recur.
I visually inspected pages 1 and 7–11. The amended introduction,
resource theory, exact-synthesis/grid section, Appendix C statements,
and outside-scope paragraph are legible and resolve their citations
and references. The split C.20 statement flows across pages 9–10.

This accepts finding 1.5 source and render propagation. Broader D8
acceptance, Stage 13 remeasurement and canonical closure belong to ROOT.
