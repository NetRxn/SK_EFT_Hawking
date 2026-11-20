# Independent original Eq11 signed complementary minor review R1

**ACCEPT the exact original Berezin signed complementary-minor and
executable row-index bridge at source scope.** ROOT owns the independent
kernel replay, aggregate import, native build and delivery.

Commit `cc7c1f2ff4190c70364922fb7d2c768d942d22bd` has sole parent
`7b71522c766f846c188edc0b5e0fbc3a3c7b6ada`. It adds only
`lean/SKEFTHawking/ADW/FiniteGrassmannComplementaryMinor.lean` (423
lines). The exact Git blob SHA-256 is
`e644bf91f57a96f589af4686d94b6b2d24100549b2c2f4a50213d18f4a142a35`.
The whitespace check passed. The only import is the accepted original
Dirac/Berezin module. The new file introduces no new measure,
normalization, axiom, unsafe declaration or admitted proof.

## Eight exact public statements

| Statement | Independent semantic check |
|---|---|
| `nilExp_barMpsi_rows` | At exactly 4V rows, all row factors square to zero and commute in the original even bilinear subalgebra. The finite exponential factors into (1+row) over every row. Inclusion of the sum is the actual barred-matrix-unbarred word. |
| `berezin_insert_rows` | The selected unit rows carry the exact ordered barred/unbarred pairs. In a selected row the inserted and original factors have the same barred generator and their product vanishes, leaving the inserted row alone. Over complementary rows the product expands over all subsets. A strict subset has exterior grade below 8V, hence zero original top coefficient. The full term is exactly the original normalized row determinant of the replaced matrix. Repeated selected columns are permitted at this layer and give identical unit rows and a zero determinant. |
| `det_of_unit_row` | Laplace expansion at the given row isolates the unit entry and deletes precisely its row and column, with sign (-1)^(r+c) in zero-based coordinates. |
| `det_of_ordered_unit_rows` | The ascending selected row/column orders pair corresponding indices. Delete the smallest selected pair and transport all later selected and complementary entries through the strictly increasing deletion embeddings. Each later selected row and column drops by one, so the exponent difference is 2 per remaining pair. The complementary enumeration is exhaustive by strict monotonicity, disjointness and total cardinality. This includes k=0 and the empty complement. |
| `berezin_grouped_insert_rows` | Moving each unbarred generator past all subsequent barred generators gives exactly choose(k,2) odd swaps. The pair product can be taken in list order because it lies in the even subalgebra, and the paired product and grouped product differ by a self-inverse sign. No alternating permutation of arbitrary even factors is inserted. |
| `berezin_ordered_complementary_minor` | The chosen increasing lists give exactly all barred insertions followed by all unbarred insertions. The same Fermion equivalence reindexes both axes, preserving the existing determinant and literal Berezin normalization. Combining row deletion and regrouping gives (-1)^(k(k-1)/2 + sum rows + sum columns), with no premise relating the selected row and column sets. The determinant is the untouched complementary submatrix. |
| `executableFermionIndex_val` | The coordinate digits are the canonical values in ZMod for the positive extents. The nested product equivalences use the right extent as the radix multiplier, then append the spin digit in radix four. The expression agrees with the pinned Python `site_number` fold and `assemble_coframe` row and column offsets. |
| `theta_word_repeat_zero` | Find two occurrences of the same generator. Move one through the intervening prefix with the proved odd-swap sign. The adjacent square vanishes before Berezin evaluation. The recursively repeated tail case also vanishes. |

The fixed top coefficient is still the original exterior basis
coefficient in the literal source orientation. The earlier
`rowBerezin_normalization` computes its value as one on the diagonal
paired source, independently of M. Applying the same arbitrary
equivalence to barred rows and unbarred columns contributes cancelling
permutation signs, rather than replacing the exterior basis. No matrix
invertibility, determinant nonzero, reality or positivity is assumed.
The zero-size *minor* is included; the original positive-extent Torus
itself has positive volume.

## Exact control receipts

At clean primary 7b71522c I reran the frozen rational-complex exterior
row-product oracle against the actual Python `complementary_insertion`.
The result was byte-identical to the frozen receipt. It checks all
equal-cardinality deletion subsets of four dense, rank-deficient, zero
and off-diagonal matrix families at dimensions zero through four.
The counts at k=0,1,2,3,4 are 20, 120, 184, 68 and 4, totaling 396.
All four adverse selector probes were rejected, covering repeats,
unsorted selectors, unequal sizes and out-of-range indices. The
oracle explicitly wedges ordered exterior factors and normalizes by
the diagonal pair orientation. It does not use the implementation's
determinant or deletion sign to derive expected values.

The adjacent supplemental control computes signs by direct inversion
count on the original grouped insertion followed by the complementary
paired word, normalized by the diagonal paired orientation. It also
checks the mixed-radix expression against Python's actual site
enumeration and index method on 81 positive extent tuples. Python's
public helper expects sorted distinct selectors and rejects malformed
input. The repeated exterior word theorem supplies the distinct
algebraic zero fact for words upstream of that helper.

The signed theorem now establishes the original mathematical minor
and the indexing/sign convention correspondence. Formal equivalence
to the Python determinant evaluator, actual assembled matrix and
coefficient pipeline, measure/jet implementation, exact saved N16
lattice coefficients and full numerical Z remain distinct obligations.
Neither these bounded coefficient controls nor this source review
certify connected normalization, physical response, publication
acceptance or any compiled result.

First and final continuity returned SAME and are byte-identical. The
review made no repository or slot changes and ran no Lean or build.
