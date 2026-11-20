# Independent Task1 exact algebra/error review R1

**Verdict: REVISE.** The bounded suite passes, but four concrete API correctness defects require repair before Task1 implementation intake. All findings are P2, lane pyrust, owned by the implementation author through ROOT's existing remediation route. This report grants no scientific execution, physical certificate, formal bridge, full-tree, main or publication acceptance.

Reviewed all 657 lines of `src/vestigial/original_coefficients.py`, all 382 test lines and all 165 appended canonical formula lines in PRIMARY at baseline `056ccb9f08454238934977de4bb6548d18c6275e`. The original 500606-byte formulas prefix is byte-identical to that baseline; its SHA256 is `7a1fff54dcdcd0d52ade2ef1cab136d66f2f1697b67bec8b278007d3a857a990`. Read the entire assigned ROOT notebook, accepted R2 construction/structured fields, prospective physics/cost reviews, actual author report, source provenance and red/green/storage receipts. Authority and wave-pipeline guidance preserve independent scientific review and broader gates; nothing here waives them.

## ALG-1: last potentially nonzero degree is reported vanishing

- **Severity:** P2
- **Lane:** pyrust
- **Path:** `src/vestigial/original_coefficients.py:532`; mirrored by `tests/test_original_coefficients.py:195`.

`degree_bound` is the largest potentially nonzero centered power: 8 on N16 and 4 on a one-site carrier. R2 expressly says monomials of total degree **greater than 8** vanish. `vanishes_above(degree)` currently returns `degree >= degree_bound`. A caller asking whether the boundary coefficient vanishes receives True, which can remove the top allowed term. The existing assertion repeats that error instead of testing a nonzero boundary.

Minimal exact counterexample, derived directly from the source; not separately executed under this review's only-29-test allocation:

```python
reg = OriginalRegulator((1, 1, 1, 1))
e = ExteriorPolynomial.generator
frames = [e(0)*e(2), e(1)*e(3), e(4)*e(6), e(5)*e(7)]
cert = local_degree_certificate(reg, (0, 0, 0, 0), frames)
# All four factors are centered homogeneous bilinears, each with two center generators.
# cert.degree_bound == 4, and their product has mask255 with coefficient+1.
# Current cert.vanishes_above(4) == True nevertheless.
```

Use a strict comparison for tested-degree semantics, or rename/document the method if it asks a different question; callers/tests must unambiguously retain the boundary degree. Add independent nonzero degree4 and zero degree5 controls and check N16 boundary8/9. `production_authorized=False` prevents this from being a current local8 production claim, but does not make a false public certificate safe to accept.

## ALG-2: a sparse matrix represents different coefficients through different accessors

- **Severity:** P2
- **Lane:** pyrust
- **Path:** `src/vestigial/original_coefficients.py:440-455`.

`SparseMatrix` does not validate, collect or freeze its entries. `at()` constructs a dictionary and keeps only the last duplicate; `to_exterior()` sums every occurrence. Thus the same accepted object has two different mathematical meanings. A caller-owned entries list also remains mutable through the frozen wrapper, unlike the repaired regulator.

Minimal source-derived counterexamples, not separately executed:

```python
reg = OriginalRegulator((1, 1, 1, 1))
m = SparseMatrix(4, (((0, 0), Polynomial.scalar(1)),
                     ((0, 0), Polynomial.scalar(2))))
# m.at(0, 0) is scalar2.
# dict(m.to_exterior(reg).terms)[5] is scalar3 (bar0 at position0, psi0 at position2).
entries = [((0, 0), Polynomial.scalar(1))]
m = SparseMatrix(4, entries)
entries.clear()
# m has now changed even though its dataclass is frozen.
```

Normalize by addition and remove exact zeros, or reject duplicate entries consistently. Validate nonnegative integer size, in-range scalar coordinates and coefficient domain; copy to immutable normalized tuples. Add accessor/exterior consistency and caller-mutation tests. `Symbol.index` and other accepted frozen records should likewise copy or reject mutable label/container inputs; the present `Symbol` constructor accepts a list that can subsequently change and cannot serve as a hashed polynomial key. Do not claim blanket deep immutability from `frozen=True` alone.

## ALG-3: ragged dense matrices silently lose entries

- **Severity:** P2
- **Lane:** pyrust
- **Path:** `src/vestigial/original_coefficients.py:218-226`.

Multiplication checks A's row lengths against B's row count but never checks B's row widths. Output width is taken only from B[0]. Dagger similarly uses only the first row width. A longer later row is silently truncated rather than rejected. These helpers feed supplied links into the original coframe/action, so malformed inputs can yield plausible incomplete results.

Minimal source-derived counterexample, not separately executed:

```python
b = ((1,), (2, 3))
matrix_multiply(((1, 1),), b)   # current result ((Polynomial.scalar(3),),), dropping3
matrix_dagger(b)               # current result ((Polynomial.scalar(1), Polynomial.scalar(2)),), dropping3
```

Validate complete rectangular shape before multiply/dagger, with intentional empty-matrix behavior and ValueError for ragged inputs. Check the original supplied-link boundary is genuinely4x4 so larger valid rectangular matrices cannot be mistaken for Spin4 matrices. Add adverse tests; equal-shape matrix_add alone does not establish rectangularity.

## ALG-4: real quaternion API silently accepts complex coordinates

- **Severity:** P2
- **Lane:** pyrust
- **Path:** `src/core/formulas.py:13059-13066`.

The canonical helper explicitly promises exact real polynomial or rational coordinates, and subsequent conjugation treats q coordinates as real. Only vector length is validated. `Polynomial.coerce` accepts arbitrary QComplex values and complex source symbols. For example `original_spin4_link((QComplex(0,1),0,0,0),(1,0,0,0))` returns diag(i,i,1,1), whose purported left SU2 block has determinant -1. `Polynomial.variable(Symbol('J', (0,)))` is likewise accepted as a quaternion coordinate even though dagger correctly treats J as complex elsewhere. A bad real-domain input silently becomes a different group/coordinate model.

Reject inputs not real under the polynomial involution, or introduce an explicitly distinct complexified constructor with separate domain metadata. Test a nonzero imaginary exact scalar and a complex J polynomial, while retaining rational real q/h and legitimate self-conjugate polynomials. This request does not impose a new symbolic sphere reduction or normalize arbitrary supplied rational vectors: it enforces the API's existing real-domain boundary.

## Valid-path findings and cost/test assessment

QComplex stores reduced Fraction numerator/denominator pairs with positive denominators; arithmetic is exact and float/built-in complex conversion is refused. Polynomial construction collects repeated sorted monomials, removes exact zeros and freezes supported coefficient terms. Conjugation correctly distinguishes real q/h from complex J on valid labels. Exterior multiplication uses inversion parity, rejects overlapping masks and preserves exact cancellations; the independently supplied permutation matrix tests the Berezin output orientation rather than just reproducing the action builder.

The coframe tests contain a hand-derived quaternion entry, additive coincident-neighbor controls, distinct L2 anchors, L1/L2/boundary coverage and a dropped-quarter adverse test. Gamma Clifford/chirality, noncommuting printed/closed words, independent determinant definition for S4, unsquared g2, explicit C3 coefficient, dictionary epsilon signs and separate cut metadata are meaningful. Some dense accumulation tests mirror supplied increments, but the other controls supply independent oracles. The four defects above expose missing adverse coverage despite those valid controls.

ScalarCost charges each expanded polynomial coefficient product, including sign/scalar multiplications; it does not price a whole polynomial or future jet as one scalar slot. Nested scope tests intentionally use their own counters, so outer teardown counts are not aggregate CPU work for nested scopes. The actual fixtures stay far below the allocation. Resource statements here are bounded test observations, not a process-wide allocator/watchdog or universal budget on arbitrary extents/inputs. `determinant_support` can grow exponentially on larger carriers and needs future admission before such execution.

`recursive_size_bytes` deduplicates the supported tuple/list/set/dict/dataclass object graph by identity and counts QComplex's four-int payload. The author9,131,398-byte symbolic Dirac fixture and848.952-byte dummy scalar record receipts concern those supplied graphs. They do not include arbitrary opaque object referents, allocator slack, simultaneous future resize maps or process RSS; no future W/jet/Haar fit is certified. Future six-slot jets must account for six scalar slots and all convolution terms.

## Independent verification and continuity

Executed in PRIMARY with existing `.venv`, single-thread numerical-library environment, `PYTHONDONTWRITEBYTECODE=1`, no cacheprovider and captured subprocess return code:

```text
.venv/bin/python -m pytest tests/test_original_coefficients.py tests/test_dependency_declaration.py -q -rP -p no:cacheprovider
pytest returncode=0; 29 passed in 8.57s; stderr empty
maximum reported expanded scalar products/test=70016
```

The24 Task1 plus5 dependency tests pass; no new adverse snippet, broad pytest/validator/extractor, scientific coefficient/W/Haar program or full partition computation ran. Source imports resolve to PRIMARY's actual two modules, not the task's different current working tree. Author fixture graph bytes were inspected, not independently remeasured as RSS.

First explicit checker invocation and final SAME packet check both returned exit0, fresh=true, changed=[]. Procedural limitation: I read the packet and notebook before running the explicit initial checker; it still ran before bounded tests. All bound reference hashes match. Frozen source hashes remain:

```text
src/core/formulas.py                         0293e17b4b0c73aa2e39d8741bb631acea1f30a45bf87ede9cde6375cdcd696d
src/vestigial/original_coefficients.py        dbda2b494204116771f44ffca72757b14f79a44ddb0dc22faf7ab1ce020323dd
tests/test_original_coefficients.py           d50977905e85a9143d60a09291b766186f3b4282d3aba1e34be0a8f2c348794f
```

Early broad combined document reads truncated; complete source/test/formula reads and narrower scientific/spec/receipt reads supplied the review findings. No conclusion is based on an omitted excerpt. Only the two assigned `/tmp` report files were written; no source, Git, Lean, MCP/controller, build, dependency, registry, roadmap or notebook edits were made. A lightweight memory-registry query found no relevant entry and supplied no evidence.

## Remaining original requirements

Task2 still owes exact family-graded raw jets/minors/Hermite W/Gaussian/Haar/refusal APIs and separately admitted COMPLETE original one-site direct-vs-W4 computation:3876 quartics/740 support-compatible slots,4029 raw W terms/23504 queries, both words, variances2/3, complete interacting denominator and T/H/frame contacts. Task3 still owes all36-entry direct/minor invariant tensors, the full24-minor roster/projectors, F60/G52/contact/exclusion/anchor/chirality execution under separate70M allocation. Task4 still owes complete split-factor denominator/source frontier, viable independently accepted full allocation, actual full coefficients and certified nonzero normalization.

`metric_M` remains Euclidean M_N, not Executor's Lorentz L_P label. source_C's uncut polynomial with cut0 is not its cut3 physical source/reflection/kernel datum. Entrywise gamma agreement after S does not authorize physical certificate cross-consumption; that remains withheld pending Executor's actual P0/C3/N0 map. No new Lean bridge is invented. Local8 formal/production admission, physical source/projector/calibration/state/adjoint/domain, B3 normalization/window, modes/matter/transport/limits, independent scientific review, full-tree/native/main/publication gates all remain owed. ROOT owns reconciliation, fixes dispatch, broader gates and canonical closure.
