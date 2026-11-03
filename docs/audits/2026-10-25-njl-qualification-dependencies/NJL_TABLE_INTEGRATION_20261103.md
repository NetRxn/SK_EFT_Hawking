# NJL table integration checkpoint

Merge `f82c28b0` matches the reviewed table candidate `3d724b43` byte for byte at the Git tree level. The target checkout's pre-existing untracked test stub was preserved. The D1 compile receipt records 20 pages, matching both independently compiled PDFs.

| Scope | Pinned commit | Independent readback |
| --- | --- | --- |
| Five D1/D4/D6/D9 tables | `b3292f77` | 67 rows and manuscript table wrappers preserved, five regenerated outputs matched, all four baseline and candidate table placements matched |
| D9 exact and bounded results | `af80375b` | Ten rows, separator after row eight, caption describes eight equalities and two bounds. All 93 existing renderer outputs byte-identical |
| D6 count comparison | `3d724b43` | Five displayed rows match the prior table. AGP v3 §8.3 matrix and corrected count arithmetic independently reproduced. Both generated D6 tables and PDF placements verified |

The scoped independent review reports have SHA-256 digests `513afecaaa0bd200366bb6eb5f429762be3ee727e267ccd3e863ed4896587e2e`, `9493779881de0b738b47c1d8de8cf4e78aae736259773f320ebea0d2eb1ebee0`, and `d24a48f984132a8ed5cc8230d7a0356a467a050fe09968e355b3e7030b811729` respectively.

The existing table tests passed 5/5 on the candidate. The live table count fell from eight to one against the unchanged ceiling of one. D10 inhabitance remains the sole handwritten table. The canonical inline-numerical check fell from 141 to 136 against 117. D1 accounts for 32 remaining hits, including five BEC floor values backed by the existing benchmark evaluator. The full configured fast suite was started on `3d724b43`; its outcome is pending.

Inherited layout issues include D1's table and bibliography overlap, clipped D4 rows and D9 text extending past the right rule. The reviews cover these table changes. Whole-candidate qualification, the remaining finding and module-reach checks, and publication acceptance remain open.
