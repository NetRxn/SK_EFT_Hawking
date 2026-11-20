# D1 hierarchy table migration

Reuse the existing table renderer and the registered benchmark evaluators.
The BEC formatting remains shared with the existing CLI. The polariton rows
use the as-built cavity decay ratio and the registered smooth and steep
gradients. The Dean row uses the existing graphene evaluator. These
are model comparisons; the adopted dispersive law and physical calibration
remain separate obligations. At fixed gradient and viscous ratio, changing
the model mean free path from 50.92 to 100 nm reverses the net shift.

The existing D1 verifier must inspect the table actually included immediately
after the hierarchy label. It must reject a missing or substituted include
and still detect a wrong BEC cell in the generated artifact. Its crossover
assertion and tolerances remain. Keep the existing inline test fixtures for
historical comparison. The complete migration awaits qualification and
independent review.

The bound generated artifact must also equal the canonical renderer output
byte for byte. This covers the non-BEC cells without a second formula source.
Route source changes to this same check; keep the BEC tolerances and crossover
comparison independent of the generated-byte check.

The [focused independent readback](D1_HIERARCHY_TABLE_READBACK.md) accepts the
corrected migration. The actual generated Dean and BEC cell mutations and the
substituted include are rejected and restored. The post-census focused suite
passed 77 tests, and the final D1 PDF compiled to 20 pages. The generated
table removed one handwritten tabular and six manuscript literal hits:
14 remain against the table ceiling of 1, and 143 against the numerical
ceiling of 117. The sentence gate remains at four. The earlier broad suite
predates this change.
