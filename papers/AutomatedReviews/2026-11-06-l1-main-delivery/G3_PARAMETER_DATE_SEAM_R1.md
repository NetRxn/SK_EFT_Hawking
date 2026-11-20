# Parameter graph dates for G3

On exact draft PR117 parent `260a75597`, all 20 declared L1
parameter dependencies were reported as missing human verification dates.
The registry actually stores dates for 13 entries. The Parameter extractor
emitted only the legacy verification booleans while the G3 evaluator read
`meta.human_verified_date`. The link-state helper and last-modified
annotation also consume date fields.

The existing Parameter node producer now copies both verification dates
from the registry and retains the existing booleans. The regression feeds
real produced nodes to the gate and link-state helper. Before the producer
change, it wrongly blocked both the dated and pending records. After
the change, only the pending record blocks and both link classifications
match their source dates. The graph rules, registry and human attestations
were not edited. Existing dates are historical registry data, including the
April 2026 categorization sweep. This delivery does not record any new
operator attestation.

The exact paired production extraction retains all 704 paper-level gate
states and all 231 bundle states. Seven G3 detail sets change. L1 changes
from 20 missing dates to seven. Its two comparison-window endpoints,
fiducial susceptibility, frequency probe, transport placeholder, and both
ADW range endpoints still lack dates. G3 remains blocked, and the separate
G11 finding for operator attestation remains open. The full graph retains
all 19,076 edge identities and adds only the regression test node. All
211 Parameter nodes retain their original booleans and carry source-exact
dates. No live dashboard or publication acceptance follows.

The author suite passed 196 tests, with one skip and 15 deselected.
Paired canonical parameter-provenance, graph-integrity, edge-type and
readiness-agreement checks passed. The architecture-inventory control
initially found the same missing installed hook on each scratch tree.
Both pass after pointing at the actual installed hook directory.

Independent review accepted the exact patch after reproducing the red and
green regression, all seven G3 detail changes, and the unchanged registry.
Its core suite passed 144 tests. A cold-cache control reproduced two
failures on both revisions with bytecode disabled. All nine dashboard cache
tests passed in the warmed candidate checkout with normal bytecode settings.
The [evidence archive](G3_PARAMETER_DATE_SEAM_R1_EVIDENCE.zip) retains the
independent review, captured failures, hashes, and exact candidate patch.
