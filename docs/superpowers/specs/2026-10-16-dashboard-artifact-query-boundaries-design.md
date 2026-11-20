# Dashboard artifact and read-query boundaries — proposed design

Status: selected mechanism after independent R6 review and bounded disposable
database controls. Owner-first implementation is allocated in the isolated
checkout. Full implementation/provisioning acceptance remains unverified.
This document does not certify a deployed or accepted control. The existing
`docs/architecture/DASHBOARD.md` remains the surface owner and must state the
reviewed mechanism before source implementation. No new checker, ADR, cache,
metadata writer, session mechanism or closure path is proposed.

## Purpose and measured baseline

The dashboard must read the intended paper artifacts and retain its supported
free-form read-only Cypher console. At base `db72be9d79eb8729eb95d481ddea05e6261fdeb4`,
`_safe_paper_dir` confines a resolved selected directory beneath resolved `papers/`,
but consumers append fixed artifact paths afterward. `api_cypher` applies current
verb/stacking/comment/length guards and delimiter exclusion, then executes using
its configured credential and fetches all rows. It has no explicit read-only
transaction, timeout or result bound. Its parameter-binding/accepted-triage
comments do not establish those guarantees. The source observations are filed in
`papers/AutomatedReviews/2026-10-16-dashboard-consumer-boundaries/infra.md`.

Neither source observation proves an input-only traversal, SQL breakout or write
exploit. Existing proxy session-value checks and fixed-relative redirect encoding
are material and remain unchanged. Existing exact-head aggregate CodeQL failure
is not waived by this design.

### Bounded pilot observations — 2026-10-16

The baseline dummy-paper experiment exercised eight actual dashboard/graph readers;
each followed a child symlink outside the temporary papers root. Database connection
attempts were refused and none occurred. This establishes the child-path defect in
those consumers, not complete family coverage or an implemented repair.

Disposable cached-image experiments observed PostgreSQL17.7, AGE1.6.0 and loaded
psycopg3.3.3. Both ordinary `sql.Literal(query)` and source server binding failed
with SQLSTATE42601, requiring a dollar-quoted string constant, on the sampled
queries. The existing delimiter-checked dollar-literal form executed the sampled
scalar/null/graph/quote/backslash/dollar-tag/Unicode/line-comment reads. The driver
literal is therefore an unsuccessful candidate on this measured stack. This is
not a universal claim about other versions, binding mechanisms or query APIs.

A fresh restricted login could not directly LOAD AGE. The first two servers
already globally preloaded AGE, and their restricted reads succeeded before
per-role configuration. A separate control disabled global preloading and
observed empty effective preload settings and no initial role setting. Its fresh
no-LOAD restricted read failed; after administrator-configured per-role
`session_preload_libraries='age'`, a subsequent fresh restricted login read the
dummy graph in a read-only transaction. This demonstrates that per-role route
on the measured stack without granting privileged membership. The combined
restricted-role/read-only-transaction candidate read the fixture; independent
table, graph-create and sequence probes were denied by role privileges, and
separate healthy transaction probes refused UPDATE with SQLSTATE25006. The
observer's committed positive control was visible and the permanent sentinel
remained unchanged afterward. SQL outer-cap observations distinguished
0/999/1000/1001 rows; a statement timeout produced57014 and a subsequent fresh
transaction read succeeded. These are database observations, not HTTP outcomes.

All exact temporary containers were removed. Raw failed and successful sequences
remain in the primary checkout's ignored continuity evidence, alongside ROOT's
bounded reconciliation. The first experiment's driver-literal bootstrap/read
failures are retained; its transaction-only write after an aborted read supplies
no refusal evidence. The corrected second experiment provides the healthy
transaction comparisons. No production graph or shared volume was used.

The focused control timed out an expensive small-result AGE query with57014,
and a separate held fixture-table lock made an actual AGE read fail with55P03.
A fresh connection subsequently read the graph successfully. After populating
the same backend's graph cache, `delete_global_graphs` returned true then false;
repopulation followed by its null/all-cache form also returned true then false.
The table/graph data and permanent sentinel remained unchanged. This is an
allowed backend-local cache effect, not an enforced refusal or a claim of pure
function execution.

An allowed-looking qualified Cypher expression invoked the installed edge file
loader under the restricted role and under a read-only transaction. Existing
header-only dummy CSV access succeeded; missing dummy files reached the file-open
error. Correct explicit SQL-text unboxing before name casts was necessary to
reach the intended graph/label. The vertex loader instead failed at temporary
table creation. These observations establish a file-access boundary gap for the
measured edge loader, not arbitrary secret disclosure or an HTTP exploit.

Revoking EXECUTE from PUBLIC on the exact ten named function signatures below,
then granting the separate writer, made all eight loader SQL/Cypher
existing/missing-file cases and six qualified mutation cases fail42501 at the
function boundary. Effective ACLs showed query-role false/writer true for all ten
signatures. Both writer loader controls succeeded with explicit writer-only TEMP.
Trusted-owner create/drop/rename/create-label/drop-label controls executed their
actual effects and committed. Before EXECUTE revocation, restricted drop_label
returned an internal XX000 error; that error supplies no privilege-enforcement
evidence. The graph generators were ACL-inspected but not invoked.

Defaults configured for the actual fixture label creator gave two subsequently
created vertex/edge tables SELECT but no DML for the query role; actual table
existence, owner and privileges were inspected. This covers that creator and those
objects, not every future creator. Ordinary graph reads remained available. An
actual population of2000 produced1001 rows under the SQL sentinel cap. Connections
closed and aborted transactions rolled back in the observed disposable driver
paths; actual application HTTP cleanup, overflow/error/default/browser behavior,
negative configuration and full artifact-consumer cases remain owed.

These observations support the proposed combined policy on the measured immutable
image. Its mapping to the inspected upstream source revision remains UNKNOWN.
No production credential, deployed control or scanner disposition is established.

A further qualified AGE call changed the effective lock timeout to zero. With
explicit SQL-typed numeric arguments, a held advisory-lock control changed from
55P03 after about one second to statement cancellation57014 after about five
seconds when the setter preceded the lock call. Both the baseline sleep and the
same-expression attempt to set statement_timeout to zero still cancelled at about
five seconds. This measures the tested expressions; it does not establish a
universal current-statement timer property. Earlier duplicate-extension bootstrap
and untyped numeric-function failures are preserved as failed controls.
PUBLIC EXECUTE denial on `pg_catalog.set_config(text,text,boolean)` blocked both
the qualified AGE expression and direct SQL with42501. Trusted constant SQL
SET LOCAL and a fresh ordinary graph read remained available. All temporary
containers were removed. Writer compatibility and the final combined policy's
timeout/lock tests remain implementation/provisioning obligations.

## Proposed requirements

### A1 — Carry the existing containment root to final artifacts

Every paper-id-derived artifact read in the paper-artifact family must validate a
final resolved target confined
to resolved `papers/`. Preserve the existing paper-id validation and selected
paper-directory containment. Apply final containment to claims review, nested
figure review, prose state, audit log and TeX, including their v1/v2 consumers.
Inspect all existing helper callers and related reads before claiming coverage.
Include the Paper Claims collector, paper lists/title/abstract paths and graph
rebuild ingestion of the same TeX/claims/prose/audit family. Static source registries,
Lean metadata and unrelated repository inputs remain governed by their own owners.
There is no separately trusted unconfined ingestion exception for this family.
Promote the existing containment mechanism into one shared reader/path boundary
used by dashboard and graph ingestion, rather than maintain parallel validators.
Review `scripts/build_graph.py` and `docs/KNOWLEDGE_GRAPH.md` as additional owners
before code. A new shared Python module may be needed to promote the existing
helper; do not add a second guard or maintain a hand-curated consumer registry.
Preserve lexical paper identity and existing metadata when an allowed in-root
symlink resolves to another paper; returning a resolved TeX parent must not
silently rename the paper or merge two identities.

The proposed root remains `papers/`, matching the existing guard. A stable symlink
to another artifact within that root stays permitted. A file or intermediate
figure-directory symlink resolving outside it is refused with the existing
missing/empty response for that reader. No outside content may be parsed first.
Preserve malformed/missing-artifact behavior, sole writers and event order.

The family includes paper-derived reads delegated by dashboard actions to the
existing sentence-state writer: claims/prose prerequisites of `cmd_mark`, related
tombstone/reconcile state reads and audit replay. Its separately bound
`sentence_state.PAPERS_ROOT` participates in isolation. Apply the promoted guard
at read seams; do not globally replace lexical claims/prose/audit path helpers
with resolved targets, because those helpers also feed writes. Preserve locking,
validation, audit-first mutation, atomic prose replacement and replay. Refuse
unsafe prerequisite reads through controlled command errors before successful
ratification/audit outcomes; guard selected-directory escapes before creating
their lock path. Explicit CLI source-file arguments remain a distinct input
contract; do not confine an arbitrary supplied source file by basename alone.

This proposal assumes cooperative local artifact writers during one read. A
resolve-then-open check does not resist a malicious concurrent local retargeting
race. Do not claim descriptor/no-follow confinement. If source or pilot evidence
requires hostile local writers, return to specification review before choosing a
stronger filesystem mechanism; do not silently narrow supported file semantics.

### Q1 — Preserve the console while strengthening the existing boundary

Retain supported free-form read queries, existing verb/stacking/comment/length
refusals, single agtype-result shape, normal JSON output and generic error
handling. Do not replace the console with a fixed-operation API or a new query
language. A driver-composed SQL literal is a candidate for removing manual dollar
literal construction; server binding of the Cypher source and binding of Cypher
parameters are different claims. Verify the supported method against actual
psycopg and pinned AGE before selecting it. Correct comments to the mechanism
actually proved, without an accepted-triage assertion.

### Q2 — Demonstrate the database capability, not just the query text filter

The actual query execution must use an enforced read boundary. Evaluate an
explicit read-only transaction and a dedicated restricted credential against
`apache/age:release_PG17_1.6.0`. Setup/load/search-path statements must occur at the
appropriate transaction boundary. A setup or capability failure must not fall
back to an ordinary writable query.

A read-only transaction alone does not establish absence of every function side
effect or file read. The pilot must inspect role/schema/table/function privileges,
show ordinary AGE reads succeed and demonstrate refusal of relevant write-capable
paths, including an allowed-looking function expression where applicable. Select
the credential/configuration contract only from this evidence. Any required
production role/configuration operation remains a separate rollout action; tests
must not touch the running shared graph or its volume.

The proposed connection input is required `SK_EFT_DASHBOARD_READ_DSN`, distinct
from the mirror writer. A privileged provisioning step configures AGE session
preloading for that restricted login; the query route neither performs privileged
LOAD nor elevates or falls back. Provisioning grants CONNECT, schema USAGE and
SELECT on the intended graph's existing labels, with equivalent future-label
defaults for every actual label creator. It grants no database/schema CREATE,
TEMP, table DML, sequence mutation, ownership or privileged membership to the
query role. Production provisioning remains a separate rollout action.

The concrete creator declaration is administrator-provisioned role/database
`sk_eft.dashboard_label_creators`. It is a nonempty comma-separated set of simple
ASCII role names, without whitespace, duplicates or unknown roles. Admission
matches the effective value to the unique highest-precedence applicable catalog
entry: role-plus-database, role, then database. Include every current graph-table
and graph-schema owner and check combined global/schema defaults for the complete
declared set. A later creator needs reviewed provisioning; the declaration is not
evidence of future administrator intent.

Use the unique highest-precedence applicable `pg_db_role_setting` declaration of
`session_preload_libraries` to require configured AGE loading, followed by the
fixed trusted read on that same connection. Do not require privileged visibility
of protected preload GUCs or grant settings-reader membership. Missing, malformed,
ambiguous or denied catalog evidence still refuses; actual read-only and time
settings remain checked immediately before user execution.

The measured function policy removes PUBLIC EXECUTE and grants the writer on
these installed signatures:

- `load_edges_from_file(name,name,text,boolean)`
- `load_labels_from_file(name,name,text,boolean,boolean)`
- `create_graph(name)`, `drop_graph(name,boolean)`
- `alter_graph(name,cstring,name)`
- `create_vlabel(cstring,cstring)`, `create_elabel(cstring,cstring)`
- `drop_label(name,name,boolean)`
- `create_complete_graph(name,integer,name,name)`
- `age_create_barbell_graph(name,integer,integer,name,ag_catalog.agtype,name,ag_catalog.agtype)`

Also deny effective query-role EXECUTE on
`pg_catalog.set_config(text,text,boolean)`, removing PUBLIC inheritance and granting
only the separately reviewed trusted identities that require it. The query route
uses constant SQL SET LOCAL for its own setup. This proposed database-wide PUBLIC
change is provisioning, not an application mutation or a deployed policy.

Revoking only the query role does not remove PUBLIC inheritance. Effective
membership, ownership, existing/future label privileges and these exact function
ACLs are admission evidence; a role name or read-only default alone is not.
Each fresh query connection must verify this provisioned capability before any
user source. Require an explicit, nonempty dedicated endpoint/database/login DSN;
missing, malformed or ambiguous defaults fail without connecting to a fallback.
Enter explicit READ ONLY, set trusted local limits/search path and inspect current
authority using static schema-qualified catalog SQL. Verify the selected identity
and database, no privileged attributes or memberships, no ownership/CREATE/TEMP/
table mutation or sequence mutation authority, intended graph/schema USAGE and
current label SELECT. Include effective PUBLIC grants and unrelated writable user
objects, not just the sampled fixture labels.

Resolve every required forbidden function signature to an actual OID with the
expected argument/result/security identity and effective EXECUTE=false. Missing
objects, nulls, omitted/truncated rows, executable extra overloads of protected
names, unreviewed executable definers or relevant server-file/program capabilities
fail admission. Inspect current label owners and combined global/schema defaults
for the provisioned creator set; a new creator requires reviewed provisioning.
This checks existing objects and defaults, not every future administrator intent.
Verify inspectable initialization configuration, execute a fixed tiny trusted AGE
read without LOAD, and confirm the actual read-only transaction and5s/1s settings
immediately before user execution. Demonstrate the catalog predicates under the
restricted fixture; never grant privileged membership merely for introspection.

Missing, unsafe, denied or unknown admission evidence returns generic503 before
user execution, with rollback/close. No privilege repair, writer credential,
fallback or cached-ready bit belongs in the route. Recheck every fresh connection.
Provisioning and concurrent privileged database changes remain trusted operational
responsibilities; this is not atomic confinement against a hostile administrator.
Negative fixtures must exercise the production admission seam, prove the user
query sentinel was never run, check cleanup and recover on a fresh safe request.
Include role/PUBLIC grants, ownership, protected-function regrant or missing/extra
signature, executable definer, missing preload, global-default DML hidden by local
SELECT and a newly created label. Missing/malformed DSNs make zero connections.

The finite inspected AGE inventory and ten-signature policy do not establish an
absence of every callable effect. Preserve the measured backend-cache effect and
the statement/lock/row residual limits; assess relevant remaining reachable
effects without claiming source-to-image attestation or changing the console API.

### Q3 — Bound execution and responses explicitly

Proposed starting limits are a five-second statement timeout, one-second lock
wait and a response ceiling of one thousand rows. These are initial pilot values,
not measured performance claims. Verify ordinary supported read queries and
failure cleanup before settling them. Configure database-local transaction bounds
and fetch only a bounded result; an SQL outer limit and client fetch limit do not
prove the AGE executor avoids all internal materialization, so retain the server
time bound. Refuse overflow clearly rather than silently presenting a truncated
result as complete. Preserve safe error messages and transaction cleanup.

## Pilot-readiness contract after independent review

### I1 — Isolate every verification path before imports or requests

For ordinary Python/test-client paths set the actual dashboard
`app.config['PG_SYNC_ENABLED'] = False` before rendering or graph reads, and set
`SK_EFT_GRAPH_SOURCE=json`. A process environment alone does not replace the app
configuration switch. Ordinary live-browser fixtures require both JSON source in
the child environment and `--no-pg-sync`. The existing no-PG-sync flag alone does
not prevent the CLI's PG-source startup query. Reuse and extend existing fixtures;
do not replace real routes or claim template-only coverage as a rendered journey.

Query pilots use an exclusive disposable connection. Assert the actual connection
identity before any query: unique database, expected container/endpoint, loopback
port distinct from the shared graph, actual user and role. Missing/malformed pilot
configuration aborts; never use the hardcoded shared DSN or a fallback. Test this
negative path. No production graph, shared volume or real-paper fixture is allowed.
Final focused/profile/template/browser and closure Verify invocations must retain
these isolation controls. A fixture that patches only sentence_state.PAPERS_ROOT
does not isolate dashboard.PROJECT_ROOT or build_graph.PROJECT_ROOT. The actual
imported readiness_gates.PAPERS_DIR is a separate root and must also be substituted
before any graph/evaluator request. Instrument paper-family file reads to reject
real-corpus access if a further independently bound root is discovered; record the
attempt as a failed isolation case rather than silently reading real artifacts.
Delegated writer-route experiments also substitute the actual imported
sentence_state.PAPERS_ROOT and verification-log fixture before any command or
lock creation. Use dummy state only and assert refused prerequisites do not
produce successful ratification or audit events.

### I2 — Ordered database/literal feasibility matrix

Record resolved image identity, PostgreSQL/AGE and loaded psycopg versions; the
lockfile's psycopg3.3.3 is not proof of the loaded driver. Bootstrap a unique
throwaway graph, label data and permanent sentinel table using an administrative
connection. Close that connection before untrusted-query experiments. No writer
credential may serve as the selected endpoint credential.

Run these candidates separately and retain exact successful/failed sequences:

- Control: fresh bootstrap identity, autocommit LOAD, explicit search_path, ordinary
  read, cleanup. It supplies compatibility outputs only, not capability acceptance.
- Transaction-only control: setup while idle/autocommit, explicit BEGIN READ ONLY,
  transaction-local statement/lock limits, read and write-capability observations,
  rollback/close. Administrative read success does not meet Q2.
- Role-only control: a fresh restricted login with no privileged memberships,
  ownership, superuser/role-create/database-create/replication/bypass-RLS attributes;
  exact LOAD-or-initialization/search_path sequence, ordinary transaction and the
  same read/write observations. Capture a LOAD refusal rather than granting the
  query identity elevation.
- Combined candidate: fresh restricted login, independently demonstrated supported
  initialization, explicit read-only transaction, local limits, actual query,
  rollback/commit and connection close. Record session_user/current_user,
  transaction_read_only and effective limits at the query execution point.

If direct LOAD is refused, investigate administrator-configured per-role session
preloading on the throwaway instance. If needed, separately measure a documented
container-level preload route. Record exact settings, privilege and restart scope;
do not assume either route works. The selected runtime contract must name the
successful initialization/provisioning sequence and dedicated connection input.
Proposed input is `SK_EFT_DASHBOARD_READ_DSN`, required for the query route: absence
or invalid capability would return a generic non-success without falling back to
the mirror writer. This remains proposed until the combined candidate proves both
ordinary reads and capability. Production provisioning/rollout is a separate act.

Capture effective role attributes/memberships, database CONNECT/CREATE/TEMP,
schema USAGE/CREATE, graph/label-table and sequence privileges/ownership, PUBLIC
inheritance, reachable function EXECUTE and SECURITY DEFINER/server-file/program
capabilities. Bootstrap only disposable privilege changes. Exercise database
capability independently of HTTP text filters, using both ordinary writes and an
installed AGE-callable allowed-looking function expression where one exists.
Observe the permanent sentinel from a separate administrative observer before and
after each attempt, and validate that observer with a harmless committed positive
control. Record actual command success/denial and transaction-local state. A write
that succeeds and is later rolled back is not an enforced refusal. Trusted identity
probes on the prevalidated disposable endpoint precede candidate/untrusted payloads;
I1 does not prohibit those necessary probes. Error text alone is insufficient. If no such expression is
reachable, record the installed-resolution evidence and actual attempted forms;
do not invent a supported call or claim all possible function effects excluded.

For each viable execution candidate compare original supported reads against:
(1) the route-equivalent driver SQL composition using `sql.Literal(query)` within a
constant `sql.SQL` template, and (2) server binding of the Cypher source as a
separate measured candidate. Test quotes, backslashes, dollar tags, Unicode and
allowed line comments plus ordinary MATCH/RETURN, scalar/null/graph values. Keep
the single agtype column. Cypher's third-argument parameter maps are a different
feature and are not added to the current API. No failure establishes a universal
binding-impossibility claim; select only a demonstrated mechanism.

### I3 — Measured artifact consumer matrix

Before a source pilot, derive a one-off consumer-to-case table from actual source;
store it as evidence, not a maintained reader registry. Include direct claims,
figure, prose and audit loaders; v1/v2 title and v1 abstract; Paper Claims collector;
paper/dropdown listings; JSON/SSE consumers; and graph discovery plus title/claim/
figure/claims-review/prose/audit ingestion of this artifact family, plus the
transitive readiness_gates.GraphIndex.paper_tex and actual evaluator consumers.
Include the sentence-state paper-derived read seams above, preserving lexical
write destinations and command ordering rather than reusing resolved read targets
for mutation.
Carry the readiness reader through the same promoted boundary; preserve None for
refused/unreadable text, empty string for a readable empty draft, and the existing
measured=False/UNMEASURED propagation. No new evaluator or gate is proposed. Confirm source
paths rather than assuming a safe direct helper confines an indirect graph build.

Substitute the actual dashboard/graph roots and readiness module PAPERS_DIR. Use dummy
contents and a read/parse sentinel outside the temporary papers root, prove the
old implementation reaches at least one forbidden child, and later prove the fix
refuses it before parsing. Cases cover ordinary files, selected-directory escapes,
final-file escapes, intermediate figures-directory escapes, in-root cross-paper
links, dangling/cyclic links and missing/malformed files. Preserve each reader's
None/empty/missing outcome and lexical identity; do not pass unsafe TeX onward to
a title or abstract parser. Ordinary cooperative atomic replacement must yield
safe behavior; no consistent multi-file snapshot or hostile race guarantee follows.

### I4 — Observable row/error/cleanup contract

For the proposed public row ceiling1000, expose at most1001 rows to bounded client
consumption using a server-visible cap. Zero through1000 rows retain the current
normal rows/count/ms/query response. Observing a1001st row returns HTTP400 with a
static overflow error and no partial normal rows/count. Pilot0/999/1000/1001;
fetching exactly1000 alone cannot establish completeness. Assert actual connection
closure on overflow and every early return.

Test expensive small-result queries, lock contention, timeout, initialization and
query failure, then successful fresh requests after each. Check transaction end/
rollback and close. Classify timeout/privilege/query/connectivity errors by actual
cause rather than broad exception inheritance, and keep details server-side.
Malformed JSON/nonmapping bodies/nonstring queries produce safe HTTP400 before a
DB connection. Missing or invalid selected query configuration/capability produces
generic HTTP503; no elevated or production fallback is allowed.

These starting limits bound measured database statement/lock wait and response row
count. They do not establish a bound on one agtype value, total JSON bytes,
internal AGE materialization, serialization time or whole-request duration. Retain
those residual limits explicitly; do not infer them from a row cap or timeout.

## Admission evidence before implementation acceptance

1. Use temporary paper roots with dummy contents only. Exercise actual production
   readers/routes: ordinary files, in-root symlinks, escaping final files,
   intermediate figure symlinks, missing/malformed inputs and all related TeX
   paths. Show the original implementation fails at least the escaping-child
   assertion, then the reviewed fix passes it. No real papers are mutated.
2. Reproduce SQL/query behavior in a disposable AGE instance at the declared image
   version, with unique container/database resources, no shared volumes and no
   production port or graph connection. Record actual server/extension/driver
   identity, chosen literal method, role/transaction behavior, ordinary results,
   negative cases, timeout, row ceiling and cleanup. A mock is not AGE evidence.
3. Extend established route/reader tests, retain template contracts and actual
   browser journeys using the existing no-PG-sync fixture. New source tests must
   observe the production seam and distinguish the old defective implementation.
4. Independently review the full implementation and owner changes. Run actual
   changed-scope gates and the existing closure writer. Integrate only through
   ROOT's normal Git process and re-run exact-head aggregate CodeQL, inspecting
   remaining annotations/dataflow. Analyzer-job success is not aggregate success.

No Lean slot, build/cache/pin change, runtime reload, main merge or publication
acceptance follows from a source pilot or passing unit tests. Preserve active
proof dependencies throughout isolated preparation.
