# Architecture inventory: Git-context hook catalog and schema ownership

Status: independent source review and current whole-evidence review accept the bounded NJL inventory source, corrected baseline and both authentic production controls. Documentary readback is accepted and the existing writer recorded the narrow infra finding fixed after its declared verification passed. Full delivery qualification, main integration and scientific/publication acceptance remain pending.

Reintegration boundary: only the inventory component is reused here. Historical G4 references below do not adopt the related G4 producer, evaluator, readiness policy or scientific mappings. The canonical writer must derive the current candidate, not copy a donor census.

## Historical checkpoint — 2026-10-20, 1550f5ff

Status: whole design/intent review `579aa460` and independent whole source review
`58e8f60b` accepted their bounded scopes. ROOT established the reviewed canonical
baseline with the existing writer; both actual production-reader fault controls
passed red/restore-green, and the full inventory module passed. Whole actual-evidence
review `34f8122b` accepted the bounded D1–D5 source and authentic controls. Complete
delivery qualification and protected delivery remain owed.
The normative D1–D5 contract below remains unchanged; these results do not establish
hook activation or publication acceptance.

## Purpose and existing owners

Extend `scripts/architecture_inventory.py::hooks` inside the existing
`collect`/`render` path. The current `architecture_inventory_fresh` check already
compares the complete derived inventory and guards narrative paths, counts,
rosters and required Answers declarations. Keep that single writer and checker;
add no scanner, service, resolver package, registry, gate, exemption or floor.

The mechanical layer owns enumerable metadata and path fidelity. The reviewer
layer, documented by the architecture README, QA map and plugin reviewer roster,
owns semantic adequacy and source/intent correspondence. Those reviewers do not
supply hook activation telemetry or replace the existing inventory derivation.
Fresh independent architecture review is required for this proposal; neither an
author self-check nor a publication-paper reviewer name is that acceptance.

The current machine collector reads public plugin-manifest registrations and
immediate non-sample files under a physical checkout `.git/hooks`. The latter
mistakes a Git file for the absence of the shared hook catalog. Existing source
already uses Git's administrative-context queries in `scripts/codex_continuity.py`
and `scripts/pre-commit-sync.sh`; use the same Git mechanism within the existing
inventory owner, without importing continuity policy or building a generic resolver.

## Measured problem and bounded pilot

The 2026-10-20 read-only pilot used separate source-bound subprocesses for the
main-based candidate and the moving primary checkout. Their actual HEADs, complete
collections, module origins, config origins and metadata rows are retained in the
local author evidence, with no private Git-hook contents opened or hashed. The
candidate is based on ce194cdc; the primary pilot is at ae9e5112. They are distinct
scientific/source populations and are never merged by this evidence.

Both contexts identify the same common and Git-resolved hooks directory, with an
explicit absolute `core.hooksPath` setting. The unchanged identical generator
collects six plugin rows and no Git row in the linked candidate, versus those same
six plugin rows and one Git row in primary. A known-present Git entry is lost solely
because the candidate `.git` is a file. These are dated pilot results, not a new
census floor or a promise about other clones/configurations. The original candidate
check also reports the corrected G4 check description stale and one historical
schema pointer dangling. Its other ownership/roster/count legs pass. Old main-based
CI independently records tracked-seven versus derived-six; blindly writing six
would canonize the omission.

Inspected generator history retains the original physical-path scan. The prior
round68 generated-artifact repair reports a registry-count update, not a hook-path
implementation. A bounded history/continuation search did not identify an accepted
hook portability repair; no claim about inaccessible work follows.

## D1 — Explicit metadata lookup context

Resolve the hook directory with read-only Git queries anchored to the generator's
existing `PROJECT_ROOT`, using `rev-parse --path-format=absolute --git-path hooks`.
Validate that Git's top-level is the same target checkout; a foreign inherited
Git environment must not silently redirect the collector. Use Git's own common-dir
and config handling rather than parsing a `.git` file or guessing the primary path.
Top-level equality alone is insufficient: inherited `GIT_COMMON_DIR` or other
selector/config context can redirect administration while preserving that top-level.
Validate the administrative identity of the target checkout as well, and refuse
foreign redirection rather than cataloging it. Future actual fixture controls must
include same-top-level foreign `GIT_COMMON_DIR`, foreign `GIT_DIR`/`GIT_WORK_TREE`
selectors and inherited selector/config redirection; successful ordinary local and
worktree config precedence remain positive controls. A legitimate configured external
`core.hooksPath` is not foreign administration by itself. Do not blindly strip the
environment, discard supported precedence, or silently fall back to another catalog.
Keep a bounded query timeout, check return codes, and refuse empty, ambiguous,
unparseable or unsupported-version output. A private owner-local helper is enough;
no reusable cross-project resolver is introduced.

`core.hooksPath` may redirect the lookup, including outside the checkout. The
collector must honor the Git-resolved path, not merge an inactive common-directory
catalog into it or silently fall back when config/querying fails. Git applies its
configuration precedence; do not hand-parse a config file or assume multiple
reported origins are an error. Local evidence records origin/scope for diagnosis;
the committed inventory does not expose private absolute paths or config contents.

Relative settings are interpreted by the actual Git query anchored to PROJECT_ROOT,
not relative to the config file or whichever subdirectory launched the generator.
This contract catalogs that observed lookup directory. It does not claim a complete
per-event dispatch map: Git invokes some server-side hooks from a different working
directory, and an actual invocation/configuration/environment can differ. No event
name table or guessed execution-path resolver belongs here.

This distinction follows the official [Git hooks contract](https://git-scm.com/docs/githooks),
[hooksPath configuration](https://git-scm.com/docs/git-config#Documentation/git-config.txt-corehooksPath)
and [path-query interface](https://git-scm.com/docs/git-rev-parse). Upstream Git's
[path implementation](https://github.com/git/git/blob/master/path.c) also distinguishes
configured hooks paths from shared administrative directories. These references
explain the interface, not the behavior of an unmeasured local installation;
installed-version tests and the actual metadata pilot remain required.

## D2 — Membership, readable absence and refusal

Preserve existing plugin-manifest row values/order and existing Git membership:
sorted immediate entries that are regular files under the resolved directory,
excluding names ending `.sample`. Keep nonexecutables in the catalog, as the
current derivation does; do not silently change this into a list of executable or
recognized/active hook names. A symlink to a regular file retains the current
file-membership meaning, but its body/target contents are never read.

Distinguish known empty from unmeasurable. A successful unambiguous Git lookup whose
directory is genuinely absent, empty, sample-only or a known non-directory target
has no immediate hook files to catalog; that observed absence is not a claim about
runtime enforcement. Expose that diagnosis in a small additive `git_hook_context` metadata object within
the existing collect result: `lookup` is the stable string `git-path:hooks` and
`directory_state` is `directory`, `absent` or `non-directory`. The existing render
prints this metadata-only state. Do not include absolute/config-origin paths, file
contents or an activation verdict. Keep hooks() returning its existing row list;
collect() obtains rows and this context together through the same inventory-private
read, without a second scan/cache or new status registry.
Permission/stat/listing errors, malformed config, Git failure, foreign context,
partial reads or an entry disappearing during enumeration must refuse derivation,
not silently produce fewer rows. Do not use broad `except: []` or existence predicates
that collapse permission errors into absence. The existing check's `derivation_runs`
failure and CLI nonzero are the refusal channel; preserve its established
CheckResult/measured policy rather than changing cannot-measure semantics here.

Do not open, execute, copy or hash private Git-hook bodies. The census states
on-disk metadata and manifest configuration only. Presence, executable mode or a
registered plugin command does not establish session loading, actual invocation,
subprocess enforcement or successful runtime admission.

## D3 — Deterministic public representation and conservation

Keep the existing list/dictionary collector interface and row keys, adding only the
bounded `git_hook_context` observation described in D2 to the collect payload. Represent the
Git row's command/origin with a stable logical label `git-path:hooks/<event>`,
defined by the generator's rendered explanation, rather than a private absolute
path or a misleading checkout-relative path that does not exist in a worktree.
The Git command field is a catalog locator, not the shell text or contents of the
private hook. Preserve kind/event/matcher/timeout; attribute this explicit logical
locator correction in the before/after manifest. Other plugin and non-hook
collection records remain byte-for-byte equivalent at the same source.

Render no timestamps, context-specific absolute paths, content hashes or alleged
activation flags. Same source and same resolved catalog give identical public hook
rows from primary, linked worktree and nested launch points. Legitimately different
per-worktree/configured catalogs may differ; never force a fixed hook count to make
them agree. Root must review that real delta before any canonical writer runs.

The implementation must snapshot every existing collection family, demonstrate the
known-present entry, and explain every generated-line delta. G4's corrected check
description comes from its already accepted source; no new G4 policy, formula,
consumer, test-kind, numerical proof or scientific mapping is part of this repair.

## D4 — Schema pointer and affected owners

In the later implementation, replace END_TO_END_MAP's historical placement paragraph
with the actual ownership chain: `docs/KNOWLEDGE_GRAPH.md` is descriptive; authoritative
node taxonomy is `scripts/build_graph.py::SHAPE_MAP`, edge taxonomy is the existing
per-edge extractors, and `docs/architecture/SURFACE_INVENTORY.md` derives the enumerable
view. Remove the absent working-document pointer and the implication that a historical
roadmap is current canonical schema. Do not create a dummy missing file, copy an
old schema, add a dangling-reference exception, or transplant a prose roster.

Update generator/header docstrings and the same topology/QA owner notes in the
implementation commit. README's ownership allocation and Answers declarations stay
unchanged. Knowledge-graph prose need not gain another taxonomy; its current explicit
source-authority statement already resolves that question. The source and canonical
inventory writer must land coherently, with the real description/path changes visible.

## D5 — Controls, independent review and release

Independent whole adversarial and literal operator-intent design acceptance precedes
implementation. Retain the original complete inventory tests and existing mutation
obligation. Add real-Git main/linked/nested fixtures, unset/absolute/relative/spaced
hooksPath and worktree config precedence positives, all metadata membership and
known-empty cases, plus the explicit D1 same-top-level and visibly foreign context
refusal cases. Preserve query/readability/partial-read/race controls and all other
collection families. These tests are future implementation work, not this pilot.

After design acceptance, implement and freeze the coherent source/tests/owner/schema
package, then obtain genuinely nonauthor source review. ROOT next runs the existing
canonical writer to establish the reviewed corrected baseline, inspects every actual
generated-line delta and freshly confirms that baseline before production controls.
This is a necessary prerequisite of the controls, not a later shipping-only task.
Never canonize the old omitted population. Write once for the frozen reviewed inputs;
repeat only when actual changed inputs or a failure justify it, preserving chronology.
A corrected baseline is not whole implementation/evidence acceptance or closure.

Only after that reviewed baseline exists, ROOT owns the journalled real-source control
restoring the old physical `.git/hooks` mistake into the actual generator. A fresh
source-bound process in the real linked checkout must make the existing freshness
check RED for the measured known entry, without changing any floor. Exact restoration
of bytes/fullmode/nsmtime must recover the same targeted GREEN and an empty journal,
including exception handling. Retain the separate real generated-inventory corruption
control through its actual reader, with exact restoration. No private-hook installation,
content mutation or execution is needed. Preserve failures and test actual paths and
outputs rather than copied derivation/count-only asserts. These controls are mandatory
before shipping/closure; they are not prerequisites of source implementation.

Then obtain genuinely nonauthor WHOLE implementation plus actual-control evidence
review, current registration/gates and required delivery qualification before existing
closure/protected-main delivery. Source changes after review require renewed affected
review, baseline confirmation and controls before that final acceptance. No writer
runs during an active mutation; controls restore the established baseline rather than
regenerating an expected answer from the regressed source.

Whole adversarial review examines context, config precedence, unreadable versus empty,
public privacy, canonical-line deltas and all conservation. The separate literal intent
instrument verifies that this makes the existing map truthful and portable, rather
than hiding a red cell or replacing publication work with new machinery. Self-review
satisfies neither instrument. No CI floor, fixture ceiling, schema, G4 aggregate policy,
review ledger, book, publication stage or scientific BUILD changes in this proposal.
