# Shared-runtime source fingerprint design

**Status: WHOLE SOURCE IMPLEMENTATION INDEPENDENTLY ACCEPTED / PRIMARY INTEGRATION CHECKS IN PROGRESS / NATIVE ADMISSION PENDING.**
Whole R3 design is independently admitted. The isolated implementation is source-present; final mutation evidence, whole implementation review, ROOT integration and native admission remain separate. This document grants no runtime authority.
Normative proposal: [ADR-008 SF-1–SF-7](../../adrs/ADR-008-shared-lean-slot-control-plane.md#2026-10-12-shared-runtime-source-fingerprint-proposal).
Execution: [bounded plan](../plans/2026-10-12-shared-runtime-source-fingerprint.md).

## Purpose and measured residue

Extend Supervisor._runtime_fingerprint instead of adding a registry, status API,
validator family, launcher API or background observer. Existing process metadata,
stale detection, observations and locks remain the producers and consumers.
ADR-008 owns lifecycle; the operator guide owns diagnosis; independent review and
the supported finding-closure writer retain their acceptance roles.

Source read at the assigned 39f8e544 candidate, 2026-10-12:
supervisor.py:150-176 enumerates inventory.repo_root/scripts/lean_slots and allows
confirmed-absent source candidates to be skipped. If a downstream launcher imports
the shared package elsewhere and has no local package directory, its fingerprint
can contain the launcher without the imported package source.
_spawn:496-515 records and compares that digest; _resource_status:1219-1227 compares
it for an identity-matched observable service. Neither supplies the omitted source.
This is source-derived coverage analysis, not a live-process experiment,
host-prevalence estimate or incident attribution.

The direct public scripts/slotctl.py imports lean_slots.cli.main. Current package
membership includes __init__.py, claude_config.py, cli.py, controller.py,
host_limits.py, proxy.py, state.py and supervisor.py. These are mandatory
compatibility inputs, not an exhaustive future manifest. Added package Python
files must be included. The old slot_repo fixture lacks a launcher/package, so
truthful source validation requires a bounded fixture addition.

The mechanical layer already compares digests in status/reuse; the reviewer layer
already assesses lifecycle source and evidence. The residue is actual imported
source and child-route binding, not a missing validator/reviewer. No population
shape is asserted. A later such assertion owes a dated production-slice pilot.

## SF-1 — Expected launch inputs, not process-memory attestation

Keep the existing method signature and string digest. Identify capable expected
launch source/configuration inputs. Existing process records retain the digest
calculated for their launch transaction; comparing current expected inputs exposes
drift. This does not recover Python code objects from memory, attest already
imported bytecode, prove an unchanged interpreter environment or establish request
drain. Correct the method's "actually loaded" docstring during implementation.

Never rewrite old records to current fingerprints, automatically reload, derive
PID authority from module origins, adopt a process or remove reservations.
Only existing root-coordinated ownership/quiescence/client-drain gates can permit
an eligible replacement. Source and runtime acceptance remain separate.

## SF-2 — Mandatory actual imported package

Anchor source to the running supervisor module's __file__ and the actual loaded
state module used by its imported Inventory/observation functions. Use actual
module objects and qualified identities, not inventory location, environment
text, sibling conventions or a newly imported replacement.
Both origins must resolve to regular source files named supervisor.py and state.py
under one capable package directory. Any already-loaded shared controller/CLI/
proxy/auxiliary module must agree.
The R2 source candidate caps relevant loaded qualified origins at 1024 per pass,
including same-file aliases, before native origin observations. Collection refuses
at the first excess name and the final actual Inventory origin is included.
Discovery snapshots the existing Python module dictionary: its scan/allocation
cost scales with that dictionary, so this is not a fixed total CPU/memory bound. Initializer and required compatibility files
must be present and readable.

Absent, malformed, namespace-only, bytecode-only, incoherent or denied origins
fail with typed unavailable evidence. No empty or launcher-only fallback and no
fabricated origins. Canonical root aliases require capable path resolution and
final re-resolution. These observations confer source authority only.

## SF-3 — Complete bounded source observation

Recursively enumerate all package .py files, including every initializer and
nested/additional module, using native os.stat/os.scandir semantics from the
existing state observers. Never use exists()/glob() as confirmed absence.
Reject traversal cycles, links escaping the resolved root, nonregular Python
files, duplicate relative keys and denied/partial enumeration. Root aliases are
supported only when capable canonical resolution and reobservations agree.

Proposed safety limits, not measured population figures: 4096 entries overall,
256 directories, depth 16, 1024 Python files, MAX_JSON_BYTES per file, 32 MiB total
source. Apply the same per-file read bound to the launcher. Exceeded bounds refuse
unavailable; never return a successful truncated manifest. Required modules must
be genuinely read, not counted. Bind relative names and bytes, not mtime alone.

After reading, reobserve origin/root resolution, complete membership and native
file identity/size/timestamps. Re-read and digest all files in this second pass;
compare membership, identities and digests, not a manifest against itself.
Observed additions, deletion, edit, replacement or alias retargeting refuse the
digest. No automatic retry may silently hide detected drift.
Sequential observation is not an atomic filesystem snapshot and cannot rule out
a concurrent writer restoring bytes between reads; make no such attestation.

## SF-4 — Actual supported launcher routing

The inventory-root scripts/slotctl.py named by proxy_command is mandatory,
regular and readable for both managed kinds. Bind its bytes/path and existing
interpreter/argv. Derive the route from bounded actual source and a captured
launch environment. Parent module origins alone do not bind a child's imports.

### Complete supported AST forms and order

Use a whole-template recognizer, not a general Python/AST interpreter. Accept
only the following statement categories, in their actual source order:

- Optional leading docstring/future-annotations declaration; safe imports of os,
  sys and pathlib.Path, including aliases bound to those exact stdlib objects.
- At most eight single-assignment path bindings. Each RHS is one of the fixed
  source-defined forms below and refers only to a preceding validated binding.
  No reassignment, wildcard import, imported custom Path class or arbitrary call.
- Optionally one selected-cli fail-fast guard, after its selected scripts Path
  binding and before CLI import. Optionally one default-inventory setdefault,
  after its source-path bindings and before CLI import. A shared-path template
  has exactly one sys.path.insert(0, str(selected_scripts)) before CLI import.
  These three statements can occur in any source order satisfying their binding/
  import prerequisites; process their effects in that exact order.
- Exactly one import of main from lean_slots.cli, optionally with a bound alias,
  then the terminal main guard testing __name__ == "__main__" and raising
  SystemExit(the_imported_main()). No other executable statements or branches.

Direct public form has no path insertion and selects the capable initialized
lean_slots package in the script directory. Shared form selects an actual path
from its one insertion. A path RHS is a literal absolute path (or bare-tilde/
tilde-slash literal only in the exact captured-HOME expansion below), Path(__file__).
resolve() with literal parent index/parent steps totaling at most four across the
complete source-defined recipe, literal joined components, or Path of a literal-key os.environ.get/os.getenv selection with an
optional fallback of those source-defined path forms. Permit str() only for
declared path operands in the fixed forms; resolve() has no arguments. A recognized
source selector/fallback Path may have exactly one no-argument/no-keyword
expanduser() immediately before that no-argument/no-keyword resolve(), including
validated aliases. Its captured-HOME semantics are specified below; reordered,
repeated or argument-bearing transforms are unsupported. Identity-preserving str()/Path()
conversions and selected source-defined string fallbacks retain the operand
transform state. Aliases, conversions, literal joins, expansion and resolution
retain cumulative parent-operation provenance; parents[index] consumes index + 1
operations. Parent/join-derived operands may have a new transform state and one
admitted expansion, without resetting that cumulative four-operation budget.
Inactive selector/default expressions are validated eagerly under these rules. A supported parent index
must also exist on the actual recognized Path; missing parents yield typed unavailable
evidence before pending/Popen, rather than an uncaught IndexError. Bound literal components
and selector names/values under the launcher read limit. There is no general
expression evaluation, ambient home lookup or inferred path fallback.

The CLI guard's sole condition is UnaryOp(Not, Call(Attribute(P / "lean_slots" /
"cli.py", "exists" or "is_file"), no args/keywords)), where P is the already
validated selected scripts Path (a preceding alias can resolve to that same P).
Its body is exactly one Raise(Call(Name(SystemExit), [message], no keywords));
there is no else. Message is a string Constant or JoinedStr containing only string
Constants and FormattedValue(Name(P), conversion=-1, format_spec=None).
P is a genuine validated pathlib.Path value, never a custom object. No attribute,
subscript, function call, arithmetic or other expression inside interpolation,
no conversion or format spec, and no other Name. Bound the resulting diagnostic
to 4096 UTF-8 bytes; over-bound/malformed templates refuse rather than execute.
The recognizer never executes the guard: native capability independently requires
selected cli.py regular/readable, so denied observation is unavailable even if
the launcher's exists() would suppress it.

The default operation is one Expr(Call(os.environ.setdefault,
[Constant("LEAN_SLOT_CONFIG"), str(validated_source_inventory_Path)], no keywords)).
Accept an os import alias and the same bounded source-derived Path forms only.
This is the existing Inventory.load environment key, not a new environment API.
No assignment of the return value and no additional environment writes. Resolve
the source-defined default path without inventing a sibling. It may occur before
or after insertion/guard, but only before importing CLI. Unsupported calls, extra
conditions, dynamic statements, duplicate default operations or insertions refuse.

### Bounded captured-HOME expansion (SFR4)

Recognize only Call(Attribute(Call(Attribute(genuine_recognized_Path,
"expanduser"), [], []), "resolve"), [], []) or its already validated Path alias.
This is a fixed source-template operation, not permission to call arbitrary
Path methods. Do not execute ambient Path.expanduser() while predicting: implement
the bounded recognized subset from the immutable captured environment, without
temporary os.environ mutation, pwd/current-UID lookup or new home API.

An absolute operand not starting with tilde is an identity expansion. It consumes
no HOME, requires no irrelevant HOME observation and has no HOME sensitivity in
the digest, even if ambient/captured HOME is missing, invalid or changed. Relative
non-tilde package selections remain unsupported unless their recognized source
expression already derives an absolute path from the actual launcher file.
Admit only raw bare "~" or a raw path starting with "~/" for the home branch.
Named "~user", "~user/...", unsupported tilde spellings and arbitrary transforms
refuse. A home branch requires captured HOME present as a nonempty absolute string,
at most 4096 UTF-8 bytes, with no NUL/CR/LF, and a capably observed directory.
Raw path and expanded selected path each have the same 4096-byte string bound.
No absent/empty/relative/malformed/over-bound HOME or unavailable directory may
fall back to process-user or live ambient home. Other platforms/layouts outside
this declared bare-tilde slash form refuse until a revised bounded contract.

Resolve HOME aliases canonically with native path capability, not a textual
equality claim. For bare "~" the expanded value is captured HOME; for "~/" replace
only that leading prefix with captured HOME plus the source suffix, then perform
the declared canonical resolve. Require capable selected scripts/package/mandatory
source and equality to actual loaded origins as before. Link escapes, missing/
denied directories, invalid path targets and changed canonical aliases refuse.
Do not manufacture an identity from the home string.

Routing binds the actual raw operand, whether expansion is absent/absolute-noop/
captured-home, the expanded value and canonical selected path. Only when consumed,
bind HOME presence/value plus its resolved home path; omit unused HOME entirely.
Capability identities, observation time and timestamps remain evidence outside
the digest, never incidental currentness inputs. Same spelling/source repeated
under unchanged capable evidence is deterministic; distinct consumed raw HOME
aliases may have distinct source-input digests even when their canonical target
agrees. Neither identity nor a spelling alone confers PID authority.

Both bounded source passes must reobserve the used home directory/canonical alias
and raw-to-expanded-to-selected path chain along with mandatory origins/membership/
bytes. Use the same immutable captured value; do not reread ambient HOME to repair
a drift. A home alias retargeted or required path becoming denied/missing between
passes is unavailable and retains resources. Unused HOME cannot cause a false stale
or unavailable result for an absolute no-op. Sequential path/source observations
remain non-atomic and are not actual imported-child or process-memory evidence.

### Exact generic examples

These are proposed source templates for future controls, not deployed-wrapper
or imported-child measurements. EXAMPLE_SHARED_ROOT is a launcher-local literal
selector in the example, not a newly proposed public environment variable.

~~~python
from lean_slots.cli import main

if __name__ == "__main__":
    raise SystemExit(main())
~~~

~~~python
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SHARED = Path(os.environ.get("EXAMPLE_SHARED_ROOT", str(ROOT.parent / "shared-source"))).resolve()
SELECTED_SCRIPTS = SHARED / "scripts"
if not (SELECTED_SCRIPTS / "lean_slots" / "cli.py").is_file():
    raise SystemExit(f"Shared source unavailable: {SELECTED_SCRIPTS}")
sys.path.insert(0, str(SELECTED_SCRIPTS))
os.environ.setdefault("LEAN_SLOT_CONFIG", str(ROOT / "config" / "lean-slots.downstream.json"))
from lean_slots.cli import main

if __name__ == "__main__":
    raise SystemExit(main())
~~~

~~~python
import os as environment
import sys as runtime
from pathlib import Path as SourcePath

ROOT = SourcePath(__file__).resolve().parents[1]
SHARED = SourcePath(environment.getenv("EXAMPLE_SHARED_ROOT", str(ROOT.parent / "shared-source"))).resolve()
SELECTED_SCRIPTS = SHARED / "scripts"
runtime.path.insert(0, str(SELECTED_SCRIPTS))
environment.environ.setdefault("LEAN_SLOT_CONFIG", str(ROOT / "config" / "lean-slots.downstream.json"))
if not (SELECTED_SCRIPTS / "lean_slots" / "cli.py").exists():
    raise SystemExit("Shared CLI source unavailable")
from lean_slots.cli import main as entry

if __name__ == "__main__":
    raise SystemExit(entry())
~~~

The home-capable shared form below is also a complete proposed template. Its
fallback is explicitly source-derived; only a selected tilde operand consumes HOME.

~~~python
import os as environment
import sys as runtime
from pathlib import Path as SourcePath

ROOT = SourcePath(__file__).resolve().parents[1]
RAW_SHARED = SourcePath(environment.environ.get("EXAMPLE_SHARED_ROOT", str(ROOT.parent / "shared-source")))
SHARED = RAW_SHARED.expanduser().resolve()
SELECTED_SCRIPTS = SHARED / "scripts"
if not (SELECTED_SCRIPTS / "lean_slots" / "cli.py").is_file():
    raise SystemExit(f"Shared source unavailable: {SELECTED_SCRIPTS}")
runtime.path.insert(0, str(SELECTED_SCRIPTS))
environment.environ.setdefault("LEAN_SLOT_CONFIG", str(ROOT / "config" / "lean-slots.downstream.json"))
from lean_slots.cli import main as entry

if __name__ == "__main__":
    raise SystemExit(entry())
~~~

Each form is recognized as a complete module, with alpha-renamed symbols bound
once to validated stdlib objects/path values. A permitted-looking fragment inside
arbitrary executable source is unsupported. Reject the f-string variants
{SELECTED_SCRIPTS.parent}, {str(SELECTED_SCRIPTS)}, {SELECTED_SCRIPTS!s},
{SELECTED_SCRIPTS:>10} and interpolation of any unrelated variable. Likewise reject
extra guard branches, calls/mutations or a custom formatting/import hook.

### Captured effects, selected sources and consumer contract

Capture the environment once before route validation. Evaluate source-defined
path selection only against that immutable capture. Compute a separate predicted
child-import environment: setdefault leaves a present LEAN_SLOT_CONFIG value
unchanged (including present-empty); absent key receives the exact source-derived
default. Record key presence, effective string, source default and whether applied
in deterministic routing inputs, not the opaque whole environment or secret data.
Malformed/over-bound values refuse; this must not turn unrelated environment
variables into source authority. Never mutate the caller's os.environ while
predicting launcher behavior.

The actual Popen gets the captured pre-wrapper environment, with only the existing
applicable backend-token addition; the child wrapper itself performs its setdefault.
A predictor must not preapply/default-overwrite Popen input and erase the distinction
between absent and present. The selected --inventory command argument retains its
existing precedence over LEAN_SLOT_CONFIG. Bind the actual configured inventory
source and existing server/auth inputs; a source-defined default does not replace
explicit inventory authority. If a permitted entry point uses the environment
default as effective inventory, observe that selected regular source capably.
An inactive source-defined default is still recorded as routing behavior, without
inventing an assertion that its target was read or selected.

The selected scripts directory must contain an ordinary initialized lean_slots
package whose resolved root equals the mandatory loaded supervisor/state root.
Check actual chosen paths and required sources natively. An override selecting
valid package B while parent remains loaded from A refuses incoherence. Missing/
empty/invalid root selection or unavailable guard target is not optional absence.
Same-root aliases work only with capable canonical equality/reobservation.
Routing must not depend on the backend authentication-token key; that addition
is secret authentication data, not a package selector or digest input.

Use this same captured image for route validation and Popen even if a filesystem/
environment external seam changes the process environment between those stages.
Private internal computation can accept the captured image; existing public
_runtime_fingerprint signature/command outputs remain unchanged. Status performs
its own new bounded capture; it never reuses a cached old route verdict.

SFR3 owes a distinct real A/B control. Genuinely import the shared package from A,
and create another real supported package B. Route/validate captured selector A.
An external observation/read seam then changes os.environ's selector to B before
actual intercepted Popen, without modifying any internal verdict or module origin.
Assert recorded Popen env still selects A, retains an independently declared unrelated
capture sentinel and applicable backend-token addition, with unchanged argv.
Assert absent/present default-inventory input semantics separately. A subsequent
new current-route call against B while parent remains A must refuse. Only changing
production Popen construction to recapture current os.environ is the sole mutant;
the unchanged recorded-env assertion must turn native red, restore byte-exact green.
This is future isolated evidence, not an executed probe or process-memory proof.

SFR4 adds a distinct HOME-aware A/B control rather than relying on the earlier
selector-only capture test. Genuinely import package A under a real capable home A
and build another genuine package B under capable home B. Captured HOME A and raw
tilde selector resolve to A. During an external source/path read observation,
change live HOME, selector and independent sentinel to B before proxy/backend
Popen. Its independently intercepted environment must still carry captured
HOME A, selector A and original sentinel, plus applicable backend token, with
unchanged argv and default-inventory semantics. A subsequent fresh B evaluation
while parent remains A refuses incoherence and performs no new launch or record
clearing. No __file__/route/fingerprint/completeness verdict is mocked.

Absolute non-tilde no-op with absent/invalid/different HOME, canonical home/path
aliases and bare-tilde/tilde-slash positives are independently required. Named-user,
missing/empty/relative/malformed/over-bound/denied HOME, escaping/retargeted aliases,
unsupported/reordered/argument-bearing transforms and both-pass path drift refuse.
Separate sole production mutations that use ambient HOME instead of captured
HOME and that accept one unsupported transform must fail unchanged independent
native assertions, then pass with exact restored source. HOME prediction/refusal
and actual Popen capture must both be exercised; no child probe or new API.

Preserve proxy_command/backend_command and executable/server inputs. Backend
executables are not asserted to import this package; their digest also binds the
shared supervisor managing their transaction. No general interpreter, repeated
child import probe, new public environment API or source registry is introduced.
Unsupported entry forms are explicit design blockers, not silently simplified
fixtures. Independent review must inspect these exact guard/default/alias forms
and real import precedence before implementation admission.

## SF-5 — Distinct deterministic source namespaces

Retain role, kind, command, complete server/configuration and selected slot inputs,
including client-auth sensitivity. Add a versioned deterministic payload with
separate shared, launcher, local and routing namespaces. Same relative names cannot
overwrite each other. Bind canonical roots and full sorted relative-name/content
manifests; bind recognized route and actual selected environment/path branch.
Do not include observation time, incidental order, repr or locale in the digest.

Inventory-local scripts/lean_slots is optional only when **confirmed absent**.
If present, observe it completely under the same bounds and a distinct namespace,
even when explicit shared routing selects another package. Equal local/shared
roots are deterministic aliases with equal checked manifests; mandatory shared
coverage is never removed. Denied/malformed optional contents are unavailable.

## SF-6 — Actual consumers and independent evidence

Fingerprint refusal precedes any new pending write/Popen. _resource_status already
catches SlotError: carry typed unavailable witnesses into actual status/doctor/
health while retaining metadata/reservations. A matched owned observable service
with changed capable inputs is stale, not down; unchanged inputs preserve running.
Confirmed exit/quiescence retains its separate down diagnosis. Source/root
coherence does not replace process/census identity or endpoint ownership.

The implementation candidate uses actual temporary files, genuine fixture package imports and production
fingerprint/status/reuse consumers. External filesystem/process/socket/write/
handle/time seams may isolate tests. Fingerprint/route/completeness/internal guard
verdicts may not be mocked to certify them. Do not forge module __file__.
Public-direct positives import genuine fixture package source; overlay positives
import genuine selected shared source with no local package. Add a supported
slot_repo launcher that agrees with actual imported origins, not a source bypass.

Every plan control owes sole production mutation/native assertion red and exact
restored green through unchanged independent oracles. Preserve raw output, commands,
times, failures and hashes. Helper-mirroring, altered test oracle, import/syntax/
harness error or canned verdict is invalid. Byte edits are actual read inputs.

## SF-7 — Compatibility, alternatives and admission

Preserve every original F1–F6/LO-1–LO-6, R1–R6, ND1/ND2 and NC1–NC7 obligation and
immutable evidence. Retain sessions/auth, fixed roots, pairing/dependencies,
capacity, borrowing, rollback, stored identities, literal absorption and no SIGKILL.
Do not edit CLI/controller/proxy/state, scientific/numerical/proof sources,
generated configuration, lease schema, registries or books. Report extra scope
before implementation if measured necessary.

Provisional smallest route: whole-template matching adds bounded source/AST/file
work within supervisor, without a child observer or new lifecycle surface.
Alternative child import-origin observation would add production subprocess launch,
import side effects, timeout/reap/error seams and repeated status/reuse work.
No timing is measured and no probe is authorized in this design phase.
Local-only or environment-named hashing cannot prove selected imports; a general
Python interpreter would add another execution mechanism. Both are rejected.

Independent adversarial/intent specification review and ROOT admission precede
implementation. Whole implementation review, meaningful controls/restoration,
current project gates, normal integration and supported closure remain required.
Native request drain, loaded-code evidence and matching-lease MCP admission are
later root-owned gates. Historical failed gates remain unwaived. Nothing here
permits unknown-process actions or silently changes existing acceptance.


## Current source-evidence checkpoint

Whole R3 design remains admitted. The coherent provenance repair carries same-operand
last-transform state through source string reconstruction and selected source-defined
fallbacks, and cumulative parent-operation count through conversions, aliases, joins
and transforms. Parent/join-derived transform state remains distinct from the
four-operation complete-recipe budget. Payload/default/Popen strings remain ordinary
strings; captured environment-selected strings start fresh operands. Eager inactive
fallback/default validation remains required.

The frozen R2 originals and all previous raw evidence remain retained. Historical
47 qualifying scenarios cover 43 production images; the corrected FP34 control omits
all three absolute-path policy gates, and its older invalid attempt remains invalid.
The admitted current campaign retains those scenarios and adds distinct provenance/budget
omissions. ROOT verified every baseline/red/restored triad against native assertions:
56 scenarios, 52 distinct production images and 168 command captures, with exact source
restoration. Independent whole implementation review accepted the complete source,
original-contract preservation and frozen evidence without mandatory repairs. The
reviewed files are present in the primary checkout; its five-module integration check
passed 469 tests. The canonical closure writer verified each declared command and closed the source
findings. Current full-project gates, normal commit and separately measured native
admission remain pending.
Expected-source fingerprints are not process-memory or request-drain evidence.
