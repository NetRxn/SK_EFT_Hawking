# Selected ADW scalar certificate and figure consistency

Status: the complete design and current-population pilot are independently accepted.
The implemented consumer and production controls await whole integrated verification. Numerical source acceptance, actual runtime, native proof, physical
interpretation, publication gates and main integration are separate states.

## Current scope and existing coverage

The main-based candidate already supplies the canonical scalar enclosure, semantic replay,
wrapper and `certified-scalar-v1` Fig29 producer. Its complete numerical suite and original
producer populations have executed; the evidence remains a numerical result rather than a
kernel proof. The selected structural helper from the earlier publication candidate describes
`bounded-scalar-v1` and cannot validate the current producer. This design extends that same
selected consistency mechanism on `scripts/review_figures.py`'s real structural path.

The machine layer already has FigureSpecs, producer mappings, generic structural checks,
figure freshness and existing numeric tests. `physics_checks` are manifest prompts. The
figure reviewer assesses pixels, physics interpretation and caption agreement; the claims
and adversarial reviewers assess backing and scientific correctness. A shared mathematical
error in the canonical generator/verifier remains subject to independent numerical and
scientific review. No new check registry, readiness evaluator or reviewer class is created.

`run_structural_checks()` generates each figure, consumes its dictionary and returns ordinary
`CheckIssue` objects. Its actual CLI writes structural results and returns nonzero for errors.
Stage-9 prechecks do not automatically invoke this writing CLI; its qualification must be
explicit. There is no claim that G4 or a whole bundle becomes green through this helper.

## Decisions

### D1. Preserve the actual scalar problem and independent policy

The checker fixes `Lambda=1.0`, `N_f=4`, the original ordered
`numpy.linspace(0.1, 5.0, 100)` and actual `G = requested_ratio * diagnostic_G_c`.
The diagnostic critical coefficient is derived independently from the existing canonical
`critical_coupling`, never from figure metadata. The represented ratio is diagnostic only.
The checker never substitutes an exact nominal ratio for actual supplied G.

The fixed policy is `atol=0`, `rtol=1e-10`, `energy_atol=0`, `energy_rtol=1e-8`,
`max_work=200000`, `max_bits=100000`. Each float tolerance means its exact supplied binary
rational value, not its printed decimal. These are the already executed producer requests.
Expected inputs and policy originate in checker code. Receipt, diagnostic, metadata and
hover copies cannot define them. Policy/model/input/type/size preflight precedes costly
semantic replay. A future deliberate policy change needs fresh evidence and review.

### D2. Use the canonical bounded decoder and semantic verifier

For each original row, call `adw_scalar_enclosure_from_dict` with the independently fixed
external caps, then `adw_validate_scalar_enclosure` with that row's expected actual
G, Lambda, N_f and all six named policy arguments. Require the parameter facade's
`supplied-parameters-exact-pi` model. An `exact-ratio` receipt cannot pass this route.

The canonical verifier checks actual rational series/tails, pi and parameter bounds,
initial bracket, every trace transition, final magnitude and returned-point energy/error
under its own meter. The current root-distance transition uses the actual outward dyadic
mesh and strict width contraction below 5/8; do not reintroduce the earlier unrounded
intersection rule or a second residual evaluator in the figure helper. Reported generation
`work_used` remains range-checked telemetry, not a reconstructed history or complexity proof.

The actual route receives a dictionary from `fig.to_dict()`. Do not add a JSON round trip
or unused parser as an assurance substitute. Any actual future text reader must reject
duplicate keys before dictionary creation across the whole accepted figure. Canonical
certificate parsing alone cannot recover duplicates already discarded by another decoder.

### D3. Bind the entire selected population and visible meaning

Require one `paper5_scalar_scan` trace and exactly the independently fixed original grid,
with all ordered row indices, x/y/customdata lengths and schema `certified-scalar-v1`.
Reject missing, duplicate, reordered, shortened or synchronized changed grids. Require
the expected full metadata/row schema; permit ordinary unrelated Plotly layout fields.

Every row binds its actual G, represented ratio, status, r interval, returned C/V,
normalization, magnitude error, total energy error and complete certificate snapshot.
Decode and verify each receipt; a status or matching pair of mirrors is insufficient.
Numeric types remain canonical: Python equality must not make bool/int/float substitutions
indistinguishable where transport types matter. Rational records/text are canonical and
must not turn positive error into displayed zero. Compare every relevant type and value.

For origin, require certified `r_hi <= 1`, C=V=0, exact zero errors, pre-geometric
scope and coherent no-search/no-selection diagnostics. For a positive scalar minimum,
require certified `r_lo > 1`, finite positive C, finite strictly negative V, unrestricted
domain and coherent selected/enclosed diagnostics. `bounds`, cutoff and optimizer fields
remain None. Both branch records bind the certificate and expected scalar validity tags.

Require the trace ordinate to equal the verified returned C/Lambda, not a clipped or
reconstructed convenience value. At Lambda=1 the displayed error is the verified magnitude
error. Require the existing eight customdata positions and actual hover-template references
for branch, domain, represented ratio, model, r endpoints and both errors. A correct hidden
snapshot does not excuse a false visible hover. Nominal r=1 remains diagnostic.

Require the complete visible qualification after only HTML-break/whitespace normalization:

> This scan approximates minima of the illustrative scalar ansatz with certified numerical
> error; it does not derive a vestigial metric phase, dynamical signature or physical gravity.

Title and axes retain scalar/requested-input meaning. Raster readability, long exact-rational
hover usability and typeset/caption agreement remain independent acceptance work.

### D4. Retain the separate Fig30 assignment contract

Fig30's existing component assignment is not a fluctuation-spectrum derivation. Carry the
already reviewed source subset for its four-dimensional assignment labels/metadata/negative
qualification into this candidate only through exact reconciled hunks. Preserve the actual
ordered category identifiers, corresponding counts and total, and reject mismatched data,
labels, hidden metadata or physical-spectrum interpretation. Do not copy a complete older
`visualizations.py` over the independently accepted scalar, NJL and origin repairs.

The earlier selected helper's Fig30 branch and original explicit negative qualification
remain the contract. A passing category sum cannot supply spin, mass or physical modes.
Any actual current preimage conflict returns to author reconciliation before application.

### D5. Ordinary failures reach the existing CLI

The helper returns no issue for genuinely unrelated FigureSpecs. For either selected spec,
missing/type/shape/policy/model/grid/receipt/visible-binding failures and numerical replay
refusal become ordinary severity-error `paper5_selected_consistency` issues with row context.
Do not swallow replay exhaustion, return a partial passing figure or accept legacy schema.
Generation exceptions already produce ordinary generation errors; preserve that path.

Install one real helper call after successful `fig.to_dict()` in the existing structural
loop. Verify the AST call, not a substring in a comment. Both selected FigureSpecs and both
producer maps remain real. The existing `--check` CLI and nonzero-error mapping are the
entrypoint; no new flag, narrowed selector, registry or dispatcher is needed.

### D6. Non-vacuity is demonstrated on actual production seams

Preserve all original tests and numerical populations. Add meaningful complete selected
transport and real-route tests; fixtures alone cannot establish production reach.
The actual unchanged hundred-row pilot contains no above-cutoff ordinate: its maximum
C/Lambda is about0.7706062. A cap at1 leaves this figure unchanged and cannot demonstrate
non-vacuity. Preserve the original independent exact-ratio r12 above-cutoff scalar/API
regression and add an actual supplied-parameter public-facade above-cutoff control using
its supplied G and trusted policy. These scalar controls do not establish figure reach.

Required figure production mutations through `seed_journal` include deleting the real
helper call, altering the producer grid, changing an actually reached positive ordinate
away from its verified returned C/Lambda, corrupting a real receipt, synchronizing forged
requests/caps across receipt/meta/hover, changing only visible hover or qualification,
and mismatching a Fig30 category/count pairing. Confirm each seed changes its consumed
artifact and produces the intended RED, then exact bytes/full-mode/ns-mtime restoration,
a hard GREEN and no outstanding journal. Do not alter the original grid to manufacture
an above-cutoff figure row or credit an inert clipping mutation.

Separate transport-oracle spies can prove preflight precedes replay; label them as transport
controls. They do not replace the original independent high-precision scalar oracles,
actual original producer population, original full runtime or real CLI error-path evidence.

### D7. Scientific and delivery boundaries remain explicit

The underlying model is the stipulated even scalar potential. Numerical/globality/error
acceptance does not identify microscopic HS/ADW dynamics, establish a physical tetrad or
gravity spectrum, compute an independently justified vacuum scale, fit KV cosmology or
close the other publication builds. Native pi/log/sqrt/rounding/consumer correspondence
remains separately owed. Correct source qualifications remain while those builds run.

Independent whole design review and the real current population pilot precede checker
implementation. Later whole integrated source review, required current gates, actual
artifact/pixel/type-setting verification, original finding Verify and canonical closure,
normal protected Git/main milestones and human publication acceptance remain required.
