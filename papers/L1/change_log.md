# Bundle L1 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-letter from `paper25_gravitational_waves` (§1)

- Source title: GW170817 vs vestigial graviton
- Lift action: Lift-letter
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Initial lift: paper25 → L1 PRL splash (GW170817 vestigial-graviton falsifier; voucher candidate; Phase 6a W2)

## 2026-05-06 — Lift-section from `_phase6o_W1b_lean_only` (§4)

- Source title: G4 Kerr-Schild double-copy on Petrov-D analog gravity
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1b Kerr-Schild single-copy as alternative substrate context to vestigial graviton; cross-ref-only

## 2026-06-10 — Review-fix (review-2026-06-05 L1-EV1 / L1-EV2)

- Source: (none — prose-precision remediation from the 2026-06-05 external review)
- Lift action: Prose-revision (abstract bound precision + Vergeles provenance correction)
- Insertion point: abstract; §1 (intro, c_GW definition); §2 (vestigial-susceptibility natural-range paragraph)
- Stage-13 redo required: no (claims made more precise; numerical content unchanged; body already carried the asymmetric bound)
- Notes: (EV1) Abstract now states the asymmetric Abbott et al. constraint −3e−15 ≤ Δc/c ≤ +7e−16 with the conservative two-sided envelope in parentheses, matching the body (§1 lines ~104-106, unchanged). (EV2) Vergeles attribution corrected against the cached primary source (Lit-Search/Phase-5d/primary-sources/Vergeles2025.pdf, PRD 112, 054509 = arXiv:2506.00036v2 "Unitarity of 4D Lattice Theory of Gravity"): the paper contains NO RPA bubble integral, NO metric-channel susceptibility, and NO [0.1,10] range (keyword-sweep verified: 0 hits for RPA/bubble/susceptib/natural range/vestigial/second sound/graviton). The draft no longer attributes the bubble integral or the range to Vergeles; the RPA closed form is credited to the project's VestigialSusceptibility.lean formalization, the [0.1,10] window is stated as a project-adopted ±1-decade naturalness window about the dimensional-analysis scale O(Λ_UV²/16π²), and the Vergeles citation is retained for what the paper actually establishes (unitarity of the underlying Einstein–Cartan–Palatini lattice theory). The inaccurate "half-decade window" wording was also corrected. NOTE for provenance registry: PARAMETER_PROVENANCE['GW.CHI_VEST_NATURAL_LOWER'/'UPPER'] proposed human-verify notes (src/core/provenance.py ~2697-2750) carry the same misattribution ("Vergeles 2025 ... derives χ_RPA = ...") — flagged for dashboard correction; not edited here (outside this fix's file scope).

## 2026-10-15 — Abstract length and conditional-model scope

The abstract now states the assumed project kinematic speed, conservative symmetric GW170817 tolerance, compatible susceptibility interval and width, surviving interior value and adopted naturalness range. It retains the lack of a microscopic derivation and limits the constraint to this model. Detailed asymmetric observational bound, endpoint witnesses, formalization descriptions and recovery alternatives remain in the unchanged body. This abstract-only repair does not accept the body's preexisting attribution, singleton/finite-tolerance, susceptibility-displacement or conjunct-independence claims. The declared abstract ceiling and its unverified provenance are unchanged.

Displaced abstract, retained as manuscript history:

```latex
Several emergent-gravity programs identify the spin-2 graviton with
the second-sound mode of a fermionic vestigial fluid, predicting a
gravitational-wave propagation speed
$\cGW = c\sqrt{\chivest}$ where $\chivest$ is the metric-channel
susceptibility of the broken-symmetry phase. We formalize this
identification and confront it with the multi-messenger
GW170817~\cite{Abbott2017GW170817} bound
$-3\times 10^{-15} \leq \dccap \leq +7\times 10^{-16}$
(conservatively two-sided: $|\dccap| \leq 3\times 10^{-15}$). The
result is sharp: over the natural susceptibility range
$\chivest \in [0.1, 10]$ (a project-adopted order-unity
naturalness window about the random-phase-approximation
bubble-integral scale) the
deviation $\dccap = \sqrt{\chivest} - 1$ sweeps $[-0.68, +2.16]$,
vanishing only at $\chivest = 1$ and exceeding the GW170817 cap by
$\sim 7\times 10^{14}$ at the endpoints. The
GW170817-compatible window
$\chivest \in [(1-\tau)^2,(1+\tau)^2]$ with $\tau = 3\times 10^{-15}$
has measure $4\tau \approx 1.2\times 10^{-14}$, vanishingly small
under any natural-range prior. The result is a Lean 4 formal proof
(\texttt{GravitationalWaves.lean}, 32 theorems, zero \texttt{sorry},
zero new axioms): a biconditional locating the compatible window plus
two endpoint falsifier theorems witnessed at $\chivest \in \{0.1,
10\}$, and the Phase~5y H1 underdetermination caveat. The compatible
window is not disjoint from the natural range but strictly nested
inside it, meeting it at $\chivest = 1$; the datum \emph{confines}
$\chivest$ to that window, while no speed-of-light rescaling admits
either endpoint. The identification therefore survives only on a
sub-interval narrower than the natural range by more than 14 orders of
magnitude. The constraint is local to the leading-
order kinematic identification; we identify three avenues by which
emergent-gravity programs may yet recover GW170817 compatibility
(symmetry-driven $\chivest \to 1$ fixed point; distinct
metric-channel identification decoupled from second sound;
frequency-dependent $\chivest$ at higher derivative order).
```

The shorter abstract reflows the preexisting overwide tracked-hypothesis display into the left column, where its original single line overlaps neighboring prose. The display is therefore broken across four aligned lines, preserving its complete mathematical token sequence. This is the sole body-layout exception; it does not establish the adjacent conjunct-independence claim. All other body source bytes are preserved. The original clipped baseline and the pre-layout-fix overlapping rendering are retained in local execution evidence.

### 2026-11-04 — Finite tolerance, attribution and units

Reapplied the independently reviewed finite-tolerance source and figure
repair from `45c740f2` to the lead branch. For the assumed speed law,
finite compatibility gives the exact interval `[(1−τ)², (1+τ)²]`.
Exact luminality singles out unity. Interval width alone gives no
prior probability. The introduction distinguishes Volovik's proposal
from this paper's conditional speed law and uses a dimensionless model
parameter. The RPA response still requires physical normalization and
matching to that parameter.

Independent review held the first composition for an inconsistent
inverse-cutoff unit and language that presented the tensor hypothesis
and project speed law as established or externally derived. The
reviewer accepted the corrected composition and visually checked all
four rebuilt pages. The producer regenerated the October-reviewed
figure byte for byte. The manuscript SHA-256 is
`84184864b857e69a2786f522f13b38cbefe98f849b6a15afb1b6d79394ddc293` and the PDF SHA-256 is
`9f09e22dddbf8f6efbb433366d2b91fd8fb8df3530a66a2302b3e3b1690c4bbb`. Six inherited overfull boxes and blank section pointers
remain open, along with H1 microscopic dynamics, B3 normalization and
window, transport matching, D3 and Paper 25 figure propagation, and
fresh claims and Stage 13 evaluation. This record is scoped to the
lead-branch source, figure and rendered PDF.

### 2026-11-04 — Current sentence review

Refreshed the existing claims-review artifact against the reviewed
manuscript and recorded it through the canonical sentence-state
ingest writer. The 114 body, display, caption and list records
include 79 PASS, 16 WARN, 12 INFO, three TRANSITION, three
UNGROUNDED and one FAIL. The title observation is retained as
a separate followup under the review protocol.

The review preserves the open physical susceptibility/window,
microscopic dynamics, transport and propagation obligations.
It also reproduces the H1 endpoint-theorem attribution problem
and records a numerical window-cancellation limitation that
existing test tolerances mask. Five prior findings are marked
for reconciliation; no finding is closed by this review.

### 2026-11-05 — Stable numerical interval and boundary comparison

The compatible-window computation now uses compensated endpoint
evaluation for small caps, stable lower evaluation near cap one
and the correct zero lower bound for caps at or above one. It
validates cap inputs and documents unrepresentable endpoint
overflow. The speed deviation uses its rationalized form and
preserves wider scalar arithmetic. D3's width ratio uses the
exact algebraic width.

Independent review accepted the repair and its rounding budget.
The regression suite first exposed eleven failures, then two
additional single-precision failures. The final 69 cases pass,
with exact rational and high-precision references. A fresh
210-input boundary control has zero classification mismatches.
The existing counts writer updates the project total to 6,911,
and all fourteen focused freshness checks pass.

The manuscript test count is 69. It compiles to four pages;
the first three pages and the regenerated headline figure are
pixel-identical to the prior accepted outputs. Page four was
visually checked. The six inherited overfull boxes remain.
The refreshed canonical sentence review has 114 records and
preserves the physical BUILD obligations and H1 attribution
failure. The focused numerical finding is
`review:2026-11-05-publication-l1-window-precision:L1:1.1`.


## 2026-11-05: reconcile reviewed microscopic and frequency scope

Restored the reviewed October H1, source-attribution, frequency-model and
concrete-inequality corrections from `2e33bf6`, `90be7b1` and `bd7172ed`.
The current draft retains the November stable numerical interval and positive
speed repairs, the dimensionless normalized-response qualification, finite
tolerance, relative-width/prior distinction and redundant-conjunct disclosure.
Removed the two remaining prose em dashes without changing eponym en dashes.

The manuscript distinguishes conditional endpoint constraints from microscopic
action/propagator/matter construction, and numerical omega=100 from a physically
matched 100 Hz band. The additive correction qualification retains the tau+B
near-boundary condition. These corrections do not discharge the original BUILD
obligations. Compile: four pages, zero TeX errors/unresolved references, six
overfull boxes. Independent review and canonical stage reevaluation remain owed.
Evidence: `papers/AutomatedReviews/2026-11-05-l1-reviewed-manuscript-reconciliation/`.


## 2026-11-05: repair L1 identifier overflow and section pointers

Use breakable path typesetting for the six overflowing identifiers/paths,
preserving their exact spelling, and refer to unnumbered REVTeX sections by
their displayed names. The original layout invariant failed with six
overfull boxes; the repaired four-page compile reports zero overfull boxes,
zero TeX errors and zero unresolved references. Independent review inspected all four pages and accepted exact scientific
and identifier preservation. The existing closure writer records layout
finding1.1 fixed at `4fb4e23ea`; full stage and physical BUILD acceptance remain open.


## 2026-11-05: readable canonical figure and current claim catalog

Repair the canonical Plotly canvas/fonts and propagate the identical reviewed
PNG to the global figure, L1, D3 and contributing source paper. Preserve all
three trace coordinate arrays and existing shapes. Correct the FigureSpec's
Abbott speed-bound anchor to actual Eq.(1), retaining the conservative-envelope
qualification. D3 now states the exact susceptibility interval center and
half-width instead of conflating them with the speed cap. Source-paper TeX
notation and column overflows are separately repaired without scientific
acceptance of its remaining stale claims. Five focused findings have actual
RED/GREEN controls and independent rendered/source acceptance; full stages
and physical BUILDs remain open.

Install the independently verified124-unit claims-reviewer catalog and run
the existing sentence-state intake writer. All114 predecessor records and
four blocker identities are reconciled,49 entries remain supersession
candidates and zero are automatically closed. Existing human sentence states
and prior audit bytes are preserved. The full prose read-through blocks on
reader outcome and the missing original physical argument; its restructuring
instruction is in prose_review.md. Exhaustive quoted-number validation and
full-body source corroboration remain owned publication obligations.

Evidence: papers/AutomatedReviews/2026-11-05-l1-figure-propagation/ and
papers/AutomatedReviews/2026-11-05-l1-current-claims/.


## 2026-11-05 — exact numerical acceptance and source mathematical propagation

Retain the original universal abstract/caption numerical-verification requirement and supply its complete independently accepted exact/high-precision value-to-assertion map. Eight scientific cases extend the original81 unchanged cases to89; meaningful wrong-cap, swapped-star and premature-rounding controls fail. Correct four Abbott bound locators from Eq.(5) to Eq.(1), preserving values, historical dates, tiers and human state. Propagate exact finite-interval, endpoint, prior and tracked-conjunct mathematics into the contributing source, with independently reviewed all-page rendering. Correct its stale conclusion census using actual32 built theorem/lemma records.

The existing sentence-state writer records one bounded current catalog refresh:124units,81PASS/12WARN/26INFO/4TRANSITION/1UNGROUNDED. One count-based successor and numerical-coverage reassessment preserve all four blocker IDs,49 prior candidates and all human state, with zero automatic closures. Full physical B3/modes/matter/transport and full prose-readthrough remain open.

The broad fast result remains RED; six additional environment failures pass their exact targeted rerun with no source/harness modification. Original29 failure identities remain unwaived. Evidence and scoped finding controls: papers/AutomatedReviews/2026-11-05-l1-mathematical-propagation/. Canonical findings1.1 and1.2 are FIXED through the existing writer at scientific repairc183f44a9; all1256 prior records are conserved. Remote checkpoint qualification remains distinct from main acceptance.


## 2026-11-05 — primary-body comparison and custody repair

Separate the Sakstein–Jain cluster/dwarf analysis from its GW-plus-M87 quartic-galileon inference, state the considered matter-coupling scope, qualify affected Ezquiaga–Zumalacarregui sectors and bound the comparison to the four inspected analyses. Correct the matching registry provides/notes and select the four verified PDFs through the existing acquisition record writer, retaining journal identities, verification fields and all earlier abstracts. Source/fulltext versions are explicitly recorded; no fulltext is copied into this repository.

Independent primary-body and integrated125-unit catalog/rendered review accept the bounded correction. The existing sentence-state writer preserves historical assessment/ID lineage, all audit bytes and human state; four scientific blockers remain open. Citation/GW domain tests pass152cases and the four-page compile has zero overflow/errors/unresolved references. The derived acquisition register now has159gaps: four owned body acquisitions plus removal of one already-stale uncited row, not five acquisitions. Full corpus prose/full-stage/main/publication qualification remains open. Evidence: papers/AutomatedReviews/2026-11-05-l1-primary-body-comparison/.


## 2026-11-05 — Reader notation and fixed-tolerance source fidelity

The complete current-draft prose review remains BLOCK on the original physical
response/tensor/matter/transport chain and reader structure. ROOT retains the
whole L1 deliverable; Executor owns bounded substantial constructions.

The revision defines the electromagnetic speed reference and effective RPA
coupling while preserving undetermined physical normalization. It states the
actual dispersion theorem at the fixed GW170817 tolerance rather than an
undefined generic tolerance, with positive numerical probe and correction-only
scope. Two redundant taste/process clauses are removed without changing any
scientific statement, number, attribution or obligation. Independent source and
all-four-page rendered reviews accept this bounded revision. Initial notation
proposals overflowed the charter at five pages; final compact wording restores
four pages without changing typography. All89 focused tests pass. Original
compile/test receipts and full prose instruction are in
`papers/AutomatedReviews/2026-11-05-l1-reader-notation/`.

Canonical claim intake and focused finding closure are recorded separately
through their existing writers. No full-stage, current broad-suite, main or
human publication acceptance follows; original scientific BUILD remains open.
