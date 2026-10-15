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
