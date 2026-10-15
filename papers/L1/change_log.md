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

## 2026-10-15 — Finite-tolerance and logical-clause interpretation

The symmetric speed cap permits a finite susceptibility interval, not just the exact-zero anchor. Its expanded susceptibility endpoints have approximately twice the speed-deviation offset. P2 already implies P3 at the stated tolerance, and positivity holds throughout the compatible physical interval; the falsifier proofs do not establish independent-clause necessity. The quarter point lies inside the adopted range. Interval width is distinguished from prior probability and microscopic selection, including recovery mechanisms that can preserve the speed law. The figure caption and the exclusively allocated canonical producer label/docstring carry the same distinctions; numerical trace/shape data are preserved. The accepted 443-character abstract and displayed predicate/theorem statements are unchanged. No live Lean/proof, external-attribution, source/comment/metadata or whole-paper certification follows.

Displaced manuscript spans and proposal-propagation corrections, retained as exact history (the science text states the current result):

```latex
GW170817-compatible window $[(1-\tau)^2, (1+\tau)^2]$ has measure
$\sim 4\tau$ in $\chivest$, vanishingly small under any natural-range
prior, and sits strictly interior to $[0.1, 10]$ about the anchor
$\chivest = 1$.
```

```latex
What the bound can do instead is fix $\chivest$ itself, and the content
of this Letter is that it fixes $\chivest$ to a part in $10^{15}$ of
the order-unity window the identification's own microscopic origin
would predict --- a value that window contains, but does not favour.
```

```latex
establish that the failure is not an endpoint artefact. The one value
that survives is the singleton:
\verb|ligo_satisfied_at_chi_one| proves \verb|LigoSatisfied| holds at
$\chivest = 1$, and \verb|c_GW_deviation_zero_iff_chi_one| makes that
the exact biconditional.
```

```latex
  $[(1-\tau)^2,(1+\tau)^2]$ is $10^{14}$ times narrower than the
  natural range and so renders as the single gold star --- note that it
  sits \emph{inside} the band, not beside it: the datum confines
  $\chivest$, it does not exclude the range.
```

```latex
three independently load-bearing conjuncts:
```

```latex
demanding positivity (P1), GW170817 compatibility (P2), and
sub-half-deviation $|\dccap| < 1/2$ as P3'. P3' is genuinely
independent of P1 (e.g.\ $\chivest = 1/10$ satisfies P1 with
$|\dccap| \approx 0.684 \not< 1/2$). The bundle is discharged at
$\chivest = 1$ (\texttt{H\_VestigialModeIsGraviton\_at\_one}) and
\emph{four} explicit falsifier theorems prove non-vacuity:
\verb|*_fails_at_natural_lower| (P2),
\verb|*_fails_at_natural_upper| (P2),
\verb|*_fails_at_zero| (P1), and
\verb|*_fails_at_quarter| (P3'; at $\chivest = 1/4$ the deviation is
exactly $\dccap = -1/2$, saturating the bound and isolating P3'
independence). The bundle's support over the natural-range prior has
measure $4\tau \approx 1.2\times 10^{-14}$ --- vanishingly small, but
non-empty, and containing $\chivest = 1$ --- and that is the
load-bearing falsifiability claim. (The
original Wave-2 P3 = $\forall c{>}0,\,\cGW(\chivest, c) > 0$ was
removed in the 2026-04-25 post-Wave-2 audit as redundant given P1;
P3' replaces it with a load-bearing quantitative constraint per the
project's preemptive-strengthening discipline.)


```

```latex
\paragraph{What this rules out.} GW170817 does not exclude the
leading-order vestigial-second-sound identification outright: it
survives at $\chivest = 1$. What it rules out is the identification as
a \emph{generic} consequence of the natural range. Eq.~\eqref{eq:cGW}
requires $\chivest = 1 \pm 3\times 10^{-15}$, a fine-tuning so extreme
it cannot follow from a generic UV theory --- so any surviving version
of the identification owes an account of why $\chivest$ sits exactly
at unity.


```

```latex
The present evidence
most favours this path: Volovik's own background returns $s_2 = c$
exactly, i.e.\ $\chivest = 1$, structurally. The value GW170817
selects is thus the value his construction already produces --- the
datum corroborates his result and indicts our substrate's failure to
reproduce it, not the identification. Phase~6 should examine
whether such a fixed point is realized in the ADW broken phase.

```

```latex
$\chivest \in \{0, 1/4\}$, which are outside the natural range and
establish that the failure is not an endpoint artefact.
```

```latex
Sec.~\ref{sec:discussion} are correspondingly different in kind, and
each requires replacing the identification rather than repairing it.
```

```latex
$\cGW$ depends on the metric-channel susceptibility, where the
relevant scale is the dimensionless $\chivest$ which the natural
range happens to pin around 1 only by coincidence. GW170817 sees
the latter, and its bound is too tight to absorb the natural-range
spread.
```
