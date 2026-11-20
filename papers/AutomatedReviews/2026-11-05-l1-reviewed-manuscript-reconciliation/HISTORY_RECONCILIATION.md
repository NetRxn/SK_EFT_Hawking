# L1 historical manuscript reconciliation (read-only)

Baseline: d7a8f8a991c8ba2ec19b775239ee3f6ccc977a89, papers/L1/paper_draft.tex SHA256 eb35e94c682129086757ce1abfe0c5383c6ac7381a51fd98fc48a0c1b75ab922. Continuity check returned fresh=true before analysis. ROOT remains sole source/notebook writer; during analysis ROOT reported applying exact 2e33bf6 and bd7172ed manuscript patches. Recommendations below describe d7 baseline omissions, not an instruction to reapply those patches. No compile, Lean, slot or Git mutation performed by this reviewer.

## Source and review provenance

- 2e33bf664b30ed77f08793168028128ae88307f7 (2026-10-15): five-span H1 correction plus scoped review. Directly inspected git-show manuscript diff, papers/AutomatedReviews/2026-10-15-l1-h1-dynamics/L1.md and SCOPED_REVIEW.md at that commit. Final independently accepted full manuscript SHA31c40609931054dde18d9cba68f8c8faed3d33f9890b9314f275099dcc591bdc; reasoning SHA361c1f888ae08211446123e915b4517f27882b486a8ace96848a93d7ecfc0e07. Acceptance explicitly covers five spans, operator mechanisms included, and bounded source/rendering; it explicitly excludes full-paper readiness, fresh Lean or microscopic construction.
- 90be7b1ac15f4be87b5ad4e0c3c431eb5b61bc61 (2026-10-15): source attribution, scoped RPA statement, distinct-channel alternative, conditional dispersion, bibliography edition identity. Its claims_review.json identifies fresh independent complete actual119 assessment by claims-reviewer-v2, gpt-6, run claims-reviewer-v2:2026-10-15T22:25:47.754711Z. Pinned manuscript SHA634fc885fca2d105212507898076f8d33c18577a29e2ddb9d3f663c0b3038809; summary119 units:68PASS,36INFO,13WARN,1UNGROUNDED,1TRANSITION; blocking_issues empty. This is scoped assessment, not full-paper acceptance: layout_acceptance=false, fresh_lean_build_or_kernel_acceptance=false, canonical_finding_closure=false, human_ratification=false.
- bd7172edbebcb97b04cebf451374937d1889b46d (2026-10-15): replaces decidable-real-inequality phrasing with concrete source proof claim; independent changed-unit source-proof review run claims-reviewer-v2:2026-10-15T23:20:05.476998Z; only sentence:L1:formal-setup-and-result:675ab7d2 reassessed,118 prior assessments retained exactly. Summary119 units69PASS/36INFO/13WARN/1TRANSITION. source_only_no_kernel_or_build=true; no fresh theorem inspection or elaboration claimed here.
- 593d70bb7efdaa8449617c74370b25ace6ac786d restores reviewed abstract/display, not these H1/attribution paragraphs.
- 47f99e86a48cd503d64d3a8e5f03e1e3ccd3a5af restores numerical tolerance, finite window/anchor, adopted-range/prior qualification, conjunct dependence and fixed-point scope. Its diff leaves obsolete H1/dispersion and bibliography spans; it is not a safe whole-file substitute for October reviewed text.
- 5ffc0e445510cb290af22deb6cff9d578857b1f6 changes manuscript test count49→69 and numerical producer/consumer precision elsewhere.
- 77aeb709101f68803905aa9fc2c9b6fd450f5442 changes manuscript count69→81 and repairs scalar positive speed elsewhere. Preserve81; do not restore October49.

## Already absent at d7, subsequently adopted by ROOT

Exact 2e33bf6 comparison shows four lost H1 regions: Lagrangian/operator paragraph (d7 lines137–141); operator-mechanism inference150–154; endpoint/open-dynamics paragraph324–336; distinct-channel likelihood365–371. The fifth introductory missing-dynamics paragraph already survives d7 lines88–94; the preceding universal no-value-in-project clause is independently corrected by90be. ROOT reports exact2e33 and bd717 manuscript patch application. No additional reapplication needed.

## Remaining precise adoption spans from90be

Use exact git-object spans below, preserving current numerical paragraphs outside these spans. All paths are papers/L1/paper_draft.tex.

1. Replace introduction from the first paragraph after label sec:intro through just before `The 2017 binary-neutron-star merger` with the historical90be block below. Retain the later dimensionless normalized-response qualification explicitly: historical wording calls susceptibility free but does not state the normalization. Recommended minimal adaptation: replace `where $\chivest$ is the metric-channel susceptibility of the
assumed vestigial substrate.` with `where $\chivest$ represents a dimensionless normalized metric-channel
response of the assumed vestigial substrate.` This is a deliberate later qualifier, not byte-identical90be adoption.

```tex
Spinor-gravity constructions use composite vielbeins built from
fermions~\cite{Diakonov2011,HebeckerWetterich2003}.
Volovik proposes a vestigial phase with metric order preceding a
nonzero tetrad expectation~\cite{Volovik2024Vestigial}.
His symmetry-breaking analysis distinguishes absorbed
Nambu--Goldstone modes from the Higgs-sector gravitational-wave
modes, whose counting also uses coordinate
constraints~\cite{Volovik2022Counting}.
Here we assume that a metric-channel excitation of such a substrate
can be identified with a spin-2 second-sound graviton.

\paragraph{Motivation and assumed speed law.}
Volovik applies Landau two-fluid hydrodynamics to a de~Sitter
state in~\cite{Volovik2026SecondSound}.
The underlying thermodynamic framework treats the gravitational
normal component as stiff matter~\cite{Volovik2024VacuumDecay}.
Within that de~Sitter model, the Landau formula and the stiff-component
thermodynamic relations give $s_2=c$, independently of $H$.
He discusses several possible graviton interpretations of this
collective mode and leaves its type open.
For the spin-2 substrate identification assumed here, we also assume
the susceptibility-dependent speed law:
\begin{equation}
  \cGW^2(\chivest) = c^2 \cdot \chivest, \qquad
  \cGW(\chivest) = c\sqrt{\chivest},
  \label{eq:cGW}
\end{equation}
where $\chivest$ is the metric-channel susceptibility of the
assumed vestigial substrate.
It is a free parameter in this calculation.
The RPA form in \texttt{VestigialSusceptibility.lean} models it using
unevaluated bare susceptibility and coupling inputs, so that form
alone supplies no numerical value of $\chivest$.
The underlying
lattice-fermion framework is the one whose unitarity Vergeles
establishes~\cite{Vergeles2025}. The identification is appealing in its
brevity. In this Letter, Eq.~\eqref{eq:cGW} is an assumed kinematic speed law.
We constrain its free susceptibility without deriving a propagating
second-sound mode from a microscopic action, its propagator, or its
coupling to matter. This missing dynamical bridge is a limitation of
the present calculation, not an impossibility result.

```

2. Replace the current distinct metric-channel enumerate item through immediately before `\end{enumerate}` with this exact90be block. This combines the reviewed no-likelihood correction with the reviewed dispersion correction; it preserves the existing fixed-point item and all November numerical discussion preceding it.

```tex
\item \textbf{Distinct metric-channel identification.} We propose as an
alternative that the ``vestigial mode'' is a separate UV-input metric
channel rather than the second-sound DOF.
Its dynamics could in principle pin its susceptibility to unity;
this remains a model-building possibility. The missing dynamical
bridge in this Letter does not establish that this alternative is
more likely. Phase~6e (full nonlinear emergent action) is the natural
venue for the disambiguation.
\item \textbf{Frequency-dependent $\chivest$.} Equation~\eqref{eq:cGW} is
an assumed frequency-independent kinematic law.
A frequency-dependent susceptibility or a compensating correction
in the LIGO band is a possible phenomenological extension.
We consider the algebraic ansatz $\delta_{\rm disp}=\gamma\omega$,
without asserting that it is the leading term of a matched
microscopic derivative expansion.
The formal probe is numerical $\omega=100$; interpreting it as a
$100\,\mathrm{Hz}$ band and setting $\gamma=\Gamma_H/\cGW^2$ are
modeling assumptions requiring physical normalization and
microscopic matching.
\texttt{vestigial\_dispersion\_below\_ligo\_at\_inspiral\_peak}
assumes $|\gamma|\leq10^{-30}$ and proves that
$|\delta_{\rm disp}|$ at that numerical probe is below the
GW170817 tolerance.
The adopted $10^{-30}$ is a placeholder chosen to keep the
correction below the cap; it is neither derived nor measured.
In the further additive model
$\delta_{\rm tot}=\delta_0+\delta_{\rm disp}$, with
$\delta_0=\sqrt{\chivest}-1$, that assumed coefficient bound gives
$|\delta_{\rm disp}|\leq B=10^{-28}$ at $\omega=100$.
The reverse triangle inequality then excludes restoration of
$|\delta_{\rm tot}|\leq\tau$ whenever $|\delta_0|>\tau+B$.
Offsets just outside $\pm\tau$ can nevertheless become compatible
through an oppositely signed correction within this bound.
Larger corrections are not excluded by the placeholder theorem.
For positive $\omega$, \texttt{dispersion\_within\_ligo\_iff}
exchanges the correction's tolerance for
$|\gamma|\leq\mathrm{tol}/\omega$.
\texttt{dispersion\_correction\_abs\_bound},
\texttt{dispersion\_correction\_linear\_in\_gamma} and
\texttt{dispersion\_correction\_zero\_at\_no\_dissipation} describe
the product's magnitude, additivity in $\gamma$ and zero-coefficient
limit.
Deriving $\Gamma_H$ and the normalization of this ansatz from
microscopic dynamics remains open.
```

3. Replace only these two bibliography entries with exact90be entries:

```tex
\bibitem{Volovik2026SecondSound}
G.~E.~Volovik, ``Massless graviton in de Sitter as second sound in
two-fluid hydrodynamics,'' arXiv:2601.00639v1 (2026).
\emph{Derives luminal second sound within its de~Sitter two-fluid
model and discusses possible graviton interpretations.}

\bibitem{Volovik2024VacuumDecay}
G.~E.~Volovik, ``From Landau two-fluid model to de Sitter Universe,''
arXiv:2410.04392v11 (2025).

```

4. Intro conclusion d7 calls [0.1,10] `natural range`;90be instead says `our adopted range`. A minimal compatible substitution is `sub-interval of the natural range`→`sub-interval of our adopted range`, retaining the full current width4tau, ratio4tau/9.9≈1.2e-15, prior requirement and anchor paragraph. Whole historical paragraph replacement would discard the current explicit ratio/prior sentences.

## Preserved November content

Keep conservative tau3e-15 and asymmetric observed bounds; interval[(1−tau)^2,(1+tau)^2], width4tau=1.2e-14, offsets±6e-15, anchor distinct from compatible set, figure and caption, redundant-conjunct qualifications, adopted interval without dimensional inverse-UV-square assignment, no generic-UV/likelihood/fixed-point selection inference, and current81 test-case wording pending its independent coverage finding. Keep all scalar-speed and precision producer/consumer/test repairs untouched. These manuscript substitutions do not justify changing computation/Lean/metadata/canonical counts. Catalog review90 already retained WARN on incomplete numeric coverage;81 cases is not proof that every quoted number is tested.

## Scientific limits and owed work

This report compares manuscript history and directly read review artifacts. It does not infer missing physical constructions or theorem declarations from text search. Historical H1 review says the Letter lacks a supplied microscopic bridge; scope correction is not an impossibility theorem and is not a substitute for physical B3 BUILD. Full original B3/window/common-Z/modes/matter/transport/Lean obligations remain owed. ROOT must validate fresh source composition and render after adoption; historical layout acceptance does not transfer automatically.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

- The brief's `already independently reviewed` must remain scope-qualified. 2e33 has actual independent scientific/rendering acceptance;90be and bd717 have independent claims assessment with explicit no-layout/no-fresh-Lean/no-human/no-canonical-closure limits. They cannot be represented as whole-L1 scientific acceptance.
- Not every2e33 correction was absent at d7: its introductory missing-dynamics paragraph already survives. Four other regions were regressed. ROOT's later exact patch adoption changes the live candidate; this report remains anchored to d7.
- Historical90be introduction omits later explicit dimensionless normalized-response wording; preserve that qualifier deliberately. Historical manuscript wholesale restoration would undo November count/window fixes, so adopt bounded spans only.
