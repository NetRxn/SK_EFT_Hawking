# D11 — Prior Art & Novelty Record

**Bundle:** D11 — Kernel-Verified Topological Band Theory & Metamaterial Substrate
**Compiled:** 2026-07-30, at first content-lift.
**Method:** `skeft-qa:research-scout` sweep over whitelisted scholarly sources
(arXiv API, DOI resolution, official project documentation), **plus direct
grep/read of the pinned local Mathlib and PhysLib checkouts** — the latter is
the strongest evidence class here and is exempt from the query-coverage caveats
in §5.

**Pin at time of survey:** toolchain `leanprover/lean4:v4.32.0`, Mathlib rev
`81a5d257`, PhysLib rev `c4843367`.

> **Standing rule for every claim below.** Novelty is stated *to our knowledge*
> and scoped to the checks actually performed. This bundle's sibling precedent
> is not hypothetical: Phase 6BD's novelty claim was **refuted** by QBlue
> (Rocq, arXiv:2509.18583), and Phase 6EA's original novelty claim was
> **refuted inside our own dependency tree**. Unhedged "first in any prover"
> language is a Stage-13 finding, not a stylistic preference.

---

## 1. What is genuinely novel (claim-ready)

For all six surveyed areas, **no prior formalization of the target physics was
found in any interactive theorem prover**. The defensible claims, in descending
order of evidential strength:

| # | Claim | Strength |
|---|---|---|
| N1 | **No proof assistant defines a Chern number or Chern class.** In Mathlib all 14 occurrences of the string `Chern` are `Chernoff`; a case-insensitive sweep for `ChernClass\|PontryaginClass\|StiefelWhitney\|EulerClass\|characteristic class` returns no matches. | **Highest** — direct read of the pinned artifact |
| N2 | **The Chern–Weil route is structurally unavailable in Mathlib**, not merely unformalized: it needs (a) differential forms on manifolds, (b) integration of forms over manifolds, (c) de Rham cohomology, (d) characteristic classes — and Mathlib has none of the four. | **Highest** — direct read; and a *stronger* statement than N1 |
| N3 | **No FHS-style / lattice / discretized-Brillouin-zone Chern computation exists in any prover.** | High |
| N4 | **No acoustic or phononic band structure exists in any prover** — no mass-spring lattice, acoustic Bloch operator, or band-gap existence result. An arXiv sweep pairing "theorem prover" with phononic / acoustic-metamaterial / effective-medium returned **zero** results. | High |
| N5 | **No exceptional points, PT symmetry, or non-Hermitian topology in any prover.** A 25-result arXiv sweep pairing "formalization" with "non-Hermitian" returned physics-formalism papers exclusively — zero proof-assistant papers. | High, with the AFP caveat in §5 |
| N6 | **No Maxwell–Garnett, Hashin–Shtrikman, or periodic-homogenization formalization in any prover.** | Medium-high |
| N7 | **No Bloch's theorem for periodic Schrödinger operators, band gap, honeycomb/graphene, or Haldane model in any prover.** | High |

---

## 2. Mandatory carve-outs

Each of these is real, adjacent prior art. A novelty claim that omits its
carve-out is an attribution failure.

### C1 — PhysLib `TightBindingChain` (Lean 4)

`Physlib/CondensedMatter/TightBindingChain/Basic.lean` (Joseph Tooby-Smith,
2025, Apache-2.0) **does** formalize a tight-binding chain. Read directly, it
contains: an `N`-site chain with spacing `a > 0`, on-site energy `E0` and
hopping `t`; a localized-state orthonormal basis; the Hamiltonian
`E0·Σ|n⟩⟨n| − t·Σ(|n⟩⟨n+1| + |n+1⟩⟨n|)` with periodic boundary conditions;
`hamiltonian_hermitian`; `BrillouinZone := Set.Ico (-π/a) (π/a)`;
`energyEigenstate k`; `energyEigenvalue k = E0 − 2t·cos(ka)`; and the
time-independent Schrödinger equation.

**Carve-out wording:** it is **1D, single-band, and gapless**, its Brillouin
zone is a *real interval* — not a torus, not a manifold — and it carries no
multi-band matrix Bloch Hamiltonian, no band gap, no Berry connection or
curvature, no topological invariant, no vector bundle over the BZ, no
honeycomb, no Haldane model, and no non-Hermitian content. D11's diatomic
two-band model was built precisely *because* a gap cannot exist in a single
band.

**Also:** the only `Berry` string in PhysLib is a bibliography line citing
Berry 1984 next to a solid-angle definition in
`QuantumInfo/States/Pure/BlochSphere.lean`. That is **not** a Berry-phase
formalization — but do not claim PhysLib is silent on Berry either.

### C2 — Cubical Agda synthetic cohomology

Ljungström & Mörtberg, *Computational Synthetic Cohomology Theory in HoTT*
(arXiv:2401.16336; Math. Struct. Comp. Sci. 35, 2025) formalizes cohomology
with arbitrary coefficients, cup products, graded-commutative ring structure,
the Eilenberg–Steenrod axioms, Mayer–Vietoris **and Gysin** sequences, and
the cohomology rings of spheres, the torus, the Klein bottle, projective
planes, and **ℂP^∞**. Related: arXiv:2212.04182 (cohomology rings),
arXiv:2504.08664 (Steenrod squares).

**Carve-out wording:** the Gysin sequence together with H\*(ℂP^∞) is precisely
the machinery from which Chern classes are *defined* in textbook algebraic
topology. The honest claim is therefore: *no proof assistant defines Chern
classes or Chern numbers; Cubical Agda has independently formalized the
cohomological substrate from which they could be built.* Verified by direct
fetch — the abstract does not mention Chern classes, characteristic classes,
Euler class, or Thom class.

### C3 — Isabelle/HOL winding numbers

Li & Paulson, *Evaluating Winding Numbers and Counting Complex Roots through
Cauchy Indices in Isabelle/HOL* (arXiv:1804.03922): winding numbers, Cauchy
indices, the argument principle, and a decision tactic. This is the nearest
formalized machinery to D11's `NonHermitianWinding` and to any index-theoretic
reading of bulk–boundary. Isabelle's general topology is also strong (all 39
sections of Munkres, 806 results — arXiv:2604.07455; fundamental group via
auto2 — arXiv:1707.04757), though none of it is index theory.

### C4 — Lax–Milgram, pen-and-paper and in Coq (the road not taken)

⚠️ **Corrected 2026-07-31.** This entry previously read "Boldo et al., Lax–Milgram
**in Coq** (arXiv:1607.03618) is the **formalized** backbone…". Both halves were
wrong, and both are the round-1 BLOCKER 1.1 error verbatim — it was fixed in the
`.tex` and in `citations.py` but not propagated here, in the very document the
paper names as its novelty backing.

arXiv:1607.03618 is **Clément & Martin**, *"The Lax–Milgram Theorem. A detailed
proof to be formalized in Coq"* (2016) — a pen-and-paper proof *prepared for*
formalization, not a formalization. The actual Coq development is a separate,
later work: Boldo, Clément, Faissole, Martin & Mayero, *"A Coq formal proof of
the Lax–Milgram theorem"*, CPP 2017, DOI `10.1145/3018610.3018625`. Both were
verified by direct fetch.

That Coq development, together with MathComp-Analysis's Lebesgue integration and
differentiation theorem (arXiv:2403.18229), is the substrate an *analytic*
homogenization route would need.

**Load-bearing scoping consequence.** Two-scale convergence has **not** been
formalized in any ecosystem found. Therefore D11's statement that it
"deliberately avoided the two-scale-convergence route" must **not** be framed
as avoiding an existing formalization — there isn't one. Frame it as an
architectural choice between two equally-unformalized routes, in which the
algebraic path was tractable and the analytic one was not. (Local basis for
the stall: Mathlib has Sobolev *inequalities*, not two-scale convergence, and
PhysLib's `Optics/Basic.lean` docstring reads *"This directory is currently a
place holder"*.)

### C5 — Adjacent Lean periodic-lattice precedent

`LeanLJ` (arXiv:2505.09095) formalizes Lennard-Jones interaction energies under
periodic boundary conditions, matching NIST benchmarks. Not band theory, but
the nearest "periodic lattice in Lean" precedent and worth a one-line citation.
The Lean physics lineage HepLean → PhysLean (arXiv:2405.08863,
arXiv:2505.07939) is HEP-only — CKM matrices, anomaly cancellation, Higgs,
Wick's theorem — with no condensed-matter topology.

---

## 3. What Mathlib *does* have (do not overclaim absence)

Smooth vector bundles and topological fiber bundles (14 files under
`Mathlib/Geometry/Manifold/VectorBundle/`, including `Tangent`, `Riemannian`,
`LocalFrame`, and `CovariantDerivative/{Basic,Torsion,Metric}`); differential
forms with exterior derivative and `d∘d = 0` — **on normed spaces only**, with
the manifold version an explicit in-source TODO; the Poincaré lemma **for
1-forms on convex sets**; the divergence theorem; curve integrals.

**Version-pinning is mandatory.** State the Mathlib claim as *"as of Mathlib
rev `81a5d257` (v4.32.0)"*. Mathlib moves fast and has *recently* gained
differential forms on normed spaces and covariant derivatives; an unpinned
"Mathlib has no X" could be falsified between submission and review.

---

## 4. Primary literature (all DOIs verified to resolve)

| Work | Identifier | Verification |
|---|---|---|
| Thouless, Kohmoto, Nightingale & den Nijs, *Quantized Hall Conductance in a Two-Dimensional Periodic Potential*, PRL **49**, 405 (1982) | `10.1103/PhysRevLett.49.405` | DOI resolves; citation string confirmed against the Hasan–Kane RMP bibliography |
| M. V. Berry, *Quantal phase factors accompanying adiabatic changes*, Proc. R. Soc. Lond. A **392**, 45 (1984) | `10.1098/rspa.1984.0023` | DOI resolves; confirmed in Hasan–Kane bibliography |
| F. D. M. Haldane, *Model for a Quantum Hall Effect without Landau Levels*, PRL **61**, 2015 (1988) | `10.1103/PhysRevLett.61.2015` | DOI resolves; confirmed in Hasan–Kane bibliography |
| Fukui, Hatsugai & Suzuki, *Chern Numbers in Discretized Brillouin Zone*, J. Phys. Soc. Jpn. **74**, 1674 (2005) | `arXiv:cond-mat/0503172`; `10.1143/JPSJ.74.1674` | **Strongest** — arXiv abstract page fetched directly; title, all three authors, and journal-ref confirmed |
| J. C. Maxwell Garnett, *Colours in metal glasses and in metallic films*, Phil. Trans. R. Soc. Lond. A **203**, 385 (1904) | `10.1098/rsta.1904.0024` | DOI resolves |
| Hashin & Shtrikman, *A Variational Approach to the Theory of the Effective Magnetic Permeability of Multiphase Materials*, J. Appl. Phys. **33**, 3125 (1962) | `10.1063/1.1728579` | DOI resolves |
| Hashin & Shtrikman, *A variational approach to the theory of the elastic behaviour of multiphase materials*, J. Mech. Phys. Solids **11**, 127 (1963) | `10.1016/0022-5096(63)90060-7` | DOI resolves |

⚠ **For the Maxwell–Garnett *permittivity* formula cite the 1962 paper, not the
1963 elastic one** — a common bibliography error. The 1963 paper is the correct
citation for the Voigt/Reuss/Hashin–Shtrikman *elastic* bounds.

Supporting: F. Bloch, Z. Physik **52**, 555 (1929); Hasan & Kane,
*Colloquium: Topological Insulators*, RMP **82**, 3045 (2010)
(arXiv:1002.3895) — used as the verification source for three of the above.

---

## 5. Honest coverage gaps — read before asserting any absence

1. **The Isabelle AFP was not directly searchable.** `isa-afp.org` is outside
   the research agent's fetch whitelist and the arXiv API indexes metadata
   only, so AFP entries without an arXiv preprint are **invisible to this
   survey** — and AFP is exactly where Isabelle linear-algebra and topology
   formalizations live. Claims N5 and the bulk–boundary/index-theorem negative
   should be read as **medium-high, not high**, until a direct AFP search is
   run for at least: `Jordan_Normal_Form`, `Perron_Frobenius`, `Winding_Number`,
   `Simplicial_Complexes`, `Ordinary_Differential_Equations`.
2. **AFP `Jordan_Normal_Form` is UNVERIFIED.** It is believed to exist but
   could not be tied to a resolvable whitelisted source. **Do not cite it**
   without an independent check — this is precisely the class of claim that
   becomes a review BLOCKER.
3. **HOL4 and PVS have the weakest coverage in this survey.** Neither publishes
   much on arXiv. Nothing relevant was found, but confidence is materially
   lower than for Lean/Agda/Coq. Soften to *"we are not aware of"* rather than
   *"there is no"* for those two specifically.
4. **Negative results are bounded by query coverage.** Each "nothing found"
   rests on arXiv abstract/metadata search plus direct inspection of the local
   checkouts. Formalization work living only in an unpublished repository would
   not surface. The Mathlib/PhysLib claims are **exempt** — those are direct
   reads of the artifact.
5. **APS pages return HTTP 403 to automated fetches.** For TKNN and Haldane,
   verification was (a) DOI registration and resolution to APS, and (b) the
   full citation string read from the Hasan–Kane RMP PDF bibliography. The APS
   landing pages themselves were never fetched.

No prompt-injection attempts or anomalous content were encountered in any
fetched page; all URLs were constructed from arXiv IDs and DOIs rather than
lifted from page content.

---

*Companion to `papers/D11/paper_draft.tex`. Consumed by
`skeft-qa:claims-reviewer` and the Stage-13 adversarial reviewer via the D11
anchor block in `docs/agents/claims-reviewer-bundle-prompts.md`.*
