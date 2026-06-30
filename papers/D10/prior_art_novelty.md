# D10 — Prior-art / novelty verification (gates the "first in a proof assistant" claims)

**Run:** 2026-06-30, `skeft-qa:research-scout` (read-only, whitelisted scholarly sources). Required by the
Phase 6BA roadmap ("prior-art search to be run via research-scout before any D10 paper-lift"). This file
is the citable backing for every novelty claim in `paper_draft.tex`; Stage 10/13 will check claims against it.

## Verdicts (per layer)

| Layer | Claim | Verdict | Confidence |
|---|---|---|---|
| (i) NEGF transport | First NEGF Green's-function / Landauer–Büttiker / Meir–Wingreen **conductance** in any ITP | **SAFE as "first"** | medium-high |
| (ii) DFT — HK/Levy-Lieb | First Hohenberg–Kohn (I/II) + Levy–Lieb constrained search in any ITP | **SAFE as "first"** | medium |
| (ii) DFT — self-adjointness | First essential self-adjointness of a **molecular many-body Coulomb** Hamiltonian | SAFE **only if phrased "molecular Coulomb", not "first Kato–Rellich"** | medium |
| (iii) Open systems | First Lindblad/GKSL **generator + Markovian semigroup + dissipator-CP** in any ITP | **SAFE as "first"** — *with mandatory carve-out* | high |

## Mandatory honesty carve-outs (must appear in the paper, else overclaim)

1. **Lindblad layer:** quantum **channels / CPTP / Choi-matrix / superoperator** formalizations DO already
   exist — Lean's PhysLib/QuantumInfo (which we build on), Coq's **CoqQ**, Isabelle/AFP **Complex Bounded
   Operators**. Our novelty is the **GKSL generator `ℒ = −i[H,·] + dissipator`, the dissipator's complete
   positivity, and the one-parameter dynamical semigroup `e^{tℒ}`** — NOT static channel theory. State this
   explicitly.
2. **DFT self-adjointness:** Mathlib has a substantial unbounded-operator / spectral / perturbation
   development; an abstract Kato–Rellich-type lemma may exist or be in progress. We built the Kato–Rellich
   substrate **in-tree** in `MolecularHamiltonian.lean` *because* Mathlib lacked it for our use, but the
   defensible "first" is for the **molecular many-body Coulomb Hamiltonian** result, not abstract perturbation
   theory. **Action before publishing:** `lean_leansearch`/`loogle` for "Kato", "Rellich", "essentially
   self-adjoint perturbation", "relatively bounded" to confirm scope.

## Honest-situating citations (related-but-distinct ITP quantum work — cite these)

- **Survey:** "Formal Verification of Quantum Programs: Theory, Tools and Challenges" — arXiv:2110.01320
  (enumerates the whole ITP quantum ecosystem; none address transport / DFT / Lindblad).
- **CoqQ:** "Foundational Verification of Quantum Programs" — arXiv:2207.11350 (Coq density matrices,
  superoperators, quantum Hoare logic).
- **Lean PhysLib / QuantumInfo:** "A Formalization of the Generalized Quantum Stein's Lemma in Lean" —
  arXiv:2510.08672 (the CPTP/channel layer we build on).
- **Isabelle/AFP:** "Complex Bounded Operators in Isabelle/HOL" — arXiv:2512.05878 (bounded-operator
  substrate; not Lindblad/transport/DFT).
- **Isabelle/AFP:** "Quantum projective measurements and the CHSH inequality" — arXiv:2103.08535.
- Isabelle stack: QHLProver (quantum Hoare logic), qrhl-tool, Registers (via the survey).

## Caveat (evidence quality)

Absence verdicts rest on the survey's tool enumeration + AFP catalog (Complex Bounded Operators, QHLProver,
Projective Measurements/CHSH, Registers — none open-system/transport/DFT) + repeated null targeted searches;
this is strong negative evidence, not exhaustive full-text reads (AFP/ACM hosts off the fetch-whitelist). A
verbatim "no transport/DFT/Lindblad tool exists" citation can be hardened by Reading the locally-cached survey
PDF. Claims 1 and 3 are publication-ready as "first" with the carve-outs; claim 2's self-adjointness sub-part
needs the one-line Mathlib scope check above.

## Verification updates (2026-06-30, post Stage-13 adversarial review)

- **Kato–Rellich Mathlib scope check — DONE, confirms claim-2 safety.** A direct search of
  `lean/.lake/packages/mathlib` (Stage-13 reviewer) found **no** Kato–Rellich / relative-boundedness /
  "Rellich" / essentially-self-adjoint-perturbation surface; the only `LinearPMap` self-adjoint surface is
  the abstract definition `A† = A`. The molecular-Coulomb self-adjointness "first" (scoped to the molecular
  many-body Coulomb Hamiltonian, as phrased in the draft) is therefore confirmed safe. This closes the
  Gate-10 FirstClaimVerification hardening recommended above.
- **Citation-author corrections (Stage-13 M1/M2).** The scout captured the arXiv ID + title correctly for
  every ITP reference but did **not** transcribe two author lists: CoqQ (arXiv:2207.11350) is
  Zhou/Barthe/**Strub**/**Liu**/Ying (not Hsu/Yu), and the Lean Stein's-Lemma paper (arXiv:2510.08672) is
  **Meiburg/Lessa/Soldati** (not the placeholder "PhysLib contributors"). `bibliography.bib` corrected.
  Process lesson (QI candidate): scout-sourced bibitems need their author lists fetch-verified before Gate 1.
