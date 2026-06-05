# Impact Assessment: Route A (faithful ko/Adams/ABP) vs Route B (spectra-free Rokhlin)

> **DECISION (2026-06-03): proceeding with Route B.** The canonical plan is
> [Phase5qB_SpectraFreeSpinBordism_Roadmap.md](../roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md).
> This document is retained as the comparative analysis (and for possible future reconsideration of A).

*Prepared 2026-06-03. Purpose: the larger-program context behind the Route-A-vs-B choice for making the
**bordism leg** of the three-generations constraint unconditional. North star: **correctness over expedience.***

---

## 1. The decision, precisely (target corrected after adversarial review 2026-06-03)

**What the headline actually rests on.** The proven Lean path to `3 ∣ N_f`
(`GenerationConstraint.generation_mod3_constraint` → `ModularInvarianceConstraint` → arithmetic) consumes
only **`24 ∣ 8 N_f`** — the Dedekind-eta / modular-invariance framing-anomaly leg. It does **not** formally
consume `Ω^Spin_4 ≅ ℤ`. The Rokhlin fact **`16 ∣ σ(M)`** is a *separate* "16 convergence" / ℤ₁₆
anomaly-matching leg, entered as a **hypothesis** in `RokhlinBridge.sixteen_convergence_full` (Rokhlin axiom
removed 2026-04-04 → hypothesis; `RokhlinBridge` does not import `SpinBordism`). The full
`Ω^Spin_4 ≅ ℤ` / `SpinBordismData` structure (iso + `σ` generator `= -16`) is *strictly stronger* than
anything the chain consumes and lives only in `SpinBordism.lean`'s framing.

**So this decision is about the 16-convergence leg, not the headline.** Discharging H1/H3/H4 (Route A) or
proving `16 ∣ σ` spectra-free (Route B) makes the **ℤ₁₆ / chirality-wall / SPT** narrative rigorous
(load-bearing for Papers 8/10's bordism story) — it does **not**, by itself, make `3 ∣ N_f` unconditional,
because the headline's residual gaps are the *physics premises* of the eta/24 leg (`Z(τ) ∼ η^{-c₋}`;
`c = ½` per Weyl ⟹ `c₋ = 8 N_f`), which no bordism work touches. The operative fact to make unconditional is
**`16 ∣ σ`** (what `RokhlinBridge` consumes); the full `≅ ℤ` iso is optional and harder.

H1/H3/H4 are currently `Prop := True` pointers (by design, to avoid axioms). Two genuinely-different ways to
make the `16 ∣ σ` / 16-convergence leg unconditional:

- **Route A — Faithful homotopy-theoretic discharge.** Build the ko/Adams/ABP tower literally as the
  D2/L2 bundle narrative describes: `H*(ko;F₂) ≅ A//A(1)` (H1), Adams-SS collapse for ko (H3), ABP
  splitting `π_n(MSpin) ≅ π_n(ko)`, n<8 (H4) ⟹ `Ω^Spin_4 ≅ ℤ`.
- **Route B — Spectra-free discharge.** Prove **`16 ∣ σ`** (the fact `RokhlinBridge` consumes) by classical
  4-manifold / index / lattice methods (Arf invariant of a characteristic surface; or `σ=-8Â`+`Â` even;
  or the α-invariant). Optionally also build the full `Ω^Spin_4 ≅ ℤ` / `SpinBordismData` iso (a separate,
  harder computation not needed by the chain). Same operative endpoint as A, different mathematics. Scoped in
  `docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md`.

(Independent of A/B: **Phase 5q.T** substantiates the *algebraic* Ext layer against Mathlib's real `Ext`.
Wave T1 shipped 2026-06-03 — `A1ExtSubstantive.lean`. That work proceeds regardless of this decision.)

---

## 2. Larger program context (where this result sits)

- **Publication surface.** The generation result is the spine of the **L2** PRL splash ("Three Generations
  from Modular Invariance") and the **D2** deep paper ("Anomaly Constraints on SM Particle Content"), per
  `docs/PAPER_STRATEGY.md`; the chirality-wall synthesis is also in D2. (The `papers/paperN_*` drafts —
  paper7/8/9/10 — are the internal source material D2/L2 consolidate, not deliverables.) It is repeatedly
  cited as a program headline: *"the same ℤ₁₆
  that classifies the chirality wall also constrains the SM's generation count — all formally verified"*
  (Consolidated Critical Review v3, §2.1).
- **Novelty already banked.** "First machine-checked Ext computation over any Steenrod subalgebra" is a
  genuine first and survives independently of A/B (and is strengthened by Phase 5q.T). The headline does
  **not** require A or B to be a true, defensible novelty claim — but the stronger phrasing ("derived that
  the number must be divisible by three") rests on the bordism leg being either honestly-hypothesized
  (current) or unconditional (post-A or post-B).
- **Program's own estimate of the gap.** The consolidated review already logs the full Z₁₆/cobordism proof
  as *"axiomatized, 15–25 person-years"* and `dai_freed_spin_z4` as *"beyond current Mathlib scope."* That
  figure is sourced (Consolidated Critical Review v3 §147; `review_finding_supersessions.json:991`) and is
  the right order of magnitude for Route A, though it names the *Z₁₆/cobordism* construction specifically —
  Route A (ko/Adams/ABP) is the closely-related homotopy-theoretic sibling, not a line-for-line match. Either
  way the program already books this as the dominant open cost.
- **Posture constraints.** PUBLIC repo. Anti-axiom stance is explicit (placeholders chosen over axioms).
  `native_decide` is being systematically eliminated (intent/in-progress — ~49 Lean files still use it as of
  2026-06-03 — so finite-but-huge enumeration is not treated as a free pass). Correctness-over-expedience is
  the stated quality bar.

---

## 3. Route A — faithful ko/Adams/ABP

**What it delivers**
- The D2/L2 bundle narrative becomes *literally* true: the machine-checked `Ext_{A(1)}` genuinely is the
  E₂ page of the Adams SS for ko, and `Ω^Spin_4 ≅ ℤ` follows by the stated chain.
- A reusable, almost-certainly-upstreamable **stable-homotopy / Steenrod / Adams-SS / Thom-spectrum stack
  in Lean** — this would be a landmark Mathlib-grade contribution in its own right, far beyond this program.

**Cost & risk**
- Must construct (each a multi-person-year, Mathlib-scale project): spectra / stable homotopy category;
  the full Steenrod algebra + action on `H*(ko)`; the Adams SS as a topological device + convergence +
  collapse; `MSpin` + ABP splitting. The program's own figure (15–25 PY) is the right order of magnitude.
- **`native_decide`/`decide` give zero leverage here** — this is infinite, non-decidable mathematics;
  the program's demonstrated "months→hours" compression (which lives on finite F₂ enumeration) does **not**
  transfer. This is the single most important risk fact for the decision.
- **H4 circularity** must be discharged by routing ABP through the Adams SS, *not* through any
  Rokhlin-equivalent input — otherwise the derivation is circular. Adds constraint, not impossibility.

**Strategic upside.** Highest prestige; turns a program sub-result into foundational infrastructure others
would build on. If the program's ambition is "leave behind reusable Mathlib algebraic topology," A is the
play.

## 4. Route B — spectra-free Rokhlin

**What it delivers**
- The **16-convergence leg becomes unconditional**: `16 ∣ σ(M)` — the exact fact `RokhlinBridge` consumes —
  by an independent, self-contained proof. (The full `Ω^Spin_4 ≅ ℤ` iso is optional and not delivered by the
  divisibility sub-routes.) H1/H3/H4 are *superseded* (not discharged-as-stated): the conclusion is reached
  without the ko narrative.
- Reusable **4-manifold intersection-form + Arf/Brown-invariant** infrastructure (smaller, but genuinely
  useful and upstreamable).

**Cost & risk**
- Primary sub-route B-Arf (Freedman–Kirby/Guillou–Marin): needs the Arf invariant of a `ZMod 2` quadratic
  form (Mathlib has the forms, not the Arf invariant — a clean upstreamable brick) + characteristic
  surfaces + intersection forms of closed 4-manifolds. The intersection-form/manifold layer (Wave B2) is
  the real lift; Mathlib's `Geometry/Manifold/Bordism.lean` is only at "beginnings of unoriented bordism."
- **CORRECTED by direct Mathlib/repo scout (2026-06-03; supersedes the earlier "~10× smaller" claim):**
  Route B is **not** an order-of-magnitude shortcut. Every Route-B hard core is Mathlib-absent — Arf
  invariant + char-2 quadratic-form theory (4D 8→16), η-invariant/APS/index theory (5D ℤ₁₆ via APS, also the
  repo's APS-η is `η=0` placeholder), Adams-SS for ℤ₄-twisted bordism (5D via bordism = Route-A machinery),
  Niemeier/Schellekens (24-leg, `trivial` scaffold). Mathlib's `QuadraticForm`+signature buys the
  *bookkeeping*, not the load-bearing steps. The **one bounded, in-wheelhouse win** is making the *algebraic*
  `8 ∣ σ` unconditional (discharge `CharacteristicSquareModEight` via van der Blij / Gauss–Milgram — quadratic
  Gauss sums DO exist in Mathlib, so this brick is reachable). The `16` and the 5D ℤ₁₆ stay genuinely hard.
  Full detail + wave plan in `docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md`.
- So both A and B are serious multi-PY efforts for the *load-bearing* topological core; B's advantage is a
  cheaper *partial* win (unconditional `8∣σ`) and a *narrower, more honest hypothesis* at the manifold
  boundary, not a cheap full discharge.

**Strategic downside.** Does **not** make the *ko/Adams narrative* literally true — the D2/L2 bundles would
have to reframe the bordism leg as "established by an independent spin-Rokhlin proof" rather than "by the
Adams SS for ko." The Ext-as-E₂-page story stays a (true, motivating) narrative, not a wired theorem.

## 5. Hybrid / sequencing

- **B's partial win now, full discharge later.** Route B's *bounded* increment — unconditional algebraic
  `8 ∣ σ` (Wave B1, reachable via Mathlib Gauss sums) — is genuinely cheaper and shippable soon, and it
  strengthens the D2 deep paper's rigor incrementally. But the *full* `16 ∣ σ` (Waves B2–B4) and the 5D ℤ₁₆
  are greenfield, comparable in difficulty to Route A's core. So "B reaches the same fact far sooner" is only
  true of the `8`; for the `16`/ℤ₁₆ neither route is cheap. B and A are still compatible (same endpoint), so
  B does not waste A.
- **A as a long-horizon community-aligned track.** If Mathlib ships spectra/Adams milestones (the Phase-5q
  Wave H M1/M2/M3 triggers), Route A's marginal cost drops; keep it tracked-and-watched regardless.
- **Phase 5q.T is the common prerequisite** for the *honesty* of either claim and is already underway.

## 6. What would resolve the decision (recommended next steps, not the call)

1. **Dispatch Wave B0 deep research** (per Phase 5q.B roadmap): exact lemma chain for B-Arf/B-Â/B-α, with
   per-link Mathlib-have-vs-build and LOE. This converts B's cost from "plausibly 10× smaller" to a number.
2. **Run a Route-A scoping spike**: a 1–2 day survey of what a minimal Lean spectra/Adams stack would need
   (or whether to wait on Mathlib), to put a defensible PY range on A beyond the program's 15–25 estimate.
3. Decide on the basis of: (a) how load-bearing the *literal* ko narrative is to the intended publications
   vs. an independent-Rokhlin framing; (b) appetite for foundational-infrastructure investment vs. shortest
   correct path to "unconditional"; (c) Mathlib roadmap signals on spectra/Adams.

**Framing recommendation (decision still yours):** if the goal is the *shortest correct path to an
unconditional 16-convergence / bordism leg* (note: NOT the `3 ∣ N_f` headline itself — that additionally
needs the eta-leg physics premises, untouched by either route), sequence **B first** (dispatch B0 now) while
keeping **A** as a tracked long-horizon infrastructure ambition. If the goal is *foundational reusable
algebraic topology in Lean* and the program is willing to fund a multi-PY build, **A** is the higher-ceiling
play. The two are compatible; the only genuinely wasteful choice is committing to A's full cost *solely* to
obtain the single divisibility fact `16 ∣ σ` that B yields far more cheaply.

*Assessment doc. Created 2026-06-03. Companion to Phase5qT_ExtSubstantiation_Roadmap.md and
Phase5qB_SpectraFreeSpinBordism_Roadmap.md.*
