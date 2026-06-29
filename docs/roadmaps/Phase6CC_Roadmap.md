# Phase 6CC — SPT Classification via Cobordism (Pin⁺ Reframe) — CONDITIONAL, consumes existing arc

**Status: PLANNED (authorized 2026-06-29) — CONDITIONAL, coordinate with `5q.G`.** The topological-superconductor symmetry-protected-topological (SPT) classification in **condensed-matter language**, as a *reframe/application* of the project's existing Pin⁺ ℤ/16 bordism arc. Distinct phase in the `6C*` materials series.

> **⚠️ SCOPING — READ BEFORE ANY WORK.** This phase **consumes** `KitaevSixteenFold`, `RokhlinClassification`, `ArfInvariant`, `BrownInvariant`, `SPTStacking`, `Omega5FiniteIso`, `BordismGroup` — it does **NOT** re-derive them and **NOT** fork or race the **active, separate `5q.G` unconditional-geometric-Pin⁺ `/goal`** (read `Phase5qG_GenuineUnconditional_Roadmap.md` + `Phase5qB_LabNotebook.md` first; coordinate). The finite ℤ/16 cardinality is unconditional; the *geometric full-carrier identification is OPEN (5q.G)*. Per the standing rule a **conditional (disclosed-landmark) discharge is an acceptable temporary posture** for this materials reframe — ship it kernel-clean while 5q.G proceeds.
>
> **⚠️ PHYSICS FIX (mandatory):** an external proposal mis-stated Kitaev's sixteen-fold way as "1D class-BDI." It is **2D class-D**. Every condensed-matter statement here uses 2D class-D.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms (#15)** — the conditional content uses the existing KEEP tracked Prop "Kirby–Taylor Pin⁺ bordism geometric ISO" (Deferred-Targets register item 15) as the disclosed landmark, **not** a new axiom; no `native_decide`; no `maxHeartbeats` (#10); never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual condensed-matter publication).

**Bundle target:** **D2** (existing — anomaly/SM; already owns the 16-convergence, Rokhlin's 16, Kitaev DIII) as a condensed-matter-reframe section — **or** D11; decided at Stage 1 (first-lift). Absorb via `LATE_PHASE6_ABSORPTION_PROTOCOL`.

---

## Wave 1 — topological-superconductor SPT classification *(CONDITIONAL)*
- **Goal:** the **2D class-D** sixteen-fold classification of topological superconductors in materials language, CONDITIONAL on the disclosed `H_PinPlusBordismLandmark`; cites the existing arc and adds the condensed-matter interpretation layer. **Verdict: reachable (conditional)** — interpretation over already-proven structure.
- **Why:** restates a marquee program result in the language of the condensed-matter audience; broadens reach at near-zero marginal cost.
- **Bricks:** `KitaevSixteenFold`, `RokhlinClassification`, `Omega5FiniteIso`; the existing landmark tracked Prop.
- **Gate:** `topSuperconductor_sixteenfold_classification` (conditional on `H_PinPlusBordismLandmark`), kernel-pure, 2D-class-D, landmark disclosed. **No new axiom.**

## Wave 2 — SPT stacking / group structure
- **Goal:** the stacking law / ℤ/16 group structure in materials language, on the existing `SPTStacking`. **Verdict: reachable.**
- **Why:** completes the classification as a group (stacking = addition mod 16).
- **Bricks:** W1; `SPTStacking`/`SPTClassification`.
- **Gate:** `spt_stacking_z16` kernel-pure.

## Sequencing
Coordinate with `5q.G` **before** starting (gate G-6CC.0). W1 (classification) → W2 (stacking). Independent of 6CA/6CB/6CD/6CE. The smallest materials phase (reframe, not new derivation).

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; explicit cross-ref to D2 + to the active 5q.G unconditional work; bundle row staged for first-lift; roadmap status updated.
