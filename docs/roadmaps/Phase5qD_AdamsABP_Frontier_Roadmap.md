# Phase 5q.D: Adams / ABP frontier — the faithful homotopy-theoretic discharge of H1/H3/H4

## Technical Roadmap (DEFERRED, TRIGGER-GATED) — June 2026

*Created 2026-06-08. Governed by
[ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md). This is the "Route A"
of the [Route A/B assessment](../assessments/GenerationConstraint_RouteA_vs_B_ImpactAssessment.md), preserved
as a **shelf-ready plan** so that, if a trigger fires, reactivation is **execution, not re-planning**. It is
NOT an active wave. PUBLIC repo; same invariants as all phases (kernel-pure; no axioms; no `native_decide`).*

---

## Status: DEFERRED. Do not open without a trigger (below).

**Three reasons it is deferred (per ADR-003), all of which must be weighed before activation:**
1. **Off the `16 ∣ σ` critical path.** Phase 5q.B already delivers `16 ∣ σ` unconditionally via the
   spectra-free classification route. Leg D's *only* payoff is upgrading the Ext-over-A(1) computation from
   "honest standalone algebra" to a *wired* "Ext = E₂ page of the Adams SS for ko ⟹ `Ω^Spin_4 ≅ ℤ`" theorem —
   a narrative/prestige gain, not a new load-bearing fact.
2. **Bottom-row cost (ADR-003 LOE table).** The entire stack is Mathlib-absent and partly research-grade —
   spectra, the Steenrod algebra action on `H*(ko)`, the Adams spectral sequence as a topological device, Thom
   spectra + ABP. Traditional ≈ **15–25 PY** (the program's own booked figure). Our demonstrated ~150–300×
   compression is a **top-row** phenomenon (finite/decidable/known-proof); it does **not** transfer to a
   no-blueprint foundational build. Realistically this is a multi-foundation project even at our velocity, and
   the capstones are velocity-insensitive until the foundations exist.
3. **H4 is circular for Rokhlin.** ABP historically uses Rokhlin-equivalent inputs
   (`HYPOTHESIS_REGISTRY['spin_bordism_iso_Z'].circularity_note`). If ever built, H4 **must** route through the
   Adams SS, not any Rokhlin-equivalent fact — otherwise the derivation is circular.

---

## The target

Discharge the three topological hypotheses currently carried as `Prop := True` pointers (by design, to avoid
axioms), making the D2/L2 ko/Adams narrative *literally* true:
- **H1** — `H*(ko; 𝔽₂) ≅ A//A(1)` as a module over the Steenrod algebra A.
- **H3** — the Adams spectral sequence for ko collapses at E₂ in the relevant range.
- **H4** — Anderson–Brown–Peterson splitting `MSpin ≃ ko ∨ (suspensions of ko) ∨ (HF₂ summands)`, giving
  `π_n(MSpin) ≅ π_n(ko)` for `n < 8` ⟹ `Ω^Spin_4 ≅ ℤ`.

The *algebraic* content of H1 (the `A//A(1)` module structure, no spectra) is the **tractable adjacent** and is
scoped as the OPTIONAL **Phase 5q.T Wave T6** — it can land independently and strengthens the corroboration
without entering this frontier.

---

## Prerequisite stack (dependency order; all Mathlib-ABSENT, semantic-verified 2026-06-08)

| # | Foundation | Mathlib status | Row | Notes |
|---|---|---|---|---|
| 1 | Spectra / stable homotopy category | ABSENT (`loogle "Spectrum"` → none) | middle→bottom | the base object; large foundational design |
| 2 | Full Steenrod algebra A + Adem relations + action on `H*(−;𝔽₂)` | ABSENT (`loogle "Steenrod"` → none) | top (algebra) / bottom (action on spectra) | algebraic half = Wave T6 |
| 3 | Eilenberg–MacLane spectra + mod-2 cohomology of a spectrum | ABSENT | bottom | needed to state the Adams E₂ |
| 4 | Adams spectral sequence (resolution + convergence) | ABSENT (general `SpectralObject` ✓ ≠ Adams SS) | bottom | H3 lives here |
| 5 | Thom spectra (MSpin, MO) + Thom isomorphism | ABSENT (`loogle "Thom"` → none) | bottom | needed for ABP |
| 6 | ko / connective real K-theory spectrum + Bott | ABSENT | bottom | H1/H4 target |
| 7 | ABP splitting theorem | ABSENT | bottom (no blueprint) | H4; **route non-circularly** |

Reusable scaffolding that *does* exist: general homological-algebra spectral-sequence machinery
(`Algebra/Homology/SpectralObject`), `Ext R C n`, singular homology, vector bundles. These cover bookkeeping,
not the load-bearing stable-homotopy objects.

---

## Wave plan (only on activation)

- **D.1 — Spectra + stable homotopy category** (foundation 1). The base; almost certainly a Mathlib-community
  collaboration rather than a solo build.
- **D.2 — Steenrod algebra action on cohomology** (foundation 2; the algebraic ring half = Wave T6, reusable
  now). State H1 as a module iso `H*(ko) ≅ A//A(1)`.
- **D.3 — Adams SS + collapse** (foundations 3–4). Build the Adams resolution for ko; identify E₂ with
  `Ext_A(H*(ko), 𝔽₂)`; prove H3 (collapse in range).
- **D.4 — Thom MSpin + ABP** (foundations 5–7). Prove H4 **through the Adams SS** (anti-circular constraint),
  yielding `Ω^Spin_4 ≅ ℤ`.
- **D.5 — Wire** the Ext-as-E₂ narrative into a theorem; reframe D2/L2 from "established by independent
  spin-Rokhlin" to "by the Adams SS for ko"; update `HYPOTHESIS_REGISTRY` H1/H3/H4 and `spin_bordism_iso_Z`;
  Stage-13.

---

## Re-trigger conditions (when to reactivate)

Activate **only** if one fires; otherwise the D2/L2 ko/Adams content stays motivational narrative.

| Trigger | Signal (monitor via periodic semantic search) | Then |
|---|---|---|
| **Mathlib ships stable homotopy / spectra** | `loogle "Spectrum"`, `leanfinder "stable homotopy category"` return real defs | D.1 cost collapses → reconsider D.2–D.5 |
| **Mathlib ships the Adams SS or Thom spectra** | `loogle "Adams"`, `loogle "Thom"`, `loogle "MSpin"` | D.3/D.4 become tractable |
| **A publication requires the *literal* ko/Adams wiring** | editorial/strategic decision that the "Ext = E₂ page" claim must be a theorem, not narrative | fund the build as a foundational-infrastructure ambition |
| **We deliberately fund foundational algebraic topology in Lean** | project decision to "leave behind reusable Mathlib stable homotopy" | open D.1; treat as a standalone landmark project |

**Do nothing on:** routine Mathlib bumps that don't add the foundations above; narrative pressure that the
spectra-free framing (Phase 5q.B/5q.C) already satisfies honestly.

---

## Relationship to the other phases

- **Phase 5q.B** already makes `16 ∣ σ` unconditional **without** this frontier (the reason D is optional).
- **Phase 5q.C** sharpens the one irreducible topological residue (`Arf(q̄)=0`) on the spectra-free side.
- **Phase 5q.T Wave T6** is the *only* piece of Leg D worth doing pre-trigger (algebraic `A//A(1)`, top-row).
- **Leg C-geometric** (the *other* deferred frontier — smooth-4-manifold index theory) is documented in the
  `Phase5qC` roadmap §"Phase 2"; it is a *different* frontier (geometric topology, not stable homotopy) with
  its own triggers. D and Leg-C-geometric are independent; neither blocks the other.
- **The 2026-06-09 Leg-C scouting spike** ([assessment](../assessments/LegC_GeometricResidue_ScoutingSpike.md))
  re-confirmed this roadmap's absence list **for our pinned v4.29.1** (on the `lean-lsp-netrxn` server,
  Mathlib + physlib in scope, `Thom`/`Cobordism`/`Bordism`/spectra all return ∅) **and** checked **live master**
  via `gh`. **Update — Leg-D is now EARLY-WARMING, not cold:** Mathlib master (`v4.31.0-rc2`, we pin `v4.29.1`)
  has shipped **`Geometry/Manifold/Bordism.lean`** (Rothgang — `SingularManifold`, the *first brick* of
  unoriented bordism; bordism *groups* + abelian structure are stated future PRs) and a concrete
  **`Algebra/Homology/SpectralSequence`** layer. These are *started, not load-bearing* (no spin bordism, no
  computation, and `Bordism.lean` carries v4.31 module-system syntax) → **watch, don't vendor yet.** The
  load-bearing trigger for Leg-D is **oriented/spin bordism groups + a low-degree computation** (or the full
  Adams/ABP stack). **Two-layer watch:** `loogle "Spectrum"`/`loogle "Thom"` on our pin **and**
  `gh`-watch `Mathlib/Geometry/Manifold/Bordism*` on master (per ADR-003 Decision #7). Leg-C's homology layer is
  comparably warming; both frontiers are on the community trajectory, Leg-C marginally ahead (homotopy-invariant
  homology vs. first-brick bordism).

---

*Phase 5q.D roadmap (deferred). Created 2026-06-08. Governed by ADR-003. Follows
[Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
