# Phase 6CA — Topological Band Theory (Chern Number / Bulk–Boundary Correspondence)

**Status: PLANNED (authorized 2026-06-29).** Berry curvature and the Chern number on a Bloch band, plus the bulk–boundary correspondence. Likely whitespace (no Bloch-band Chern number in any prover). First of the public materials-substrate phases scoped 2026-06-29 (companion materials phases 6CB–6CE; chemistry phases 6BA–6BD). Distinct double-letter phase in the `6C*` (materials) series, independent of the unrelated `6A`/`6c`.

> **⚠️ CHECK PhysLib + project substrate FIRST.** PhysLib `CondensedMatter/TightBindingChain/Basic.lean` is a *fully proven* 1D band model (`E₀ − 2t·cos(ka)` + TISE + Brillouin zone) — the reusable skeleton. Project `ChernBridge` is the *abstract* categorical↔real-space marker (NOT a Bloch Chern number); `HeatKernelExpansion`/`FermiPointTopology` are index-theory toeholds. `loogle Chern` → empty in Lean: the Berry/Chern machinery is the new (build-it) infrastructure.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms (#15)** — the deep bulk–boundary wave ships **CONDITIONAL on a disclosed tracked-Prop landmark, not an axiom**; no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual condensed-matter publication + flagship scope).

**Bundle target:** **D11** (authorized 2026-06-29) — "Kernel-Verified Topological & Metamaterial Band Theory" *(provisional)*, shared with 6CB/6CD/6CE. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — Bloch bundle + Berry data
- **Goal:** a 2-band Bloch Hamiltonian on the PhysLib TB template; Berry connection `A(k)` and curvature `F(k) = ∂_{k₁}A_{k₂} − ∂_{k₂}A_{k₁}`. **Verdict: reachable** — differential-geometric layer over the proven band model.
- **Why:** the geometric substrate the Chern number integrates.
- **Bricks:** PhysLib `TightBindingChain`; Mathlib differentiation on the torus/BZ.
- **Gate:** `berryCurvature_def` + gauge-covariance, kernel-pure.

## Wave 2 — Chern-number integrality
- **Goal:** `C = (1/2π) ∫_BZ F ∈ ℤ` (winding-number computation); a concrete `C = ±1` two-band model + falsifier (`C ∉ ℤ ⇒ ⊥`). **Verdict: reachable-moderate.**
- **Why:** the headline topological invariant; integrality is the falsifiable claim.
- **Bricks:** W1; Mathlib winding number / degree theory.
- **Gate:** `chern_number_integer` + a worked `C = 1` model, kernel-pure.

## Wave 3 — bulk–boundary correspondence *(DEEP → CONDITIONAL)*
- **Goal:** edge-mode count `= C` (the bulk–boundary correspondence). **Verdict: DEEP** — index / K-theory; matches the 5qF/5qG-L2 deep-topology weakness. **Ship CONDITIONAL** on a disclosed `H_BulkBoundaryLandmark` tracked Prop (the index-theorem step), exactly like the H1/H3/H4 generation-constraint hypotheses; the unconditional discharge is deferred, not blocking.
- **Why:** the physically observable consequence (protected edge states); shipping it conditional demonstrates the result while the deep index theorem is built.
- **Bricks:** W2; project index-theory toeholds (`HeatKernelExpansion`); tracked-Prop pattern.
- **Gate:** `bulk_boundary_correspondence` (conditional on `H_BulkBoundaryLandmark`), kernel-pure, landmark disclosed in statement + header. **No new axiom.**

## Sequencing
W1 (Berry) → W2 (Chern) → W3 (bulk–boundary, conditional). W1→W2 are fast-moderate; W3 is the only deep wave (conditional escape hatch). Independent of 6CB–6CE.

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; the W3 landmark logged in the tracked-hypothesis register; D11 §topological-bands row staged for first-lift; roadmap status updated.
