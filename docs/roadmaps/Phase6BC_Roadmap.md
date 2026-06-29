# Phase 6BC — Open-System Dynamics (Lindblad / GKSL)

**Status: PLANNED (authorized 2026-06-29).** The verified Lindblad / Gorini–Kossakowski–Sudarshan (GKSL) master equation for open-system molecular dynamics. PhysLib ships the full CPTP/Choi/Kraus channel layer — the **static half is done**; the new content is the *generator* and the Markovian semigroup. Distinct phase in the `6B*` chemistry series.

> **⚠️ CHECK PhysLib FIRST.** PhysLib `QuantumInfo/Channels/CPTP.lean` + `MatrixMap.lean` ship `CPTPMap`, `choi_PSD_iff_CP_map`, `exists_kraus`, `exists_purify`; `ForMathlib/HermitianMat/*` ships operator-monotone/CFC `exp`/`log`. The channel object is free — only the GKSL generator + semigroup are new. The project `QuantumNetwork/*` supplies diamond-norm / trace-distance. Verify by search before re-deriving.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the generator/semigroup *formulas* are Lean-verified; the physical-channel identification (which bath, which jump operators) stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D10** (authorized 2026-06-29; §open-systems), shared with 6BA/6BB. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — GKSL generator + complete positivity
- **Goal:** `ℒ(ρ) = −i[H,ρ] + Σ_k (L_k ρ L_k† − ½{L_k†L_k, ρ})`; complete positivity of the generated map via PhysLib Choi (`choi_PSD_iff_CP_map`). **Verdict: reachable** — generator over the existing CPTP layer.
- **Why:** the central object of open-system dynamics; CP is the physical-consistency condition.
- **Bricks:** PhysLib CPTP/Choi; `HermitianMat` CFC.
- **Gate:** `lindblad_generator_CP` kernel-pure.

## Wave 2 — structure theorem (trace preservation + canonical form)
- **Goal:** `Tr ℒ(ρ) = 0` (trace preservation); the canonical Hamiltonian-vs-dissipator decomposition; gauge freedom of the jump operators. **Verdict: reachable.**
- **Why:** the structural backbone (the "GKSL form") downstream constructions cite.
- **Bricks:** W1; Mathlib trace + Hermitian structure.
- **Gate:** `gksl_trace_preserving` + `gksl_canonical_form`, kernel-pure.

## Wave 3 — Markovian semigroup + contractivity
- **Goal:** `Λ_t = e^{tℒ}` (HermitianMat CFC-exp); the semigroup law `Λ_t ∘ Λ_s = Λ_{t+s}`; trace-distance monotonicity (data-processing under the dynamical map). **Verdict: reachable.**
- **Why:** Markovianity + contractivity are the dynamical guarantees a certificate would invoke.
- **Bricks:** W1/W2; `HermitianMat` exp; project diamond-norm/trace-distance.
- **Gate:** `lindblad_semigroup` + `traceDist_lindblad_monotone`, kernel-pure.

## Wave 4 — concrete certified model
- **Goal:** a damped two-level / vibrational-relaxation model instantiating the generator, with a **certified exponential decay envelope** (rational-enclosure corollary, no floating-point). **Verdict: reachable.**
- **Why:** a worked, falsifiable instance that grounds the abstract substrate.
- **Bricks:** W1–W3; `expNeg_enclosure`.
- **Gate:** `dampedTwoLevel_decay_envelope` with a `norm_num`-backed bound, kernel-pure.

## Sequencing
W1 (generator) → W2 (structure) → W3 (semigroup) → W4 (model). Independent of 6BA/6BB/6BD; the fastest chemistry phase (PhysLib does the most here).

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D10 §open-systems row staged for first-lift; roadmap status updated.
