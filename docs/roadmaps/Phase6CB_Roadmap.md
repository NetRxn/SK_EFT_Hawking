# Phase 6CB — Acoustic / Phononic Band Structure & Gaps

**Status: PLANNED (authorized 2026-06-29).** Bloch–Floquet band theory for a periodic acoustic/elastic medium and a **certified band-gap existence theorem** for a concrete phononic crystal. Clean whitespace (no Bloch/Floquet for acoustics in any prover). Distinct phase in the `6C*` materials series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** PhysLib `CondensedMatter/TightBindingChain/Basic.lean` — the band-model template (`hamiltonian_energyEigenstate` TISE, `BrillouinZone`, `energyEigenvalue`, `energyEigenstate_orthogonal`); Mathlib `Analysis.InnerProductSpace.Rayleigh` — `LinearMap.IsSymmetric.hasEigenvalue_iSup/iInf_of_finiteDimensional` (**extremal** eigenvalue only); project `QuantumNetwork/NumericalBounds.expNeg_enclosure` (rational enclosure).
- **Absent → build:** `Floquet` (0 in PhysLib); the acoustic Bloch operator; the **band-gap** theorem. **Key nuance (verified):** the PhysLib TB model is a *single* `E₀−2t·cos(ka)` band with **no gap** — a gap requires a **≥2-band (diatomic / two-sublattice) acoustic chain** (gap between acoustic & optical branches). The **k-th-eigenvalue Courant–Fischer** is also new (Mathlib has only extremal Rayleigh).
- **New content:** the diatomic mass-spring acoustic Bloch operator (≥2 bands); band-gap existence via min-max + the new Courant–Fischer; certified gap enclosure.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the band/gap *theorems* are Lean-verified; the physical-crystal identification stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual acoustics publication + flagship scope).

**Bundle target:** **D11** (authorized 2026-06-29; §phononic), shared with 6CA/6CD/6CE. A Stage-1 option (decide at first-lift): evaluate a standalone "first verified phononic band gap" headline letter. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — acoustic Bloch operator
- **Goal:** a periodic acoustic/elastic operator (mass-spring / Helmholtz lattice); Bloch–Floquet spectrum + Brillouin zone (PBC), porting the TB template. **Verdict: reachable** — structural port of a proven model.
- **Why:** the spectral object whose gaps the phase certifies.
- **Bricks:** PhysLib `TightBindingChain`; Mathlib self-adjoint spectral theory.
- **Gate:** `acousticBloch_spectrum` (real, bounded-below) kernel-pure.

## Wave 2 — band-gap existence
- **Goal:** min-max (Rayleigh) + k-th-eigenvalue **Courant–Fischer**; a spectral gap `[ω₋, ω₊]` proven for a concrete **diatomic (two-sublattice)** crystal — the gap opens between the acoustic and optical branches (no eigenvalue in the open interval). **Verdict: reachable-moderate.**
- **Why:** the headline result — a *proven* phononic band gap.
- **Bricks:** W1; Mathlib `Rayleigh`; new Courant–Fischer.
- **Gate:** `phononic_band_gap_exists` + falsifier (`∃ mode in (ω₋,ω₊) ⇒ ⊥`), kernel-pure.

## Wave 3 — certified gap enclosure
- **Goal:** interval-arithmetic bounds on the gap edges (`expNeg_enclosure`-style); a rational enclosure usable with no floating-point. **Verdict: reachable.**
- **Why:** turns the existence theorem into a certificate-grade numerical bound.
- **Bricks:** W2; `expNeg_enclosure`.
- **Gate:** `band_gap_rational_enclosure` (`norm_num`-backed) kernel-pure.

## Sequencing
W1 (operator) → W2 (gap existence) → W3 (enclosure). Independent of 6CA/6CC/6CD/6CE; one of the two fast materials phases (with 6CD).

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D11 §phononic row staged for first-lift; roadmap status updated.
