# Phase 6CD — Non-Hermitian Topology / Exceptional Points

**Status: PLANNED (authorized 2026-06-29).** Non-Hermitian Bloch Hamiltonians, exceptional-point (EP) degeneracies via Jordan-block coalescence, and PT-symmetry / real-spectrum criteria. Clean physics whitespace. Distinct phase in the `6C*` materials series.

> **⚠️ CHECK PhysLib FIRST.** PhysLib `Mathematics/SchurTriangulation.lean` (`A = U·T·U†` over ℂ) is the home for defective/non-normal analysis. Project `CGLTransform`/`HigherOrderSK`/`SecondOrderSK` supply the dissipative SK-EFT algebra. Mathlib lacks matrix Jordan Normal Form (`loogle JordanNormalForm` → empty) — **build the finite-dim EP/Jordan primitive** (a fast finite-dim construction; Isabelle AFP's JNF is a reference cross-check). "Absent from Mathlib" is *not* a park reason.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D11** (authorized 2026-06-29; §non-Hermitian), shared with 6CA/6CB/6CE. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — non-Hermitian Bloch + exceptional point
- **Goal:** a non-Hermitian 2-band Bloch Hamiltonian on Schur; the **exceptional point** = simultaneous eigenvalue + eigenvector coalescence (a defective Jordan block); the finite-dim EP/JNF primitive. **Verdict: reachable** — finite-dim linear algebra on Schur.
- **Why:** EPs are the defining feature of non-Hermitian band physics; the JNF primitive is reusable infrastructure.
- **Bricks:** PhysLib `SchurTriangulation`; project dissipative algebra.
- **Gate:** `exceptional_point_defective` (algebraic mult > geometric mult at the EP) kernel-pure.

## Wave 2 — PT-symmetry + EP order
- **Goal:** the PT-symmetric real-spectrum criterion; EP-order classification (EP2/EP3); the square-root spectral splitting near an EP. **Verdict: reachable.**
- **Why:** PT-symmetry breaking is the experimentally salient transition; EP order sets the sensing response.
- **Bricks:** W1; characteristic-polynomial discriminant.
- **Gate:** `pt_symmetric_real_spectrum_iff` (biconditional) kernel-pure.

## Wave 3 — skin effect + certified EP-proximity bound
- **Goal:** (optional) non-Hermitian winding / the skin effect; a certified EP-proximity bound (enclosure on the spectral-gap closing). **Verdict: reachable.**
- **Why:** the skin effect is the bulk topological signature; the proximity bound is the certificate-grade output.
- **Bricks:** W1/W2; `expNeg_enclosure`.
- **Gate:** `ep_proximity_enclosure` (`norm_num`-backed) kernel-pure.

## Sequencing
W1 (EP/JNF primitive) → W2 (PT + order) → W3 (skin/proximity). Independent of 6CA/6CB/6CC/6CE; one of the two fast materials phases (with 6CB).

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; the finite-dim JNF/EP primitive flagged as Mathlib-PR-eligible; D11 §non-Hermitian row staged for first-lift; roadmap status updated.
