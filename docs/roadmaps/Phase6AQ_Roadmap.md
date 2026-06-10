# Phase 6AQ — device-characterization envelope completion (readout-window bounds)

**Status: OPEN 2026-06-10.** Successor to 6AP (closed 2026-06-10). Scope: two small waves
completing the device-characterization envelope family where textbook/published math is still
missing from the substrate. The family today bounds *gate* performance from coherence data
(coherence-limited fidelity ceiling; composed-gate fidelity; n-qubit Pauli/thermal diamond
distances); the missing member bounds *readout* performance from the same universally-stated
parameters. Per the going-forward origination rule: textbook/published math lives HERE
(defensive-pub), at full strength, first try.

**Invariants (unchanged):** kernel-pure (`{propext, Classical.choice, Quot.sound}`), zero sorry,
no project-local axioms (#15), no `maxHeartbeats` in proof bodies (#10), preemptive-strengthening
checklist applied to every statement before writing it. Gate-strength discipline per the 6AO/6AP
headers: no vacuous/definitional-only deliverables; two-layer honesty (formula Lean-verified;
device-identification/modeling step literature-cited) stated in module headers wherever it
applies — the established `plobBound`/coherence-ceiling posture.

## W1 — readout-window relaxation envelope (`ReadoutRelaxationBound.lean` or NumericalBounds ext.)

- **What:** the assignment-error floor imposed by relaxation during a finite measurement window:
  for window `t ≥ 0` and relaxation time `T1 > 0`, the excited-state decay probability
  `p_decay = 1 − exp(−t/T1)` lower-bounds the (model-level) excited-branch misassignment, with
  the averaged-assignment form carrying the model prefactor (exact constant fixed at proof time —
  state the strongest cleanly-provable form, per the 6AP W3 precedent). Monotonicity (increasing
  in `t`, decreasing in `T1`), endpoints (`t = 0` ⇒ 0; `t → ∞` ⇒ 1), and the rational enclosure
  corollary via 6AP's `expNeg_enclosure` (both endpoints rational at rational `t/T1` — rigorous
  rational brackets without floating-point `exp`).
- **Why now:** completes the characterization-envelope family — coherence data bounds gates
  (existing ceiling), the same data plus the readout window bounds measurement. Textbook content
  (dispersive-readout literature, Gambetta/Walter class); absent from the substrate and from
  Mathlib (verify by search before writing).
- **Two-layer posture:** the decay formula + monotonicity + enclosure are the Lean-verified
  layer; the identification with device assignment error (QND-ideal, no re-excitation, decay-
  flips-outcome model) stays literature-cited in the module header — never conflated.
- **Gate:** kernel-pure; full-strength statements (no worked-instance-only shipping); the
  enclosure corollary usable at rational operating points; strengthening checklist applied.

## W2 (stretch) — thermal-population assignment floor

- **What:** the thermal-excitation floor on assignment error: excited-state thermal occupancy
  `p_th = 1/(1 + exp(ℏω/kT))` (two-level Boltzmann/detailed-balance form) as a temperature-indexed
  floor, with monotonicity in `T` (and in `ω`), endpoints (`T → 0+` ⇒ 0; high-`T` ⇒ 1/2), and a
  rational-enclosure corollary via `expNeg_enclosure`.
- **Substrate:** the existing PhysLib `Temperature` bridge + FDT/quantum-floor modules (6AM W4 /
  6AN W4 family) — reuse, don't re-derive.
- **Two-layer posture:** occupancy formula Lean-verified; the assignment-floor reading (thermal
  population mistaken for signal under the stated readout model) literature-cited.
- **Gate:** kernel-pure, full strength; if the cleanly-provable form requires more PhysLib
  thermal substrate than exists, descope THIS wave honestly (ship W1 alone) rather than shipping
  a weakened statement — stretch means stretch.

## Closure

- `lake build` + `lake build SKEFTHawking.ExtractDeps` clean; `validate.py` green; counts +
  Inventory refreshed; root `SKEFTHawking.lean` imports; Stage-13-style strengthening review of
  new statements; roadmap status updated.
