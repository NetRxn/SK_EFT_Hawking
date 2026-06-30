# D10 Discharge Roadmap — discharging the disclosed tracked-Props of the comp-chem / open-system substrate

**Status: ACTIVE (opened 2026-06-30).** Source-of-truth for the **discharge `/goal` loop**. Motivated by the
D10 paper's stated "natural next steps" (`papers/D10/paper_draft.tex` §Conclusion): the kernel-verified
foundations of NEGF transport (6BA), DFT (6BB), and Lindblad/GKSL open systems (6BC) ship with a small set of
**disclosed, load-bearing `Prop` hypotheses** (NOT axioms). This roadmap tracks discharging them so the
headline theorems become unconditional (or documents an honest wall). A paper should not advertise next steps
it could discharge; this loop does the discharging.

## Non-negotiables (every wave)
- Kernel-pure `{propext, Classical.choice, Quot.sound}`; zero new `sorry`/`axiom`/`native_decide`; no
  `maxHeartbeats` in proof bodies (decompose into `have`). Verify each headline with `lean_verify`.
- **No new project-local axiom without explicit user sign-off** (Pipeline Invariant #15). A disclosed `Prop`
  with a discharge note is the fallback, never an axiom.
- **Per-Prop budget ≈ ≤ 500 LOC.** If a single discharge clearly exceeds that, ship the reusable infrastructure
  it produced and **leave the Prop disclosed** (documented here) rather than grinding — that is a legitimate
  stop, recorded, not a silent cap.
- MCP-first proof loop (`lean-lsp`); read the relevant `Lit-Search/Phase-*` / Mathlib / PhysLib source
  **directly** (no sub-agent depth-reads for hard proofs).
- Update this roadmap's per-wave **Status** every brick; never push (user action).

## Disclosed-Prop inventory (what this loop discharges)
| Prop | Where | Theorem it gates | Wave |
|---|---|---|---|
| `hkin` (kinetic ess-s.a.) | `MolecularHamiltonian.lean` | `molecularHamiltonian_essSelfAdjoint` | W1✓+W2 |
| `hrel` (Coulomb rel-bound `a<1`, Hardy) | `MolecularHamiltonian.lean` | `molecularHamiltonian_essSelfAdjoint` | W3 |
| `hreal` (CPTP Kraus realization of `e^{tℒ}`) | `LindbladSemigroup.lean` | `traceDist_lindblad_monotone` | W4 |
| `DensityVariational.bddBelow` / `LevyLiebData.fiber_bddBelow` | `HohenbergKohnVariational.lean`, `LevyLiebFunctional.lean` | `hohenberg_kohn_variational`, `levyLieb_*` | W5 |
| (`hpot` — potential symmetric) | — | — | **DONE** (6BB W5, `molecularPotentialOperator_isSymmetric`) |

---

## W1 — Essential-self-adjointness criterion (✅ DONE 2026-06-30, commit `66e0a20c`)
- **Deliverable:** `isSelfAdjoint_closure_of_dense_range` in `lean/SKEFTHawking/KineticEssentialSelfAdjoint.lean`
  — a densely-defined symmetric `S` with `S ± iμ` having DENSE range is essentially self-adjoint (`S.closure`
  self-adjoint). Plus `isClosed_range_sub_I_smul_of_isClosed` (Wave-1 closed-range argument generalized from
  self-adjoint to closed-symmetric). Kernel-pure; in root.
- **Substrate used:** Wave-1 deficiency lemmas (`MolecularHamiltonian.lean`) + PhysLib
  `IsUnbounded.adjoint_closure_eq_adjoint`, `isSymmetric_iff_le_adjoint`, `isUnbounded_of_dense_of_isSymmetric`,
  Mathlib `IsClosable.{closure_isClosed,closure_mono}`.
- **Consumed by:** W2 (the kinetic-operator dense-range result applies this criterion).

## W2 — `hkin`: kinetic operator dense range, via the Fourier multiplier
- **Goal:** `IsSelfAdjoint (molecularSystem N m hm nuclei).kineticOperator.closure` (the disclosed `hkin`),
  then drop `hkin` from `molecularHamiltonian_essSelfAdjoint` (new unconditional-in-`hkin` apex).
- **Route:** (a) PhysLib's `kineticOperator = c • momentumSqOperator` ⟹ reduce via
  `IsEssentiallySelfAdjoint.real_smul` to `momentumSqOperator`; (b) **dense range** `ran(momentumSqOperator ± i) ⊇
  Schwartz`: for `g ∈ 𝓢`, `f := fourierMultiplier (|p|²·c ± i)⁻¹ g ∈ 𝓢` solves `(momentumSq ± i)f = g` — the
  inverse symbol `(|p|²c±i)⁻¹` is a bounded temperate multiplier (Schwartz-preserving); (c) apply **W1** criterion.
- **Substrate:** Mathlib `SchwartzMap.laplacian_eq_fourierMultiplierCLM` (`Δ = −(2π)²·mult ‖·‖²`, ALREADY in
  Mathlib), `fourierTransformCLE`/`fourierMultiplierCLM`; PhysLib `momentumSqOperator`, `IsEssentiallySelfAdjoint`.
  **The PhysLib-momentum ↔ Mathlib-Fourier bridge is the hard, from-scratch step** (no Plancherel-unitary needed —
  the dense-range route avoids it). **Risk:** at/over budget — if the bridge balloons, ship partial infra + keep
  `hkin` disclosed.
- **Status:** ⏳ NEXT. W1 foundation done.

## W3 — `hrel`: Coulomb relative bound, via Hardy's inequality
- **Goal:** `IsRelBounded kineticOperator.closure potentialOperator a b` with `a < 1` (the disclosed `hrel`),
  then drop `hrel`.
- **Route:** Hardy's inequality `∫_{ℝ³} |u|²/|x|² ≤ 4 ∫ |∇u|²` ⟹ each Coulomb term `‖V_C u‖ ≤ ε‖Δu‖ + C_ε‖u‖`
  with `ε → 0` ⟹ `a < 1`.
- **Substrate:** **Hardy is absent from Mathlib AND PhysLib (verified 2026-06-30)** — fully from-scratch
  (integration-by-parts on ℝ³; PhysLib v4.30.0 distributional-Laplacian fundamental-solution lemmas #1169–#1175
  MAY help the Green's-function step, behind the bump). **Highest budget risk** — if Hardy alone exceeds ~500
  LOC, ship it as its own infrastructure lemma set and keep `hrel` disclosed.
- **Status:** ⏳ planned.

## W4 — `hreal`: CPTP semigroup, via the matrix Lie–Trotter product
- **Goal:** `e^{tℒ}` (the vectorized propagator) is CPTP, hence realized by a Kraus channel — discharge the
  `hreal` hypothesis of `traceDist_lindblad_monotone` (and ideally drop it).
- **Route:** split `ℒ = ℒ_jump + ℒ_drift` (`ℒ_jump(ρ)=Σ L_k ρ L_k†` CP via W1-6BC `lindblad_generator_CP`;
  `ℒ_drift(ρ)=e^{-tΓ}ρe^{-tΓ†}` conjugation, CP); Lie–Trotter `e^{t(ℒ_jump+ℒ_drift)} = lim_n (e^{(t/n)ℒ_drift}
  e^{(t/n)ℒ_jump})^n`; each factor CP ⟹ product CP ⟹ limit CP (CP closed under limits).
- **Substrate:** **matrix Lie–Trotter product formula is absent from Mathlib (verified 2026-06-30)** —
  from-scratch (or via `Matrix.exp` series + finite-dim limit). Finite-dimensional, so more tractable than
  W2/W3 but still real. Reuses 6BC `lindblad_generator_CP`, `MatrixMap.of_kraus_CP`, project `krausMap`/CPTP.
- **Status:** ⏳ planned.

## W5 — DFT structural semiboundedness Props (`bddBelow`, `fiber_bddBelow`)
- **Goal:** discharge the structural `BddBelow` fields of `DensityVariational` / `LevyLiebData` from the Wave-1
  semibounded self-adjoint Hamiltonian (real spectrum bounded below).
- **Route:** needs eigenvalue / spectral-measure theory connecting the self-adjoint `T̄ + V` (Wave-1) to a
  ground-state energy infimum. **This is the natural trigger for the deliberate PhysLib v4.30.0 bump** (its
  spectral-theory commits #1218/#1239) — to be done on a **clean branch, blast-radius-managed** (test
  StatMech/QuantumInfo + the parallel public agent, as for the #1120 bump). Gate on the bump decision.
- **Status:** ⏸ gated on the v4.30.0 bump (user sign-off).

## W6 — Transport ↔ open-system synthesis (Markovian quantum transport) — *feature, not a discharge*
- **Goal:** the D10 §Conclusion's "connect the transport and open-system layers" — a verified treatment linking
  the NEGF steady-state (6BA) to the Lindblad dynamical map (6BC) (e.g. a Lindblad-driven steady-state current).
- **Status:** ⏳ planned (lowest priority; new synthesis, opens after W2–W4).

---

## Sequencing & Definition of Done
**Order:** W2 (hkin-Fourier) → W4 (hreal-Trotter, finite-dim, likely next-tractable) → W3 (hrel-Hardy, hardest)
→ W5 (gated on bump) → W6 (feature). Each wave independent; do the tractable ones first.

**Per-wave DoD:** the disclosed `Prop` is discharged (theorem made unconditional, or a strictly-stronger
unconditional companion shipped) OR a documented budget-wall recorded here; module builds clean + kernel-pure
(`lean_verify`); root imports; **the D10 paper (`papers/D10/paper_draft.tex`) updated** to state the now-stronger
result and the supersession ledger noted; `validate.py` green.

**Loop DoD (`/goal` exit):** W2 + W4 discharged (or honestly walled-and-documented) AND the D10 paper reflects
the result AND `lake build` + ExtractDeps green AND `validate.py` prints ALL CHECKS PASSED in the transcript AND
a fresh-context `skeft-qa:adversarial-reviewer` ran with ZERO BLOCKER ZERO MAJOR. (W3 attempted; W5 gated on the
bump decision; W6 if budget remains.)
