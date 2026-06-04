# Phase 6AM — Adopt PhysLib as the quantum-information foundation (DPI / Lieb / SSA / REE)

**Status: REVISED 2026-06-04 — DIRECTION CHANGED. Do NOT hand-roll DPI / Lieb concavity / SSA / REE.**

> **⚠️ AGENTS IN FLIGHT — READ THIS FIRST.** An earlier draft of this phase planned to build the
> data-processing inequality (DPI) from scratch (vendor-in operator concavity of log → construct the
> relative modular operator → discharge joint convexity → REE). **That plan is SUPERSEDED.** The entire
> cluster is already proven, complete and kernel-clean, in **PhysLib** (`leanprover-community/physlib`,
> arXiv:2510.08672), which is pinned to **Mathlib v4.29.1 / 5e932f97 — our exact toolchain pin**. Do not
> reinvent any of it. This phase is now: *adopt PhysLib and bridge to it.*

## What PhysLib already provides (verified complete, 0 axiom)

| PhysLib module | content | thms | sorry |
|---|---|---|---|
| `QuantumInfo/Finite/Entropy/DPI.lean` | **data-processing inequality** (sandwiched-Rényi, strong form) | 45 | 0 |
| `QuantumInfo/Finite/Entropy/SSA.lean` | **strong subadditivity** | 34 | 0 |
| `…/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean` | **Lieb / Lieb–Ando trace concavity** | 6 | 0 |
| `…/TraceInequality/GeneralizedPerspectiveFunction.lean` | **operator perspective** (the joint-convexity route) | 4 | 0 |
| `…/TraceInequality/LownerHeinzTheorem.lean`, `JensenOperatorInequality*.lean` | operator monotone / operator Jensen | — | 0 |
| `QuantumInfo/Finite/Entropy/VonNeumann.lean` | von Neumann entropy | 18 | 0 |
| `QuantumInfo/Finite/Entropy/Relative.lean` | quantum relative entropy | 51 | 1 |
| `QuantumInfo/Finite/ResourceTheory/FreeState.lean` | **separable / free-state framework** (the REE substrate) | 33 | 0 |
| `QuantumInfo/Finite/Distance/{Fidelity,TraceDistance}.lean`, `Entanglement.lean`, `Capacity.lean` | fidelity, trace distance, entanglement measures, capacity | — | — |

**Consequence:** the "genuine walls" the entropy work previously deferred — DPI, strong subadditivity, and
the relative entropy of entanglement (REE, `inf` over the separable set) — are **not walls**: PhysLib has DPI,
SSA, and the free-state/separable framework already. The remaining content is **interoperation**, not proof.

## The actual work: adopt + bridge

The existing in-repo QI substrate (`QuantumNetwork/*`: diamond/fidelity/entropy/negativity) is built on raw
**Kraus families** (`Fin m → Matrix`); PhysLib is built on `MState` / `CPTPMap`. The work is to connect them.

### Wave 1 — add PhysLib as a project dependency
- Add `require Physlib` to `lean/lakefile.toml` (git `leanprover-community/physlib`). It is already on the
  Mathlib v4.29.1 / 5e932f97 pin, so there is **no toolchain/pin conflict** — do NOT bump the pin.
- `lake build` clean with PhysLib available. Confirm `#print axioms` on a sample PhysLib DPI theorem is
  kernel-pure `{propext, Classical.choice, Quot.sound}`.
- **Gate:** PhysLib imports resolve; library builds clean.

### Wave 2 — Kraus ↔ MState bridge *(the real LOE)*
- Provide the translation between the repo's Kraus-family channels / density matrices and PhysLib's
  `CPTPMap` / `MState`, so existing in-repo objects can be fed to PhysLib's DPI/SSA/entropy theorems and
  PhysLib results can be read back as statements about the repo's representation.
- **Gate:** a round-trip bridge lemma (repo channel → `CPTPMap` → repo) + the matching state bridge,
  kernel-pure; one worked example feeding a repo channel into a PhysLib entropy theorem.

### Wave 3 — consume PhysLib for the downstream goals
- Discharge the previously-deferred targets by consuming PhysLib **by FQN** through the Wave-2 bridge:
  DPI for the repo's channels, strong subadditivity, relative-entropy monotonicity, and the
  relative-entropy-of-entanglement via the free-state framework. State the repo-facing corollaries.
- **Gate:** DPI / SSA / REE corollaries in the repo's representation, each backed by a PhysLib FQN.

### Wave 4 — (optional, longer-term) substrate migration
- Where it reduces maintenance, migrate the ad-hoc in-repo QI substrate (diamond/fidelity/entropy/negativity)
  onto PhysLib's `MState`/`CPTPMap` rather than maintaining a parallel formalization. This is a deliberate,
  incremental decision per module — not required to land Waves 1–3. Leave dual + bridged where migration cost
  exceeds benefit.

## Standing invariants
Kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (Invariant #15); no
`native_decide`; no `maxHeartbeats` in proof bodies; do **not** bump the Mathlib pin; never push.

## Sequencing
W1 (dependency add — small) → W2 (the bridge, the real work) → W3 (consume, ships the previously-walled
results) → W4 (optional migration, per-module, later). Start at W1; it unblocks everything.

## Note for coordination
Several adjacent phases (entropy/entanglement strengthening; channel-composition substrate, Phase 6AN W1)
overlap PhysLib's `Distance.lean` / `Entropy/*` — **check PhysLib before proving any QI lemma from scratch.**
The previous from-scratch DPI/modular-operator plan is retained only in version history; do not resurrect it.
