/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 4) — system-line synthesis on the two-qubit register

Connects the two-qubit gate semantics (`CliffordTGate2.lean`) to the **shipped, verified** single-qubit
KMM exact synthesis (`KMM.kmmReduce`). The realizability transport `Gate2.embedFst_interp` becomes
concrete: an ℤ[ω][1/√2]-realizable single-qubit operator `M` is realized on the system line of the
(system + ancilla) register, as `M ⊗ I`, by a two-qubit Clifford+T word of the **same KMM length bound**
`N₃ + 4·denExp(|M₀₀|²)` (= O(sde), exponent-1 in `log(1/ε)`). This is the building block the ancilla
circuit uses for every system-line operation; the entangling/ancilla structure is the remaining brick.

## Headlines

  * `embedFst_kmmReduce_interp` — `interp2 ((kmmReduce M).map onFst) = embedFst M` (the system-line
    Gate2-word exactly realizes `M ⊗ I`), via `embedFst_interp` + the shipped `KMM.kmmReduce_correct`.
  * `embedFst_kmmReduce_length` — that word has length `≤ N₃ + 4·denExp(|M₀₀|²)` (`length_map_onFst`
    + the shipped `KMM.kmmReduce_length_bound`): the single-qubit KMM length bound transports onto the
    two-qubit register at **no length cost**.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` in this file's own proofs, and the `KMM.kmmReduce` substrate it consumes
  is kernel-pure since Phase 6AO Track 3 eliminated all four former `native_decide` sites.
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate2
import SKEFTHawking.FKLW.RossSelinger.KMM
import SKEFTHawking.FKLW.RossSelinger.CliffordBase

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open Gate2

attribute [local instance] KMM.nonempty_kmmReduction

/-- **System-line realization.** An ℤ[ω][1/√2]-realizable single-qubit `M` is realized on the system
line of the two-qubit register, as `M ⊗ I`, by the two-qubit Clifford+T word `(kmmReduce M).map onFst`:
`interp2 ((kmmReduce M).map onFst) = embedFst M`. (`embedFst_interp` + `KMM.kmmReduce_correct`.) -/
theorem embedFst_kmmReduce_interp (M : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)
    (hM : KMM.IsCliffordTRealizable M) :
    interp2 ((KMM.kmmReduce M).map Gate2.onFst) = embedFst M := by
  rw [← embedFst_interp, KMM.kmmReduce_correct M hM]

/-- **System-line length bound transports at no cost.** The two-qubit word realizing `M ⊗ I` has the
single-qubit KMM length `≤ N₃ + 4·denExp(|M₀₀|²)` (= O(sde), the exponent-1 `O(log 1/ε)` scaling).
(`length_map_onFst` + `KMM.kmmReduce_length_bound`.) -/
theorem embedFst_kmmReduce_length (M : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)
    (hM : KMM.IsCliffordTRealizable M) :
    ((KMM.kmmReduce M).map Gate2.onFst).length
      ≤ KMM.N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (M 0 0)) := by
  rw [length_map_onFst]
  exact KMM.kmmReduce_length_bound M hM

/-- **Single-qubit → two-qubit realizability transport.** An ℤ[ω][1/√2]-realizable single-qubit `M`
makes `M ⊗ I` two-qubit Clifford+T-realizable, witnessed by `(kmmReduce M).map onFst`. -/
theorem embedFst_isRealizable (M : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)
    (hM : KMM.IsCliffordTRealizable M) :
    Gate2.IsRealizable (Gate2.embedFst M) :=
  ⟨(KMM.kmmReduce M).map Gate2.onFst, embedFst_kmmReduce_interp M hM⟩

/-- **System-line synthesis with the O(log 1/ε) length budget.** An ℤ[ω][1/√2]-realizable single-qubit
`M` makes `M ⊗ I` realizable on the two-qubit register *within length* `N₃ + 4·denExp(|M₀₀|²)` — the
single-qubit KMM bound (= O(sde), exponent-1 `O(log 1/ε)`). This is the length-tracked base case the
ancilla circuit composes (via `IsRealizableWithin.mul`) for its system-line operations. -/
theorem embedFst_kmmReduce_realizableWithin (M : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2)
    (hM : KMM.IsCliffordTRealizable M) :
    Gate2.IsRealizableWithin (Gate2.embedFst M)
      (KMM.N₃ + 4 * ZOmegaSqrt2.denExp (ZOmegaSqrt2.normSq (M 0 0))) :=
  ⟨(KMM.kmmReduce M).map Gate2.onFst, embedFst_kmmReduce_interp M hM, embedFst_kmmReduce_length M hM⟩

end SKEFTHawking.RossSelinger
