/-
# Phase 5q.H — THE `hker` AMBIENT-PIN GATE: pinning `amb` does NOT restore geometric content.

Round-12 spec 1 (`PinPlusResidualGate`, FROZEN) rules that a `KTSharpnessSupplyConstr` /
`KTSharpnessSupplyGeo` claim is construction progress ONLY IF `amb x hx` is the tethered witness's
`TopCat.of b.W`, "checked by DATA INSPECTION; the statement shape is conclusion-strength (G12-1) and
can never enforce this". Its kernel backing
(`PinPlusResidualGate.nonempty_dualSpinConstruction_iff_thirtytwo_dvd`) is stated at the **trivial**
ambient `PUnit`, which leaves open the natural repair: *pin the ambient to the genuine `b.W` and the
supply becomes a real geometric obligation.*

**This module refutes that repair.** The conclusion-equivalence holds at **EVERY** ambient `W` —
including the genuine tethered bordism total space — so pinning `amb` buys exactly nothing.

## Why (the structural reason, and why no `amb`-pin can help)

`SmoothSpinManifold4` (`SpinRokhlinInterface.lean:62`) is **pure lattice data**: `rank`, `form`,
`even_unimod`, `topo`. It carries **no underlying space**. In `DualSpinFromW` the topological half
(`Vspace`, `ιV`, `hclosed`) and the arithmetic half (`Vspin`, `hdouble`) are therefore **disconnected
by construction** — nothing in the type relates the embedded space to the lattice claimed to be its
intersection form. Consequently the topological half can be satisfied by the EMPTY submanifold (whose
inclusion into any `W` is a closed embedding) while the arithmetic half is supplied by the σ-onto
engine `spinOfSigMul16`, for any `W` whatsoever.

**Consequence for the `hker` lane (the honest scope of the deep atom).** `hker`'s geometric content
cannot be carried by any shape built over `SmoothSpinManifold4` + a bare embedded `Vspace`: the
interface is too weak to *express* "V is the `w₁(W)`-dual submanifold AND `Vspin` is its intersection
lattice". A genuine `hker` discharge needs an interface that carries the submanifold and DERIVES its
lattice (the `SpinSigmaAtomPkg` pattern: fundamental class + `H²` basis + Poincaré duality on an
actual manifold), plus the `w₁`-duality tie. That is the real work; `amb`-pinning is not a step toward
it, and this module is the kernel record of that.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTDualSpinSubmanifold
import SKEFTHawking.PinPlusResidualGate
import SKEFTHawking.PinPlusCharPairEmptySourceRealization

namespace SKEFTHawking.PinPlusKTHkerAmbPinGate

open SKEFTHawking.PinPlusKTDualSpinSubmanifold
open SKEFTHawking.PinPlusResidualGate
open SKEFTHawking.PinPlusCharPairEmptySourceRealization

/-! ## §1. The empty `w₁`-dual: the topological half of `DualSpinFromW` is free at every ambient. -/

/-- **The empty submanifold closed-embeds into ANY space.** The topological half of `DualSpinFromW`
(`Vspace`, `ιV`, `hclosed`) imposes no constraint whatsoever: `PEmpty` maps into every `W` by a closed
embedding (empty range is closed, injectivity is vacuous). This is the lever that makes the ambient
pin worthless. -/
theorem isClosedEmbedding_empty (W : Type) [TopologicalSpace W] [T2Space W] :
    Topology.IsClosedEmbedding (fun x : PEmpty.{1} => (isEmptyElim x : W)) :=
  (continuous_of_isEmpty _).isClosedEmbedding (fun x => isEmptyElim x)

/-! ## §2. The refutation: conclusion-equivalence at EVERY ambient. -/

/-- **THE AMBIENT PIN IS WORTHLESS** — for **every** topological space `W`, including the genuine
tethered bordism total space `b.W` that round-12 spec 1 demands, `DualSpinFromW W sigM` is inhabited
**iff** `32 ∣ sigM` — stated for HAUSDORFF `W`, which is exactly the honest case: faithfulness leg 1
(`nonhausdorff-bordism-collapse`) already forces every bordism carrier in this phase to be `T2`. So the
datum carries exactly the strength of its own conclusion at every ambient,
and pinning `amb` to the honest `b.W` adds nothing.

Forward: the banked `DualSpinFromW.thirtytwo_dvd` (Rokhlin on `Vspin` + the σ-doubling). Backward: the
empty submanifold (§1) supplies the whole topological half at any `W`, and `spinOfSigMul16` supplies a
GENUINE `SmoothSpinManifold4` of signature `16·m` for the arithmetic half — the two halves never have
to meet, because `SmoothSpinManifold4` has no carrier to meet on. -/
theorem nonempty_dualSpinFromW_iff_thirtytwo_dvd (W : Type) [TopologicalSpace W] [T2Space W]
    (sigM : ℤ) :
    Nonempty (DualSpinFromW W sigM) ↔ (32 : ℤ) ∣ sigM := by
  constructor
  · rintro ⟨d⟩
    exact d.thirtytwo_dvd
  · rintro ⟨m, hm⟩
    refine ⟨{ Vspace := PEmpty.{1}
              Vtop := inferInstance
              ιV := ⟨fun x => isEmptyElim x, continuous_of_isEmpty _⟩
              hclosed := isClosedEmbedding_empty W
              Vspin := spinOfSigMul16 m
              hdouble := ?_ }⟩
    rw [spinOfSigMul16_sig, hm]
    ring

/-- **The refutation as a FAMILY** — the shape the `hker` lane would actually consume. For ANY index
type `ι` (in the lane: the Brown-kernel elements), ANY ambient assignment `amb : ι → Type` (in the
lane: `fun x => b.W` of the genuine tethered witness — the strongest pin round-12 spec 1 could ask
for), and ANY signature assignment `sg : ι → ℤ`, a family of dual-spin data exists **iff** the `hfwd`
conclusion holds pointwise. The ambient is universally quantified, so no choice of pin escapes. -/
theorem dualSpinFamily_iff_pointwise_thirtytwo_dvd {ι : Type*} (amb : ι → Type)
    [∀ i, TopologicalSpace (amb i)] [∀ i, T2Space (amb i)] (sg : ι → ℤ) :
    (∀ i, Nonempty (DualSpinFromW (amb i) (sg i))) ↔ (∀ i, (32 : ℤ) ∣ sg i) :=
  ⟨fun h i => (nonempty_dualSpinFromW_iff_thirtytwo_dvd (amb i) (sg i)).mp (h i),
   fun h i => (nonempty_dualSpinFromW_iff_thirtytwo_dvd (amb i) (sg i)).mpr (h i)⟩

/-- **The structural root, recorded as a theorem**: `SmoothSpinManifold4` has no carrier, so the
`Vspin` half of `DualSpinFromW` is entirely independent of the embedded `Vspace` half — one may swap
in ANY lattice of the right signature without touching the embedding. Concretely: at a fixed ambient
and a fixed signature, the datum's topological half can be the empty submanifold while `Vspin` ranges
over the whole σ-onto family. -/
theorem dualSpin_arith_independent_of_embedding (W : Type) [TopologicalSpace W] [T2Space W]
    (m : ℤ) :
    Nonempty (DualSpinFromW W (32 * m)) ∧ (spinOfSigMul16 m).sig = 16 * m :=
  ⟨(nonempty_dualSpinFromW_iff_thirtytwo_dvd W (32 * m)).mpr ⟨m, rfl⟩, spinOfSigMul16_sig m⟩

end SKEFTHawking.PinPlusKTHkerAmbPinGate
