/-
# Phase 5q.H (W-A arm 4) — the relative-MV cover of the punctured product `(M×I) ∖ x`

Route-B infrastructure for the terminal interior local-Künneth nonvanishing
`crossHloc ([M]|_σ) ≠ 0` (equivalently `[prismOp graphHom z] ≠ 0`). At an interior point
`x = (σ,t)` the puncture complement `{x}ᶜ ⊆ M×I` is the union of the two open pieces

  `puncU x = M × (I∖{t}) = {p | p.2 ≠ x.2}`,   `puncV x = (M∖σ) × I = {p | p.1 ≠ x.1}`,

with `puncU x ∪ puncV x = {x}ᶜ` **exactly** (`p ≠ x ⟺ p.1 ≠ σ ∨ p.2 ≠ t`) and
`puncU x ∩ puncV x = (M∖σ) × (I∖{t})`. This is the open cover the in-tree relative Mayer–Vietoris
LES (`SingularRelativeMV`) consumes to compute the punctured-product local homology
`H_{m'+3}(M×I, {x}ᶜ)` from the two pieces — the mod-2-safe route to the nonvanishing that avoids a
general Künneth (the ℤ no-go does not apply to this mod-2 MV).

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the two open pieces** `puncU`, `puncV` and their openness (`isOpen_puncU` needs only that
  `I` is `T1`; `isOpen_puncV` needs `T1Space ↑N`).
* **§2 — the cover identities** `puncU ∪ puncV = {x}ᶜ` and `puncU ∩ puncV = {p | p.1 ≠ σ ∧ p.2 ≠ t}`.
* **§3 — the relative-MV LES** at this cover: the connecting `relMvDelta` and the three exactness
  segments specialised to `(puncU x, puncV x)`, giving
  `H_{m'+3}(M×I, {x}ᶜ) →[δ] H_{m'+2}(M×I, (M∖σ)×(I∖t)) → …` — the exact sequence the interior
  nonvanishing is detected inside.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularRelativeMV

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

noncomputable section

variable {N : TopCat}

/-! ## §1. The two open pieces `puncU = M×(I∖t)`, `puncV = (M∖σ)×I` -/

/-- **The `I`-punctured piece** `M × (I∖{t}) = {p | p.2 ≠ x.2}` of the cylinder. -/
def puncU (x : ↑(cyl N)) : Set ↑(cyl N) := {p | p.2 ≠ x.2}

/-- **The `M`-punctured piece** `(M∖{σ}) × I = {p | p.1 ≠ x.1}` of the cylinder. -/
def puncV (x : ↑(cyl N)) : Set ↑(cyl N) := {p | p.1 ≠ x.1}

/-- `puncU` is open: it is `Prod.snd ⁻¹' {x.2}ᶜ`, and `{x.2}ᶜ` is open in the `T1` interval. -/
theorem isOpen_puncU (x : ↑(cyl N)) : IsOpen (puncU x) := by
  have : puncU x = (fun p : ↑(cyl N) => p.2) ⁻¹' {x.2}ᶜ := by
    ext p; simp [puncU, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [this]
  exact isOpen_compl_singleton.preimage continuous_snd

/-- `puncV` is open (needs `T1Space ↑N`): it is `Prod.fst ⁻¹' {x.1}ᶜ`, and `{x.1}ᶜ` is open. -/
theorem isOpen_puncV [T1Space ↑N] (x : ↑(cyl N)) : IsOpen (puncV x) := by
  have : puncV x = (fun p : ↑(cyl N) => p.1) ⁻¹' {x.1}ᶜ := by
    ext p; simp [puncV, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [this]
  exact isOpen_compl_singleton.preimage continuous_fst

/-! ## §2. The cover identities -/

/-- **The cover is exactly the puncture complement**: `puncU x ∪ puncV x = {x}ᶜ`. A point `p` differs
from `x = (σ,t)` iff it differs in the interval coordinate (`p ∈ puncU`) or the base coordinate
(`p ∈ puncV`). -/
theorem puncU_union_puncV (x : ↑(cyl N)) : puncU x ∪ puncV x = ({x}ᶜ : Set ↑(cyl N)) := by
  ext p
  simp only [puncU, puncV, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h) hp <;> exact h (hp ▸ rfl)
  · intro hp
    by_cases h : p.1 = x.1
    · exact Or.inl (fun h2 => hp (Prod.ext h h2))
    · exact Or.inr h

/-- **The overlap is the doubly-punctured product**: `puncU x ∩ puncV x = (M∖σ) × (I∖t)`. -/
theorem puncU_inter_puncV (x : ↑(cyl N)) :
    puncU x ∩ puncV x = {p : ↑(cyl N) | p.1 ≠ x.1 ∧ p.2 ≠ x.2} := by
  ext p
  simp only [puncU, puncV, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact And.comm

/-! ## §3. The relative-MV LES at the punctured-product cover -/

/-- **The relative-MV connecting map** at the punctured-product cover:
`δ : H_{k+1}(M×I, {x}ᶜ) → H_k(M×I, (M∖σ)×(I∖t))` — the domain is `H_{k+1}(M×I, puncU ∪ puncV)` and
`puncU ∪ puncV = {x}ᶜ` (`puncU_union_puncV`); the target is `H_k(M×I, puncU ∩ puncV)`. This is the
connecting homomorphism whose image the interior local-Künneth class is detected inside. -/
def puncMvDelta [T1Space ↑N] (x : ↑(cyl N)) (k : ℕ) :
    RelativeHomology (puncU x ∪ puncV x) (k + 1) →ₗ[ZMod 2]
      RelativeHomology (puncU x ∩ puncV x) k :=
  relMvDelta (puncU x) (puncV x) (isOpen_puncU x) (isOpen_puncV x) k

/-- **Exactness at `H_{k+1}(M×I, {x}ᶜ)`**: the sum from the pieces `H_{k+1}(M×I, puncU) ×
H_{k+1}(M×I, puncV)` and the connecting `puncMvDelta` are exact — the segment of the relative-MV LES
that expresses which classes of the punctured-product local homology survive `δ`. -/
theorem puncMv_exact_sum [T1Space ↑N] (x : ↑(cyl N)) (k : ℕ) :
    Function.Exact (relMvHomSum (puncU x) (puncV x) (k + 1)) (puncMvDelta x k) :=
  relMv_exact_sum' (puncU x) (puncV x) (isOpen_puncU x) (isOpen_puncV x) k

/-- **Exactness at `H_k(M×I, (M∖σ)×(I∖t))`**: the connecting `puncMvDelta` and the MV diagonal
`relMvHomDiag` are exact — the next segment, controlling the image of `δ` in the overlap homology. -/
theorem puncMv_exact_connecting [T1Space ↑N] (x : ↑(cyl N)) (k : ℕ) :
    Function.Exact (puncMvDelta x k) (relMvHomDiag (puncU x) (puncV x) k) :=
  relMv_exact_connecting' (puncU x) (puncV x) (isOpen_puncU x) (isOpen_puncV x) k

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
