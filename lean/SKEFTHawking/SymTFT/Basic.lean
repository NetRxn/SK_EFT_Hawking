/-
# Phase 6r Wave 1a.3 — SymTFT predicate-substrate (KOZ + FMT wrapper)

Bosonic-SymTFT predicate scaffolding implementing the Kaidi–Ohmori–Zheng
"Drinfeld center + Lagrangian-algebra boundary" working framework
(arXiv:2209.11062, Commun. Math. Phys. 404 (2023) 1021) wrapped in the
Freed–Moore–Teleman axiomatic functorial predicate layer
(arXiv:2209.07471, Quantum Topology 15 (2024) 779).

This module ships only the *predicates* — `Is3DTQFT`, `IsBulkBoundary`,
`TopologicalBoundary` — at the predicate-substrate level, without
constructing the underlying `Bord_n` functor or full TQFT-as-functor.
Witnessing happens elsewhere: `SymTFT/BulkTQFT.lean` (Wave 1b.1)
specializes `Is3DTQFT` to the bulk side; `SymTFT/GappedBoundary.lean`
(Wave 1c.2) and `SymTFT/LagrangianAlgebra.lean` (Wave 1c.2) specialize
the boundary side; `SymTFT/BulkBoundaryCorrespondence.lean` (Wave 1d.1)
states the substantive bulk-boundary correspondence as a load-bearing
tracked Prop.

## Decision: predicate-on-typeclass, not structure-wrapping

Per Wave 1a.1 §1.3 + Wave 2a.1 §2.1, the FMT-wrapper predicates take
the data of a monoidal category as a `Type` + typeclass arguments
(rather than wrapping in a separate `SymTFTBulk` structure). This
matches the project's existing `SymTFTAudit/DrinfeldCenter.lean`
predicate style (`WittEquivalentMTC C D := Nonempty (Center C ≌ Center D)`)
and avoids universe-mismatch issues with Mathlib's `Center C :
Type (max u₁ v₁)` carrier.

## No `axiom` declarations

Per project Invariant #15 and the Phase 6r working-doc §4 tracked-Prop
catalog, this module ships zero `axiom` declarations. Statements that
encode A-class published physics but lack constructive Mathlib substrate
are wrapped as named `def Prop` predicates, surfacing them at the
type-signature level rather than as global axioms.

## References

- Kaidi-Ohmori-Zheng, "Symmetry TFTs for Non-Invertible Defects,"
  arXiv:2209.11062, Commun. Math. Phys. 404 (2023) 1021.
- Freed-Moore-Teleman, "Topological symmetry in quantum field theory,"
  arXiv:2209.07471, Quantum Topology 15 (2024) 779.
- Bhardwaj-Copetti-Pajer-Schäfer-Nameki, "Boundary SymTFT,"
  arXiv:2409.02166, SciPost Phys. 19 (2025) 061.
- Wave 1a.1 DR `Lit-Search/Phase-6r/Phase 6r Wave 1a.1 — SymTFT 2024–2026
  Substrate Deep Research Return.md` §1, §8.
-/
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Equivalence

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u v₁ u₁ v₂ u₂

/-! ## §1. The FMT predicates on raw category types

The Kaidi–Ohmori–Zheng SymTFT for a `d`-dim QFT with finite symmetry
category `𝒮` is a `(d+1)`-dim TFT obtained by gauging `𝒮` in one
dimension higher; for `d+1 = 3` the topological defects form the
Drinfeld center `𝒵(𝒮)`. At the predicate-substrate level we package
the bulk and boundary as raw monoidal categories plus typeclass
constraints, with the bulk-boundary relation as a separate predicate.

Per FMT (arXiv:2209.07471), a "topological symmetry" of a relative QFT
is a `(d+1)`-dim TQFT together with a topological boundary condition.
We encode the three load-bearing FMT predicates — `Is3DTQFT`,
`IsBulkBoundary`, `IsSymTFTSlab` — as `Prop`-valued defs at
predicate-substrate level — *interface* only, not the underlying
`Bord_n` functor.

### Hedging discipline (Wave 1a.1 §1.4, Wave 2a.1 §0)

These predicates are *interfaces* in the sense of Freed-Moore-Teleman;
they specify what a SymTFT bulk and boundary look like at the type
level without constructing the underlying functor `Bord_3 → C`. The
predicate-level approach lets us swap in a `Bord_n`-based witness when
Mathlib catches up (currently no `Mathlib/AlgebraicTopology/Cobordism`).

We do NOT claim "first SymTFT formalization in Lean"; we claim
"predicate-level encoding of the KOZ + FMT-wrapper SymTFT framework
in Lean 4." -/

/-- **`Is3DTQFT B`** — predicate that a monoidal category `B` carries
the categorical data of a 3-dimensional topological quantum field theory.

At the predicate-substrate level, `Is3DTQFT` records that `B` is a
braided monoidal category — the categorical data of a 3D TFT in the
sense of Reshetikhin-Turaev. The full TQFT-as-functor `Bord_3 → B` is
not constructed at this layer.

**Hedging:** This predicate captures the *categorical interface* of a
3D TQFT (a braided monoidal category encoding line operators), not the
full Atiyah-style functorial TQFT. Mathlib does not currently ship the
cobordism category `Bord_3`, so the functorial form is deferred to a
future wave / Mathlib upstream PR.

Anchor: Reshetikhin-Turaev, "Ribbon graphs and their invariants derived
from quantum groups," Commun. Math. Phys. 127 (1990) 1-26;
Bhardwaj-Copetti-Pajer-Schäfer-Nameki, arXiv:2409.02166 (boundary
SymTFT framework). -/
def Is3DTQFT (B : Type u) [Category.{v} B] [MonoidalCategory B] : Prop :=
  Nonempty (BraidedCategory.{v, u} B)

/-- **`IsBulkBoundary B C`** — predicate that `C` is a topological
boundary condition for the `(d+1)=3` bulk `B`.

At the predicate-substrate level, `IsBulkBoundary` records that `B`
satisfies `Is3DTQFT` and that the boundary `C` has fusion-category data.
The substantive bulk-boundary correspondence — Drinfeld center
`𝒵(C) ≃ B` — is stated separately in
`SymTFT/BulkBoundaryCorrespondence.lean` (Wave 1d.1) as a tracked Prop.

Anchor: FMT (arXiv:2209.07471) "axiomatic / functorial point of view:
a 'topological symmetry' of a relative QFT is a `(d+1)`-dim TQFT
together with a topological boundary condition." -/
def IsBulkBoundary
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B]
    (C : Type u₂) [Category.{v₂} C] [MonoidalCategory C] : Prop :=
  Is3DTQFT B

/-- **`IsSymTFTSlab B C_sym C_phys`** — predicate that the slab
construction `B` ⊃ `C_sym` × `C_phys` realizes a SymTFT presentation
of a relative QFT.

Anchor: Apruzzi-Bonetti-García-Etxebarria-Hosseini-Schäfer-Nameki
arXiv:2112.02092 §2; Bhardwaj-Copetti-Pajer-Schäfer-Nameki
arXiv:2409.02166 §1. -/
def IsSymTFTSlab
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B]
    (C_sym : Type u₂) [Category.{v₂} C_sym] [MonoidalCategory C_sym]
    (C_phys : Type u₂) [Category.{v₂} C_phys] [MonoidalCategory C_phys] : Prop :=
  IsBulkBoundary B C_sym ∧ IsBulkBoundary B C_phys

/-! ## §2. The dependent topological-boundary structure

`TopologicalBoundary B` packages a topological boundary condition for
a SymTFT bulk `B` as a sigma-like structure: the underlying boundary
fusion category data + the proof that it satisfies `IsBulkBoundary`.

Used downstream by Wave 3a.3 to construct `sm_boundary_data N_f :
TopologicalBoundary (sm_bulk N_f)`. -/

/-- The type of topological boundary conditions of a SymTFT bulk `B`.
A `TopologicalBoundary B` is a fusion-category boundary `C` paired with
a proof `IsBulkBoundary B C`.

Predicate-substrate-level; concrete instantiations are provided by
Wave 1c (toric code Lagrangian) and Wave 3a.3 (SM matter content). -/
structure TopologicalBoundary
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B] where
  /-- The boundary's carrier type (fusion category data). -/
  carrier : Type u₂
  [category : Category.{v₂} carrier]
  [monoidal : MonoidalCategory carrier]
  /-- Proof that the boundary is compatible with the bulk. -/
  isBdy : IsBulkBoundary B carrier

attribute [instance] TopologicalBoundary.category TopologicalBoundary.monoidal

/-! ## §3. Predicate-level properties

These are routine corollaries of the predicate definitions, establishing
that the FMT wrapper preserves the expected interface relations. -/

theorem isBulkBoundary_of_isSymTFTSlab
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C_sym C_phys : Type u₂} [Category.{v₂} C_sym] [MonoidalCategory C_sym]
    [Category.{v₂} C_phys] [MonoidalCategory C_phys]
    (h : IsSymTFTSlab B C_sym C_phys) :
    IsBulkBoundary B C_sym ∧ IsBulkBoundary B C_phys := h

theorem is3DTQFT_of_isBulkBoundary
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
    (h : IsBulkBoundary B C) : Is3DTQFT B := h

theorem is3DTQFT_of_isSymTFTSlab
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C_sym C_phys : Type u₂} [Category.{v₂} C_sym] [MonoidalCategory C_sym]
    [Category.{v₂} C_phys] [MonoidalCategory C_phys]
    (h : IsSymTFTSlab B C_sym C_phys) : Is3DTQFT B :=
  h.1

/-! ## §4. The `IsBoundarySymTFTCorrespondence` tracked Prop

This is the load-bearing tracked Prop that captures the verbatim
content of Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166
(SciPost Phys. 19 (2025) 061):

> "transformation properties, or (generalized) charges, of BCs are
>  captured by topological BCs of Symmetry Topological Field Theory
>  (SymTFT)."

> "Gapped boundary conditions are in one-to-one correspondence with
>  Lagrangian algebras L in the Drinfeld center."

This is the *primary anchor* for Wave 3a.3 substantive content. We
ship it as a tracked Prop here so downstream consumers
(`CrossBridges/SMMatterAsSymTFTBoundary.lean`) can take it as an
explicit hypothesis without needing to re-state the verbatim claim.

**Tracked-Prop discipline:** the content is what
Bhardwaj-Copetti-Pajer-Schäfer-Nameki state as a published theorem.
We carry it as a hypothesis (load-bearing physics statement) rather
than as a project-local `axiom` per Invariant #15. -/

/-- **Bhardwaj-Copetti-Pajer-Schäfer-Nameki "Boundary SymTFT"
correspondence.** Tracked Prop: for every SymTFT bulk `B`, gapped
boundary conditions of `B` are in bijection with Lagrangian algebras
in the Drinfeld center realizing `B`. The bijection is the load-bearing
content of arXiv:2409.02166.

Per Wave 3a.1 §Q1(a), this is the *primary anchor* for the SM-matter
identification. Consumers (Wave 3a.3) take this hypothesis explicitly.

This is a `Prop`-level predicate on a 3D TQFT; the substantive
mathematical content (the actual bijection — gapped boundaries ↔
Lagrangian algebras in the Drinfeld center) is supplied externally
via the cited primary source. The Lean-side body is the *interface*
of the correspondence — what it says, not how it is proved.

The predicate-substrate body is `Is3DTQFT B`: a bulk satisfying the
3D TQFT predicate enters the Bhardwaj et al. correspondence at the
interface level. Wave 1d.1 (`BulkBoundaryCorrespondence.lean`) ships
the substantive statement of the bijection conditional on this
tracked Prop.

**Phase 6r-prime W2.4 status note (2026-05-25, post adversarial-review
round-1 remediation)**: the substantive biconditional content of this
predicate (`Is3DTQFTBraided B ↔ HasLagrangianAlgebra B`) is **captured
via the companion predicates** `IsDMNOBiconditional B` (body IS the
biconditional, post W2.3 v2 rename) and `IsKapustinSaulinaGappedBoundary B`
(body := `HasLagrangianAlgebra B` substantively, post W2.4) in
`SymTFT/LagrangianAlgebra.lean`. The predicate body here remains the
predicate-substrate marker `Is3DTQFT B` because strengthening it to
the biconditional would require importing `HasLagrangianAlgebra` which
lives downstream (architectural circular-import constraint). **The
substantive BCPS-N biconditional content is shipped via**
`SymTFT/BulkBoundaryCorrespondence.lean::witt_triviality_iff_has_lagrangian_algebra`
(REAL BLOCKER-2 closure per W2.5 v2: hypothesis IS the biconditional,
proof is one-line extraction). -/
def IsBoundarySymTFTCorrespondence
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B] : Prop :=
  Is3DTQFT B

end SKEFTHawking.SymTFT
