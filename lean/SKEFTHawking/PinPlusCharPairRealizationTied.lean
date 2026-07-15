/-
# Phase 5q.H (W-A arm 4, ROUND 5 fix) — THE DERIVED-BASIS REALIZATION TIE.

The round-5 re-gate (`PinPlusCharPairGeoRealizationGate`) refuted the as-built realization seam on
finding **F2 (basis-gauge covariance)**: `GeoRealizationData`'s enhancement bases `eσ`/`eτ` are FREE
`LinearEquiv` fields, so the `killerGauge` (`id ⊞ (J+I)`) carries the honest doubling membrane's
computed kernel EXACTLY onto the e₈-graph kernel (`map_killerGauge_ker_negBorBInc`) while fixing the
spaces `∂Q`, `Q`, the inclusion `ι`, and hence every topological certificate a strengthening could
attach (T2/compact/dimension/closed-embedding are all GAUGE-BLIND, `gaugeσ_bdry`/`gaugeσ_Q`/…). The
gate's own verdict: *"the load-bearing missing tie is the (n, q, surf) BASIS tie: `eσ`/`eτ` must be
pinned to the ends' carried enhancement bases (`hpolar`/`hchar`), not free fields."*

This module supplies exactly that pin — a **derived-basis** realization datum `GeoRealizationTied`.
Its boundary homology bases are NO LONGER free: they are `DERIVED` from the two ends' carried
COHOMOLOGY bases through

* the **mod-2 UCT bridge** `homologyBasisOfCohomologyBasis` (`SingularKroneckerBasisBridge`), which
  dualizes a coordinate system on `H¹(Σ)` to one on `H₁(Σ)` canonically (the Kronecker pairing is
  perfect over `ℤ/2`), and
* a **homeomorphism-field identification** `homσ : ∂Q ⊇ Σ_σ ≃ₜ Sσ` (resp. `homτ`), transported to
  homology by `homeoHomologyEquiv`.

so `eσ := homologyBasisOfCohomologyBasis bσ ∘ H₁(homσ)` is a `rfl`-computed function of the CARRIED
cohomology basis `bσ` (`toData_eσ`), never an independent field. The killer gauge can no longer move
`eσ` while keeping `bσ` — hence `q` (which `hpolar` ties covariantly to `bσ`) — fixed. Per the
membrane-level non-Hausdorff no-go the topological certificates are carried **per object** (T2 AND
Compact on `∂Q` and `Q` SEPARATELY, plus `ι` an `IsClosedEmbedding`), never as a joint/quotient
certificate that a collapse could satisfy vacuously.

The datum produces a genuine `GeoRealizationData` (`toData`) and thence a `GeoMembrane` whose Taylor
leg submodule is the honest geometric boundary-inclusion kernel read through the DERIVED bases
(`toMembrane`, `toMembrane_L`), so all the seam's transport machinery (`transportedBInc`,
`transportedBInc_ker`, `ofGeometric_L`) applies unchanged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairMembraneGeoRealization
import SKEFTHawking.SingularKroneckerBasisBridge

open CategoryTheory Opposite Topology
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairMembraneTie
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization

namespace SKEFTHawking.PinPlusCharPairRealizationTied

/-! ## §1. The homeomorphism-induced homology equivalence.

A homeomorphism of the underlying spaces induces a `LinearEquiv` on mod-2 singular homology — the
functorial iso `H₁(homσ)` used to transport the boundary-component homology to the end surface's
homology (where the carried cohomology basis lives). Built from `Homology.map_comp` / `Homology.map_id`
with the inverse the reverse homeomorphism's induced map. -/
noncomputable def homeoHomologyEquiv {X Y : TopCat} (h : (X : Type) ≃ₜ (Y : Type)) (n : ℕ) :
    Homology X n ≃ₗ[ZMod 2] Homology Y n :=
  LinearEquiv.ofLinear
    (Homology.map ⟨h, h.continuous⟩ n)
    (Homology.map ⟨h.symm, h.symm.continuous⟩ n)
    (by rw [← Homology.map_comp,
        show (⟨h, h.continuous⟩ : C(↑X, ↑Y)).comp ⟨h.symm, h.symm.continuous⟩
            = ContinuousMap.id ↑Y from ContinuousMap.ext (fun y => h.apply_symm_apply y),
        Homology.map_id])
    (by rw [← Homology.map_comp,
        show (⟨h.symm, h.symm.continuous⟩ : C(↑Y, ↑X)).comp ⟨h, h.continuous⟩
            = ContinuousMap.id ↑X from ContinuousMap.ext (fun x => h.symm_apply_apply x),
        Homology.map_id])

@[simp] theorem homeoHomologyEquiv_apply {X Y : TopCat} (h : (X : Type) ≃ₜ (Y : Type)) (n : ℕ)
    (x : Homology X n) :
    homeoHomologyEquiv h n x = Homology.map ⟨h, h.continuous⟩ n x :=
  rfl

/-! ## §2. The derived-basis realization datum. -/

variable {nσ nτ : ℕ} {Sσ Sτ : TopCat}
variable {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)}
variable {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}

/-- **The derived-basis membrane-realization datum.** Parameterized by the two ends' carried
COHOMOLOGY bases `bσ : H¹(Sσ) ≃ (Fin nσ → ℤ/2)`, `bτ : H¹(Sτ) ≃ (Fin nτ → ℤ/2)` (the shape
`CharPairStrBundled.basis` carries). Supplies the geometric membrane `Q` with boundary `∂Q` clopen-
split as `Σ_σ ⊔ Σ_τ`, homeomorphism identifications `homσ`/`homτ` of each boundary component with the
carried end surface, and per-object topological certificates (T2 + Compact on `∂Q` and `Q`
separately — the membrane-level non-Hausdorff no-go — plus `ι` an `IsClosedEmbedding`). The boundary
homology bases are NOT fields: they are DERIVED (`toData`) from `bσ`/`bτ` through the UCT bridge and
`homσ`/`homτ`, killing the F2 basis-gauge exploit. Only the interior basis `eQ` remains free — and the
interior gauge leaves the computed kernel invariant (`ker_transportedBInc_gaugeQ`), so it carries no
laundering freedom. -/
structure GeoRealizationTied (Sσ Sτ : TopCat)
    (bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) where
  /-- the boundary object `∂Q`. -/
  bdry : TopCat
  /-- the ambient membrane `Q`. -/
  Q : TopCat
  /-- the clopen set splitting `∂Q = Σ_σ ⊔ Σ_τ`. -/
  U : Set ↑bdry
  /-- the split is clopen. -/
  hU : IsClopen U
  /-- **per-object certificate**: `∂Q` is Hausdorff. -/
  bdryT2 : T2Space ↑bdry
  /-- **per-object certificate**: `∂Q` is compact. -/
  bdryCompact : CompactSpace ↑bdry
  /-- **per-object certificate**: `Q` is Hausdorff (NOT a joint/quotient T2 — the membrane-level
  non-Hausdorff no-go). -/
  QT2 : T2Space ↑Q
  /-- **per-object certificate**: `Q` is compact. -/
  QCompact : CompactSpace ↑Q
  /-- the boundary inclusion `∂Q ↪ Q`. -/
  ι : C(↑bdry, ↑Q)
  /-- **certificate**: the boundary inclusion is a closed embedding. -/
  hιce : IsClosedEmbedding ι
  /-- the σ-boundary component `Σ_σ = sub U` is homeomorphic to the carried end surface `Sσ`. -/
  homσ : (↑(sub U) : Type) ≃ₜ (↑Sσ : Type)
  /-- the τ-boundary component `Σ_τ = sub Uᶜ` is homeomorphic to the carried end surface `Sτ`. -/
  homτ : (↑(sub Uᶜ) : Type) ≃ₜ (↑Sτ : Type)
  /-- `mid = dim H₁(Q;ℤ/2)`. -/
  mid : ℕ
  /-- `H₁(Q)` interior basis (a free field, but the interior gauge is kernel-invariant). -/
  eQ : Homology Q 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2)

/-- **The DERIVED σ-boundary homology basis** — `H₁(Σ_σ) ≃ (Fin nσ → ℤ/2)`, computed as the UCT
dual of the carried cohomology basis `bσ`, pulled back along the identification homeomorphism `homσ`.
NOT a free field: it is a function of `bσ` and `homσ` alone. -/
noncomputable def GeoRealizationTied.derivedEσ (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    Homology (sub d.U) 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2) :=
  (homeoHomologyEquiv d.homσ 1).trans (homologyBasisOfCohomologyBasis bσ)

/-- **The DERIVED τ-boundary homology basis** — `H₁(Σ_τ) ≃ (Fin nτ → ℤ/2)`, the UCT dual of `bτ`
pulled back along `homτ`. -/
noncomputable def GeoRealizationTied.derivedEτ (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    Homology (sub d.Uᶜ) 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2) :=
  (homeoHomologyEquiv d.homτ 1).trans (homologyBasisOfCohomologyBasis bτ)

/-! ## §3. Producing a genuine `GeoRealizationData` — with DERIVED boundary bases. -/

/-- **The realization datum as a `GeoRealizationData`** — the same geometry (`bdry`/`Q`/`U`/`hU`/`ι`,
`eQ`), with the boundary bases FILLED by the derived values `derivedEσ`/`derivedEτ`. This exhibits the
tied datum as a legitimate input to the whole seam-transport machinery — but its `eσ`/`eτ` are pinned
to the carried cohomology bases, not free. -/
noncomputable def GeoRealizationTied.toData (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    GeoRealizationData nσ nτ d.mid where
  bdry := d.bdry
  Q := d.Q
  U := d.U
  hU := d.hU
  ι := d.ι
  eσ := d.derivedEσ
  eτ := d.derivedEτ
  eQ := d.eQ

/-- **The derivation witness (σ)** — the seam's `eσ` IS the UCT-dual of the carried cohomology basis
`bσ` pulled back along `homσ`, on the nose (`rfl`). This is the F2 fix: `eσ` is no longer a free
`LinearEquiv` field the `killerGauge` can post-compose independently of `bσ`. -/
@[simp] theorem GeoRealizationTied.toData_eσ (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    d.toData.eσ = (homeoHomologyEquiv d.homσ 1).trans (homologyBasisOfCohomologyBasis bσ) :=
  rfl

/-- **The derivation witness (τ)**. -/
@[simp] theorem GeoRealizationTied.toData_eτ (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    d.toData.eτ = (homeoHomologyEquiv d.homτ 1).trans (homologyBasisOfCohomologyBasis bτ) :=
  rfl

@[simp] theorem GeoRealizationTied.toData_ι (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    d.toData.ι = d.ι :=
  rfl

/-! ## §4. Producing the `GeoMembrane` — the honest geometric fold-kernel. -/

/-- **The membrane produced by a derived-basis realization** — `GeoMembrane.ofGeometric` of the
derived-basis data. Its computed Taylor-leg submodule `L = ker (transportedBInc toData)` is the honest
geometric boundary-inclusion kernel read through the DERIVED bases. -/
noncomputable def GeoRealizationTied.toMembrane (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ) : GeoMembrane qσ qτ :=
  GeoMembrane.ofGeometric qσ qτ d.toData

/-- **The membrane's kernel is the geometric boundary-inclusion kernel, read through the DERIVED
source basis** `srcEquiv toData` — never a free submodule. The image is of `ker(H₁(∂Q) → H₁(Q))`, the
honest geometric fold-kernel. -/
theorem GeoRealizationTied.toMembrane_L (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    (d.toMembrane qσ qτ).L
      = Submodule.map (srcEquiv d.toData).toLinearMap (LinearMap.ker (Homology.map d.ι 1)) :=
  GeoMembrane.ofGeometric_L qσ qτ d.toData

/-! ## §5. Seam-transport support lemmas (reused by the cylinder realization). -/

open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn

/-- The degree-`n` additivity equivalence in coordinates: `splitHnEquiv (a, b) = i_*(a) + i_*(b)`. -/
theorem splitHnEquiv_apply {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (m : ℕ)
    (p : Homology (sub U) m × Homology (sub Uᶜ) m) :
    splitHnEquiv hU m p = homIncl U m p.1 + homIncl Uᶜ m p.2 := by
  show splitHn U m p = _
  rw [splitHn, LinearMap.coprod_apply]

/-- **The realization datum's source equivalence, inverse in coordinates.** `srcEquiv d` splits
`H₁(∂Q)` through the clopen partition and the boundary bases; its inverse reassembles a sum-indexed
vector as `i_*(eσ⁻¹(x∘inl)) + i_*(eτ⁻¹(x∘inr))`. This is the concrete decomposition the transported
boundary-inclusion kernel computation rides. -/
theorem srcEquiv_symm_apply {mid : ℕ} (d : GeoRealizationData nσ nτ mid)
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (srcEquiv d).symm x
      = homIncl d.U 1 (d.eσ.symm (fun i => x (Sum.inl i)))
        + homIncl d.Uᶜ 1 (d.eτ.symm (fun i => x (Sum.inr i))) := by
  rw [LinearEquiv.symm_apply_eq, srcEquiv]
  simp only [LinearEquiv.trans_apply]
  rw [← splitHnEquiv_apply d.hU 1
      (d.eσ.symm (fun i => x (Sum.inl i)), d.eτ.symm (fun i => x (Sum.inr i))),
    LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext j
  cases j with
  | inl j => rfl
  | inr j => rfl

end SKEFTHawking.PinPlusCharPairRealizationTied
