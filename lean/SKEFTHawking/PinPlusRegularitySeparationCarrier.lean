/-
# The CARRIER-LEVEL separating witness — a compact `C⁰` 4-manifold that is not `C¹`

`PinPlusRegularitySeparation` separated the `𝓡 4` regularity binder using the non-compact
`TwistedR4`, and flagged the compact witness as the residual brick.  This module lands it.

The construction is generic: given *any* nonempty charted space `M` over `ℝ⁴`, adjoin to its
atlas the single extra chart `chartAt p₀ ≫ₕ twist c₀`, where `c₀ = chartAt p₀ p₀` is the image
of the basepoint and `twist c₀` is the kink shear of `PinPlusRegularitySeparation` centred
there.  The result `Twisted M` has the same topology (hence the same compactness) and the same
`chartAt`, so it is still a charted space; but its atlas now contains a transition whose
inverse is not differentiable at `c₀`.

Instantiated at `RP4PointSet.RP4` — the project's concrete compact, boundaryless, charted
4-manifold, already used as the carrier witness `RP4Witness.rp4SM : SingularManifold PUnit 0
(𝓡 4)` — this produces an honest **element of the `k = 0` carrier that cannot exist at
`k ≥ 1`**.

See §4 for scope: this separates the *object classes*, not the bordism groups.
-/

import Mathlib
import SKEFTHawking.PinPlusRegularitySeparation
import SKEFTHawking.RP4PointSet

namespace SKEFTHawking.PinPlusRegularitySeparationCarrier

open scoped Manifold
open SKEFTHawking.PinPlusRegularitySeparation

/-- Abbreviation for the 4-dimensional model space. -/
local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The shear fixes its kink point (`kinkInv 0 = 0`). -/
theorem shearInv_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (v c : E) : shearInv f v c c = c := by
  simp [shearInv, kinkInv_of_nonneg (le_refl (0 : ℝ))]

theorem twist_symm_self (c : E4) : (twist c).symm c = c :=
  shearInv_self coord4 vec4 c

/-! ## §1. The generic twist of a charted space -/

variable (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [Nonempty M]

/-- `M` with one extra, deliberately non-`C¹`, chart adjoined to its atlas. -/
def Twisted : Type := M

instance : TopologicalSpace (Twisted M) := inferInstanceAs (TopologicalSpace M)

instance [CompactSpace M] : CompactSpace (Twisted M) := inferInstanceAs (CompactSpace M)

instance [T2Space M] : T2Space (Twisted M) := inferInstanceAs (T2Space M)

instance : Nonempty (Twisted M) := inferInstanceAs (Nonempty M)

/-- An arbitrary basepoint of `M`. -/
noncomputable def basePoint : M := Classical.arbitrary M

/-- The chart of `M` at the basepoint. -/
noncomputable def baseChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 4)) :=
  chartAt (EuclideanSpace ℝ (Fin 4)) (basePoint M)

/-- The point of `ℝ⁴` at which the adjoined chart kinks: the image of the basepoint. -/
noncomputable def kinkPoint : EuclideanSpace ℝ (Fin 4) := baseChart M (basePoint M)

theorem basePoint_mem_source : basePoint M ∈ (baseChart M).source :=
  mem_chart_source _ _

theorem kinkPoint_mem_target : kinkPoint M ∈ (baseChart M).target :=
  (baseChart M).map_source (basePoint_mem_source M)

/-- **The adjoined chart** — the basepoint chart post-composed with the kink shear. -/
noncomputable def twistChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 4)) :=
  (baseChart M) ≫ₕ (twist (kinkPoint M)).toOpenPartialHomeomorph

/-- The identity map, viewing a point of `Twisted M` at its underlying type `M`.  Needed so
that instance search on the two (defeq but distinct) type synonyms cannot loop. -/
def untwist : Twisted M → M := id

/-- `Twisted M` is a charted space: same `chartAt` as `M`, atlas enlarged by `twistChart`. -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Twisted M) where
  atlas := insert (twistChart M) (atlas (EuclideanSpace ℝ (Fin 4)) M)
  chartAt p := (_root_.chartAt (EuclideanSpace ℝ (Fin 4)) (untwist M p) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 4)))
  mem_chart_source p := _root_.mem_chart_source (EuclideanSpace ℝ (Fin 4)) (untwist M p)
  chart_mem_atlas p := Set.mem_insert_of_mem _ (_root_.chart_mem_atlas _ (untwist M p))

/-- At `k = 0` the twisted atlas is still a manifold structure — the binder is free. -/
theorem twisted_isManifold_zero : IsManifold (𝓡 4) 0 (Twisted M) :=
  PinPlusRegularityFence.isManifoldZero_free (𝓡 4)

/-! ## §2. …but the twisted atlas is not `C¹` -/

/-- The composite transition `baseChart⁻¹ ≫ twistChart`, whose non-`C¹`-ness is the whole
point.  Kept as a definition so the two facts about it below read cleanly. -/
noncomputable def transitionChart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 4))
    (EuclideanSpace ℝ (Fin 4)) :=
  (baseChart M).symm ≫ₕ (twistChart M)

theorem kinkPoint_mem_transition_target : kinkPoint M ∈ (transitionChart M).target := by
  simp [transitionChart, twistChart, twist_symm_self, kinkPoint_mem_target]

theorem transition_symm_eqOn :
    Set.EqOn (transitionChart M).symm (twist (kinkPoint M)).symm (transitionChart M).target := by
  intro y hy
  simp [transitionChart, twistChart] at hy ⊢
  exact (baseChart M).right_inv hy.1

theorem twisted_not_isManifold_one : ¬ IsManifold (𝓡 4) 1 (Twisted M) := by
  intro h
  have hbase0 : baseChart M ∈ ChartedSpace.atlas (H := EuclideanSpace ℝ (Fin 4)) (M := M) :=
    _root_.chart_mem_atlas _ (basePoint M)
  have hbase : (baseChart M : OpenPartialHomeomorph (Twisted M) (EuclideanSpace ℝ (Fin 4)))
      ∈ atlas (EuclideanSpace ℝ (Fin 4)) (Twisted M) :=
    Set.mem_insert_of_mem _ hbase0
  have htw : (twistChart M : OpenPartialHomeomorph (Twisted M) (EuclideanSpace ℝ (Fin 4)))
      ∈ atlas (EuclideanSpace ℝ (Fin 4)) (Twisted M) :=
    Set.mem_insert _ _
  have hmem0 := StructureGroupoid.compatible (contDiffGroupoid 1 (𝓡 4)) hbase htw
  have hmem : transitionChart M ∈ contDiffGroupoid 1 (𝓡 4) := hmem0
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hmem
  have h2 := hmem.2
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.preimage_id, Set.range_id, Set.inter_univ, Function.comp_def, id_eq] at h2
  have h3 : ContDiffOn ℝ 1 (twist (kinkPoint M)).symm (transitionChart M).target :=
    h2.congr (fun x hx => (transition_symm_eqOn M hx).symm)
  have hdiff : DifferentiableAt ℝ (shearInv coord4 vec4 (kinkPoint M)) (kinkPoint M) :=
    (h3.differentiableOn one_ne_zero).differentiableAt
      ((transitionChart M).open_target.mem_nhds (kinkPoint_mem_transition_target M))
  exact not_differentiableAt_shearInv coord4 vec4 (kinkPoint M) coord4_vec4 hdiff

/-! ## §3. The carrier-level witness — `Twisted ℝP⁴` -/

open SKEFTHawking.RP4PointSet

/-- **The twisted `ℝP⁴`.**  Same underlying compact, Hausdorff, boundaryless topological
4-manifold as `RP4PointSet.RP4` (so the `CompactSpace` / `BoundarylessManifold` instances that
make `RP4Witness.rp4SM` a legal `SingularManifold` still fire), but carrying one extra atlas
chart whose transition against the basepoint chart is not `C¹`. -/
def TwistedRP4 : Type := Twisted RP4

noncomputable instance : TopologicalSpace TwistedRP4 :=
  inferInstanceAs (TopologicalSpace (Twisted RP4))

noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 4)) TwistedRP4 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Twisted RP4))

instance : CompactSpace TwistedRP4 := inferInstanceAs (CompactSpace (Twisted RP4))

instance : T2Space TwistedRP4 := inferInstanceAs (T2Space (Twisted RP4))

instance : IsManifold (𝓡 4) 0 TwistedRP4 :=
  PinPlusRegularityFence.isManifoldZero_free (𝓡 4)

/-- **THE CARRIER-LEVEL SEPARATING WITNESS.**  An element of `SingularManifold PUnit 0 (𝓡 4)`
— the *exact* type `pinPlusCharPairData residualProv` quantifies over, and the same type
`RP4Witness.rp4SM` inhabits — whose charted structure is provably **not** `C¹`
(`twistedRP4_not_isManifold_one`).  It therefore exists at `k = 0` and cannot be an object of
the corresponding `k ≥ 1` category. -/
noncomputable def twistedRP4SM : SingularManifold.{0} PUnit.{1} 0 (𝓡 4) where
  M := TwistedRP4
  f := fun _ => PUnit.unit
  hf := continuous_const

theorem twistedRP4_not_isManifold_one : ¬ IsManifold (𝓡 4) 1 TwistedRP4 :=
  twisted_not_isManifold_one RP4

/-- **THE SEPARATION, AT THE CARRIER.**  The `k = 0` carrier `SingularManifold PUnit 0 (𝓡 4)`
contains an object whose charted structure fails `IsManifold (𝓡 4) 1`.  Re-declaring the KT
assembly at `k ≥ 1` therefore genuinely *removes* objects from the carrier — the `k := 0`
instantiation is not a harmless generalisation. -/
theorem exists_carrier_element_not_smooth :
    ∃ s : SingularManifold.{0} PUnit.{1} 0 (𝓡 4), ¬ IsManifold (𝓡 4) 1 s.M :=
  ⟨twistedRP4SM, twistedRP4_not_isManifold_one⟩

/-! ## §4. SCOPE

* **ESTABLISHED (kernel):** `SingularManifold PUnit 0 (𝓡 4)` — the carrier of the live KT
  assembly — contains an object that is *not* a `C¹` manifold.  The `C⁰` object class is
  therefore strictly larger than the `C¹` one; the `k := 0` binder is not harmless generality.
  Combined with `PinPlusRegularitySeparation.no_generic_zero_to_one_transport`, route (B) —
  "transport the `k = 0` conclusion to `k ≥ 1`" — is closed.

* **NOT established — a bordism-group inequality.**  A strictly larger *object class* does not
  by itself give a strictly larger *bordism group*: bordism could identify the extra objects.
  Whether `T2DataBordismGrp (pinPlusCharPairData residualProv)` differs from its `k ≥ 1`
  analogue is **open** and is NOT claimed here.

* **NOT established — Kirby–Siebenmann.**  The roadmap's `Ω₄^{TopPin⁺} ≅ ℤ/2 ⊕ ℤ/8` (§2 leg 2
  of `Phase5qH_LiteratureGradeUnconditional_Roadmap.md`) is not formalized anywhere in-tree and
  is not used.  In particular `TwistedRP4` is *homeomorphic* to `ℝP⁴` and does admit *some*
  smooth structure — what fails is that **its atlas**, the datum the carrier actually carries,
  is not `C¹`.  That is the correct level for this fence: `SingularManifold` bundles a specific
  `ChartedSpace` together with its `IsManifold` field.

* **This is not evidence against the KT lane's mathematics.**  It is evidence that the lane's
  conclusions, *as declared*, are `C⁰` conclusions. -/

end SKEFTHawking.PinPlusRegularitySeparationCarrier
