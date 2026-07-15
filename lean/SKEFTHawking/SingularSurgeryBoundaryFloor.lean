/-
# Phase 5q.H W-D — SURGERY WAVE 8 (stage 3): THE BOUNDARY IDENTIFICATION FLOOR

Wave 8 stages 1–2 closed the seam collar. The remaining input of `ambientTraceBordism_concrete_D5`
is the boundary identification `e : s.M ⊕ t.M → W` with `he_inj` and
`he_boundary : Set.range e = J.boundary W`. This module lands the **set-level floor** of that input:
the canonical **source-end inclusion** `s.M ↪ W` (the `M × {0}` face carved by `fromCyl`), a closed
embedding, and its disjointness from the handle end (under the surgery-geometric fact that the
attaching map lands in the top face `M × {1}`). With it, half of `e` and half of `he_inj` are
constructed, not assumed — only the surgered end `M'` and its embedding remain a geometric input.

## The two ends — set-level structure (document of record)

`∂W = (source end) ⊔ (surgered end)`:

* **the source end** `fromCyl(M × {0})` — the incoming closed 4-manifold `s.M`, this module's
  `ktSourceEnd`, a closed embedding (`isClosedEmbedding_ktSourceEnd`);
* **the surgered end** `M' = (M ∖ φ(S̊)) ∪ (handle cap)` — carved from the un-attached top of the
  cylinder and the interior of the handle end. As a `SingularManifold` it is itself a handle
  attachment one dimension down (opener §5), whose packaging outgrows this wave; the set-level
  identification (the surgered end is disjoint from the source end) suffices to discharge `he_inj`
  for the source half.

## The `he_boundary` residual — the honest wall (document of record)

`he_boundary : Set.range e = ((𝓡 4).prod (𝓡∂ 1)).boundary W` is the genuinely-deep residual, and it is
**chart-choice-dependent in the continuous category**: `ModelWithCorners.boundary` is defined through the
distinguished `chartAt`, and the assembled `chartedSpaceOfOpensCover` atlas picks its chart per point by
a nonconstructive `choose`; at `k = 0` the transitions are merely continuous, so boundary-ness is *not*
transition-invariant. Pinning `J.boundary W` exactly therefore requires either the smooth (`k > 0`) weld
(so boundary-ness is well-defined) or the explicit surgered-end `SingularManifold` packaging. This wave
lands the set-level floor beneath it — the two ends as disjoint embeddings — and names the full
identification as the residual the packaging (smooth weld / M' construction) rides.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryChartsConcrete

namespace SKEFTHawking.SurgeryFoundation

open Topology TopologicalSpace Set

/-! ## §1. The source-end inclusion `s.M ↪ W` — the `M × {0}` boundary face. -/

variable (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (Ha : Type) [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha]
    (S : Set Ha) (hS : IsClosed S) (φ : ↥S → M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)

/-- **The `M × {0}` point of the cylinder** — the bottom face of `B = M × I`, the source-manifold end. -/
def cylBot (m : M) : M × Set.Icc (0 : ℝ) 1 := (m, ⟨0, by norm_num⟩)

/-- **The source-end inclusion** `s.M ↪ W` — the source 4-manifold `M` included as the bottom face
`M × {0}` of the cylinder, glued into the carrier `W = B ⊔_φ Ha`. This is the source half of the
bordism's boundary map `e`, constructed (not assumed). -/
def ktSourceEnd (m : M) : (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier :=
  (ktHandleAttachment M Ha S hS φ hφ hφinj).fromCyl (cylBot M m)

omit [CompactSpace M] [T2Space M] in
theorem continuous_cylBot : Continuous (cylBot M) :=
  continuous_id.prodMk continuous_const

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] in
theorem injective_cylBot : Function.Injective (cylBot M) := by
  intro a b h
  simpa [cylBot] using h

/-- The `M × {0}` inclusion is a closed embedding of `M` into the cylinder `B = M × I`. -/
theorem isClosedEmbedding_cylBot : IsClosedEmbedding (cylBot M) :=
  (continuous_cylBot M).isClosedEmbedding (injective_cylBot M)

theorem continuous_ktSourceEnd : Continuous (ktSourceEnd M Ha S hS φ hφ hφinj) :=
  (ktHandleAttachment M Ha S hS φ hφ hφinj).continuous_fromCyl.comp (continuous_cylBot M)

/-- **The source-end inclusion is a closed embedding** — `M` sits inside `W` as the closed source-end
boundary face (composite of the closed embedding `M ↪ M × I` at the bottom face and the closed
embedding `fromCyl : B ↪ W`). -/
theorem isClosedEmbedding_ktSourceEnd :
    IsClosedEmbedding (ktSourceEnd M Ha S hS φ hφ hφinj) :=
  (ktHandleAttachment M Ha S hS φ hφ hφinj).isClosedEmbedding_fromCyl.comp
    (isClosedEmbedding_cylBot M)

theorem injective_ktSourceEnd : Function.Injective (ktSourceEnd M Ha S hS φ hφ hφinj) :=
  (isClosedEmbedding_ktSourceEnd M Ha S hS φ hφ hφinj).injective

/-! ## §2. The top-face fact, and the source-end / handle-end disjointness.

Surgery traces attach along the TOP face `M × {1}`: the attaching map `φ` lands in `M × {1}`. Under
this honest geometric fact (`hφtop`), the source end `M × {0}` is disjoint from the attaching image,
hence its carrier image is disjoint from the handle end (opener §4). This is the set-level separation
that discharges `he_inj` for the source half of the boundary map. -/

omit [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [TopologicalSpace Ha] [CompactSpace Ha] [T2Space Ha] in
/-- **No bottom-face point is attached** — under the top-face fact `hφtop`, `(m, 0) ∉ range φ`
(the attaching map lands at height `1`, not `0`). -/
theorem cylBot_not_mem_range_phi (hφtop : ∀ a, ((φ a).2 : ℝ) = 1) (m : M) :
    cylBot M m ∉ Set.range φ := by
  rintro ⟨a, ha⟩
  have h0 : ((φ a).2 : ℝ) = 0 := by rw [ha]; simp [cylBot]
  rw [hφtop a] at h0
  norm_num at h0

/-- **The source end is disjoint from the handle end.** Under the top-face fact, `fromCyl(M × {0})`
lands among the un-attached cylinder points `fromCyl((range φ)ᶜ)`, which the opener showed is disjoint
from the handle end `range fromHandle`. The source-manifold boundary component is thereby cleanly
separated in `W` from the surgered end carved from the handle. -/
theorem ktSourceEnd_disjoint_range_fromHandle (hφtop : ∀ a, ((φ a).2 : ℝ) = 1) :
    Disjoint (Set.range (ktSourceEnd M Ha S hS φ hφ hφinj))
      (Set.range (ktHandleAttachment M Ha S hS φ hφ hφinj).fromHandle) := by
  have hsub : Set.range (ktSourceEnd M Ha S hS φ hφ hφinj)
      ⊆ (ktHandleAttachment M Ha S hS φ hφ hφinj).fromCyl '' (Set.range φ)ᶜ := by
    rintro _ ⟨m, rfl⟩
    exact ⟨cylBot M m, cylBot_not_mem_range_phi M Ha S φ hφtop m, rfl⟩
  exact Disjoint.mono_left hsub
    (ktHandleAttachment M Ha S hS φ hφ hφinj).fromCyl_image_compl_disjoint_range_fromHandle

/-! ## §3. The boundary-map combinators — the source half of `e`, constructed.

The bordism boundary map `e : s.M ⊕ t.M → W` splits as `Sum.elim (ktSourceEnd) eM'`, where `eM'` is the
surgered-end embedding (`t.M ↪ W`, carved from the handle, the caller's geometric input). This section
constructs the injectivity and the closed embedding of the full `e` from the source-end structure (§1)
plus the surgered-end map's own structure plus their range-disjointness — so `he_inj` for the source
half is discharged, not assumed. -/

variable {t : Type*} [TopologicalSpace t]

omit [TopologicalSpace t] in
/-- **The full boundary map is injective** — `Sum.elim (ktSourceEnd) eM'` is injective from the
source-end injectivity (§1), the surgered-end map's injectivity, and their range-disjointness. -/
theorem injective_sumElim_ktSourceEnd (eM' : t → (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier)
    (heM'_inj : Function.Injective eM')
    (hdisj : Disjoint (Set.range (ktSourceEnd M Ha S hS φ hφ hφinj)) (Set.range eM')) :
    Function.Injective (Sum.elim (ktSourceEnd M Ha S hS φ hφ hφinj) eM') :=
  (injective_ktSourceEnd M Ha S hS φ hφ hφinj).sumElim heM'_inj
    (fun m x hcontra => (Set.disjoint_left.mp hdisj) ⟨m, hcontra⟩ ⟨x, rfl⟩)

/-- **The full boundary map is a closed embedding** — `Sum.elim (ktSourceEnd) eM'` is a closed embedding
from the source-end closed embedding (§1), the surgered-end closed embedding, and their
range-disjointness. This is the boundary-map shape `e` a `Bordism` wants: a closed injection onto the
two-ended `∂W` (the surgered end `eM'` being the caller's residual). -/
theorem isClosedEmbedding_sumElim_ktSourceEnd
    (eM' : t → (ktHandleAttachment M Ha S hS φ hφ hφinj).carrier)
    (heM' : IsClosedEmbedding eM')
    (hdisj : Disjoint (Set.range (ktSourceEnd M Ha S hS φ hφ hφinj)) (Set.range eM')) :
    IsClosedEmbedding (Sum.elim (ktSourceEnd M Ha S hS φ hφ hφinj) eM') :=
  IsClosedEmbedding.sumElim (isClosedEmbedding_ktSourceEnd M Ha S hS φ hφ hφinj) heM'
    (injective_sumElim_ktSourceEnd M Ha S hS φ hφ hφinj eM' heM'.injective hdisj)

end SKEFTHawking.SurgeryFoundation
