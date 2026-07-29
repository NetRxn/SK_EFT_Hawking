/-
# Phase 5q.H (#212) — THE COLLAR BRIDGE, ANATOMISED AND REFUTED.

`PinPlusTraceSeamResidualNarrow.ClosedSeamAttachedCollarBridge S a` was honest-reduced as the "sole
remaining geometric atom" of the disk-side seam decomposition, with the prose reading that it is the
*collar deformation-retraction* content. This module settles it, in two steps.

* **§1 — it has no collar content at all.** `attachedBridge_iff_support_dichotomy`: the bridge holds
  **iff** every support simplex of `a` has image inside `S` or inside `sphere ∖ S`. Both directions
  are constructive. So the bridge is not a retraction statement — it is the purely combinatorial
  assertion that *no simplex of `a` straddles the closed seam `S`*. Nothing about collars, homotopies
  or deformation retractions can supply it, because it is not that kind of statement: a straddling
  simplex is a basis vector of the free `ℤ/2`-module that lies in neither summand, and no homotopy
  moves a chain to an EQUAL chain.

* **§2 — it is FALSE at an admissible engine configuration.** `collar_bridge_refuted` exhibits a
  closed nonempty seam `S ⊆ sphere`, an open `U ⊇ S` satisfying the engine's cover hypothesis
  `sphere ⊆ U ∪ Sᶜ` verbatim, and a chain `a ∈ subspaceChains (U ∩ sphere)` — the exact shape of the
  attached part produced by `diskDetectChain_subtype_boundary_split_freeSphere` — with
  `¬ ClosedSeamAttachedCollarBridge S a`. The witness is a single great-circle 4-simplex of `S⁴` that
  runs from a point of `S` to a point off it. **No proof of the atom can exist**, so `#212 item d`
  cannot be discharged as stated; it must be replaced by a split that CERTIFIES the absence of
  straddlers.

**Scope (do not over-read).** This refutes the atom **as stated and as consumed** — universally over
the attached chain `a`, which is how `exact_seam_split_of_attachedBridge` takes it. It does NOT say
the collar-pair row is dead: the row's `hctrlH`/`houtH` pair asks for the remainder off the
*builder-chosen* core `K`, not off `S`, and that IS produced — see
`PinPlusTraceCapstoneCollarPairHandle.exists_ctrlHandle_split_offCore`. The bridge was a needlessly
strong reduction, not the row's actual obligation.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceSeamResidualNarrow

namespace SKEFTHawking.PinPlusTraceSeamCollarBridgeNoGo

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularExcision
open SKEFTHawking.PinPlusTraceSeamResidualNarrow
open SKEFTHawking.DiskChartGeneric (D5)

noncomputable section

/-- The boundary sphere `S⁴ = ∂D⁵` as a subset of `D⁵`. -/
abbrev sphere5 : Set D5 := {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}

/-- Singular `4`-simplices of `D⁵` — the basis of the chain group the bridge lives in. -/
abbrev Simp4 : Type := (TopCat.toSSet.obj (TopCat.of D5)).obj (op (SimplexCategory.mk (3 + 1)))

/-- The realization of a singular `4`-simplex of `D⁵` as a continuous map `Δ⁴ → D⁵`. -/
abbrev realize4 (τ : Simp4) : C(↥(stdSimplex ℝ (Fin 5)), D5) :=
  (TopCat.of D5).toSSetObjEquiv (op (SimplexCategory.mk (3 + 1))) τ

/-! ## §1. The bridge is a pure support dichotomy — no collar content. -/

/-- **Forward: the bridge FORCES a straddler-free support.** If `a` decomposes as a pushforward from
`↥S` plus a `sphere ∖ S`-supported correction, then each of its support simplices came from exactly
one of the two summands, hence has image inside `S` or inside `sphere ∖ S`. Chains are free
`ℤ/2`-modules on the singular simplices, so this is coefficient-wise and admits no slack. -/
theorem support_dichotomy_of_attachedBridge {S : Set D5} {a : SingularChain (TopCat.of D5) (3 + 1)}
    (h : ClosedSeamAttachedCollarBridge S a) {τ : Simp4} (hτ : τ ∈ a.support) :
    Set.range (realize4 τ) ⊆ S ∨ Set.range (realize4 τ) ⊆ sphere5 \ S := by
  classical
  obtain ⟨cSeam, corr, ha, hcorr⟩ := h
  have hseam : mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cSeam
      ∈ subspaceChains (X := TopCat.of D5) S (3 + 1) := by
    rw [mapChain_ambIncl]
    exact LinearMap.mem_range_self _ cSeam
  rw [ha] at hτ
  rcases Finset.mem_union.mp (Finsupp.support_add hτ) with h1 | h1
  · exact Or.inl (range_of_mem_subspaceChains hseam h1)
  · exact Or.inr (range_of_mem_subspaceChains hcorr h1)

/-- **Backward: a straddler-free support BUILDS the bridge.** Filtering `a` by "image inside `S`"
splits it into a subspace chain of `S` (a pushforward from `↥S`) and a remainder each of whose
simplices, not being `S`-supported, is `sphere ∖ S`-supported by hypothesis. -/
theorem attachedBridge_of_support_dichotomy {S : Set D5}
    {a : SingularChain (TopCat.of D5) (3 + 1)}
    (h : ∀ τ ∈ a.support, Set.range (realize4 τ) ⊆ S ∨ Set.range (realize4 τ) ⊆ sphere5 \ S) :
    ClosedSeamAttachedCollarBridge S a := by
  classical
  have hpos : a.filter (fun τ => Set.range (realize4 τ) ⊆ S)
      ∈ subspaceChains (X := TopCat.of D5) S (3 + 1) := by
    refine mem_subspaceChains_of_support (fun τ hτ => ?_)
    rw [Finsupp.support_filter] at hτ
    exact (Finset.mem_filter.mp hτ).2
  have hneg : a.filter (fun τ => ¬ Set.range (realize4 τ) ⊆ S)
      ∈ subspaceChains (X := TopCat.of D5) (sphere5 \ S) (3 + 1) := by
    refine mem_subspaceChains_of_support (fun τ hτ => ?_)
    rw [Finsupp.support_filter] at hτ
    obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hτ
    exact (h τ hmem).resolve_left hnot
  obtain ⟨cSeam, hcSeam⟩ := hpos
  refine ⟨cSeam, a.filter (fun τ => ¬ Set.range (realize4 τ) ⊆ S), ?_, hneg⟩
  rw [mapChain_ambIncl, hcSeam]
  exact (Finsupp.filter_pos_add_filter_neg a _).symm

/-- **THE ANATOMY (headline of §1).** `ClosedSeamAttachedCollarBridge S a` is EXACTLY the statement
that no support simplex of `a` straddles `S`. The atom carries no geometric content beyond this
combinatorial condition — in particular the "collar deformation-retraction" reading is wrong: a
retraction gives homotopy/homology invariance, never the chain-level EQUALITY this demands. -/
theorem attachedBridge_iff_support_dichotomy (S : Set D5)
    (a : SingularChain (TopCat.of D5) (3 + 1)) :
    ClosedSeamAttachedCollarBridge S a
      ↔ ∀ τ ∈ a.support, Set.range (realize4 τ) ⊆ S ∨ Set.range (realize4 τ) ⊆ sphere5 \ S :=
  ⟨fun h _ hτ => support_dichotomy_of_attachedBridge h hτ, attachedBridge_of_support_dichotomy⟩

/-! ## §2. The straddle witness — a great-circle 4-simplex crossing the seam. -/

/-- The great-circle point `cos t · e₀ + sin t · e₁` of the unit sphere of `E⁵`. -/
def circPt (t : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  Real.cos t • EuclideanSpace.single 0 1 + Real.sin t • EuclideanSpace.single 1 1

theorem norm_circPt (t : ℝ) : ‖circPt t‖ = 1 := by
  simp [circPt, EuclideanSpace.norm_eq, Fin.sum_univ_five]

theorem continuous_circPt : Continuous circPt :=
  (Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)

/-- The great-circle point, as a point of the closed ball `D⁵` (it has norm `1`, so it is on `∂D⁵`). -/
def circD5 (t : ℝ) : D5 := ⟨circPt t, mem_closedBall_zero_iff.mpr (le_of_eq (norm_circPt t))⟩

theorem circD5_mem_sphere5 (t : ℝ) : circD5 t ∈ sphere5 := norm_circPt t

theorem continuous_circD5 : Continuous circD5 := continuous_circPt.subtype_mk _

/-- **The straddling 4-simplex**: `Δ⁴ → ∂D⁵`, `v ↦ cos(πv₀/2)·e₀ + sin(πv₀/2)·e₁`. It runs along a
quarter of a great circle, from `e₀` (at `v₀ = 0`) to `e₁` (at `v₀ = 1`), and its whole image lies on
the boundary sphere. -/
def straddleMap : C(↥(stdSimplex ℝ (Fin 5)), D5) :=
  ⟨fun v => circD5 (Real.pi / 2 * (v : Fin 5 → ℝ) 0), by
    exact continuous_circD5.comp
      (continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val))⟩

/-- The straddling simplex as a basis element of `C₄(D⁵)`. -/
def straddleSimplex : Simp4 :=
  ((TopCat.of D5).toSSetObjEquiv (op (SimplexCategory.mk (3 + 1)))).symm straddleMap

theorem realize4_straddleSimplex : realize4 straddleSimplex = straddleMap :=
  Equiv.apply_symm_apply _ _

/-- The straddling chain — a single basis simplex with coefficient `1`. -/
def straddleChain : SingularChain (TopCat.of D5) (3 + 1) := Finsupp.single straddleSimplex 1

/-- The witness seam: the single point `e₀` of the boundary sphere. Closed, nonempty, sphere-contained
— every hypothesis the engine places on the attaching region `S`. -/
def straddleSeam : Set D5 := {circD5 0}

theorem single_mem_stdSimplex (i : Fin 5) : Pi.single i (1 : ℝ) ∈ stdSimplex ℝ (Fin 5) :=
  ⟨fun _ => by simp [Pi.single_apply]; positivity, by simp⟩

/-- The `i`-th vertex of the standard 4-simplex. -/
def vtx (i : Fin 5) : ↥(stdSimplex ℝ (Fin 5)) := ⟨Pi.single i 1, single_mem_stdSimplex i⟩

/-- At the vertex `e₁` of `Δ⁴` the straddling simplex takes the value `circD5 0` — the seam point. -/
theorem straddleMap_vtx_one : straddleMap (vtx 1) = circD5 0 := by
  simp [straddleMap, vtx]

/-- At the vertex `e₀` of `Δ⁴` it takes the value `circD5 (π/2)` — a point off the seam. -/
theorem straddleMap_vtx_zero : straddleMap (vtx 0) = circD5 (Real.pi / 2) := by
  simp [straddleMap, vtx]

theorem circD5_pi_div_two_ne_zero : circD5 (Real.pi / 2) ≠ circD5 0 := by
  intro hEq
  have h : circPt (Real.pi / 2) = circPt 0 := congrArg Subtype.val hEq
  have h0 : (circPt (Real.pi / 2)).ofLp 0 = (circPt 0).ofLp 0 := by rw [h]
  norm_num [circPt] at h0

/-- The straddling simplex lives entirely on the boundary sphere — so the chain it spans is an
admissible `subspaceChains (U ∩ sphere)` element for the engine's cover. -/
theorem range_straddleMap_subset_sphere5 : Set.range straddleMap ⊆ sphere5 := by
  rintro _ ⟨v, rfl⟩
  exact circD5_mem_sphere5 _

/-! ## §3. The refutation. -/

theorem straddleSimplex_mem_support : straddleSimplex ∈ straddleChain.support := by
  rw [straddleChain, Finsupp.support_single_ne_zero _ (one_ne_zero)]
  exact Finset.mem_singleton_self _

/-- The witness simplex is NOT `S`-supported: it reaches `circD5 (π/2) ≠ circD5 0`. -/
theorem not_range_subset_straddleSeam :
    ¬ Set.range (realize4 straddleSimplex) ⊆ straddleSeam := by
  intro hsub
  refine circD5_pi_div_two_ne_zero ?_
  have : circD5 (Real.pi / 2) ∈ straddleSeam := by
    refine hsub ?_
    rw [realize4_straddleSimplex, ← straddleMap_vtx_zero]
    exact Set.mem_range_self _
  exact this

/-- The witness simplex is NOT free-sphere-supported either: it MEETS the seam at `circD5 0`. -/
theorem not_range_subset_free :
    ¬ Set.range (realize4 straddleSimplex) ⊆ sphere5 \ straddleSeam := by
  intro hsub
  have hmem : circD5 0 ∈ Set.range (realize4 straddleSimplex) := by
    rw [realize4_straddleSimplex, ← straddleMap_vtx_one]
    exact Set.mem_range_self _
  exact (hsub hmem).2 rfl

/-- **THE REFUTATION.** The bridge fails for the single-simplex chain spanned by the straddler. -/
theorem not_attachedBridge_straddle :
    ¬ ClosedSeamAttachedCollarBridge straddleSeam straddleChain := by
  intro h
  rcases support_dichotomy_of_attachedBridge h straddleSimplex_mem_support with h1 | h1
  · exact not_range_subset_straddleSeam h1
  · exact not_range_subset_free h1

theorem straddleChain_mem_subspaceChains :
    straddleChain ∈ subspaceChains (X := TopCat.of D5) (Set.univ ∩ sphere5) (3 + 1) := by
  refine single_mem_subspaceChains_of_subordinate ?_
  rw [Set.univ_inter]
  -- v4.32: `realize4` is an `abbrev` (reducible), and the goal now arrives with it already
  -- delta-reduced, so `simp only [realize4_straddleSimplex]` finds no `realize4` to rewrite.
  -- Re-fold it by type ascription (defeq through the abbrev), rewrite there, then close.
  have h : Set.range ⇑(realize4 straddleSimplex) ⊆ sphere5 := by
    rw [realize4_straddleSimplex]
    exact range_straddleMap_subset_sphere5
  exact h

theorem isClosed_straddleSeam : IsClosed straddleSeam := isClosed_singleton

theorem straddleSeam_subset_sphere5 : straddleSeam ⊆ sphere5 :=
  Set.singleton_subset_iff.mpr (circD5_mem_sphere5 0)

/-- **`ClosedSeamAttachedCollarBridge` IS FALSE — the settled no-go for `#212` item d.**

There exist a CLOSED NONEMPTY seam `S` contained in the boundary sphere, an OPEN `U ⊇ S` satisfying
the engine's own cover hypothesis `sphere ⊆ U ∪ Sᶜ` verbatim (the hypothesis of
`diskDetectChain_subtype_boundary_split_freeSphere`), and an attached chain `a` supported in
`U ∩ sphere` — precisely the shape the engine's split produces — for which the bridge FAILS.

Hence no proof of `ClosedSeamAttachedCollarBridge` can exist at the generality at which it is stated
and at which `exact_seam_split_of_attachedBridge` consumes it. Any discharge of the disk-side seam
decomposition must instead CERTIFY that the produced split has no straddling simplex (§1's
`attachedBridge_iff_support_dichotomy` says that certificate is exactly equivalent to the bridge) —
or, as the collar-pair row in fact does, ask for the remainder off a builder-chosen core `K` rather
than off `S`, which the open-cover engine reaches directly
(`PinPlusTraceCapstoneCollarPairHandle.exists_ctrlHandle_split_offCore`). -/
theorem collar_bridge_refuted :
    ∃ (S U : Set D5) (a : SingularChain (TopCat.of D5) (3 + 1)),
      IsClosed S ∧ S.Nonempty ∧ S ⊆ sphere5 ∧ IsOpen U ∧ S ⊆ U ∧ sphere5 ⊆ U ∪ Sᶜ
        ∧ a ∈ subspaceChains (X := TopCat.of D5) (U ∩ sphere5) (3 + 1)
        ∧ ¬ ClosedSeamAttachedCollarBridge S a :=
  ⟨straddleSeam, Set.univ, straddleChain, isClosed_straddleSeam, Set.singleton_nonempty _,
    straddleSeam_subset_sphere5, isOpen_univ, Set.subset_univ _,
    fun _ _ => Or.inl (Set.mem_univ _), straddleChain_mem_subspaceChains,
    not_attachedBridge_straddle⟩

end

end SKEFTHawking.PinPlusTraceSeamCollarBridgeNoGo
