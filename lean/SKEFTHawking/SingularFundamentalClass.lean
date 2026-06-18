import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularRelativeEmpty
import SKEFTHawking.SingularGoodCompactManifold

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4p) — the [M] finale foundations (Hatcher 3.26)

Foundations for the closed-manifold fundamental class `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`:

* `restrictHomologyToPoint x` — the restriction `ρₓ : Hₙ(M) → Hₙ(M | x)` of an absolute homology class
  to the local homology at `x`, the composite `Hₙ(M) ≅[relHomologyEmptyEquiv⁻¹] Hₙ(M, ∅) → Hₙ(M, M∖x)`.
* `linearEquiv_zmod2_unique` — over `ℤ/2` there is a **unique** linear iso `V ≃ₗ ℤ/2` (the only nonzero
  scalar is `1`). This is the ℤ/2-coefficient simplification that makes the Hatcher 3.26 local-orientation
  argument elementary: any two identifications of a local homology group with `ℤ/2` agree, so the local
  value `x ↦ (Hₙ(M|x) ≅ ℤ/2)(ρₓ α)` is well-defined and (over a convex chart ball) locally constant.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty

namespace SKEFTHawking.SingularFundamentalClass

/-- **Restriction of an absolute class to the local homology at a point** `ρₓ : Hₙ(M) → Hₙ(M | x)`:
identify `Hₙ(M) ≅ Hₙ(M, ∅)` (`relHomologyEmptyEquiv`), then include the pair `(M, ∅) → (M, M∖x)`
(`relIncl`, as `∅ ⊆ {x}ᶜ`). The map whose simultaneous behaviour over all `x` detects the fundamental
class. -/
noncomputable def restrictHomologyToPoint {X : TopCat} (x : ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology ({x}ᶜ : Set ↑X) n :=
  (relIncl (Set.empty_subset ({x}ᶜ : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- **Restriction of an absolute class to the local homology over a set** `ρ_K : Hₙ(M) → Hₙ(M | K)`,
the composite `Hₙ(M) ≅ Hₙ(M, ∅) → Hₙ(M, M∖K)`. Factors `restrictHomologyToPoint y` for `y ∈ K`
(`restrictToPoint_restrictHomologyToSet`). -/
noncomputable def restrictHomologyToSet {X : TopCat} (K : Set ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology (Kᶜ : Set ↑X) n :=
  (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- **Restriction to a set then to a point equals restriction to the point**: for `y ∈ K`,
`restrictToPoint hy ∘ ρ_K = ρ_y` (functoriality of `relIncl`, `relIncl_trans`). The factoring that
lets the per-point restriction value of `α` be read off the single class `ρ_K α ∈ Hₙ(M|K)`. -/
theorem restrictToPoint_restrictHomologyToSet {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K)
    (n : ℕ) (α : Homology X n) :
    SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy n
        (restrictHomologyToSet K n α)
      = restrictHomologyToPoint y n α := by
  show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n
      (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α))
    = relIncl (Set.empty_subset ({y}ᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α)
  rw [relIncl_trans]

/-! ### `setOf`-form local restrictions (matching `manifoldLocalIso`'s domain syntactically)

`manifoldLocalIso x`'s domain is `RelativeHomology {y | y ≠ x}` (the `setOf` form, baked through the
committed chart bridge). Composing `restrictToPoint`/`restrictHomologyToPoint` (which land in the
**compl** form `{x}ᶜ`) with it forces the unifier to reduce `{x}ᶜ → {y | y ≠ x}` through the heavy
`RelativeHomology` quotient on *every* comparison — a 200k-heartbeat `isDefEq` wall (the two forms are
`rfl`-equal in isolation but lethal in the machinery). These `Ne`-variants land in the **`setOf`** form
syntactically, so the local-constancy composition is defeq-free. Each is `rfl`-equal to its compl-form
sibling (`{z | z ≠ x} = {x}ᶜ`), bridging to the rest of the finale cheaply at the `relIncl` level. -/

/-- `setOf`-form `ρₓ` — `restrictHomologyToPoint` landing in `{z | z ≠ x}` (= `{x}ᶜ`). -/
noncomputable def restrictHomologyToPointNe {X : TopCat} (x : ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology ({z | z ≠ x} : Set ↑X) n :=
  (relIncl (Set.empty_subset ({z | z ≠ x} : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- `setOf`-form restriction-to-a-point `Hₙ(M|K) → Hₙ(M|y)` (`y ∈ K`), landing in `{z | z ≠ y}`. -/
noncomputable def restrictToPointNe {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K) (n : ℕ) :
    RelativeHomology (Kᶜ : Set ↑X) n →ₗ[ZMod 2] RelativeHomology ({z | z ≠ y} : Set ↑X) n :=
  relIncl (show (Kᶜ : Set ↑X) ⊆ {z | z ≠ y} from fun _z hz hzy => hz (hzy.symm ▸ hy)) n

/-- **The `setOf`-form factoring** `restrictToPointNe hy ∘ ρ_K = ρ_yNe` (`relIncl_trans`); the
`Ne`-analogue of `restrictToPoint_restrictHomologyToSet`. All `relIncl`, no `manifoldLocalIso` — so the
`{z|z≠y}` form appears consistently and there is no cross-form defeq. -/
theorem restrictToPointNe_restrictHomologyToSet {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K)
    (n : ℕ) (α : Homology X n) :
    restrictToPointNe hy n (restrictHomologyToSet K n α) = restrictHomologyToPointNe y n α := by
  show relIncl (show (Kᶜ : Set ↑X) ⊆ {z | z ≠ y} from fun _z hz hzy => hz (hzy.symm ▸ hy)) n
      (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α))
    = relIncl (Set.empty_subset ({z | z ≠ y} : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α)
  rw [relIncl_trans]

/-- **Over `ℤ/2` a linear iso to `ℤ/2` is unique**: any two `e₁ e₂ : V ≃ₗ[ZMod 2] ZMod 2` agree, since
the only nonzero element of `ZMod 2` is `1`. The ℤ/2-orientation triviality underlying Hatcher 3.26. -/
theorem linearEquiv_zmod2_unique {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e₁ e₂ : V ≃ₗ[ZMod 2] ZMod 2) (v : V) : e₁ v = e₂ v := by
  have h0 : (e₁ v = 0) ↔ (e₂ v = 0) := by rw [e₁.map_eq_zero_iff, e₂.map_eq_zero_iff]
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases (e₁ v) with ha | ha <;> rcases hcases (e₂ v) with hb | hb
  · rw [ha, hb]
  · rw [h0] at ha; rw [ha] at hb; exact absurd hb (by decide)
  · rw [← h0] at hb; rw [hb] at ha; exact absurd ha (by decide)
  · rw [ha, hb]

/-! ## High-degree vanishing of the closed manifold -/

/-- **A closed manifold has no homology above its dimension**: `Hᵢ(M;ℤ/2) = 0` for `i > m+2`. The
absolute version of `goodCompact_univ`'s `vanishAbove (m+2) univ` (`Hᵢ(M | univ) = Hᵢ(M, ∅) = Hᵢ(M)`
via `relHomologyEmptyEquiv`). -/
theorem homology_vanish_above {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (i : ℕ) (hi : m + 2 < i)
    (α : Homology (TopCat.of M) i) : α = 0 := by
  have h := (SingularGoodCompactManifold.goodCompact_univ (m := m) (M := M)).1 i hi
  rw [Set.compl_univ] at h
  exact (relHomologyEmptyEquiv (X := TopCat.of M) i).symm.injective
    (by rw [h ((relHomologyEmptyEquiv (X := TopCat.of M) i).symm α), map_zero])

theorem restrictToPointNe_chartBall_bijective {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (y₀ : M) {r : ℝ}
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).target)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r) :
    Function.Bijective (restrictToPointNe (X := TopCat.of M) hy (m + 2)) :=
  SingularGoodCompactManifold.restrictToPoint_chartBall_bijective y₀ hrsub hy

/-- **The local-value composite `Hₘ₊₂(M|K) → ℤ/2`** for `y ∈ K`: restrict to the point `y`, then the
local-homology iso `manifoldLocalIso y`. Built as a **manual** `LinearMap` (`toFun` = the bare
application, which is well-typed) rather than `manifoldLocalIso y ∘ₗ restrictToPoint hy` — the
`∘ₗ`/`.trans` *formation* triggers the `{y}ᶜ`↔`{z|z≠y}` `RelativeHomology` congruence wall, but the
*application* does not. -/
noncomputable def localComposite {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} {y : M} (hy : y ∈ K) :
    RelativeHomology (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) (m + 2) →ₗ[ZMod 2] ZMod 2 where
  toFun z := SKEFTHawking.SingularChartBridge.manifoldLocalIso y
    (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint (X := TopCat.of M) hy (m + 2) z)
  map_add' a b := by rw [map_add]; exact map_add _ _ _
  map_smul' c a := by rw [map_smul]; exact map_smul _ _ _

/-- The local-value composite is bijective, given the restriction is bijective — proved **manually**
via injective+surjective from the component bijectivities (at the application level, so it avoids the
`∘`/`Function.comp` middle-type match that triggers the `{y}ᶜ`↔`{z|z≠y}` wall). -/
theorem localComposite_bijective {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} {y : M} (hy : y ∈ K)
    (hbij : Function.Bijective
      (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint (X := TopCat.of M) hy (m + 2))) :
    Function.Bijective (localComposite (m := m) hy) := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · -- `hab` (defeq) is `manifoldLocalIso (rtp a) = manifoldLocalIso (rtp b)`; `m` is pinned by `rtp`.
    have hab' : SKEFTHawking.SingularChartBridge.manifoldLocalIso y
        (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) a)
      = SKEFTHawking.SingularChartBridge.manifoldLocalIso y
        (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) b) := hab
    exact hbij.injective
      ((SKEFTHawking.SingularChartBridge.manifoldLocalIso y).injective hab')
  · obtain ⟨u, hu⟩ := (SKEFTHawking.SingularChartBridge.manifoldLocalIso
      (m := m) (M := M) y).surjective w
    obtain ⟨z, hz⟩ := hbij.surjective u
    refine ⟨z, ?_⟩
    show SKEFTHawking.SingularChartBridge.manifoldLocalIso y
      (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) z) = w
    rw [hz, hu]

/-- **The two local-value composites on a chart ball agree** (Hatcher 3.26 local constancy, abstract
form): for `y₁, y₂` in `K = (chartAt y₀).symm '' B̄(chartAt y₀ · y₀, r)`, the composites
`localComposite hy₁`, `localComposite hy₂ : Hₘ₊₂(M|K) ≃ ℤ/2` agree on every class — each is an iso
(`localComposite_bijective`), and over `ℤ/2` linear isos to `ℤ/2` are unique (`linearEquiv_zmod2_unique`).
Applied to `ρ_K α` this says `f(y₁) = f(y₂)` (the fundamental-class restriction value is locally
constant); the per-point connection `f(y) = localComposite hy (ρ_K α)` is the factoring
`restrictToPoint_restrictHomologyToSet`. -/
theorem localComposite_agree_chartBall {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (y₀ : M) {r : ℝ}
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).target) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r)
    (hy₂ : y₂ ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r)
    (z : RelativeHomology (X := TopCat.of M)
      (((chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin (m + 2))) y₀ y₀) r)ᶜ) (m + 2)) :
    localComposite (m := m) hy₁ z = localComposite (m := m) hy₂ z :=
  linearEquiv_zmod2_unique
    (LinearEquiv.ofBijective (localComposite (m := m) hy₁)
      (localComposite_bijective hy₁
        (SingularGoodCompactManifold.restrictToPoint_chartBall_bijective y₀ hrsub hy₁)))
    (LinearEquiv.ofBijective (localComposite (m := m) hy₂)
      (localComposite_bijective hy₂
        (SingularGoodCompactManifold.restrictToPoint_chartBall_bijective y₀ hrsub hy₂)))
    z

/-- **`localComposite hy z = 0 ↔ restrictToPoint hy z = 0`** — `manifoldLocalIso y` is injective on
values (referenced in the *application* `manifoldLocalIso y (restrictToPoint hy z)`, never composed),
so the composite vanishes iff the restriction does. The bridge from the (defeq-safe) `localComposite`
form to the bare `restrictToPoint` form used by `determinedByPoints`. -/
theorem localComposite_eq_zero_iff {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {K : Set M} {y : M} (hy : y ∈ K)
    (z : RelativeHomology (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) (m + 2)) :
    localComposite (m := m) hy z = 0
      ↔ SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) z = 0 := by
  show SKEFTHawking.SingularChartBridge.manifoldLocalIso y
      (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) z) = 0
    ↔ SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy (m + 2) z = 0
  exact (SKEFTHawking.SingularChartBridge.manifoldLocalIso y).map_eq_zero_iff

/-- **Local constancy of the per-point restriction-vanishing of a fixed class** (Hatcher 3.26): for
`α : Hₘ₊₂(M)` and any `x₀`, the chart-ball neighbourhood `U = interior((chartAt x₀).symm '' B̄)` is open,
contains `x₀`, and on it `restrictHomologyToPoint y α = 0 ↔ restrictHomologyToPoint x₀ α = 0`. On a
chart ball the local-value composite is constant (`localComposite_agree_chartBall`), the composite
vanishes iff the bare restriction does (`localComposite_eq_zero_iff`), and the restriction to a set
factors the per-point restriction (`restrictToPoint_restrictHomologyToSet`). The engine that makes the
vanishing set `{x | restrictHomologyToPoint x α = 0}` clopen — hence (`M` connected) all-or-nothing. -/
theorem restrictHomologyToPoint_locally_constant {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (α : Homology (TopCat.of M) (m + 2)) (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∀ y ∈ U,
      (restrictHomologyToPoint (X := TopCat.of M) y (m + 2) α = 0
        ↔ restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) α = 0) := by
  obtain ⟨r, _hr, hrsub, hx₀int⟩ := SingularGoodCompactManifold.exists_chartBall_nbhd (m := m) x₀
  set c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x₀ with hc
  set K : Set M := c.symm '' Metric.closedBall (c x₀) r with hK
  refine ⟨interior K, isOpen_interior, hx₀int, fun y hy => ?_⟩
  have hyK : y ∈ K := interior_subset hy
  have hx₀K : x₀ ∈ K := interior_subset hx₀int
  have hagree :
      localComposite (m := m) hx₀K (restrictHomologyToSet (X := TopCat.of M) K (m + 2) α)
        = localComposite (m := m) hyK (restrictHomologyToSet (X := TopCat.of M) K (m + 2) α) :=
    localComposite_agree_chartBall (m := m) x₀ hrsub hx₀K hyK _
  rw [← restrictToPoint_restrictHomologyToSet hyK (m + 2) α,
      ← restrictToPoint_restrictHomologyToSet hx₀K (m + 2) α,
      ← localComposite_eq_zero_iff hyK, ← localComposite_eq_zero_iff hx₀K, hagree]

/-- **Injectivity of the per-point restriction on a connected closed manifold** (Hatcher 3.26,
kernel-triviality half of `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`): a class `α : Hₘ₊₂(M)` that restricts to `0` at a
single point `x₀` is `0`. The vanishing set `S = {x | restrictHomologyToPoint x α = 0}` is **clopen**
(both `S` and `Sᶜ` are open by local constancy, `restrictHomologyToPoint_locally_constant`); `M`
connected and `x₀ ∈ S` force `S = univ`, so `α` restricts to `0` at every point; then
`determinedByPoints` (`goodCompact_univ`) gives `α = 0`. (`(univ)ᶜ = ∅`, so the determined-by-points
class is `(relHomologyEmptyEquiv).symm α`, and `restrictToPoint` of it at `x` is the per-point
restriction `restrictHomologyToPoint x α` — proof-irrelevantly, as both are `relIncl … ((relHomologyEmptyEquiv).symm α)`.) -/
theorem restrictHomologyToPoint_injective {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {α : Homology (TopCat.of M) (m + 2)} {x₀ : M}
    (hx₀ : restrictHomologyToPoint (X := TopCat.of M) x₀ (m + 2) α = 0) : α = 0 := by
  set S : Set M := {x | restrictHomologyToPoint (X := TopCat.of M) x (m + 2) α = 0} with hS
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hUopen, hxU, hUconst⟩ := restrictHomologyToPoint_locally_constant α x
    exact ⟨U, fun y hy => (hUconst y hy).mpr hx, hUopen, hxU⟩
  have hScopen : IsOpen Sᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hUopen, hxU, hUconst⟩ := restrictHomologyToPoint_locally_constant α x
    exact ⟨U, fun y hy hyS => hx ((hUconst y hy).mp hyS), hUopen, hxU⟩
  have hSclopen : IsClopen S := ⟨isOpen_compl_iff.mp hScopen, hSopen⟩
  have hSuniv : S = Set.univ := hSclopen.eq_univ ⟨x₀, hx₀⟩
  have hall : ∀ x : M, restrictHomologyToPoint (X := TopCat.of M) x (m + 2) α = 0 :=
    Set.eq_univ_iff_forall.mp hSuniv
  -- determined-by-points on `univ`: `ρ_univ α` restricts to `0` at every point, hence is `0`.
  have hdet := (SingularGoodCompactManifold.goodCompact_univ (m := m) (M := M)).2
  have hβ0 : restrictHomologyToSet (X := TopCat.of M) (Set.univ : Set ↑(TopCat.of M)) (m + 2) α = 0 :=
    hdet (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) (m + 2) α)
      (fun x hx => by rw [restrictToPoint_restrictHomologyToSet hx (m + 2) α]; exact hall x)
  -- `ρ_univ` is injective: `relIncl (univᶜ ⊆ ∅)` left-inverts `relIncl (∅ ⊆ univᶜ)` (≡ `id` on `H(M|∅)`).
  have huniv_empty : (Set.univ : Set ↑(TopCat.of M))ᶜ ⊆ (∅ : Set ↑(TopCat.of M)) := Set.compl_univ.subset
  have hγ : (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α = 0 := by
    have hback : relIncl huniv_empty (m + 2)
        (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) (m + 2) α)
        = (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α := by
      show relIncl huniv_empty (m + 2)
          (relIncl (Set.empty_subset (Set.univ : Set ↑(TopCat.of M))ᶜ) (m + 2)
            ((relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α))
        = (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α
      rw [relIncl_trans, relIncl, SKEFTHawking.SingularRelativeFunctoriality.RelativeHomology.map_id]
      rfl
    rw [hβ0, map_zero] at hback
    exact hback.symm
  have hα := congrArg (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)) hγ
  rwa [LinearEquiv.apply_symm_apply, map_zero] at hα

end SKEFTHawking.SingularFundamentalClass
