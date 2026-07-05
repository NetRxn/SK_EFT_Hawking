import Mathlib
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SingularRelativeFunctorialityInt
import SKEFTHawking.SingularChartBridge

/-!
# Assembling the integral local-homology iso `H₄(M, M∖x; ℤ) ≅ ℤ` (brick 14f)

Composes brick 13's `localHomologyInt_reduces_to_sphere` (`H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)` as a bijection)
with brick 14e's `H3S3IsoInt` (`H₃(S³;ℤ) ≅ ℤ`) to get the **Euclidean-model** integral local iso
`H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ` (`euclLocalHomologyIsoInt`), and via 14d chart excision the **general-manifold**
integral local iso `H₄(M, M∖x; ℤ) ≅ ℤ` (`manifoldLocalHomologyIsoInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularLineMinusPointInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularLocalHomologyIsoInt

open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularPuncturedRetract (normalize)
open SKEFTHawking.SingularLocalHomologyInt (localHomologyInt_reduces_to_sphere)

/-- **The Euclidean-model integral local iso `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ`.** Brick 13's tower
`H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)` (a bijection) composed with brick 14e's `H₃(S³;ℤ) ≅ ℤ`
(`H3S3IsoInt`). The `SingularPuncturedRetract.Sph 4` (sphere in ℝ⁴ = S³) target of brick 13 is defeq
to the `SingularSphereAcyclic.Sph 3` of `H3S3IsoInt`. -/
noncomputable def euclLocalHomologyIsoInt :
    RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 4 ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective
      ((Homology.mapInt (normalize (n := 4)) 3).comp (connectingInt (X := Eucl 4) {x | x ≠ 0} 3))
      (localHomologyInt_reduces_to_sphere 4 2)).trans H3S3IsoInt

/-! ## §2. The translated Euclidean model `H₄(ℝ⁴, ℝ⁴∖p; ℤ) ≅ ℤ` -/

open SKEFTHawking.SingularLocalModelChart
  (transl transl_comp_transl_neg transl_neg_comp_transl mapsTo_transl mapsTo_transl_neg)
open SKEFTHawking.SingularRelativeFunctorialityInt (RelHomologyInt.map RelHomologyInt.map_bijective_of_comp_id)

/-- **`H₄(ℝ⁴, ℝ⁴∖p; ℤ) ≅ ℤ`** for any point `p` — the translated local model (`y ↦ y − p` is a
homeomorphism of pairs `(ℝ⁴, ℝ⁴∖p) → (ℝ⁴, ℝ⁴∖0)`). Integral mirror of `localHomologyAtPointIso`. -/
noncomputable def localHomologyAtPointIsoInt (p : EuclideanSpace ℝ (Fin 4)) :
    RelHomologyInt (X := Eucl 4) {y | y ≠ p} 4 ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective (RelHomologyInt.map (transl p) (mapsTo_transl p) 4)
      (RelHomologyInt.map_bijective_of_comp_id (transl p) (transl (-p)) (mapsTo_transl p)
        (mapsTo_transl_neg p) (transl_neg_comp_transl p) (transl_comp_transl_neg p) 4)).trans
    euclLocalHomologyIsoInt

/-! ## §3. Open-point excision + chart-pair transport (integral) -/

open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularChartBridge (cover_ne_point_open)

/-- **Open-point excision** (integral): `Hₙ₊₁(V, V∖q; ℤ) ≅ Hₙ₊₁(X, X∖q; ℤ)` for `V` open, `q ∈ V`
(`T1` space). Instance of `excisionEquivInt` with the cover `{X∖q, V}`. -/
noncomputable def openPointExcisionEquivInt {X : TopCat} [T1Space ↑X] {q : ↑X} {V : Set ↑X}
    (hV : IsOpen V) (hq : q ∈ V) (n : ℕ) :
    RelHomologyInt (restr {y | y ≠ q} V) (n + 1)
      ≃ₗ[ℤ] RelHomologyInt {y | y ≠ q} (n + 1) :=
  excisionEquivInt {y | y ≠ q} V n (cover_ne_point_open hV hq)

/-- The chart homeo maps `(U, U∖x)` to `(V, V∖q)` (inline, dimension-agnostic — avoids the generic-`m`
`Eucl (m+2)` unification wall of `SingularChartBridge.mapsTo_chart`). -/
theorem mapsTo_chartInt {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U)
    {Y : TopCat} {q : ↑Y} {V : Set ↑Y} (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑Y) = q) :
    Set.MapsTo (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (restr {y | y ≠ x} U)
      (restr {y | y ≠ q} V) := by
  intro u hu
  simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, ContinuousMap.coe_mk] at hu ⊢
  intro hval
  exact hu (congrArg Subtype.val (e.injective (Subtype.ext (hval.trans hex.symm))))

theorem mapsTo_chart_symmInt {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U)
    {Y : TopCat} {q : ↑Y} {V : Set ↑Y} (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑Y) = q) :
    Set.MapsTo (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (restr {y | y ≠ q} V)
      (restr {y | y ≠ x} U) := by
  intro v hv
  simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, ContinuousMap.coe_mk] at hv ⊢
  intro hval
  apply hv
  have h2 : v = e ⟨x, hx⟩ := by rw [← (Subtype.ext hval : e.symm v = ⟨x, hx⟩), e.apply_symm_apply]
  rw [h2]; exact hex

/-- **The chart-pair homeomorphism induces an integral relative-homology iso** `Hₖ(U, U∖x;ℤ) ≅
Hₖ(V, V∖q;ℤ)`. -/
noncomputable def chartPairEquivInt {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U)
    {Y : TopCat} {q : ↑Y} {V : Set ↑Y} (e : ↥U ≃ₜ ↥V)
    (hex : (e ⟨x, hx⟩ : ↑Y) = q) (k : ℕ) :
    RelHomologyInt (restr {y | y ≠ x} U) k ≃ₗ[ℤ] RelHomologyInt (restr {y | y ≠ q} V) k :=
  LinearEquiv.ofBijective
    (RelHomologyInt.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (mapsTo_chartInt hx e hex) k)
    (RelHomologyInt.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (mapsTo_chartInt hx e hex)
      (mapsTo_chart_symmInt hx e hex)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

/-- **The integral chart↔excision bridge `H₄(M, M∖x; ℤ) ≅ ℤ`**: excise `M∖U` to a chart domain,
transport by the chart homeo of pairs to `(V, V∖q) ⊆ ℝ⁴`, excise `ℝ⁴∖V`, apply the translated local
model. Integral mirror of `chartLocalIso`. -/
noncomputable def chartLocalIsoInt {M : TopCat} [T1Space ↑M] {x : ↑M} {U : Set ↑M} (hU : IsOpen U)
    (hx : x ∈ U) {q : ↑(Eucl 4)} {V : Set ↑(Eucl 4)} (hV : IsOpen V)
    (hq : q ∈ V) (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl 4)) = q) :
    RelHomologyInt (X := M) {y | y ≠ x} 4 ≃ₗ[ℤ] ℤ :=
  (openPointExcisionEquivInt hU hx 3).symm.trans
    ((chartPairEquivInt hx e hex 4).trans
      ((openPointExcisionEquivInt hV hq 3).trans (localHomologyAtPointIsoInt q)))

/-- **The integral local homology of a topological 4-manifold is `ℤ`** at every point: for `M` a `T1`
topological manifold modeled on `ℝ⁴`, `H₄(M, M∖x; ℤ) ≅ ℤ`. The chart `chartAt x` supplies the
homeomorphism of pairs `chartLocalIsoInt` consumes. Integral mirror of `manifoldLocalIso`; the general-
manifold `iso` field of `IntLocalHomologyIso`. -/
noncomputable def manifoldLocalHomologyIsoInt {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 4 ≃ₗ[ℤ] ℤ :=
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x
  chartLocalIsoInt (M := TopCat.of M) (x := x) (U := c.source) (V := c.target) (q := c x)
    c.open_source (mem_chart_source _ x) c.open_target (mem_chart_target _ x)
    c.toHomeomorphSourceTarget rfl

end SKEFTHawking.SingularLocalHomologyIsoInt
