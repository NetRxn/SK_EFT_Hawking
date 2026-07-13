/-
# Phase 5q.H (W-A.1c) — the relative mod-2 fundamental class `[W,∂W]` and its functional μ

The deep geometric input the Poincaré–Lefschetz Wu tower (`PoincareLefschetzWu5`) consumes: the
**relative mod-2 fundamental class** `[W,∂W] ∈ Hₙ(W, ∂W; ℤ/2)` of a compact charted
manifold-with-boundary, and the **functional** `μ = ⟨·, [W,∂W]⟩ : Hⁿ(W,∂W;ℤ/2) → ℤ/2` that is the
`mu` field of `LefschetzWuDatum`. Built bottom-up on the project's genuine singular ℤ/2
(co)homology.

## The boundary-as-`Set` setting (design-forcing, matching `PoincareLefschetzWu5`)

`Mathlib.ModelWithCorners.boundary J W` is only a **`Set W`** (`InteriorBoundary.lean`; the
boundary-as-manifold is unproven), and
`ModelWithCorners.interior J W = (ModelWithCorners.boundary J W)ᶜ` (`compl_boundary`). So
everything here uses the boundary/interior purely as subspaces of `X := TopCat.of W` and the
in-tree relative machinery `SingularRelativeHomologyMod2.RelativeHomology (S : Set X)` for the
**arbitrary** subspace `S := ∂W`. No boundary-manifold datum is ever formed.

## The class shape (relative analogue of `SingularFundamentalClass.fundamentalClass_restricts`)

For a closed manifold, `[M] ∈ Hₙ(M)` is characterised by
`restrictHomologyToPoint x [M] = generatorₓ` at **every** point (`fundamentalClass_restricts`).
For the pair `(W, ∂W)` the class lives in `Hₙ(W, ∂W) = RelativeHomology (∂W) n` and its
characterising property is one-sided:

* at an **interior** point `x ∈ int W = (∂W)ᶜ`, the local homology `Hₙ(W, W∖x) ≅ ℤ/2` is the same
  as the closed case (the chart at an interior point is Euclidean —
  `SingularChartBridge.chartLocalIso` applies verbatim to any interior Euclidean chart), and
  `[W,∂W]` restricts to its generator;
* at a **boundary** point `x ∈ ∂W`, the half-space local homology `Hₙ(W, W∖x)` **vanishes** —
  this is exactly what makes the class *relative*; boundary points impose no condition. (This
  restriction map is not even formed here: the restriction `restrictBd` is only defined for
  `x ∉ S`.)

`restrictBd S hx n : Hₙ(W, ∂W) → Hₙ(W, W∖x)` is the interior-point restriction (`relIncl` over
`∂W ⊆ {x}ᶜ`, available exactly because `x ∉ ∂W`). `RestrictsToRelGen S gen α` is the relative
analogue of `restrictsToGenerator`: `restrictBd α = gen⁻¹ 1` at every interior point, where
`gen x hx` is the interior local iso `Hₙ(W, W∖x) ≅ ℤ/2`. `HasRelFundClass` asserts such a class
exists.

## Route decision for existence (design item 2)

The closed-case existence (`SingularFundamentalClass.hasFundClass_univ`) covers a **compact**
manifold by finitely many chart balls and glues via relative Mayer–Vietoris
(`hasFundClass_biUnion`). The interior `int W` is an **open, non-compact** manifold, so that cover
argument does not transfer verbatim. Two routes were weighed:
* **direct pair-cover** — adapt the compact chart-ball cover of `W` (which *is* compact) to the
  pair, splitting interior vs boundary charts. This is the honest route but needs the
  interior/boundary chart extraction from `ModelWithCorners` (thin in Mathlib) + a half-space
  relative-MV step;
* **double `DW = W ∪_∂ W`** — the closed double's fundamental class restricts. Rejected: the
  in-tree machinery has **no manifold gluing**, so `DW` cannot be formed.

**Decision: the direct pair-cover route.** This module banks the route-independent layers
(restriction machinery, characterisation, uniqueness, the μ functional) and the interior-local-iso
wrapper; the compact chart-cover existence assembly and the two `ModelWithCorners` geometric
discharges are the named remaining obligations (below), to be shipped as later slices (1d/1e) —
exactly as the closed case discharged its `PoincareDual4*` instances (`SingularPD4Instances`)
after the abstract tower.

## Named-slice map (the remaining obligations, all stated, none faked)

* `interiorPoint_hasEuclChart` — an interior point `x ∈ int W` of a compact `C^k` (`k ≥ 1`)
  manifold-with-boundary has an open Euclidean chart `U ∋ x`, `e : U ≃ₜ V ⊆ ℝⁿ` open, `e x ∈ V`.
  Feeds `chartLocalIso` to instantiate `gen` at interior points. (Mathlib: `extChartAt` on
  `int W` lands in `interior (range J)`; compose with `E' ≃L EuclideanSpace ℝ (Fin n)`.)
* `boundaryPoint_localHomology_zero` — at a boundary point, `Hₙ(W, W∖x) = 0` (half-space local
  homology vanishes: the half-space is convex/contractible and its complement of a boundary point
  is star-convex — `SingularStarConvexSlit.starConvexContraction` — so the pair LES gives 0). The
  genuinely-new *relative* content; a half-space analogue of `manifoldConvexLocalHomologyIso`.
* `hasRelFundClass_of_compact` — existence: the compact chart-cover of `W` glued via relative MV,
  using the interior charts for the generator condition and boundary-vanishing to kill the
  boundary contributions. Consumes the two obligations above + a half-space relative-MV union
  step.

All cohomology/homology is the project's genuine singular ℤ/2 theory. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.PoincareLefschetzWu5

namespace SKEFTHawking.PoincareLefschetzRelFundClass

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularChartBridge
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2

variable {X : TopCat}

/-! ## §1. Restriction of a relative class to an interior (non-boundary) point -/

/-- **Restriction to an interior point** `Hₙ(W, ∂W) → Hₙ(W, W∖x)` for `x ∉ ∂W` (i.e.
`x ∈ int W`): the inclusion-of-pairs map for `∂W ⊆ {x}ᶜ`, available exactly because `x` is not on
the boundary. `Hₙ(W, W∖x) = RelativeHomology {x}ᶜ n` is the local homology at `x`. Boundary points
are excluded by `hx : x ∉ S`, so no restriction is ever formed at the boundary — the source of the
class being *relative*. -/
noncomputable def restrictBd (S : Set ↑X) {x : ↑X} (hx : x ∉ S) (n : ℕ) :
    RelativeHomology S n →ₗ[ZMod 2] RelativeHomology ({x}ᶜ) n :=
  relIncl (Set.subset_compl_singleton_iff.mpr hx) n

/-- **Restriction factors through a sub-restriction**: for `S' ⊆ S` with `x ∉ S` (hence
`x ∉ S'`), restricting `Hₙ(W, S') → Hₙ(W, W∖x)` equals first including `Hₙ(W, S') → Hₙ(W, S)`
then restricting. The functoriality the existence MV induction transports the generator condition
along. -/
theorem restrictBd_relIncl (S S' : Set ↑X) (hS' : S' ⊆ S) {x : ↑X} (hx : x ∉ S) (n : ℕ)
    (α : RelativeHomology S' n) :
    restrictBd S hx n (relIncl hS' n α)
      = restrictBd S' (fun hxS' => hx (hS' hxS')) n α := by
  rw [restrictBd, restrictBd, relIncl_trans]

/-! ## §2. The relative fundamental-class functional `μ = ⟨·, [W,∂W]⟩`

Given a relative fundamental **homology** class `z ∈ Hₙ(W, ∂W)`, its Kronecker pairing with
relative **cohomology** is the functional the Lefschetz Wu datum consumes. This reuses the
project's genuine relative Kronecker pairing `SingularRelativePairing.relKroneckerH` (no new
pairing is built). -/

/-- **The relative fundamental-class functional** `μ = ⟨·, z⟩ : Hⁿ(W,∂W) → ℤ/2`, the Kronecker
pairing of relative cohomology against a fixed relative homology class `z ∈ Hₙ(W,∂W)`. For
`z = [W,∂W]` this is the `mu` field of `PoincareLefschetzWu5.LefschetzWuDatum`. -/
noncomputable def relFundFunctional (S : Set ↑X) {N : ℕ} (z : RelativeHomology S (N + 1)) :
    RelativeCohomology S (N + 1) →ₗ[ZMod 2] ZMod 2 :=
  (relKroneckerH S).flip z

/-- `μ(ω) = ⟨ω, z⟩` computes as the relative Kronecker pairing. -/
theorem relFundFunctional_apply (S : Set ↑X) {N : ℕ} (z : RelativeHomology S (N + 1))
    (ω : RelativeCohomology S (N + 1)) :
    relFundFunctional S z ω = relKroneckerH S ω z := rfl

/-! ## §3. The relative-fundamental-class characterisation, its uniqueness, and the class datum -/

/-- **A class restricts to the interior generator** (relative analogue of
`SingularFundamentalClass.restrictsToGenerator`): `restrictBd α = (gen x hx)⁻¹ 1` at every
interior point `x ∉ S`, where `gen x hx : Hₙ(W, W∖x) ≅ ℤ/2` is the interior local iso. Boundary
points impose nothing. -/
def RestrictsToRelGen {m : ℕ} (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (α : RelativeHomology S (m + 2)) : Prop :=
  ∀ (x : ↑X) (hx : x ∉ S), restrictBd S hx (m + 2) α = (gen x hx).symm 1

/-- **`Hₙ(W, ∂W)` has a relative fundamental class**: some class restricts to the interior
generator at every interior point. The relative analogue of
`SingularFundamentalClass.hasFundClass`. -/
def HasRelFundClass {m : ℕ} (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2)) : Prop :=
  ∃ α : RelativeHomology S (m + 2), RestrictsToRelGen S gen α

/-- **Determined by interior points** (relative analogue of
`SingularManifoldFundamentalClass.determinedByPoints`): a class in `Hₙ(W, ∂W)` that restricts to
`0` in `Hₙ(W, W∖x)` for every interior point `x ∉ S` is itself `0`. For a compact
manifold-with-boundary this holds at `n = dim W` and pins the relative fundamental class
(uniqueness below). -/
def DeterminedByInteriorPoints (S : Set ↑X) (n : ℕ) : Prop :=
  ∀ α : RelativeHomology S n, (∀ (x : ↑X) (hx : x ∉ S), restrictBd S hx n α = 0) → α = 0

/-- **Uniqueness of the relative fundamental class** (given determined-by-interior-points): two
classes that both restrict to the interior generator everywhere are equal. Their difference
restricts to `0` at every interior point, so `DeterminedByInteriorPoints` forces it to vanish. The
relative analogue of the injective half of `Hₙ(M) ≅ ℤ/2`. -/
theorem relFundClass_unique {m : ℕ} (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hdet : DeterminedByInteriorPoints S (m + 2)) {α β : RelativeHomology S (m + 2)}
    (hα : RestrictsToRelGen S gen α) (hβ : RestrictsToRelGen S gen β) : α = β := by
  have h : α - β = 0 := hdet _ (fun x hx => by rw [map_sub, hα x hx, hβ x hx, sub_self])
  exact sub_eq_zero.mp h

/-- **A relative fundamental-class datum** for the pair `(W, ∂W)` (`X := TopCat.of W`,
`S := ∂W`): the class `[W,∂W]`, the interior local-iso family `gen`, and the proof that the class
restricts to the generator at every interior point. Bundles exactly the data the functional `μ`
and the Wu tower consume (matching the `LefschetzWuDatum` bundle-the-manifestation design). The
geometric construction of a datum from a compact manifold-with-boundary is the named remaining
obligation `hasRelFundClass_of_compact`. -/
structure RelFundClassDatum {m : ℕ} (S : Set ↑X) where
  /-- The relative fundamental class `[W,∂W] ∈ Hₙ(W, ∂W)`. -/
  cls : RelativeHomology S (m + 2)
  /-- The interior local-homology iso family `Hₙ(W, W∖x) ≅ ℤ/2` at interior points `x ∉ S`. -/
  gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2)
  /-- `[W,∂W]` restricts to the local generator at every interior point. -/
  restricts : RestrictsToRelGen S gen cls

/-- **The `μ` functional of a relative fundamental-class datum**, `μ = ⟨·, [W,∂W]⟩`. This is
precisely the `mu` field a `PoincareLefschetzWu5.LefschetzWuDatum X S k nk (m+2)` expects (same
type), so a datum supplies the deepest input of the Wu tower. -/
noncomputable def RelFundClassDatum.mu {m : ℕ} {S : Set ↑X} (D : RelFundClassDatum (m := m) S) :
    RelativeCohomology S (m + 2) →ₗ[ZMod 2] ZMod 2 :=
  relFundFunctional S D.cls

/-- `μ(ω) = ⟨ω, [W,∂W]⟩` for a datum. -/
theorem RelFundClassDatum.mu_apply {m : ℕ} {S : Set ↑X} (D : RelFundClassDatum (m := m) S)
    (ω : RelativeCohomology S (m + 2)) : D.mu ω = relKroneckerH S ω D.cls := rfl

/-! ## §4. The interior/boundary local-homology dichotomy

The two local models that make `[W,∂W]` *relative*. At an **interior** point the local homology
is `ℤ/2` (same as the closed case — a Euclidean chart via `SingularChartBridge.chartLocalIso`);
at a **boundary** point it **vanishes**. The boundary vanishing is the abstract heart of the pair
`(W, ∂W)`: it holds precisely because both the ambient half-space *and* its puncture are acyclic
— in contrast to an interior point, whose puncture is a sphere `S^{n-1}` with
`H_{n-1} ≅ ℤ/2 ≠ 0`. -/

/-- **Interior local-homology iso** `Hₙ(W, W∖x) ≅ ℤ/2` at an interior point, from a Euclidean
chart around `x` (`e : U ≃ₜ V` onto an open `V ⊆ ℝⁿ`, `e x = q ∈ V`). This is the closed-case
`SingularChartBridge.chartLocalIso` re-exported in the `{x}ᶜ` phrasing of `restrictBd`; it
instantiates the `gen` field of a `RelFundClassDatum` at interior points once an interior chart
is supplied (the named obligation `interiorPoint_hasEuclChart`). Interior charts give a *full*
Euclidean neighbourhood, so this is `ℤ/2` (not `0`). -/
noncomputable def interiorLocalIso {m : ℕ} [T1Space ↑X] {x : ↑X} {U : Set ↑X} (hU : IsOpen U)
    (hx : x ∈ U) {q : ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))} (hV : IsOpen V) (hq : q ∈ V) (e : ↥U ≃ₜ ↥V)
    (hex : (e ⟨x, hx⟩ : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) = q) :
    RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  chartLocalIso hU hx hV hq e hex

/-- **Boundary local-homology vanishing** — the abstract mechanism `Hₙ(W, W∖x) = 0` at a boundary
point. It holds whenever the ambient (`X` = the half-space chart) is acyclic in degrees `n = m+2`
and `n-1 = m+1`, *and* the puncture `X∖x` is acyclic in degree `m+1`. The acyclic-ambient
pair-LES connecting iso (`connectingEquiv_of_acyclic`) identifies `Hₙ(X, X∖x) ≅ H_{n-1}(X∖x)`,
which then vanishes. For a boundary point the half-space is convex (contractible) and its
puncture is star-convex (`SingularStarConvexSlit.starConvexContraction`), so both hypotheses hold
— *this* is why the class is relative. For an interior point the puncture is a sphere with
`H_{n-1} ≅ ℤ/2 ≠ 0`, so the hypothesis `hpunct` fails and the local homology is `ℤ/2` instead
(see `interiorLocalIso`). -/
theorem localHomology_eq_zero_of_acyclic_puncture {Y : TopCat} (q : ↑Y) (m : ℕ)
    (hY1 : ∀ y : Homology Y (m + 2), y = 0) (hY0 : ∀ y : Homology Y (m + 1), y = 0)
    (hpunct : ∀ y : Homology (sub ({q}ᶜ : Set ↑Y)) (m + 1), y = 0)
    (α : RelativeHomology ({q}ᶜ : Set ↑Y) (m + 2)) : α = 0 := by
  have e := connectingEquiv_of_acyclic ({q}ᶜ : Set ↑Y) (m + 1) hY1 hY0
  rw [← e.symm_apply_apply α, hpunct (e α), map_zero]

/-! ## §5. Feeding the relative fundamental class into the Poincaré–Lefschetz Wu tower

The `mu` field of `PoincareLefschetzWu5.LefschetzWuDatum X S k nk (m+2)` is exactly the relative
fundamental-class functional `μ = ⟨·, [W,∂W]⟩`. This section wires a `RelFundClassDatum` into a
full `LefschetzWuDatum`: `mu := D.mu`, with the remaining Lefschetz manifestations (`cup`,
`sqOp`, the finite dimensionality, non-degeneracy, and the Betti equality) supplied as arguments
— matching how the closed 4-manifold tower assembled `PoincareDual4Lo` from the fundamental
functional plus the abstract cup/Sq. The point: the deep geometric input `[W,∂W]` produced here
*is* the `mu` the Wu class consumes. -/

/-- **Assemble a `LefschetzWuDatum` from a relative fundamental-class datum**: its `mu` is the
relative fundamental-class functional `⟨·, [W,∂W]⟩`, and the remaining Lefschetz manifestations
are supplied. Confirms `RelFundClassDatum` produces the deepest field the Wu tower consumes. -/
noncomputable def RelFundClassDatum.toLefschetzWuDatum {m : ℕ} {S : Set ↑X}
    (D : RelFundClassDatum (m := m) S) {k nk : ℕ}
    (cup : Cohomology X k →ₗ[ZMod 2]
      RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S (m + 2))
    (sqOp : RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S (m + 2))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X k))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S nk))
    (nondeg : Function.Injective ⇑(cup.compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X k)
           = Module.finrank (ZMod 2) (RelativeCohomology S nk)) :
    PoincareLefschetzWu5.LefschetzWuDatum X S k nk (m + 2) where
  mu := D.mu
  cup := cup
  sqOp := sqOp
  findimAbs := findimAbs
  findimRel := findimRel
  nondeg := nondeg
  dimeq := dimeq

/-- The assembled Lefschetz datum's `mu` is exactly the relative fundamental-class functional. -/
theorem RelFundClassDatum.toLefschetzWuDatum_mu {m : ℕ} {S : Set ↑X}
    (D : RelFundClassDatum (m := m) S) {k nk : ℕ}
    (cup : Cohomology X k →ₗ[ZMod 2]
      RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S (m + 2))
    (sqOp : RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S (m + 2))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X k))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S nk))
    (nondeg : Function.Injective ⇑(cup.compr₂ D.mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X k)
           = Module.finrank (ZMod 2) (RelativeCohomology S nk)) :
    (D.toLefschetzWuDatum cup sqOp findimAbs findimRel nondeg dimeq).mu = D.mu := rfl

end SKEFTHawking.PoincareLefschetzRelFundClass
