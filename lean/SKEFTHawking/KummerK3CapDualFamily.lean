/-
# Phase 5q.H — `hfam` AND `hpd` from ONE geometric datum: a cap-dual, cap-spanning family

`KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` owes three geometric
inputs. Two of them — `hfam` (22 classes with Gram `⟨−2⟩¹⁶ ⊕ 3H`) and `hpd` (integral Poincaré
duality at every orientation) — are *not* independent obligations once both are phrased in the
cap-dual language, and this module proves it.

## The translation

`IntersectionMatrixBasisChange.interFormInt_capDual` is the in-tree cap–cup adjunction
`⟨a ∪ b, [M]⟩ = ⟨b, a ⌢ [M]⟩` packaged for families: if `αᵢ ⌢ [M] = cᵢ` then

    ⟨αᵢ ∪ αⱼ, [M]⟩ = ⟨αⱼ, cᵢ⟩,

so the 253 **cup products** of `hfam` become 253 **Kronecker pairings** of cohomology classes
against homology classes — the shape every detection map in this arc
(`KummerT4CycleDetection.Phi1`/`Phi2`, the `Q`-side transfer, the exceptional block) actually
computes in.

## The consolidation

`KummerK3PoincareDuality.nonempty_intPD_of_capSpan` (lead-checked here: its own hypothesis list is
`{Module.Free/Finite ℤ H₂, Module.Finite ℤ H², Module.Projective ℤ (boundaries 1)}` — all
unconditional at the welded `K3` — plus a cap-**spanning** family; it mentions no Gram, so it is
**not** the banned `kummerK3_pdInput_of_gram` circle of `SETTLED_FORKS:
k3-gram-must-not-use-pdInput-of-gram`) delivers `hpd` from a family of cohomology classes whose
cap-images *generate* `H₂(K3;ℤ)`.

Both inputs therefore consume the same primitive — **cohomology classes with known cap-duals** —
and `nonempty_kummerK3E1Atoms_of_stable_of_geoData` takes them together:

| was | is now |
|---|---|
| `hstable` | `hstable` (wt1's lattice lane, unchanged) |
| `heven` | `heven` (Wu / `w₂ = 0`, unchanged) |
| `hpd` + `hfam` | ONE datum: classes `a`, their cap-duals `c`, `span c = ⊤`, and a `22×22` Kronecker table on a selected sub-family |

Note the two roles the datum plays are genuinely different and both are needed: the *spanning*
condition is what `SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis` says the 16
exceptional + 6 descended classes alone do **not** satisfy (they generate an index-`2⁸` subgroup), so
`ι` must be strictly larger than the selected 22 — the Kummer half-sums live exactly there. The
selector `sel` is what keeps the *signature* tabulation confined to the 22 classes whose Gram is
computable, which is the whole point of the full-rank-sublattice route.

## Non-vacuity

`linearIndependent_of_gram_kummerSubForm` (from `KummerK3GeometricFamily`) applies to the selected
sub-family, so the datum forces 22 `ℤ`-linearly independent classes; `hspan` independently forces the
cap-images to generate a rank-22 lattice. Neither can be met with no geometry.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3GeometricFamily

namespace SKEFTHawking.KummerK3CapDualFamily

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.KummerK3GeometricFamily

noncomputable section

variable {X : TopCat}

/-! ## §1. The Gram of a cap-dual family is its Kronecker table -/

/-- **A cap-dual family's intersection Gram is a table of Kronecker pairings.**

`interFormInt_capDual` in `∀ i j` form and against a named target matrix `G`. This is the interface
that turns the `hfam` obligation from "compute `n²` cup products in `H²`" — for which the arc has no
machinery — into "evaluate `n` cohomology classes on `n` homology classes", which every detection map
in the arc already does. -/
theorem gram_of_capDual (zM : Homology X 4) {n : ℕ} (α : Fin n → Cohomology X 2)
    (c : Fin n → Homology X 2) (hcap : ∀ i, capHInt 2 1 (α i) zM = c i)
    (G : Matrix (Fin n) (Fin n) ℤ) (hkron : ∀ i j, kroneckerHInt 2 (α j) (c i) = G i j) :
    ∀ i j, interFormInt (intFundamentalClassOfHomology zM) (α i) (α j) = G i j := by
  intro i j
  rw [SKEFTHawking.IntersectionMatrixBasisChange.interFormInt_capDual zM α c hcap i j]
  exact hkron i j

/-! ## §2. `hfam` at one orientation of the welded `K3`, from a cap-dual family -/

/-- **`hfam`'s existential at a single orientation, from a cap-dual family and its Kronecker table.**
`intFundamentalClassOfIntOrientation o` is by definition `intFundamentalClassOfHomology o.fundClass`,
so §1 applies verbatim. -/
theorem exists_kummerSubForm_family_of_capDual (o : IntOrientation KummerK3)
    (α : Fin 22 → Cohomology KummerK3top 2) (c : Fin 22 → Homology KummerK3top 2)
    (hcap : ∀ i, capHInt 2 1 (α i) o.fundClass = c i)
    (hkron : ∀ i j, kroneckerHInt 2 (α j) (c i) = kummerSubForm i j) :
    ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
        = kummerSubForm i j :=
  ⟨α, gram_of_capDual o.fundClass α c hcap kummerSubForm hkron⟩

/-! ## §3. `hpd` from the SAME primitive — a cap-spanning family -/

/-- **Integral Poincaré duality at `o` from cap-duals that generate `H₂(K3;ℤ)`.**

`KummerK3PoincareDuality.nonempty_intPD_of_capSpan` restated with the cap-images named, so that a
single family `(a, c)` serves both §2 and this. The route is the cap route, **not** the Gram route:
nothing here mentions `IntCongr`, `k3Form`, or any determinant, so it does not re-enter the banned
`Gram ⟹ pdInput ⟹ Gram` circle. -/
theorem nonempty_intPD_of_capDual_span {ι : Type*} (o : IntOrientation KummerK3)
    (a : ι → Cohomology KummerK3top 2) (c : ι → Homology KummerK3top 2)
    (hcap : ∀ i, capHInt 2 1 (a i) o.fundClass = c i)
    (hspan : Submodule.span ℤ (Set.range c) = ⊤) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) := by
  refine KummerK3PoincareDuality.nonempty_intPD_of_capSpan o a ?_
  rwa [show (fun i => capHInt 2 1 (a i) o.fundClass) = c from funext hcap]

/-! ## §4. THE CONSOLIDATED HEADLINE — `hpd` and `hfam` merged into one geometric datum -/

/-- **The welded `K3`'s E1 atoms from `StableNegRank16Two`, Wu-evenness, and ONE geometric datum.**

Compared with `KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` the two
inputs `hpd` and `hfam` are replaced by a single per-orientation package:

* `a : ι → H²(K3;ℤ)` — cohomology classes, with `c : ι → H₂(K3;ℤ)` their cap-duals (`hcap`);
* `hspan` — the cap-duals **generate** `H₂(K3;ℤ)` (this is what discharges `hpd`, and by
  `SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis` it is *strictly more* than the
  16 exceptional + 6 descended classes: the half-sums must be present in `ι`);
* `sel : Fin 22 → ι` together with `hkron` — the `22 × 22` Kronecker table of the selected
  sub-family, equal to `⟨−2⟩¹⁶ ⊕ 3H` (this is what discharges `hfam`; the selected 22 need **not**
  generate, which is precisely the full-rank-sublattice route's dispensation).

The remaining inputs are `hstable` (wt1's pure-lattice Eichler lane) and `heven` (Wu / `w₂ = 0`). -/
theorem nonempty_kummerK3E1Atoms_of_stable_of_geoData (hstable : StableNegRank16Two)
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hgeo : ∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤
          ∧ ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms := by
  refine nonempty_kummerK3E1Atoms_of_stable_of_geometric hstable (fun o => ?_) heven (fun o => ?_)
  · obtain ⟨ι, a, c, _, hcap, hspan, _⟩ := hgeo o
    exact nonempty_intPD_of_capDual_span o a c hcap hspan
  · obtain ⟨ι, a, c, sel, hcap, _, hkron⟩ := hgeo o
    exact exists_kummerSubForm_family_of_capDual o (fun i => a (sel i)) (fun i => c (sel i))
      (fun i => hcap (sel i)) hkron

/-! ## §5. Non-vacuity of the consolidated datum -/

/-- **The datum's selected sub-family is `ℤ`-linearly independent.** The zero-geometric-input attack
on §4: the `22 × 22` Kronecker table alone (never mind `hspan`) already forces 22 independent classes
in `H²(K3;ℤ)`, because `det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ ≠ 0`. So `hgeo` cannot be met by `a = 0`, by a
constant family, or by any family spanning a subgroup of rank `< 22`. -/
theorem linearIndependent_sel_of_geoData {ι : Type*} (o : IntOrientation KummerK3)
    (a : ι → Cohomology KummerK3top 2) (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι)
    (hcap : ∀ i, capHInt 2 1 (a i) o.fundClass = c i)
    (hkron : ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    LinearIndependent ℤ (fun i => a (sel i)) :=
  linearIndependent_of_gram_kummerSubForm (intFundamentalClassOfIntOrientation o) _
    (gram_of_capDual o.fundClass (fun i => a (sel i)) (fun i => c (sel i))
      (fun i => hcap (sel i)) kummerSubForm hkron)

end

end SKEFTHawking.KummerK3CapDualFamily
