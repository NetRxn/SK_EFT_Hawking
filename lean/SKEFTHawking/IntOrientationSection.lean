import Mathlib
import SKEFTHawking.SingularReducedGeneratorInt

/-!
# The integral orientation section `[M]` from a coherent local-generator choice (brick 17c)

Task-2 of the E1 orientation program. With the integral local-homology iso now a **hypothesis-free
theorem** (`SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold'`), the LOCAL orientation datum
`H₄(M, M∖x; ℤ) ≅ ℤ` at every point is fully-proved geometry. This module builds the orientation
*structure* on top of it:

* the integral point-restriction map `restrictToPointInt` (mirror of the mod-2
  `SingularManifoldFundamentalClass.restrictToPoint`, via `RelHomologyInt.map` of the inclusion of
  pairs `(M, Kᶜ) → (M, {x}ᶜ)`);
* the coherent local-generator predicate `restrictsToLocalGeneratorInt` — an integral class
  `α ∈ H₄(M, Kᶜ; ℤ)` restricts to the **oriented** local generator `orient x • localGenerator x` at
  every `x ∈ K`, for an orientation section `orient : M → ℤ` valued in `{±1}` (the honest ℤ sign-choice
  the mod-2 `x + x = 0` collapse hides);
* the orientation structure `IntOrientationData M` carrying a section + a global fundamental class
  restricting to the coherent oriented generators;
* the bridge `intOrientationOfData` constructing the disclosed `IntOrientation M` from it, where the
  per-point local input is now the PROVED `intLocalHomologyIso_of_manifold'` (not a posit).

The residual isolated here is exactly the GLOBAL coherent section (existence of `fundClass` gluing the
oriented local generators) — the ℤ-`hasFundClassInt` induction (mirror of `hasFundClass_univ`), whose
union step matches the two `±1` local generators via `orient` instead of collapsing by `x + x = 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no new axiom (orientation = structure data).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt

namespace SKEFTHawking.IntOrientationSection

variable {X : TopCat}

/-! ## §1. The integral inclusion-of-pairs / point-restriction maps -/

/-- **Integral inclusion of pairs** `Hₙ(X, T;ℤ) → Hₙ(X, S;ℤ)` for `T ⊆ S` (the identity map of `X`
sends `T` into `S`). The ℤ mirror of `SingularRelativeFunctoriality.relIncl`. -/
noncomputable def relInclInt {S T : Set ↑X} (hTS : T ⊆ S) (n : ℕ) :
    RelHomologyInt T n →ₗ[ℤ] RelHomologyInt S n :=
  RelHomologyInt.map (ContinuousMap.id ↑X) (fun _ ha => hTS ha) n

/-- **`relInclInt` is functorial** across a nested pair of subset inclusions. -/
theorem relInclInt_trans {S T U : Set ↑X} (hTS : T ⊆ S) (hSU : S ⊆ U) (n : ℕ)
    (α : RelHomologyInt T n) :
    relInclInt hSU n (relInclInt hTS n α) = relInclInt (hTS.trans hSU) n α := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  show relInclInt hSU n (relInclInt hTS n (RelHomologyInt.mk T n z))
    = relInclInt (hTS.trans hSU) n (RelHomologyInt.mk T n z)
  simp only [relInclInt, RelHomologyInt.map_mk]
  refine congrArg (Submodule.Quotient.mk) (Subtype.ext ?_)
  show relMapChainInt (ContinuousMap.id ↑X) (fun a ha => hSU ha) n
      (relMapChainInt (ContinuousMap.id ↑X) (fun a ha => hTS ha) n (z : RelativeChainInt T n))
    = relMapChainInt (ContinuousMap.id ↑X) (fun a ha => (hTS.trans hSU) ha) n
        (z : RelativeChainInt T n)
  rw [← relMapChainInt_comp]
  congr 1

/-- **Integral restriction to a point** `Hₙ(M|K;ℤ) → Hₙ(M|x;ℤ)` for `x ∈ K` (`Hₙ(M|K) = Hₙ(M, Kᶜ)`):
the inclusion of pairs for `Kᶜ ⊆ {x}ᶜ`. The ℤ mirror of
`SingularManifoldFundamentalClass.restrictToPoint`. -/
noncomputable def restrictToPointInt {K : Set ↑X} {x : ↑X} (hx : x ∈ K) (n : ℕ) :
    RelHomologyInt Kᶜ n →ₗ[ℤ] RelHomologyInt ({x}ᶜ) n :=
  relInclInt (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n

/-- **Restriction of an absolute integral class to the local homology at a point** `ρₓ : Hₙ(M;ℤ) →
Hₙ(M|x;ℤ)`, the pair map `homProjInt {x}ᶜ n`. The integral mirror of
`SingularFundamentalClass.restrictHomologyToPoint`; the object whose per-point value the orientation
section pins to `orient x • localGenerator`. -/
noncomputable def restrictHomologyToPointInt (x : ↑X) (n : ℕ) :
    Homology X n →ₗ[ℤ] RelHomologyInt ({y | y ≠ x} : Set ↑X) n :=
  homProjInt ({y | y ≠ x} : Set ↑X) n

/-! ## §2. The orientation section datum and the coherent-generator condition -/

open SKEFTHawking.SingularReducedGeneratorInt (intLocalHomologyIso_of_manifold')

/-- **The oriented local generator at `x`** for an orientation section value `s : ℤ` — `s •` the
integral local generator `(intLocalHomologyIso_of_manifold' x).iso.symm 1`. For `s = ±1` these are the
two generators of `H₄(M|x;ℤ) ≅ ℤ`; the orientation chooses one coherently across overlaps. Uses the
now-PROVED hypothesis-free local iso (`SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold'`),
not a disclosed datum. -/
noncomputable def orientedLocalGenerator {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) (s : ℤ) :
    RelHomologyInt (SingularRelHomologyInt.localSub x) 4 :=
  s • SingularRelHomologyInt.localGenerator x (intLocalHomologyIso_of_manifold' x)

/-- **The oriented local generator lies over the (nonzero) mod-2 local generator for odd `s`.** For
`s = ±1`, `redRelHomology (orientedLocalGenerator x s)` is the nonzero mod-2 local class — because the
integral local generator reduces to it (`redRelHomology_localGenerator_ne_zero`, brick 16 §9) and `±1`
acts as the identity mod 2. This is the falsifiable per-point compatibility the orientation records; it
is now PROVED geometry (the local iso is a theorem), not disclosed. -/
theorem redRelHomology_orientedLocalGenerator_ne_zero {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    redRelHomology (SingularRelHomologyInt.localSub x) 4 (orientedLocalGenerator x s) ≠ 0 := by
  rw [orientedLocalGenerator, map_zsmul]
  have hgen := SKEFTHawking.SingularLocalHomologyRedCompatInt.redRelHomology_localGenerator_ne_zero x
    (intLocalHomologyIso_of_manifold' x)
  rcases hs with h | h
  · rw [h, one_zsmul]; exact hgen
  · rw [h]
    intro hz
    -- (-1) • w = 0 ⟹ w = 0
    apply hgen
    have : (-1 : ℤ) • redRelHomology (SingularRelHomologyInt.localSub x) 4
        (SingularRelHomologyInt.localGenerator x (intLocalHomologyIso_of_manifold' x)) = 0 := hz
    rwa [neg_one_zsmul, neg_eq_zero] at this

/-- **The integral orientation datum** of a closed charted 4-manifold: an orientation *section* plus a
global fundamental class realising it.

* `orient : M → ℤ` — the ±1 section (the coherent choice of local generator at each point);
* `orient_unit` — `orient x ∈ {1, -1}` everywhere (a genuine generator choice);
* `fundClass : H₄(M;ℤ)` — the global class the coherent section glues;
* `restricts` — `fundClass` restricts at every `x` to the **oriented** local generator
  `orientedLocalGenerator x (orient x)` (the honest ℤ sign-match, replacing the mod-2 `x + x = 0`);
* `redCompat` — the ℤ→ℤ/2 reduction of `fundClass` is the on-main orientation-free mod-2 `[M]₂`.

The residual (existence of such data) is exactly the GLOBAL coherent section — the ℤ-`hasFundClassInt`
induction whose union step matches the two `±1` local generators via `orient`. All LOCAL inputs
(`orientedLocalGenerator`, its mod-2 non-vanishing) are now proved geometry. NOT an axiom. -/
structure IntOrientationData (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  /-- The ±1 orientation section. -/
  orient : M → ℤ
  /-- Each section value is a generator sign `±1`. -/
  orient_unit : ∀ x, orient x = 1 ∨ orient x = -1
  /-- The global integral fundamental class `[M] ∈ H₄(M;ℤ)`. -/
  fundClass : Homology (TopCat.of M) 4
  /-- `[M]` restricts at every point to the oriented local generator. -/
  restricts : ∀ x : M, restrictHomologyToPointInt (X := TopCat.of M) x 4 fundClass
    = orientedLocalGenerator x (orient x)
  /-- Mod-2 compatibility: the reduction of `[M]` is the on-main mod-2 fundamental class. -/
  redCompat : redHomology (TopCat.of M) 4 fundClass
    = SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := M)

/-! ## §3. The bridge to the disclosed `IntOrientation` -/

/-- **An orientation datum produces the disclosed `IntOrientation`.** Forwards `fundClass` + `redCompat`;
the datum's extra section + coherent-restriction fields witness that `fundClass` is a genuine oriented
fundamental class (its per-point restriction is a `±1` local generator), so the produced `IntOrientation`
is non-vacuous by construction. This is the honest structure the brief requests: orientation carried as
DATA, discharging the `[M]` input to the integral intersection form on oriented 4-manifolds. -/
noncomputable def intOrientationOfData {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (o : IntOrientationData M) :
    SKEFTHawking.SingularHomologyInt.IntOrientation M where
  fundClass := o.fundClass
  redCompat := o.redCompat

/-- **The oriented fundamental class restricts to a nonzero mod-2 local class at every point.** The
falsifiability witness: for a `T1` datum, `redHomology`-reducing the per-point restriction of `[M]` gives
a nonzero mod-2 local generator everywhere (the orientation is a genuine `±1` choice over the proved
local iso). Extracted from `restricts` + `redRelHomology_orientedLocalGenerator_ne_zero`. -/
theorem intOrientationData_restricts_ne_zero {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [T1Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (o : IntOrientationData M) (x : M) :
    redRelHomology (SingularRelHomologyInt.localSub x) 4
        (restrictHomologyToPointInt (X := TopCat.of M) x 4 o.fundClass) ≠ 0 := by
  rw [o.restricts x]
  exact redRelHomology_orientedLocalGenerator_ne_zero x (o.orient_unit x)

end SKEFTHawking.IntOrientationSection
