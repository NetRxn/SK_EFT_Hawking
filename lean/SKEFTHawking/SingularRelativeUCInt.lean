import Mathlib
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularEuclideanCapIsoInt

/-!
# Phase 5q.H (E1 integral topology) — the integral relative universal-coefficient pairing + free-case UCT

The integral (ℤ-coefficient) analogue of the mod-2 `SingularRelativePairing` + `SingularRelativeUC`.
Over the field `ℤ/2` the relative Kronecker pairing `Hⁿ(X,S) → Hom(Hₙ(X,S), ℤ/2)` is unconditionally an
iso (`SingularRelativeUC`, field UC). Over ℤ the universal-coefficient short exact sequence

  `0 → Ext(Hₙ₋₁(X,S), ℤ) → Hⁿ(X,S; ℤ) --κ--> Hom(Hₙ(X,S; ℤ), ℤ) → 0`

has a genuine `Ext` term; the pairing is an iso exactly when `Ext(Hₙ₋₁) = 0`, i.e. when the previous
homology `Hₙ₋₁(X,S; ℤ)` is **free** (`Ext(free, ℤ) = 0`). This module builds:

* §1 — the integral relative Kronecker pairing `relKroneckerInt`/`relKroneckerHInt` (mirror of
  `SingularRelativePairing`, over ℤ), reusing the §B `relCochainsInt`/`RelativeCohomologyInt`;
* §2 — the free-case non-degeneracies (both arguments), i.e. `relKroneckerHInt` bijective when `Hₙ₋₁`
  is free — the reusable integral relative UCT the PD MV five-lemma consumes at every convex cover-piece.

The singular chains are already free ℤ-modules and the relative chains `RelativeChainInt S n` are free
(quotient of `Finsupp` by a coordinate submodule), so the Hom-side (surjectivity) needs only that a
functional on the free relative chains extends; the Ext obstruction is the injectivity/kernel, killed by
`Hₙ₋₁` free.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt

namespace SKEFTHawking.SingularRelativeUCInt

variable {X : TopCat} (S : Set X)

/-! ## §1. The integral relative Kronecker pairing -/

/-- **The integral relative Kronecker pairing on relative chains** `relKroneckerInt a : RelativeChainInt S n
→ₗ ℤ`, `[c] ↦ ⟨a, c⟩` for a relative cochain `a` (vanishing on `subspaceChainsInt S`). Well-defined: `a`
kills the subspace chains, so `kronecker a ·` descends through `RelativeChainInt`. Integral mirror of
`SingularRelativePairing.relKronecker`. -/
noncomputable def relKroneckerInt {n : ℕ} (a : relCochainsInt S n) :
    RelativeChainInt S n →ₗ[ℤ] ℤ :=
  Submodule.liftQ (subspaceChainsInt S n) (kroneckerₗ n a.1) (fun c hc => a.2 c hc)

@[simp] theorem relKroneckerInt_mk {n : ℕ} (a : relCochainsInt S n) (c : SingularChainInt X n) :
    relKroneckerInt S a (RelativeChainInt.mk S n c) = kronecker a.1 c := rfl

/-- **The integral relative Kronecker pairing is ℤ-bilinear** `relCochainsInt S n →ₗ (RelativeChainInt S n
→ₗ ℤ)`. -/
noncomputable def relKroneckerIntₗ {n : ℕ} :
    relCochainsInt S n →ₗ[ℤ] RelativeChainInt S n →ₗ[ℤ] ℤ where
  toFun := relKroneckerInt S
  map_add' a b := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(a + b)) c = kronecker (↑a) c + kronecker (↑b) c
    rw [Submodule.coe_add, kronecker_add_left]
  map_smul' s a := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(s • a)) c = s • kronecker (↑a) c
    rw [SetLike.val_smul, kronecker_smul_left]

/-- **The integral relative adjunction** `⟨a, ∂[w]⟩ = ⟨δa, [w]⟩`. -/
theorem relKroneckerInt_relBoundary {n : ℕ} (a : relCochainsInt S n) (w : RelativeChainInt S (n + 1)) :
    relKroneckerInt S a (relBoundaryInt S n w) = relKroneckerInt S (relCoboundaryIntₗ S n a) w := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show relKroneckerInt S a (relBoundaryInt S n (RelativeChainInt.mk S (n + 1) c))
    = kronecker (relCoboundaryIntₗ S n a).1 c
  rw [relBoundaryInt_mk, relKroneckerInt_mk, relCoboundaryIntₗ_coe, kronecker_coboundary_chainBoundary]

/-- **The integral relative Kronecker pairing descends to relative homology** for a fixed relative cocycle
`a`: `relKroneckerRightHInt a : RelHomologyInt S n →ₗ ℤ`, `[z] ↦ ⟨a, z⟩`. Well-defined: `a` a relative
cocycle ⟹ `relKroneckerInt a` kills relative boundaries (adjunction). Integral mirror of
`relKroneckerRightH`. -/
noncomputable def relKroneckerRightHInt {n : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S n)) :
    RelHomologyInt S n →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ ((relKroneckerInt S a.1).domRestrict (relCyclesInt S n))
    (fun z hz => by
      obtain ⟨w, hw⟩ := hz
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply,
        show (z : RelativeChainInt S n) = relBoundaryInt S n w from hw.symm,
        relKroneckerInt_relBoundary,
        show relCoboundaryIntₗ S n a.1 = 0 from LinearMap.mem_ker.mp a.2]
      exact congrFun (congrArg DFunLike.coe (map_zero (relKroneckerIntₗ S))) w)

@[simp] theorem relKroneckerRightHInt_mk {n : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S n))
    (z : relCyclesInt S n) :
    relKroneckerRightHInt S a (RelHomologyInt.mk S n z) = relKroneckerInt S a.1 z.1 := rfl

/-- **`relKroneckerRightHInt` is ℤ-linear in the relative cocycle** — packaged
`ker (relCoboundaryIntₗ S n) →ₗ (RelHomologyInt S n →ₗ ℤ)`. -/
noncomputable def relKroneckerRightHIntₗ {n : ℕ} :
    LinearMap.ker (relCoboundaryIntₗ S n) →ₗ[ℤ] RelHomologyInt S n →ₗ[ℤ] ℤ where
  toFun := relKroneckerRightHInt S
  map_add' a b := by
    ext q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (relKroneckerIntₗ S (↑(a + b))) z.1 = (relKroneckerIntₗ S a.1) z.1 + (relKroneckerIntₗ S b.1) z.1
    rw [Submodule.coe_add, map_add, LinearMap.add_apply]
  map_smul' s a := by
    ext q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (relKroneckerIntₗ S (↑(s • a))) z.1 = s • (relKroneckerIntₗ S a.1) z.1
    rw [SetLike.val_smul, map_smul, LinearMap.smul_apply]

/-- **A relative coboundary pairs to `0` with every relative cycle**: `relKroneckerRightHInt (δg) = 0`. -/
theorem relKroneckerRightHInt_relCoboundary {N : ℕ} (g : relCochainsInt S N)
    (hb : (relCoboundaryIntₗ S N g : relCochainsInt S (N + 1)) ∈
      LinearMap.ker (relCoboundaryIntₗ S (N + 1))) :
    relKroneckerRightHIntₗ S ⟨relCoboundaryIntₗ S N g, hb⟩ = 0 := by
  ext q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show relKroneckerInt S (relCoboundaryIntₗ S N g) z.1 = 0
  rw [← relKroneckerInt_relBoundary, show relBoundaryInt S N z.1 = 0 from
    LinearMap.mem_ker.mp z.2, map_zero]

/-- **The integral relative Kronecker pairing on (co)homology classes**
`relKroneckerHInt : Hᵏ(X,S; ℤ) →ₗ (Hₙ(X,S; ℤ) →ₗ ℤ)` (`k = N+1`). Integral mirror of `relKroneckerH`;
the pairing whose bijectivity (when `Hₙ₋₁` free) is the integral relative UCT. -/
noncomputable def relKroneckerHInt {N : ℕ} :
    RelativeCohomologyInt S (N + 1) →ₗ[ℤ] RelHomologyInt S (N + 1) →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ (relKroneckerRightHIntₗ S) (by
    intro b hb
    rw [LinearMap.mem_ker]
    have hb' : (b : relCochainsInt S (N + 1)) ∈ relCoboundaryRangeInt S (N + 1) := hb
    rw [show relCoboundaryRangeInt S (N + 1) = LinearMap.range (relCoboundaryIntₗ S N) from rfl,
      LinearMap.mem_range] at hb'
    obtain ⟨g, hg⟩ := hb'
    rw [show b = ⟨relCoboundaryIntₗ S N g, hg ▸ b.2⟩ from Subtype.ext hg.symm]
    exact relKroneckerRightHInt_relCoboundary S g _)

@[simp] theorem relKroneckerHInt_mk_mk {N : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S (N + 1)))
    (z : relCyclesInt S (N + 1)) :
    relKroneckerHInt S (RelativeCohomologyInt.mk S (N + 1) a) (RelHomologyInt.mk S (N + 1) z)
      = relKroneckerInt S a.1 z.1 := rfl

/-- **The curried integral relative Kronecker map** `κ : Hⁿ(X,S; ℤ) →ₗ Module.Dual ℤ (Hₙ(X,S; ℤ))`,
`ω ↦ ⟨ω, ·⟩` — the map the integral relative UCT asserts is an iso when `Hₙ₋₁` is free. -/
noncomputable def relKronMapInt {N : ℕ} :
    RelativeCohomologyInt S (N + 1) →ₗ[ℤ] Module.Dual ℤ (RelHomologyInt S (N + 1)) :=
  relKroneckerHInt S

/-! ## §2. Cochain realization of functionals (unconditional — the chains are free) -/

/-- **Every integral chain functional is `kronecker` of a cochain** (the dual of the free `Finsupp`
chain module is the full function space): `φ = ⟨f, ·⟩` for `f σ = φ (single σ 1)`. Unconditional over ℤ.
Integral mirror of `SingularUniversalCoeff.exists_cochain_of_functional`. -/
theorem exists_cochainInt_of_functional {n : ℕ} (φ : SingularChainInt X n →ₗ[ℤ] ℤ) :
    ∃ f : SingularCochainInt X n, ∀ c : SingularChainInt X n, kronecker f c = φ c := by
  refine ⟨fun σ => φ (Finsupp.single σ 1), fun c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp [kronecker_apply]
  | add c d hc hd => rw [kronecker_add_right, map_add, hc, hd]
  | single σ s =>
      rw [kronecker_single,
        show Finsupp.single σ s = s • Finsupp.single σ (1 : ℤ) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one],
        map_smul, smul_eq_mul]

/-- **Every integral relative-chain functional is `relKroneckerInt` of a relative cochain**
(unconditional — the relative chains, a quotient of the free chains by a coordinate submodule, are
free): pull `φ` back along the quotient map `mkQ` to a functional on the absolute chains vanishing on
subspace chains, realize it as `kronecker f`, note `f ∈ relCochainsInt S n`. Integral mirror of
`SingularRelativeUC.exists_relCochain_of_functional`. -/
theorem exists_relCochainInt_of_functional {n : ℕ} (φ : RelativeChainInt S n →ₗ[ℤ] ℤ) :
    ∃ a : relCochainsInt S n, relKroneckerInt S a = φ := by
  set ψ : SingularChainInt X n →ₗ[ℤ] ℤ := φ.comp (Submodule.mkQ (subspaceChainsInt S n)) with hψ
  obtain ⟨f, hf⟩ := exists_cochainInt_of_functional (X := X) ψ
  have hfrel : f ∈ relCochainsInt S n := by
    intro c hc
    rw [hf, hψ, LinearMap.comp_apply]
    show φ (Submodule.Quotient.mk c) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2 hc]
    exact map_zero φ
  refine ⟨⟨f, hfrel⟩, ?_⟩
  ext q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show relKroneckerInt S ⟨f, hfrel⟩ (RelativeChainInt.mk S n c) = φ (RelativeChainInt.mk S n c)
  rw [relKroneckerInt_mk, hf, hψ, LinearMap.comp_apply]
  rfl

/-! ## §3. The cycle-summand retraction from projective boundaries

The one genuinely ℤ-specific ingredient (over `ZMod 2` it is `LinearMap.exists_extend`, free because
every subspace of a vector space is complemented): a functional on the relative cycles extends to all
relative chains **when the relative boundaries are projective**. Over ℤ the relative boundaries
`relBoundariesInt S N` (a submodule of the free relative chains) are always free — hence projective —
by the structure theorem for modules over a PID; Mathlib currently proves this only in finite rank, so
we take `Module.Projective ℤ (relBoundariesInt S N)` as an explicit hypothesis (discharged structurally
by the caller). It makes the boundary map `∂` split, giving the retraction `Cₙ ↠ Zₙ`. -/

/-- **The boundary map splits when the boundaries are projective**: a section
`s : relBoundariesInt S N → RelativeChainInt S (N+1)` of `∂` (`∂ ∘ s = id` on the boundaries),
from `Module.Projective`'s lifting property against the surjection `∂ : C_{N+1} ↠ B_N`. -/
theorem exists_boundary_section {N : ℕ} [Module.Projective ℤ (relBoundariesInt S N)] :
    ∃ s : relBoundariesInt S N →ₗ[ℤ] RelativeChainInt S (N + 1),
      ∀ b : relBoundariesInt S N, relBoundaryInt S N (s b) = (b : RelativeChainInt S N) := by
  -- `∂` corestricted to its range `relBoundariesInt` is surjective; projectivity lifts `id`.
  let bdryR : RelativeChainInt S (N + 1) →ₗ[ℤ] relBoundariesInt S N :=
    (relBoundaryInt S N).codRestrict (relBoundariesInt S N) (fun c => ⟨c, rfl⟩)
  have hsurj : Function.Surjective (bdryR : RelativeChainInt S (N + 1) → relBoundariesInt S N) := by
    rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := hb
    exact ⟨c, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property bdryR LinearMap.id hsurj
  refine ⟨s, fun b => ?_⟩
  have hcf := LinearMap.congr_fun hs b
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hcf
  have h2 : ((bdryR (s b) : relBoundariesInt S N) : RelativeChainInt S N)
      = ((b : relBoundariesInt S N) : RelativeChainInt S N) := congrArg Subtype.val hcf
  rwa [show (bdryR (s b) : relBoundariesInt S N).1 = relBoundaryInt S N (s b) from rfl] at h2

/-- **The retraction onto the relative cycles** `r : RelativeChainInt S (N+1) → relCyclesInt S (N+1)`
(`r ∘ incl = id`), from a boundary section `s`: `r = id - s ∘ ∂` lands in `ker ∂ = Zₙ₊₁` and fixes
cycles. The ℤ replacement for the field complement. -/
theorem exists_cycles_retraction {N : ℕ} [Module.Projective ℤ (relBoundariesInt S N)] :
    ∃ r : RelativeChainInt S (N + 1) →ₗ[ℤ] relCyclesInt S (N + 1),
      ∀ z : relCyclesInt S (N + 1), r (z : RelativeChainInt S (N + 1)) = z := by
  obtain ⟨s, hs⟩ := exists_boundary_section S (N := N)
  -- `∂ c ∈ relBoundariesInt` for every `c`; `c - s(∂c) ∈ ker ∂ = relCyclesInt (N+1)`.
  have hmem : ∀ c : RelativeChainInt S (N + 1),
      relBoundaryInt S N c ∈ relBoundariesInt S N := fun c => ⟨c, rfl⟩
  refine ⟨{
    toFun := fun c => ⟨c - s ⟨relBoundaryInt S N c, hmem c⟩, ?_⟩
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · -- membership in relCyclesInt (N+1) = ker ∂
    show c - s ⟨relBoundaryInt S N c, hmem c⟩ ∈ LinearMap.ker (relBoundaryInt S N)
    rw [LinearMap.mem_ker, map_sub, hs ⟨relBoundaryInt S N c, hmem c⟩, sub_self]
  · intro c d
    apply Subtype.ext
    show (c + d) - s ⟨relBoundaryInt S N (c + d), _⟩
      = (c - s ⟨relBoundaryInt S N c, _⟩) + (d - s ⟨relBoundaryInt S N d, _⟩)
    rw [show (⟨relBoundaryInt S N (c + d), hmem (c + d)⟩ : relBoundariesInt S N)
        = ⟨relBoundaryInt S N c, hmem c⟩ + ⟨relBoundaryInt S N d, hmem d⟩ from by
          apply Subtype.ext; simp [map_add], map_add]
    abel
  · intro t c
    apply Subtype.ext
    show (t • c) - s ⟨relBoundaryInt S N (t • c), _⟩
      = t • (c - s ⟨relBoundaryInt S N c, _⟩)
    rw [show (⟨relBoundaryInt S N (t • c), hmem (t • c)⟩ : relBoundariesInt S N)
        = t • ⟨relBoundaryInt S N c, hmem c⟩ from by
          apply Subtype.ext; simp [map_smul], map_smul, smul_sub]
  · intro z
    apply Subtype.ext
    show (z : RelativeChainInt S (N + 1)) - s ⟨relBoundaryInt S N z, _⟩ = z
    have hz0 : relBoundaryInt S N (z : RelativeChainInt S (N + 1)) = 0 := by
      have hzmem : (z : RelativeChainInt S (N + 1)) ∈ LinearMap.ker (relBoundaryInt S N) := z.2
      rwa [LinearMap.mem_ker] at hzmem
    rw [show (⟨relBoundaryInt S N (z : RelativeChainInt S (N + 1)), hmem _⟩ : relBoundariesInt S N)
        = 0 from by apply Subtype.ext; exact hz0, map_zero, sub_zero]

/-! ## §4. Surjectivity of `κ` (the Hom-side; needs only projective boundaries, no `Hₙ₋₁`-free) -/

/-- **`κ` is surjective**: every functional on relative homology `Hₙ₊₁(X,S; ℤ)` is `relKroneckerHInt` of
a relative cohomology class — provided the relative boundaries `relBoundariesInt S (N+1)` are projective
(so a functional on the cycles extends to all chains via the retraction §3). The integral Hom-side of
the relative UCT; the `Ext` obstruction lives only in injectivity. Integral mirror of
`SingularRelativeUCSurj.relKroneckerH_surjective_field`. -/
theorem relKroneckerHInt_surjective {N : ℕ}
    [Module.Projective ℤ (relBoundariesInt S N)] :
    Function.Surjective (relKroneckerHInt S (N := N)) := by
  intro φ
  -- Pull `φ` back along the homology quotient to a functional `ψ` on the relative cycles.
  set ψ : relCyclesInt S (N + 1) →ₗ[ℤ] ℤ :=
    φ.comp ((relBoundariesInt S (N + 1)).submoduleOf (relCyclesInt S (N + 1))).mkQ with hψ
  -- Extend `ψ` to all relative chains via the retraction `r : C_{N+1} → Z_{N+1}`.
  obtain ⟨r, hr⟩ := exists_cycles_retraction S (N := N)
  set F : RelativeChainInt S (N + 1) →ₗ[ℤ] ℤ := ψ.comp r with hF
  -- `F` agrees with `ψ` on relative cycles.
  have hFcyc : ∀ z : relCyclesInt S (N + 1), F (z : RelativeChainInt S (N + 1)) = ψ z := by
    intro z; rw [hF, LinearMap.comp_apply, hr z]
  -- Realize `F` as `relKroneckerInt a` for a relative cochain `a`.
  obtain ⟨a, ha⟩ := exists_relCochainInt_of_functional S F
  -- `F` kills relative boundaries (they are `0` in homology).
  have hFbd : ∀ w : RelativeChainInt S (N + 2), F (relBoundaryInt S (N + 1) w) = 0 := by
    intro w
    have hmem : relBoundaryInt S (N + 1) w ∈ relBoundariesInt S (N + 1) := ⟨w, rfl⟩
    have hcyc : relBoundaryInt S (N + 1) w ∈ relCyclesInt S (N + 1) :=
      relBoundariesInt_le_relCyclesInt S (N + 1) hmem
    have hzero : ((relBoundariesInt S (N + 1)).submoduleOf (relCyclesInt S (N + 1))).mkQ
        ⟨relBoundaryInt S (N + 1) w, hcyc⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hmem
    rw [hFcyc ⟨relBoundaryInt S (N + 1) w, hcyc⟩, hψ, LinearMap.comp_apply]
    show φ (((relBoundariesInt S (N + 1)).submoduleOf (relCyclesInt S (N + 1))).mkQ
      ⟨relBoundaryInt S (N + 1) w, hcyc⟩) = 0
    rw [hzero]; exact map_zero φ
  -- Hence `a` is a relative cocycle: `relKroneckerInt (δa) w = F (∂w) = 0` on every basis, so `δa = 0`.
  have hcocycle : a ∈ LinearMap.ker (relCoboundaryIntₗ S (N + 1)) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (relCoboundaryIntₗ S (N + 1) a).1 = 0
    funext σ
    have hkz : relKroneckerInt S (relCoboundaryIntₗ S (N + 1) a)
        (RelativeChainInt.mk S (N + 2) (Finsupp.single σ 1)) = 0 := by
      rw [← relKroneckerInt_relBoundary, ha]
      rw [show relBoundaryInt S (N + 1) (RelativeChainInt.mk S (N + 2) (Finsupp.single σ 1))
          = relBoundaryInt S (N + 1) (RelativeChainInt.mk S (N + 2) (Finsupp.single σ 1)) from rfl]
      exact hFbd _
    rw [relKroneckerInt_mk, kronecker_single, one_mul] at hkz
    exact hkz
  -- `[a]` pairs to `φ`.
  refine ⟨RelativeCohomologyInt.mk S (N + 1) ⟨a, hcocycle⟩, ?_⟩
  ext z'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
  rw [show (Submodule.Quotient.mk z : RelHomologyInt S (N + 1))
      = RelHomologyInt.mk S (N + 1) z from rfl, relKroneckerHInt_mk_mk,
    show relKroneckerInt S a z.1 = F z.1 from congrFun (congrArg DFunLike.coe ha) z.1, hFcyc z, hψ,
    LinearMap.comp_apply]
  rfl

/-! ## §5. Injectivity of `κ` — the Ext obstruction, killed by `Hₙ` free

`κ` injectivity is where the `Ext(Hₙ)` term of the UCT lives. `[a]` pairs to `0` with all of `Hₙ₊₁` ⟹
`φ = relKroneckerInt a` vanishes on the cycles `Zₙ₊₁ = ker ∂ₙ`, so factors through `im ∂ₙ = Bₙ ⊆ Cₙ` as
`ḡ`. To realize `ḡ` as `relKroneckerInt b` (making `a = δb` a coboundary) we must **extend** `ḡ` from
`Bₙ` to all of `Cₙ`; that needs `Bₙ` a direct summand of `Cₙ`, i.e. the inclusion `Bₙ ↪ Zₙ` splits
(`Hₙ = Zₙ/Bₙ` free ⟹ projective) and `Zₙ ↪ Cₙ` splits (`Bₙ₋₁` projective, §3). -/

/-- **The boundaries retract inside the cycles when `Hₙ` is free**: a projection
`RelativeChainInt-cycles Zₙ ↠ Bₙ` fixing `Bₙ`, from splitting the quotient `Zₙ ↠ Hₙ = Zₙ/Bₙ`
(`Hₙ` free ⟹ projective ⟹ the quotient map splits). -/
theorem exists_boundaries_in_cycles_retraction {N : ℕ} [Module.Free ℤ (RelHomologyInt S N)] :
    ∃ ρ : relCyclesInt S N →ₗ[ℤ]
        (relBoundariesInt S N).submoduleOf (relCyclesInt S N),
      ∀ b : (relBoundariesInt S N).submoduleOf (relCyclesInt S N),
        ρ (b : relCyclesInt S N) = b := by
  set Bsub := (relBoundariesInt S N).submoduleOf (relCyclesInt S N) with hBsub
  -- `Hₙ = Zₙ / Bsub` is free ⟹ projective ⟹ the surjection `Bsub.mkQ : Zₙ ↠ Hₙ` splits
  -- (`Module.projective_lifting_property` lifts `id : Hₙ → Hₙ`).
  have e : RelHomologyInt S N ≃ₗ[ℤ] (↥(relCyclesInt S N) ⧸ Bsub) := LinearEquiv.refl ℤ _
  haveI hproj : Module.Projective ℤ (↥(relCyclesInt S N) ⧸ Bsub) := Module.Projective.of_equiv e
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property Bsub.mkQ
    (LinearMap.id (R := ℤ) (M := ↥(relCyclesInt S N) ⧸ Bsub)) Bsub.mkQ_surjective
  -- `z - sec (mkQ z) ∈ Bsub = ker (mkQ)` since `mkQ (z - sec (mkQ z)) = mkQ z - mkQ z = 0`.
  have hmem : ∀ z : relCyclesInt S N, z - sec (Bsub.mkQ z) ∈ Bsub := by
    intro z
    have hid : Bsub.mkQ (sec (Bsub.mkQ z)) = Bsub.mkQ z := by
      -- v4.32: `simpa`'s closing step will not bridge `LinearMap.id x` to `x` here.
      -- Normalise the HYPOTHESIS instead and close with a bare `exact` (P11).
      have h := LinearMap.congr_fun hsec (Bsub.mkQ z)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
      exact h
    have hk : z - sec (Bsub.mkQ z) ∈ LinearMap.ker Bsub.mkQ := by
      rw [LinearMap.mem_ker, map_sub, hid, sub_self]
    rwa [Submodule.ker_mkQ] at hk
  refine ⟨{
    toFun := fun z => ⟨z - sec (Bsub.mkQ z), hmem z⟩
    map_add' := ?_
    map_smul' := ?_ }, ?_⟩
  · intro a b; apply Subtype.ext
    show (a + b) - sec (Bsub.mkQ (a + b)) = (a - sec (Bsub.mkQ a)) + (b - sec (Bsub.mkQ b))
    rw [map_add, map_add]; abel
  · intro t a; apply Subtype.ext
    show (t • a) - sec (Bsub.mkQ (t • a)) = t • (a - sec (Bsub.mkQ a))
    rw [map_smul, map_smul, smul_sub]
  · intro b; apply Subtype.ext
    show ((b : relCyclesInt S N)) - sec (Bsub.mkQ (b : relCyclesInt S N)) = (b : relCyclesInt S N)
    have hb0 : Bsub.mkQ (b : relCyclesInt S N) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact b.2
    rw [hb0, map_zero, sub_zero]

/-- **A functional on the relative boundaries extends to all relative chains** (the `Ext = 0` engine):
given `Hₙ = H_{M+1}` free and the previous boundaries `B_M` projective, `Bₙ = B_{M+1}` is a direct
summand of `Cₙ` (via the composite retraction `Cₙ ↠ Zₙ ↠ Bₙ`, §3 then §5a), so any `ḡ : Bₙ → ℤ`
extends to `F : Cₙ → ℤ` with `F|Bₙ = ḡ`. -/
theorem exists_functional_extension_boundaries {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))] [Module.Projective ℤ (relBoundariesInt S M)]
    (g : relBoundariesInt S (M + 1) →ₗ[ℤ] ℤ) :
    ∃ F : RelativeChainInt S (M + 1) →ₗ[ℤ] ℤ,
      ∀ b : relBoundariesInt S (M + 1), F (b : RelativeChainInt S (M + 1)) = g b := by
  -- Retraction `Cₙ ↠ Zₙ` (§3, needs `B_M` projective).
  obtain ⟨r, hr⟩ := exists_cycles_retraction S (N := M)
  -- Retraction `Zₙ ↠ Bₙ` inside the cycles (§5a, needs `H_{M+1}` free).
  obtain ⟨ρ, hρ⟩ := exists_boundaries_in_cycles_retraction S (N := M + 1)
  -- `ĝ : (Bₙ.submoduleOf Zₙ) → ℤ` = `g` transported to the in-cycles form.
  -- Membership: `↑(ρ (r c)) : Zₙ`, and its value lies in `Bₙ` (submoduleOf), i.e. as a chain in `Bₙ`.
  have hcoe : ∀ w : (relBoundariesInt S (M + 1)).submoduleOf (relCyclesInt S (M + 1)),
      ((w : relCyclesInt S (M + 1)) : RelativeChainInt S (M + 1)) ∈ relBoundariesInt S (M + 1) := by
    intro w
    exact Submodule.mem_comap.mp w.2
  refine ⟨g.comp
    ({ toFun := fun c => ⟨((ρ (r c) : relCyclesInt S (M + 1)) : RelativeChainInt S (M + 1)),
          hcoe (ρ (r c))⟩
       map_add' := fun a b => by apply Subtype.ext; simp [map_add]
       map_smul' := fun t a => by apply Subtype.ext; simp [map_smul] } :
      RelativeChainInt S (M + 1) →ₗ[ℤ] relBoundariesInt S (M + 1)), ?_⟩
  intro b
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  show ((ρ (r (b : RelativeChainInt S (M + 1))) : relCyclesInt S (M + 1)) : RelativeChainInt S (M + 1))
    = (b : RelativeChainInt S (M + 1))
  -- `b : Bₙ ⊆ Zₙ`; `r` fixes it (it is a cycle), `ρ` fixes it (it is a boundary).
  have hbcyc : (b : RelativeChainInt S (M + 1)) ∈ relCyclesInt S (M + 1) :=
    relBoundariesInt_le_relCyclesInt S (M + 1) b.2
  have hrb : r (b : RelativeChainInt S (M + 1)) = ⟨(b : RelativeChainInt S (M + 1)), hbcyc⟩ :=
    hr ⟨(b : RelativeChainInt S (M + 1)), hbcyc⟩
  rw [hrb]
  have hbsubmem : (⟨(b : RelativeChainInt S (M + 1)), hbcyc⟩ : relCyclesInt S (M + 1))
      ∈ (relBoundariesInt S (M + 1)).submoduleOf (relCyclesInt S (M + 1)) :=
    Submodule.mem_comap.mpr b.2
  rw [hρ ⟨_, hbsubmem⟩]

/-! ## §6. Injectivity of `κ` (free-`Hₙ` UCT) and the bijectivity headline -/

/-- **`κ` is injective when `Hₙ` is free** (the `Ext(Hₙ) = 0` half): a relative cohomology class
`ω = [a]` of degree `N+1` pairing to `0` with every relative homology class is `0`. `φ = relKroneckerInt
a` vanishes on the cycles `Z_{N+1} = ker ∂`, so factors as `ḡ ∘ ∂` through `im ∂ = B_N` (`ḡ : B_N → ℤ`);
extend `ḡ` to `g : C_N → ℤ` (`exists_functional_extension_boundaries`, needs `Hₙ = H_{M+1}` free +
`B_M` projective); realize `g = relKroneckerInt b`; the relative adjunction gives `a = δb`, so `ω = 0`.
Integral free-case mirror of `SingularRelativeUC.relCohomology_eq_zero_of_relKroneckerH`. -/
theorem relKroneckerHInt_injective_of_free {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))] [Module.Projective ℤ (relBoundariesInt S M)]
    (ω : RelativeCohomologyInt S (M + 2))
    (h : ∀ β : RelHomologyInt S (M + 2), relKroneckerHInt S ω β = 0) : ω = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  set φ : RelativeChainInt S (M + 2) →ₗ[ℤ] ℤ := relKroneckerInt S a.1 with hφ
  -- `φ` vanishes on the relative cycles `Z_{M+2} = ker ∂_{M+1}`.
  have hvanish : LinearMap.ker (relBoundaryInt S (M + 1)) ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hφ]
    have hzcyc : z ∈ relCyclesInt S (M + 2) := hz
    have hh := h (RelHomologyInt.mk S (M + 2) ⟨z, hzcyc⟩)
    rwa [show (Submodule.Quotient.mk a : RelativeCohomologyInt S (M + 2))
        = RelativeCohomologyInt.mk S (M + 2) a from rfl, relKroneckerHInt_mk_mk] at hh
  -- Factor `φ` through `im ∂_{M+1} = B_{M+1}` as `ḡ : B_{M+1} → ℤ` with `φ = ḡ ∘ ∂`.
  set dlm := relBoundaryInt S (M + 1) with hdlm
  set gbar : dlm.range →ₗ[ℤ] ℤ :=
    (Submodule.liftQ (LinearMap.ker dlm) φ hvanish).comp
      (LinearMap.quotKerEquivRange dlm).symm.toLinearMap with hgbar
  -- `gbar (∂ c) = φ c`.
  have hgbar_apply : ∀ c : RelativeChainInt S (M + 2),
      gbar ⟨relBoundaryInt S (M + 1) c, ⟨c, rfl⟩⟩ = φ c := by
    intro c
    have hrr : (LinearMap.quotKerEquivRange dlm).symm ⟨relBoundaryInt S (M + 1) c, ⟨c, rfl⟩⟩
        = Submodule.Quotient.mk c := by
      apply (LinearMap.quotKerEquivRange dlm).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    rw [hgbar, LinearMap.comp_apply, LinearEquiv.coe_coe, hrr, Submodule.liftQ_apply]
  -- Extend `gbar` to `g : C_{M+1} → ℤ`.
  obtain ⟨g, hg⟩ := exists_functional_extension_boundaries S gbar
  -- Realize `g` as `relKroneckerInt b`.
  obtain ⟨b, hb⟩ := exists_relCochainInt_of_functional S g
  -- `a = δb` (relative coboundary): check on each basis via the adjunction.
  have hcobound : (a : relCochainsInt S (M + 2)) = relCoboundaryIntₗ S (M + 1) b := by
    apply Subtype.ext
    show (a.1 : SingularCochainInt X (M + 2)) = coboundary X (M + 1) b.1
    funext σ
    have e1 : kronecker a.1.1 (Finsupp.single σ 1) = a.1.1 σ := by rw [kronecker_single, one_mul]
    have e2 : kronecker (coboundary X (M + 1) b.1) (Finsupp.single σ 1)
        = coboundary X (M + 1) b.1 σ := by rw [kronecker_single, one_mul]
    rw [← e1, ← e2]
    -- LHS = φ (single σ) via relKronecker; RHS = relKronecker (δb) (single σ) = g (∂ single σ) = φ (single σ).
    have hlhs : kronecker a.1.1 (Finsupp.single σ 1)
        = φ (RelativeChainInt.mk S (M + 2) (Finsupp.single σ 1)) := by
      rw [hφ, relKroneckerInt_mk]
    have hrhs : kronecker (coboundary X (M + 1) b.1) (Finsupp.single σ 1)
        = φ (RelativeChainInt.mk S (M + 2) (Finsupp.single σ 1)) := by
      rw [show coboundary X (M + 1) b.1 = (relCoboundaryIntₗ S (M + 1) b).1 from rfl,
        ← relKroneckerInt_mk S (relCoboundaryIntₗ S (M + 1) b) (Finsupp.single σ 1),
        ← relKroneckerInt_relBoundary, relBoundaryInt_mk]
      -- relKroneckerInt b (∂ (single σ)) = g (∂ (single σ)) = gbar ⟨∂ (single σ), _⟩ = φ (single σ)
      rw [show relKroneckerInt S b (RelativeChainInt.mk S (M + 1)
            (chainBoundary X (M + 1) (Finsupp.single σ 1)))
          = g (RelativeChainInt.mk S (M + 1) (chainBoundary X (M + 1) (Finsupp.single σ 1)))
          from congrFun (congrArg DFunLike.coe hb) _]
      have hbdmk : RelativeChainInt.mk S (M + 1) (chainBoundary X (M + 1) (Finsupp.single σ 1))
          = relBoundaryInt S (M + 1) (RelativeChainInt.mk S (M + 2) (Finsupp.single σ 1)) := by
        rw [relBoundaryInt_mk]
      rw [hbdmk, hg ⟨relBoundaryInt S (M + 1) (RelativeChainInt.mk S (M + 2) (Finsupp.single σ 1)),
        ⟨_, rfl⟩⟩]
      exact hgbar_apply (RelativeChainInt.mk S (M + 2) (Finsupp.single σ 1))
    rw [hlhs, hrhs]
  refine (RelativeCohomologyInt.mk_eq_zero_iff S (M + 2) a).mpr ?_
  rw [hcobound]
  exact ⟨b, rfl⟩

/-! ### The `Module.Dual` transport of a rank-1 iso -/

/-- Transport a `ℤ`-linear iso `H ≃ₗ ℤ` to `Module.Dual ℤ H ≃ₗ ℤ` (dualize + `Dual ℤ ℤ ≅ ℤ`). -/
noncomputable def dualEquivOfIsoZ {H : Type*} [AddCommGroup H] [Module ℤ H]
    (e : H ≃ₗ[ℤ] ℤ) : Module.Dual ℤ H ≃ₗ[ℤ] ℤ :=
  (e.symm.dualMap).trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ)

/-- **The integral relative universal-coefficient theorem, free case** — `κ` is BIJECTIVE:
`Hⁿ(X, S; ℤ) ≅ Hom(Hₙ(X, S; ℤ), ℤ)` (`n = M+2`) when the previous homology `H_{n-1} = H_{M+1}` is free
(⟹ `Ext(H_{n-1}, ℤ) = 0`) and the relevant boundaries are projective. Combines §4 surjectivity (Hom-side,
projective boundaries) with §6 injectivity (Ext=0 from `H_{M+1}` free). The reusable integral relative
UCT the PD MV five-lemma consumes at every convex cover-piece. -/
theorem relKroneckerHInt_bijective_of_free {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))]
    [Module.Projective ℤ (relBoundariesInt S M)]
    [Module.Projective ℤ (relBoundariesInt S (M + 1))] :
    Function.Bijective (relKronMapInt S (N := M + 1)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    exact relKroneckerHInt_injective_of_free S ω (fun β => LinearMap.congr_fun hω β)
  · exact relKroneckerHInt_surjective S (N := M + 1)

/-- **The integral relative UCT free-case iso** as a `LinearEquiv`
`Hⁿ(X, S; ℤ) ≃ₗ Module.Dual ℤ (Hₙ(X, S; ℤ))` (`n = M+2`), built from `relKroneckerHInt_bijective_of_free`
via `LinearEquiv.ofBijective`. -/
noncomputable def relUCTEquivOfFree {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))]
    [Module.Projective ℤ (relBoundariesInt S M)]
    [Module.Projective ℤ (relBoundariesInt S (M + 1))] :
    RelativeCohomologyInt S (M + 2) ≃ₗ[ℤ] Module.Dual ℤ (RelHomologyInt S (M + 2)) :=
  LinearEquiv.ofBijective (relKronMapInt S) (relKroneckerHInt_bijective_of_free S)

/-- **The integral relative UCT free-case iso, when `Hₙ ≅ ℤ`** — composing `relUCTEquivOfFree` with the
`Module.Dual` transport of a disclosed `Hₙ(X,S; ℤ) ≅ ℤ`: `Hⁿ(X, S; ℤ) ≅ Module.Dual ℤ (Hₙ) ≅ ℤ`. The
shape the PD base case needs (`Hⁿ_c ≅ ℤ` from `Hₙ ≅ ℤ` free-UCT). -/
noncomputable def relUCTIsoZOfFree {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))]
    [Module.Projective ℤ (relBoundariesInt S M)]
    [Module.Projective ℤ (relBoundariesInt S (M + 1))]
    (e : RelHomologyInt S (M + 2) ≃ₗ[ℤ] ℤ) :
    RelativeCohomologyInt S (M + 2) ≃ₗ[ℤ] ℤ :=
  (relUCTEquivOfFree S).trans (dualEquivOfIsoZ e)

end SKEFTHawking.SingularRelativeUCInt

/-! ## §7. The Euclidean application: `H⁴(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ` (discharging `sourceIso`)

Applying the reusable free-case UCT to the local model with `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ`
(`euclLocalHomologyIsoInt'`). The free hypothesis is on `H₃(ℝ⁴, ℝ⁴∖0; ℤ)`, and the boundary-projectivity
instances are the (universally-true over the PID ℤ, but Mathlib-gapped for infinite rank) freeness of the
relative singular boundaries. -/

namespace SKEFTHawking.SingularEuclideanCapIsoInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)

/-- **`H⁴(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ`** — the source-side compactly-supported cohomology iso that discharges
`EuclLocalCapIsoData.sourceIso`, from the reusable free-case relative UCT
(`SingularRelativeUCInt.relUCTIsoZOfFree`) applied with `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ` (`euclLocalHomologyIsoInt'`).

Residual hypotheses (all universally true; the first from `H₃(ℝ⁴, ℝ⁴∖0; ℤ) = 0`, the boundary ones from
the freeness of submodules of the free relative singular chains over the PID ℤ — Mathlib proves the
latter only in finite rank, so they are carried as instance hypotheses): `Module.Free ℤ (RelHomologyInt
{x|x≠0} 3)` and `Module.Projective ℤ (relBoundariesInt {x|x≠0} 2 / 3)`. -/
noncomputable def euclSourceIso
    [Module.Free ℤ (RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 3)]
    [Module.Projective ℤ (relBoundariesInt (X := Eucl 4) {x | x ≠ 0} 2)]
    [Module.Projective ℤ (relBoundariesInt (X := Eucl 4) {x | x ≠ 0} 3)] :
    RelativeCohomologyInt (X := Eucl 4) {x | x ≠ 0} 4 ≃ₗ[ℤ] ℤ :=
  relUCTIsoZOfFree {x | x ≠ 0} euclLocalHomologyIsoInt'

open SKEFTHawking.SingularCohomologyInt in
/-- **`EuclLocalCapIsoData` from just a fundamental cycle + generator match** — the `sourceIso` field is
now DERIVED (`euclSourceIso`, from the reusable free-case UCT) rather than disclosed. Given the residual
instances (`H₃(ℝ⁴,ℝ⁴∖0;ℤ)` free + relative-boundary projectivity — the universally-true, Mathlib-gapped
facts), only a relative fundamental cycle `z` (`∂z ∈ subspace chains`) and the generator match
`ε̄(D_z gen) = ±1` remain to be supplied. This strictly reduces the original disclosed `sourceIso` +
`genMatch` datum to `genMatch` alone (over the residual instances). -/
noncomputable def EuclLocalCapIsoData.ofFundCycle
    [Module.Free ℤ (RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 3)]
    [Module.Projective ℤ (relBoundariesInt (X := Eucl 4) {x | x ≠ 0} 2)]
    [Module.Projective ℤ (relBoundariesInt (X := Eucl 4) {x | x ≠ 0} 3)]
    (z : SingularChainInt (Eucl 4) 4)
    (hz : chainBoundary (Eucl 4) 3 z ∈ subspaceChainsInt {x | x ≠ 0} 3)
    (genMatch : IsUnit (SKEFTHawking.SingularLineMinusPointInt.augHInt (Eucl 4)
      (relativeDualityInt0 {x | x ≠ 0} 3 z hz (euclSourceIso.symm 1)))) :
    EuclLocalCapIsoData where
  z := z
  hz := hz
  sourceIso := euclSourceIso
  genMatch := genMatch

end SKEFTHawking.SingularEuclideanCapIsoInt
