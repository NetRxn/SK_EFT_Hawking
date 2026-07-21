import Mathlib
import SKEFTHawking.BrownInvariant
import SKEFTHawking.SingularKroneckerBasisBridge

/-!
# Audit M4 — the surface-PD transport gate (fence + repair)

**The audited claim.** `PinCharSurface.H1Iso` is documented as identifying the enhancement's
coordinate space with "the surface's genuine singular `H₁(F;ℤ/2)` via the explicit iso"
(`CharSurfaceBounding`), and `pinCharSurfaceOfBundled` fills it with
`homologyBasisOfCohomologyBasis τ.basis` — the **Kronecker/UCT dual** of the carrier's cohomology
basis. Every enhancement-valued consumer (`kernelL`/`TaylorKernelVanishing`,
`EmbeddedCircle.qVal`, `TaylorLegVanishes` through `derivedEσ`/`derivedEτ`) evaluates `q` at
`H1Iso`-coordinates of a genuine homology class.

**The verdict this module encodes.** The Kronecker-dual transport is the WRONG one whenever the
rank is nonzero. The carrier's `hpolar` pins `q.B` to the cup pairing in the **cohomology** basis
`e`; the Kronecker dual is the transport that makes the *Kronecker pairing* the dot product
(`kroneckerH_eq_dotProduct`), not the transport that makes `q.B` the *homology* intersection form.
The two differ by the Gram operator of `q.B`, and the discrepancy is not a harmless normalization:

* §2 `homologyCoords_gauge` — a gauge `e ↦ g ∘ e` on the carried cohomology basis moves the derived
  homology coordinates **contravariantly** (`dualGauge g`, the transpose-inverse), while `hpolar`
  forces the enhancement to move **covariantly** (`gaugePullback q g.symm`). The composite
  `q ∘ (Kronecker transport)` is therefore not gauge-invariant.
* §4 `not_forall_kroneckerTransport_gauge_invariant` — kernel-checked refutation at rank 2 with
  the standard form and an explicit transvection: the two gauge-equivalent carriers assign
  DIFFERENT `q`-values to the same homology class. Since the gauge move keeps the surface, the
  embedding, the fundamental class, `hpolar`, `hchar` and the Brown invariant fixed
  (§5 `gaugePullback_brown` and the `hpolar` transport `hpolar_gaugePullback`), the value the
  consumers read is **not a function of the geometry** at nonzero rank.

**The repair (§3).** `homologyBasisPD Q e := (homologyBasisOfCohomologyBasis e).trans
(gramEquiv Q).symm` — the Gram-corrected transport. `gramEquiv` is an equivalence *unconditionally*
(the `Z4Quadratic.nondeg` field is exactly the invertibility of the Gram operator), so this needs no
new hypothesis. It is the Poincaré-dual transport in disguise: on a closed surface
`homologyCoords e ([Σ] ⌢ a) = gramMap q (e a)` by `hpolar`, so `homologyBasisPD q e ([Σ] ⌢ a) = e a`
— the derived homology basis is the PD image of the cohomology basis, which is what a
Guillou–Marin/Taylor enhancement on `H₁` requires. It is gauge-covariant
(`homologyBasisPD_gauge`) and the enhancement value it produces is gauge-INVARIANT
(`q_homologyBasisPD_gauge_invariant`) — precisely the property §4 refutes for the raw transport.

**Equivalence certificate (§6).** At rank `0` the two transports are equal
(`homologyBasisPD_eq_of_rank_zero`), so every rank-zero consumer — which is the entire live
`PinPlusKTRankZeroBounding` chain — is untouched by the repair. The defect is a strictly
nonzero-rank one, exactly as audit M4 flagged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/

namespace SKEFTHawking.CharSurfacePDTransport

open SKEFTHawking.Brown
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularKroneckerBasisBridge

/-! ## §1. The two halves of the gauge move -/

/-- The `ZMod 2` scalars are `0` and `1` — the reason every `ZMod 2`-additive map is automatically
`ZMod 2`-linear (used to package `B`'s slots as `LinearMap`s). -/
theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- **The enhancement's half of the gauge**: pullback of a `Z4Quadratic` along a linear
automorphism of the coordinate space. This is the move `hpolar` FORCES on `q` when the carried
cohomology basis is gauged: if `e' = g ∘ e` then `q' := gaugePullback q g.symm` is the unique
enhancement for which `q'.B (e' a) (e' b) = q.B (e a) (e b)` (§5 `hpolar_gaugePullback`). -/
def gaugePullback {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) : Z4Quadratic ι where
  q x := Q.q (g x)
  B x y := Q.B (g x) (g y)
  refine' x y := by rw [map_add]; exact Q.refine' (g x) (g y)
  B_add_left x y z := by rw [map_add]; exact Q.B_add_left (g x) (g y) (g z)
  B_symm x y := Q.B_symm (g x) (g y)
  nondeg x hx := by
    have : g x = 0 := Q.nondeg (g x) fun y => by
      have := hx (g.symm y); rwa [g.apply_symm_apply] at this
    simpa using congrArg g.symm this

@[simp] theorem gaugePullback_q {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (x : ι → ZMod 2) :
    (gaugePullback Q g).q x = Q.q (g x) := rfl

@[simp] theorem gaugePullback_B {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (x y : ι → ZMod 2) :
    (gaugePullback Q g).B x y = Q.B (g x) (g y) := rfl

/-- **The derived homology coordinates' half of the gauge**: the transpose-inverse. Explicitly,
`(dualGauge g u) i = ∑ j, (g.symm (δ i)) j * u j` — matrix-free, and exactly the transformation
the Kronecker bridge produces (§2). -/
def dualGauge {n : ℕ} (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun u := fun i => ∑ j, g.symm (Pi.single i 1) j * u j
  map_add' u v := by
    funext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c u := by
    funext i
    simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem dualGauge_apply {n : ℕ} (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (u : Fin n → ZMod 2) (i : Fin n) :
    dualGauge g u i = ∑ j, g.symm (Pi.single i 1) j * u j := rfl

/-! ## §2. The transformation law of the Kronecker transport (the contravariance) -/

variable {X : TopCat}

/-- **The Kronecker transport is CONTRAVARIANT under a cohomology-basis gauge.** Gauging the
carried basis by `g` transforms the derived homology coordinates by the transpose-inverse
`dualGauge g` — the opposite variance from the enhancement's forced move `gaugePullback _ g.symm`
(§5). This is the whole defect in one equation. -/
theorem homologyCoords_gauge {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    homologyCoords (e.trans g) x = dualGauge g (homologyCoords e x) := by
  funext i
  show kroneckerH (N + 1) ((e.trans g).symm (Pi.single i 1)) x = _
  rw [show ((e.trans g).symm (Pi.single i 1)) = e.symm (g.symm (Pi.single i 1)) from rfl]
  rw [kroneckerH_symm_eq_sum e (g.symm (Pi.single i 1)) x]
  rfl

/-! ## §3. THE REPAIR — the Gram-corrected (Poincaré-dual) transport -/

/-- **The Gram operator of the enhancement's polar form**: `u ↦ (i ↦ B (δ i) u)`. On a bundled
carrier `hpolar` makes this exactly the "cup with, then evaluate on `[Σ]`" operator — i.e. the
operator through which Poincaré duality of the surface acts on coordinates. -/
def gramMap {n : ℕ} (Q : Z4Quadratic (Fin n)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun u := fun i => Q.B (Pi.single i 1) u
  map_add' u v := by funext i; exact Q.B_add_right _ u v
  map_smul' c u := by
    funext i
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp [Q.B_symm _ (0 : Fin n → ZMod 2), Q.B_zero_left]
    · simp

@[simp] theorem gramMap_apply {n : ℕ} (Q : Z4Quadratic (Fin n)) (u : Fin n → ZMod 2) (i : Fin n) :
    gramMap Q u i = Q.B (Pi.single i 1) u := rfl

/-- Standard-basis expansion of the polar form's LEFT slot: `B y u = ∑ i, y i * B (δ i) u`. The
`ZMod 2`-linearity of `B` in its first argument, made explicit (the scalars are `0`/`1`). -/
theorem B_left_expand {n : ℕ} (Q : Z4Quadratic (Fin n)) (y u : Fin n → ZMod 2) :
    Q.B y u = ∑ i, y i * gramMap Q u i := by
  have hy : y = ∑ i, y i • Pi.single i (1 : ZMod 2) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ (s : Finset (Fin n)),
      Q.B (∑ i ∈ s, y i • Pi.single i (1 : ZMod 2)) u = ∑ i ∈ s, y i * gramMap Q u i := by
    intro s
    classical
    induction s using Finset.induction with
    | empty => simpa using Q.B_zero_left u
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Q.B_add_left, ih]
        congr 1
        rcases zmod2_eq_zero_or_one (y a) with h | h
        · rw [h]; simp [Q.B_zero_left]
        · rw [h]; simp
  conv_lhs => rw [hy]
  exact hlin Finset.univ

theorem gramMap_injective {n : ℕ} (Q : Z4Quadratic (Fin n)) :
    Function.Injective (gramMap Q) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  refine Q.nondeg u fun y => ?_
  rw [Q.B_symm, B_left_expand Q y u]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show gramMap Q u i = 0 from by rw [hu]; rfl, mul_zero]

theorem gramMap_bijective {n : ℕ} (Q : Z4Quadratic (Fin n)) :
    Function.Bijective (gramMap Q) :=
  ⟨gramMap_injective Q,
    (LinearMap.injective_iff_surjective (f := gramMap Q)).mp (gramMap_injective Q)⟩

/-- **The Gram operator is an equivalence, UNCONDITIONALLY** — `Z4Quadratic.nondeg` is exactly its
invertibility, so the repair below needs no extra hypothesis. -/
noncomputable def gramEquiv {n : ℕ} (Q : Z4Quadratic (Fin n)) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.ofBijective (gramMap Q) (gramMap_bijective Q)

@[simp] theorem gramEquiv_apply {n : ℕ} (Q : Z4Quadratic (Fin n)) (u : Fin n → ZMod 2) :
    gramEquiv Q u = gramMap Q u := rfl

/-- **THE REPAIRED TRANSPORT**: the homology basis a `Z4Quadratic`-enhanced cohomology basis
induces — the Kronecker/UCT dual, Gram-corrected. Unlike the raw dual this is COVARIANT in the
gauge (§5), so the enhancement value it produces is a function of the class, not of the basis
choice. -/
noncomputable def homologyBasisPD {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Homology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (homologyBasisOfCohomologyBasis e).trans (gramEquiv Q).symm

theorem gramMap_homologyBasisPD {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    gramMap Q (homologyBasisPD Q e x) = homologyCoords e x :=
  (gramEquiv Q).apply_symm_apply _

/-- **The raw transport factors through the repaired one by the Gram operator** — the exact
dictionary between the two coordinate systems. Read right-to-left: if a homology class has
PD-correct coordinates `v`, the raw Kronecker transport reports `gramMap Q v`. This is what §4b
turns into a truth-value flip of the frozen Taylor Prop. -/
theorem homologyCoords_eq_gramMap {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    homologyCoords e x = gramMap Q (homologyBasisPD Q e x) :=
  (gramMap_homologyBasisPD Q e x).symm

/-- **The PD-normalization — why `homologyBasisPD` is THE right transport.** Suppose the surface
carries a Poincaré-duality map `pd : H¹(Σ;ℤ/2) → H₁(Σ;ℤ/2)` satisfying the cap adjunction
`⟨ω, pd a⟩ = ⟨ω ⌣ a, [Σ]⟩`, and the enhancement satisfies the carrier's `hpolar` tie against the
same `[Σ]`. Then the repaired transport sends the PD image of the cohomology basis to the standard
basis: `homologyBasisPD Q e (pd a) = e a`. That is exactly the statement "the derived `H₁`-basis is
the Poincaré dual of the carried `H¹`-basis", which is what a Guillou–Marin/Taylor enhancement on
`H₁` requires — and it is FALSE for the raw Kronecker transport unless `gramMap Q = id` (§4b).

The `pd`/`hpd` hypotheses are the surface's 2-dimensional PD tower, which is the documented
still-abstract anchor of `CharPairStrBundled` — named here as an explicit hypothesis rather than
assumed silently. -/
theorem homologyBasisPD_pd {n : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X 1 ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (surfClass : Homology X 2)
    (hpolar : ∀ a b : Cohomology X 1, Q.B (e a) (e b) = kroneckerH 2 (cupH a b) surfClass)
    (pd : Cohomology X 1 → Homology X 1)
    (hpd : ∀ (ω a : Cohomology X 1), kroneckerH 1 ω (pd a) = kroneckerH 2 (cupH ω a) surfClass)
    (a : Cohomology X 1) :
    homologyBasisPD Q e (pd a) = e a := by
  refine gramMap_injective Q ?_
  rw [gramMap_homologyBasisPD]
  funext i
  rw [homologyCoords_apply, hpd, ← hpolar, e.apply_symm_apply, gramMap_apply]

/-! ## §4. The refutation — the raw Kronecker transport is NOT gauge-invariant -/

/-- The rank-2 transvection `(x₀, x₁) ↦ (x₀ + x₁, x₁)` — an involution over `ZMod 2`, and NOT
orthogonal (`g gᵀ ≠ 1`), which is exactly what makes it detect the variance mismatch. -/
def transvection2 : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun x := ![x 0 + x 1, x 1]
  map_add' := by decide
  map_smul' := by decide
  invFun x := ![x 0 + x 1, x 1]
  left_inv := by decide
  right_inv := by decide

/-- **THE FENCE (kernel-checked refutation).** There is NO gauge-invariance for the raw Kronecker
transport: for the standard rank-2 form and the transvection gauge, the enhancement value read
through the derived homology coordinates CHANGES. Combined with §2 (`homologyCoords_gauge` carries
this to any surface class whose coordinates are the witness vector) and §5 (the gauged carrier is a
legitimate carrier with the same surface, `hpolar` and Brown invariant), the value
`Q.q (homologyBasisOfCohomologyBasis e x)` — what `EmbeddedCircle.qVal`,
`PinCharSurface.Bounding.kernelL`/`TaylorKernelVanishing` and `TaylorLegVanishes` all read — is not
a function of the geometry at nonzero rank. -/
theorem not_forall_kroneckerTransport_gauge_invariant :
    ¬ ∀ (n : ℕ) (Q : Z4Quadratic (Fin n))
        (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (v : Fin n → ZMod 2),
      (gaugePullback Q g.symm).q (dualGauge g v) = Q.q v := by
  intro h
  have := h 2 (Z4Quadratic.stdQuadratic 2) transvection2 ![0, 1]
  revert this
  decide

/-- The witness in explicit form: the two gauge-equivalent readings of the SAME class differ by
`1` vs `2` in `ZMod 4`. -/
theorem kroneckerTransport_gauge_witness :
    (gaugePullback (Z4Quadratic.stdQuadratic 2) transvection2.symm).q (dualGauge transvection2 ![0, 1]) = 2 ∧
      (Z4Quadratic.stdQuadratic 2).q ![0, 1] = 1 := by
  constructor <;> decide

/-! ### §4b. The genus-1 witness — the frozen Taylor Prop FLIPS truth value -/

/-- **The smallest honest characteristic-surface model above rank zero**: the genus-1 (torus)
enhancement. `B` is the symplectic mod-2 intersection pairing of `H₁(T²;ℤ/2)` in an `(a, b)`-basis;
`q` is the Guillou–Marin refinement with `q(a) = 0`, `q(b) = 2`. Unlike `stdQuadratic` (whose Gram
operator is the identity — the accidental case where the raw transport happens to be right), a
symplectic basis has Gram operator the coordinate SWAP. -/
def hyperbolic2 : Z4Quadratic (Fin 2) where
  q x := embed2 (x 1 + x 0 * x 1)
  B x y := x 0 * y 1 + x 1 * y 0
  refine' := by decide
  B_add_left := by decide
  B_symm := by decide
  nondeg := by decide

/-- The Gram operator of a symplectic basis is the coordinate swap — NOT the identity. So for a
genus-1 characteristic surface the raw Kronecker transport and the repaired PD transport report
genuinely different coordinates for the same homology class (`homologyCoords_eq_gramMap`). -/
theorem gramMap_hyperbolic2 (v : Fin 2 → ZMod 2) : gramMap hyperbolic2 v = ![v 1, v 0] := by
  revert v; decide

/-- Contrast: for the standard (orthonormal) form the Gram operator IS the identity — this is the
degenerate case in which the raw Kronecker transport is accidentally correct. A closed surface of
positive genus has no orthonormal basis for its mod-2 intersection form on the symplectic sector,
so this is not the generic situation. -/
theorem gramMap_stdQuadratic {n : ℕ} (v : Fin n → ZMod 2) :
    gramMap (Z4Quadratic.stdQuadratic n) v = v := by
  funext i
  show (Z4Quadratic.stdQuadratic n).B (Pi.single i 1) v = v i
  show ∑ j, (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j * v j = v i
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- **THE TRUTH-VALUE FLIP — the sharpest form of the fence.** Take the genus-1 model with the
a-cycle metabolizer `L = span ![1, 0]` (the honest Taylor/Klug bounding kernel of a solid torus).
Taylor's Theorem 1.1 says the enhancement vanishes on `L`, and it does: `q ![1,0] = 0`. But the RAW
Kronecker transport reports that class's coordinates as `gramMap hyperbolic2 ![1,0] = ![0,1]`
(`homologyCoords_eq_gramMap`), where `q = 2 ≠ 0`. So `PinCharSurface.Bounding.TaylorKernelVanishing`
— stated through `pinCharSurfaceOfBundled`'s `H1Iso` — is FALSE exactly where the geometry says it
must be TRUE. The frozen Prop is not merely unproven at nonzero rank; it is mis-stated. -/
theorem hyperbolic2_taylor_flip :
    hyperbolic2.q ![1, 0] = 0 ∧ hyperbolic2.q (gramMap hyperbolic2 ![1, 0]) ≠ 0 := by
  refine ⟨by decide, ?_⟩
  rw [gramMap_hyperbolic2]
  decide

/-! ## §5. The repaired transport IS gauge-covariant, and the gauge is geometry-preserving -/

/-- **Covariance of the repaired transport**: gauging the cohomology basis by `g` moves the
PD-corrected homology coordinates by `g` itself — the SAME variance as the enhancement. -/
theorem homologyBasisPD_gauge {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    homologyBasisPD (gaugePullback Q g.symm) (e.trans g) x = g (homologyBasisPD Q e x) := by
  set w := homologyBasisPD Q e x with hw
  have hgw : gramMap Q w = homologyCoords e x := gramMap_homologyBasisPD Q e x
  have key : gramMap (gaugePullback Q g.symm) (g w) = homologyCoords (e.trans g) x := by
    funext i
    rw [gramMap_apply, gaugePullback_B, g.symm_apply_apply, homologyCoords_gauge,
      dualGauge_apply, B_left_expand Q (g.symm (Pi.single i 1)) w]
    exact Finset.sum_congr rfl fun j _ => by rw [hgw]
  have : gramEquiv (gaugePullback Q g.symm) (g w) = homologyCoords (e.trans g) x := key
  rw [homologyBasisPD]
  exact (LinearEquiv.symm_apply_eq _).mpr this.symm

/-- **THE REPAIR'S HEADLINE — gauge-INVARIANCE of the enhancement value.** The `q`-value read
through the PD-corrected transport is the same for a carrier and for any gauge-equivalent one.
This is exactly the property §4 refutes for the raw Kronecker transport. -/
theorem q_homologyBasisPD_gauge_invariant {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    (gaugePullback Q g.symm).q (homologyBasisPD (gaugePullback Q g.symm) (e.trans g) x)
      = Q.q (homologyBasisPD Q e x) := by
  rw [homologyBasisPD_gauge, gaugePullback_q, g.symm_apply_apply]

/-- The polar form is likewise gauge-invariant through the repaired transport. -/
theorem B_homologyBasisPD_gauge_invariant {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x y : Homology X (N + 1)) :
    (gaugePullback Q g.symm).B (homologyBasisPD (gaugePullback Q g.symm) (e.trans g) x)
        (homologyBasisPD (gaugePullback Q g.symm) (e.trans g) y)
      = Q.B (homologyBasisPD Q e x) (homologyBasisPD Q e y) := by
  rw [homologyBasisPD_gauge, homologyBasisPD_gauge, gaugePullback_B, g.symm_apply_apply,
    g.symm_apply_apply]

/-- **The gauge preserves `hpolar`**: if `(e, Q)` satisfies the carrier's polar tie against any
pairing `c`, so does `(g ∘ e, gaugePullback Q g.symm)`. Hence the gauged carrier is a legitimate
`CharPairStrBundled` with the SAME surface, embedding and fundamental class — the §4 discrepancy is
between two honest carriers of one geometry, not between an honest and a fake one. -/
theorem hpolar_gaugePullback {n N : ℕ} (Q : Z4Quadratic (Fin n))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (g : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (c : Cohomology X (N + 1) → Cohomology X (N + 1) → ZMod 2)
    (hpolar : ∀ a b, Q.B (e a) (e b) = c a b) (a b : Cohomology X (N + 1)) :
    (gaugePullback Q g.symm).B ((e.trans g) a) ((e.trans g) b) = c a b := by
  rw [gaugePullback_B]
  show Q.B (g.symm (g (e a))) (g.symm (g (e b))) = c a b
  rw [g.symm_apply_apply, g.symm_apply_apply]
  exact hpolar a b

/-- **The gauge preserves the Brown invariant** — the computed grade `abk8` is untouched, so the
gauged carrier is not merely legitimate but sits in the same graded class. (`gaussSum4` is a sum
over the whole space, invariant under any bijective reparametrization.) -/
theorem gaugePullback_gaussSum4 {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    gaussSum4 (gaugePullback Q g).q = gaussSum4 Q.q :=
  Equiv.sum_comp g.toEquiv (fun x => zeta4 (Q.q x))

theorem gaugePullback_brownUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (gaugePullback Q g).brownUnit = Q.brownUnit := by
  have h := (gaugePullback Q g).gaussSum4_eq_brownUnit
  rw [gaugePullback_gaussSum4, Q.gaussSum4_eq_brownUnit] at h
  exact zeta4_mul_pow_right_inj (N := Fintype.card ι) h.symm

theorem gaugePullback_brown {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)
    (g : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (gaugePullback Q g).brown = Q.brown := by
  simp only [Z4Quadratic.brown, gaugePullback_brownUnit]

/-! ## §6. EQUIVALENCE CERTIFICATE — the two transports agree at rank zero -/

/-- **The live chain is untouched.** At rank `0` the coordinate space is a subsingleton, so the raw
Kronecker transport and the PD-corrected transport are literally equal. Every rank-zero consumer —
which is the whole `PinPlusKTRankZeroBounding` chain — is unaffected by the repair, and the M4
defect is strictly a nonzero-rank one. -/
theorem homologyBasisPD_eq_of_rank_zero {N : ℕ} (Q : Z4Quadratic (Fin 0))
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin 0 → ZMod 2)) :
    homologyBasisPD Q e = homologyBasisOfCohomologyBasis e :=
  LinearEquiv.ext fun _ => Subsingleton.elim _ _

end SKEFTHawking.CharSurfacePDTransport
