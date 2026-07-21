/-
# Phase 5q.H close-out — THE ℝ RELATIVE SUBSTRATE: the pair-LES/PD decomposition of the Novikov `half`

`PinPlusKTSpinSigmaNovikovOpener.NovikovBoundaryRestriction` reduces the σ-descent's last geometric atom
(`NovikovLagrangianAtom`) to a single DEEP residual: the `half` field — the real Poincaré–Lefschetz
half-dimensionality `n = 2·dim(im ι*)` of the restriction image. `NovikovBoundaryRestriction.isotropic`
already banks the isotropy conjunct (from `func`/`bvanish`/`gram`). This module OPENS the `half` residual by
DECOMPOSING it into the three genuine relative-cohomology pieces of the classical "half lives, half dies"
argument, and DERIVES `half` from them — so the single PD residual is factored into named, in-tree-realizable
shapes.

## The coefficients + architecture decision — route (b): the ℤ (Int) stack + ℝ extension of scalars

The consumers are already ℤ-valued (`SingularCohomologyInt.Cohomology`, `IntFundamentalClass`,
`cohomologyPullbackInt`, `interFormInt`, `cupH24`; the §1 isotropy lemma `interFormInt_isotropic_of_pullback`
lives there), and the boundary lattice form is `Bd.map (Int.cast : ℤ → ℝ)` — the ℤ intersection matrix
tensored to ℝ. There is NO honest need for a separate singular-ℝ chain tower: the relative-cohomology pieces
live on the in-tree integral stack (`SingularRelativeCohomologyRestrictInt.relCohomRestrictInt` — the
restriction; `SingularRelativeKroneckerEquivInt.relKroneckerIntEquiv` — the relative Kronecker pairing; the
pair-LES `SingularPairLES` — exactness), and the Novikov Lagrangian form lives over ℝ. So the substrate is an
**abstract ℝ-linear-algebra engine** whose fields are the ℝ-tensored images of those integral pieces, each
realizable in-tree by extension of scalars (`⊗ℝ`, UCT-over-a-field free parts — the #172 precedent). This is
the cheapest honest route; it needs no new singular machinery.

## The three pieces (the named shapes from #174/#177/#180)

`NovikovRealPairLES Bd` carries exactly:

* **(i) the pair-LES middle exactness** — `hexact : Function.Exact rest2 delta`, i.e.
  `im(ι* : H²(W) → H²(∂W)) = ker(δ : H²(∂W) → H³(W,∂W))` (the cohomology pair-LES at `H²(∂W)`; the
  ℝ-image of `SingularPairLES`'s `exact_homIncl_homProj`/`exact_homProj_connecting`);
* **(ii) the relative Kronecker pairing** — `pairing : H²(W) →ₗ H³(W,∂W) →ₗ ℝ` with `hnondeg` (the
  δ-side is separated by the `H²(W)`-family): the ℝ-image of `relKroneckerIntEquiv`, the PD pairing
  `H³(W,∂W) × H₃(W,∂W)` against `[W,∂W]` the co-isotropy's PD-intertwining consumes;
* **(iii) the restriction-image object** — `LinearMap.range rest2`, identified as `ker delta` (via
  `range_eq_ker`) — what `NovikovBoundaryRestriction.rest2` wants to BE for the honest instantiation.

The **PD-intertwining** `hadj : ⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` (`rest2 ⊣ delta` under the Kronecker pairing) is
the adjunction linking the boundary form to the connecting map — the single relation that couples the pieces.

## What this buys — `half` is DERIVED, not disclosed

* `isotropic`/`isotropic_bilin` — `im ι*` is isotropic. NOT a separate input: from `hadj` + `hexact`
  (`δ ∘ ι* = 0`), the boundary form on `im ι*` is `⟨a, δ(ι*b)⟩ = ⟨a, 0⟩ = 0`. So the isotropy that §1 banks
  via `func`/`bvanish`/`gram` re-emerges here as a THEOREM of the pair-LES + adjunction.
* `coisotropic` — `(im ι*)^⊥ ⊆ im ι*`: `v ⊥ im ι*` ⟹ `⟨a, δv⟩ = 0 ∀a` (`hadj`) ⟹ `δv = 0` (`hnondeg`) ⟹
  `v ∈ ker δ = im ι*` (`hexact`). This is the "half dies" — the PD-intertwining consuming the Kronecker
  nondegeneracy.
* `half` — `n = 2·dim(im ι*)`: isotropic + coisotropic + boundary-nondegenerate, via the banked
  `finrank_eq_half_of_isotropic_coisotropic`. The monolithic PD residual is now a corollary of (i)+(ii).

## Consumer wiring

`toBoundaryRestriction` builds a genuine `NovikovBoundaryRestriction Bd` from the substrate (the provider
pattern for constructed `W`'s with `[W,∂W]` data), so `NovikovHalfDimAtom`/`NovikovLagrangianAtom` are
served with `half` reduced to the pair-LES/Kronecker/adjunction triple; `lagrangian` produces the
`NovikovLagrangianAtom` body directly. `sigmaInvariant_of_pairLES` records the hcob-sibling shape:
σ-invariance over the boundary of an orientable cobordism (`W∖E(V)` for the dual-spin `hdouble`) is the SAME
engine — the boundary form has a Lagrangian, so its signature vanishes.

Dimension discipline: `W` 5-dim (the tethered bordism or `W∖E(V)`), `∂W` 4-dim; the forms on `H²`;
`im ι* ⊆ H²(∂W;ℝ) = Fin n → ℝ`. Spin-side, `k₀`-free.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaNovikovHalfDim

namespace SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate

variable {k : WithTop ℕ∞}

open scoped Manifold
open QuadraticMap Module
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle
open SKEFTHawking.PinPlusKTSpinSigmaHbord
open SKEFTHawking.PinPlusKTSpinSigmaNovikovOpener
open SKEFTHawking.PinPlusKTSpinSigmaNovikovHalfDim

/-! ## §1. The ℝ pair-LES / PD substrate — the three pieces bundled -/

/-- **The Novikov real pair-LES substrate.** For a boundary intersection matrix `Bd` (in the atom,
`Bd = blockDiag (II M_p) (−(II M_q))`), this bundles the ℝ-tensored relative-cohomology data of a bounding
manifold `W` (`∂W ↪ W`) that DECOMPOSES the Novikov `half` residual:

* `H2W`/`H3rel` — `H²(W;ℝ)` and `H³(W,∂W;ℝ)`;
* `rest2` — restriction `ι* : H²(W) → H²(∂W) = Fin n → ℝ` (piece iii's carrier);
* `delta` — connecting `δ : H²(∂W) → H³(W,∂W)`;
* `pairing` — relative Kronecker `H²(W) × H³(W,∂W) → ℝ` (piece ii);
* `hexact` — pair-LES middle exactness `im ι* = ker δ` (piece i);
* `hadj` — the PD-intertwining `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` (`rest2 ⊣ delta`);
* `hnondeg` — Kronecker nondegeneracy (the `H²(W)`-family separates `H³(W,∂W)`);
* `hbdnd` — boundary-form nondegeneracy (`radical = ⊥`, banked from even-unimodularity).

`half` is then a THEOREM (`NovikovRealPairLES.half`), not a field. -/
structure NovikovRealPairLES {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℤ) where
  /-- `H²(W;ℝ)`. -/
  H2W : Type
  [instAcgW2 : AddCommGroup H2W]
  [instModW2 : Module ℝ H2W]
  /-- `H³(W,∂W;ℝ)`. -/
  H3rel : Type
  [instAcgR3 : AddCommGroup H3rel]
  [instModR3 : Module ℝ H3rel]
  /-- The restriction `ι* : H²(W) → H²(∂W) = Fin n → ℝ`. -/
  rest2 : H2W →ₗ[ℝ] (Fin n → ℝ)
  /-- The connecting `δ : H²(∂W) → H³(W,∂W)`. -/
  delta : (Fin n → ℝ) →ₗ[ℝ] H3rel
  /-- The relative Kronecker pairing `H²(W) × H³(W,∂W) → ℝ`. -/
  pairing : H2W →ₗ[ℝ] H3rel →ₗ[ℝ] ℝ
  /-- **(i) pair-LES middle exactness** `im ι* = ker δ`. -/
  hexact : Function.Exact rest2 delta
  /-- **PD-intertwining** `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩` — `rest2 ⊣ delta` under the Kronecker pairing. -/
  hadj : ∀ (a : H2W) (v : Fin n → ℝ),
    (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap') (rest2 a) v = pairing a (delta v)
  /-- **(ii) Kronecker nondegeneracy** — the `H²(W)`-family separates `H³(W,∂W)`. -/
  hnondeg : ∀ x : H3rel, (∀ a : H2W, pairing a x = 0) → x = 0
  /-- **Boundary-form nondegeneracy** `radical = ⊥` (banked from even-unimodularity). -/
  hbdnd : (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥

attribute [instance] NovikovRealPairLES.instAcgW2 NovikovRealPairLES.instModW2
  NovikovRealPairLES.instAcgR3 NovikovRealPairLES.instModR3

variable {n : ℕ} {Bd : Matrix (Fin n) (Fin n) ℤ} (d : NovikovRealPairLES Bd)

/-- **Piece (iii): the restriction-image object as `ker δ`.** `im ι* = ker δ` — the pair-LES exactness
identifies the restriction image with the kernel of the connecting map. -/
theorem NovikovRealPairLES.range_eq_ker :
    LinearMap.range d.rest2 = LinearMap.ker d.delta :=
  (LinearMap.exact_iff.mp d.hexact).symm

/-- `δ ∘ ι* = 0` — the composite of the pair-LES is zero (immediate from exactness). -/
theorem NovikovRealPairLES.delta_rest2 (a : d.H2W) : d.delta (d.rest2 a) = 0 :=
  d.hexact.apply_apply_eq_zero a

/-- **Bilinear isotropy of `im ι*`.** `⟨ι*a ∪ ι*b, [∂W]⟩ = 0`: by `hadj` the value is `⟨a, δ(ι*b)⟩`, and
`δ(ι*b) = 0` by exactness. This is the §1 `func`/`bvanish`/`gram` isotropy re-derived from the pair-LES +
adjunction. -/
theorem NovikovRealPairLES.isotropic_bilin (a b : d.H2W) :
    (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap') (d.rest2 a) (d.rest2 b) = 0 := by
  rw [d.hadj a (d.rest2 b), d.delta_rest2 b, map_zero]

/-- **Quadratic isotropy of `im ι*`.** The boundary quadratic form vanishes on the restriction image. -/
theorem NovikovRealPairLES.isotropic {x : Fin n → ℝ} (hx : x ∈ LinearMap.range d.rest2) :
    (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  have h2 : (2 : ℝ) • (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' (d.rest2 a) = 0 := by
    have := d.isotropic_bilin a a
    rwa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul, ← two_smul ℝ] at this
  have h2' : (2 : ℝ) ≠ 0 := two_ne_zero
  exact (smul_eq_zero.mp h2).resolve_left h2'

/-- **Co-isotropy of `im ι*` — the "half dies" direction.** `(im ι*)^⊥ ⊆ im ι*`. Proof: `v ⊥ im ι*` gives
`⟨ι*a ∪ v, [∂W]⟩ = 0 ∀a`, so `⟨a, δv⟩ = 0 ∀a` by `hadj`, so `δv = 0` by `hnondeg`, so `v ∈ ker δ = im ι*` by
exactness. The PD-intertwining consuming the Kronecker nondegeneracy. -/
theorem NovikovRealPairLES.coisotropic :
    LinearMap.BilinForm.orthogonal
        (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap')
        (LinearMap.range d.rest2) ≤ LinearMap.range d.rest2 := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  rw [d.range_eq_ker, LinearMap.mem_ker]
  apply d.hnondeg
  intro a
  rw [← d.hadj a v]
  have := hv (d.rest2 a) ⟨a, rfl⟩
  rwa [LinearMap.BilinForm.isOrtho_def] at this

/-- **The Novikov `half`, DERIVED.** `n = 2·dim(im ι*)`: the restriction image is isotropic + co-isotropic
for the nondegenerate boundary form, so half-dimensional (`finrank_eq_half_of_isotropic_coisotropic`). The
single Poincaré–Lefschetz residual is now a corollary of pieces (i)+(ii). -/
theorem NovikovRealPairLES.half :
    n = 2 * Module.finrank ℝ (LinearMap.range d.rest2) :=
  finrank_eq_half_of_isotropic_coisotropic Bd d.hbdnd (LinearMap.range d.rest2)
    (fun _ hx => d.isotropic hx) d.coisotropic

include d in
/-- **The Novikov Lagrangian, produced from the substrate.** The restriction image is a half-dimensional
isotropic subspace of the boundary form — exactly the `NovikovLagrangianAtom` body for `Bd`. -/
theorem NovikovRealPairLES.lagrangian :
    ∃ L : Submodule ℝ (Fin n → ℝ),
      n = 2 * Module.finrank ℝ L ∧
      ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0 :=
  ⟨LinearMap.range d.rest2, d.half, fun _ hx => d.isotropic hx⟩

/-! ## §2. Consumer wiring — the `NovikovBoundaryRestriction` provider -/

include d in
/-- **The substrate provides a genuine `NovikovBoundaryRestriction`.** From `NovikovRealPairLES Bd` build the
Opener's boundary-restriction engine directly: `H²(W) := d.H2W`, `rest2 := d.rest2`, the boundary cup
`cupBd := polarBilin Q` (`evalBd := ½·id` correcting the polarization factor so `gram` returns `Q`), the
`func` isotropy from `isotropic_bilin` (with `cupW`/`rest4 := 0`), and — the point — `half := d.half`, the
PD residual now DERIVED from the pair-LES/Kronecker triple. So a constructed `W` with `[W,∂W]` relative data
feeds `NovikovHalfDimAtom` with `half` no longer disclosed but factored. -/
noncomputable def NovikovRealPairLES.toBoundaryRestriction : NovikovBoundaryRestriction Bd where
  H2W := d.H2W
  H4W := ℝ
  H4bd := ℝ
  cupW := 0
  cupBd := QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
  rest2 := d.rest2
  rest4 := 0
  evalBd := (2⁻¹ : ℝ) • LinearMap.id
  func := by intro a b; rw [d.isotropic_bilin a b]; simp
  bvanish := by intro w; simp
  gram := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self, nsmul_eq_mul, smul_eq_mul]
    ring
  half := d.half

/-! ## §3. The σ-descent consumer — `NovikovHalfDimAtom` from per-pair real substrates -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **`NovikovHalfDimAtom` from per-pair real pair-LES substrates.** If, for every data-bordant pair
`p, q`, the boundary block form `blockDiag (II M_p) (−(II M_q))` carries a `NovikovRealPairLES` (the ℝ
relative-cohomology data of the tethered bordism `W`), then the σ-descent's residual half-dim atom holds:
each substrate produces its `NovikovBoundaryRestriction` via `toBoundaryRestriction`. So the σ-descent
completes modulo exactly the three pair-LES/Kronecker pieces — the `half` residual fully factored. -/
theorem novikovHalfDim_of_realPairLES {a : SpinSigmaAtoms prov}
    (h : ∀ p q : StrMfd (spinEmptyData prov), IsDataBordant (spinEmptyData prov) p q →
      NovikovRealPairLES
        (blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q)))) :
    NovikovHalfDimAtom prov a :=
  fun p q hb => ⟨(h p q hb).toBoundaryRestriction⟩

/-! ## §4. The hcob sibling — signature invariance over an orientable cobordism -/

/-- **The hcob-sibling shape: σ is a cobordism invariant, via the SAME engine.** For even-unimodular
boundary forms `A`, `B` and a `NovikovRealPairLES` on the block form `blockDiag A (−B)` — the ℝ
relative-cohomology data of an orientable cobordism `W` with `∂W = ∂₁ ⊔ (−∂₂)` — the lattice signatures
agree: `σ(A) = σ(B)`. Proof: `lagrangian` produces the half-dim isotropic `L`, which makes the (even-
unimodular, hence nondegenerate) block form metabolic (`latticeSig_eq_zero_of_lagrangian`), so `σ = 0`;
block additivity + orientation reversal (`latticeSig_blockDiag` + `latticeSig_neg`) give `σ(A) − σ(B) = 0`.

This is the shared floor #180's `hcob`/`DualSpinFromW.hdouble` bottoms out in — `σ(M) = σ(∂E(V))` over the
cobordism `W∖E(V)` is this lemma with `A = II(M)`, `B = II(∂E(V))` — the exact twin of the σ-lane's
`hbord_of_novikovLagrangian`. The two consumers (σ-lane floor + dA leaf) are genuinely ONE engine: the real
pair-LES substrate on an orientable cobordism's boundary. (The factor-of-2 double-cover step of `hdouble`
is a DISTINCT geometric input — the orientation double cover `∂E(V) → V` — not this restriction substrate.) -/
theorem latticeSig_eq_of_realPairLES {r s : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (B : Matrix (Fin s) (Fin s) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (d : NovikovRealPairLES (blockDiag A (-B))) :
    latticeSig A = latticeSig B := by
  obtain ⟨L, hdim, hiso⟩ := d.lagrangian
  have hnegB := isEvenUnimodular_neg _ hB
  have hbd_eu := isEvenUnimodular_blockDiag A (-B) hA hnegB
  have hzero := latticeSig_eq_zero_of_lagrangian hdim (blockDiag A (-B)) hbd_eu.radical_eq_bot L rfl hiso
  have hadd := latticeSig_blockDiag A (-B) hA hnegB
  rw [latticeSig_neg] at hadd
  omega

/-! ## §5. The faithfulness converse — a Lagrangian BUILDS the substrate (`ofLagrangian`)

The substrate is **faithful**: it is inhabited for a boundary form `Bd` *exactly when* `Bd` carries a
half-dimensional isotropic subspace (a Lagrangian). §1's `lagrangian` gives the forward direction
(`NovikovRealPairLES Bd → ∃ Lagrangian`); this section gives the converse — from a Lagrangian `L` we
CONSTRUCT a `NovikovRealPairLES Bd` synthetically, with `H³(W,∂W) := (Fin n → ℝ) ⧸ L`, `delta := L.mkQ`,
`rest2 := L.subtype`, and `pairing` the boundary form descended through the quotient. The pair-LES
exactness `im rest2 = ker delta` is then `range L.subtype = ker L.mkQ = L` (definitional), and the
Kronecker nondegeneracy is the co-isotropy `L^⊥ ⊆ L` (from half-dimensionality + nondegeneracy, banked as
`coisotropic_of_isotropic_half_matrix`). This confirms the merge-note's "sound by design — inhabitable only
when the signature agrees" as a THEOREM: the substrate route is *equivalent* to the classical Lagrangian
route, neither weaker nor stronger. -/

/-- **Bilinear isotropy on a Lagrangian.** If the boundary quadratic form vanishes on `L` (a subspace),
its polar form vanishes on `L × L`: `polar Q a w = Q(a+w) − Q a − Q w = 0` for `a, w ∈ L`. -/
theorem polarBilin_vanish_of_mem {n : ℕ} {Bd : Matrix (Fin n) (Fin n) ℤ}
    {L : Submodule ℝ (Fin n → ℝ)}
    (hiso : ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0)
    {a w : Fin n → ℝ} (ha : a ∈ L) (hw : w ∈ L) :
    (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap') a w = 0 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [hiso _ (L.add_mem ha hw), hiso _ ha, hiso _ hw]; ring

/-- **The descended boundary pairing.** For a Lagrangian `L` the boundary polar form `B := polarBilin Q`
descends to a genuine bilinear pairing `L × ((Fin n → ℝ) ⧸ L) → ℝ`, `⟨a, mkQ v⟩ := B a v`. Well-defined:
for `a ∈ L`, `B a` vanishes on `L` (`polarBilin_vanish_of_mem`), so it factors through the quotient. This is
the `pairing` field the substrate consumes; linearity in the `L`-slot is proven representative-wise (no
`liftQ_add`; the descent is assembled by hand). -/
noncomputable def lagrangianPairing {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℤ)
    (L : Submodule ℝ (Fin n → ℝ))
    (hiso : ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0) :
    L →ₗ[ℝ] ((Fin n → ℝ) ⧸ L) →ₗ[ℝ] ℝ where
  toFun a := Submodule.liftQ L
    (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' (a : Fin n → ℝ))
    (by intro w hw; simp only [LinearMap.mem_ker]
        exact polarBilin_vanish_of_mem hiso a.2 hw)
  map_add' a b := by
    apply LinearMap.ext; intro v
    induction v using Submodule.Quotient.induction_on with
    | H w => simp [Submodule.liftQ_apply, Submodule.coe_add, map_add]
  map_smul' c a := by
    apply LinearMap.ext; intro v
    induction v using Submodule.Quotient.induction_on with
    | H w => simp [Submodule.liftQ_apply, map_smul]

/-- **The faithfulness converse: a Lagrangian builds the substrate.** From a half-dimensional isotropic
subspace `L` of a nondegenerate boundary form `Bd`, construct `NovikovRealPairLES Bd`:
`H²(W) := L`, `H³(W,∂W) := (Fin n → ℝ) ⧸ L`, `rest2 := L.subtype`, `delta := L.mkQ`, `pairing` the descended
polar form. Pair-LES exactness is `range subtype = ker mkQ = L`; Kronecker nondegeneracy is the co-isotropy
`L^⊥ ⊆ L` (from half-dimensionality via `coisotropic_of_isotropic_half_matrix`); the PD-intertwining is the
defining equation of `pairing`. -/
noncomputable def NovikovRealPairLES.ofLagrangian {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℤ)
    (hbdnd : (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (L : Submodule ℝ (Fin n → ℝ))
    (hhalf : n = 2 * Module.finrank ℝ L)
    (hiso : ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0) :
    NovikovRealPairLES Bd where
  H2W := L
  H3rel := (Fin n → ℝ) ⧸ L
  rest2 := L.subtype
  delta := L.mkQ
  pairing := lagrangianPairing Bd L hiso
  hexact := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  hadj := by
    intro a v
    simp only [lagrangianPairing, LinearMap.coe_mk, AddHom.coe_mk, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  hnondeg := by
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      have hco := PinPlusKTSpinSigmaNovikovHalfDim.coisotropic_of_isotropic_half_matrix Bd hbdnd L hiso hhalf
      have hvperp : v ∈ LinearMap.BilinForm.orthogonal
          (QuadraticMap.polarBilin (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap') L := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro a ha
        rw [LinearMap.BilinForm.isOrtho_def]
        have := hx ⟨a, ha⟩
        simpa [lagrangianPairing, Submodule.liftQ_apply] using this
      rw [Submodule.Quotient.mk_eq_zero]
      exact hco hvperp
  hbdnd := hbdnd

/-- **Faithfulness (form level): the substrate is inhabited iff a Lagrangian exists.** For a nondegenerate
boundary form `Bd` (`radical = ⊥`, banked from even-unimodularity), `NovikovRealPairLES Bd` is inhabited
*exactly when* `Bd` carries a half-dimensional isotropic subspace. Forward: `d.lagrangian`; backward:
`ofLagrangian`. So the pair-LES/Kronecker/adjunction substrate encodes neither more nor less than the
classical Lagrangian — the merge-note's "sound by design, inhabitable only when the signature agrees" made a
theorem. -/
theorem NovikovRealPairLES.nonempty_iff_exists_lagrangian {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℤ)
    (hbdnd : (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥) :
    Nonempty (NovikovRealPairLES Bd) ↔
      ∃ L : Submodule ℝ (Fin n → ℝ),
        n = 2 * Module.finrank ℝ L ∧
        ∀ x ∈ L, (Bd.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0 :=
  ⟨fun ⟨d⟩ => d.lagrangian,
   fun ⟨L, hhalf, hiso⟩ => ⟨NovikovRealPairLES.ofLagrangian Bd hbdnd L hhalf hiso⟩⟩

/-! ## §6. The σ-descent atom (Prop form) — EQUIVALENT to the classical Lagrangian atom -/

/-- **The per-pair real pair-LES atom (Prop form).** For every data-bordant pair `p, q`, the boundary block
form `blockDiag (II M_p) (−II M_q)` carries a `NovikovRealPairLES`. This is the `Nonempty`-valued twin of the
data hypothesis of `novikovHalfDim_of_realPairLES`, a genuine `Prop` fit for the atom equivalence. -/
def NovikovRealPairLESAtom (prov : CharPairWProviderPerOp (𝓡 4) k) (a : SpinSigmaAtoms prov) : Prop :=
  ∀ p q : StrMfd (spinEmptyData prov), IsDataBordant (spinEmptyData prov) p q →
    Nonempty (NovikovRealPairLES
      (blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q))))

/-- **`NovikovHalfDimAtom` from the real pair-LES atom.** Each per-pair substrate yields a
`NovikovBoundaryRestriction` via `toBoundaryRestriction`; so the substrate atom discharges the σ-descent's
residual half-dim atom (the `Nonempty`-driven form of `novikovHalfDim_of_realPairLES`). -/
theorem novikovHalfDim_of_novikovRealPairLESAtom {a : SpinSigmaAtoms prov}
    (h : NovikovRealPairLESAtom prov a) : NovikovHalfDimAtom prov a :=
  fun p q hb => ⟨(h p q hb).some.toBoundaryRestriction⟩

/-- **The real pair-LES atom from the classical Lagrangian atom.** Given, per data-bordant pair, a
half-dimensional isotropic Lagrangian `L`, the boundary block form is even-unimodular (from `wu`/`pd`), hence
nondegenerate, so `ofLagrangian` builds the substrate. This is the converse that makes the substrate atom
EQUIVALENT to `NovikovLagrangianAtom`, not a strictly stronger demand. -/
theorem novikovRealPairLESAtom_of_novikovLagrangian {a : SpinSigmaAtoms prov}
    (h : NovikovLagrangianAtom prov a) : NovikovRealPairLESAtom prov a := by
  intro p q hb
  obtain ⟨L, hdim, hiso⟩ := h p q hb
  have heuP := isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p)
  have heuQ := isEvenUnimodular_of_intPD (a.fc q) (a.B q) (a.wu q) (a.pd q)
  have hbd_eu := isEvenUnimodular_blockDiag (interMatrix (a.fc p) (a.B p))
    (-interMatrix (a.fc q) (a.B q)) heuP (isEvenUnimodular_neg _ heuQ)
  exact ⟨NovikovRealPairLES.ofLagrangian _ hbd_eu.radical_eq_bot L hdim hiso⟩

/-- **`NovikovRealPairLESAtom ↔ NovikovLagrangianAtom`** — the substrate atom is a faithful re-expression of
the classical Novikov Lagrangian atom. Forward: through `novikovHalfDim_of_novikovRealPairLESAtom` +
`novikovLagrangian_of_novikovHalfDim`; backward: `novikovRealPairLESAtom_of_novikovLagrangian`. With the
half-dim/co-isotropy equivalences already banked, all four formulations of the σ-descent's last geometric
atom (Lagrangian, half-dim boundary restriction, Lefschetz co-isotropy, real pair-LES substrate) are
kernel-provably interchangeable: discharging ANY one makes the σ-descent unconditional. -/
theorem novikovRealPairLESAtom_iff_novikovLagrangian {a : SpinSigmaAtoms prov} :
    NovikovRealPairLESAtom prov a ↔ NovikovLagrangianAtom prov a :=
  ⟨fun h => novikovLagrangian_of_novikovHalfDim (novikovHalfDim_of_novikovRealPairLESAtom h),
   novikovRealPairLESAtom_of_novikovLagrangian⟩

/-! ## §7. The σ-descent payload — `hbord` and the canonical Thom hom from the real pair-LES atom -/

/-- **`hbord` (lattice-signature bordism invariance) from the real pair-LES atom.** With
`novikovRealPairLESAtom_iff_novikovLagrangian` feeding `hbord_of_novikovLagrangian`: for data-bordant
`p, q`, `σ(II M_p) = σ(II M_q)`. So supplying the real pair-LES substrate per pair (equivalently, the
classical Lagrangian) discharges the σ-descent's single geometric atom. -/
theorem hbord_of_novikovRealPairLESAtom (a : SpinSigmaAtoms prov)
    (h : NovikovRealPairLESAtom prov a) :
    ∀ p q, IsDataBordant (spinEmptyData prov) p q →
      latticeSig (interMatrix (a.fc p) (a.B p)) = latticeSig (interMatrix (a.fc q) (a.B q)) :=
  hbord_of_novikovLagrangian a (novikovRealPairLESAtom_iff_novikovLagrangian.mp h)

/-- **The canonical bundle's Thom signature hom from the real pair-LES atom.** With `hbord` discharged from
`NovikovRealPairLESAtom`, the bordism-invariant signature `Ω → ℤ` is built with the deep bordism-invariance
supplied by the substrate atom. -/
noncomputable def sigThomNovikovRealPairLESCanonical (c : CanonicalSpinSigmaAtoms prov)
    (h : NovikovRealPairLESAtom prov c.toSpinSigmaAtoms) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  c.sigThom (hbord_of_novikovRealPairLESAtom c.toSpinSigmaAtoms h)

/-- **The disclosed `sig` field collapses onto the real pair-LES atom on the canonical bundle.** Both
`c.sig` and `sigThomNovikovRealPairLESCanonical c h` are `AddMonoidHom`s on `DataBordismGrp` agreeing on
every generator, hence equal. So on the canonical construction the whole σ-presentation reduces to the real
pair-LES substrate atom — which, by §6, is exactly the classical Novikov Lagrangian: the σ-descent completes
modulo the (architecturally still-open) geometric relative-cohomology tower, phrased in substrate terms. -/
theorem sig_eq_sigThomNovikovRealPairLESCanonical (c : CanonicalSpinSigmaAtoms prov)
    (h : NovikovRealPairLESAtom prov c.toSpinSigmaAtoms) :
    c.toSpinSigmaAtoms.sig = sigThomNovikovRealPairLESCanonical c h :=
  c.sig_eq_sigThom (hbord_of_novikovRealPairLESAtom c.toSpinSigmaAtoms h)

end SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
