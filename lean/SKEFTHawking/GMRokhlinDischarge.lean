import SKEFTHawking.SpinRokhlinInterface
import SKEFTHawking.GuillouMarinBridge
import SKEFTHawking.GMArfVanishing

/-!
# Discharging the smooth-Rokhlin `2 ∣ σ/8` node via the Guillou–Marin / Freedman–Kirby congruence

Phase 5q.H — H8 route (b) foundation (roadmap §9.3; blueprint
`Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md`).

`SpinRokhlinInterface.SmoothSpinManifold4` carries the single irreducibly-topological hypothesis
`topo : 2 ∣ latticeSig form / 8` (the "extra factor of two" the lattice cannot see — E₈ has `σ/8 = 1`).
The elementary (Freedman–Kirby / Matsumoto) proof pins that factor to a GEOMETRIC invariant: the
**Guillou–Marin congruence** `σ(M) − F·F ≡ 2·β(F) (mod 16)` for a characteristic surface `F`, already
formalized in-tree as `GuillouMarin.GMrelation` (with the `RP⁴` witness `GM_rp4`).

This module connects that congruence to the Rokhlin `topo` discharge. In the **spin** case the canonical
characteristic surface is null — `F·F = 0` and its enhancement is trivial (`β(F) = 0`) — so the GM
congruence collapses to `σ ≡ 0 (mod 16)`, i.e. `16 ∣ σ`, i.e. `topo` (blueprint node **[SPIN]**). The
remaining content is the GM congruence itself (the smooth **[FK]** theorem: nodes [G1]/[G2]/[Q1] build the
surface `F` and its enhancement `Q`); this reduces the opaque `topo` posit to that one named,
literature-grounded geometric input, with the `ZMod 16 → divisibility` algebra ([Q2]/[SPIN]) discharged here
kernel-pure.
-/

namespace SKEFTHawking.GMRokhlin

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin

/-- **The 8→16 arithmetic bit.** If `16 ∣ n` then `2 ∣ n / 8` (integer division is exact here since
`8 ∣ 16 ∣ n`). This is the `σ/8`-evenness the topological factor asserts. -/
theorem two_dvd_div_eight_of_sixteen_dvd {n : ℤ} (h : 16 ∣ n) : (2 : ℤ) ∣ n / 8 := by
  obtain ⟨m, rfl⟩ := h
  rw [show (16 : ℤ) * m = 8 * (2 * m) by ring, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
  exact ⟨m, by ring⟩

/-- **The Guillou–Marin congruence with a null (spin) characteristic surface ⟹ `16 ∣ σ`.** Blueprint
node **[SPIN]**: for `F·F = 0` and vanishing Brown invariant `β(F) = 0`, the GM congruence
`σ − F·F ≡ 2·β(F) (mod 16)` collapses to `σ ≡ 0 (mod 16)`. Kernel-pure; the geometric content is entirely
in the hypothesis `hgm` (the [FK] congruence). -/
theorem sixteen_dvd_sig_of_gm_null {σ F_F : ℤ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Z4Quadratic ι} (hgm : GMrelation σ F_F Q) (hF : F_F = 0) (hQ : Q.brown = 0) :
    (16 : ℤ) ∣ σ := by
  have hz : (σ : ZMod 16) = 0 := by
    have h : ((σ - F_F : ℤ) : ZMod 16) = doubleBrown Q := hgm
    rw [hF, doubleBrown, hQ] at h
    simpa using h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd σ 16).mp hz

/-- **The Rokhlin `topo` factor discharged FROM the GM congruence (spin case).** Given the Guillou–Marin
congruence for a smooth spin 4-manifold `M` with a null characteristic surface (`F·F = 0`, `β(F) = 0`),
the topological factor `2 ∣ σ/8` — the single remaining tracked hypothesis of `SmoothSpinManifold4` — is a
theorem. This is the [FK]+[SPIN] → `topo` bridge: it reduces the opaque divisibility posit to the named,
in-tree, `RP⁴`-witnessed GM congruence (`GuillouMarin.GMrelation`), the sanctioned §9.3 H8-route-(b) input. -/
theorem topo_of_gm_null (M : SmoothSpinManifold4) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Z4Quadratic ι} (hgm : GMrelation M.sig 0 Q) (hQ : Q.brown = 0) :
    (2 : ℤ) ∣ latticeSig M.form / 8 :=
  two_dvd_div_eight_of_sixteen_dvd (sixteen_dvd_sig_of_gm_null hgm rfl hQ)

/-- **A smooth spin 4-manifold presented by its Guillou–Marin characteristic-surface datum** — the
literature-grounded form of `SmoothSpinManifold4` in which the topological factor is NOT an opaque posit but
the named GM congruence for the manifold's (spin ⟹ null) characteristic surface. The remaining geometric
content is entirely the field `gm` (the [FK] congruence, blueprint nodes [G1]/[G2]/[Q1]); every other field
is the even-unimodular lattice data the algebra already consumes. -/
structure SpinCharSurfaceData where
  /-- rank of `H²(M; ℤ)`. -/
  rank : ℕ
  /-- the intersection form on `H²(M; ℤ)`. -/
  form : Matrix (Fin rank) (Fin rank) ℤ
  /-- spin ⟹ even unimodular. -/
  even_unimod : IsEvenUnimodular form
  /-- index type of `H₁` of the characteristic surface. -/
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  /-- the `ℤ/4`-quadratic enhancement `q̂_F` of the characteristic surface `F`. -/
  Q : Z4Quadratic ι
  /-- self-intersection `F·F`. -/
  FdotF : ℤ
  /-- the **Guillou–Marin / Freedman–Kirby congruence** `σ − F·F ≡ 2·β(F) (mod 16)` for the manifold's
      characteristic surface (the single smooth input; witnessed on `RP⁴` by `GM_rp4`). -/
  gm : GMrelation (latticeSig form) FdotF Q
  /-- spin ⟹ the canonical characteristic surface is null: `F·F = 0`. -/
  spin_FdotF : FdotF = 0
  /-- spin ⟹ the characteristic-surface Brown invariant vanishes: `β(F) = 0`. -/
  spin_brown : Q.brown = 0

attribute [instance] SpinCharSurfaceData.fι SpinCharSurfaceData.dι

/-- **The GM datum yields a genuine `SmoothSpinManifold4` with `topo` DERIVED, not posited.** So `16 ∣ σ`
(`SmoothSpinManifold4.rokhlin`) on this manifold traces to the named GM congruence, closing the H8 foundation
layer: the manifold now enters Rokhlin's theorem through the sanctioned §9.3 route-(b) input rather than an
opaque divisibility. -/
def SpinCharSurfaceData.toSmoothSpinManifold4 (D : SpinCharSurfaceData) : SmoothSpinManifold4 where
  rank := D.rank
  form := D.form
  even_unimod := D.even_unimod
  topo := two_dvd_div_eight_of_sixteen_dvd
    (sixteen_dvd_sig_of_gm_null D.gm D.spin_FdotF D.spin_brown)

/-- **Rokhlin `16 ∣ σ` for a GM-datum-presented spin 4-manifold**, grounded in the FK congruence. -/
theorem SpinCharSurfaceData.rokhlin (D : SpinCharSurfaceData) : 16 ∣ latticeSig D.form :=
  D.toSmoothSpinManifold4.rokhlin

/-! ## The mod-16 characteristic-square refinement (integrating `AlgebraicRokhlin`)

`AlgebraicRokhlin` carries the mod-8 van der Blij identity `CharacteristicSquareModEight M σ`
(`selfPairing M c ≡ σ mod 8` for characteristic `c`) — the algebraic base [L1]. The Guillou–Marin /
Freedman–Kirby congruence refines it one level: it pins `σ − c²` mod 16 to the GEOMETRIC Brown invariant of
the surface representing `c`, with `c² = selfPairing M c = F·F`. This grounds the GM datum's `F·F` in the
actual intersection lattice's characteristic-vector structure (not a free field). -/

/-- **The mod-16 characteristic-square refinement** — the GM/Freedman–Kirby upgrade of
`CharacteristicSquareModEight`. For a characteristic vector `c` (with `c² = selfPairing M c = F·F`)
represented by a surface with `ℤ/4`-quadratic enhancement `Q`: `(c² : ZMod 16) = σ − 2·β(Q)`, i.e. the GM
congruence `σ − F·F ≡ 2·β(Q) (mod 16)`. The content beyond the mod-8 identity is the geometric Brown
invariant `β(Q)` (not lattice-computable — `RokhlinArfNoGo`). -/
def CharacteristicSquareModSixteen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι) (c : Fin n → ℤ) : Prop :=
  ((selfPairing M c : ℤ) : ZMod 16) = (σ : ZMod 16) - doubleBrown Q

/-- **The mod-16 refinement ⟹ Rokhlin, spin case** — the `serre_even_unimodular_mod8` analog one level up.
At the spin datum (the zero characteristic vector `0`, which `zero_is_characteristic_of_even` gives for an
even form, and `β(Q) = 0`), the mod-16 characteristic-square identity forces `16 ∣ σ`. The algebraic
skeleton of Rokhlin's theorem in the project's characteristic-vector idiom; the geometric input is isolated
entirely in `h16`. -/
theorem sixteen_dvd_of_charSq16_spin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Z4Quadratic ι}
    (h16 : CharacteristicSquareModSixteen M σ Q (fun _ => 0)) (hQ : Q.brown = 0) :
    16 ∣ σ := by
  have hsp : selfPairing M (fun _ => 0) = 0 := by simp [selfPairing]
  rw [CharacteristicSquareModSixteen, hsp, doubleBrown, hQ] at h16
  have hz : (σ : ZMod 16) = 0 := by
    have := h16.symm
    simpa using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd σ 16).mp hz

/-! ## Bordism-additivity of the GM invariant + the two-idiom bridge

The Guillou–Marin invariant `2·β(Q)` is additive under disjoint union of characteristic surfaces
(`Z4Quadratic.orthSum`), so the GM congruence `σ − F·F ≡ 2·β mod 16` is compatible with the additive
structure of `DataBordismGrp` — the first algebraic step of the eventual bordism-invariance proof of the
[FK] congruence (both sides additive; agree on generators via `GM_rp4`). And the two idioms
(`GMrelation` / `CharacteristicSquareModSixteen`) coincide once `F·F = selfPairing M c`. -/

/-- **`doubleBrown` is additive under `orthSum`** — `2·β` of a disjoint union splits, since `β` is additive
(`brown_orthSum`) and the doubling `ZMod 8 → ZMod 16` (`x ↦ 2·x.val`) is a group hom. Kernel-pure (the
doubling additivity is `decide` over the 64 `ZMod 8 × ZMod 8` cases). -/
lemma doubleBrown_orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    doubleBrown (Z4Quadratic.orthSum Q₁ Q₂) = doubleBrown Q₁ + doubleBrown Q₂ := by
  unfold doubleBrown
  rw [Z4Quadratic.brown_orthSum]
  have key : ∀ a b : ZMod 8,
      (2 * ((a + b).val : ZMod 16)) = 2 * (a.val : ZMod 16) + 2 * (b.val : ZMod 16) := by decide
  exact key Q₁.brown Q₂.brown

/-- **The GM congruence is additive under disjoint union of characteristic surfaces.** If `(M₁, F₁)` and
`(M₂, F₂)` satisfy Guillou–Marin, so does `(M₁ ⊔ M₂, F₁ ⊔ F₂)` with `σ`, `F·F` and `β` all adding. This is
bordism-additivity of the FK invariant — the algebraic engine for proving `[FK]` by bordism-invariance. -/
theorem gmrelation_orthSum {σ₁ F₁ σ₂ F₂ : ℤ} {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {Q₁ : Z4Quadratic ι₁} {Q₂ : Z4Quadratic ι₂}
    (h₁ : GMrelation σ₁ F₁ Q₁) (h₂ : GMrelation σ₂ F₂ Q₂) :
    GMrelation (σ₁ + σ₂) (F₁ + F₂) (Z4Quadratic.orthSum Q₁ Q₂) := by
  have h : ((σ₁ + σ₂ - (F₁ + F₂) : ℤ) : ZMod 16) = doubleBrown Q₁ + doubleBrown Q₂ := by
    have e₁ : ((σ₁ - F₁ : ℤ) : ZMod 16) = doubleBrown Q₁ := h₁
    have e₂ : ((σ₂ - F₂ : ℤ) : ZMod 16) = doubleBrown Q₂ := h₂
    push_cast at e₁ e₂ ⊢
    rw [← e₁, ← e₂]; ring
  show ((σ₁ + σ₂ - (F₁ + F₂) : ℤ) : ZMod 16) = doubleBrown (Z4Quadratic.orthSum Q₁ Q₂)
  rw [doubleBrown_orthSum]; exact h

/-- **The two idioms coincide.** `CharacteristicSquareModSixteen M σ Q c` is exactly the GM congruence
`GMrelation σ (selfPairing M c) Q` (with `F·F = c² = selfPairing M c`) — the char-vector framing and the
`GMrelation` framing are the same statement. -/
theorem charSq16_iff_gmrelation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι) (c : Fin n → ℤ) :
    CharacteristicSquareModSixteen M σ Q c ↔ GMrelation σ (selfPairing M c) Q := by
  unfold CharacteristicSquareModSixteen GMrelation
  rw [Int.cast_sub]
  constructor <;> intro h <;> linear_combination -h

/-- **The GM congruence computes `σ mod 16`** from the intersection data: `σ ≡ c² + 2·β(Q) (mod 16)`. The
general (non-spin) content of Guillou–Marin — the Pin⁺ `ℤ/16` residue read off the characteristic surface. -/
theorem sig_zmod16_of_charSq16 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Z4Quadratic ι} {c : Fin n → ℤ}
    (h : CharacteristicSquareModSixteen M σ Q c) :
    (σ : ZMod 16) = (selfPairing M c : ZMod 16) + doubleBrown Q := by
  rw [CharacteristicSquareModSixteen] at h
  rw [h]; ring

/-! ## A concrete witness — the trivial (S⁴) datum

The reviewer noted the framework carried no concrete inhabitant. Here is one: the empty (rank-0)
intersection form — the 4-sphere `S⁴` — with the empty characteristic surface. It validates that
`SpinCharSurfaceData` is genuinely populatable and that `.toSmoothSpinManifold4`/`.rokhlin` fire on a real
(if trivial, `σ = 0`) instance. -/

/-- **A rank-0 intersection form has signature 0** (from `|σ| ≤ rank = 0`). -/
theorem latticeSig_fin_zero (M : Matrix (Fin 0) (Fin 0) ℤ) : latticeSig M = 0 := by
  have h : |latticeSig M| ≤ 0 := by simpa using abs_latticeSig_le M
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- **The 4-sphere as a `SpinCharSurfaceData`** — the empty even-unimodular form, empty characteristic
surface (`stdQuadratic 0`, `β = 0`), `F·F = 0`; a genuine concrete inhabitant. -/
def sphereS4Data : SpinCharSurfaceData where
  rank := 0
  form := 0
  even_unimod := ⟨Matrix.transpose_zero, Or.inl Matrix.det_fin_zero, fun i => i.elim0⟩
  ι := Fin 0
  Q := stdQuadratic 0
  FdotF := 0
  gm := by
    show ((latticeSig (0 : Matrix (Fin 0) (Fin 0) ℤ) - 0 : ℤ) : ZMod 16)
      = doubleBrown (stdQuadratic 0)
    rw [latticeSig_fin_zero, doubleBrown_stdQuadratic]; decide
  spin_FdotF := rfl
  spin_brown := by rw [brown_stdQuadratic]; decide

/-- The trivial datum's Rokhlin conclusion: `16 ∣ 0` — the framework fires end-to-end. -/
example : (16 : ℤ) ∣ latticeSig sphereS4Data.form := sphereS4Data.rokhlin

/-! ## Consistency: the FK refinement recovers van der Blij on oriented surfaces

The FK congruence must be consistent with the *proven* mod-8 van der Blij bound. For an EVEN (oriented)
characteristic surface — `β ∈ {0,4} ⊂ ZMod 8` (`brown_even_two_torsion`) — the mod-8 reduction of `2·β`
vanishes, so the mod-16 identity descends exactly to `selfPairing ≡ σ (mod 8)`. This confirms
`CharacteristicSquareModSixteen` is the correct one-level-up refinement of `CharacteristicSquareModEight`,
not an inconsistent overreach. -/

/-- The mod-8 reduction of the GM term `2·β(Q)` is `2·β(Q)` in `ZMod 8`. -/
lemma reduce16to8_doubleBrown {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι) :
    reduce16to8 (doubleBrown Q) = 2 * Q.brown := by
  unfold doubleBrown
  rw [map_mul, map_ofNat, map_natCast, ZMod.natCast_val, ZMod.cast_id]

/-- **The FK congruence refines van der Blij on oriented surfaces.** For an even (oriented) characteristic
surface `Q`, the mod-16 identity `CharacteristicSquareModSixteen` reduces exactly to the mod-8 van der Blij
identity `selfPairing M c ≡ σ (mod 8)` — the FK refinement is consistent with the proven algebraic bound. -/
theorem charSq8_of_charSq16_even {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Z4Quadratic ι} {c : Fin n → ℤ}
    (h : CharacteristicSquareModSixteen M σ Q c) (hE : Z4Quadratic.IsEven Q) :
    (selfPairing M c : ZMod 8) = (σ : ZMod 8) := by
  have h' : ((selfPairing M c : ℤ) : ZMod 16) = (σ : ZMod 16) - doubleBrown Q := h
  have hred := congrArg reduce16to8 h'
  rw [map_intCast, map_sub, map_intCast, reduce16to8_doubleBrown, brown_even_two_torsion Q hE,
    sub_zero] at hred
  exact hred

end SKEFTHawking.GMRokhlin
