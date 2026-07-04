import SKEFTHawking.SpinRokhlinInterface
import SKEFTHawking.GuillouMarinBridge

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

open SKEFTHawking.Brown SKEFTHawking.GuillouMarin

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

end SKEFTHawking.GMRokhlin
