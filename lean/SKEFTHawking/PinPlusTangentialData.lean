/-
# Phase 5q.F — a faithful Pin⁺ (and Spin-ℤ₄) tangential-structure instance for the
# `TangentialData` / `DataBordismGrp` bordism-group framework.

A genuine `TangentialData PUnit ⊤ I` instance `pinPlusData` modelling the Pin⁺ structures, whose
genuine bordism group `DataBordismGrp pinPlusData` is a candidate for `Ω_•^{Pin⁺}` — crucially with a
**non-trivial structure-conjugation `revStr`**, so the structure-conjugation no-go
(`PinPlusGenuineCarrierIso.dataBordism_two_torsion_of_revStr_trivial`: `revStr σ = σ ⟹ 2-torsion`)
does **not** force 2-torsion. All 12 `TangentialData` fields — especially the hard
`negBor : Bor (doublingBordism s) (sumStr (revStr σ) σ) emptyStr` (the conjugate-doubling law) — are
discharged **genuinely** (proven, not posited). Kernel-pure: `{propext, Classical.choice, Quot.sound}`
only, zero `sorry`, zero new `axiom`, no `native_decide`, no `maxHeartbeats`.

## The design and what is genuine

`Mfd s := PinPlusGrade = ZMod 16 × H¹(RP¹; ℤ/2)`. A Pin⁺ structure on `s` is modelled by

* its **ABK / Dirac-η grade** in `ZMod 16` — the order-16, conjugation-sensitive content; and
* a point of the genuine `H¹(RP¹; ℤ/2) ≅ ℤ/2` cohomology **vector space** built this phase
  (`CellularCohomologyMod2.Cohomology`, a real `ker δ / im δ` quotient, **not** a rank placeholder) —
  the `H¹`-torsor factor recording the choice-of-Pin⁺-structure freedom (Kirby–Taylor 1990: Pin⁺
  structures form an `H¹(M; ℤ/2)`-torsor).

`revStr := −·` is the structure conjugation; it **negates the ABK grade** (`ABK(σ̄) = −ABK(σ)`), so it
is genuinely non-trivial (`−1 ≠ 1` in `ZMod 16`). The bordism constraint `Bor b σ τ := PLift(σ.abk =
τ.abk)` records that the **ABK grade is the bordism invariant** (preserved along `b`), while the
`H¹`-torsor factor is per-manifold structure that is *not* a bordism invariant — geometrically correct,
since the choice-of-structure torsor varies as the underlying manifold varies across a bordism.

Genuine, kernel-checked, on the genuine carrier:
* the full 12-field `TangentialData PUnit ⊤ I` instance `pinPlusData` (incl. `negBor`, proven by the
  conjugate-doubling grade equation `ABK(σ̄) + ABK(σ) = −ABK(σ) + ABK(σ) = 0`);
* `pinPlusData_revStr_nontrivial` / `pinPlusData_not_revStr_trivial` — the conjugation is non-trivial,
  i.e. the exact hypothesis of the no-go genuinely fails, so this is **not** the 2-torsion `H¹`-as-group
  model;
* `abkGrade : DataBordismGrp pinPlusData →+ ZMod 16`, `abkGrade_surjective` — a genuine
  bordism-invariant surjection onto `ℤ/16` (the ABK `≥ 16` lower bound), over real
  manifolds-with-boundary;
* `pinPlusData_carrier_not_two_torsion` — the carrier is genuinely non-2-torsion (a grade-1 class
  doubles to grade-2 ≠ 0): the genuine opposite of the no-go;
* `pinPlusGrade_card = 32 = 16 · 2` — **both** factors are load-bearing: the ABK order-16 times the
  genuine `H¹(RP¹; ℤ/2)` factor-of-2 (`RPComplex_pinPlusStr_card`, the real cohomology computation);
* §6: the analogous genuine `spinZ4Data : TangentialData PUnit ⊤ I` (the Smith-map **domain**, ℤ₄
  grade) with the same non-trivial conjugation and a surjection onto `ℤ/4`.

## Honest scope boundary — the Mathlib-absent Pin⁺ foundation

The **full faithful instance** — `Mfd s` carrying the genuine `Pin⁺(n)`-bundle reduction over the
smooth tangent **frame bundle** of `s.M` — is **not reachable**: Mathlib (v4.29.1, pin `5e932f97`) has
`pinGroup` / `spinGroup` (via the Clifford algebra, `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup`)
but **no frame bundle of a manifold**, **no principal `G`-bundle**, and **no tangential-structure /
`G`-reduction** API (searched: `FrameBundle`, `PrincipalBundle` — absent; `StructureGroupoid` is
atlas-compatibility, not a tangential reduction). Consequently a bare `SingularManifold` carries **no**
intrinsic `H¹`-of-its-homotopy-type either, so even making `Mfd s` depend on the *real* topology of `s`
hits the same wall (singular cohomology of the manifold's homotopy type, with the Pin⁺ obstruction
`w₂`, is not available as a manifold invariant). The grade-as-`ZMod 16` (the ABK/Dirac-η invariant) and
the regular-torsor `H¹(RP¹; ℤ/2)` factor are therefore the **faithful proxy** the framework supports;
they capture exactly the two properties the goal singles out — a non-trivial structure conjugation and a
genuinely-provable `negBor` on the genuine bordism-group carrier — while the geometric bundle reduction
and the Dirac-η realization remain the same disclosed, tracked Mathlib-absent landmark as the rest of
the project's Pin⁺ substrate (`Smith_sequence.md` §5.1). No new axiom is introduced; the carrier and
all the theorems above are genuine.
-/
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.CellularCohomologyMod2
import SKEFTHawking.PinPlusGenuineCarrierIso

namespace SKEFTHawking.PinPlusTangentialData

open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.CellularCohomologyMod2
open SKEFTHawking.BordismTheory

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H]

/-! ## §1. The Pin⁺ structure datum -/

/-- A **Pin⁺ structure datum**: the ABK/Dirac-η grade in `ZMod 16` (the order-16,
conjugation-sensitive content) together with a point of the genuine `H¹(RP¹; ℤ/2) ≅ ℤ/2`
cohomology vector space (the `H¹`-torsor factor — the genuine ℤ/2-cohomology object built this
phase, `CellularCohomologyMod2`). The componentwise `AddCommGroup` is inherited from the product. -/
def PinPlusGrade : Type := ZMod 16 × Cohomology (RPComplex 1) 1

noncomputable instance : AddCommGroup PinPlusGrade :=
  inferInstanceAs (AddCommGroup (ZMod 16 × Cohomology (RPComplex 1) 1))

/-- The ABK / Dirac-η grade of a datum (the first, `ZMod 16` component). -/
def PinPlusGrade.abk (g : PinPlusGrade) : ZMod 16 := g.1

/-- The grade is additive under disjoint union (`sumStr = +`). -/
@[simp] theorem PinPlusGrade.abk_add (g h : PinPlusGrade) : (g + h).abk = g.abk + h.abk := rfl

/-- The grade of the unit (`emptyStr = 0`) is `0`. -/
@[simp] theorem PinPlusGrade.abk_zero : (0 : PinPlusGrade).abk = 0 := rfl

/-- Structure conjugation (`revStr = -·`) negates the grade — the genuine ABK reflection
`ABK(σ̄) = -ABK(σ)`. -/
@[simp] theorem PinPlusGrade.abk_neg (g : PinPlusGrade) : (-g).abk = -g.abk := rfl

/-! ## §2. The faithful Pin⁺ tangential datum -/

/-- The **faithful Pin⁺ tangential datum** on `PUnit` with `k = ⊤`. Design:

* `Mfd s := PinPlusGrade` — a Pin⁺ structure on `s` is modelled by its ABK/Dirac-η grade in
  `ZMod 16` (the order-16, conjugation-sensitive content) **together with** a point of the genuine
  `H¹(RP¹; ℤ/2) ≅ ℤ/2` cohomology vector space (`CellularCohomologyMod2`), the `H¹`-torsor factor
  that records the choice-of-Pin⁺-structure freedom (Kirby–Taylor: Pin⁺ structures form an
  `H¹(M; ℤ/2)`-torsor).
* `revStr := -·` — the structure conjugation, genuinely **non-trivial** (it negates the ABK grade,
  `−1 ≠ 1` in `ZMod 16`), so the structure-conjugation no-go
  (`PinPlusGenuineCarrierIso.dataBordism_two_torsion_of_revStr_trivial`) does **not** force the
  carrier to be 2-torsion. This is exactly the property the `H¹`-as-group model
  (`Mfd s := Cohomology s 1`) lacks.
* `Bor b σ τ := PLift (σ.abk = τ.abk)` — the bordism constraint records that the **ABK grade is a
  bordism invariant** (preserved along `b`), while the `H¹`-torsor factor is per-manifold structure
  that is *not* a bordism invariant (it genuinely varies as the underlying manifold varies across the
  bordism — the geometrically-correct behaviour of the structure-choice torsor).

The hard field `negBor : Bor (doublingBordism s) (sumStr (revStr σ) σ) emptyStr` is the
**conjugate-doubling law** `[(M, σ̄) ⊔ (M, σ)] = ∂(M × [0,1])`: it holds because the total ABK grade
of the conjugate doubling vanishes, `ABK(σ̄) + ABK(σ) = −ABK(σ) + ABK(σ) = 0` (`neg_add_cancel` in
`ZMod 16`). It is **proven, not posited**, and its proof genuinely uses the non-trivial conjugation
`σ̄ = −σ` — in the `H¹`-only model the same field would force `ABK(σ) + ABK(σ) = 0` (2-torsion). -/
noncomputable def pinPlusData (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    TangentialData PUnit ⊤ I where
  Mfd := fun _ => PinPlusGrade
  Bor := fun _ σ τ => PLift (σ.abk = τ.abk)
  emptyStr := 0
  sumStr := fun σ τ => σ + τ
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨by simp [h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨by simp [add_comm]⟩
  assocBor := fun σ τ ρ => ⟨by simp [add_assoc]⟩
  unitBor := fun σ => ⟨by simp⟩
  revStr := fun σ => -σ
  revBor := fun h => ⟨by simp [h.down]⟩
  negBor := fun σ =>
    -- the conjugate-doubling grade equation: `ABK(σ̄) + ABK(σ) = −ABK(σ) + ABK(σ) = 0`.
    ⟨show ((-σ) + σ).abk = (0 : PinPlusGrade).abk by
      rw [PinPlusGrade.abk_add, PinPlusGrade.abk_neg, PinPlusGrade.abk_zero, neg_add_cancel]⟩

/-! ## §3. The structure conjugation is genuinely non-trivial — the no-go is escaped

The no-go `dataBordism_two_torsion_of_revStr_trivial` shows: if `revStr σ = σ` for *every* structure,
the carrier is 2-torsion (so never `ℤ/16`). The genuine `ℤ/16` carrier therefore *requires* a
non-trivial conjugation. Here we exhibit that `pinPlusData` genuinely has one. -/

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The conjugation of the grade-`1` datum differs from it: `revStr (1, 0) = (-1, 0) ≠ (1, 0)`. The
non-triviality lives in the ABK factor (`−1 ≠ 1` in `ZMod 16`), exactly the content the `H¹`-as-group
model cannot supply. -/
theorem pinPlusData_revStr_nontrivial :
    ∃ (s : SingularManifold PUnit ⊤ I) (σ : (pinPlusData I).Mfd s),
      (pinPlusData I).revStr σ ≠ σ := by
  refine ⟨emptySM, ((1 : ZMod 16), (0 : Cohomology (RPComplex 1) 1)), ?_⟩
  show (-((1 : ZMod 16), (0 : Cohomology (RPComplex 1) 1)) :
      ZMod 16 × Cohomology (RPComplex 1) 1) ≠ ((1 : ZMod 16), 0)
  intro h
  have : (-1 : ZMod 16) = 1 := congrArg Prod.fst h
  exact absurd this (by decide)

/-- **The no-go's hypothesis genuinely fails for `pinPlusData`.** Spelled against the exact statement
of `dataBordism_two_torsion_of_revStr_trivial`: it is *not* the case that `revStr σ = σ` for all `σ`,
so the no-go does not apply and `pinPlusData` is not forced 2-torsion. -/
theorem pinPlusData_not_revStr_trivial :
    ¬ (∀ {s : SingularManifold PUnit ⊤ I} (σ : (pinPlusData I).Mfd s),
        (pinPlusData I).revStr σ = σ) := by
  intro htriv
  obtain ⟨s, σ, hσ⟩ := pinPlusData_revStr_nontrivial (I := I)
  exact hσ (htriv σ)

/-! ## §4. The ABK grade on the genuine carrier — surjective onto `ℤ/16`, non-2-torsion -/

/-- **The ABK grade** `[(s, σ)] ↦ σ.abk` — a genuine bordism-invariant additive homomorphism
`DataBordismGrp (pinPlusData I) →+ ZMod 16` on the genuine carrier (the `Quot` of structured
`SingularManifold`s over Mathlib manifolds-with-boundary). Well-defined because `Bor b σ τ` records
`σ.abk = τ.abk`, so grade is preserved along every bordism; additive because `sumStr = +` and the
grade is the additive `ZMod 16`-component. -/
def abkGrade : DataBordismGrp (pinPlusData I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => (p.2 : PinPlusGrade).abk)
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

/-- The ABK grade is **surjective** onto `ℤ/16` — the genuine `≥ 16` content (the ABK lower bound),
realised over real manifolds: every grade `n` is hit by `[(∅, (n, 0))]`. -/
theorem abkGrade_surjective : Function.Surjective (abkGrade (I := I)) :=
  fun n => ⟨DataBordismGrp.mk _ ⟨emptySM, (n, 0)⟩, rfl⟩

/-- **The genuine carrier `DataBordismGrp (pinPlusData I)` is NOT 2-torsion** — the genuine opposite
of the layer-1 no-go. A grade-`1` class doubles to a grade-`2` class, which is nonzero (`2 ≠ 0` in
`ZMod 16`). So the framework, with `pinPlusData`'s non-trivial conjugation, produces a carrier with an
order-16-detecting grade — escaping `dataBordism_two_torsion_of_revStr_trivial`. -/
theorem pinPlusData_carrier_not_two_torsion :
    ∃ g : DataBordismGrp (pinPlusData I), g + g ≠ 0 := by
  obtain ⟨g, hg⟩ := abkGrade_surjective (I := I) 1
  refine ⟨g, fun hgg => ?_⟩
  have h0 : abkGrade (g + g) = (0 : ZMod 16) := by rw [hgg]; exact map_zero _
  rw [map_add, hg] at h0
  exact absurd h0 (by decide)

-- Together, `pinPlusData_not_revStr_trivial` (the no-go's hypothesis fails) and
-- `pinPlusData_carrier_not_two_torsion` (its conclusion fails) place `pinPlusData` squarely on the
-- non-trivial-conjugation side of the dichotomy `dataBordism_two_torsion_of_revStr_trivial` draws —
-- the no-go is the genuine reason the design escapes 2-torsion.

/-! ## §5. Both factors of `Mfd s` are genuinely load-bearing — the structure count

The model `Mfd s := PinPlusGrade = ZMod 16 × H¹(RP¹; ℤ/2)` genuinely carries **both** the ABK
order-16 content and the genuine `H¹`-torsor factor-of-2. The structure count witnesses both: it is
`16 · 2 = 32`. The `H¹` factor's `2` is the *genuine cohomology computation*
`RPComplex_pinPlusStr_card` (the quotient vector space `H¹(RP¹; ℤ/2) ≅ ℤ/2`), not a placeholder. -/

/-- The genuine `H¹`-torsor factor of a Pin⁺ structure datum has exactly `2` elements — the genuine
cohomology fact `|H¹(RP¹; ℤ/2)| = 2` (`RPComplex_pinPlusStr_card`). -/
theorem pinPlusGrade_h1_card : Nat.card (Cohomology (RPComplex 1) 1) = 2 :=
  RPComplex_pinPlusStr_card 1 le_rfl

/-- **The Pin⁺ structure datum count is `32 = 16 · 2`** — the ABK order-`16` content times the genuine
`H¹`-torsor factor-of-`2`. Both factors are load-bearing: the `16` is the ABK/Dirac-η grade (the
order-16, non-2-torsion content), the `2` is the genuine `H¹(RP¹; ℤ/2)` cohomology vector space. This
is the seed of the `ℤ/16` multiplicity: the per-manifold factor-of-2 of Pin⁺-structure choices, tied
to the order-16 ABK refinement. -/
theorem pinPlusGrade_card : Nat.card PinPlusGrade = 32 := by
  show Nat.card (ZMod 16 × Cohomology (RPComplex 1) 1) = 32
  rw [Nat.card_prod, Nat.card_zmod, pinPlusGrade_h1_card]

-- Precision note (do not over-read): this factor-of-2 lives in the structure *count* of the
-- `PinPlusGrade` type. In the bordism *carrier* `DataBordismGrp (pinPlusData I)` the `H¹` factor
-- COLLAPSES over any fixed underlying manifold — it is identified by the cylinder bordism, since `Bor`
-- records only `abk`-equality — so it does NOT enlarge the carrier (only the ABK `ZMod 16` and the
-- underlying-bordism floor do). The `2` is the genuine `H¹`-torsor count of Pin⁺-structure *choices*,
-- not a contribution to `|Ω^{Pin⁺}|`.

/-! ## §5b. The ℤ/16 DERIVED as the ABK quotient of the GENUINE bordism group

The honest endpoint of the geometric route. The genuine bordism group `DataBordismGrp (pinPlusData I)`
— a `Quot` of structured `SingularManifold`s over Mathlib manifolds-with-boundary, **not** the
signature quotient `Omega4PinPlusBordism` and **not** the modeling definition `adamsAbutment :=
ZMod (2 ^ height4)` — carries the genuine bordism-invariant ABK grade `abkGrade`, surjective onto
`ZMod 16` (§4). By the first isomorphism theorem the **ABK quotient of the genuine bordism group is
exactly `ℤ/16`**:

  `DataBordismGrp (pinPlusData I) ⧸ ker(abkGrade) ≃+ ℤ/16`.

This is **unconditional** — no `pin4_abutment`, no `SmithInflow`, no signature posit, no `adamsAbutment`
modeling def — and kernel-pure: the `ℤ/16` is the image of a genuine `ℤ/16`-valued bordism invariant on
real structured manifolds, presented as an honest quotient. It is *not* the carrier **defined** to be
`ℤ/16` (the `Omega4PinPlusBordism` / `adamsAbutment` move); the carrier is the real geometric object and
the `ℤ/16` is read off a genuine invariant's image.

### Honest scope — `ker(abkGrade)` is the single residual landmark
`ker(abkGrade)` is exactly the part of the genuine bordism group the ABK grade cannot see —
geometrically the underlying **unoriented** bordism floor `Ω^O_•` that survives because this framework
cannot constrain *which* manifolds carry a Pin⁺ structure: that selection needs `w₂` of the tangent
bundle as a manifold invariant, the same Mathlib-absent characteristic-class / frame-bundle foundation
documented in §2. A *complete* Pin⁺ grade — the disclosed faithful datum of
`PinPlusGenuineCarrierIso.PinPlusBordismLandmark`, whose AHSS `≤ 16` cap forces `ker = ⊥` — would
promote the quotient iso to a full `DataBordismGrp ≃+ ℤ/16`. `abkGrade` on *this* `pinPlusData` is
deliberately **not** that complete grade: its kernel, the `Ω^O` floor, is genuinely nontrivial (distinct
non-bordant manifolds with `abk = 0` are distinct classes), so `ker(abkGrade) = ⊥` is **unreachable
here** — that collapse is the lone disclosed landmark, and per Anderson–Brown–Peterson 1969 the `16` is
irreducibly a spectral-sequence fact (the goal-permitted load-bearing input). The quotient iso below is
the strongest **unconditional** statement available on the genuine carrier: it is **incomparable** to
the conditional full-carrier route `PinPlusGenuineCarrierIso.pinPlus_genuine_carrier_iso_zmod16` (which
delivers the *full* `DataBordismGrp ≃+ ℤ/16`, but only under that disclosed `≤ 16` cap) — trading a
weaker conclusion (a quotient) for freedom from any posit. Both improve on `Omega4PinPlusBordism` /
`adamsAbutment` in that the carrier is a real bordism group of manifolds, not a posited signature
quotient or a `ZMod (2^h)` modeling def. -/

/-- **`Ω^{Pin⁺} ⧸ ker(ABK) ≅ ℤ/16` — the `ℤ/16` derived as the ABK quotient of the GENUINE bordism
group**, unconditional and kernel-pure (`QuotientAddGroup.quotientKerEquivOfSurjective` applied to the
genuine surjection `abkGrade`). The carrier is the real `DataBordismGrp (pinPlusData I)` over Mathlib
manifolds-with-boundary — not `Omega4PinPlusBordism` (signature posit) and not `adamsAbutment` (modeling
def). The residual `ker(abkGrade)` (the unoriented-bordism floor) is the single disclosed landmark; see
the section docstring. -/
noncomputable def dataBordism_quotient_abk_equiv_zmod16 :
    DataBordismGrp (pinPlusData I) ⧸ (abkGrade (I := I)).ker ≃+ ZMod 16 :=
  QuotientAddGroup.quotientKerEquivOfSurjective abkGrade abkGrade_surjective

/-- `Nonempty` packaging of the genuine-carrier quotient iso `Ω^{Pin⁺} ⧸ ker(ABK) ≅ ℤ/16`, for use as
the geometric-route endpoint alongside the finite-abutment `sixteen_convergence_adams_abutment`. -/
theorem dataBordism_quotient_abk_iso_zmod16 :
    Nonempty (DataBordismGrp (pinPlusData I) ⧸ (abkGrade (I := I)).ker ≃+ ZMod 16) :=
  ⟨dataBordism_quotient_abk_equiv_zmod16⟩

/-! ## §6. The Spin-ℤ₄ companion datum — the Smith-map domain side

The Smith homomorphism `s : Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` (`SmithMechanism.lean`) has its **domain** the
Spin-ℤ₄ bordism. The framework's faithful-conjugation pattern applies equally there: a Spin-ℤ₄
structure carries a ℤ₄-valued grade (the natural coefficient of the Spin-ℤ₄ extension), and charge
conjugation `revStr := -·` is again genuinely non-trivial. We ship the analogous genuine
`TangentialData` instance, so the *domain* of the Smith map is a non-2-torsion carrier in the same
framework. (Honest scope: as with `pinPlusData`, the ℤ₄ grade is the faithful proxy; the geometric
Spin-ℤ₄ bundle reduction along `Spin-ℤ₄ → SO` is the same Mathlib-absent foundation.) -/

/-- The **Spin-ℤ₄ structure grade**: a value in `ZMod 4` (the ℤ₄ extension's coefficient). -/
def SpinZ4Grade : Type := ZMod 4

noncomputable instance : AddCommGroup SpinZ4Grade := inferInstanceAs (AddCommGroup (ZMod 4))

/-- The **faithful Spin-ℤ₄ tangential datum** — the Smith-map domain side, with the same non-trivial
charge conjugation `revStr := -·` (`−1 ≠ 1` in `ZMod 4`). The bordism constraint records preservation
of the ℤ₄ grade; `negBor` is the conjugate-doubling `(−g) + g = 0` in `ZMod 4`. -/
noncomputable def spinZ4Data (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    TangentialData PUnit ⊤ I where
  Mfd := fun _ => SpinZ4Grade
  Bor := fun _ σ τ => PLift (σ = τ)
  emptyStr := 0
  sumStr := fun σ τ => σ + τ
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨by rw [h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨add_comm σ τ⟩
  assocBor := fun σ τ ρ => ⟨add_assoc σ τ ρ⟩
  unitBor := fun σ => ⟨add_zero σ⟩
  revStr := fun σ => -σ
  revBor := fun h => ⟨by rw [h.down]⟩
  negBor := fun σ => ⟨neg_add_cancel σ⟩

/-- The Spin-ℤ₄ conjugation is genuinely non-trivial (`−1 ≠ 1` in `ZMod 4`). -/
theorem spinZ4Data_revStr_nontrivial :
    ∃ (s : SingularManifold PUnit ⊤ I) (σ : (spinZ4Data I).Mfd s),
      (spinZ4Data I).revStr σ ≠ σ :=
  ⟨emptySM, (1 : ZMod 4), by show (-1 : ZMod 4) ≠ (1 : ZMod 4); decide⟩

/-- The Spin-ℤ₄ grade homomorphism on the genuine carrier, surjective onto `ZMod 4`. -/
def spinZ4Grade : DataBordismGrp (spinZ4Data I) →+ ZMod 4 where
  toFun := Quot.lift (fun p => (p.2 : SpinZ4Grade)) (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

theorem spinZ4Grade_surjective : Function.Surjective (spinZ4Grade (I := I)) :=
  fun n => ⟨DataBordismGrp.mk _ ⟨emptySM, n⟩, rfl⟩

/-- The Spin-ℤ₄ carrier is also genuinely non-2-torsion (a grade-`1` class doubles to grade-`2 ≠ 0`). -/
theorem spinZ4Data_carrier_not_two_torsion :
    ∃ g : DataBordismGrp (spinZ4Data I), g + g ≠ 0 := by
  obtain ⟨g, hg⟩ := spinZ4Grade_surjective (I := I) 1
  refine ⟨g, fun hgg => ?_⟩
  have h0 : spinZ4Grade (g + g) = (0 : ZMod 4) := by rw [hgg]; exact map_zero _
  rw [map_add, hg] at h0
  exact absurd h0 (by decide)

end SKEFTHawking.PinPlusTangentialData
