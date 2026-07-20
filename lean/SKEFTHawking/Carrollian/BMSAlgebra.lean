import Mathlib
import SKEFTHawking.Carrollian.WittAlgebra

/-!
# Phase 6o′ Wave 1a′ C3 — the BMS₃ semidirect product + supertranslation ideal

The horizon symmetry algebra of the 2+1 acoustic (sonic) horizon per the C0 verdict
(`Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md`) is the
Donnay-et-al./Penna **horizon** algebra `Vect(S¹) ⋉ C∞(S¹)_ab` — the BMS₃-type semidirect product
of the Witt algebra of superrotations (C2, `WittAlgebra.lean`) acting on an abelian sector of
supertranslations. This module builds it as a genuine Lie algebra on the concrete graded model.

## The model

`BMSAlgebra := WittAlgebra × SuperTrans` where `SuperTrans := ℤ →₀ ℝ` is the abelian
supertranslation sector (the algebraic `C∞(S¹)` stand-in, same graded Fourier model as C2). The
bracket is the semidirect product
`⁅(X,α),(Y,β)⁆ = (⁅X,Y⁆_Witt, X·β − Y·α)`
where the **`Vect(S¹)`-action** `superAction` is `Lₘ · Tₙ = (m − n) T_{m+n}` — supertranslations
as weight `−1` densities. This is the honest BMS₃ convention: it is exactly the action for which
the **Jacobi identity closes** (`bmsBracket_leibniz`), whose second (supertranslation) component
reduces to the Witt Leibniz identity applied to the three action cross-terms. The proven
`WittAlgebra` Leibniz/skew machinery is reused throughout (both sectors share the underlying
`ℤ →₀ ℝ`).

## What is proved

* `LieRing`/`LieAlgebra ℝ` instances for `BMSAlgebra` (Jacobi = `bmsBracket_leibniz`).
* Non-vacuity: the computed mixed bracket `bmsL_bmsT : ⁅Lₘ,Tₙ⁆ = (m−n)T_{m+n}` and its
  `norm_num`-backed pin `bmsL_one_bmsT_neg_one : ⁅L₁,T₋₁⁆ = 2 T₀`.
* The **supertranslation ideal** `superTransIdeal` (`= ker` of the projection onto `Vect(S¹)`):
  abelian (`supertrans_abelian`), genuinely nonzero (`superTransIdeal_ne_bot`) and proper
  (`superTransIdeal_ne_top`).
* The **quotient** `bmsQuotSupertransEquivWitt : BMS ⧸ supertranslations ≃ₗ⁅ℝ⁆ Witt` (first
  isomorphism theorem on the surjective projection `bmsProjWitt`) — the BMS₃ short exact sequence
  `0 → C∞(S¹)_ab → BMS₃ → Vect(S¹) → 0`.

## Centerless discipline (C0 verdict)

NO central extension appears in `BMSAlgebra` itself: at the vector-field level the algebra is
CENTERLESS; any central charge is a boundary-condition-dependent property of the C4/C5 *charge*
algebra, to be DERIVED there, never assumed here. (The Virasoro central extension of the Witt
factor lives separately in `VirasoroExtension.lean` as a cohomology object.)

## C4 seam

`superAction` (the `Vect(S¹)`-action) and `bmsInr : SuperTrans →ₗ BMSAlgebra` are exposed for C4:
the supertranslation charge functional `Q_f` (Penna eq 3.3/3.13, `membranePressure κ = κ/8π` from
`Structure.lean`) pairs against the supertranslation sector `bmsInr`. See §9.

## References
- C0 verdict, `Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md`.
- Barnich–Compère, "Classical central extension for asymptotic symmetries…," gr-qc/0610130 (BMS₃).
- Penna, "BMS invariance and the membrane paradigm," arXiv:1508.06577.
-/

noncomputable section

namespace SKEFTHawking.Carrollian

open WittAlgebra (wittBracketAux wittBracket_leibniz wittBracket_self wittBracket_skew L
  wittBracketAux_single wittBracketAux_L single_smul)

/-! ## §1. The supertranslation module -/

/-- The **supertranslation** carrier: finitely-supported functions `ℤ →₀ ℝ`, basis `Tₙ`. -/
def SuperTrans : Type := ℤ →₀ ℝ

namespace SuperTrans

instance : AddCommGroup SuperTrans := inferInstanceAs (AddCommGroup (ℤ →₀ ℝ))
instance : Module ℝ SuperTrans := inferInstanceAs (Module ℝ (ℤ →₀ ℝ))

/-- The basis supertranslation `Tₙ`. -/
def T (n : ℤ) : SuperTrans := Finsupp.single n 1

end SuperTrans

open SuperTrans (T)

/-! ## §2. The Witt action on supertranslations -/

/-- The **Witt action** on supertranslations `Lₘ · Tₙ = (m − n) T_{m+n}` — the same structure
constants as the Witt bracket (supertranslations transform as weight `−1` densities; this is the
convention for which the BMS₃ Jacobi identity holds, verified in `bmsBracket_leibniz`). Reuses the
already-proven bilinear `wittBracketAux` (same underlying `ℤ →₀ ℝ`). -/
def superAction : WittAlgebra →ₗ[ℝ] SuperTrans →ₗ[ℝ] SuperTrans := wittBracketAux

/-- The action on the basis: `Lₘ · Tₙ = (m − n) T_{m+n}`. -/
theorem superAction_L_T (m n : ℤ) :
    superAction (L m) (T n) = ((m : ℝ) - n) • T (m + n) :=
  wittBracketAux_L m n

/-- The Witt bracket typed on `WittAlgebra` (so `map_add`/`map_smul` fire on `.1` projections,
which are `WittAlgebra`-typed). Definitionally the same bilinear map as `wittBracketAux`. -/
def wittMul : WittAlgebra →ₗ[ℝ] WittAlgebra →ₗ[ℝ] WittAlgebra := wittBracketAux

/-- Witt Leibniz identity, `WittAlgebra`-typed (defeq to `wittBracket_leibniz`). -/
theorem wittMul_leibniz (X Y Z : WittAlgebra) :
    wittMul X (wittMul Y Z) = wittMul (wittMul X Y) Z + wittMul Y (wittMul X Z) :=
  wittBracket_leibniz X Y Z

/-- The Witt bracket is alternating, `WittAlgebra`-typed. -/
theorem wittMul_self (X : WittAlgebra) : wittMul X X = 0 := wittBracket_self X

/-- **The action's derivation (Leibniz) property**: `X·(Y·t) = (X·Y)·t + Y·(X·t)`. This is the
crux making the semidirect product a Lie algebra — the action of `Vect(S¹)` on supertranslations
is a Lie-algebra action (defeq to `wittBracket_leibniz`). -/
theorem superAction_leibniz (X Y : WittAlgebra) (t : SuperTrans) :
    superAction X (superAction Y t)
      = superAction (wittMul X Y) t + superAction Y (superAction X t) :=
  wittBracket_leibniz X Y t

/-! ## §3. The BMS algebra carrier -/

/-- The **BMS₃-type algebra** carrier: `WittAlgebra × SuperTrans` (superrotations × supertranslations). -/
def BMSAlgebra : Type := WittAlgebra × SuperTrans

namespace BMSAlgebra

instance : AddCommGroup BMSAlgebra := inferInstanceAs (AddCommGroup (WittAlgebra × SuperTrans))
instance : Module ℝ BMSAlgebra := inferInstanceAs (Module ℝ (WittAlgebra × SuperTrans))

/-! ## §4. The BMS bracket -/

/-- Projection simp lemmas (the BMSAlgebra module ops ARE the product ops, definitionally). -/
@[simp] theorem fst_add (x y : BMSAlgebra) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem snd_add (x y : BMSAlgebra) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem fst_smul (r : ℝ) (x : BMSAlgebra) : (r • x).1 = r • x.1 := rfl
@[simp] theorem snd_smul (r : ℝ) (x : BMSAlgebra) : (r • x).2 = r • x.2 := rfl

/-- The underlying bracket function: `[(X,α),(Y,β)] = ([X,Y]_W, X·β − Y·α)`. -/
def bmsBracketFun (x y : BMSAlgebra) : BMSAlgebra :=
  (wittMul x.1 y.1, superAction x.1 y.2 - superAction y.1 x.2)

theorem bmsBracketFun_addLeft (a b c : BMSAlgebra) :
    bmsBracketFun (a + b) c = bmsBracketFun a c + bmsBracketFun b c := by
  refine Prod.ext ?_ ?_
  · simp only [bmsBracketFun, fst_add, map_add, LinearMap.add_apply]
  · simp only [bmsBracketFun, fst_add, snd_add, map_add, LinearMap.add_apply]; abel

theorem bmsBracketFun_smulLeft (r : ℝ) (a b : BMSAlgebra) :
    bmsBracketFun (r • a) b = r • bmsBracketFun a b := by
  refine Prod.ext ?_ ?_
  · simp only [bmsBracketFun, fst_smul, LinearMap.map_smul₂]
  · simp only [bmsBracketFun, fst_smul, snd_smul, map_smul, LinearMap.smul_apply, smul_sub]

theorem bmsBracketFun_addRight (a b c : BMSAlgebra) :
    bmsBracketFun a (b + c) = bmsBracketFun a b + bmsBracketFun a c := by
  refine Prod.ext ?_ ?_
  · simp only [bmsBracketFun, fst_add, map_add, LinearMap.add_apply]
  · simp only [bmsBracketFun, fst_add, snd_add, map_add, LinearMap.add_apply]; abel

theorem bmsBracketFun_smulRight (r : ℝ) (a b : BMSAlgebra) :
    bmsBracketFun a (r • b) = r • bmsBracketFun a b := by
  refine Prod.ext ?_ ?_
  · simp only [bmsBracketFun, fst_smul, snd_smul, map_smul]
  · simp only [bmsBracketFun, fst_smul, snd_smul, map_smul, LinearMap.smul_apply, smul_sub]

/-- The BMS₃ semidirect bracket as an ℝ-bilinear map:
`[(X,α),(Y,β)] = ([X,Y]_W, X·β − Y·α)`. -/
def bmsBracketAux : BMSAlgebra →ₗ[ℝ] BMSAlgebra →ₗ[ℝ] BMSAlgebra :=
  LinearMap.mk₂ ℝ bmsBracketFun
    bmsBracketFun_addLeft bmsBracketFun_smulLeft
    bmsBracketFun_addRight bmsBracketFun_smulRight

instance : Bracket BMSAlgebra BMSAlgebra where
  bracket x y := bmsBracketAux x y

theorem bracket_def (x y : BMSAlgebra) : ⁅x, y⁆ = bmsBracketAux x y := rfl

@[simp] theorem bmsBracketAux_apply (x y : BMSAlgebra) :
    bmsBracketAux x y = (wittMul x.1 y.1, superAction x.1 y.2 - superAction y.1 x.2) := rfl

@[simp] theorem fst_zero : (0 : BMSAlgebra).1 = 0 := rfl
@[simp] theorem snd_zero : (0 : BMSAlgebra).2 = 0 := rfl

/-- The first (superrotation) component of a BMS bracket is the Witt bracket. -/
theorem bracket_fst (x y : BMSAlgebra) : (⁅x, y⁆ : BMSAlgebra).1 = wittMul x.1 y.1 := rfl

/-- The second (supertranslation) component of a BMS bracket is the action commutator. -/
theorem bracket_snd (x y : BMSAlgebra) :
    (⁅x, y⁆ : BMSAlgebra).2 = superAction x.1 y.2 - superAction y.1 x.2 := rfl

/-! ## §5. LieRing / LieAlgebra instances -/

theorem bmsBracket_self (x : BMSAlgebra) : bmsBracketAux x x = 0 := by
  apply Prod.ext
  · simpa only [bmsBracketAux_apply, fst_zero] using wittMul_self x.1
  · simp only [bmsBracketAux_apply, snd_zero, sub_self]

/-- **BMS₃ Jacobi (Leibniz form)** — the real content. The first (Witt) component is
`wittBracket_leibniz`; the second (supertranslation) component reduces to the same Witt Leibniz
identity applied to the three action cross-terms (this is why the weight-`−1` action
`[Lₘ,Tₙ] = (m−n)T_{m+n}` is the convention for which Jacobi closes). -/
theorem bmsBracket_leibniz (x y z : BMSAlgebra) :
    bmsBracketAux x (bmsBracketAux y z)
      = bmsBracketAux (bmsBracketAux x y) z + bmsBracketAux y (bmsBracketAux x z) := by
  apply Prod.ext
  · simp only [bmsBracketAux_apply, fst_add]
    exact wittMul_leibniz x.1 y.1 z.1
  · simp only [bmsBracketAux_apply, snd_add, map_sub]
    rw [superAction_leibniz x.1 y.1 z.2, superAction_leibniz x.1 z.1 y.2,
        superAction_leibniz y.1 z.1 x.2]
    abel

instance : LieRing BMSAlgebra where
  add_lie x y z := LinearMap.congr_fun (map_add bmsBracketAux x y) z
  lie_add x y z := map_add (bmsBracketAux x) y z
  lie_self x := bmsBracket_self x
  leibniz_lie x y z := bmsBracket_leibniz x y z

instance : LieAlgebra ℝ BMSAlgebra where
  lie_smul c x y := map_smul (bmsBracketAux x) c y

/-! ## §6. Generators + non-vacuity: a computed mixed bracket -/

/-- The **superrotation** generator embedded in BMS: `Lₘ ↦ (Lₘ, 0)`. -/
def bmsL (m : ℤ) : BMSAlgebra := (L m, 0)

/-- The **supertranslation** generator embedded in BMS: `Tₙ ↦ (0, Tₙ)`. -/
def bmsT (n : ℤ) : BMSAlgebra := (0, T n)

/-- The supertranslation embedding as an ℝ-linear map `SuperTrans → BMS`, `α ↦ (0,α)` — the
seam C4 pairs the supertranslation charge functional against. -/
def bmsInr : SuperTrans →ₗ[ℝ] BMSAlgebra := LinearMap.inr ℝ WittAlgebra SuperTrans

@[simp] theorem bmsInr_fst (α : SuperTrans) : (bmsInr α).1 = 0 := rfl
@[simp] theorem bmsInr_snd (α : SuperTrans) : (bmsInr α).2 = α := rfl

/-- **The mixed bracket** `[Lₘ, Tₙ] = (m − n) T_{m+n}` — the BMS₃ superrotation action on
supertranslations. -/
theorem bmsL_bmsT (m n : ℤ) : ⁅bmsL m, bmsT n⁆ = ((m : ℝ) - n) • bmsT (m + n) := by
  rw [bracket_def]
  apply Prod.ext
  · simp only [bmsBracketAux_apply, bmsL, bmsT, map_zero, fst_smul, smul_zero]
  · simp only [bmsBracketAux_apply, bmsL, bmsT, snd_smul, map_zero, sub_zero,
      superAction_L_T]

/-- **Non-vacuity pin** (`norm_num`-backed): `[L₁, T₋₁] = 2 T₀`. -/
theorem bmsL_one_bmsT_neg_one : ⁅bmsL 1, bmsT (-1)⁆ = (2 : ℝ) • bmsT 0 := by
  have h := bmsL_bmsT 1 (-1)
  norm_num at h
  exact h

/-! ## §7. The projection onto Vect(S¹) + the supertranslation ideal -/

/-- The projection `BMS → Witt` (forgetting supertranslations), `(X,α) ↦ X`, as a **Lie algebra
homomorphism**: the first (superrotation) component of a BMS bracket is the Witt bracket, so this
respects brackets. Its kernel is the supertranslation ideal; it is surjective. -/
def bmsProjWitt : BMSAlgebra →ₗ⁅ℝ⁆ WittAlgebra where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] theorem bmsProjWitt_apply (x : BMSAlgebra) : bmsProjWitt x = x.1 := rfl

theorem bmsProjWitt_surjective : Function.Surjective bmsProjWitt :=
  fun X => ⟨((X, 0) : BMSAlgebra), rfl⟩

/-- The **supertranslation ideal** `{(0,α)}` — the abelian BMS₃ ideal, definitionally the kernel
of the projection onto `Vect(S¹)`. -/
def superTransIdeal : LieIdeal ℝ BMSAlgebra := bmsProjWitt.ker

theorem mem_superTransIdeal {x : BMSAlgebra} : x ∈ superTransIdeal ↔ x.1 = 0 :=
  LieHom.mem_ker

/-- Every supertranslation `(0,α)` lies in the ideal. -/
theorem bmsInr_mem_superTransIdeal (α : SuperTrans) : bmsInr α ∈ superTransIdeal :=
  mem_superTransIdeal.mpr rfl

/-- **The supertranslation ideal is abelian**: `⁅(0,α),(0,β)⁆ = 0`. -/
theorem supertrans_abelian (α β : SuperTrans) : ⁅bmsInr α, bmsInr β⁆ = 0 := by
  rw [bracket_def]
  apply Prod.ext
  · simp only [bmsBracketAux_apply, bmsInr_fst, map_zero, LinearMap.zero_apply, fst_zero]
  · simp only [bmsBracketAux_apply, bmsInr_fst, bmsInr_snd, map_zero, LinearMap.zero_apply,
      snd_zero, sub_self]

/-- **The ideal is nonzero** (non-vacuity): it contains the nonzero supertranslation `(0, T₀)`. -/
theorem superTransIdeal_ne_bot : superTransIdeal ≠ ⊥ := by
  intro h
  have hmem : bmsInr (T 0) ∈ superTransIdeal := bmsInr_mem_superTransIdeal _
  rw [h, LieSubmodule.mem_bot] at hmem
  have : (T 0 : SuperTrans) = 0 := congrArg Prod.snd hmem
  exact (Finsupp.single_ne_zero.mpr (one_ne_zero)) this

/-- **The ideal is proper** (non-vacuity): the superrotation `L₀ = (L₀,0)` is not in it (its
projection `L₀ ≠ 0`). -/
theorem superTransIdeal_ne_top : superTransIdeal ≠ ⊤ := by
  intro h
  have hmem : bmsL 0 ∈ superTransIdeal := h ▸ Submodule.mem_top
  rw [mem_superTransIdeal] at hmem
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) hmem

/-! ## §8. The quotient: BMS / supertranslations ≅ Witt -/

/-- **BMS / supertranslations ≅ Witt** as Lie algebras — the first isomorphism theorem applied to
the surjective projection `bmsProjWitt` whose kernel is `superTransIdeal`. This is the honest
statement of the BMS₃ short exact sequence `0 → C∞(S¹)_ab → BMS₃ → Vect(S¹) → 0`. -/
noncomputable def bmsQuotSupertransEquivWitt :
    (BMSAlgebra ⧸ superTransIdeal) ≃ₗ⁅ℝ⁆ WittAlgebra :=
  have h : bmsProjWitt.range = ⊤ := (LieHom.range_eq_top bmsProjWitt).mpr bmsProjWitt_surjective
  (LieHom.quotKerEquivRange bmsProjWitt).trans (h.symm ▸ LieSubalgebra.topEquiv)

/-! ## §9. C4 seam — the charge functional pairing (documented) -/

/-
C4 (boundary phase-space + charges) consumes THIS module's `superAction` and `bmsInr`:
the supertranslation charge functional `Q_f` (Penna eq 3.3/3.13, `Q_f = ∫ f · membranePressure κ`
with `membranePressure κ = κ/8π` from `Structure.lean`) pairs against the supertranslation sector
`bmsInr : SuperTrans →ₗ BMSAlgebra` exposed here; the `Vect(S¹)`-action `superAction` is what the
charge algebra's superrotation transformation acts by. The centerless discipline (C0 verdict) is
respected: NO central extension appears in `BMSAlgebra` — any central charge is a C4/C5
charge-algebra property to be DERIVED, never baked into the algebra.
-/

end BMSAlgebra

end SKEFTHawking.Carrollian
