/-
# Phase 5q.H (N1a) — Freeze-A decomposition: the handle-trading realization at finest grain

Refactors `SpinSigmaRoute`'s **Freeze A** (`RealizesSphereProducts` — Benedetti arXiv:1907.10297
Prop 20.16 / Lemma 20.17 handle-trading; DR route `Lit-Search/Phase-5qH/
Omega4Spin_Z_formalization_route_20260706.md` sub-piece (2'): "the ONE genuinely Mathlib-absent
manifold-topology step") into its two **atomic** geometric constituents plus a machine-verified
block-iteration:

* `HyperbolicPeel` — **the single S²×S² handle-trade** (Benedetti Prop 20.16 / Lemma 20.17, the
  actual elementary lemma): if a structured manifold `p`'s intersection form splits off ONE
  hyperbolic plane `H` (`form p ≅ H ⊕ N'`), then `p` is bordant to `S²×S²` disjoint-union a
  manifold `p'` realizing `N'`: `[p] = [S²×S²] + [p']`. The single attaching-circle
  standardization in a chart (no h-cobordism / Whitney).
* `HyperbolicBase` — **the `b₂ = 0` base nullbordism** (Benedetti Thm 20.14, degenerate rank-0
  case): a structured manifold of rank `0` (`b₂ = 0`) has trivial bordism class. This atom is a
  *consequence* of `RealizesSphereProducts` itself (`hyperbolicBase_of_realizesSphereProducts`),
  so the NET new geometric ask over the monolithic freeze is exactly the single handle-trade.

The headline `realizesSphereProducts_of_peel_and_base` proves, **kernel-pure**, that these two
atoms discharge the full `RealizesSphereProducts` freeze: strong induction on the hyperbolic-block
structure peels one `S²×S²` per step (`HyperbolicPeel`), recurses, and bottoms out at
`HyperbolicBase`; the `q = rank/2` block count and the `[·] = q • [S²×S²]` accumulation are pure
`AddCommGroup`/`Nat` combinatorics, verified here. So the disclosed geometric residual shrinks from
the *iterated* realization to Benedetti's *atomic* handle-trade + base, with the combinatorial
iteration no longer hand-waved.

This does NOT weaken the geometry logically (the residual-manifold existence in `HyperbolicPeel` is
Benedetti's actual output); it refactors the geometric discharge burden into (atomic step) +
(verified iteration). Consistent with `SpinSigmaRoute`'s non-vacuity posture: the atoms are the
literature-verbatim geometric inputs, witnessed on the genuine spin instantiation (not the toy
`trivialPresentation`, which satisfies neither the atoms nor the freeze).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaRoute

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open Matrix

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Reindex composition**: `reindex e e (reindex e₀ e₀ M) = reindex (e₀.trans e) (e₀.trans e) M`.
The bookkeeping that lets the block-peel induction absorb the ambient reindex of a `cons` form. -/
theorem reindex_reindex_comp {α β γ : Type*} (e₀ : α ≃ β) (e : β ≃ γ)
    (M : Matrix α α ℤ) :
    Matrix.reindex e e (Matrix.reindex e₀ e₀ M)
      = Matrix.reindex (e₀.trans e) (e₀.trans e) M := rfl

variable {ξ : TangentialData X k I}

namespace SpinSigmaPresentation

/-- **Disclosed geometric atom — the single S²×S² handle-trade** (Benedetti arXiv:1907.10297
Prop 20.16 / Lemma 20.17): if a structured manifold `p`'s intersection form splits off one
hyperbolic plane `H` over a hyperbolic-standard complement `N'` (`form p ≅ H ⊕ N'`), then `p` is
data-bordant to `S²×S²` disjoint-union a manifold `p'` realizing `N'`, i.e.
`[p] = [S²×S²] + [p']` with `form p' ≅ N'` (reindexed to `p'`'s rank). The single elementary
handle-trade of the KT injective direction. -/
def HyperbolicPeel (R : SpinSigmaPresentation ξ) : Prop :=
  ∀ (p : StrMfd ξ) (m : ℕ) (E : Fin 2 ⊕ Fin m ≃ Fin (R.rank p))
    (N' : Matrix (Fin m) (Fin m) ℤ) (_ : IsHyperbolicForm N'),
    IntCongr (R.form p) (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ (p' : StrMfd ξ) (e' : Fin m ≃ Fin (R.rank p')),
      IntCongr (R.form p') (Matrix.reindex e' e' N') ∧
      DataBordismGrp.mk ξ p = DataBordismGrp.mk ξ R.s2s2 + DataBordismGrp.mk ξ p'

/-- **Disclosed geometric atom — the `b₂ = 0` base nullbordism** (Benedetti Thm 20.14, degenerate
rank-0 case; a spin 4-manifold with vanishing intersection form is, after surgery to a homotopy
`S⁴`, null-bordant since `S⁴ = ∂D⁵`): a structured manifold of rank `0` (`b₂ = 0`) has trivial
bordism class. -/
def HyperbolicBase (R : SpinSigmaPresentation ξ) : Prop :=
  ∀ (p : StrMfd ξ), R.rank p = 0 → DataBordismGrp.mk ξ p = 0

/-- **The block-peel iteration (kernel-pure engine)**: for a manifold `p` whose form is congruent
to (a reindexing of) a hyperbolic-standard form `N` of rank `n`, the two geometric atoms compute
`[p] = (n / 2) • [S²×S²]`. Structural induction on `IsHyperbolicForm N`: the `empty` block is the
base (`HyperbolicBase`), each `cons` block peels one `S²×S²` (`HyperbolicPeel`) and recurses. -/
theorem realizes_aux (R : SpinSigmaPresentation ξ)
    (hPeel : R.HyperbolicPeel) (hBase : R.HyperbolicBase) :
    ∀ {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}, IsHyperbolicForm N →
      ∀ (p : StrMfd ξ) (e : Fin n ≃ Fin (R.rank p)),
        IntCongr (R.form p) (Matrix.reindex e e N) →
        DataBordismGrp.mk ξ p = (n / 2) • DataBordismGrp.mk ξ R.s2s2 := by
  intro n N hN
  induction hN with
  | empty =>
    intro p e hcong
    have hr : R.rank p = 0 := by simpa using (Fintype.card_congr e).symm
    rw [hBase p hr]; simp
  | @cons m k e₀ N' h ih =>
    intro p e hcong
    rw [reindex_reindex_comp] at hcong
    obtain ⟨p', e', hcong'', hbord⟩ := hPeel p _ (e₀.trans e) _ h hcong
    have hp' := ih p' e' hcong''
    have hcard : k = m + 2 := by
      have h2 := Fintype.card_congr e₀
      simp only [Fintype.card_sum, Fintype.card_fin] at h2
      omega
    rw [hbord, hp', hcard, show (m + 2) / 2 = m / 2 + 1 from by omega, succ_nsmul, add_comm]

/-- **Freeze-A discharge from the two atoms (kernel-pure)**: `HyperbolicPeel` (the single
handle-trade) and `HyperbolicBase` (the rank-0 nullbordism) together imply the full
`RealizesSphereProducts` freeze. The block-iteration is `realizes_aux`; here `N` sits over
`Fin (rank p)` so the reindex is the identity. -/
theorem realizesSphereProducts_of_peel_and_base (R : SpinSigmaPresentation ξ)
    (hPeel : R.HyperbolicPeel) (hBase : R.HyperbolicBase) : R.RealizesSphereProducts := by
  intro p hex
  obtain ⟨N, hN, hcong⟩ := hex
  exact realizes_aux R hPeel hBase hN p (Equiv.refl (Fin (R.rank p)))
    (by simpa using hcong)

/-- **The base atom is a consequence of the freeze** — so the NET new geometric ask of the
decomposition over the monolithic `RealizesSphereProducts` is exactly the single handle-trade
`HyperbolicPeel`. A rank-0 manifold has the empty form, hence a hyperbolic presentation, hence
class `(0/2) • [S²×S²] = 0` by the freeze. -/
theorem hyperbolicBase_of_realizesSphereProducts (R : SpinSigmaPresentation ξ)
    (hR : R.RealizesSphereProducts) : R.HyperbolicBase := by
  intro p hr
  have hemp : IsEmpty (Fin (R.rank p)) := by rw [hr]; infer_instance
  have hform0 : R.form p = 0 := by funext i; exact isEmptyElim i
  have hsig : latticeSig (R.form p) = 0 := by rw [hform0]; exact latticeSig_zero_matrix
  have hreal := hR p (exists_hyperbolic_congr (R.form p) (R.even_unimod p) hsig)
  rw [hreal, hr]; simp

end SpinSigmaPresentation

end SKEFTHawking.SpinSigmaRoute
