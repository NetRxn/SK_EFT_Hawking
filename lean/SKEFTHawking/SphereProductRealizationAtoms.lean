/-
# Phase 5q.H (N1a) — Freeze-A atoms at finest grain: the handle-trade shrunk to a form-free bordism

Attacks the two Freeze-A residual atoms `HyperbolicPeel` / `HyperbolicBase` of
`SphereProductRealization.lean` (the decomposition of `SpinSigmaRoute`'s Freeze A
`RealizesSphereProducts`, Benedetti arXiv:1907.10297 Prop 20.16 / Lemma 20.17 handle-trading; DR route
`Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md`). Result: the disclosed geometric
residual of the handle-trade is **shrunk further, kernel-pure**, by discharging its
intersection-form-matching obligation with lattice algebra.

The pivot is that in `HyperbolicPeel` the geometric handle-trade is asked to certify *three* things at
once — (i) the existence of a residual structured manifold `p'`, (ii) the bordism
`[p] = [S²×S²] + [p']`, and (iii) that `p'`'s intersection form `≅ N'` (the complement). Obligation
(iii) is **not geometric**: the signature is a bordism invariant (Thom), so `latticeSig (form p') = 0`
is forced by (ii); and *every* `σ=0` even-unimodular integer form is hyperbolic-standard
(`exists_hyperbolic_congr`), with the σ=0 congruence class **unique** — proven here as
`intCongr_of_evenUnimodular_sig_zero`. So (iii) is a lattice consequence of (i)+(ii)+`even_unimod`.

We therefore introduce a **strictly smaller geometric atom** `HandleTradeSplit` — same inputs as
`HyperbolicPeel`, but whose output drops the `IntCongr (form p') …` obligation, asserting only
`rank p' = m` and the bordism — and prove `HandleTradeSplit → HyperbolicPeel` kernel-pure. Composed
with the existing `realizesSphereProducts_of_peel_and_base`, this yields
`realizesSphereProducts_of_split_and_base : HandleTradeSplit → HyperbolicBase → RealizesSphereProducts`.
The net geometric ask of Freeze A is thereby pinned at its minimal grain: the **form-free**
handle-trade (residual manifold + bordism + its second Betti number), Benedetti Prop 20.16 / Lemma
20.17, with the residual's whole intersection form discharged by the in-tree lattice engine.

Supporting kernel-pure lattice infrastructure (the σ=0 uniqueness half of the Milnor–Husemoller
even-indefinite classification, previously only present as `exists_hyperbolic_congr`'s *existence*):
`intCongr_submatrix_perm` (permutation congruence), `IsHyperbolicForm.reindex`,
`hyperbolicForm_intCongr` (two hyperbolic-standard forms of equal rank are congruent),
`intCongr_of_evenUnimodular_sig_zero` (the σ=0 congruence class is unique).

The `HyperbolicBase` atom (rank-0 nullbordism, Benedetti Thm 20.14 rank-0 case) is left as-is: it is
already minimal, and `SphereProductRealization.hyperbolicBase_of_realizesSphereProducts` already shows
it is a *consequence* of the freeze — so the net-new geometric ask of Freeze A is exactly the (now
form-free) single handle-trade.

Does NOT modify `SphereProductRealization.lean` / `SpinSigmaRoute.lean` / `SpinSigmaRouteDoor.lean`
(imports them). Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProductRealization

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open Matrix

/-- Permutation congruence over `Fin p`: `B` is `IntCongr` to any simultaneous row/col reindex. -/
theorem intCongr_submatrix_perm {p : ℕ} (f : Fin p ≃ Fin p) (B : Matrix (Fin p) (Fin p) ℤ) :
    IntCongr B (B.submatrix f f) := by
  refine ⟨Equiv.Perm.permMatrix ℤ f.symm, ?_, ?_⟩
  · rw [Matrix.det_permutation]
    exact (Equiv.Perm.sign f.symm).isUnit.map (Int.castRingHom ℤ)
  · rw [Matrix.transpose_permMatrix]
    simp only [Equiv.Perm.permMatrix]
    rw [show (f.symm)⁻¹ = f from by rw [Equiv.Perm.inv_def, Equiv.symm_symm],
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
      Matrix.submatrix_submatrix]
    simp

/-- `IsHyperbolicForm` is preserved by simultaneous reindex. -/
theorem IsHyperbolicForm.reindex {n k : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (h : IsHyperbolicForm N) (σ : Fin n ≃ Fin k) :
    IsHyperbolicForm (Matrix.reindex σ σ N) := by
  induction h generalizing k with
  | empty =>
    have hk : k = 0 := by simpa using (Fintype.card_congr σ).symm
    subst hk
    exact (Subsingleton.elim (Matrix.reindex σ σ (0 : Matrix (Fin 0) (Fin 0) ℤ)) 0) ▸
      IsHyperbolicForm.empty
  | cons e hN _ =>
    exact IsHyperbolicForm.cons (e.trans σ) hN

/-- Two hyperbolic-standard forms of equal rank are `IntCongr`. -/
theorem hyperbolicForm_intCongr : ∀ {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ},
    IsHyperbolicForm M → IsHyperbolicForm N → IntCongr M N := by
  intro n M N hM
  induction hM with
  | empty =>
    intro _
    exact Subsingleton.elim (0 : Matrix (Fin 0) (Fin 0) ℤ) N ▸ IntCongr.rfl _
  | @cons a p eM M₀ hM₀ ihM =>
    intro hN
    cases hN with
    | empty => exact absurd (Fintype.card_congr eM) (by simp)
    | @cons b pc eN N₀ hN₀ =>
      have hab : a = b := by
        have h1 := Fintype.card_congr eM
        have h2 := Fintype.card_congr eN
        simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
        omega
      subst hab
      set g : Fin p ≃ Fin p := eN.symm.trans eM with hg
      have hEq : (Matrix.reindex eM eM (Matrix.fromBlocks Hyp 0 0 M₀)).submatrix g g
          = Matrix.reindex eN eN (Matrix.fromBlocks Hyp 0 0 M₀) := by
        ext i j
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hg, Equiv.trans_apply,
          Equiv.symm_apply_apply]
      have step1 : IntCongr (Matrix.reindex eM eM (Matrix.fromBlocks Hyp 0 0 M₀))
          (Matrix.reindex eN eN (Matrix.fromBlocks Hyp 0 0 M₀)) := by
        have hp := intCongr_submatrix_perm g (Matrix.reindex eM eM (Matrix.fromBlocks Hyp 0 0 M₀))
        rwa [hEq] at hp
      exact step1.trans (IntCongr.hyp_block eN (ihM hN₀))

/-- **The σ=0 congruence class is unique**: any two even-unimodular integer forms of the *same rank*
and *both* of signature `0` are `IntCongr`. This is the σ=0 slice of the Milnor–Husemoller
even-indefinite classification — the **uniqueness** companion of the in-tree `exists_hyperbolic_congr`
(existence). Both reduce to a common hyperbolic-standard form (`exists_hyperbolic_congr`), and the two
hyperbolic-standard forms of equal rank are congruent (`hyperbolicForm_intCongr`). -/
theorem intCongr_of_evenUnimodular_sig_zero {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ}
    (heuM : IsEvenUnimodular M) (hsigM : latticeSig M = 0)
    (heuN : IsEvenUnimodular N) (hsigN : latticeSig N = 0) : IntCongr M N := by
  obtain ⟨KM, hKM, hMKM⟩ := exists_hyperbolic_congr M heuM hsigM
  obtain ⟨KN, hKN, hNKN⟩ := exists_hyperbolic_congr N heuN hsigN
  exact hMKM.trans ((hyperbolicForm_intCongr hKM hKN).trans hNKN.symm)

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {ξ : TangentialData X k I}

namespace SpinSigmaPresentation

/-- **The form-free geometric atom — the single S²×S² handle-trade without the form bookkeeping**
(Benedetti arXiv:1907.10297 Prop 20.16 / Lemma 20.17). Identical *inputs* to `HyperbolicPeel` (a
structured manifold `p` whose form splits off one hyperbolic plane `H` over a hyperbolic-standard
complement `N'`), but the *output* drops the intersection-form obligation on the residual: it asserts
only that there is a residual structured manifold `p'` of the complement's rank (`rank p' = m`, i.e.
`b₂(p') = m`) with `[p] = [S²×S²] + [p']`. That the residual's whole intersection form is `≅ N'` is
NOT asked of the geometry — it is discharged by the lattice engine (see
`hyperbolicPeel_of_handleTradeSplit`): the signature is a bordism invariant, so
`latticeSig (form p') = 0`, and the σ=0 even-unimodular congruence class is unique
(`intCongr_of_evenUnimodular_sig_zero`). This is the minimal-grain form of the KT injective-direction
handle-trade — the attaching-circle standardization in a chart (no h-cobordism / Whitney), stripped of
all lattice bookkeeping. -/
def HandleTradeSplit (R : SpinSigmaPresentation ξ) : Prop :=
  ∀ (p : StrMfd ξ) (m : ℕ) (E : Fin 2 ⊕ Fin m ≃ Fin (R.rank p))
    (N' : Matrix (Fin m) (Fin m) ℤ) (_ : IsHyperbolicForm N'),
    IntCongr (R.form p) (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ p' : StrMfd ξ, R.rank p' = m ∧
      DataBordismGrp.mk ξ p = DataBordismGrp.mk ξ R.s2s2 + DataBordismGrp.mk ξ p'

/-- **The form-free handle-trade discharges the full `HyperbolicPeel` (kernel-pure).** Given the
smaller geometric atom `HandleTradeSplit` (residual manifold + bordism + its rank), the residual's
intersection-form realization `IntCongr (form p') (reindex e' e' N')` — the extra obligation
`HyperbolicPeel` places on the geometry — is reconstructed by lattice algebra: the signature descends
to a bordism invariant (`R.sig`), so from `[p] = [S²×S²] + [p']` with both `form p` and `form s2s2`
of signature `0` (each hyperbolic-standard) one gets `latticeSig (form p') = 0`; then `form p'` (even
unimodular by `R.even_unimod`, signature `0`) and the hyperbolic-standard `reindex e' e' N'`
(`IsHyperbolicForm.reindex`) are congruent by the σ=0 uniqueness
`intCongr_of_evenUnimodular_sig_zero`. So the net geometric ask of Freeze A drops from the
form-matched handle-trade to the **form-free** one. -/
theorem hyperbolicPeel_of_handleTradeSplit (R : SpinSigmaPresentation ξ)
    (hSplit : R.HandleTradeSplit) : R.HyperbolicPeel := by
  intro p m E N' hN' hcong
  obtain ⟨p', hrank, hbord⟩ := hSplit p m E N' hN' hcong
  refine ⟨p', finCongr hrank.symm, ?_, hbord⟩
  -- The residual's form realization, from lattice algebra (signature bordism-invariance + σ=0 uniqueness).
  have hHp : IsHyperbolicForm (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) :=
    IsHyperbolicForm.cons E hN'
  have hsigFormP : latticeSig (R.form p) = 0 := by
    rw [← hcong.latticeSig]; exact hHp.latticeSig_eq_zero
  have hsigS2 : latticeSig (R.form R.s2s2) = 0 := by
    obtain ⟨N0, hN0, hc0⟩ := R.s2s2_hyp
    rw [← hc0.latticeSig]; exact hN0.latticeSig_eq_zero
  have hsigFormP' : latticeSig (R.form p') = 0 := by
    have hadd := congrArg R.sig hbord
    rw [map_add, R.sig_eq p, R.sig_eq R.s2s2, R.sig_eq p', hsigFormP, hsigS2] at hadd
    omega
  have hHrei : IsHyperbolicForm (Matrix.reindex (finCongr hrank.symm) (finCongr hrank.symm) N') :=
    IsHyperbolicForm.reindex hN' (finCongr hrank.symm)
  exact intCongr_of_evenUnimodular_sig_zero (R.even_unimod p') hsigFormP'
    hHrei.isEvenUnimodular hHrei.latticeSig_eq_zero

/-- **Freeze-A discharge from the form-free split + the rank-0 base (kernel-pure).** Composes the
handle-trade reduction `hyperbolicPeel_of_handleTradeSplit` with the existing engine
`realizesSphereProducts_of_peel_and_base`: the form-free geometric atom `HandleTradeSplit` and the
rank-0 nullbordism `HyperbolicBase` together discharge the full `RealizesSphereProducts` freeze
(Benedetti's `n(S²×S²)` realization). This pins the whole of Freeze A's geometric residual at its
minimal grain — one form-free handle-trade (Prop 20.16 / Lem 20.17) plus the rank-0 base (Thm 20.14,
itself a *consequence* of the freeze via `hyperbolicBase_of_realizesSphereProducts`). -/
theorem realizesSphereProducts_of_split_and_base (R : SpinSigmaPresentation ξ)
    (hSplit : R.HandleTradeSplit) (hBase : R.HyperbolicBase) : R.RealizesSphereProducts :=
  realizesSphereProducts_of_peel_and_base R (hyperbolicPeel_of_handleTradeSplit R hSplit) hBase

end SpinSigmaPresentation

end SKEFTHawking.SpinSigmaRoute
