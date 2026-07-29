/-
# Phase 5q.H — `heven` at the welded `K3` is exactly a Spin/Wu datum, and that datum is not vacuous

The third geometric input of
`KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` is

    heven : ∀ o a, (2 : ℤ) ∣ ⟨a ∪ a, [K3]_o⟩.

In-tree this is *already* reduced: `SingularCohomologyInt.interFormInt_diag_even` delivers exactly
that shape from a `SingularCohomologyInt.SpinWuDatum fc` — the disclosed `spinWu_even_datum`
structure carrying the mod-2 fundamental functional `μ₂`, the ℤ→ℤ/2 compatibility
`⟨·,[M]⟩ ≡ μ₂ ∘ redH`, and the Spin condition `∀ y, μ₂(y ∪ y) = 0` (`= v₂ = 0 = w₂ = 0` on an
oriented 4-manifold). §1 states the bridge at the welded carrier; §3 rewrites the headline so the
ledger reads `hstable` + Spin/Wu + one geometric datum.

## §2 — the non-vacuity that actually needed checking

`SpinWuDatum`'s Spin field `wu_vanish` is satisfied *trivially* by `μ₂ = 0`, so on its own the
structure could have been discharged with no geometry at all. It cannot be, and §2 proves why:
`μ₂ = 0` forces (through `eval_compat`) every value of `⟨·,[K3]⟩` to be even, hence every entry of
the intersection matrix to be even, hence `2²² ∣ det` — contradicting unimodularity. So on any
carrier whose intersection matrix is unimodular (`≡` integral Poincaré duality, by
`KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det`) the datum's `μ₂` is necessarily nonzero and
`wu_vanish` is a genuine constraint on the manifold.

`det_dvd_two_pow_of_entries_even` is the elementary lemma behind it, proved by pushing `det` through
`Int.castRingHom (ZMod 2)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionFormEvenInt
import SKEFTHawking.KummerK3CapDualFamily

namespace SKEFTHawking.KummerK3EvenFromSpinWu

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3CapDualFamily

noncomputable section

variable {X : TopCat}

/-! ## §1. `heven` from a Spin/Wu datum, at the welded carrier -/

/-- **`heven`, verbatim, from a per-orientation Spin/Wu datum.**

`SingularCohomologyInt.interFormInt_diag_even` instantiated at the welded `K3`'s oriented
fundamental classes. This is a bridge, not new content: it records that the third geometric input of
the K3 headline is *already* discharged in-tree modulo the disclosed `spinWu_even_datum` structure,
so no separate evenness argument on the weld is owed — only `w₂(K3) = 0`. -/
theorem kummerK3_heven_of_spinWu
    (D : ∀ o : IntOrientation KummerK3, SpinWuDatum (intFundamentalClassOfIntOrientation o)) :
    ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a :=
  fun o a => interFormInt_diag_even _ (D o) a

/-! ## §2. The datum is not vacuous: `μ₂ = 0` is incompatible with unimodularity -/

/-- **An integer matrix with all entries even has `det ≡ 0 mod 2`** (for a nonempty index type).
Pushed through `Int.castRingHom (ZMod 2)`: the reduced matrix is the zero matrix, whose determinant
vanishes in positive size. -/
theorem det_even_of_entries_even {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, (2 : ℤ) ∣ M i j) : (2 : ℤ) ∣ M.det := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hzero : ((Int.castRingHom (ZMod 2)).mapMatrix M) = 0 := by
    ext i j
    have := h i j
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    simpa using this
  rw [show ((M.det : ℤ) : ZMod 2) = (Int.castRingHom (ZMod 2)) M.det from rfl,
    -- v4.32: `Matrix.det_zero`'s `Nonempty` hypothesis is now INSTANCE-implicit, not explicit —
    -- the `haveI` above already supplies it, so the positional argument must go.
    RingHom.map_det, hzero, Matrix.det_zero]

/-- **A unimodular integer matrix of positive size has an odd entry.** The contrapositive of §2's
elementary lemma against `det = ±1`. -/
theorem exists_odd_entry_of_isUnimodular {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℤ)
    (huni : IsUnimodular M) : ∃ i j, ¬ (2 : ℤ) ∣ M i j := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hdvd := det_even_of_entries_even hn M (fun i j => hcon i j)
  rcases huni with h | h <;> rw [h] at hdvd <;> omega

/-- **THE NON-VACUITY CERTIFICATE FOR `SpinWuDatum`.**

A `SpinWuDatum` whose mod-2 fundamental functional `μ₂` is the zero map would satisfy its Spin field
`wu_vanish` for free; §2 shows such a datum cannot exist on a carrier with unimodular intersection
matrix. Chain: `μ₂ = 0` + `eval_compat` ⟹ `⟨ω,[M]⟩` even for every `ω` ⟹ every entry of
`interMatrix fc B` even ⟹ `2 ∣ det` ⟹ not `±1`.

So `wu_vanish` is a genuine assertion about the manifold (namely `v₂ = 0`), not a hypothesis that a
degenerate witness can satisfy — which is what one has to check before accepting a disclosed-datum
reduction of `heven`. -/
theorem spinWu_mu2_ne_zero (fc : IntFundamentalClass X) (B : IntH2Basis X) (hrank : 0 < B.rank)
    (huni : IsUnimodular (interMatrix fc B)) (D : SpinWuDatum fc) : D.mu2 ≠ 0 := by
  intro hmu
  obtain ⟨i, j, hij⟩ := exists_odd_entry_of_isUnimodular hrank _ huni
  apply hij
  rw [interMatrix_apply, interFormInt_apply,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    D.eval_compat, hmu]
  rfl

/-- **The certificate at the welded `K3`**, where `hrank` is discharged
(`kummerK3IntH2Basis_rank : rank = 22`) and unimodularity is `hpd` through
`KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det`. -/
theorem kummerK3_spinWu_mu2_ne_zero (o : IntOrientation KummerK3)
    (hpd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (D : SpinWuDatum (intFundamentalClassOfIntOrientation o)) : D.mu2 ≠ 0 := by
  refine spinWu_mu2_ne_zero _ kummerK3IntH2Basis (by rw [kummerK3IntH2Basis_rank]; norm_num) ?_ D
  exact Int.isUnit_iff.mp ((KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det o).mp hpd)

/-! ## §3. The ledger, restated: `hstable` + Spin/Wu + ONE geometric datum -/

/-- **THE WELDED `K3`'s E1 ATOMS FROM THREE INPUTS.**

Composing §1 with `KummerK3CapDualFamily.nonempty_kummerK3E1Atoms_of_stable_of_geoData`, the whole
E1 residual ledger of the welded Kummer `K3` reads:

* `hstable` — `StableNegRank16Two`: pure lattice theory (wt1's Eichler lane), no geometry;
* `D` — a Spin/Wu datum per orientation: `w₂(K3) = 0` plus the ℤ→ℤ/2 fundamental-class
  compatibility (§2: not satisfiable by a degenerate `μ₂`);
* `hgeo` — one geometric datum per orientation: cohomology classes with known cap-duals, whose
  cap-duals **generate** `H₂(K3;ℤ)`, together with the `22 × 22` Kronecker table `⟨−2⟩¹⁶ ⊕ 3H` on a
  selected sub-family.

The Gram congruence, the Kummer half-sums *as a Gram obligation*, integral Poincaré duality as a
separate input, and any basis of `H₂(K3;ℤ)` have all been eliminated. -/
theorem nonempty_kummerK3E1Atoms_of_stable_of_spinWu_of_geoData (hstable : StableNegRank16Two)
    (D : ∀ o : IntOrientation KummerK3, SpinWuDatum (intFundamentalClassOfIntOrientation o))
    (hgeo : ∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤
          ∧ ∀ i j, kroneckerHInt 2 (a (sel j)) (c (sel i)) = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable_of_geoData hstable (kummerK3_heven_of_spinWu D) hgeo

end

end SKEFTHawking.KummerK3EvenFromSpinWu
