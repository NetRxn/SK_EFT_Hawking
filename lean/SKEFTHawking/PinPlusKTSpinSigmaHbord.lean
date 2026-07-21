/-
# Phase 5q.H close-out — THE σ-DESCENT'S LAST ATOM `hbord`, reduced to a Novikov-Lagrangian disclosure

The σ-presentation's entire machinery, post-#167, collapses onto ONE deep atom `hbord` — Thom
bordism-invariance of the lattice signature (`sig = hbord` alone on the canonical bundle,
`PinPlusKTSpinSigmaCanonicalBundle.sig_eq_sigThom`):

    hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (fc p) (B p)) = latticeSig (interMatrix (fc q) (B q))

This module discharges `hbord` via the **classical Novikov route**. If `p`, `q` are data-bordant by a
5-dimensional bordism `W` (`∂W = M_p ⊔ (−M_q)`), then the boundary intersection form
`blockDiag (II M_p) (−(II M_q))` bounds, so it carries a **Lagrangian** `L = im(H²(W;ℝ) → H²(∂W;ℝ))` —
a half-dimensional totally-isotropic subspace — and therefore has signature `0`. Since
`σ(blockDiag (II M_p) (−(II M_q))) = σ(M_p) − σ(M_q)` (block additivity + orientation reversal), we get
`σ(M_p) = σ(M_q)`.

## The honest split (algebra BANKED, geometry a NAMED atom)

* **Algebra (a), banked/built:** the metabolic lemma `latticeSig_eq_zero_of_lagrangian`
  (`LatticeMetabolic`, "form with a Lagrangian ⟹ σ = 0"), plus block additivity `latticeSig_blockDiag`
  and orientation reversal `latticeSig_neg` (Freeze-era lattice toolbox), and even-unimodularity of the
  negated/blocked summands (`isEvenUnimodular_neg`/`isEvenUnimodular_blockDiag`, all free from `wu`/`pd`).
* **Geometry (b), a single disclosed atom `NovikovLagrangianAtom`:** for each data-bordism witness, the
  boundary form `blockDiag (II M_p) (−(II M_q))` carries a half-dimensional isotropic subspace. This is
  precisely the classical Novikov Lagrangian — its **isotropy** (classes that extend over `W` cup to zero
  on `∂W`, from cup-functoriality + `[W,∂W]`) and its **half-dimensionality** (Poincaré–Lefschetz "half
  lives, half dies") — carried as disclosed geometry at the same `discharge_future` tier as the bundle's
  `fc`/`B`/`wu`/`pd`/`fc_sum`/`B_sum`. It is NOT a fabricated grade: `L` is a genuine real subspace of the
  boundary form, the boundary form is the genuine block sum of the disclosed intersection matrices, and
  the isotropy is stated against the actual real quadratic form. It is spin-side and `k₀`-free.

Given the atom, `hbord_of_novikovLagrangian` discharges `hbord` OUTRIGHT, and the canonical bundle's
`sigThom` needs no free `hbord` hypothesis (`CanonicalSpinSigmaAtoms.sigThomNovikov`): **the σ-descent
COMPLETES** — the whole σ-presentation is live modulo the row's per-element seeds plus this single
geometric atom.

Dimension discipline: `M_p`, `M_q` closed spin 4-manifolds; `W` a 5-dimensional tethered bordism; the
forms live on `H²(M;ℤ)`; the Lagrangian `L ⊆ H²(∂W;ℝ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle
import SKEFTHawking.LatticeMetabolic
import SKEFTHawking.ThetaDefiniteDischarge

namespace SKEFTHawking.PinPlusKTSpinSigmaHbord

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaStock
open SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The Novikov-Lagrangian disclosure atom -/

/-- **The Novikov-Lagrangian geometric atom.** For the disclosed atom bundle `a`, and every pair of
data-bordant structured manifolds `p`, `q`, the boundary intersection form
`blockDiag (II M_p) (−(II M_q))` — the intersection form of `∂W = M_p ⊔ (−M_q)` — carries a
**half-dimensional isotropic subspace** `L`: the real quadratic form of the boundary matrix vanishes on
`L`, and `L`'s dimension is exactly half the boundary rank (`b₂(M_p) + b₂(M_q) = 2·dim L`).

This is the classical Lagrangian `L = im(H²(W;ℝ) → H²(∂W;ℝ))` of the bounding 5-manifold `W`: its
isotropy is cup-functoriality against `[W,∂W]` (classes extending over `W` cup to zero on the boundary),
its half-dimensionality is Poincaré–Lefschetz duality ("half lives, half dies"). Named here as the single
geometric input `hbord` reduces to; the isotropy and half-dimensionality are its two conjuncts (the
"isotropy/half-dim split"). Not discharged in-tree (no manifold cohomology in Mathlib). -/
def NovikovLagrangianAtom (a : SpinSigmaAtoms prov) : Prop :=
  ∀ p q : StrMfd (spinEmptyData prov), IsDataBordant (spinEmptyData prov) p q →
    ∃ L : Submodule ℝ (Fin ((a.B p).rank + (a.B q).rank) → ℝ),
      (a.B p).rank + (a.B q).rank = 2 * Module.finrank ℝ L ∧
      ∀ x ∈ L, ((blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q))).map
          (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0

variable {prov}

/-! ## §2. `hbord` discharged from the atom -/

/-- **The σ-descent's last atom `hbord`, DISCHARGED from the Novikov-Lagrangian disclosure.** Given the
disclosed atom bundle `a` and the geometric atom `NovikovLagrangianAtom a`, the lattice signature is
bordism-invariant — `σ(II M_p) = σ(II M_q)` for data-bordant `p`, `q`. Proof: the boundary form
`blockDiag (II M_p) (−(II M_q))` is even-unimodular (from `wu`/`pd` via `isEvenUnimodular_neg` +
`isEvenUnimodular_blockDiag`), so nondegenerate; the disclosed half-dimensional isotropic `L` makes it
metabolic, hence `σ = 0` (`latticeSig_eq_zero_of_lagrangian`); block additivity + orientation reversal
(`latticeSig_blockDiag` + `latticeSig_neg`) turn that into `σ(II M_p) − σ(II M_q) = 0`. This is exactly
the `hbord` hypothesis of `sigThomOfAtoms`/`CanonicalSpinSigmaAtoms.sigThom`, now a THEOREM given the
single geometric atom — the algebra half of Novikov additivity fully banked. -/
theorem hbord_of_novikovLagrangian (a : SpinSigmaAtoms prov)
    (hnov : NovikovLagrangianAtom prov a) :
    ∀ p q, IsDataBordant (spinEmptyData prov) p q →
      latticeSig (interMatrix (a.fc p) (a.B p)) = latticeSig (interMatrix (a.fc q) (a.B q)) := by
  intro p q hb
  obtain ⟨L, hdim, hiso⟩ := hnov p q hb
  have heuP := isEvenUnimodular_of_intPD (a.fc p) (a.B p) (a.wu p) (a.pd p)
  have heuQ := isEvenUnimodular_of_intPD (a.fc q) (a.B q) (a.wu q) (a.pd q)
  have heuNegQ := isEvenUnimodular_neg _ heuQ
  have hbd_eu := isEvenUnimodular_blockDiag (interMatrix (a.fc p) (a.B p))
    (-interMatrix (a.fc q) (a.B q)) heuP heuNegQ
  have hzero := latticeSig_eq_zero_of_lagrangian hdim
    (blockDiag (interMatrix (a.fc p) (a.B p)) (-interMatrix (a.fc q) (a.B q)))
    hbd_eu.radical_eq_bot L rfl hiso
  have hadd := latticeSig_blockDiag (interMatrix (a.fc p) (a.B p))
    (-interMatrix (a.fc q) (a.B q)) heuP heuNegQ
  rw [latticeSig_neg] at hadd
  omega

/-! ## §3. The σ-descent COMPLETES on the canonical bundle -/

/-- **The canonical bundle's Thom signature hom, needing ONLY the geometric Novikov atom** (no free
`hbord` hypothesis). With `hbord` discharged from `NovikovLagrangianAtom` (§2), the bordism-invariant
signature `Ω → ℤ` is built with the deep bordism-invariance atom supplied by the single disclosed
geometric statement. The elementary disjoint-union additivity is internal (`interMatrixBlockAtom`,
#167); nothing else is outstanding. This is the σ-descent COMPLETED on the canonical construction:
`sig = NovikovLagrangianAtom` alone. -/
noncomputable def sigThomNovikovCanonical (c : CanonicalSpinSigmaAtoms prov)
    (hnov : NovikovLagrangianAtom prov c.toSpinSigmaAtoms) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  c.sigThom (hbord_of_novikovLagrangian c.toSpinSigmaAtoms hnov)

/-- **The completed Thom hom computes the lattice signature on classes** (`rfl`) — the `sig_eq`
obligation, automatic. So `sigThomNovikovCanonical c hnov` is a drop-in for the disclosed `sig`, with
EVERY additivity/bordism-invariance obligation discharged modulo the single geometric atom. -/
@[simp] theorem sigThomNovikovCanonical_mk (c : CanonicalSpinSigmaAtoms prov)
    (hnov : NovikovLagrangianAtom prov c.toSpinSigmaAtoms) (p : StrMfd (spinEmptyData prov)) :
    sigThomNovikovCanonical c hnov (DataBordismGrp.mk (spinEmptyData prov) p)
      = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p)) :=
  rfl

/-- **The disclosed `sig` field is FORCED by the single geometric Novikov atom** — the σ-descent's last
degree of freedom is spent. Both `c.sig` (the disclosed Thom hom) and `sigThomNovikovCanonical c hnov`
(built from `NovikovLagrangianAtom` + the discharged block atom) are `AddMonoidHom`s on
`DataBordismGrp = Quot _` agreeing on every generator, hence equal. So on the canonical construction the
whole σ-presentation collapses onto ONE disclosed geometric statement (the Novikov Lagrangian), with all
elementary additivity AND the deep bordism-invariance discharged from it. -/
theorem sig_eq_sigThomNovikovCanonical (c : CanonicalSpinSigmaAtoms prov)
    (hnov : NovikovLagrangianAtom prov c.toSpinSigmaAtoms) :
    c.toSpinSigmaAtoms.sig = sigThomNovikovCanonical c hnov :=
  c.sig_eq_sigThom (hbord_of_novikovLagrangian c.toSpinSigmaAtoms hnov)

end SKEFTHawking.PinPlusKTSpinSigmaHbord
