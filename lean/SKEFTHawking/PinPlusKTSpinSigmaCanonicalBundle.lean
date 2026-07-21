/-
# Phase 5q.H close-out — THE DISCLOSURE ATOM: the canonical-sum `SpinSigmaAtoms` bundle

`PinPlusKTSpinSigmaStock.InterMatrixBlockAtom prov a` — the single geometric residual of the σ-descent's
disjoint-union additivity `hadd` — is NOT provable for an ARBITRARY disclosed bundle `a` (the #161
assessment: `a`'s `fc`/`B` on a disjoint union bear no relation to the summands). The
`IntersectionMatrixDisjointSumBlockCongr` module proved the block-congruence for the CANONICAL sum
construction (`intFundClassSum`/`intH2BasisSum`); this module lands that on a bundle-level object.

## What this module builds (the #164-named bridge, discharged)

`CanonicalSpinSigmaAtoms prov` — a `SpinSigmaAtoms prov` that additionally DISCLOSES, as two fields, that
its `fc`/`B` on a disjoint union `p ⊔ q` ARE the canonical sum constructions:

    fc ⟨p.1.sum q.1, _⟩ = intFundClassSum … (fc p) (fc q)          (`fc_sum`)
    B  ⟨p.1.sum q.1, _⟩ = intH2BasisSum  … (B p)  (B q)            (`B_sum`)

modulo the carrier identification `(p.1.sum q.1).M ≃ ↑p.1.M ⊕ ↑q.1.M`, which is **definitional**
(`SingularManifold.sum_M` is `rfl`, and `sumSpace (TopCat.of A) (TopCat.of B) = TopCat.of (↑A ⊕ ↑B)`), so
the two equations typecheck with no explicit transport.

`CanonicalSpinSigmaAtoms.interMatrixBlockAtom` then DISCHARGES `InterMatrixBlockAtom prov c.toSpinSigmaAtoms`
outright — the block congruence for the canonical construction is `IntCongr.rfl` post the block-diagonal
equality (`intCongr_reindex_interMatrix_disjointSum_blockDiag`). So on the canonical bundle the σ-descent's
additivity plumbing is fully discharged, and `sigThomOfAtoms c.toSpinSigmaAtoms hbord _` needs ONLY the
deep bordism-invariance atom `hbord` (`canonicalSigThom`).

## Honesty of the disclosure (per-field modeling choice; preemptive-strengthening)

`fc_sum`/`B_sum` are NOT "`InterMatrixBlockAtom` by fiat" — they are the strictly *stronger*, genuinely
geometric statement that the fundamental class and `H²`-basis of a disjoint union are the direct-sum
constructions (functoriality of `[M]` under `⊔`; additivity of integral cohomology `Hⁿ(A ⊔ B) ≅ Hⁿ A ×
Hⁿ B`). The block congruence is then *derived* through the real cohomological work of #164 (form-splitting
from cup-pullback multiplicativity + block-basis transport), not assumed. They are disclosed at the same
tier (`discharge_future`) as the flat bundle's `fc`/`B`/`wu`/`pd`, and they are canonical *exactly on
sums* — on non-sum elements the bundle carries its disclosed E1 data unchanged. This is a DATA-carrying
canonical construction, not a fabricated grade (fence `synthetic-grade-ker-bot-nogo`): the `⊔` is a
genuine disjoint union (the carrier's own `sumStr` add-op), distinct from the banned partition/pair-class
routes.

Dimension discipline: `spinEmptyData prov` — CLOSED SPIN 4-manifolds, empty characteristic surface;
integral (co)homology in degrees 2 and 4; the intersection form on `H²(M;ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaStock
import SKEFTHawking.IntersectionMatrixDisjointSumBlockCongr

namespace SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle

variable {k : WithTop ℕ∞}

open scoped Manifold
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
open SKEFTHawking.PinPlusKTSpinSigmaStock

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The canonical-sum disclosure bundle -/

/-- **The canonical-sum `SpinSigmaAtoms` bundle.** A disclosed E1 bundle `SpinSigmaAtoms prov` together
with the two canonical-sum disclosure equations: its integral fundamental class and `H²`-basis on a
disjoint union ARE the direct-sum constructions of the summands' data. The carrier identification
`(p.1.sum q.1).M = ↑p.1.M ⊕ ↑q.1.M` is definitional, so the equations are stated directly against the
`⊔`-slot with no transport.

* `fc_sum` — `[M ⊔ N] = [M] ⊕ [N]` (functoriality of the fundamental class under disjoint union);
* `B_sum` — the `H²(M ⊔ N;ℤ)` basis is the block basis `B_M ⊕ B_N` (integral disjoint-sum additivity of
  cohomology). Its `rank` is then `b₂(M) + b₂(N)` (`intH2BasisSum_rank`).

These are the genuine geometric disclosures the block atom reduces to (§2); on non-sum elements the
underlying `SpinSigmaAtoms` carries its disclosed E1 data unchanged. -/
structure CanonicalSpinSigmaAtoms extends SpinSigmaAtoms prov where
  /-- The fundamental class on a disjoint union is the canonical direct sum `[M ⊔ N] = [M] ⊕ [N]`. -/
  fc_sum : ∀ p q : StrMfd (spinEmptyData prov),
    toSpinSigmaAtoms.fc ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩
      = intFundClassSum (TopCat.of p.1.M) (TopCat.of q.1.M) (toSpinSigmaAtoms.fc p) (toSpinSigmaAtoms.fc q)
  /-- The `H²`-basis on a disjoint union is the canonical block basis `B_M ⊕ B_N`. -/
  B_sum : ∀ p q : StrMfd (spinEmptyData prov),
    toSpinSigmaAtoms.B ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩
      = intH2BasisSum (TopCat.of p.1.M) (TopCat.of q.1.M) (toSpinSigmaAtoms.B p) (toSpinSigmaAtoms.B q)

variable {prov}

/-! ## §2. The block atom, DISCHARGED for the canonical bundle -/

/-- **`InterMatrixBlockAtom` holds for the canonical bundle.** The single geometric residual of the
σ-descent's disjoint-union additivity — the block congruence `interMatrix (p ⊔ q) ≅ blockDiag (interMatrix
p) (interMatrix q)` — is discharged from the disclosure fields via #164's
`intCongr_reindex_interMatrix_disjointSum_blockDiag` (which makes the reindexed sum matrix literally equal
to the block sum, so the congruence is the identity). No longer a hypothesis: on the canonical bundle the
block atom is a THEOREM. -/
theorem CanonicalSpinSigmaAtoms.interMatrixBlockAtom (c : CanonicalSpinSigmaAtoms prov) :
    InterMatrixBlockAtom prov c.toSpinSigmaAtoms := by
  intro p q
  rw [c.fc_sum p q, c.B_sum p q]
  exact ⟨rfl, intCongr_reindex_interMatrix_disjointSum_blockDiag
    (TopCat.of p.1.M) (TopCat.of q.1.M) (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.fc q)
    (c.toSpinSigmaAtoms.B p) (c.toSpinSigmaAtoms.B q)⟩

/-- **σ-additivity FIRES on the canonical bundle** (the `hadd` input, concrete). For the canonical
bundle, the lattice signature of the disjoint-union intersection matrix is the sum of the pieces'
signatures — `σ(M ⊔ N) = σ(M) + σ(N)` — the disjoint-union additivity input of `sigDescend`, now a
THEOREM (via `sigAdditivity_atoms_of_blockCongr` fed by the discharged block atom). The per-piece
even-unimodularity is free from the bundle's own `wu`/`pd`. -/
theorem CanonicalSpinSigmaAtoms.sigma_additive (c : CanonicalSpinSigmaAtoms prov)
    (p q : StrMfd (spinEmptyData prov)) :
    latticeSig (interMatrix (c.toSpinSigmaAtoms.fc ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩)
        (c.toSpinSigmaAtoms.B ⟨p.1.sum q.1, (spinEmptyData prov).sumStr p.2 q.2⟩))
      = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p))
        + latticeSig (interMatrix (c.toSpinSigmaAtoms.fc q) (c.toSpinSigmaAtoms.B q)) :=
  sigAdditivity_atoms_of_blockCongr c.toSpinSigmaAtoms c.interMatrixBlockAtom p q

/-! ## §3. The σ-descent, reduced to `hbord` alone on the canonical bundle -/

/-- **The canonical bundle's Thom signature hom, needing ONLY `hbord`.** With the block atom discharged
(§2), the bordism-invariant signature `Ω → ℤ` is built from the atom bundle plus JUST the deep
bordism-invariance atom `hbord` (Novikov additivity / signature-vanishes-on-boundaries). The elementary
disjoint-union additivity `hadd` is supplied internally by `interMatrixBlockAtom` — nothing else is
needed. This is the sharpest reduction of the σ-descent on the canonical construction: `sig = hbord`
alone. -/
noncomputable def CanonicalSpinSigmaAtoms.sigThom (c : CanonicalSpinSigmaAtoms prov)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p))
        = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc q) (c.toSpinSigmaAtoms.B q))) :
    DataBordismGrp (spinEmptyData prov) →+ ℤ :=
  sigThomOfAtoms c.toSpinSigmaAtoms hbord c.interMatrixBlockAtom

/-- **The canonical Thom hom computes the lattice signature on classes** (`rfl`) — the `sig_eq`
obligation, automatic. So `CanonicalSpinSigmaAtoms.sigThom c hbord` is a drop-in for the flat bundle's
disclosed `sig`, with the disjoint-union additivity plumbing fully discharged and only `hbord` outstanding. -/
@[simp] theorem CanonicalSpinSigmaAtoms.sigThom_mk (c : CanonicalSpinSigmaAtoms prov)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p))
        = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc q) (c.toSpinSigmaAtoms.B q)))
    (p : StrMfd (spinEmptyData prov)) :
    c.sigThom hbord (DataBordismGrp.mk (spinEmptyData prov) p)
      = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p)) :=
  rfl

/-- **The disclosed `sig` field is REDUNDANT on the canonical bundle** — it is *forced* by `hbord`.
Both `c.sig` (the disclosed Thom hom, satisfying `sig_eq`) and `c.sigThom hbord` (built from `hbord` +
the discharged block atom) are `AddMonoidHom`s on `DataBordismGrp = Quot _` that agree on every
generator `[p] = latticeSig (interMatrix (fc p) (B p))`, hence are equal. So on the canonical
construction the σ-presentation's `sig` is not an independent disclosure: it collapses onto the single
deep atom `hbord` (with the elementary additivity fully discharged). -/
theorem CanonicalSpinSigmaAtoms.sig_eq_sigThom (c : CanonicalSpinSigmaAtoms prov)
    (hbord : ∀ p q, IsDataBordant (spinEmptyData prov) p q
      → latticeSig (interMatrix (c.toSpinSigmaAtoms.fc p) (c.toSpinSigmaAtoms.B p))
        = latticeSig (interMatrix (c.toSpinSigmaAtoms.fc q) (c.toSpinSigmaAtoms.B q))) :
    c.toSpinSigmaAtoms.sig = c.sigThom hbord := by
  ext x
  induction x using Quot.ind with | _ p =>
  exact (c.toSpinSigmaAtoms.sig_eq p).trans (c.sigThom_mk hbord p).symm

end SKEFTHawking.PinPlusKTSpinSigmaCanonicalBundle
