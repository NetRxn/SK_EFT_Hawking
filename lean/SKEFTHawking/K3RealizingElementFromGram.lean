/-
# Phase 5q.H — the `pd` disclosure of a K3-REALIZING ELEMENT is redundant

`PinPlusKTSpinSigmaStock.K3RealizingElement` bundles, for the σ = −16 generator slot of the spin
σ-route, a per-element E1 package `pkg : SpinSigmaAtomPkg` — `orient`, `B`, **and `pd`** (integral
Poincaré duality) — *together with* the K3-lattice congruence

  `hk3 : IntCongr (reindex (interMatrix (a.fc g) (a.B g))) SpinSigmaRoute.k3Form`.

Those two disclosures overlap. `IntPDDetCriterion` shows `IntPoincareDuality fc` is exactly "the
integer Gram matrix on the `IntH2Basis` datum is unimodular", and `k3Form` **is** unimodular
(`k3Form_isEvenUnimodular`), a property congruence and reindexing both preserve. So `hk3` already
contains `pd`.

This module makes that explicit:

* `intPoincareDualityOfK3Congr` — `IntPoincareDuality fc` from the K3-lattice congruence alone,
  for any carrier and any rank-22 `IntH2Basis`;
* `k3RealizingElement_of_gram` — a `K3RealizingElement` built from `orient` + `hfc` + `hrank` + `hk3`,
  with **no separately disclosed `pd`**; the package's `pd` field is constructed, not assumed.

Net effect on the σ÷16 row's disclosed-input ledger: the K3 generator slot's three geometric
disclosures (`orient`, `B`, `pd`) drop to two, and the second one (`B`) is taken from the total bundle
`a` rather than re-disclosed. What remains genuinely open at the generator slot is the orientation and
the Gram congruence itself.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaStock
import SKEFTHawking.IntPoincareDualityDetCriterion

namespace SKEFTHawking.K3RealizingElementFromGram

open scoped Manifold
open SKEFTHawking SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTSpinSigmaAtomReduce
open SKEFTHawking.PinPlusKTSpinSigmaStock

noncomputable section

variable {k : WithTop ℕ∞} {X : TopCat}

/-! ## §1. The K3-lattice congruence carries integral Poincaré duality -/

/-- **`IntPoincareDuality` from the K3-lattice congruence.** For any carrier with an `IntH2Basis` of
rank 22, the `hk3`-shaped hypothesis (reindexed Gram matrix `IntCongr` to `SpinSigmaRoute.k3Form`)
delivers the integral-PD datum for the same fundamental class: `k3Form` is unimodular
(`k3Form_isEvenUnimodular.2.1`), and `IntPDDetCriterion.intPoincareDualityOfIntCongr` converts that
through reindexing + congruence into unimodularity of `interMatrix fc B`, hence into the perfect
pairing. -/
def intPoincareDualityOfK3Congr (fc : IntFundamentalClass X) (B : IntH2Basis X) (hrank : B.rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank) (interMatrix fc B)) k3Form) :
    IntPoincareDuality fc :=
  IntPDDetCriterion.intPoincareDualityOfIntCongr fc B hrank k3Form_isEvenUnimodular.2.1 hk3

/-! ## §2. A K3-realizing element WITHOUT a disclosed `pd` -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **A `K3RealizingElement` from the orientation and the Gram congruence alone.** The `pd` field of the
generator's `SpinSigmaAtomPkg` is CONSTRUCTED here by §1 from `hk3`, not disclosed: a caller who has
proved the K3-lattice congruence at the generator slot owes no separate Poincaré-duality datum.

The package's `H²` basis is taken to be the total bundle's own `a.B g` (so `hB` is `rfl`), which is what
`K3RealizingElement.presentationRow` consumes anyway — `spinPresentationRow_of_atoms` is stated against
`a.fc g` / `a.B g`. -/
def k3RealizingElement_of_gram (a : SpinSigmaAtoms prov) (g : StrMfd (spinEmptyData prov))
    [T2Space g.1.M] [Nonempty g.1.M] (orient : IntOrientation g.1.M)
    (hfc : a.fc g = intFundamentalClassOfIntOrientation orient)
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
      (interMatrix (a.fc g) (a.B g))) k3Form) :
    K3RealizingElement a where
  g := g
  pkg :=
    { orient := orient
      B := a.B g
      pd := hfc ▸ intPoincareDualityOfK3Congr (a.fc g) (a.B g) hrank hk3 }
  hfc := hfc
  hB := rfl
  hrank := hrank
  hk3 := hk3

/-- **The `Nonempty` form** — the shape a downstream existence argument consumes: the K3 generator slot
is realized as soon as an orientation and the K3-lattice congruence are in hand. -/
theorem nonempty_k3RealizingElement_of_gram (a : SpinSigmaAtoms prov)
    (g : StrMfd (spinEmptyData prov)) [T2Space g.1.M] [Nonempty g.1.M]
    (orient : IntOrientation g.1.M)
    (hfc : a.fc g = intFundamentalClassOfIntOrientation orient)
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
      (interMatrix (a.fc g) (a.B g))) k3Form) :
    Nonempty (K3RealizingElement a) :=
  ⟨k3RealizingElement_of_gram a g orient hfc hrank hk3⟩

end

end SKEFTHawking.K3RealizingElementFromGram
