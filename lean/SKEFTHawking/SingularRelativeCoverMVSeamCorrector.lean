import Mathlib
import SKEFTHawking.SingularRelativeCoverMVSeam

/-!
# Phase 5q.H close-out — THE SEAM CORRECTOR-BUILDER (the datum's minimal geometric interface)

`SingularRelativeCoverMVSeam.SeamCollarChainDatum` bundles NINE fields to discharge the two
collar-chain residuals `hbd`/`hdetAB`. Of those nine, FIVE are pure bookkeeping about a single
*corrector chain* `p`: the away-error `e` is forced to be the mismatch `cA + cB - p`; the error
support `E` is forced to be the complement of the overlap `CA ∩ CB`; the chain-level agreement
`hcongr`, the membership `he`, and the overlap-avoidance `hE` are then all automatic.

This module names that reduction. **`SeamCollarChainDatum.ofCorrector`** builds the full datum from
exactly the FOUR genuinely-geometric facts about the corrector `p`:

* `hpS` — `∂p ∈ C(∂W)` (the collar chain's boundary is a boundary-chain);
* `heS` — `∂(cA + cB - p) ∈ C(∂W)` (the mismatch's boundary is a boundary-chain);
* `hp_det` — `p` detects the local generator at every overlap point off `∂W`;
* `hagree` — the mismatch `cA + cB - p` is supported OFF the overlap `CA ∩ CB`.

So inhabiting the seam datum reduces to producing one chain `p` with these four properties — the
minimal geometric shape of the collar-chain construction (a Mayer–Vietoris partition of the glued
relative-fundamental chain into a seam-detecting rel-cycle `p` and an away rel-cycle `e`). The
companion **`heS_of_hbd`** trades `heS` for the mod-2 seam-cancellation `hbd` (`∂(cA+cB) ∈ C(∂W)`)
plus `hpS`, and **`ofCorrector_ofHbd`** is the builder phrased with `hbd` in place of `heS`.

**Fences.** No collar chain is constructed here — `p` remains a supplied input (THE COLLAR FORK is
respected). This is pure chain-algebra bookkeeping that sharpens the datum's interface; the genuine
geometric residual (a corrector chain `p` with the four facts) is untouched. All statements are
generic in `X`, `S`, the cores, and the degree.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport

namespace SKEFTHawking.SingularRelativeCoverMVSeam

variable {X : TopCat}

/-- **The mismatch's boundary is a boundary-chain, from the seam-cancellation.** `∂(cA + cB - p) ∈
C(∂W)` follows from the mod-2 seam-cancellation `hbd : ∂(cA + cB) ∈ C(∂W)` and the collar chain's
`hpS : ∂p ∈ C(∂W)` — because `∂` is linear and `C(∂W)` is a submodule. This lets a corrector provider
supply the (typically already-available) `hbd` in place of the mismatch fact `heS`. -/
theorem heS_of_hbd {S : Set ↑X} (m : ℕ) {cA cB p : SingularChain X (m + 2)}
    (hbd : chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains S (m + 1))
    (hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1)) :
    chainBoundary X (m + 1) (cA + cB - p) ∈ subspaceChains S (m + 1) := by
  rw [map_sub]
  exact Submodule.sub_mem _ hbd hpS

/-- **The seam collar-decomposition datum, built from a corrector chain `p`.** Discharges the five
bookkeeping fields of `SeamCollarChainDatum` — the away-error `e := cA + cB - p`, the error support
`E := (CA ∩ CB)ᶜ`, the agreement `hcongr`, the membership `he`, and the overlap-avoidance `hE` — from
the FOUR genuinely-geometric facts about the corrector chain `p`. This is the minimal geometric
interface for inhabiting the seam datum: produce one chain `p` with boundary in `∂W`, mismatch
boundary in `∂W`, seam detection, and mismatch supported off the overlap. -/
noncomputable def SeamCollarChainDatum.ofCorrector {S CA CB : Set ↑X} {m : ℕ}
    {cA cB p : SingularChain X (m + 2)}
    (hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1))
    (heS : chainBoundary X (m + 1) (cA + cB - p) ∈ subspaceChains S (m + 1))
    (hagree : cA + cB - p ∈ subspaceChains (CA ∩ CB)ᶜ (m + 2))
    (hp_det : ∀ (x : ↑X) (hx : x ∉ S), x ∈ CA → x ∈ CB →
      relClassOf ({x}ᶜ) m p
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hpS) ≠ 0) :
    SeamCollarChainDatum S CA CB m cA cB where
  p := p
  e := cA + cB - p
  E := (CA ∩ CB)ᶜ
  hcongr := by abel
  he := hagree
  hE := fun x hxA hxB h => h ⟨hxA, hxB⟩
  hpS := hpS
  heS := heS
  hp_det := hp_det

/-- **The seam collar-decomposition datum, built from a corrector chain `p` with the seam-cancellation
supplied directly.** Identical to `ofCorrector` but takes the mod-2 seam-cancellation
`hbd : ∂(cA + cB) ∈ C(∂W)` in place of the mismatch-boundary fact `heS` (derived via `heS_of_hbd`). -/
noncomputable def SeamCollarChainDatum.ofCorrector_ofHbd {S CA CB : Set ↑X} {m : ℕ}
    {cA cB p : SingularChain X (m + 2)}
    (hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1))
    (hbd : chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains S (m + 1))
    (hagree : cA + cB - p ∈ subspaceChains (CA ∩ CB)ᶜ (m + 2))
    (hp_det : ∀ (x : ↑X) (hx : x ∉ S), x ∈ CA → x ∈ CB →
      relClassOf ({x}ᶜ) m p
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hpS) ≠ 0) :
    SeamCollarChainDatum S CA CB m cA cB :=
  SeamCollarChainDatum.ofCorrector hpS (heS_of_hbd m hbd hpS) hagree hp_det

end SKEFTHawking.SingularRelativeCoverMVSeam
