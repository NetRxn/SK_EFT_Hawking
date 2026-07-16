import Mathlib
import SKEFTHawking.SingularRelativeCoverMVTransport

/-!
# Phase 5q.H close-out — THE SEAM COLLAR-DECOMPOSITION LAYER (the two collar-chain residuals)

The cover-MV glue of a handle-attachment carrier reduces the connected `[W,∂W]` witness to two
core-supported chains `cA` (cylinder side) and `cB` (handle side) plus two residual atoms on their
pushed sum:

* **`hbd`** — the mod-2 seam-cancellation: `∂(cA + cB) ∈ C(∂W)`;
* **`hdetAB`** — the overlap straddle detection: `[cA + cB]` is locally nonzero at every overlap
  (seam-collar) point.

**Why these two are NOT chain-level trivial (the honest adjudication).** `cA`/`cB` are pushforwards
of two INDEPENDENTLY-chosen detecting chains (each a `.choose` representative of a relative
fundamental class — the cylinder engine's `exists_cylinder_detecting_chain` and the disk's relative
fundamental class). Their seam boundary faces are not literally equal, so `∂(cA + cB)` carries a
mod-2 seam mismatch that is NOT in `∂W` for arbitrary representatives: `hbd` genuinely needs a
CORRECTOR. This is the `#159` homologous-mismatch absorption — the seam mismatch is a degree-`m+1`
cycle in the seam zone, and (the seam zone being a collar `Σ ≃ S_att × I` by the `SeamCollarDatum`)
it bounds a collar `(m+2)`-chain, the corrector.

**The honest reduction (this module).** Both atoms reduce to a single **collar-decomposition datum**:
a collar product chain `p` and an away-error `e` with `cA + cB = p + e`, where `p` and `e` each have
`∂ ∈ C(∂W)` (giving `hbd`), `e` is supported off the overlap (giving the congruence at overlap
points), and `p` detects locally at overlap points (giving `hdetAB` via `relClassOf_ne_zero_of_congr`).
Each field is a genuine geometric atom about a concrete chain — the collar product chain the
`SeamCollarDatum` supplies by construction, and the "both pieces restrict to the same collar class"
agreement realized at the chain level. None is a completeness Prop; none demands detection at a
closed piece's frontier (the banned partition route).

**Fences.** No general collar theorem: the collar chain `p` is a supplied datum (the `S_att`-side
chain × the interval), never a theorem. THE COLLAR FORK is respected. All statements are generic in
`X`, `S`, the cores, degree — the capstone lane instantiates them once.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport

namespace SKEFTHawking.SingularRelativeCoverMVSeam

variable {X : TopCat}

/-! ## §1. The two chain-level reduction lemmas (generic). -/

/-- **The seam-cancellation from a collar decomposition** (the reduction of `hbd`). If the glued
chain decomposes as `cA + cB = p + e` with the collar chain `p` and the away-error `e` each having
`∂ ∈ C(S)`, then `∂(cA + cB) ∈ C(S)` — the mod-2 seam-cancellation. The corrector `p` absorbs the
seam mismatch (`#159`): `∂(cA + cB) = ∂p + ∂e`, both `S`-chains. -/
theorem hbd_of_collar_decomp {S : Set ↑X} (m : ℕ) {cA cB p e : SingularChain X (m + 2)}
    (hcongr : cA + cB = p + e)
    (hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1))
    (heS : chainBoundary X (m + 1) e ∈ subspaceChains S (m + 1)) :
    chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains S (m + 1) := by
  rw [hcongr, map_add]
  exact Submodule.add_mem _ hpS heS

/-- **The overlap straddle detection from a collar decomposition** (the reduction of `hdetAB`). At an
overlap-zone point `x ∉ S` off the error's support `E`, the glued chain's local class equals the
collar chain's local class (the away-error `e` dies), so it is nonzero whenever the collar chain
detects. This is `relClassOf_ne_zero_of_congr` specialised to `T = {x}ᶜ` — the chain-level
"the glued chain detects at the overlap because the collar product chain does". -/
theorem hdetAB_of_collar_decomp {S E : Set ↑X} (m : ℕ) {cA cB p e : SingularChain X (m + 2)}
    (hcongr : cA + cB = p + e) (he : e ∈ subspaceChains E (m + 2))
    (hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1))
    {x : ↑X} (hx : x ∉ S) (hxE : x ∉ E)
    (hcAB : chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains ({x}ᶜ) (m + 1))
    (hp_det : relClassOf ({x}ᶜ) m p
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hpS) ≠ 0) :
    relClassOf ({x}ᶜ) m (cA + cB) hcAB ≠ 0 :=
  relClassOf_ne_zero_of_congr (Set.subset_compl_singleton_iff.mpr hxE) m hcongr he hcAB
    (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hpS) hp_det

/-! ## §2. The collar-decomposition datum — the sharp seam residual. -/

/-- **The seam collar-decomposition datum** for a glued sum `cA + cB` at the pair `(X, S)` with cores
`CA`/`CB`. Bundles the honest geometric content of the seam agreement: a collar product chain `p`
(the `SeamCollarDatum`'s `S_att`-side chain × the collar interval), an away-error `e` supported off
the overlap, the chain-level agreement `cA + cB = p + e`, the two boundary-in-`S` facts, and the
collar chain's local detection at every overlap point. From it BOTH `hbd` and `hdetAB` are produced
(§3). Each field is a concrete-chain geometric atom; none is a completeness Prop, and no field
demands detection at a closed piece's frontier. -/
structure SeamCollarChainDatum (S CA CB : Set ↑X) (m : ℕ)
    (cA cB : SingularChain X (m + 2)) where
  /-- the collar product chain (the corrector — `S_att`-side chain × the collar interval). -/
  p : SingularChain X (m + 2)
  /-- the away-error chain (off the overlap). -/
  e : SingularChain X (m + 2)
  /-- the error's support set — avoids the overlap `CA ∩ CB`. -/
  E : Set ↑X
  /-- **the chain-level seam agreement**: the glued chain is the collar chain up to the away-error. -/
  hcongr : cA + cB = p + e
  /-- the away-error is supported in `E`. -/
  he : e ∈ subspaceChains E (m + 2)
  /-- `E` avoids the overlap: every point of `CA ∩ CB` is off `E` (so `e` dies at overlap points). -/
  hE : ∀ x : ↑X, x ∈ CA → x ∈ CB → x ∉ E
  /-- the collar chain's boundary is an `S`-chain (half the seam-cancellation). -/
  hpS : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1)
  /-- the away-error's boundary is an `S`-chain (the other half of the seam-cancellation). -/
  heS : chainBoundary X (m + 1) e ∈ subspaceChains S (m + 1)
  /-- the collar chain detects the local generator at every overlap-zone point off `S`. -/
  hp_det : ∀ (x : ↑X) (hx : x ∉ S), x ∈ CA → x ∈ CB →
    relClassOf ({x}ᶜ) m p
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hpS) ≠ 0

namespace SeamCollarChainDatum

variable {S CA CB : Set ↑X} {m : ℕ} {cA cB : SingularChain X (m + 2)}

/-- **The seam-cancellation `hbd`, produced from the datum.** -/
theorem hbd (D : SeamCollarChainDatum S CA CB m cA cB) :
    chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains S (m + 1) :=
  hbd_of_collar_decomp m D.hcongr D.hpS D.heS

/-- **The overlap straddle detection `hdetAB`, produced from the datum.** At every overlap point off
`S`, the glued chain's local class is nonzero — because the collar chain detects there and the
away-error dies. -/
theorem hdetAB (D : SeamCollarChainDatum S CA CB m cA cB)
    (x : ↑X) (hx : x ∉ S) (hxA : x ∈ CA) (hxB : x ∈ CB) :
    relClassOf ({x}ᶜ) m (cA + cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd) ≠ 0 :=
  hdetAB_of_collar_decomp m D.hcongr D.he D.hpS hx (D.hE x hxA hxB)
    (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd)
    (D.hp_det x hx hxA hxB)

end SeamCollarChainDatum

end SKEFTHawking.SingularRelativeCoverMVSeam
