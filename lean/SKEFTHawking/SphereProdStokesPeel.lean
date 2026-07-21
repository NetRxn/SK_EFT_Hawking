/-
# Phase 5q.H — the single-subspace signed cup–Stokes atom (hcross MV-peel reusable core)

The reusable arithmetic core of the S²×S² Eilenberg–Zilber cross-value peel (`hcross`, the deferred
Künneth residual reducing `SphereProdGramPinReduce.sphereProdGramPin_of_cross_of_basisId` to the
S²×S² Gram pin): the "one leg" of the codex-adjudicated class-level Mayer–Vietoris cup–Stokes lemma.

For a cocycle `a`, a cochain `b` whose restriction `φ*b` to a subspace-inclusion `φ : W → X` is a
coboundary `δu`, and a chain `zW` in `W`, the Kronecker pairing of `a ⌣ b` against the pushforward
`φ₊ zW` collapses onto a boundary pairing living on `W`:

  `⟨a ⌣ b, φ₊ zW⟩ = (−1)ᵖ ⟨φ*a ⌣ u, ∂ zW⟩`.

Derivation — all four steps banked:
* pullback adjunction `⟨φ*c, z⟩ = ⟨c, φ₊ z⟩` (`kronecker_cochainPullbackInt`);
* pullback–cup naturality `φ*(a ⌣ b) = φ*a ⌣ φ*b` (`cochainPullbackInt_cup`);
* the signed cup Leibniz `δ(φ*a ⌣ u) = (−1)ᵖ (φ*a ⌣ δu)` (`cup_coboundary_right`, with `φ*a` a
  cocycle via `cochainPullbackInt_mem_ker`);
* the Kronecker coboundary–boundary adjunction `⟨δf, z⟩ = ⟨f, ∂z⟩`
  (`kronecker_coboundary_chainBoundary`).

Both legs of the full MV cup–Stokes peel (the polar-cover `A₀`-leg and `B₀`-leg of the first
`S²` factor) are instances of this atom; their `(−1)ᵖ`-weighted difference over the shared seam is
the `⟨a|∩ ⌣ (u_B − u_A), MV∂[z]⟩` seam pairing that pins the cross value. This module ships the
generic, geometry-free atom; the seam assembly (`A₀,B₀` polar cover of `S²`, the `S²×S¹` seam and its
`TorusCrossPeel.kronecker_cup_snd_torCross` right-peel, and the `SphereProdHFourInt`
`coverInterHThreeEquivInt ∘ mvDeltaInt` H₄ pin) is the remaining geometric build.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCupInt
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularCohomologyFunctorialityInt
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularRelativeCapHadjInt
import SKEFTHawking.SingularMvDeltaPartitionInt
import SKEFTHawking.SingularSeamTransportInt

namespace SKEFTHawking.SphereProdStokesPeel

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt (mapChainInt)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_cup
  cochainPullbackInt_mem_ker kronecker_cochainPullbackInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl seamHomeo)
open SKEFTHawking.SingularRelHomologyInt (chainIncl chainIncl_chainBoundary boundaryExtract
  relCycleLift chainIncl_boundaryExtract)
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)
open SKEFTHawking.SingularCapChainInclInt (pullbackCochainInt)
open SKEFTHawking.SingularRelativeCapHadjInt (kronecker_chainIncl_eq_pullbackCochainInt)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSeamTransportInt (chainIncl_mapChain_seamHomeoInt)

/-- **The single-subspace signed cup–Stokes atom.** For a cocycle `a` (degree `p`), a cochain `b`
(degree `q+1`) whose pullback along `φ : W → X` is a coboundary `φ*b = δu`, and a chain `zW` in `W`:
`⟨a ⌣ b, φ₊ zW⟩ = (−1)ᵖ ⟨φ*a ⌣ u, ∂ zW⟩`. The reusable core of the MV cup–Stokes peel: the
`a ⌣ b` pairing against the `φ`-image of a chain collapses to a boundary pairing on `W`, discharged
by the four banked naturalities (pullback adjunction, pullback–cup, signed cup Leibniz, Kronecker
coboundary–boundary adjunction). -/
theorem kronecker_cup_stokes_leg {X W : TopCat} (φ : C(↑W, ↑X)) {p q : ℕ}
    (a : SingularCochainInt X p) (b : SingularCochainInt X (q + 1))
    (ha : coboundaryₗ X p a = 0)
    (u : SingularCochainInt W q)
    (hbu : cochainPullbackInt φ (q + 1) b = coboundaryₗ W q u)
    (zW : SingularChainInt W (p + (q + 1))) :
    kronecker (cup a b) (mapChainInt φ (p + (q + 1)) zW)
      = (-1 : ℤ) ^ p * kronecker (cup (cochainPullbackInt φ p a) u)
          (chainBoundary W (p + q) zW) := by
  have hφa : coboundaryₗ W p (cochainPullbackInt φ p a) = 0 :=
    LinearMap.mem_ker.mp (cochainPullbackInt_mem_ker φ ⟨a, LinearMap.mem_ker.mpr ha⟩)
  have hleib := cup_coboundary_right (cochainPullbackInt φ p a) u hφa
  rw [← kronecker_cochainPullbackInt φ (cup a b) zW, cochainPullbackInt_cup, hbu,
    ← kronecker_coboundary_chainBoundary,
    show coboundary W (p + q) (cup (cochainPullbackInt φ p a) u)
      = coboundaryₗ W (p + q) (cup (cochainPullbackInt φ p a) u) from rfl,
    hleib, kronecker_smul_left, smul_eq_mul, ← mul_assoc,
    show ((-1 : ℤ) ^ p * (-1 : ℤ) ^ p) = 1 from by rw [← mul_pow]; norm_num, one_mul]

/-- **The two-leg cover sum of the cup–Stokes atom.** For a cocycle `a`, a cochain `b` whose
restrictions to the two members `A, B` of a cover are coboundaries (`ι_A* b = δu_A`, `ι_B* b = δu_B`),
and a cover-partitioned chain `z = ι_A zA + ι_B zB`, the `a ⌣ b` pairing against `z` collapses to the
`(−1)ᵖ`-weighted SUM of the two boundary pairings, one per leg. Two instances of
`kronecker_cup_stokes_leg` glued over the partition via the `chainIncl = mapChainInt ∘ ambIncl`
bridge. The pre-seam form of the MV cup–Stokes peel. -/
theorem kronecker_cup_cover_twoleg {X : TopCat} (A B : Set ↑X) {p q : ℕ}
    (a : SingularCochainInt X p) (b : SingularCochainInt X (q + 1))
    (ha : coboundaryₗ X p a = 0)
    (uA : SingularCochainInt (sub A) q) (uB : SingularCochainInt (sub B) q)
    (hbA : cochainPullbackInt (ambIncl A) (q + 1) b = coboundaryₗ (sub A) q uA)
    (hbB : cochainPullbackInt (ambIncl B) (q + 1) b = coboundaryₗ (sub B) q uB)
    (zA : SingularChainInt (sub A) (p + (q + 1)))
    (zB : SingularChainInt (sub B) (p + (q + 1))) :
    kronecker (cup a b) (chainIncl A (p + (q + 1)) zA + chainIncl B (p + (q + 1)) zB)
      = (-1 : ℤ) ^ p *
          (kronecker (cup (cochainPullbackInt (ambIncl A) p a) uA)
              (chainBoundary (sub A) (p + q) zA)
            + kronecker (cup (cochainPullbackInt (ambIncl B) p a) uB)
              (chainBoundary (sub B) (p + q) zB)) := by
  rw [kronecker_add_right, ← mapChainInt_ambIncl, ← mapChainInt_ambIncl,
    kronecker_cup_stokes_leg (ambIncl A) a b ha uA hbA zA,
    kronecker_cup_stokes_leg (ambIncl B) a b ha uB hbB zB, mul_add]

/-- **Cochain-pullback functoriality (composition).** `φ*(ψ*a) = (ψ ∘ φ)*a`. -/
theorem cochainPullbackInt_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochainInt Z n) :
    cochainPullbackInt φ n (cochainPullbackInt ψ n a) = cochainPullbackInt (ψ.comp φ) n a := by
  funext σ; rfl

/-- **Cochain-pullback functoriality (identity).** `(id)*a = a`. -/
theorem cochainPullbackInt_id {X : TopCat} (n : ℕ) (a : SingularCochainInt X n) :
    cochainPullbackInt (ContinuousMap.id ↑X) n a = a := by
  funext σ; rfl

/-- **The single-leg seam restriction of a boundary pairing.** If `zB`'s boundary is supported on the
seam `A ∩ B` (realized as `restr A B ⊆ sub B` via `relCycleLift`), pairing any cochain `w` on `sub B`
against `∂zB` equals pairing the seam-restriction `ι_∩* w` against the extracted seam chain
`∂zB|∩ = boundaryExtract (restr A B) ⟨zB⟩`. The `chainIncl_boundaryExtract` reversal + the
`chainIncl`–pullback Kronecker adjoint. -/
theorem kronecker_boundary_seam {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (w : SingularCochainInt (sub B) m)
    (zB : SingularChainInt (sub B) (m + 1)) (hlift : zB ∈ relCycleLift (restr A B) m) :
    kronecker w (chainBoundary (sub B) m zB)
      = kronecker (pullbackCochainInt (restr A B) m w)
          (boundaryExtract (restr A B) m ⟨zB, hlift⟩) := by
  rw [← chainIncl_boundaryExtract (restr A B) m ⟨zB, hlift⟩,
    kronecker_chainIncl_eq_pullbackCochainInt]

/-- **The single-leg boundary pairing transported to the canonical seam `sub(A ∩ B)`.** Given a cochain
`w'` on `sub(A ∩ B)` whose `seamHomeo`-pullback matches the seam-restriction of `w` (`hw'`), the boundary
pairing of `w` against `∂zB` equals the pairing of `w'` against the `seamHomeo`-transported extracted
seam chain `tB = seamHomeo₊ (∂zB|∩)` — the representative `mvDeltaInt` uses. Bridges the `restr A B`
seam representation (`kronecker_boundary_seam`) to the `A ∩ B` one (`coverInterHThreeEquivInt`,
`mvDelta_cover_partition`) via the Kronecker–pullback adjoint through the seam homeomorphism. -/
theorem kronecker_boundary_seam_inter {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (w : SingularCochainInt (sub B) m) (w' : SingularCochainInt (sub (A ∩ B)) m)
    (hw' : cochainPullbackInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m w'
        = pullbackCochainInt (restr A B) m w)
    (zB : SingularChainInt (sub B) (m + 1)) (hlift : zB ∈ relCycleLift (restr A B) m) :
    kronecker w (chainBoundary (sub B) m zB)
      = kronecker w' (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m
          (boundaryExtract (restr A B) m ⟨zB, hlift⟩)) := by
  rw [kronecker_boundary_seam A B w zB hlift, ← hw', kronecker_cochainPullbackInt]

/-- **The seam-chain cover relation** — the mathematical heart of the MV cup–Stokes seam assembly.
For a cover-partitioned cycle `z = ι_A zA + ι_B zB`, the two `seamHomeo`-transported extracted seam
chains — leg-A's `t_A = seamHomeo(B,A)₊ (∂zA|∩)` in `sub(B ∩ A)` and leg-B's `t_B = seamHomeo(A,B)₊
(∂zB|∩)` in `sub(A ∩ B)` — realize, under `chainIncl` to the ambient `X`, to `∂(ι_A zA)` and
`∂(ι_B zB)` respectively, which are negatives of one another (`∂z = 0`). Chains
`chainIncl_mapChain_seamHomeoInt` + `chainIncl_boundaryExtract` + `chainIncl_chainBoundary` per leg,
then the cycle condition. -/
theorem chainIncl_seam_boundary_cover_neg {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (zA : SingularChainInt (sub A) (m + 1)) (zB : SingularChainInt (sub B) (m + 1))
    (hz_cyc : chainIncl A (m + 1) zA + chainIncl B (m + 1) zB ∈ cycles X (m + 1))
    (hliftB : zB ∈ relCycleLift (restr A B) m) (hliftA : zA ∈ relCycleLift (restr B A) m) :
    chainIncl (B ∩ A) m (mapChainInt ⟨seamHomeo B A, (seamHomeo B A).continuous⟩ m
        (boundaryExtract (restr B A) m ⟨zA, hliftA⟩))
      = - chainIncl (A ∩ B) m (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m
          (boundaryExtract (restr A B) m ⟨zB, hliftB⟩)) := by
  rw [chainIncl_mapChain_seamHomeoInt, chainIncl_mapChain_seamHomeoInt,
    chainIncl_boundaryExtract, chainIncl_boundaryExtract, chainIncl_chainBoundary,
    chainIncl_chainBoundary, eq_neg_iff_add_eq_zero, ← map_add]
  exact LinearMap.mem_ker.mp hz_cyc

end SKEFTHawking.SphereProdStokesPeel
