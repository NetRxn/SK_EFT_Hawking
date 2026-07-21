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
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_comp)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_cup
  cochainPullbackInt_mem_ker kronecker_cochainPullbackInt coboundary_cochainPullbackInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl seamHomeo mapSimplex_ambIncl)
open SKEFTHawking.SingularRelHomologyInt (chainIncl chainIncl_chainBoundary boundaryExtract
  relCycleLift chainIncl_boundaryExtract chainIncl_injective)
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

/-- **Cochain-pullback flavor bridge (integral).** The cap-side `pullbackCochainInt S` (precompose with
`simplexIncl`) equals the functoriality-side `cochainPullbackInt (ambIncl S)` (precompose with
`mapSimplex`), since `mapSimplex (ambIncl S) = simplexIncl S`. Integral mirror of
`SingularPullbackAmbIncl.pullbackCochain_eq_pullbackCochainMap_ambIncl`; reconciles the seam-adjoint
output with the two-leg cover-sum's `cochainPullbackInt`-flavored cochains. -/
theorem pullbackCochainInt_eq_cochainPullbackInt_ambIncl {X : TopCat} (S : Set ↑X) (k : ℕ)
    (a : SingularCochainInt X k) :
    pullbackCochainInt S k a = cochainPullbackInt (ambIncl S) k a := by
  funext τ
  exact congrArg a (mapSimplex_ambIncl S τ).symm

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

/-- The `A ∩ B = B ∩ A` reassociation as a continuous map `sub(B ∩ A) → sub(A ∩ B)` (identity on the
underlying `X`-point). Unifies leg-A's seam representation `sub(B ∩ A)` with leg-B's `sub(A ∩ B)`. -/
def interCommMap {X : TopCat} (A B : Set ↑X) : C(↑(sub (B ∩ A)), ↑(sub (A ∩ B))) :=
  ⟨fun p => ⟨p.1, Set.mem_inter p.2.2 p.2.1⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- `chainIncl` compatibility of `interCommMap` (identity on `X`-points): reassociation commutes with
inclusion into the ambient. -/
theorem chainIncl_mapChain_interCommMap {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (x : SingularChainInt (sub (B ∩ A)) m) :
    chainIncl (A ∩ B) m (mapChainInt (interCommMap A B) m x) = chainIncl (B ∩ A) m x := by
  rw [← mapChainInt_ambIncl, ← mapChainInt_ambIncl, ← mapChainInt_comp]
  rfl

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

/-- **The unified seam-chain cover relation on `sub(A ∩ B)`.** Transporting leg-A's seam chain `t_A`
through `interCommMap` onto the common seam `sub(A ∩ B)` makes it exactly `−t_B`: the reassociated
A-leg boundary and the B-leg boundary cancel (`∂z = 0`), now as chains of the SAME space. The pairing-
level input to the two-leg seam combination. -/
theorem seam_boundary_cover_neg_inter {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (zA : SingularChainInt (sub A) (m + 1)) (zB : SingularChainInt (sub B) (m + 1))
    (hz_cyc : chainIncl A (m + 1) zA + chainIncl B (m + 1) zB ∈ cycles X (m + 1))
    (hliftB : zB ∈ relCycleLift (restr A B) m) (hliftA : zA ∈ relCycleLift (restr B A) m) :
    mapChainInt (interCommMap A B) m
        (mapChainInt ⟨seamHomeo B A, (seamHomeo B A).continuous⟩ m
          (boundaryExtract (restr B A) m ⟨zA, hliftA⟩))
      = - mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m
          (boundaryExtract (restr A B) m ⟨zB, hliftB⟩) := by
  apply chainIncl_injective (A ∩ B) m
  rw [chainIncl_mapChain_interCommMap, map_neg,
    chainIncl_seam_boundary_cover_neg A B zA zB hz_cyc hliftB hliftA]

/-! ## §B2-capstone. Canonical seam transports and the full MV cup–Stokes seam assembly

The remaining generic (geometry-free) slice: the ONE cochain round-trip atom (a canonical
`sub (A ∩ B)`-representative for each leg cochain, discharging `kronecker_boundary_seam_inter`'s
`hw'` input by construction), and the full seam assembly — the two-leg cover sum collapsed onto a
SINGLE seam pairing `⟨(ι∩)*a ⌣ (u_B|∩ − u_A|∩), t_B⟩` against the transported extracted seam chain. -/

/-- **The canonical `sub (A ∩ B)`-representative of a leg cochain** — pull `w` (a cochain on the
`B`-leg) back to the seam `restr A B ⊆ sub B`, then transport through `seamHomeo⁻¹` onto the
canonical seam `sub (A ∩ B)`. The round-trip below makes this the constructive witness for
`kronecker_boundary_seam_inter`'s `hw'` hypothesis. -/
noncomputable def seamCochainOf {X : TopCat} (A B : Set ↑X) (m : ℕ)
    (w : SingularCochainInt (sub B) m) : SingularCochainInt (sub (A ∩ B)) m :=
  cochainPullbackInt ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩ m
    (pullbackCochainInt (restr A B) m w)

/-- **The cochain round-trip atom**: the canonical seam representative pulls back along `seamHomeo`
to exactly the seam restriction of `w` — `seamHomeo* ∘ (seamHomeo⁻¹)* = id` on cochains
(pullback functoriality + `Homeomorph.symm_apply_apply`). -/
theorem cochainPullbackInt_seamCochainOf {X : TopCat} (A B : Set ↑X) (m : ℕ)
    (w : SingularCochainInt (sub B) m) :
    cochainPullbackInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m (seamCochainOf A B m w)
      = pullbackCochainInt (restr A B) m w := by
  rw [seamCochainOf, cochainPullbackInt_comp]
  have hid : (ContinuousMap.mk _ (seamHomeo A B).symm.continuous).comp
      (ContinuousMap.mk _ (seamHomeo A B).continuous)
        = ContinuousMap.id ↑(sub (restr A B)) :=
    ContinuousMap.ext fun p => (seamHomeo A B).symm_apply_apply p
  rw [hid, cochainPullbackInt_id]

/-- `kronecker_boundary_seam_inter`, discharged at the canonical seam representative: no `hw'`
input — the round-trip atom supplies it. -/
theorem kronecker_boundary_seam_inter' {X : TopCat} (A B : Set ↑X) {m : ℕ}
    (w : SingularCochainInt (sub B) m)
    (zB : SingularChainInt (sub B) (m + 1)) (hlift : zB ∈ relCycleLift (restr A B) m) :
    kronecker w (chainBoundary (sub B) m zB)
      = kronecker (seamCochainOf A B m w) (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ m
          (boundaryExtract (restr A B) m ⟨zB, hlift⟩)) :=
  kronecker_boundary_seam_inter A B w (seamCochainOf A B m w)
    (cochainPullbackInt_seamCochainOf A B m w) zB hlift

/-- The `interCommMap` round-trip: reassociating `A ∩ B → B ∩ A → A ∩ B` is the identity
(both maps are the identity on underlying `X`-points). -/
theorem interCommMap_comp_interCommMap {X : TopCat} (A B : Set ↑X) :
    (interCommMap B A).comp (interCommMap A B) = ContinuousMap.id ↑(sub (B ∩ A)) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

/-- **THE FULL MV CUP–STOKES SEAM ASSEMBLY.** For a cocycle `a` (degree `p`), a cochain `b` whose
restrictions to both cover members are coboundaries (`ι_A* b = δu_A`, `ι_B* b = δu_B`), and a
cover-partitioned CYCLE `z = ι_A zA + ι_B zB`, the `⟨a ⌣ b, z⟩` pairing collapses onto ONE seam
pairing: the `(−1)ᵖ`-weighted pairing of the seam-difference cochain
`(seam transport of ι_B*a ⌣ u_B) − (reassociated seam transport of ι_A*a ⌣ u_A)` against the
transported extracted seam chain `t_B`. Chains the two-leg cover sum, the canonical seam
transports, and the seam-chain cover relation (`∂(ι_A zA) = −∂(ι_B zB)`). -/
theorem kronecker_cup_cover_seam {X : TopCat} (A B : Set ↑X) {p q : ℕ}
    (a : SingularCochainInt X p) (b : SingularCochainInt X (q + 1))
    (ha : coboundaryₗ X p a = 0)
    (uA : SingularCochainInt (sub A) q) (uB : SingularCochainInt (sub B) q)
    (hbA : cochainPullbackInt (ambIncl A) (q + 1) b = coboundaryₗ (sub A) q uA)
    (hbB : cochainPullbackInt (ambIncl B) (q + 1) b = coboundaryₗ (sub B) q uB)
    (zA : SingularChainInt (sub A) (p + (q + 1)))
    (zB : SingularChainInt (sub B) (p + (q + 1)))
    (hz_cyc : chainIncl A (p + (q + 1)) zA + chainIncl B (p + (q + 1)) zB
        ∈ cycles X (p + (q + 1)))
    (hliftB : zB ∈ relCycleLift (restr A B) (p + q))
    (hliftA : zA ∈ relCycleLift (restr B A) (p + q)) :
    kronecker (cup a b) (chainIncl A (p + (q + 1)) zA + chainIncl B (p + (q + 1)) zB)
      = (-1 : ℤ) ^ p *
          kronecker
            (seamCochainOf A B (p + q) (cup (cochainPullbackInt (ambIncl B) p a) uB)
              - cochainPullbackInt (interCommMap B A) (p + q)
                  (seamCochainOf B A (p + q) (cup (cochainPullbackInt (ambIncl A) p a) uA)))
            (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ (p + q)
              (boundaryExtract (restr A B) (p + q) ⟨zB, hliftB⟩)) := by
  set tB := mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ (p + q)
    (boundaryExtract (restr A B) (p + q) ⟨zB, hliftB⟩) with htB
  set wB := cup (cochainPullbackInt (ambIncl B) p a) uB with hwB
  set wA := cup (cochainPullbackInt (ambIncl A) p a) uA with hwA
  -- the two-leg cover sum
  rw [kronecker_cup_cover_twoleg A B a b ha uA uB hbA hbB zA zB]
  -- each leg onto its own canonical seam
  rw [kronecker_boundary_seam_inter' B A wA zA hliftA,
    kronecker_boundary_seam_inter' A B wB zB hliftB]
  -- move the A-leg seam pairing onto `sub (A ∩ B)` via the interComm round-trip + adjunction
  set W := cochainPullbackInt (interCommMap B A) (p + q) (seamCochainOf B A (p + q) wA) with hWdef
  have hround : cochainPullbackInt (interCommMap A B) (p + q) W
      = seamCochainOf B A (p + q) wA := by
    rw [hWdef, cochainPullbackInt_comp, interCommMap_comp_interCommMap, cochainPullbackInt_id]
  have hneg := seam_boundary_cover_neg_inter (m := p + q) A B zA zB hz_cyc hliftB hliftA
  have hAmove : kronecker (seamCochainOf B A (p + q) wA)
      (mapChainInt ⟨seamHomeo B A, (seamHomeo B A).continuous⟩ (p + q)
        (boundaryExtract (restr B A) (p + q) ⟨zA, hliftA⟩))
      = - kronecker W tB := by
    rw [← hround, kronecker_cochainPullbackInt]
    have := congrArg (kronecker W) hneg
    rw [this, htB]
    have hsm : (-(mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ (p + q)
        (boundaryExtract (restr A B) (p + q) ⟨zB, hliftB⟩)))
        = (-1 : ℤ) • mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ (p + q)
            (boundaryExtract (restr A B) (p + q) ⟨zB, hliftB⟩) := (neg_one_smul ℤ _).symm
    rw [hsm, kronecker_smul_right, neg_one_smul]
  rw [hAmove, sub_eq_add_neg, kronecker_add_left,
    show kronecker (-W) tB = -kronecker W tB from by
      rw [show -W = (-1 : ℤ) • W from (neg_one_smul ℤ _).symm, kronecker_smul_left, neg_one_smul]]
  ring

/-! ## §B2-structure. The seam difference in `(ι∩)*a ⌣ d` cocycle form

The assembly's seam cochain is structurally a cup: the ambient cocycle's `A ∩ B` restriction cupped
with the seam difference `d` of the transported leg primitives — and `d` is a COCYCLE (its
coboundary is the difference of the two seam restrictions of `b`, which agree). This is the form
the geometric evaluation (homology-invariance + explicit seam cycles) consumes. -/

/-- `cup` distributes over subtraction on the right (bilinearity unfolding). -/
theorem cup_sub_right' {X : TopCat} {p q : ℕ} (f : SingularCochainInt X p)
    (g h : SingularCochainInt X q) :
    cup f (g - h) = cup f g - cup f h := by
  have hgh : g - h = g + (-1 : ℤ) • h := by rw [neg_one_smul]; ring
  rw [hgh, cup_add_right, cup_smul_right, neg_one_smul, ← sub_eq_add_neg]

/-- `seamCochainOf` commutes with the coboundary (both transports are cochain maps). -/
theorem seamCochainOf_coboundary {X : TopCat} (A B : Set ↑X) (q : ℕ)
    (u : SingularCochainInt (sub B) q) :
    seamCochainOf A B (q + 1) (coboundaryₗ (sub B) q u)
      = coboundaryₗ (sub (A ∩ B)) q (seamCochainOf A B q u) := by
  rw [seamCochainOf, seamCochainOf, pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    pullbackCochainInt_eq_cochainPullbackInt_ambIncl]
  show cochainPullbackInt _ (q + 1) (cochainPullbackInt _ (q + 1) (coboundary (sub B) q u))
    = coboundary (sub (A ∩ B)) q (cochainPullbackInt _ q (cochainPullbackInt _ q u))
  rw [coboundary_cochainPullbackInt, coboundary_cochainPullbackInt]

/-- `seamCochainOf` is multiplicative over `cup`. -/
theorem seamCochainOf_cup {X : TopCat} (A B : Set ↑X) {p q : ℕ}
    (v : SingularCochainInt (sub B) p) (u : SingularCochainInt (sub B) q) :
    seamCochainOf A B (p + q) (cup v u)
      = cup (seamCochainOf A B p v) (seamCochainOf A B q u) := by
  rw [seamCochainOf, seamCochainOf, seamCochainOf,
    pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    cochainPullbackInt_cup, cochainPullbackInt_cup]

/-- **The ambient-pullback collapse through the seam**: the canonical seam transport of the
`B`-leg restriction of an ambient cochain is the plain `A ∩ B` restriction (all three transports
are the identity on underlying `X`-points). -/
theorem seamCochainOf_ambIncl {X : TopCat} (A B : Set ↑X) (m : ℕ) (a : SingularCochainInt X m) :
    seamCochainOf A B m (cochainPullbackInt (ambIncl B) m a)
      = cochainPullbackInt (ambIncl (A ∩ B)) m a := by
  rw [seamCochainOf, pullbackCochainInt_eq_cochainPullbackInt_ambIncl,
    cochainPullbackInt_comp, cochainPullbackInt_comp]
  exact congrArg (fun φ => cochainPullbackInt φ m a) (ContinuousMap.ext fun _ => rfl)

/-- The `A`-leg mirror: the reassociated seam transport of the `A`-leg restriction of an ambient
cochain is again the plain `A ∩ B` restriction. -/
theorem interComm_seamCochainOf_ambIncl {X : TopCat} (A B : Set ↑X) (m : ℕ)
    (a : SingularCochainInt X m) :
    cochainPullbackInt (interCommMap B A) m
        (seamCochainOf B A m (cochainPullbackInt (ambIncl A) m a))
      = cochainPullbackInt (ambIncl (A ∩ B)) m a := by
  rw [seamCochainOf_ambIncl B A m a, cochainPullbackInt_comp]
  exact congrArg (fun φ => cochainPullbackInt φ m a) (ContinuousMap.ext fun _ => rfl)

/-- **The seam difference in cup form**: the cup–Stokes assembly's seam cochain equals
`(ι∩)*a ⌣ d` with `d = (transported u_B) − (reassociated transported u_A)` the seam difference of
the leg primitives. -/
theorem seam_difference_cup_form {X : TopCat} (A B : Set ↑X) {p q : ℕ}
    (a : SingularCochainInt X p)
    (uA : SingularCochainInt (sub A) q) (uB : SingularCochainInt (sub B) q) :
    seamCochainOf A B (p + q) (cup (cochainPullbackInt (ambIncl B) p a) uB)
        - cochainPullbackInt (interCommMap B A) (p + q)
            (seamCochainOf B A (p + q) (cup (cochainPullbackInt (ambIncl A) p a) uA))
      = cup (cochainPullbackInt (ambIncl (A ∩ B)) p a)
          (seamCochainOf A B q uB
            - cochainPullbackInt (interCommMap B A) q (seamCochainOf B A q uA)) := by
  rw [seamCochainOf_cup, seamCochainOf_ambIncl, seamCochainOf_cup,
    cochainPullbackInt_cup, interComm_seamCochainOf_ambIncl, cup_sub_right']

/-- **The seam difference is a COCYCLE**: its coboundary is the difference of the two seam
restrictions of `b`, which agree (`δd = (ι∩)*b − (ι∩)*b = 0`). Makes the assembly's seam cochain a
cup of cocycles, so its Kronecker pairing descends to seam homology. -/
theorem seam_difference_cocycle {X : TopCat} (A B : Set ↑X) {q : ℕ}
    (b : SingularCochainInt X (q + 1))
    (uA : SingularCochainInt (sub A) q) (uB : SingularCochainInt (sub B) q)
    (hbA : cochainPullbackInt (ambIncl A) (q + 1) b = coboundaryₗ (sub A) q uA)
    (hbB : cochainPullbackInt (ambIncl B) (q + 1) b = coboundaryₗ (sub B) q uB) :
    coboundaryₗ (sub (A ∩ B)) q
        (seamCochainOf A B q uB
          - cochainPullbackInt (interCommMap B A) q (seamCochainOf B A q uA)) = 0 := by
  rw [map_sub, ← seamCochainOf_coboundary, ← hbB, seamCochainOf_ambIncl]
  have hcomm : coboundaryₗ (sub (A ∩ B)) q
      (cochainPullbackInt (interCommMap B A) q (seamCochainOf B A q uA))
      = cochainPullbackInt (interCommMap B A) (q + 1)
          (coboundaryₗ (sub (B ∩ A)) q (seamCochainOf B A q uA)) := by
    show coboundary (sub (A ∩ B)) q (cochainPullbackInt (interCommMap B A) q
        (seamCochainOf B A q uA))
      = cochainPullbackInt (interCommMap B A) (q + 1) (coboundary (sub (B ∩ A)) q
          (seamCochainOf B A q uA))
    rw [coboundary_cochainPullbackInt]
  rw [hcomm, ← seamCochainOf_coboundary, ← hbA, interComm_seamCochainOf_ambIncl, sub_self]

/-- **THE MV CUP–STOKES SEAM ASSEMBLY, cup-difference form** — the consumer-facing capstone. For a
cocycle `a`, leg-primitive data for `b`, and a cover-partitioned cycle:
`⟨a ⌣ b, z⟩ = (−1)ᵖ ⟨(ι∩)*a ⌣ d, t_B⟩` with `d` the (COCYCLE) seam difference of the transported
primitives and `t_B` the transported extracted seam chain — whose homology class is `mvDeltaInt [z]`
(`mvDelta_cover_partition`). The full generic peel: the geometric slices supply `a`, the primitives,
and the seam-cycle evaluation. -/
theorem kronecker_cup_cover_seam_cup_form {X : TopCat} (A B : Set ↑X) {p q : ℕ}
    (a : SingularCochainInt X p) (b : SingularCochainInt X (q + 1))
    (ha : coboundaryₗ X p a = 0)
    (uA : SingularCochainInt (sub A) q) (uB : SingularCochainInt (sub B) q)
    (hbA : cochainPullbackInt (ambIncl A) (q + 1) b = coboundaryₗ (sub A) q uA)
    (hbB : cochainPullbackInt (ambIncl B) (q + 1) b = coboundaryₗ (sub B) q uB)
    (zA : SingularChainInt (sub A) (p + (q + 1)))
    (zB : SingularChainInt (sub B) (p + (q + 1)))
    (hz_cyc : chainIncl A (p + (q + 1)) zA + chainIncl B (p + (q + 1)) zB
        ∈ cycles X (p + (q + 1)))
    (hliftB : zB ∈ relCycleLift (restr A B) (p + q))
    (hliftA : zA ∈ relCycleLift (restr B A) (p + q)) :
    kronecker (cup a b) (chainIncl A (p + (q + 1)) zA + chainIncl B (p + (q + 1)) zB)
      = (-1 : ℤ) ^ p *
          kronecker
            (cup (cochainPullbackInt (ambIncl (A ∩ B)) p a)
              (seamCochainOf A B q uB
                - cochainPullbackInt (interCommMap B A) q (seamCochainOf B A q uA)))
            (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ (p + q)
              (boundaryExtract (restr A B) (p + q) ⟨zB, hliftB⟩)) := by
  rw [kronecker_cup_cover_seam A B a b ha uA uB hbA hbB zA zB hz_cyc hliftB hliftA,
    seam_difference_cup_form]

end SKEFTHawking.SphereProdStokesPeel
