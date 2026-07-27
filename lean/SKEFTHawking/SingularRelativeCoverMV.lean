import Mathlib
import SKEFTHawking.SingularMayerVietoris
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.SingularRelativeDisjointUnionDetectInterior

/-!
# Phase 5q.H — THE RELATIVE COVER-MV GLUING LAYER (chain-level two-piece glue for `[W,∂W]`)

The connected capstone's `hasClass` atom needs a **two-piece gluing** of a relative fundamental
class: `W = (cyl-side) ∪ (handle-side)`, the pieces overlapping on the seam collar. The banned
binary-partition route (`capstone-binary-partition-detection-uninhabitable`, SETTLED_FORKS
2026-07-16) failed because it demanded per-piece detection at the *frontier* of a closed piece,
where the piece's boundary-face local homology vanishes.

**Why per-piece pair classes cannot carry the glue — ⚠ CORRECTED 2026-07-27, THE OPEN HALF OF THIS
CLAIM WAS WRONG.**

*The closed half stands.* For a *proper closed* piece `P ⊊ W` the pair `(P, S∩P)` takes the top
relative homology of a compact manifold-with-boundary relative to a **proper part** of its boundary
(the seam face is missing), which vanishes. That is the content kernel-encoded as
`capstone-binary-partition-detection-uninhabitable` (`KERNEL_NOGO_REGISTRY`, promoted 2026-07-27),
backed by `PinPlusTraceCapstoneCollarPairSeamLocalHom.not_restrictsToRelGenOn_cylRange_at_seamCore`.

*The open half was an OVERREACH and is retracted.* The former text argued: "for an *open* piece `P`,
singular chains have compact image, so no class of `(P, S∩P)` can restrict to the local generator at
every point of the noncompact `P`. Either way the summand is `0` or fails detection — **for EVERY
class**." The premise is true; **the conclusion does not follow**, and the route it declared
structurally empty is now BUILT:
`SingularRelativeCoverMVSumExact.exists_excisionMap_add_of_overlap_relAcyclic` proves exactly
`relClassOf S m z hz = excisionMap S A α + excisionMap S B β` under an honest open cover
(`⋃ interior = univ`) plus a relatively-acyclic overlap — kernel-pure, zero hypotheses beyond those.

**Where the old argument goes wrong** (lead-verified, 2026-07-27): the open route never asks `α_A` to
detect at *every* point of `A`. In the glued sum the `B`-term dies on `A ∖ B`, so `α_A` only has to
detect there — and `A ∖ B` is closed in a **compact** `W`, hence compact, which a compact-support
chain handles fine. "No single class detects everywhere on a noncompact piece" and "the decomposition
is empty" are different statements; the former does not imply the latter.

⚙ **Process note, recorded because it cost a route.** This clause read as a settled structural
impossibility and would have deterred the very construction the `SETTLED_FORKS` entry named as *the
live route*. A claim of the form "for EVERY class" is a no-go-strength assertion and belongs in
`KERNEL_NOGO_REGISTRY` with a backing theorem, or it should be written with the hedging its evidence
supports — not asserted in a module header where it silently fences future work.

The chain-level gluing described below remains correct and useful; it is simply not the *only*
route.

**The glue datum (`RelCoverGlueData`).** Two closed cores `CA ∪ CB = W` and two chains `cA`
(supported in `CA`), `cB` (supported in `CB`) with `∂(cA + cB) ∈ C(S)` — the seam-cancellation.
The sum is then a genuine relative cycle and `glueClass ∈ Hₙ(X, S)` exists with NO exactness
machinery. Detection splits by zone:

* `x ∉ CB` (the `A`-only zone): the `cB`-term dies (`C(CB) ⊆ C({x}ᶜ)`), so the restriction is the
  local class of `cA` alone — dischargeable from the piece's own (cylinder-side) data;
* `x ∉ CA`: symmetric;
* `x ∈ CA ∩ CB` (the overlap/collar zone): the restriction is the local class of the full
  `cA + cB`, and the congruence helper (`relClassOf_eq_of_congr`) reduces it to the local class of
  a single **collar product chain** `p` once `cA + cB = p + e` with `e` supported away from the
  overlap — the "both restrict to the same collar class" agreement, realized chain-level.

Nonvanishing normalizes to the generator by the `ℤ/2` two-element absorb
(`eq_linearEquiv_symm_one_of_ne_zero`), and intrinsic (in-piece) nonvanishing transports to the
ambient local class through excision at any point of the piece's **interior**
(`relClassOf_chainIncl_ne_zero_of_interior`, reusing the banked per-point excision cover of
`SingularRelativeDisjointUnionDetectInterior`). All statements are generic in `X`, `S`, degree —
both the connected-capstone lane and the disconnected-cylinder lane can consume them.

**Fences.** This is categorically NOT the banned binary-partition route: no detection is ever
demanded at a closed piece's frontier (the overlap zone carries its own straddle detection, and
the one-sided zones satisfy `x ∉ other core` ⟹ off-piece death). No general collar theorem is
invoked; the collar enters only through whichever concrete chain the consumer supplies.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeDisjointUnionDetectInterior

namespace SKEFTHawking.SingularRelativeCoverMV

variable {X : TopCat}

/-! ## §1. The relative class of an almost-cycle (a chain with `S`-small boundary) -/

/-- **The relative cycle of an almost-cycle**: an absolute chain `c` whose absolute boundary is a
`T`-subspace chain defines a relative cycle of the pair `(X, T)`. This is the chain-level entry
point of the gluing layer — classes are produced directly from chains, so boundary cancellations
between pieces (invisible at the homology level of the pieces) can be exploited. -/
noncomputable def relCycleOf (T : Set ↑X) (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1)) : relCycles T (m + 2) :=
  ⟨RelativeChain.mk T (m + 2) c, by
    show RelativeChain.mk T (m + 2) c ∈ LinearMap.ker (relBoundary T (m + 1))
    rw [LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
    exact hc⟩

/-- **The relative homology class of an almost-cycle.** -/
noncomputable def relClassOf (T : Set ↑X) (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1)) : RelativeHomology T (m + 2) :=
  RelativeHomology.mk T (m + 2) (relCycleOf T m c hc)

/-- `relClassOf` is additive in the chain (each summand an almost-cycle). -/
theorem relClassOf_add (T : Set ↑X) (m : ℕ) (c d : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1))
    (hd : chainBoundary X (m + 1) d ∈ subspaceChains T (m + 1)) :
    relClassOf T m (c + d) (by rw [map_add]; exact Submodule.add_mem _ hc hd)
      = relClassOf T m c hc + relClassOf T m d hd := by
  show RelativeHomology.mk T (m + 2) _ = RelativeHomology.mk T (m + 2) _ + RelativeHomology.mk T (m + 2) _
  rw [show relCycleOf T m (c + d) (by rw [map_add]; exact Submodule.add_mem _ hc hd)
      = relCycleOf T m c hc + relCycleOf T m d hd from Subtype.ext rfl]
  rfl

/-- **Off-piece death**: the class of an almost-cycle supported in a subspace `B ⊆ T` vanishes —
its representing chain is already a `T`-subspace chain. The chain-level twin of
`restrictBd_excisionMap_eq_zero`; with `T = {x}ᶜ` and `B` the *other* core it kills the off-piece
summand at every point outside that core. -/
theorem relClassOf_eq_zero_of_subspace {T B : Set ↑X} (hBT : B ⊆ T) (m : ℕ)
    (c : SingularChain X (m + 2)) (hcB : c ∈ subspaceChains B (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1)) :
    relClassOf T m c hc = 0 := by
  have hz : relCycleOf T m c hc = 0 := Subtype.ext (by
    show RelativeChain.mk T (m + 2) c = 0
    rw [RelativeChain.mk_eq_zero_iff]
    exact subspaceChains_mono hBT (m + 2) hcB)
  rw [relClassOf, hz]
  exact Submodule.Quotient.mk_zero _

/-- **Inclusion-of-pairs acts on almost-cycle classes by re-reading the same chain**: for
`S ⊆ T`, `relIncl` sends the `(X, S)`-class of `c` to the `(X, T)`-class of `c`. -/
theorem relIncl_relClassOf {S T : Set ↑X} (hST : S ⊆ T) (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1)) :
    relIncl hST (m + 2) (relClassOf S m c hc)
      = relClassOf T m c (subspaceChains_mono hST (m + 1) hc) := by
  rw [relClassOf, relClassOf, relIncl,
    show RelativeHomology.mk S (m + 2) (relCycleOf S m c hc)
      = Submodule.Quotient.mk (relCycleOf S m c hc) from rfl,
    RelativeHomology.map_mk]
  congr 1
  refine Subtype.ext ?_
  rw [relCyclesMap_coe]
  show relMapChain (ContinuousMap.id ↑X) (fun _ hx => hST hx) (m + 2)
      (RelativeChain.mk S (m + 2) c) = RelativeChain.mk T (m + 2) c
  rw [relMapChain_mk, mapChain_id]

/-- **Interior-point restriction of an almost-cycle class**: `restrictBd` re-reads the same chain
relative to `{x}ᶜ` — the local class of the chain at `x`. -/
theorem restrictBd_relClassOf (S : Set ↑X) {x : ↑X} (hx : x ∉ S) (m : ℕ)
    (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1)) :
    restrictBd S hx (m + 2) (relClassOf S m c hc)
      = relClassOf ({x}ᶜ) m c
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hc) :=
  relIncl_relClassOf (Set.subset_compl_singleton_iff.mpr hx) m c hc

/-- **The `ℤ/2` two-element absorb**: any nonzero element of a `ℤ/2`-line is the generator. -/
theorem eq_linearEquiv_symm_one_of_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (g : V ≃ₗ[ZMod 2] ZMod 2) {α : V} (hα : α ≠ 0) : α = g.symm 1 := by
  have hgα : g α ≠ 0 := fun h => hα (g.injective (h.trans (map_zero g).symm))
  have h1 : g α = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (g α) with h | h
    · exact absurd h hgα
    · exact h
  rw [← h1, LinearEquiv.symm_apply_apply]

/-! ## §2. The overlap congruence (the chain-level "agreement on the overlap") -/

/-- **Congruence modulo an away-supported chain**: if `c = p + e` with `e` supported in a subspace
`E ⊆ T`, then `c` and `p` have the same `(X, T)`-class. With `T = {x}ᶜ` and `E` the away-set of an
overlap-zone point `x`, this reduces the straddle detection of the glued chain to the detection of
a single collar product chain — the chain-level "both pieces restrict to the same collar class". -/
theorem relClassOf_eq_of_congr {T E : Set ↑X} (hET : E ⊆ T) (m : ℕ)
    {c p e : SingularChain X (m + 2)} (hcongr : c = p + e) (he : e ∈ subspaceChains E (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1))
    (hp : chainBoundary X (m + 1) p ∈ subspaceChains T (m + 1)) :
    relClassOf T m c hc = relClassOf T m p hp := by
  have hbe : chainBoundary X (m + 1) e ∈ subspaceChains T (m + 1) :=
    subspaceChains_mono hET (m + 1)
      (chainBoundary_mem_subspaceChains E (m + 1) e he)
  subst hcongr
  rw [show relClassOf T m (p + e) hc = relClassOf T m p hp + relClassOf T m e hbe from
      relClassOf_add T m p e hp hbe,
    relClassOf_eq_zero_of_subspace hET m e he hbe, add_zero]

/-! ## §3. The excision bridge — intrinsic (in-piece) nonvanishing transports to the ambient -/

/-- **The ambient almost-cycle class of a piece chain is the excision of its intrinsic class**:
for a chain `c'` of the subspace `C` whose intrinsic boundary is a `restr T C`-chain, the ambient
class of `chainIncl C c'` equals `excisionMap T C` of the intrinsic `(sub C, restr T C)`-class. -/
theorem relClassOf_chainIncl (T C : Set ↑X) (m : ℕ) (c' : SingularChain (sub C) (m + 2))
    (hc' : chainBoundary (sub C) (m + 1) c' ∈ subspaceChains (restr T C) (m + 1)) :
    relClassOf T m (chainIncl C (m + 2) c')
        (by
          rw [← chainIncl_chainBoundary]
          exact subspaceChains_mono Set.inter_subset_left (m + 1)
            ((chainIncl_mem_inter_iff T C (chainBoundary (sub C) (m + 1) c')).mpr hc'))
      = excisionMap T C (m + 2) (relClassOf (X := sub C) (restr T C) m c' hc') := by
  rw [relClassOf, relClassOf, excisionMap_mk]
  congr 1

/-- **Intrinsic nonvanishing transports to the ambient local class at interior points of the
piece**: if `x ∈ interior C` and the intrinsic `(sub C, sub C ∖ x)`-class of `c'` is nonzero, the
ambient local class of `chainIncl C c'` at `x` is nonzero — the excision `excisionMap {x}ᶜ C` is
injective because `{x}ᶜ` and `interior C` cover `X` (the banked per-point excision cover). -/
theorem relClassOf_chainIncl_ne_zero_of_interior [T1Space ↑X] {C : Set ↑X} {x : ↑X}
    (hxC : x ∈ interior C) (m : ℕ) (c' : SingularChain (sub C) (m + 2))
    (hc' : chainBoundary (sub C) (m + 1) c' ∈ subspaceChains (restr ({x}ᶜ) C) (m + 1))
    (hne : relClassOf (X := sub C) (restr ({x}ᶜ) C) m c' hc' ≠ 0) :
    relClassOf ({x}ᶜ) m (chainIncl C (m + 2) c')
        (by
          rw [← chainIncl_chainBoundary]
          exact subspaceChains_mono Set.inter_subset_left (m + 1)
            ((chainIncl_mem_inter_iff ({x}ᶜ) C (chainBoundary (sub C) (m + 1) c')).mpr hc')) ≠ 0 := by
  rw [relClassOf_chainIncl ({x}ᶜ) C m c' hc']
  intro h0
  exact hne (excisionMap_injective ({x}ᶜ) C (m + 1)
    (excision_cover_compl_singleton_interior hxC)
    (h0.trans (map_zero (excisionMap ({x}ᶜ) C (m + 2))).symm))

/-! ## §4. The two-piece glue datum and its class -/

/-- **The relative cover-MV glue datum** for the pair `(X, S)` in chain degree `m + 2`: two closed
cores covering `X` and two chains, each supported in its core, whose boundaries cancel on the seam
**modulo chains in `S`** — the chain-level Mayer–Vietoris agreement condition. Each field is a
concrete geometric datum (a core, a chain, a support fact, the seam-cancellation); none is a
completeness Prop. -/
structure RelCoverGlueData (S : Set ↑X) (m : ℕ) where
  /-- the first (e.g. cylinder-side) closed core. -/
  CA : Set ↑X
  /-- the second (e.g. handle-side) closed core. -/
  CB : Set ↑X
  /-- the cores cover the ambient carrier. -/
  hcover : ∀ x : ↑X, x ∈ CA ∨ x ∈ CB
  /-- the first piece chain. -/
  cA : SingularChain X (m + 2)
  /-- the second piece chain. -/
  cB : SingularChain X (m + 2)
  /-- `cA` is supported in its core. -/
  hcA : cA ∈ subspaceChains CA (m + 2)
  /-- `cB` is supported in its core. -/
  hcB : cB ∈ subspaceChains CB (m + 2)
  /-- **the seam-cancellation**: the boundary of the sum is an `S`-chain (the individual seam
  boundary terms cancel mod 2 — the chain-level "agreement on the overlap"). -/
  hbd : chainBoundary X (m + 1) (cA + cB) ∈ subspaceChains S (m + 1)

namespace RelCoverGlueData

variable {S : Set ↑X} {m : ℕ}

/-- **The glued relative class** `[cA + cB] ∈ H_{m+2}(X, S)` — a genuine relative cycle by the
seam-cancellation. -/
noncomputable def glueClass (D : RelCoverGlueData S m) : RelativeHomology S (m + 2) :=
  relClassOf S m (D.cA + D.cB) D.hbd

/-- The boundary of the `A`-piece chain is supported in `S ∪ CB` (its seam part is matched by the
`B`-piece): `∂cA = ∂(cA + cB) + ∂cB` over `ℤ/2`, the first summand an `S`-chain and the second a
`CB`-chain. -/
theorem hbdA (D : RelCoverGlueData S m) :
    chainBoundary X (m + 1) D.cA ∈ subspaceChains (S ∪ D.CB) (m + 1) := by
  have hEq : D.cA = (D.cA + D.cB) + D.cB := by
    rw [add_assoc, ZModModule.add_self, add_zero]
  rw [show chainBoundary X (m + 1) D.cA
      = chainBoundary X (m + 1) (D.cA + D.cB) + chainBoundary X (m + 1) D.cB from by
        rw [← map_add]; exact congrArg _ hEq]
  exact Submodule.add_mem _
    (subspaceChains_mono Set.subset_union_left (m + 1) D.hbd)
    (subspaceChains_mono Set.subset_union_right (m + 1)
      (chainBoundary_mem_subspaceChains D.CB (m + 1) D.cB D.hcB))

/-- The boundary of the `B`-piece chain is supported in `S ∪ CA` (symmetric to `hbdA`). -/
theorem hbdB (D : RelCoverGlueData S m) :
    chainBoundary X (m + 1) D.cB ∈ subspaceChains (S ∪ D.CA) (m + 1) := by
  have hEq : D.cB = (D.cA + D.cB) + D.cA := by
    rw [add_comm D.cA D.cB, add_assoc, ZModModule.add_self, add_zero]
  rw [show chainBoundary X (m + 1) D.cB
      = chainBoundary X (m + 1) (D.cA + D.cB) + chainBoundary X (m + 1) D.cA from by
        rw [← map_add]; exact congrArg _ hEq]
  exact Submodule.add_mem _
    (subspaceChains_mono Set.subset_union_left (m + 1) D.hbd)
    (subspaceChains_mono Set.subset_union_right (m + 1)
      (chainBoundary_mem_subspaceChains D.CA (m + 1) D.cA D.hcA))

/-- The `A`-piece chain is an almost-cycle rel `{x}ᶜ` at every point off `S ∪ CB`. -/
theorem hbdA_local (D : RelCoverGlueData S m) {x : ↑X} (hx : x ∉ S) (hxB : x ∉ D.CB) :
    chainBoundary X (m + 1) D.cA ∈ subspaceChains ({x}ᶜ) (m + 1) :=
  subspaceChains_mono
    (Set.union_subset (Set.subset_compl_singleton_iff.mpr hx)
      (Set.subset_compl_singleton_iff.mpr hxB)) (m + 1) D.hbdA

/-- The `B`-piece chain is an almost-cycle rel `{x}ᶜ` at every point off `S ∪ CA`. -/
theorem hbdB_local (D : RelCoverGlueData S m) {x : ↑X} (hx : x ∉ S) (hxA : x ∉ D.CA) :
    chainBoundary X (m + 1) D.cB ∈ subspaceChains ({x}ᶜ) (m + 1) :=
  subspaceChains_mono
    (Set.union_subset (Set.subset_compl_singleton_iff.mpr hx)
      (Set.subset_compl_singleton_iff.mpr hxA)) (m + 1) D.hbdB

/-- **The one-sided zone split (`A`-side)**: at a point off `CB` (and off `S`), the restriction of
the glued class is the local class of `cA` alone — the `cB`-summand dies. -/
theorem restrictBd_glueClass_of_notMem_CB (D : RelCoverGlueData S m) {x : ↑X} (hx : x ∉ S)
    (hxB : x ∉ D.CB) :
    restrictBd S hx (m + 2) D.glueClass = relClassOf ({x}ᶜ) m D.cA (D.hbdA_local hx hxB) := by
  have hxBc : D.CB ⊆ ({x}ᶜ : Set ↑X) := Set.subset_compl_singleton_iff.mpr hxB
  have hbBx : chainBoundary X (m + 1) D.cB ∈ subspaceChains ({x}ᶜ) (m + 1) :=
    subspaceChains_mono hxBc (m + 1)
      (chainBoundary_mem_subspaceChains D.CB (m + 1) D.cB D.hcB)
  rw [glueClass, restrictBd_relClassOf S hx m (D.cA + D.cB) D.hbd,
    show relClassOf ({x}ᶜ) m (D.cA + D.cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd)
      = relClassOf ({x}ᶜ) m D.cA (D.hbdA_local hx hxB) + relClassOf ({x}ᶜ) m D.cB hbBx from
      relClassOf_add ({x}ᶜ) m D.cA D.cB (D.hbdA_local hx hxB) hbBx,
    relClassOf_eq_zero_of_subspace hxBc m D.cB D.hcB hbBx, add_zero]

/-- **The one-sided zone split (`B`-side)**: symmetric to the `A`-side. -/
theorem restrictBd_glueClass_of_notMem_CA (D : RelCoverGlueData S m) {x : ↑X} (hx : x ∉ S)
    (hxA : x ∉ D.CA) :
    restrictBd S hx (m + 2) D.glueClass = relClassOf ({x}ᶜ) m D.cB (D.hbdB_local hx hxA) := by
  have hxAc : D.CA ⊆ ({x}ᶜ : Set ↑X) := Set.subset_compl_singleton_iff.mpr hxA
  have hbAx : chainBoundary X (m + 1) D.cA ∈ subspaceChains ({x}ᶜ) (m + 1) :=
    subspaceChains_mono hxAc (m + 1)
      (chainBoundary_mem_subspaceChains D.CA (m + 1) D.cA D.hcA)
  rw [glueClass, restrictBd_relClassOf S hx m (D.cA + D.cB) D.hbd,
    show relClassOf ({x}ᶜ) m (D.cA + D.cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd)
      = relClassOf ({x}ᶜ) m D.cA hbAx + relClassOf ({x}ᶜ) m D.cB (D.hbdB_local hx hxA) from
      relClassOf_add ({x}ᶜ) m D.cA D.cB hbAx (D.hbdB_local hx hxA),
    relClassOf_eq_zero_of_subspace hxAc m D.cA D.hcA hbAx, zero_add]

/-- **The overlap zone**: at any interior point the restriction of the glued class is the local
class of the full glued chain (`restrictBd` re-reads the chain rel `{x}ᶜ`). In the overlap zone
this is the subject of the straddle detection; combined with `relClassOf_eq_of_congr` it reduces
to the local class of a collar product chain. -/
theorem restrictBd_glueClass (D : RelCoverGlueData S m) {x : ↑X} (hx : x ∉ S) :
    restrictBd S hx (m + 2) D.glueClass
      = relClassOf ({x}ᶜ) m (D.cA + D.cB)
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd) :=
  restrictBd_relClassOf S hx m (D.cA + D.cB) D.hbd

/-! ## §5. The glued relative fundamental class -/

/-- **The glued class restricts to the interior generator everywhere** — the relative cover-MV
gluing theorem. The three per-zone nonvanishing inputs are each an honest local fact about a
concrete chain: the `A`-chain's local class off `CB`, the `B`-chain's local class off `CA`, and
the glued chain's local class on the overlap (dischargeable from a collar product chain via
`relClassOf_eq_of_congr`). Nonvanishing normalizes to the generator by the `ℤ/2` absorb. -/
theorem restrictsToRelGen_glueClass (D : RelCoverGlueData S m)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hdetA : ∀ (x : ↑X) (hx : x ∉ S) (hxB : x ∉ D.CB),
      relClassOf ({x}ᶜ) m D.cA (D.hbdA_local hx hxB) ≠ 0)
    (hdetB : ∀ (x : ↑X) (hx : x ∉ S) (hxA : x ∉ D.CA),
      relClassOf ({x}ᶜ) m D.cB (D.hbdB_local hx hxA) ≠ 0)
    (hdetAB : ∀ (x : ↑X) (hx : x ∉ S), x ∈ D.CA → x ∈ D.CB →
      relClassOf ({x}ᶜ) m (D.cA + D.cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd) ≠ 0) :
    RestrictsToRelGen S gen D.glueClass := by
  intro x hx
  by_cases hxB : x ∈ D.CB
  · by_cases hxA : x ∈ D.CA
    · rw [D.restrictBd_glueClass hx]
      exact eq_linearEquiv_symm_one_of_ne_zero (gen x hx) (hdetAB x hx hxA hxB)
    · rw [D.restrictBd_glueClass_of_notMem_CA hx hxA]
      exact eq_linearEquiv_symm_one_of_ne_zero (gen x hx) (hdetB x hx hxA)
  · rw [D.restrictBd_glueClass_of_notMem_CB hx hxB]
    exact eq_linearEquiv_symm_one_of_ne_zero (gen x hx) (hdetA x hx hxB)

/-- **The glued `HasRelFundClass`** — the exact existence witness the trace/capstone supply rows
consume, produced from the glue datum and the three per-zone detections. -/
theorem hasRelFundClass_of_glueData (D : RelCoverGlueData S m)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hdetA : ∀ (x : ↑X) (hx : x ∉ S) (hxB : x ∉ D.CB),
      relClassOf ({x}ᶜ) m D.cA (D.hbdA_local hx hxB) ≠ 0)
    (hdetB : ∀ (x : ↑X) (hx : x ∉ S) (hxA : x ∉ D.CA),
      relClassOf ({x}ᶜ) m D.cB (D.hbdB_local hx hxA) ≠ 0)
    (hdetAB : ∀ (x : ↑X) (hx : x ∉ S), x ∈ D.CA → x ∈ D.CB →
      relClassOf ({x}ᶜ) m (D.cA + D.cB)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) D.hbd) ≠ 0) :
    HasRelFundClass S gen :=
  ⟨D.glueClass, D.restrictsToRelGen_glueClass gen hdetA hdetB hdetAB⟩

end RelCoverGlueData

end SKEFTHawking.SingularRelativeCoverMV
