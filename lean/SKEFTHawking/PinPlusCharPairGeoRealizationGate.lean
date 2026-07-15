/-
# Phase 5q.H W-A RE-GATE (arm 4, ROUND 5 — the fresh-context vacuity gate on the MIGRATED carrier)

Adversarial gate findings against the membrane-TIED carrier (`pinPlusCharPairData` on
`CharPairBorTied`, `PinPlusCharPairData` §9.6/§11) and the wt2 realization seam
(`PinPlusCharPairMembraneGeoRealization`). Three kernel-checked findings:

**F1 — THE TIE IS (pre-realization) A NON-FILTER: universal laundering.** `GeoMembrane.bInc` is an
un-tethered linear-map field, and EVERY submodule of the joint boundary space is the kernel of some
linear map (`GeoMembrane.ofSubmodule`: the quotient map read through a `finBasis`). Hence every
free-`L` `CharPairBor` transports to a tied `CharPairBorTied` with the SAME kernel
(`CharPairBor.tie`), and the two carriers are inhabitation-EQUIVALENT
(`charPairBorTied_nonempty_iff_free`). This strictly generalizes the round-4.5 e₈ replay
(`doubleKillerBorTied` — one instance of `tie`): not just the doubling exploit but EVERY round-3
free-form exploit and EVERY future free-form counterexample transfers wholesale. The migration's
value is architectural (the field is now shaped to RECEIVE a realization certificate), not
restrictive.

**F2 — THE AS-BUILT REALIZATION SEAM LAUNDERS THE EXPLOIT: basis-gauge covariance.**
`GeoRealizationData`'s enhancement bases `eσ`/`eτ`/`eQ` are FREE `LinearEquiv` fields. Post-composing
`eσ` with any automorphism `g` (`GeoRealizationData.gaugeσ`) keeps the same spaces `∂Q`, `Q`, the
same inclusion `ι` — the same TOPOLOGY, hence the same T2/compactness/dimension certificates, were
they present — while moving the computed kernel by the block gauge
(`ker_transportedBInc_gaugeσ`). The explicit gauge `killerGauge` (the block-diagonal `id ⊕ φ` read
through `finSumFinEquiv`, `φ` the `J+I` isometry of the W-D gate) carries the honest doubling
membrane's kernel (the anti-diagonal, `negBorBInc_ker`) EXACTLY onto the e₈-graph kernel
(`map_killerGauge_ker_negBorBInc`). Consequently, from ANY geometric realization `d` of the honest
doubling membrane — and the strengthened carrier must admit one, or `negBor`/`cylBor` die — the
gauged datum `d.gaugeσ killerGauge` is a `GeoMembrane.ofGeometric` image hosting the full
un-reversed-double exploit (`doubleKillerBorGeoRealized`). **Certificate consequence for the
strengthening spec: T2 + compactness + dimension + genuine-boundary-inclusion certificates on
`bdry`/`Q`/`ι` are collectively INSUFFICIENT — the gauge never touches them. The load-bearing
missing tie is the (n, q, surf) BASIS tie: `eσ`/`eτ` must be pinned to the ends' carried enhancement
bases (`hpolar`/`hchar`), not free fields.**

**F3 — W-ADMISSIBILITY IS (as shaped) NOT A `w₂ = 0` FILTER: the `sqOp` gauge.** `LefschetzWuDatum`'s
`sqOp` field appears in NEITHER of its constraints (`nondeg`, `dimeq`), so any datum may have its
Steenrod square replaced by `0` (`LefschetzWuDatum.zeroSq`) — after which both Wu classes vanish
(`wuClass_zeroSq`) and `wuW2 = 0` holds DEFINITIONALLY (`wuW2_zeroSq`). Hence `WAdm b` is
inhabitable from bare Lefschetz-duality data with NO Wu/Steenrod input (`WAdm.ofLefschetzNoWu`),
and a full `CharPairWProvider` needs only duality data for every bordism
(`charPairWProviderOfDuality`): bordisms with genuine `w₂(W) ≠ 0` pass. The `hwu` field is
self-referentially discharged by the datum's own free `sqOp` — the same free-field-plus-
self-referential-condition shape as the round-3 free-`L` finding. **Certificate consequence: the
provider discharge (wt3) and any strengthened `Bor` must pin `sqOp` to the substrate's actual
relative Steenrod square (`relSq²`), else the Pin⁺ restriction is vacuous.**

Also encoded: `GeoMembrane.top` (the `mid = 0` degenerate membrane, kernel `⊤`, available for ALL
end forms — blocked downstream only by `htaylor`, never by `hlag`, which is vacuous at `⊤`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairMembraneGeoRealization
import SKEFTHawking.PinPlusKTVacuityGateWD

open scoped Manifold
open CategoryTheory Opposite
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusKTVacuityGateWD
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.RP4CharPairWitness SKEFTHawking.RP4Witness

namespace SKEFTHawking.PinPlusCharPairGeoRealizationGate

/-! ## §1. F1 — universal laundering: every submodule is a computed membrane kernel, so the tied
carrier is inhabitation-equivalent to the free carrier (pre-realization). -/

/-- **Every submodule is the computed kernel of a synthetic membrane datum.** The quotient map
`mkQ : V →ₗ V ⧸ L` read through a `finBasis` of the quotient is a `bInc` with kernel exactly `L`.
This is the UNIVERSAL form of the round-4.5 synthetic-`bInc` replay: the tie's kernel-computation
restricts NOTHING until `bInc` carries a realization certificate. -/
noncomputable def GeoMembrane.ofSubmodule {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (L : Submodule (ZMod 2) (Fin nσ ⊕ Fin nτ → ZMod 2)) :
    GeoMembrane qσ qτ :=
  ⟨Module.finrank (ZMod 2) ((Fin nσ ⊕ Fin nτ → ZMod 2) ⧸ L),
   (Module.finBasis (ZMod 2) ((Fin nσ ⊕ Fin nτ → ZMod 2) ⧸ L)).equivFun.toLinearMap ∘ₗ L.mkQ⟩

/-- The synthetic membrane's computed kernel is the prescribed submodule — laundering is exact. -/
theorem GeoMembrane.ofSubmodule_L {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (L : Submodule (ZMod 2) (Fin nσ ⊕ Fin nτ → ZMod 2)) :
    (GeoMembrane.ofSubmodule qσ qτ L).L = L := by
  show LinearMap.ker
    ((Module.finBasis (ZMod 2) ((Fin nσ ⊕ Fin nτ → ZMod 2) ⧸ L)).equivFun.toLinearMap ∘ₗ L.mkQ)
    = L
  rw [ker_equivComp, Submodule.ker_mkQ]

/-- **The `mid = 0` degenerate membrane** — `bInc = 0`, computed kernel `⊤` — inhabits `GeoMembrane`
for EVERY pair of end forms. Downstream, `hlag` NEVER blocks it (`JointLagrangian` is vacuous at
`⊤`); only `htaylor` does, and only when the joint form is somewhere nonzero. -/
def GeoMembrane.top {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    GeoMembrane qσ qτ :=
  ⟨0, 0⟩

theorem GeoMembrane.top_L {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    (GeoMembrane.top qσ qτ).L = ⊤ :=
  LinearMap.ker_zero

/-- `JointLagrangian` is VACUOUS at `L = ⊤`: the maximality direction asks nothing of a total
kernel. Any degenerate membrane is blocked (if at all) by the Taylor leg alone. -/
theorem jointLagrangian_top {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    JointLagrangian qσ qτ (⊤ : Submodule (ZMod 2) (Fin nσ ⊕ Fin nτ → ZMod 2)) :=
  fun _ _ => Submodule.mem_top

section TieEquivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **Every free-`L` bordism datum launders into the tied form** with the SAME kernel: the section
of `CharPairBorTied.toFree`. The membrane is `GeoMembrane.ofSubmodule` of the free field. -/
noncomputable def CharPairBor.tie {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBor b σ τ) : CharPairBorTied b σ τ where
  hWT2 := β.hWT2
  P14 := β.P14
  P23 := β.P23
  hwu := β.hwu
  mem := GeoMembrane.ofSubmodule σ.q τ.q β.L
  htaylor := by
    show TaylorLegVanishes σ.q τ.q (GeoMembrane.ofSubmodule σ.q τ.q β.L).L
    rw [GeoMembrane.ofSubmodule_L]
    exact β.htaylor
  hlag := by
    show JointLagrangian σ.q τ.q (GeoMembrane.ofSubmodule σ.q τ.q β.L).L
    rw [GeoMembrane.ofSubmodule_L]
    exact β.hlag

/-- The laundering preserves the kernel on the nose. -/
theorem CharPairBor.tie_mem_L {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBor b σ τ) : (CharPairBor.tie β).mem.L = β.L :=
  GeoMembrane.ofSubmodule_L σ.q τ.q β.L

/-- **F1 HEADLINE — the tied and free carriers are inhabitation-EQUIVALENT** (pre-realization).
The arm-4 migration changed the SHAPE of the membrane field, not the class of representable
bordism data: every round-3 free-`L` exploit — and every future one — transfers to the tied
carrier via `tie`, and conversely via `toFree`. The tie becomes a filter ONLY when `bInc` is
forced through a certified geometric realization. -/
theorem charPairBorTied_nonempty_iff_free {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t} :
    Nonempty (CharPairBorTied b σ τ) ↔ Nonempty (CharPairBor b σ τ) :=
  ⟨fun ⟨β⟩ => ⟨β.toFree⟩, fun ⟨β⟩ => ⟨CharPairBor.tie β⟩⟩

end TieEquivalence

/-! ## §2. The block-congruence gauge — the reusable equiv the seam attack rides -/

/-- **Block congruence** `g ⊞ h` on `Sum`-indexed function spaces — the `LinearEquiv` refinement of
the in-tree `blockMap`, assembled from `sumArrowLequivProdArrow` and `prodCongr`. -/
def blockCongr {ι₁ ι₂ κ₁ κ₂ : Type*}
    (g : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (κ₁ → ZMod 2)) (h : (ι₂ → ZMod 2) ≃ₗ[ZMod 2] (κ₂ → ZMod 2)) :
    (ι₁ ⊕ ι₂ → ZMod 2) ≃ₗ[ZMod 2] (κ₁ ⊕ κ₂ → ZMod 2) :=
  (LinearEquiv.sumArrowLequivProdArrow ι₁ ι₂ (ZMod 2) (ZMod 2)).trans
    ((g.prodCongr h).trans (LinearEquiv.sumArrowLequivProdArrow κ₁ κ₂ (ZMod 2) (ZMod 2)).symm)

@[simp] theorem blockCongr_apply {ι₁ ι₂ κ₁ κ₂ : Type*}
    (g : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (κ₁ → ZMod 2)) (h : (ι₂ → ZMod 2) ≃ₗ[ZMod 2] (κ₂ → ZMod 2))
    (x : ι₁ ⊕ ι₂ → ZMod 2) :
    blockCongr g h x = Sum.elim (g fun i => x (Sum.inl i)) (h fun i => x (Sum.inr i)) :=
  rfl

@[simp] theorem blockCongr_symm_apply {ι₁ ι₂ κ₁ κ₂ : Type*}
    (g : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (κ₁ → ZMod 2)) (h : (ι₂ → ZMod 2) ≃ₗ[ZMod 2] (κ₂ → ZMod 2))
    (x : κ₁ ⊕ κ₂ → ZMod 2) :
    (blockCongr g h).symm x = Sum.elim (g.symm fun i => x (Sum.inl i))
      (h.symm fun i => x (Sum.inr i)) :=
  rfl

/-- The block gauge carries block submodules to block submodules of the block images. -/
theorem map_blockCongr_blockSub {ι₁ ι₂ κ₁ κ₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂]
    (g : (ι₁ → ZMod 2) ≃ₗ[ZMod 2] (κ₁ → ZMod 2)) (h : (ι₂ → ZMod 2) ≃ₗ[ZMod 2] (κ₂ → ZMod 2))
    (A : Submodule (ZMod 2) (ι₁ → ZMod 2)) (B : Submodule (ZMod 2) (ι₂ → ZMod 2)) :
    Submodule.map (blockCongr g h).toLinearMap (blockSub A B)
      = blockSub (A.map g.toLinearMap) (B.map h.toLinearMap) := by
  ext x
  rw [Submodule.mem_map_equiv, mem_blockSub, mem_blockSub, blockCongr_symm_apply,
    Submodule.mem_map_equiv, Submodule.mem_map_equiv]
  rfl

/-- **The graph of ANY isometry is the block-gauged image of the honest anti-diagonal**: gauging the
τ-half of the cylinder kernel by `φ` produces exactly `graphSub φ`. The geometric half-lives–half-dies
signature (`diagonal_mem_cylGeoMembrane`) is NOT gauge-invariant — this is the seam attack's core. -/
theorem map_blockCongr_cylLagrangian {n : ℕ}
    (φ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Submodule.map (blockCongr (LinearEquiv.refl (ZMod 2) (Fin n → ZMod 2)) φ).toLinearMap
      (cylLagrangian n) = graphSub φ := by
  ext x
  rw [Submodule.mem_map_equiv, mem_cylLagrangian_iff, mem_graphSub, blockCongr_symm_apply]
  show (fun i => x (Sum.inl i)) = φ.symm (fun i => x (Sum.inr i))
    ↔ (fun i => x (Sum.inr i)) = φ (fun i => x (Sum.inl i))
  rw [LinearEquiv.eq_symm_apply, eq_comm]

/-! ## §3. F2(a) — the seam's basis fields are an unconstrained gauge: `gaugeσ` moves the computed
kernel by an arbitrary σ-block automorphism while fixing the SPACES `∂Q`, `Q` and the inclusion `ι`
(hence every topological certificate a strengthening could add to them). -/

section SeamGauge

variable {nσ nτ mid : ℕ}

/-- **The σ-basis gauge**: post-compose the free `eσ` field with an automorphism `g`. The spaces,
the clopen split, and the inclusion are UNTOUCHED — only the basis bookkeeping moves. -/
noncomputable def GeoRealizationData.gaugeσ (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) : GeoRealizationData nσ nτ mid :=
  { d with eσ := d.eσ.trans g }

/-! The σ-gauge fixes EVERY topological field of the datum — `∂Q`, `Q`, the clopen split, and the
inclusion `ι` are untouched (each equality is `rfl`). Hence ANY certificate a strengthening could
attach to the spaces or the map (T2, compactness, dimension, genuine-boundary-inclusion,
membrane-in-W) is automatically inherited by the gauged datum: topological certificates are
GAUGE-BLIND, and only a basis tie can see the laundering. -/

@[simp] theorem gaugeσ_bdry (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (GeoRealizationData.gaugeσ d g).bdry = d.bdry := rfl

@[simp] theorem gaugeσ_Q (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (GeoRealizationData.gaugeσ d g).Q = d.Q := rfl

@[simp] theorem gaugeσ_U (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (GeoRealizationData.gaugeσ d g).U = d.U := rfl

@[simp] theorem gaugeσ_ι (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    (GeoRealizationData.gaugeσ d g).ι = d.ι := rfl

theorem srcEquiv_gaugeσ (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    srcEquiv (GeoRealizationData.gaugeσ d g)
      = (srcEquiv d).trans (blockCongr g (LinearEquiv.refl (ZMod 2) (Fin nτ → ZMod 2))) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro y
  rfl

theorem transportedBInc_gaugeσ (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    transportedBInc (GeoRealizationData.gaugeσ d g)
      = (transportedBInc d) ∘ₗ
        (blockCongr g (LinearEquiv.refl (ZMod 2) (Fin nτ → ZMod 2))).symm.toLinearMap := by
  apply LinearMap.ext
  intro y
  show d.eQ (Homology.map d.ι 1 ((srcEquiv (GeoRealizationData.gaugeσ d g)).symm y)) = _
  rw [srcEquiv_gaugeσ]
  rfl

/-- **The gauge moves the computed kernel by the block gauge** — the seam's `L` is only defined up
to an arbitrary block automorphism as long as `eσ` is a free field. -/
theorem ker_transportedBInc_gaugeσ (d : GeoRealizationData nσ nτ mid)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) :
    LinearMap.ker (transportedBInc (GeoRealizationData.gaugeσ d g))
      = Submodule.map (blockCongr g (LinearEquiv.refl (ZMod 2) (Fin nτ → ZMod 2))).toLinearMap
          (LinearMap.ker (transportedBInc d)) := by
  rw [transportedBInc_gaugeσ, LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.symm_symm]

/-- The interior gauge (`eQ.trans h`) leaves the kernel INVARIANT — the laundering freedom lives
entirely in the boundary bases `eσ`/`eτ`. -/
noncomputable def GeoRealizationData.gaugeQ (d : GeoRealizationData nσ nτ mid)
    (h : (Fin mid → ZMod 2) ≃ₗ[ZMod 2] (Fin mid → ZMod 2)) : GeoRealizationData nσ nτ mid :=
  { d with eQ := d.eQ.trans h }

theorem ker_transportedBInc_gaugeQ (d : GeoRealizationData nσ nτ mid)
    (h : (Fin mid → ZMod 2) ≃ₗ[ZMod 2] (Fin mid → ZMod 2)) :
    LinearMap.ker (transportedBInc (GeoRealizationData.gaugeQ d h))
      = LinearMap.ker (transportedBInc d) := by
  show LinearMap.ker (h.toLinearMap ∘ₗ transportedBInc d) = _
  rw [ker_equivComp]

end SeamGauge

/-! ## §4. F2(b) — THE KILLER GAUGE: the honest doubling kernel gauges EXACTLY onto the e₈-graph
kernel, so any geometric realization of the honest doubling membrane launders (via `gaugeσ` +
`GeoMembrane.ofGeometric`) into a "geometrically realized" host for the un-reversed double. -/

/-- **The killer gauge** — the block-diagonal `id ⊞ φ` (φ = the W-D `J+I` isometry `phiLin`) on the
two halves of the σ-block, read through `finSumFinEquiv`. An automorphism of `Fin (4+4) → ZMod 2`:
pure basis bookkeeping, no topology. -/
noncomputable def killerGauge : (Fin (4 + 4) → ZMod 2) ≃ₗ[ZMod 2] (Fin (4 + 4) → ZMod 2) :=
  (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := 4) (n := 4))).trans
    ((blockCongr (LinearEquiv.refl (ZMod 2) (Fin 4 → ZMod 2)) phiLin).trans
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := 4) (n := 4))).symm)

/-- The `funLeft` reindex the in-tree kernels use IS the `funCongrLeft` equivalence, as a map. -/
theorem funLeft_eq_funCongrLeft :
    LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑(finSumFinEquiv (m := 4) (n := 4))
      = (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
          (finSumFinEquiv (m := 4) (n := 4))).toLinearMap :=
  rfl

/-- The killer gauge carries the (reindexed) honest anti-diagonal onto the (reindexed) e₈ graph. -/
theorem map_killerGauge_comap :
    Submodule.map killerGauge.toLinearMap
      ((cylLagrangian 4).comap (LinearMap.funLeft (ZMod 2) (ZMod 2)
        (finSumFinEquiv (m := 4) (n := 4))))
      = (graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2)
          (finSumFinEquiv (m := 4) (n := 4))) := by
  rw [funLeft_eq_funCongrLeft, Submodule.comap_equiv_eq_map_symm,
    Submodule.comap_equiv_eq_map_symm, ← Submodule.map_comp,
    ← map_blockCongr_cylLagrangian phiLin, ← Submodule.map_comp]
  congr 1
  show ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
      (finSumFinEquiv (m := 4) (n := 4))).symm.trans killerGauge).toLinearMap
    = ((blockCongr (LinearEquiv.refl (ZMod 2) (Fin 4 → ZMod 2)) phiLin).trans
        (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
          (finSumFinEquiv (m := 4) (n := 4))).symm).toLinearMap
  congr 1
  rw [killerGauge, ← LinearEquiv.trans_assoc, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_trans]

/-- **F2 KEYSTONE — the gauge carries the honest doubling membrane's computed kernel EXACTLY onto
the synthetic e₈ kernel** (`negBorBInc_ker` ↦ `doubleKillerBInc_ker`). -/
theorem map_killerGauge_ker_negBorBInc :
    Submodule.map (blockCongr killerGauge
        (LinearEquiv.refl (ZMod 2) (Fin 0 → ZMod 2))).toLinearMap
      (LinearMap.ker (negBorBInc 4))
      = LinearMap.ker doubleKillerBInc := by
  rw [negBorBInc_ker, doubleKillerBInc_ker, map_blockCongr_blockSub, map_killerGauge_comap,
    LinearEquiv.refl_toLinearMap, Submodule.map_id]

/-- **The laundered membrane**: `GeoMembrane.ofGeometric` of the σ-gauged datum. By construction it
is IN THE IMAGE of the realization seam — "geometrically realized" per the as-built
`GeoRealizationData`, with the SAME spaces and inclusion as the honest datum `d`. -/
noncomputable def doubleKillerGeoMem {mid : ℕ} (d : GeoRealizationData (4 + 4) 0 mid) :
    GeoMembrane (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr).q
      (charPairEmptyStr (I := 𝓡 4) (k := 0)).q :=
  GeoMembrane.ofGeometric _ _ (GeoRealizationData.gaugeσ d killerGauge)

/-- If `d` realizes the honest doubling membrane (its transported kernel is the anti-diagonal
`ker (negBorBInc 4)`), the laundered membrane's computed kernel is EXACTLY the e₈ kernel. -/
theorem doubleKillerGeoMem_L {mid : ℕ} (d : GeoRealizationData (4 + 4) 0 mid)
    (hd : LinearMap.ker (transportedBInc d) = LinearMap.ker (negBorBInc 4)) :
    (doubleKillerGeoMem d).L = LinearMap.ker doubleKillerBInc := by
  show LinearMap.ker (transportedBInc (GeoRealizationData.gaugeσ d killerGauge)) = _
  rw [ker_transportedBInc_gaugeσ, hd, map_killerGauge_ker_negBorBInc]

/-- **F2 HEADLINE — the un-reversed double `σ₄ ⊔ σ₄ → ∅` inhabits the TIED carrier through a
membrane IN THE IMAGE OF the realization seam**, as soon as ANY geometric realization `d` of the
honest doubling membrane exists (and the strengthened carrier MUST admit one — it is `negBor`'s own
membrane). The membrane is `GeoMembrane.ofGeometric` applied to `d.gaugeσ killerGauge`: same
`bdry`/`Q`/`ι` as the honest datum, so every topological certificate (`T2`, compactness, dimension,
genuine boundary-inclusion) that `d` satisfies, the laundered datum satisfies too. Requiring
`mem ∈ range ofGeometric` therefore does NOT close the round-4.5 hole; only pinning `eσ`/`eτ` to
the ends' carried enhancement bases does. -/
noncomputable def doubleKillerBorGeoRealized (prov : CharPairWProvider (𝓡 4) 0) {mid : ℕ}
    (d : GeoRealizationData (4 + 4) 0 mid)
    (hd : LinearMap.ker (transportedBInc d) = LinearMap.ker (negBorBInc 4)) :
    CharPairBorTied (doublingBordism s4M)
      (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr) charPairEmptyStr :=
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr).q
      ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    L44_metabolic.reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBorTied prov (doublingBordism s4M)
    (by
      haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
      exact inferInstanceAs
        (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1)))
    (doubleKillerGeoMem d)
    (by show TaylorLegVanishes _ _ (doubleKillerGeoMem d).L
        rw [doubleKillerGeoMem_L d hd, doubleKillerBInc_ker]
        exact hmeta.1)
    (by show JointLagrangian _ _ (doubleKillerGeoMem d).L
        rw [doubleKillerGeoMem_L d hd, doubleKillerBInc_ker]
        exact hmeta.2)

/-! ## §5. F3 — the `sqOp` gauge: `WAdm` is inhabitable from bare Lefschetz-duality data, so the
`w₂(W) = 0` admissibility filter (as shaped) filters nothing beyond duality. -/

section SqOpGauge

variable {X : TopCat} {S : Set ↑X}

/-- **Zero out the Steenrod square.** `sqOp` appears in NEITHER constraint (`nondeg`, `dimeq`), so
this is a legal `LefschetzWuDatum` for the SAME spaces. -/
noncomputable def LefschetzWuDatum.zeroSq {k nk n : ℕ} (P : LefschetzWuDatum X S k nk n) :
    LefschetzWuDatum X S k nk n :=
  { P with sqOp := 0 }

/-- With `sqOp = 0` the Wu functional vanishes, hence so does its Lefschetz-dual Wu class. -/
theorem wuClass_zeroSq {k nk n : ℕ} (P : LefschetzWuDatum X S k nk n) :
    wuClass (LefschetzWuDatum.zeroSq P) = 0 := by
  have hfun : wuFunctional (LefschetzWuDatum.zeroSq P) = 0 := LinearMap.comp_zero P.mu
  rw [wuClass, hfun, Equiv.symm_apply_eq, Equiv.ofBijective_apply, map_zero]

/-- **`w₂(W) = 0` holds DEFINITIONALLY for `sqOp`-zeroed data** — for every `W`, whatever its
honest `w₂`. The `hwu` condition is self-referentially discharged by the datum's own free field. -/
theorem wuW2_zeroSq (P₁₄ : LefschetzWuDatum X S 1 4 5) (P₂₃ : LefschetzWuDatum X S 2 3 5) :
    wuW2 (LefschetzWuDatum.zeroSq P₁₄) (LefschetzWuDatum.zeroSq P₂₃) = 0 := by
  rw [wuW2, wuClassW2, wuClassW1, wuClass_zeroSq, wuClass_zeroSq, map_zero, add_zero]

section WAdmVacuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **F3 — W-admissibility from bare duality data**: any two Lefschetz data for `(W, ∂W)` yield a
full `WAdm b` after `sqOp`-zeroing — NO Wu/Steenrod input, no `w₂` restriction on `W`. -/
noncomputable def WAdm.ofLefschetzNoWu {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t}
    (P₁₄ : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5)
    (P₂₃ : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5) :
    WAdm b :=
  ⟨LefschetzWuDatum.zeroSq P₁₄, LefschetzWuDatum.zeroSq P₂₃, wuW2_zeroSq P₁₄ P₂₃⟩

/-- **F3 HEADLINE — a full `CharPairWProvider` from duality data alone**: if every bordism carries
bare Lefschetz-duality data (the honest half — Betti equality + a perfect pairing — with NO Steenrod
input), the provider hypothesis is discharged and every bordism is "admissible", including those
with genuine `w₂(W) ≠ 0`. The provider's `hwu` therefore restricts NOTHING until `sqOp` is pinned
to the substrate's actual relative Steenrod square. -/
noncomputable def charPairWProviderOfDuality
    (P : ∀ {s t : SingularManifold.{0} PUnit.{1} k I} (b : Bordism.{0} (I.prod (𝓡∂ 1)) s t),
      LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5 ×
        LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5) :
    CharPairWProvider I k :=
  ⟨fun b => WAdm.ofLefschetzNoWu (P b).1 (P b).2⟩

end WAdmVacuity

end SqOpGauge

end SKEFTHawking.PinPlusCharPairGeoRealizationGate
