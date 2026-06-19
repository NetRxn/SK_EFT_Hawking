import Mathlib
import SKEFTHawking.SingularHomologyMod2

/-!
# The cap product on (co)homology `⌢ : Hᵏ × H_{k+m+1} → H_{m+1}`

The cochain-level cap product `cap a : C_{k+m} → C_m` (`SingularHomologyMod2.cap`) descends to a
`ℤ/2`-bilinear map on (co)homology classes — the homological analogue of `kroneckerH` (which
descended the Kronecker pairing) and `cupH` (which descended the cup product). This is the
foundation of the Poincaré-duality map `[M] ⌢ ·` (cap with the fundamental class).

The two descent facts are already proved in `SingularHomologyMod2`:

* `cap_cocycle_chainMap`: for a **cocycle** `a` (`δa = 0`), `a ⌢ ·` is a chain map
  `∂(a ⌢ c) = a ⌢ (∂c)`. Hence `a ⌢ ·` sends cycles to cycles (its boundary is `a ⌢ ∂z = a ⌢ 0`)
  and boundaries to boundaries (`a ⌢ ∂w = ∂(a ⌢ w)`), so it descends the **homology** argument.
* `cap_leibniz`: `∂(a ⌢ c) = (δa) ⌢ c + a ⌢ (∂c)`. For a **cycle** `z` (`∂z = 0`), capping the
  coboundary `δg` gives `(δg) ⌢ z = ∂(g ⌢ z)`, a boundary — so replacing `a` by a cohomologous
  cocycle `a + δg` does not change the homology class. This descends the **cohomology** argument.

We build inner-out, mirroring `kroneckerH`:

1. `capCyclesₗ` — for a fixed cocycle, `cap a` restricted to cycles lands in cycles (descent fact 1i).
2. `capHomology` / `capHomologyₗ` — descend the chain argument to homology via `Submodule.mapQ`
   (boundaries → boundaries, descent fact 1ii), packaged linearly in the cochain.
3. `capH` — descend the cochain argument via `Submodule.liftQ` (well-defined modulo coboundaries,
   descent fact 2).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularCapHomology

variable {X : TopCat} {j k m : ℕ}

/-- `Homology.mk` is additive (the homology class of a sum is the sum of classes). A `rfl`-lemma
(`Homology.mk` is `Submodule.Quotient.mk`), stated so it rewrites cheaply without unfolding the
homology quotient. -/
theorem Homology.mk_add (n : ℕ) (u v : cycles X n) :
    Homology.mk X n (u + v) = Homology.mk X n u + Homology.mk X n v := rfl

/-- `Homology.mk` commutes with the `ℤ/2`-action. A `rfl`-lemma (cheap rewrite). -/
theorem Homology.mk_smul (n : ℕ) (s : ZMod 2) (u : cycles X n) :
    Homology.mk X n (s • u) = s • Homology.mk X n u := rfl

/-- A homology class vanishes iff its representative cycle is a boundary. -/
theorem Homology.mk_eq_zero (n : ℕ) (u : cycles X n) :
    Homology.mk X n u = 0 ↔ u ∈ (boundaries X n).submoduleOf (cycles X n) :=
  Submodule.Quotient.mk_eq_zero _

/-- For a fixed `k`-**cocycle** `a` (`δa = 0`), `cap a` restricted to the `(k+m+1)`-cycles lands in
the `(m+1)`-cycles: by the chain-map fact `cap_cocycle_chainMap`, `∂(a ⌢ z) = a ⌢ (∂z) = a ⌢ 0 = 0`.
Packaged as a `ℤ/2`-linear map `Z_{k+m+1} → Z_{m+1}` (descent fact 1i, the homology-argument step). -/
noncomputable def capCyclesₗ (a : LinearMap.ker (coboundaryₗ X k)) :
    cycles X (k + m + 1) →ₗ[ZMod 2] cycles X (m + 1) :=
  LinearMap.restrict (cap (m := m + 1) a.1) (p := cycles X (k + m + 1)) (q := cycles X (m + 1))
    fun z hz => by
      show chainBoundary X m (cap a.1 z) = 0
      have hz' : chainBoundary X (k + m) z = 0 := hz
      rw [cap_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2) z, hz', map_zero]

@[simp] theorem capCyclesₗ_coe (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    (capCyclesₗ (m := m) a z : SingularChain X (m + 1)) = cap a.1 (z : SingularChain X (k + m + 1)) :=
  LinearMap.restrict_coe_apply _ _ _

/-- For a fixed `k`-cocycle `a`, `cap a` descends to a `ℤ/2`-linear map on homology
`H_{k+m+1} → H_{m+1}`: it sends boundaries to boundaries, since `a ⌢ ∂w = ∂(a ⌢ w)` by the chain-map
fact (descent fact 1ii). The homology-argument descent for a fixed cocycle. -/
noncomputable def capHomology (a : LinearMap.ker (coboundaryₗ X k)) :
    Homology X (k + m + 1) →ₗ[ZMod 2] Homology X (m + 1) :=
  Submodule.mapQ _ _ (capCyclesₗ a) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    -- `z` is a boundary `∂w`; `a ⌢ z = ∂(a ⌢ w)` is a boundary.
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hzb
    obtain ⟨w, hw⟩ := hzb
    refine ⟨cap (m := m + 2) a.1 w, ?_⟩
    show chainBoundary X (m + 1) (cap a.1 w) = cap a.1 z
    rw [cap_cocycle_chainMap (m := m + 1) a.1 (LinearMap.mem_ker.mp a.2) w]
    exact congrArg (cap a.1) hw)

@[simp] theorem capHomology_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    capHomology (m := m) a (Homology.mk X (k + m + 1) z) = Homology.mk X (m + 1) (capCyclesₗ a z) :=
  Submodule.mapQ_apply _ _ _ _

/-- `capCyclesₗ` is additive in the cochain (at the cycle level): `(a + a') ⌢ z = a ⌢ z + a' ⌢ z`. -/
theorem capCyclesₗ_add (a a' : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    capCyclesₗ (a + a') z = capCyclesₗ a z + capCyclesₗ a' z := by
  apply Subtype.ext
  simp only [capCyclesₗ_coe, Submodule.coe_add]
  exact cap_add_cochain (k := k) (m := m + 1) a.1 a'.1 z.1

/-- `capCyclesₗ` commutes with the `ℤ/2`-action in the cochain (at the cycle level). -/
theorem capCyclesₗ_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    capCyclesₗ (s • a) z = s • capCyclesₗ a z := by
  apply Subtype.ext
  simp only [capCyclesₗ_coe, SetLike.val_smul]
  exact cap_smul_cochain (k := k) (m := m + 1) s a.1 z.1

/-- `capHomology` is additive in the cochain. Checked on representatives via `capCyclesₗ_add`. -/
theorem capHomology_add (a a' : LinearMap.ker (coboundaryₗ X k)) :
    capHomology (m := m) (a + a') = capHomology a + capHomology a' := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capHomology (a + a') (Homology.mk X (k + m + 1) z)
    = capHomology a (Homology.mk X (k + m + 1) z) + capHomology a' (Homology.mk X (k + m + 1) z)
  rw [capHomology_mk, capHomology_mk, capHomology_mk, ← Homology.mk_add, capCyclesₗ_add]

/-- `capHomology` commutes with the `ℤ/2`-action in the cochain. Checked on representatives. -/
theorem capHomology_smul (s : ZMod 2) (a : LinearMap.ker (coboundaryₗ X k)) :
    capHomology (m := m) (s • a) = s • capHomology a := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capHomology (s • a) (Homology.mk X (k + m + 1) z)
    = s • capHomology a (Homology.mk X (k + m + 1) z)
  rw [capHomology_mk, capHomology_mk, ← Homology.mk_smul, capCyclesₗ_smul]

/-- The map `a ↦ capHomology a`, packaged as `ℤ/2`-linear in the cochain (before descending the
cohomology quotient). Linearity is `capHomology_add`/`capHomology_smul`. -/
noncomputable def capHomologyₗ :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ZMod 2]
      (Homology X (k + m + 1) →ₗ[ZMod 2] Homology X (m + 1)) where
  toFun := capHomology
  map_add' := capHomology_add
  map_smul' := capHomology_smul

/-- The cap of a `0`-cochain that is `0`: `(0 : C⁰) ⌢ z = 0`. -/
theorem cap_zero_cochain (z : SingularChain X (0 + (m + 1))) :
    cap (0 : SingularCochain X 0) z = (0 : SingularChain X (m + 1)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single σ s => rw [cap_single_smul]; simp [capBasis]

/-- `chainBoundary` commutes with a degree cast on the chain: a cast cycle is a cycle. (Generic
re-indexing helper, proved by `subst`.) -/
private theorem chainBoundary_cast_eq_zero {a b : ℕ} (z : SingularChain X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) (hz : chainBoundary X a z = 0) :
    chainBoundary X b (e ▸ z) = 0 := by
  subst eb
  rw [show e = rfl from rfl]
  simpa using hz

/-- **The cohomology-argument descent fact (coboundary in degree `j+1`)**: for a `j`-cochain `g`, its
coboundary `δg` caps a `(j+1+m+1)`-**cycle** `z` (`∂z = 0`) to a `(m+1)`-**boundary**. `cap_leibniz`
gives `∂(g ⌢ z) = (δg) ⌢ z + g ⌢ (∂z)`; the last term dies (`∂z = 0`), so `(δg) ⌢ z = ∂(g ⌢ z)` is a
boundary. The `cap_leibniz` degree convention `j+(m+1)+1` is bridged to the `capH` convention
`j+1+m+1` by a single pair of cancelling casts. This is what makes `capH` well-defined modulo
coboundaries in the cohomology argument. -/
theorem cap_coboundary_cycle_mem_boundaries (g : SingularCochain X j)
    (z : SingularChain X (j + 1 + m + 1)) (hz : chainBoundary X (j + 1 + m) z = 0) :
    cap (m := m + 1) (coboundary X j g) z ∈ boundaries X (m + 1) := by
  -- Cast `z` into `cap_leibniz`'s convention degree `j + (m+1) + 1`; the casts cancel at the end.
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  have hz' : chainBoundary X (j + (m + 1)) (e ▸ z) = 0 :=
    chainBoundary_cast_eq_zero z e (by omega) hz
  refine ⟨cap (m := m + 2) g (e ▸ z), ?_⟩
  have hleib := cap_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  rw [hz', map_zero, add_zero] at hleib
  -- `h ▸ (e ▸ z) = z`: the composite cast is over the defeq `j + 1 + m + 1 = j + 1 + (m + 1)`.
  have hcancel : (h ▸ (e ▸ z) : SingularChain X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rwa [hcancel] at hleib

/-- **The cap product on (co)homology** `⌢ : Hᵏ × H_{k+m+1} → H_{m+1}` — a genuine `ℤ/2`-bilinear map
(the homological analogue of `kroneckerH`/`cupH`). Well-defined: a cocycle caps a cycle to a cycle and
a boundary to a boundary (`cap_cocycle_chainMap`, descending the homology quotient via `capHomology`),
and a *coboundary* caps a cycle to a boundary (`cap_leibniz`: `(δg) ⌢ z = ∂(g ⌢ z)`, descending the
cohomology quotient). The substrate for the Poincaré-duality map `[M] ⌢ ·`. -/
noncomputable def capH (k m : ℕ) :
    Cohomology X k →ₗ[ZMod 2]
      Homology X (k + m + 1) →ₗ[ZMod 2] Homology X (m + 1) :=
  Submodule.liftQ _ capHomologyₗ (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.zero_apply]
    show capHomology a (Homology.mk X (k + m + 1) z) = 0
    rw [capHomology_mk, Homology.mk_eq_zero]
    -- Reduce to: the representative `cap a.1 z.1` is a `(m+1)`-boundary.
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, capCyclesₗ_coe]
    -- `a = δg` is a coboundary; `(δg) ⌢ z = ∂(g ⌢ z)` is a boundary, hence `0` in homology.
    have hzc : chainBoundary X (k + m) z.1 = 0 :=
      LinearMap.mem_ker.mp (z.2 : z.1 ∈ LinearMap.ker (chainBoundary X (k + m)))
    cases k with
    | zero =>
        rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
          Submodule.mem_bot] at ha
        rw [show (a.1 : SingularCochain X 0) = 0 from ha, cap_zero_cochain]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        rw [← hg]
        exact cap_coboundary_cycle_mem_boundaries g z.1 hzc)

@[simp] theorem capH_mk_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    capH k m (Cohomology.mk X k a) (Homology.mk X (k + m + 1) z)
      = Homology.mk X (m + 1) (capCyclesₗ a z) :=
  rfl

end SKEFTHawking.SingularCapHomology
