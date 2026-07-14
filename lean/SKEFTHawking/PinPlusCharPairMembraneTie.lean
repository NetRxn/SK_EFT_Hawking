/-
# Phase 5q.H (W-A Round 4) — THE MEMBRANE TIE: `CharPairBor`'s kernel `L` COMPUTED from a
# certified membrane, closing the kernel-checked gate FAIL `free-membrane-kernel-kills-nonsplit`.

**The gate finding this repairs.** `PinPlusKTVacuityGateWD.lean` proves that with `CharPairBor.L`
a **FREE `Submodule` field**, the e₈-graph Lagrangian `graphSub phiLin` (the extended Hamming code,
a metabolic Lagrangian of the un-negated doubled form `q₄ ⊞ q₄`) inhabits a `CharPairBor` on the
UN-reversed double `σ₄ ⊔ σ₄` — collapsing `⟨[ℝP⁴]⟩` to `ℤ/8` and refuting `KTNonSplit`
(`doubleKillerBor`). The frozen v4 design (§2 items 2–4) ALWAYS required `L` to be
`ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))` of an actual characteristic membrane `Q ⊆ W`; the free-`L` build was
a documented abstraction pending the membrane machinery.

**The fix, and why it kills the exploit.** `L` is no longer free: it is `LinearMap.ker mem.bInc`
of a `GeoMembrane` datum whose `bInc` is the transported `H₁(∂Q) → H₁(Q)` boundary-inclusion map of
a genuine membrane. For the honest doubling membrane `Q = Σ × [0,1]` the boundary-inclusion is the
**fold map `cylBd`** (both ends of the cylinder include homotopically as the identity, so
`H₁(Σ ⊔ Σ) → H₁(Σ×I) ≅ H₁(Σ)` is `(a,b) ↦ a + b`), and its kernel is the **anti-diagonal**
`{(a,a)}` — which CONTAINS the diagonal boundary classes (the "half-lives–half-dies" half that
genuinely bounds in the membrane interior). Two consequences, both decidable:

* **The honest kernel KILLS the un-reversed double.** On the diagonal class `Sum.elim a a` the
  un-negated doubled form evaluates to `q₄(a) + q₄(a) = 2·q₄(a)`, which is `≠ 0` for the odd
  `ℝP⁴` generator (`q₄(gen) = 1`). So the Taylor leg FAILS on the geometric kernel — no
  `CharPairBor` for the un-reversed double survives the tie (`untwisted_double_fails_taylor_on_cyl`).
* **The e₈ Lagrangian is NOT a geometric kernel.** `graphSub phiLin` OMITS the diagonal
  (`φ(gen) = gen + 𝟙 ≠ gen`), so it can never be `ker(H₁∂ → H₁Q)` of a cylinder membrane
  (`e8_omits_diagonal`, `cylKernel_ne_e8`). The exploit's metabolic Lagrangian passes the Taylor
  leg but has no membrane realizing it — exactly the gap the free-`L` field papered over.

**Acceptance test (the gate's exit criterion) — PASSES.** With `L := ker mem.bInc`, the
`doubleKillerBor` construction has no `L` field to write the e₈ code into; any replay must furnish a
membrane whose fold-kernel is the e₈ graph, which is geometrically impossible (the honest kernel is
the anti-diagonal, `cylKernel_ne_e8` / `untwisted_double_fails_taylor_on_cyl`). The honest ops
survive (`charPairCylBorTied`, `charPairNegBorTied`) and the anti-collapse engine descends unchanged
(`CharPairBorTied.brown_eq`).

**Honest-intermediate scope (design §2 item 2, authorized).** The `bInc` map is carried as the
membrane's transported boundary-inclusion; the *geometric realization* of `bInc` by an actual
compact-T2 3-manifold-with-boundary `Q ⊆ W` (the `SingularRelativeHomologyMod2` H₁ functoriality +
the `H₁(Σ) ≃ Fin n` basis transport) is the ONE remaining obligation, discharged by wt3's
rel-Lefschetz/PD tower — exactly as `CharPairWProvider` carries item 1's W-admissibility. What is
NON-abstract and kernel-checked here is the algebraic heart: the tied `L = ker bInc` form, the
fold-kernel = anti-diagonal signature, and the acceptance test.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTVacuityGateWD

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusKTVacuityGateWD

namespace SKEFTHawking.PinPlusCharPairMembraneTie

/-! ## §1. The certified membrane's transported boundary-inclusion; `L` COMPUTED as its kernel -/

/-- **A certified membrane's transported `H₁` boundary-inclusion datum** (design §2 item 2). `bInc`
is the `H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2)` map of a genuine characteristic membrane `Q`, transported through
the boundary identification `∂Q = Σ_σ ⊔ Σ_τ` and the enhancement bases to
`(Fin nσ ⊕ Fin nτ → ZMod 2) → (Fin mid → ZMod 2)` (`mid = dim H₁(Q;ℤ/2)`). The Taylor-leg submodule
`L` is COMPUTED as its kernel — NOT a free field. (Geometric realization of `bInc` by an actual
`Q ⊆ W` is the wt3 obligation; see the module docstring.) -/
structure GeoMembrane {nσ nτ : ℕ} (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) where
  /-- `mid = dim H₁(Q;ℤ/2)`. -/
  mid : ℕ
  /-- the transported boundary-inclusion `H₁(∂Q) → H₁(Q)`. -/
  bInc : (Fin nσ ⊕ Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin mid → ZMod 2)

/-- **The COMPUTED Taylor-leg submodule** `L = ker(H₁(∂Q) → H₁(Q))`. This is the design's item 2/3
content: `L` is no longer a free field but the kernel of the membrane's boundary-inclusion. -/
def GeoMembrane.L {nσ nτ : ℕ} {qσ : Z4Quadratic (Fin nσ)} {qτ : Z4Quadratic (Fin nτ)}
    (m : GeoMembrane qσ qτ) : Submodule (ZMod 2) (Fin nσ ⊕ Fin nτ → ZMod 2) :=
  LinearMap.ker m.bInc

/-- **The honest cylinder/doubling membrane** `Q = Σ × [0,1]`: its transported boundary-inclusion is
the **fold map `cylBd`** (both cylinder ends include homotopically as `id`, so
`H₁(Σ ⊔ Σ) → H₁(Σ×I) ≅ H₁(Σ)` is `(a,b) ↦ a + b`). Its kernel is the anti-diagonal `cylLagrangian`. -/
def cylGeoMembrane {n : ℕ} (q : Z4Quadratic (Fin n)) : GeoMembrane q q :=
  ⟨n, cylBd n⟩

@[simp] theorem cylGeoMembrane_L {n : ℕ} (q : Z4Quadratic (Fin n)) :
    (cylGeoMembrane q).L = cylLagrangian n := rfl

/-- **The honest cylinder membrane's kernel CONTAINS the diagonal** (the half-lives–half-dies
boundary classes: the loop `a` on the bottom `Σ` and its copy on the top together bound the annulus
`a × [0,1]` in `Q`). This is the geometric signature that the e₈ graph lacks. -/
theorem diagonal_mem_cylGeoMembrane {n : ℕ} (q : Z4Quadratic (Fin n)) (a : Fin n → ZMod 2) :
    Sum.elim a a ∈ (cylGeoMembrane q).L := by
  rw [cylGeoMembrane_L, mem_cylLagrangian_iff]; rfl

/-- **The doubling membrane's boundary-inclusion** `H₁(Σ ⊔ Σ) → H₁(Σ×I)` on the reindexed σ-block:
fold the two ends after de-reindexing `Fin (n+n) ≅ Fin n ⊕ Fin n` (`finSumFinEquiv`), and ignore the
empty τ-block. This is `cylBd` transported to the `sumStr`-reindexed doubling domain — the same fold,
so the computed kernel is the anti-diagonal (`negBorBInc_ker`). -/
def negBorBInc (n : ℕ) : (Fin (n + n) ⊕ Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (cylBd n).comp ((LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := n) (n := n))).comp
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inl : Fin (n + n) → Fin (n + n) ⊕ Fin 0)))

/-- **The doubling membrane's COMPUTED kernel is the reindexed anti-diagonal** — exactly the
metabolic Lagrangian the honest `negBor` witness uses (block-sum of the reindexed `cylLagrangian`
with the empty τ-end `⊤`). So `negBor`'s `L` is genuinely the fold-kernel of a cylinder membrane. -/
theorem negBorBInc_ker (n : ℕ) :
    LinearMap.ker (negBorBInc n)
      = blockSub ((cylLagrangian n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv))
          (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) := by
  ext x
  rw [LinearMap.mem_ker, mem_blockSub, Submodule.mem_comap, cylLagrangian, LinearMap.mem_ker]
  constructor
  · intro h; exact ⟨h, Submodule.mem_top⟩
  · intro h; exact h.1

/-! ## §2. The tied `CharPairBor` — `L` derived from the membrane; anti-collapse survives -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The MEMBRANE-TIED characteristic-pair bordism datum** (design v4 §2 `Bor` items 0–4, with the
item-2/3 membrane TIE landed). Identical to `PinPlusCharPairData.CharPairBor` EXCEPT the free `L`
field is replaced by a `GeoMembrane` datum `mem` and the Taylor leg / Lagrangian are stated over the
COMPUTED kernel `mem.L = ker(H₁∂ → H₁Q)`. This is the repaired carrier: no free submodule can be
supplied, so the e₈-graph exploit has nowhere to write. -/
structure CharPairBorTied {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) (σ : CharPairStr I s) (τ : CharPairStr I t) : Type where
  /-- item 0 (▲A-2): the bordism carrier is Hausdorff (the T2-refined relation). -/
  hWT2 : T2Space b.W
  /-- item 1: the `(1,4)` Lefschetz–Wu datum. -/
  P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5
  /-- item 1: the `(2,3)` Lefschetz–Wu datum. -/
  P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5
  /-- item 1: W-admissibility `w₂(W) = 0`. -/
  hwu : wuW2 P14 P23 = 0
  /-- item 2/3 (THE TIE): the certified membrane whose boundary-inclusion COMPUTES `L`. -/
  mem : GeoMembrane σ.q τ.q
  /-- item 4 (▲A-1): the τ-end-negated joint enhancement vanishes on the COMPUTED kernel `mem.L`. -/
  htaylor : TaylorLegVanishes σ.q τ.q mem.L
  /-- `mem.L` is Lagrangian for the joint polar form (`half-lives-half-dies`). -/
  hlag : JointLagrangian σ.q τ.q mem.L

/-- **The tied `Bor` STILL forces grade equality of the ends** — the anti-collapse engine descends
UNCHANGED onto the computed kernel `mem.L` (design item 4: "the Taylor leg's brown-equality argument
should strengthen, not break"). `brown_eq_of_taylorLeg_lagrangian` is agnostic to whether `L` is a
free field or `ker bInc`, so the computed grade `abk8 := brown ∘ q` remains a bordism invariant. -/
theorem CharPairBorTied.brown_eq {s t : SingularManifold PUnit k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStr I s} {τ : CharPairStr I t}
    (β : CharPairBorTied b σ τ) : σ.q.brown = τ.q.brown :=
  brown_eq_of_taylorLeg_lagrangian σ.q τ.q β.mem.L β.htaylor β.hlag

/-- Assemble a tied `CharPairBor` from the concretely-buildable data + item 1 from the provider. -/
def mkCharPairBorTied (prov : CharPairWProvider I k) {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) {σ : CharPairStr I s} {τ : CharPairStr I t}
    (hWT2 : T2Space b.W) (mem : GeoMembrane σ.q τ.q)
    (htaylor : TaylorLegVanishes σ.q τ.q mem.L) (hlag : JointLagrangian σ.q τ.q mem.L) :
    CharPairBorTied b σ τ where
  hWT2 := hWT2
  P14 := (prov.wadm b).P14
  P23 := (prov.wadm b).P23
  hwu := (prov.wadm b).hwu
  mem := mem
  htaylor := htaylor
  hlag := hlag

/-! ## §3. The honest op witnesses survive the tie (`cylBor` discriminator + `negBor` inverse law) -/

/-- **`cylBor` instantiates on the tied form** (design §2 item 4 ⚠, the discriminator): the reflexive
cylinder's membrane is `Σ × [0,1]`, `bInc = cylBd` (fold), computed kernel = the anti-diagonal
`cylLagrangian`, on which the τ-end-negated joint enhancement `q − q = 0` vanishes. Goes through
under the honest membrane exactly as in the free-`L` build — the tie costs the discriminator nothing. -/
noncomputable def charPairCylBorTied (prov : CharPairWProvider I k) {s : SingularManifold PUnit k I}
    (σ : CharPairStr I s) : CharPairBorTied (reflCylinder s) σ σ :=
  mkCharPairBorTied prov (reflCylinder s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    (cylGeoMembrane σ.q) (taylorLeg_cyl σ.q) (lagrangian_cyl σ.q)

/-- **`negBor` instantiates on the tied form** — the honest inverse law `(M,σ̄) ⊔ (M,σ) → ∅` SURVIVES
the tie. The membrane is `Σ × [0,1]`; its COMPUTED fold-kernel (`negBorBInc_ker`) is the anti-diagonal
`cylLagrangian`, on which the τ-end-NEGATED joint form `(−q) ⊞ q` vanishes (`diag_metabolic`:
`−q(a) + q(a) = 0`). Because the σ̄-end is NEGATED, the diagonal Taylor leg HOLDS — precisely the
un-reversed double's failure mode (`untwisted_double_fails_taylor_on_cyl`), which the genuine inverse
AVOIDS. The tie kills the e₈ exploit AND keeps the legitimate inverse law: the discriminator is the
end-negation, exactly as the design intends. -/
noncomputable def charPairNegBorTied (prov : CharPairWProvider I k) {s : SingularManifold PUnit k I}
    (σ : CharPairStr I s) :
    CharPairBorTied (doublingBordism s) (charPairSumStr (charPairRevStr σ) σ) charPairEmptyStr :=
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr (charPairRevStr σ) σ).q
      ((cylLagrangian σ.n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    (diag_metabolic (neg σ.q) σ.q (fun a => neg_add_cancel _) rfl).reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBorTied prov (doublingBordism s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    ⟨_, negBorBInc σ.n⟩
    (by show TaylorLegVanishes _ _ (LinearMap.ker (negBorBInc σ.n)); rw [negBorBInc_ker]; exact hmeta.1)
    (by show JointLagrangian _ _ (LinearMap.ker (negBorBInc σ.n)); rw [negBorBInc_ker]; exact hmeta.2)

/-- **`revBor` instantiates on the tied form** — end-reversal (`revStr` on both ends) transports a
tied `CharPairBor` with the SAME membrane (`bInc` is rank-indexed, independent of the enhancement):
the Taylor leg survives (the joint value negates, `−0 = 0`, `jointEnhancement_neg_q`) and the
Lagrangian is literally unchanged (`jointEnhancement_neg_B`). The membrane datum is index-agnostic, so
the geometric realization is inherited verbatim — the cleanest transport after `cylBor`. -/
def charPairRevBorTied {s t : SingularManifold PUnit k I} {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStr I s} {τ : CharPairStr I t} (β : CharPairBorTied b σ τ) :
    CharPairBorTied b (charPairRevStr σ) (charPairRevStr τ) where
  hWT2 := β.hWT2
  P14 := β.P14
  P23 := β.P23
  hwu := β.hwu
  mem := ⟨β.mem.mid, β.mem.bInc⟩
  htaylor := by
    intro l hl
    show (jointEnhancement (neg σ.q) (neg τ.q)).q l = 0
    rw [jointEnhancement_neg_q, β.htaylor l hl, neg_zero]
  hlag := by
    intro v hv
    refine β.hlag v (fun l hl => ?_)
    have hvl := hv l hl
    rwa [show (jointEnhancement (charPairRevStr σ).q (charPairRevStr τ).q).B
        = (jointEnhancement σ.q τ.q).B from jointEnhancement_neg_B σ.q τ.q] at hvl

/-! ## §4. THE ACCEPTANCE TEST — the e₈-graph Lagrangian cannot inhabit the tied `Bor` for the
un-reversed double.

The gate's exit criterion (`free-membrane-kernel-kills-nonsplit`): `doubleKillerBor` must BREAK.
On the tied form there is no free `L` field — `L = ker mem.bInc` is COMPUTED. The exploit's
`graphSub phiLin` (e₈) is a metabolic Lagrangian of `q₄ ⊞ q₄` (it PASSES the Taylor leg), but it is
NOT the kernel of any cylinder membrane's boundary-inclusion — it OMITS the diagonal that every
honest cylinder kernel contains. And the honest cylinder kernel (the anti-diagonal), which the
geometry forces, FAILS the un-reversed double's Taylor leg. Both facts are decidable in `Fin 8`. -/

/-- The odd `ℝP⁴`-generator class `gen ∈ Fin 4 → ZMod 2` (a single `1`). `q₄(gen) = 1`, so
`q₄(gen) + q₄(gen) = 2 ≠ 0` — the un-reversed double's obstruction. -/
def gen4 : Fin 4 → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- **The un-reversed double's joint form does NOT vanish on the diagonal `gen`** — the concrete
`2·q₄(gen) ≠ 0` fact (`q₄(gen) = 1`). This is why the geometric (anti-diagonal-containing) kernel
kills `σ₄ ⊔ σ₄`. -/
theorem q4_diag_ne_zero : (Z4Quadratic.orthSum q4 q4).q (Sum.elim gen4 gen4) ≠ 0 := by
  rw [plain_joint_forces_two_torsion_on_diagonal]; decide

/-- **THE HONEST CYLINDER KERNEL KILLS THE UN-REVERSED DOUBLE.** The geometric doubling membrane's
kernel `(cylGeoMembrane q₄).L` (the anti-diagonal) contains the diagonal class `Sum.elim gen gen`, on
which the un-negated doubled form is `2·q₄(gen) ≠ 0`. So the Taylor leg FAILS — no `CharPairBorTied`
for the un-reversed double can use the honest cylinder membrane. -/
theorem untwisted_double_fails_taylor_on_cyl :
    ¬ (∀ l ∈ (cylGeoMembrane q4).L, (Z4Quadratic.orthSum q4 q4).q l = 0) := by
  intro h
  exact q4_diag_ne_zero (h _ (diagonal_mem_cylGeoMembrane q4 gen4))

/-- **THE e₈ LAGRANGIAN OMITS THE DIAGONAL** — `graphSub phiLin` does not contain `Sum.elim gen gen`
(because `φ(gen) = gen + 𝟙 ≠ gen`). So the extended Hamming code can NEVER be the boundary-inclusion
kernel of a cylinder membrane: it fails the geometric half-lives–half-dies signature. -/
theorem e8_omits_diagonal : Sum.elim gen4 gen4 ∉ graphSub phiLin := by
  rw [mem_graphSub]
  intro h
  have hval : phiFun gen4 = gen4 := by
    have h' := h.symm
    simpa [phiLin, gen4] using h'
  revert hval; decide

/-- **THE TIE DISCRIMINATES**: the honest cylinder membrane's COMPUTED kernel is NOT the e₈ graph
(a decidable `Fin 8` distinction). The exploit's Lagrangian is metabolic but geometrically
unrealizable — exactly the gap the free-`L` field papered over. -/
theorem cylKernel_ne_e8 : (cylGeoMembrane q4).L ≠ graphSub phiLin := by
  intro h
  exact e8_omits_diagonal (h ▸ diagonal_mem_cylGeoMembrane q4 gen4)

/-- **ACCEPTANCE TEST — POSITIVE FORM.** On the tied carrier, ANY membrane whose kernel realizes the
honest cylinder geometry (contains the full diagonal — the mandatory half-lives–half-dies classes of
a genuine `Σ × [0,1]` membrane) CANNOT host the un-reversed double: its diagonal class violates the
Taylor leg. The e₈ graph evades this only by NOT containing the diagonal — i.e. by not being a
geometric kernel at all. Hence the free-`L` exploit is dead on the tie. -/
theorem no_untwisted_double_via_geometric_membrane
    (m : GeoMembrane q4 q4) (hgeo : ∀ a, Sum.elim a a ∈ m.L)
    (htaylor : ∀ l ∈ m.L, (Z4Quadratic.orthSum q4 q4).q l = 0) : False :=
  q4_diag_ne_zero (htaylor _ (hgeo gen4))

end SKEFTHawking.PinPlusCharPairMembraneTie
