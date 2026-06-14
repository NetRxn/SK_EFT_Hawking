import Mathlib
import SKEFTHawking.BrownInvariant

/-!
# The Guillou–Marin / Kirby–Taylor bridge: the derived Brown invariant in Ω₄^{Pin⁺}

Phase 5q.F lower-bound entry. Connects the kernel-pure Brown/ABK invariant (`BrownInvariant.lean`) to the
Pin⁺ 4-manifold ℤ₁₆ bordism group via the **Guillou–Marin / Kirby–Taylor formula**

  `σ(X) − F·F ≡ 2·β(F)  (mod 16)`

(Guillou–Marin 1980; Kirby–Taylor 1990, *Comment. Math. Helv.* 65; sources collated in
`Lit-Search/Phase-5qF/KT_eta_lower_bound.md`). Here `β(F) ∈ ℤ/8` is the Arf–Brown–Kervaire invariant of
the characteristic surface `F`'s `ZMod 4`-quadratic enhancement — and that enhancement and its Gauss sum
match **verbatim** the project's already-built kernel-pure invariant: our `Z4Quadratic.refine'`
(`q(x+y)=q x+q y+2·B`) is Debray (arXiv:1803.11183) Eq. 3.11, and our `gaussSum4 = ∑ᵢ i^{q(x)}` is his
Eq. 3.14 `AB(Σ)=(1/√|H₁|)∑ exp(2πi·q/4)`. So `brown` **is** the literature ABK.

**Honest scope (no over-claim).** The GM term `2·β` is even-valued, so it detects exactly the **even
subgroup `ℤ/8 ⊂ Ω₄^{Pin⁺} ≅ ℤ/16`** (the `2·β` image): the derived Brown invariant gives `|Ω₄^{Pin⁺}| ≥ 8`
from genuine surface data (modulo the cited GM bordism-invariance). The full `≥ 16` — the **odd** generator
`η(RP⁴)=1/16` — is the irreducibly geometric/analytic η-invariant top-bit (APS), which the sources'
`KT/16` normalization does NOT cleanly pin (the DR flags: "anchor on η(RP⁴):=1/16; convention not
canonical"). That top-bit is **tracked/cited, not built here**. Respects `[[nogo-lattice-arf-not-sigma8]]`:
the `2·β` term is the embedded-characteristic-**surface** ABK (our `brown`), NOT the lattice Arf.
-/

namespace SKEFTHawking.GuillouMarin

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ℤ/8 → ℤ/16` doubling of the derived Brown invariant — the `2·β` term of Guillou–Marin. -/
noncomputable def doubleBrown (Q : Z4Quadratic ι) : ZMod 16 := 2 * (Q.brown.val : ZMod 16)

@[simp] lemma doubleBrown_stdQuadratic (g : ℕ) :
    doubleBrown (stdQuadratic g) = 2 * (((g : ZMod 8)).val : ZMod 16) := by
  unfold doubleBrown; rw [brown_stdQuadratic]

/-- The **Guillou–Marin / Kirby–Taylor relation** `σ(X) − F·F ≡ 2·β(F) (mod 16)` (cited verbatim),
with `β(F)` the DERIVED Brown invariant of the characteristic surface. -/
def GMrelation (σ F_F : ℤ) (Q : Z4Quadratic ι) : Prop :=
  ((σ - F_F : ℤ) : ZMod 16) = doubleBrown Q

/-- **RP⁴ satisfies Guillou–Marin** with characteristic surface `RP² = stdQuadratic 1`:
`σ(RP⁴)=0`, `F·F=−2`, `β(RP²)=brown(stdQuadratic 1)=1`, and `0−(−2)=2=2·1`. Kernel-pure via the derived
Brown invariant. -/
theorem GM_rp4 : GMrelation (0 : ℤ) (-2) (stdQuadratic 1) := by
  show ((0 - (-2) : ℤ) : ZMod 16) = doubleBrown (stdQuadratic 1)
  rw [doubleBrown_stdQuadratic]; decide

/-- The GM invariant `2·β` takes **8 distinct values** on the standard surfaces `stdQuadratic 0..7` —
the derived Brown invariant detects the even subgroup `ℤ/8 ⊂ Ω₄^{Pin⁺} ≅ ℤ/16`, giving `|Ω₄^{Pin⁺}| ≥ 8`
(modulo the cited GM bordism-invariance). The full `≥ 16` is the η top-bit (not built here). -/
theorem doubleBrown_eight_distinct :
    Function.Injective (fun g : Fin 8 => doubleBrown (stdQuadratic g.val)) := by
  have key : (fun g : Fin 8 => doubleBrown (stdQuadratic g.val))
      = (fun g : Fin 8 => 2 * (g.val : ZMod 16)) := by
    funext g
    rw [doubleBrown_stdQuadratic, ZMod.val_natCast_of_lt g.isLt]
  rw [key]; decide

end SKEFTHawking.GuillouMarin
