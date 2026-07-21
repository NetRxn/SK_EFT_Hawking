/-
# Phase 5q.H — K10 span 1: the **integral orientation criterion** for a closed 4-manifold

`IntFundamentalClassOrientation.IntOrientation M` is the `orient` field of every
`SpinSigmaAtomPkg` (`PinPlusKTSpinSigmaAtomReduce`): an integral fundamental class
`[M] ∈ H₄(M;ℤ)` **together with** the mod-2 compatibility `redCompat` pinning its ℤ→ℤ/2 reduction
to the on-main, orientation-free mod-2 fundamental class
`SingularFundamentalClass.fundamentalClass`. Its docstring calls the datum a "community-scale
residual", pointing at the missing *integral local-homology tower* (coherent `±1` generator
choices across chart overlaps).

**That is the wrong reduction for THIS datum.** `IntOrientation M` does not ask for an orientation
of the local system — it asks only that the *already-constructed* mod-2 class `[M]₂` admit an
integral lift under `redHomology`. And the chain-level lift/halve machinery for exactly that
question is already in tree, unconditionally: `SphereProdHTwoMod2.redHomology_surjective` (the
"rank UCT" core) says `redHomology X (n+1)` is surjective as soon as `Hₙ(X;ℤ)` is
2-torsion-free. At `n = 3` that is precisely the Bockstein criterion for `[M]₂` to lift.

So this module replaces the tower residual by a **single homological input**:

> `H₃(M;ℤ)` 2-torsion-free ⟹ `Nonempty (IntOrientation M)`.

(`intOrientation_of_h3_twoTorsionFree`, and the `Subsingleton` corollary
`intOrientation_of_h3_subsingleton`.) The criterion is SHARP, not merely sufficient: §2 records
the exact `iff` (`nonempty_intOrientation_iff_mem_range`) — existence of the datum IS liftability
of `[M]₂` — so nothing is being over-claimed by the sufficient form. §3 fires the criterion at the
in-tree `S⁴` witness (`H₃(S⁴;ℤ) = 0`), a non-vacuity certificate: the criterion produces the
`orient` atom of the already-shipped `S⁴` package from homology alone.

Note the criterion is genuinely restrictive, i.e. it is not a disguised tautology: for a closed
NON-orientable 4-manifold `H₄(M;ℤ) = 0` while `[M]₂ ≠ 0` (`fundamentalClass_ne_zero`), so no lift
exists and the hypothesis must fail — as it does (e.g. `H₃(ℝP⁴;ℤ) ≅ ℤ/2` is 2-torsion). §2's
`iff` is what makes that reading exact.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntFundamentalClassOrientation
import SKEFTHawking.SphereProdHTwoMod2
import SKEFTHawking.SphereWitnessTowerInt

namespace SKEFTHawking.IntOrientationMod2Lift

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFundamentalClass (fundamentalClass)

/-! ## §1. The criterion -/

/-- **The integral orientation datum exists as soon as `H₃(M;ℤ)` is 2-torsion-free.**

For a closed charted 4-manifold `M`, an `IntOrientation M` is exactly a class
`c ∈ H₄(M;ℤ)` with `redHomology 4 c = [M]₂`. The in-tree rank-UCT core
(`SphereProdHTwoMod2.redHomology_surjective`, the lift/halve chain argument) makes
`redHomology M 4` SURJECTIVE whenever `H₃(M;ℤ)` has no 2-torsion, so the on-main mod-2
fundamental class — which exists unconditionally (`hasFundClass_univ`) — is in its image.

This converts the `orient` atom of `SpinSigmaAtomPkg` from the "integral local-homology tower /
coherent generator choice" residual into a single **homological** hypothesis on one degree. -/
theorem intOrientation_of_h3_twoTorsionFree {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (h3 : ∀ x : Homology (TopCat.of M) 3, (2 : ℤ) • x = 0 → x = 0) :
    Nonempty (IntOrientation M) := by
  obtain ⟨c, hc⟩ := SKEFTHawking.SphereProdHTwoMod2.redHomology_surjective
    (X := TopCat.of M) 3 h3 (fundamentalClass (m := 2) (M := M))
  exact ⟨⟨c, hc⟩⟩

/-- **`H₃(M;ℤ) = 0` ⟹ the orientation datum exists** — the `Subsingleton` specialisation of
`intOrientation_of_h3_twoTorsionFree` (a subsingleton module is trivially 2-torsion-free). This is
the form the concrete witnesses use, since the in-tree homology computations deliver vanishing, not
torsion statements. -/
theorem intOrientation_of_h3_subsingleton {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [Subsingleton (Homology (TopCat.of M) 3)] :
    Nonempty (IntOrientation M) :=
  intOrientation_of_h3_twoTorsionFree (fun _ _ => Subsingleton.elim _ _)

/-! ## §2. The criterion is sharp — existence IS liftability of `[M]₂` -/

/-- **`Nonempty (IntOrientation M)` ↔ `[M]₂` lifts.** The datum's content is *exactly* membership
of the mod-2 fundamental class in the range of the reduction `redHomology M 4`; there is no further
coherence obligation hidden in the structure. Stated so the §1 sufficient criterion is visibly not
an over-approximation: `intOrientation_of_h3_twoTorsionFree` discharges the RHS, and any other
route to the RHS discharges the datum. -/
theorem nonempty_intOrientation_iff_mem_range {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :
    Nonempty (IntOrientation M) ↔
      fundamentalClass (m := 2) (M := M) ∈ Set.range (redHomology (TopCat.of M) 4) :=
  ⟨fun ⟨o⟩ => ⟨o.fundClass, o.redCompat⟩, fun ⟨c, hc⟩ => ⟨⟨c, hc⟩⟩⟩

/-! ## §3. Non-vacuity: the criterion fires at the in-tree `S⁴` witness -/

open SKEFTHawking.SphereWitnessTowerInt (SphereFour)

/-- **The criterion produces the `S⁴` orientation atom from homology alone.** `H₃(S⁴;ℤ) = 0` is
computed in tree (`SphereWitnessTowerInt.sphere4_homology_three_eq_zero`, the integral sphere
tower's middle vanishing), so §1 hands back an `IntOrientation SphereFour` — the `orient` field of
`PinPlusKTSpinSigmaStock.sphere4IntOrientation`, obtained here WITHOUT the orientation-section
construction (`sphere4IntOrientationDataUncond`) that module routes through. Non-vacuity certificate
for §1: its hypothesis is satisfiable and its conclusion is a datum the project already uses. -/
theorem intOrientation_sphere4 : Nonempty (IntOrientation SphereFour) :=
  intOrientation_of_h3_subsingleton

end SKEFTHawking.IntOrientationMod2Lift
