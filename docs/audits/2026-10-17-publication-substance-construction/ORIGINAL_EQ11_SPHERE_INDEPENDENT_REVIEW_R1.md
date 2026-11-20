# Independent quaternion–SU(2) sphere proof review

**ACCEPT** exact worker commit `9a5cc446332865d7440cd306da37c7e74eadb924`
on `487a2b3a7cb9c5bd0fc7198016350520335b6010` for the pointwise
sphere homeomorphism and equivariant isometric action. The sole added
path is `lean/SKEFTHawking/ADW/QuaternionSU2Sphere.lean` and its SHA256
is `a7941038e655d8737812f9e174099d4659332ff72690f906d0fd4dc514b42a74`.
The exact committed diff passed whitespace checking and the slot was
clean. Intake and terminal continuity matched byte-for-byte.

## Exact source review

- The target uses the project's actual `Matrix.specialUnitaryGroup (Fin 2) ℂ`,
  and the domain uses `Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`.
  The norm proof computes the sum of four coordinate squares in the
  Euclidean norm. No equivalence, norm identity or action law is supplied
  as a premise.
- `realBlock` reuses the previously accepted plus-i block, matching both
  chiral components of `original_spin4_link`. The inverse reads
  `(Re A00, Im A01, Re A01, Im A00)`. The two lower-row identities follow
  by equating conjugate transpose with the adjugate. The adjugate is a
  right inverse by determinant one and the conjugate transpose a left
  inverse by unitarity. The inverse coordinates satisfy the unit condition
  by the determinant formula valid for every real coordinate vector.
- Both inverse laws use the exact block and coordinate maps. Continuity
  comes from finite matrix evaluations and the continuous `PiLp` maps,
  restricted to the two subtypes. This establishes an actual homeomorphism
  with the inherited topologies.
- The ambient action `leftMap` reads the coordinates of matrix left
  multiplication, proves real additivity and homogeneity, and reconstructs
  the full multiplied block by entrywise closure. Determinant
  multiplicativity and determinant one imply preservation of squared
  Euclidean norm, hence norm preservation. Left multiplication by the
  actual group inverse supplies surjectivity. `leftIsometry` packages
  these facts as a real linear isometry equivalence on all vectors.
- The sphere restriction intertwines the homeomorphism with actual
  SU(2) multiplication. Identity and composition follow by injectivity
  and the group laws. The source is constructive at the level of these
  mathematical statements, with no admitted proof, added axiom or
  nonstandard proof escape in the exact diff.

## Independent bounded controls

The exact rational-complex Python oracle in `check.py` used a
stereographic parametrization plus the missing pole to generate 126
unit quaternions, and 81 ambient rational vectors including zero.
It matched 414 chiral blocks to `original_spin4_link` and checked
10,206 ambient actions for matrix reconstruction, norm preservation,
inverse, real linearity and composition. The oracle uses separate
pair-of-rationals matrix arithmetic. A coordinate-swap adverse control
failed reconstruction, and the half-coordinate unit vector
distinguished Euclidean and supremum norms. `check.json` holds the exact
terminal counts. These controls corroborate the formulas and are not
kernel or measure evidence.

## Measure boundary

The proved isometry supplies the precise input to Mathlib's
`LinearIsometryEquiv.measurePreserving`. The normalized sphere measure
still needs a proof that the cone construction in
`Measure.toSphere_apply'` is invariant under the restricted action.
Push that probability measure through the proved homeomorphism, show
left invariance by equivariance, then compare with the project's actual
`su2Haar` using compact uniqueness
`Measure.isMulInvariant_eq_smul_of_compactSpace` and both masses on
`univ`. That is a separate proof. All-order moments, independent anchor
products, actual Python integration correspondence, native absorption
and publication acceptance remain separate. This review performed no
kernel, build, slot or repository mutation.
