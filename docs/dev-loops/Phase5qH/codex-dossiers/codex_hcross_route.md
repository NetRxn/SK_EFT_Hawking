# codex_hcross_route

> **Promoted from session scratchpad 2026-07-21.** The raw ~1-2 MB codex
> transcript was session-scoped and would have been lost on cleanup; this is the run's
> **final deliverable** plus its run metadata. Source transcript: `codex_hcross_route.md` in the
> session scratchpad (ephemeral). Cited by `LAB_NOTEBOOK_INDEX.md`.

## Run metadata

```
workdir: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research
model: gpt-5.6-sol
provider: openai
approval: on-request
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f8208-1e58-7d91-8d94-c4f6ef7764c1
```

## Deliverable

## Verdict

The “no cheap bound” wall is real, but the absolute WALL is not.

There is a fourth route that avoids:

- an \(S^2\) winding cocycle,
- \(T^4\to S^2\times S^2\) degree multiplicativity,
- integral Poincaré duality, and
- a \((2,2)\)-shuffle/Eilenberg–Zilber construction.

The best route is a one-factor Mayer–Vietoris Stokes peel. It proves \(c=\pm1\). Exact \(c=1\) needs one additional sign comparison with the project’s MV-pinned orientation.

### Why the existing facts cannot bound \(c\)

The currently exposed algebraic interfaces admit, for every odd integer \(d\), the ring

\[
H^2=\mathbb Z\alpha\oplus\mathbb Z\beta,\qquad H^4=\mathbb Z\gamma,
\]
\[
\alpha^2=\beta^2=0,\qquad \alpha\beta=\beta\alpha=d\gamma.
\]

The projection and section maps have their expected actions, the top evaluation sends \(\gamma\mapsto1\), and mod \(2\) the pairing is hyperbolic whenever \(d\) is odd. Thus every currently banked constraint is compatible with \(c=1,3,5,\ldots\). Cap detection is mod-2 injectivity and therefore cannot distinguish them; the repository itself records that odd determinant is strictly weaker than a unit determinant.

Sections, diagonals and self-maps add no magnitude information. A product self-map argument needs \(\deg(f\times g)=\deg(f)\deg(g)\), which is precisely the missing product theorem. Ordinary transfer is unavailable because \(S^2\times S^2\) has no nontrivial connected finite covers.

## Fourth route: MV Stokes peel to \(S^2\times S^1\)

First fix the correct primitive generator, since `alphaOf x` and `betaOf x` currently accept arbitrary \(x\):

\[
x_2 :=
  (\mathrm{ucIntEquivOfFree}(S^2,0))^{-1}
  \bigl((\mathrm{topSphereIsoInt}\ 1):H_2(S^2)\to\mathbb Z\bigr).
\]

Then

\[
\langle x_2,h\rangle=\mathrm{topSphereIsoInt}(1)(h),
\qquad
\langle x_2,(\mathrm{topSphereIsoInt}\ 1)^{-1}(1)\rangle=1.
\]

No explicit radial cycle is needed: choose a cycle representative of this homology generator by quotient surjectivity. A radial tetrahedral-boundary cycle helps only if it is also proved to represent this particular generator up to sign; cyclehood alone is insufficient.

The required lemma chain is:

1. **Local primitives on a polar cover.**

   For \(A_0=S^2\setminus\{v\}\) and \(B_0=S^2\setminus\{-v\}\), the restrictions of a cocycle representative \(g\) of \(x_2\) are coboundaries because both punctured spheres are acyclic:

   \[
   g|_{A_0}=\delta u_A,\qquad g|_{B_0}=\delta u_B.
   \]

   On \(A_0\cap B_0\), define the transition cocycle

   \[
   \eta=u_B|_{A_0\cap B_0}-u_A|_{A_0\cap B_0}.
   \]

2. **Generic MV cup–Stokes lemma.**

   Prove a class-level lemma of the following form. If

   \[
   z=\iota_{A\#}z_A+\iota_{B\#}z_B
   \]

   is a cover-partitioned cycle, \(a\) is a degree-\(p\) cocycle, and \(b|_A=\delta u_A\), \(b|_B=\delta u_B\), then

   \[
   \langle a\smile b,[z]\rangle
   =
   (-1)^p
   \left\langle
     a|_{A\cap B}\smile(u_B-u_A),
     \operatorname{MV}\partial[z]
   \right\rangle .
   \]

   For this target \(p=2\), so the sign is \(+1\).

   This is a direct consequence of:

   \[
   \delta(a\smile u)=(-1)^p a\smile\delta u
   \]

   for cocycle \(a\), followed by \(\langle\delta f,z\rangle=\langle f,\partial z\rangle\). The exact primitives are already banked in the signed cup Leibniz rule and Kronecker adjunction. Cover-partition representatives and the chain action of `mvDeltaInt` are also already present in [SingularCoverPartitionMkInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularCoverPartitionMkInt.lean:34>), [SingularMvDeltaPartitionInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularMvDeltaPartitionInt.lean:92>), [SingularCupInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularCupInt.lean:361>), and [SingularHomologyInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularHomologyInt.lean:288>).

3. **Show \(\eta\) is the winding generator up to sign.**

   Apply the same Stokes calculation to the fundamental class of the single \(S^2\):

   \[
   1=\langle x_2,[S^2]\rangle
     =\langle\eta,\operatorname{MV}\partial[S^2]\rangle .
   \]

   The sphere’s `topSphereIsoInt` is constructed by precisely this polar-cover dimension reduction to \(H_1(S^1)\). Hence \([\eta]\) is primitive. The explicit `windS` class is also primitive because `KummerT4GramCross` proves

   \[
   \langle\mathrm{windS},t_1\rangle=1.
   \]

   Since \(H^1(S^1;\mathbb Z)\cong\mathbb Z\), the normalized pullback of \([\eta]\) equals \(\pm[\mathrm{windS}]\).

4. **Peel the product seam.**

   Apply the product polar cover in the second factor. Its seam is

   \[
   S^2\times(S^2\setminus\{v,-v\})
   \simeq S^2\times(\mathbb R^2\setminus0)
   \simeq S^2\times S^1.
   \]

   The transition class for \(\beta\) is the second-factor pullback of \(\eta\). Thus the seam class is

   \[
   \theta=\operatorname{pr}_1^*x_2\smile\operatorname{pr}_2^*\eta.
   \]

   Choose a cycle representative \(z_2\) of the \(S^2\) generator. The already-proved generic torus peel gives

   \[
   \left\langle
     \operatorname{pr}_1^*g\smile\operatorname{pr}_2^*\mathrm{windS},
     \operatorname{torCross}(z_2)
   \right\rangle
   =(-1)^2\langle g,z_2\rangle=1.
   \]

   This is exactly [TorusCrossPeel.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/TorusCrossPeel.lean:438>). Therefore \(\theta\) is a primitive \(H^3\)-class on the seam.

5. **Evaluate on the project’s fundamental class.**

   The current \(H_4\)-coordinate was defined so that

   \[
   \operatorname{coverInterHThreeEquivInt}
   \bigl(\operatorname{mvDeltaInt}[S^2\times S^2]\bigr)=1.
   \]

   Thus its MV boundary is a primitive \(H_3\)-class. Pairing the primitive seam class \(\theta\) with that primitive class gives \(\pm1\). The Stokes lemma then yields

   \[
   c=
   \langle\alpha\smile\beta,[S^2\times S^2]\rangle
   =\pm1.
   \]

   The relevant orientation coordinate is visibly the defining mechanism in [SphereProdHFourInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdHFourInt.lean:217>).

### Estimated Lean cost

| Slice | Estimated new Lean |
|---|---:|
| UCT-defined \(S^2\) generator and local primitive extraction | 120–220 lines |
| Generic class-level MV cup–Stokes lemma | 220–400 |
| Transition class versus `windS` primitivity | 180–300 |
| Seam transport, UCT \(H^3\)-coordinate and `torCross` application | 200–350 |
| Final \(c=\pm1\) closure | 60–120 |
| **Total** | **about 800–1,400 lines** |

The risk is mostly subtype/seam transport, not new mathematics. This is lower-risk than building normalization or deleted-product topology.

## Why \(+1\) is separate

The current fundamental class is pinned by nested MV connecting coordinates, not by a product-orientation theorem. The route above proves both the cup class and the MV boundary class are primitive, hence only \(\pm1\).

To prove literal \(+1\), add a sign pin identifying the transported `torCross` generator with `coverInterHThreeEquivInt.symm 1`, not merely up to a unit. That means checking the order of:

- the \(A/B\) cover,
- `boundaryExtract`’s \(B\)-leg convention,
- the equator/normalize map, and
- `arcA`/`arcB`.

Estimate another 150–300 lines.

Alternatively, the robust `s2s2_hyp` reducer should accept `c = 1 ∨ c = -1`: when \(c=-1\), the matrix \(-H\) is integrally congruent to \(H\) via \(\operatorname{diag}(1,-1)\). Literal `SphereProdGramPin = H` remains orientation-sensitive. The present reducers explicitly require `=1` in [SphereProdGramPinReduce.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdGramPinReduce.lean:66>).

## Minimal EZ fragment, if that route is preferred

It is not only the six-term \((2,2)\) definition.

Because the project’s chains and cochains are unnormalized, the minimal safe fragment is:

1. the six-term shuffle \(\nabla_{2,2}\);
2. its boundary law, requiring effective \((1,2)\) and \((2,1)\) components—or a direct 30-face cancellation;
3. AW–shuffle compatibility in bidegree \((2,2)\);
4. either degree-\(\le2\) cochain normalization or an explicit low-degree homotopy killing the degenerate terms.

The tree explicitly records “degenerate cycles bound” as an unresolved normalization statement in [SingularPrismProjectionNull.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularPrismProjectionNull.lean:88>). Therefore a proof that merely expands six shuffles and claims five terms vanish would be invalid for the current unnormalized cochains.

One correction to the worker’s diagnosis: the generic integral-PD assembly is now substantially present. What remains unavailable for \(S^2\times S^2\) is the space-specific orientation/local-generator tie; the stock module explicitly acknowledges that gap. Proving it reduces to \(H_4\) and \(H_3\) vanishing for the punctured product, via [IntOrientationGlobalSection.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/IntOrientationGlobalSection.lean:171>). That is still a larger route than the MV peel.

No files were changed; this was a source-level second-opinion rather than an implemented proof.


tokens used
525,047
## Verdict

The “no cheap bound” wall is real, but the absolute WALL is not.

There is a fourth route that avoids:

- an \(S^2\) winding cocycle,
- \(T^4\to S^2\times S^2\) degree multiplicativity,
- integral Poincaré duality, and
- a \((2,2)\)-shuffle/Eilenberg–Zilber construction.

The best route is a one-factor Mayer–Vietoris Stokes peel. It proves \(c=\pm1\). Exact \(c=1\) needs one additional sign comparison with the project’s MV-pinned orientation.

### Why the existing facts cannot bound \(c\)

The currently exposed algebraic interfaces admit, for every odd integer \(d\), the ring

\[
H^2=\mathbb Z\alpha\oplus\mathbb Z\beta,\qquad H^4=\mathbb Z\gamma,
\]
\[
\alpha^2=\beta^2=0,\qquad \alpha\beta=\beta\alpha=d\gamma.
\]

The projection and section maps have their expected actions, the top evaluation sends \(\gamma\mapsto1\), and mod \(2\) the pairing is hyperbolic whenever \(d\) is odd. Thus every currently banked constraint is compatible with \(c=1,3,5,\ldots\). Cap detection is mod-2 injectivity and therefore cannot distinguish them; the repository itself records that odd determinant is strictly weaker than a unit determinant.

Sections, diagonals and self-maps add no magnitude information. A product self-map argument needs \(\deg(f\times g)=\deg(f)\deg(g)\), which is precisely the missing product theorem. Ordinary transfer is unavailable because \(S^2\times S^2\) has no nontrivial connected finite covers.

## Fourth route: MV Stokes peel to \(S^2\times S^1\)

First fix the correct primitive generator, since `alphaOf x` and `betaOf x` currently accept arbitrary \(x\):

\[
x_2 :=
  (\mathrm{ucIntEquivOfFree}(S^2,0))^{-1}
  \bigl((\mathrm{topSphereIsoInt}\ 1):H_2(S^2)\to\mathbb Z\bigr).
\]

Then

\[
\langle x_2,h\rangle=\mathrm{topSphereIsoInt}(1)(h),
\qquad
\langle x_2,(\mathrm{topSphereIsoInt}\ 1)^{-1}(1)\rangle=1.
\]

No explicit radial cycle is needed: choose a cycle representative of this homology generator by quotient surjectivity. A radial tetrahedral-boundary cycle helps only if it is also proved to represent this particular generator up to sign; cyclehood alone is insufficient.

The required lemma chain is:

1. **Local primitives on a polar cover.**

   For \(A_0=S^2\setminus\{v\}\) and \(B_0=S^2\setminus\{-v\}\), the restrictions of a cocycle representative \(g\) of \(x_2\) are coboundaries because both punctured spheres are acyclic:

   \[
   g|_{A_0}=\delta u_A,\qquad g|_{B_0}=\delta u_B.
   \]

   On \(A_0\cap B_0\), define the transition cocycle

   \[
   \eta=u_B|_{A_0\cap B_0}-u_A|_{A_0\cap B_0}.
   \]

2. **Generic MV cup–Stokes lemma.**

   Prove a class-level lemma of the following form. If

   \[
   z=\iota_{A\#}z_A+\iota_{B\#}z_B
   \]

   is a cover-partitioned cycle, \(a\) is a degree-\(p\) cocycle, and \(b|_A=\delta u_A\), \(b|_B=\delta u_B\), then

   \[
   \langle a\smile b,[z]\rangle
   =
   (-1)^p
   \left\langle
     a|_{A\cap B}\smile(u_B-u_A),
     \operatorname{MV}\partial[z]
   \right\rangle .
   \]

   For this target \(p=2\), so the sign is \(+1\).

   This is a direct consequence of:

   \[
   \delta(a\smile u)=(-1)^p a\smile\delta u
   \]

   for cocycle \(a\), followed by \(\langle\delta f,z\rangle=\langle f,\partial z\rangle\). The exact primitives are already banked in the signed cup Leibniz rule and Kronecker adjunction. Cover-partition representatives and the chain action of `mvDeltaInt` are also already present in [SingularCoverPartitionMkInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularCoverPartitionMkInt.lean:34>), [SingularMvDeltaPartitionInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularMvDeltaPartitionInt.lean:92>), [SingularCupInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularCupInt.lean:361>), and [SingularHomologyInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularHomologyInt.lean:288>).

3. **Show \(\eta\) is the winding generator up to sign.**

   Apply the same Stokes calculation to the fundamental class of the single \(S^2\):

   \[
   1=\langle x_2,[S^2]\rangle
     =\langle\eta,\operatorname{MV}\partial[S^2]\rangle .
   \]

   The sphere’s `topSphereIsoInt` is constructed by precisely this polar-cover dimension reduction to \(H_1(S^1)\). Hence \([\eta]\) is primitive. The explicit `windS` class is also primitive because `KummerT4GramCross` proves

   \[
   \langle\mathrm{windS},t_1\rangle=1.
   \]

   Since \(H^1(S^1;\mathbb Z)\cong\mathbb Z\), the normalized pullback of \([\eta]\) equals \(\pm[\mathrm{windS}]\).

4. **Peel the product seam.**

   Apply the product polar cover in the second factor. Its seam is

   \[
   S^2\times(S^2\setminus\{v,-v\})
   \simeq S^2\times(\mathbb R^2\setminus0)
   \simeq S^2\times S^1.
   \]

   The transition class for \(\beta\) is the second-factor pullback of \(\eta\). Thus the seam class is

   \[
   \theta=\operatorname{pr}_1^*x_2\smile\operatorname{pr}_2^*\eta.
   \]

   Choose a cycle representative \(z_2\) of the \(S^2\) generator. The already-proved generic torus peel gives

   \[
   \left\langle
     \operatorname{pr}_1^*g\smile\operatorname{pr}_2^*\mathrm{windS},
     \operatorname{torCross}(z_2)
   \right\rangle
   =(-1)^2\langle g,z_2\rangle=1.
   \]

   This is exactly [TorusCrossPeel.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/TorusCrossPeel.lean:438>). Therefore \(\theta\) is a primitive \(H^3\)-class on the seam.

5. **Evaluate on the project’s fundamental class.**

   The current \(H_4\)-coordinate was defined so that

   \[
   \operatorname{coverInterHThreeEquivInt}
   \bigl(\operatorname{mvDeltaInt}[S^2\times S^2]\bigr)=1.
   \]

   Thus its MV boundary is a primitive \(H_3\)-class. Pairing the primitive seam class \(\theta\) with that primitive class gives \(\pm1\). The Stokes lemma then yields

   \[
   c=
   \langle\alpha\smile\beta,[S^2\times S^2]\rangle
   =\pm1.
   \]

   The relevant orientation coordinate is visibly the defining mechanism in [SphereProdHFourInt.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdHFourInt.lean:217>).

### Estimated Lean cost

| Slice | Estimated new Lean |
|---|---:|
| UCT-defined \(S^2\) generator and local primitive extraction | 120–220 lines |
| Generic class-level MV cup–Stokes lemma | 220–400 |
| Transition class versus `windS` primitivity | 180–300 |
| Seam transport, UCT \(H^3\)-coordinate and `torCross` application | 200–350 |
| Final \(c=\pm1\) closure | 60–120 |
| **Total** | **about 800–1,400 lines** |

The risk is mostly subtype/seam transport, not new mathematics. This is lower-risk than building normalization or deleted-product topology.

## Why \(+1\) is separate

The current fundamental class is pinned by nested MV connecting coordinates, not by a product-orientation theorem. The route above proves both the cup class and the MV boundary class are primitive, hence only \(\pm1\).

To prove literal \(+1\), add a sign pin identifying the transported `torCross` generator with `coverInterHThreeEquivInt.symm 1`, not merely up to a unit. That means checking the order of:

- the \(A/B\) cover,
- `boundaryExtract`’s \(B\)-leg convention,
- the equator/normalize map, and
- `arcA`/`arcB`.

Estimate another 150–300 lines.

Alternatively, the robust `s2s2_hyp` reducer should accept `c = 1 ∨ c = -1`: when \(c=-1\), the matrix \(-H\) is integrally congruent to \(H\) via \(\operatorname{diag}(1,-1)\). Literal `SphereProdGramPin = H` remains orientation-sensitive. The present reducers explicitly require `=1` in [SphereProdGramPinReduce.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdGramPinReduce.lean:66>).

## Minimal EZ fragment, if that route is preferred

It is not only the six-term \((2,2)\) definition.

Because the project’s chains and cochains are unnormalized, the minimal safe fragment is:

1. the six-term shuffle \(\nabla_{2,2}\);
2. its boundary law, requiring effective \((1,2)\) and \((2,1)\) components—or a direct 30-face cancellation;
3. AW–shuffle compatibility in bidegree \((2,2)\);
4. either degree-\(\le2\) cochain normalization or an explicit low-degree homotopy killing the degenerate terms.

The tree explicitly records “degenerate cycles bound” as an unresolved normalization statement in [SingularPrismProjectionNull.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularPrismProjectionNull.lean:88>). Therefore a proof that merely expands six shuffles and claims five terms vanish would be invalid for the current unnormalized cochains.

One correction to the worker’s diagnosis: the generic integral-PD assembly is now substantially present. What remains unavailable for \(S^2\times S^2\) is the space-specific orientation/local-generator tie; the stock module explicitly acknowledges that gap. Proving it reduces to \(H_4\) and \(H_3\) vanishing for the punctured product, via [IntOrientationGlobalSection.lean](</Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/IntOrientationGlobalSection.lean:171>). That is still a larger route than the MV peel.

No files were changed; this was a source-level second-opinion rather than an implemented proof.
