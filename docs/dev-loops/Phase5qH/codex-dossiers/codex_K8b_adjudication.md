# codex_K8b_adjudication

> **Codex dossier — the run's FINAL DELIVERABLE only.** Harvested 2026-07-21 by `scripts/codex_dossier.py`.
> The raw transcript (888,698 bytes) is ephemeral and is deliberately NOT in the repo: reading it
> would overflow the orchestrator and defeat the point of using a second provider.
> Source: `codex_K8b_adjudication.md`.

**Question asked:** (record it in CODEX_INDEX.md)

## Run metadata

```
workdir: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research
model: gpt-5.6-sol
provider: openai
approval: on-request
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f8208-5739-79b0-a0d7-0ae3d5a052f0
```

## Deliverable

# K8b route adjudication

Verdict: use route (i), but as a K8b-specialized classification hybrid—not as a naïve extension of the current hyperbolic induction. Reuse the existing split engine, then formalize one targeted stable-classification theorem for the remaining rank-16 definite piece. Confidence in route choice: **0.84**. Confidence in cost estimate: **0.65**.

Read-only snapshot: HEAD `f803ccd1`, Lean `v4.29.1`, Mathlib `5e932f97…`. The branch advanced during review, but the K8b-relevant files did not change. No files were modified and no build was needed for this source-level adjudication.

## 1. Exact in-tree inventory

### `EvenUnimodularHyperbolic.lean`

It proves two enabling facts, not a normal-form congruence:

- [`even_unimodular_sig_zero_indefinite`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/EvenUnimodularHyperbolic.lean:34): nonzero-rank, signature-zero, even-unimodular implies both inertia indices are positive.
- [`even_unimodular_sig_zero_split`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/EvenUnimodularHyperbolic.lean:57): produces an even-unimodular rank-`n−2` residual with signature zero.

Technique:

1. Unimodularity kills the real radical.
2. `sigPos + sigNeg = n` and `sigPos − sigNeg = 0` imply indefiniteness.
3. The discharged Hasse–Minkowski theorem supplies a primitive isotropic vector.
4. Unimodularity produces a partner pairing to one.
5. Evenness corrects that partner to an isotropic partner:
   `w' = w − (wᵀMw/2)v`.
6. The orthogonal complement is free of rank `n−2`.

The arithmetic heart is [`exists_hyperbolic_pair`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/LatticePrimitive.lean:65). This file does **not** expose the unimodular change-of-basis matrix.

### `HyperbolicNormalForm.lean`

This is the actual congruence engine.

- Defines `IntCongr M N := ∃ P, IsUnit P.det ∧ PᵀMP=N` at [`IntCongr`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HyperbolicNormalForm.lean:28), with reflexivity, symmetry, transitivity, signature transport, and even-unimodularity transport.
- [`even_unimodular_sig_zero_split_congr`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HyperbolicNormalForm.lean:98) strengthens the earlier split to
  `M ≅ H ⊕ M'`.
- It constructs `P` from `hypFullBasis`, proves `det P` is a unit using the inverse basis matrix, then identifies the Gram matrix using [`gramB_eq`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SplitHyperbolic.lean:34).
- [`IntCongr.hyp_block`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HyperbolicNormalForm.lean:140) lifts a residual congruence through an `H` block.
- [`exists_hyperbolic_congr`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HyperbolicNormalForm.lean:169) performs strong induction on rank and proves every signature-zero even-unimodular form is congruent to an iterated reindexed sum of `H`.
- [`isHyperbolicForm_congr_iff`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HyperbolicNormalForm.lean:270) packages the full `σ=0` iff characterization.

An adjacent file already proves uniqueness in that slice: [`intCongr_of_evenUnimodular_sig_zero`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductRealizationAtoms.lean:113).

### Important documentation correction

[`SpinRokhlinInterface.lean`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinRokhlinInterface.lean:31) says the general `E₈^a ⊕ (−E₈)^b ⊕ H^c` existence theorem is proved. That comment is overstated/stale.

What is actually proved is:

- unconditional Hasse–Minkowski isotropy;
- hyperbolic splitting;
- theta-modular `8 ∣ rank` in the definite branch;
- consequently [`eight_dvd_latticeSig`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/RokhlinHMRankFour.lean:599).

The definite branch only proves divisibility, not identification of a definite lattice with an `E₈` sum. [`RokhlinClassification.lean`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/RokhlinClassification.lean:38) contains generator and closure bookkeeping, not normal-form existence.

## 2. Route (i): what remains

From rank 22, unimodularity and signature `−16`:

\[
p+n=22,\qquad p-n=-16,
\]

so the real inertia is `(p,n)=(3,19)`.

The current machinery can split three hyperbolic planes:

\[
M \cong H^3 \oplus D,
\]

where `D` is negative-definite, even, unimodular, rank 16.

That does **not** close the proof. Positive/negative-definite even-unimodular rank-16 lattices are not unique: `E₈⊕E₈` and `D₁₆⁺` are distinct. They become isometric only after indefinite stabilization. Therefore any proposed lemma equivalent to

```lean
definite_even_unimodular_rank16_unique
```

would be false.

The missing theorem must retain an indefinite summand, for example:

```lean
theorem stable_neg_rank16
    (D : Matrix (Fin 16) (Fin 16) ℤ)
    (heu : IsEvenUnimodular D)
    (hneg : sigPos (D.map Int.cast).toQuadraticMap' = 0) :
    IntCongr
      (blockDiag Hyp D)
      (blockDiag Hyp (blockDiag (-E8lit) (-E8lit)))
```

This is essentially the hard core of the classical indefinite classification. The classical theorem indeed says that parity, rank and signature determine an indefinite unimodular form; see [Milnor–Husemoller](https://link.springer.com/book/10.1007/978-3-642-88330-9) and the explicit formulation in [Benedetti, Theorem 20.2](https://arxiv.org/pdf/1907.10297).

### Is `8 ∣ σ` needed?

For a reusable general theorem: yes, as the arithmetic existence condition and to define the number of signed `E₈` blocks.

For K8b specifically: no new proof is needed.

- The hypothesis already says `σ=-16`.
- The generic divisibility theorem is already in tree.
- Reusing it costs only arithmetic bookkeeping.

But `8 ∣ σ` is far weaker than the missing stable-classification step. It tells us that the definite remainder has rank divisible by eight; it does not identify that remainder after stabilization.

The characteristic-vector substrate is incomplete. [`AlgebraicRokhlin.lean`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/AlgebraicRokhlin.lean:108) defines `CharacteristicSquareModEight` as a proposition and derives consequences conditionally; it does not prove the generic characteristic-square theorem or the required orbit/cancellation result.

### Mathlib reachability

Pinned Mathlib supplies useful infrastructure:

- free submodules over PIDs;
- Smith-normal-form bases;
- matrices, bases and determinant units;
- quadratic forms and real inertia.

See the available substrate in [`FreeModule/PID.lean`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean:34).

A source-tree search found no Mathlib theorem for:

- odd indefinite unimodular diagonalization;
- indefinite even-unimodular classification;
- characteristic-vector normal forms;
- Kummer/discriminant overlattices.

So the route is Mathlib-reachable in primitives, but the theorem itself must be built project-locally.

### Cost estimate

| Missing component | Estimated net Lean | Risk |
|---|---:|---|
| Generalize `split_congr` from `σ=0` to arbitrary indefinite residual signature | 100–180 | Low |
| Rank/signature-to-inertia and fixed rank-22 split orchestration | 100–180 | Low |
| Odd-line, oddness and characteristic-vector transport infrastructure | 200–350 | Medium |
| Odd indefinite diagonalization or equivalent characteristic-vector orbit reduction | 600–1,100 | High |
| Extract the even orthogonal complement / prove rank-16 stable absorption | 350–650 | High |
| Block congruence, reindexing and normalization to nested `k3Form` | 180–320 | Medium |
| Public K8b theorem and `interMatrix` hookup | 60–120 | Low |

K8b-specialized total: roughly **1,600–2,900 net Lean lines**, in 7–10 reviewable bricks.

A polished all-rank, both-signs normal-form API would likely add another **500–900 lines**. Specializing to rank 22 saves Nat/multiplicity bookkeeping, but it does not turn the hard theorem into finite arithmetic: the input matrix entries remain arbitrary and unbounded.

## 3. Route (ii): arithmetic versus hidden geometry

### The proposed naïve integer `P` is impossible

For the naïve 22 classes,

\[
G_0 = U(2)^3 \oplus \langle-2\rangle^{16}.
\]

Hence

\[
|\det G_0|
= |\det U(2)|^3\,2^{16}
= 4^3\,2^{16}
=2^{22}.
\]

But `k3Form` is unimodular, so `|\det k3Form|=1`. For any integer matrix `P`,

\[
\det(P^T G_0P)=\det(P)^2\det(G_0),
\]

which cannot have absolute value one. Thus there is **no 22×22 integer matrix `P`** taking the naïve Gram matrix to `k3Form`, even if `P` is not required to be unimodular.

Relative to the naïve generators, a genuine basis necessarily has half-integral coordinates and determinant magnitude `2⁻¹¹`. An integer unimodular `P` becomes possible only after first constructing a saturated integral basis of the actual `H₂`.

### Exact saturation ledger

Let `Λ = ⟨-2⟩¹⁶` be generated by the exceptional curves.

1. The Kummer lattice `K`, the saturation of `Λ`, satisfies

   \[
   [K:\Lambda]=2^5,\qquad |\operatorname{disc}K|=2^6.
   \]

   Its five binary enlargement directions are represented by half-sums supported on affine hyperplanes in `F₂⁴`, together with the all-16 class. The affine-code description is explicit in [Bryan–Pietromonaco, Lemma 4.10](https://content.algebraicgeometry.nl/2024-2/2024-2-008.pdf).

2. `U(2)^3 ⊕ K` still has discriminant `2¹²`, so it has index `2⁶` in the full unimodular K3 lattice.

3. Those six further gluing directions are mixed classes of the form

   \[
   \omega_{ij}/2+\frac12\sum_{a\in V}E_a,
   \]

   where `V` is a four-point affine 2-plane. Garbagnati gives six such generators and explains them through strict transforms of coordinate subtori; see [Proposition 3.3 and Remarks 3.8–3.11](https://arxiv.org/pdf/0802.0369).

Therefore the total index of the naïve lattice is

\[
2^5\cdot2^6=2^{11},
\]

exactly agreeing with `\sqrt{2^{22}}`.

### What is bounded arithmetic?

Once the following are genuine integral `H₂` classes:

- a 16-element generating set for the saturated Kummer lattice;
- the six mixed torus/exceptional glue classes;
- a proof that the resulting 22 classes form a basis;

then computing their Gram matrix, finding an explicit `P`, and verifying `PᵀGP=k3Form` is bounded arithmetic. That portion is likely a few hundred structured Lean lines, assisted by an offline matrix calculation whose result Lean verifies kernel-purely.

### What is hidden geometry?

Nearly everything before that arithmetic step:

- proving the exceptional zero sections have Gram `−2I₁₆`;
- proving the affine-hyperplane half-sums are integral homology classes;
- proving the six mixed half-torus/four-exceptional combinations are integral;
- proving saturation and independence;
- identifying this basis with the `IntH2Basis` consumed by [`interMatrix`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/IntersectionMatrixInt.lean:83).

These divisibility statements encode the double-cover/branched-resolution structure. They are derivable in principle from Route B at chain level—puncture invariant tori, descend them through the free quotient, track their `ℝP³` boundary data, and cap them inside the `O(-2)` pieces—but they are not consequences of rank, evenness, PD or Novikov additivity.

Current in-tree position:

- The `T⁴` Gram computation to `3H` is banked at [`interMatrix_t4_intCongr_torusFourForm`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerT4GramCross.lean:983).
- Each resolution piece has `H₂≅ℤ` and a pinned zero-section generator at [`resEH2EquivInt`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerBaseSphereH2Int.lean:264).
- The `−2` self-intersection is explicitly deferred to K8 at [`KummerResolutionPiece.lean`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerResolutionPiece.lean:666).
- There is no current declaration implementing the Kummer saturation code or the six mixed glue classes.

So route (ii) is approximately **15% bounded arithmetic and 85% new geometry/homology integration**. Its original description as “explicit 22×22 integer base change” hides the principal work and, when applied to the naïve basis, is arithmetically impossible.

## 4. Verdict

Choose route (i), with this scoped hybrid:

> Prove only the public rank-22/signature-`−16` theorem needed by K8b, but implement the hard interior brick as a reusable one-hyperbolic stabilization theorem.

Target interface:

```lean
theorem even_unimodular_rank22_sig_neg16_congr_k3
    (M : Matrix (Fin 22) (Fin 22) ℤ)
    (heu : IsEvenUnimodular M)
    (hsig : latticeSig M = -16) :
    IntCongr M k3Form
```

This consumes exactly what K8a promises and works for the arbitrary disclosed cohomology basis in [`K3RealizingElement.hk3`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:277).

### Winning brick decomposition

1. **K8b-C1 — General indefinite split**

   Refactor the proof at `HyperbolicNormalForm:98` into a theorem taking explicit positive/negative inertia and returning `M ≅ H⊕M'`, with residual even-unimodularity and unchanged signature.

2. **K8b-C2 — K3 inertia**

   From rank 22, radical zero and signature `−16`, prove inertia `(3,19)`.

3. **K8b-C3 — Two routine `H` splits**

   Reduce to a rank-18 even-unimodular form of inertia `(1,17)`. Retain the final positive direction inside the hard classification brick.

4. **K8b-C4 — Odd stabilization and diagonalization**

   Adjoin a rank-one odd form, prove odd indefinite unimodular diagonalization, and transport the distinguished characteristic vector.

5. **K8b-C5 — Characteristic-vector normalization**

   Prove the required orbit/reduction theorem for the primitive characteristic vector whose orthogonal complement is even. This is the principal mathematical brick.

6. **K8b-C6 — Stable rank-16 absorption**

   Extract:

   \[
   H\oplus D_{16}\cong H\oplus(-E_8)^2.
   \]

   The statement must include `H` or an indefinite hypothesis. Add a guard against accidentally asserting definite rank-16 uniqueness.

7. **K8b-C7 — Block assembly**

   Lift through the two earlier `H` blocks, normalize reindexings and block associations, and identify the result with the exact nested definition of [`k3Form`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinSigmaGenerator.lean:122).

8. **K8b-C8 — Geometry-independent hookup**

   Apply the theorem to the reindexed `interMatrix`, using K8a’s rank, even-unimodularity and signature, then fill `K3RealizingElement.hk3`.

Route (ii) should remain a later geometric audit or an alternative only if K7/K8a independently decide to construct the saturated Kummer basis and its eleven binary gluing directions. It should not be placed on K8b’s critical path.
