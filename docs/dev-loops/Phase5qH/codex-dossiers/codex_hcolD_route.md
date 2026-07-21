# codex_hcolD_route

> **Promoted from session scratchpad 2026-07-21.** The raw ~1-2 MB codex
> transcript was session-scoped and would have been lost on cleanup; this is the run's
> **final deliverable** plus its run metadata. Source transcript: `codex_hcolD_route.md` in the
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
session id: 019f82eb-4f08-7d81-9892-4fe38acb7a8d
```

## Deliverable

## 1. Executive verdict — winning route in five lines

- Kirby–Taylor’s terminal move is a characteristic-submanifold bordism to a different 4-manifold, not a cap inside \(M\times I\).
- The carrier splits sharply: \(v_2=0\) makes a same-carrier cap homologically plausible; \(v_2\neq0\) forces a topology-changing endpoint.
- Construct the source-oriented trace \(p'_{\emptyset}\to p\), use `emptySourceRealizationTied` plus a genuine \(Q\hookrightarrow W\) weld, then apply `symmBorTethered`.
- Reuse the generic `D⁵` attachment/capstone/weld stack; do not identify `S²×D³` with the local \(D^3\times D^2\) index-3 handle, and do not assume the normal Euler number vanishes.
- For the final assembly alone, bypass exact `hcolD`: `SectorIsGeometric` or universal class-level collapse is sufficient; `KTKernelCard` is a substantially deeper trade.

## 2. Per-question analysis

### (a) Source fidelity

#### What §5 actually does

The premise “terminal rank-zero step of an induction” is a project-level reorganization, not Kirby–Taylor’s presentation. KT instead considers

\[
F^2=V^3\pitchfork V^3\subset M^4,
\]

where \(V\) is dual to \(w_1(M)\), so \(F\) represents \(w_1^2\) and inherits the relevant Pin\(^{-}\) structure. In the Pin\(^{+}\) case, the map is the characteristic-surface map to \(\Omega_2^{\mathrm{Pin^-}}\cong\mathbb Z/8\); its kernel consists of manifolds whose \(F\) Pin\(^{-}\)-bounds. The local extraction correctly summarizes the conclusion as “any kernel element is Pin\(^{+}\)-bordant to an orientable (Spin) manifold” ([KT extraction:35–39](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:35)).

The scanned primary gives the actual mechanism. KT constructs “a Pin⁺ bordism to a new 4-manifold \(M_1\)” where “the dual to \(w_1\) has trivial normal bundle.” The resulting \(V_1\) gets a Pin\(^{+}\) structure; orienting it gives a Spin 3-manifold. Since \(\Omega_3^{\mathrm{Spin}}=0\), \(V_1\) bounds, and \(M_1\) is then Pin\(^{+}\)-bordant to an orientable endpoint. See [local KT PDF, PDF page 21/book pp. 216–217](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KirbyTaylor_PinStructures_LMS151.pdf) and the extracted \(\Omega_3^{\mathrm{Spin}}=0\) input ([KT extraction:16–21](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:16)).

Therefore:

- It is not a membrane cap \(Q\subset M\times I\) on the unchanged carrier.
- It is a characteristic-pair bordism whose new end has become orientable/spin.
- The bounding 3-manifold for \(F\) lives as the characteristic membrane inside that 5-dimensional bordism.
- The source may use more than one conceptual bordism stage; it does not identify the move with one standard index-3 handle on the original sphere.

The translation to the project’s rank-zero language is:

1. `p.2.n = 0` makes the enhancement space zero-dimensional ([KernelSector:73–82](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:73)).
2. Hence the induced quadratic enhancement has Brown class zero.
3. Since Brown/ABK classifies \(\Omega_2^{\mathrm{Pin^-}}\), \(F\) Pin\(^{-}\)-bounds.
4. KT’s characteristic-extension construction turns that nullbordism into a Pin\(^{+}\) bordism to an orientable end.

Taylor’s circle-surgery condition \(q(C)=0\) is the positive-rank surgery mechanism, not this terminal step ([GM normalization report:33–35](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/GM_structure_ABK_invariant_normalizations_20260703.md:33)). The repository has recently encoded that distinction explicitly: it rejects a same-\(M\) compression disk as a source attribution and allows a different endpoint ([KTCompletenessTether:43–52](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessTether.lean:43)).

#### PDF verification note

The local PDF is image-only. Current `pdfinfo` reports 34 two-up PDF pages, whereas the extraction says “136 scan pages” ([KT extraction:3–7](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:3)). I OCR-checked PDF page 21, containing book pp. 216–217. The mechanism is clear, but OCR corrupts some Pin superscripts; exact typography beyond the quoted short phrases should be checked visually if used in a publication.

#### What `emptySourceRealizationTied` actually supplies

At declaration level, `emptySourceRealizationTied` constructs only a `GeoRealizationTied`: compact Hausdorff \(Q\), a closed boundary embedding, empty/source and \(\Sigma\)/target boundary identifications, and an interior \(H_1\) basis ([EmptySourceRealization:112–143](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:112)). It does **not** itself construct a bordism or a tether into a bordism carrier.

Beyond that realization, a full `CharPairBorRealizedTethered` requires:

- `WAdmPinned b` and `T2Space b.W`;
- Taylor-leg vanishing and joint Lagrangian conditions for the computed kernel;
- a specific map `ιW : Q → b.W` which is a closed embedding;
- both endpoint glue equations against `b.e`;
- `chartQ : ChartedSpace MembraneModel Q`.

Those inputs are explicit in `mkCharPairBorRealizedTethered` ([BorTethered:869–902](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:869)); the tether-specific fields themselves are at [BorTethered:117–134](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:117).

The existing `TauMembraneWeldDatum` is already the correct terminal package: it adds \(Q\), the boundary embedding, kernel conditions, a 3-dimensional handle presentation, a weld into the actual \(W\), target glue, and `chartQ` ([EmptySourceRealization:392–451](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:392)). Its builder produces the membrane leaf row, not the trace or its W-admissibility ([EmptySourceRealization:453–471](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:453)).

The orientation is favorable: construct the KT trace from an empty-surface source \(p'_{\emptyset}\) to \(p\), then use `symmBorTethered`, which preserves \(Q\hookrightarrow W\) and swaps the glue equations ([BorTethered:229–242](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:229)).

### (b) Obstruction analysis

Let

\[
[\Sigma]_M=\operatorname{emb}_*[\Sigma]\in H_2(M;\mathbb F_2).
\]

For every nonempty T2 carrier, `hchar` says

\[
\langle a,[\Sigma]_M\rangle=\mu(a\smile a)
\quad\text{for all }a\in H^2(M;\mathbb F_2)
\]

([CharPairData:1455–1464](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairData.lean:1455)). The Kronecker pairing is nondegenerate in its homology argument ([PoincareDualityConstruct:69–76](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PoincareDualityConstruct.lean:69)). Therefore:

\[
[\Sigma]_M=0
\iff
\mu(a^2)=0\;\forall a.
\]

The square functional is represented by the project’s `wuClass2`; its pairing map is bijective and the defining relation identifies it with \(a\mapsto\mu(a^2)\) ([PoincareDualityWu:67–88](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PoincareDualityWu.lean:67)). Thus, on these carriers,

\[
[\Sigma]_M=0\iff v_2(M)=0.
\]

This equivalence is assembled from existing declarations, but I did not find it exposed as one named Lean theorem.

#### Sector (i): \(v_2=0\)

Here a cap \(Q\subset M\times I\) with \(\partial Q=\Sigma\) is homologically unobstructed. That is only a necessary condition:

- one still needs an embedded compact 3-manifold rather than a mod-2 chain;
- the correct Pin/characteristic extension data;
- `chartQ`;
- a closed embedding \(Q\hookrightarrow W\);
- the kernel conditions;
- the W-admissibility/relative-duality tower.

So “same-\(M\) cap plausible” is the correct verdict, not “same-\(M\) cap exists.” No in-tree theorem supplies that promotion.

#### Sector (ii): \(v_2\neq0\)

A cap in \(M\times I\) is impossible because \(M\times I\simeq M\), while the boundary of such a \(Q\) would make \([\Sigma]_M=0\).

More strongly, the same underlying carrier cannot support the required empty-surface target: an empty surface has pushed-forward class zero, so its `hchar` would force \(\mu(a^2)=0\) for every \(a\). The project proves this direction explicitly for empty-\(\Sigma\) structures ([SpinSigmaAtomReduce:84–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:84)). Hence a genuinely different carrier topology is forced.

The source-faithful replacement is KT’s characteristic extension:

\[
(M,F)\rightsquigarrow (M_1,F_1),
\]

where the dual hypersurface \(V_1\) has trivial normal bundle, followed by the Spin nullbordism of \(V_1\). The final end is orientable and therefore admits the literal empty characteristic surface.

#### Is this a 5-dimensional index-3 handle along each sphere?

Not in the generality required.

Classically, rank zero plus closedness implies that \(\Sigma\) is a finite union of \(S^2\)’s. The repository records this only as explanatory mathematics; it does not contain the closed-surface classification needed to construct those components ([SectorGate:80–93](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGate.lean:80)). Even after choosing a component:

- A standard 5-dimensional index-3 handle is \(D^3\times D^2\).
- It attaches along \(S^2\times D^2\), so it requires a framing of the normal 2-plane bundle.
- If the sphere has an oriented normal bundle of Euler number \(e\), this attaching region is a product only when \(e=0\).
- For a nonorientable ambient Pin\(^{+}\) manifold, the normal bundle need not be orientable; the appropriate obstruction is then a twisted Euler class.

Neither `hchar` nor rank zero forces \(e=0\). `hchar` sees the mod-2 characteristic class, not an integral framing. In the oriented Guillou–Marin setting,

\[
\sigma(M)\equiv F\!\cdot\!F+2\beta(F)\pmod {16},
\]

up to the documented Brown-sign convention ([GM report:48–51](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/GM_structure_ABK_invariant_normalizations_20260703.md:48)). Rank zero gives \(\beta=0\), so only

\[
F\!\cdot\!F\equiv\sigma(M)\pmod {16},
\]

not \(F\!\cdot\!F=0\). It constrains total self-intersection, not each component’s Euler number. Applying this oriented formula directly to the nonorientable Pin\(^{+}\) carrier was not verified.

Therefore the one-sphere/one-3-handle route works only after supplying an honest framing hypothesis. It cannot be the universal hcolD construction. KT’s global characteristic-bordism route avoids asserting that the original sphere is framed.

#### Reusable substrate verdict

- `ktHandleAttachment` accepts a general compact handle, closed attaching region, and embedding, so its quotient/T2 floor is reusable ([SurgeryChartsConcrete:102–117](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryChartsConcrete.lean:102)).
- The `D⁵` specialization supplies the handle atlas and leaves only attaching, collar, and target-boundary data ([SurgeryHandleD5:45–80](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryHandleD5.lean:45)).
- `SurgeredEndDatum` is exactly the appropriate target-end/boundary-decomposition packaging ([SurgeryTraceCapstone:97–152](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryTraceCapstone.lean:97)).
- `HandleAttachment.Weld` is the literal membrane-to-trace substrate; it constructs a closed embedding on carriers ([SingularSurgeryWeld:34–60](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryWeld.lean:34), [119–124](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryWeld.lean:119)).
- `SphereDisk = S²×D³` is a whole 5-manifold with boundary \(S²\times S²\), not the local \(D^3\times D^2\) handle ([SphereProductBounding:139–160](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductBounding.lean:139)). Its atlas and W-admissibility proofs are patterns, not direct terminal-collapse witnesses.
- `sphereProdCoboundaryWAdm_sphereDisk` applies to the stock \(S²\times S²\to\varnothing\) bordism only ([SphereProdP23Close:165–190](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:165)).
- `KummerWeld` is a strong structural precedent for an exact seam relation and closed embeddings, but its smooth seam-chart descent is itself described as follow-on work ([KummerWeld:462–493](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerWeld.lean:462)). Reuse its discipline, not its carrier.

### (c) Demand narrowing

`hcolD` is quantified over **every** structured representative satisfying `IsSpinSectorStr`, and that predicate is literally only `p.2.n = 0` ([CollapseDischarge:144–157](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:144), [KernelSector:80–82](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:80)). There is no restriction to outputs of the positive-rank surgery chain, sums, or doubled representatives.

The call path is:

1. universal `hcolD` produces `RankZeroCollapsesToEmptySurf` ([CollapseDischarge:125–135](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:125));
2. that produces `SectorIsGeometric` ([SectorGeometricReduce:90–99](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGeometricReduce.lean:90));
3. dC consumes only `SectorIsGeometric` ([SpinPresentationRow:147–155](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinPresentationRow.lean:147));
4. the final assembly invokes dC at that point ([BinderDischarge:78–95](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTBinderDischarge.lean:78)).

Consequences:

- Exact `RankZeroCollapseDatum` is stronger than dC needs.
- The exact weakest existing interface is `SectorIsGeometric`.
- A convenient intermediate is the universal class-level statement:
  \[
  \forall p,\ n(p)=0\Rightarrow
  \exists p'_{\emptyset},\ [p']=[p].
  \]
  The repository already proves this is the class-level shadow of `SectorIsGeometric` ([SectorGeometricReduce:101–113](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGeometricReduce.lean:101)).
- Collapse after adding an explicitly null-bordant summand is enough if it yields that class equality.
- Restricting collapse to \([\Sigma]_M=0\) is insufficient unless a separate theorem first replaces every broad rank-zero class by a representative in that sub-sector.
- A sequence of T2 bordisms is enough for class equality even without a bordism-composition implementation: `T2DataBordismGrp` uses `Quot`, whose equivalence closure supplies transitivity ([T2TangentialBordism:63–79](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/T2TangentialBordism.lean:63), [BordismGroup:263–268](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/BordismGroup.lean:263)). This is a major reason the class-level route is Lean-cheaper than exact hcolD.

#### G9-4 / `KTKernelCard`

`KTKernelCard` classifies **every Brown-kernel class** as either \(0\) or the distinguished \(k_0\) ([PinPlusKTExtension:100–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTExtension.lean:100)). The in-tree derivation requires both:

- `KernelReducesToSpin`: all Brown-zero classes admit rank-zero representatives;
- `SpinImageIsTwo`: all such representatives lie in \(\{0,k_0\}\).

That factorization is explicit ([KernelSector:266–273](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:266)). The first is already labelled the deep KT §5 completeness direction ([KernelSector:210–225](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:210)).

Verdict: G9-4 is a valid logical alternative but the wrong trade for hcolD. It replaces a terminal class-geometric overhang with a global classification of the complete Brown kernel.

## 3. Brick decomposition

The exact-hcolD route should construct the reverse trace \(p'_{\emptyset}\to p\), then reverse it. Statement freezes should be theorem parameters or per-object structures—not new Lean `axiom`s.

| Brick | Content and output | Banked substrate | Honest freeze | Estimated new LOC |
|---|---|---|---|---:|
| B0 | Prove `emb_* surfClass = 0 ↔ wuClass2 = 0`; expose the \(v_2\) split | `hchar`, `homology_eq_zero_of_kroneckerH`, `pairing_bijective` | None | 80–140 |
| B1 | `RankZeroSurfaceBoundingDatum p`: compact T2/charted \(Q^3\), exact \(\partial Q\cong\Sigma\), closed boundary embedding, induced Pin\(^{-}\) compatibility | `GeoRealizationTied`, `emptySourceRealizationTied` | Low-dimensional Pin\(^{-}\) nullbordism / closed-surface classification | 120–220 interface; 800–1,500 to prove |
| B2 | `TerminalCharacteristicExtensionDatum`: produce an empty-surface endpoint \(p'_{\emptyset}\) and a combined Pin\(^{+}\) characteristic bordism \(W:p'_{\emptyset}\to p\), with \(Q\hookrightarrow W\) and exact end glue | `ktHandleAttachmentD5`, `SurgeredEndDatum`, `HandleAttachment.Weld`; Kummer seam discipline | **KT’s characteristic-extension theorem**, with framing/normal-bundle and endpoint construction | 180–300 interface; 2,000–5,000 to prove |
| B3 | Build `TraceWAdmLeaves b`: relative fundamental class, PL duality, finite-dimensionality, Betti equalities, and `wuW2=0` | `TraceRelFundLeaves`, `TraceWAdmLeaves.toWAdmPinned` ([TraceWAdm:109–153](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceWAdmPinned.lean:109)) | Per-trace PL/Wu row until a general manifold theorem exists | 300–700; 1,000–3,000 if foundations are proved |
| B4 | Instantiate the empty-source membrane. Rank zero makes `hq` and `hlagK` essentially `Fin 0`/zero-map proofs; package `TauMembraneWeldDatum` | `taylorLegVanishes_emptySource`, `jointLagrangian_emptySource`, `ofTauMembraneWeldDatum` | No further global theorem | 120–220 |
| B5 | Combine W-admissibility and membrane leaves to obtain a genuine tethered `Bor` | `traceTethered_of_leaves` ([TraceMembranePresented:141–151](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceMembranePresented.lean:141)) | None | 30–60 |
| B6 | Apply `symmBorTethered`; assemble `RankZeroCollapseDatum p` and its universal supply | `symmBorTethered`, `rankZeroCollapsesToEmptySurf_of_datumSupply` | None | 40–80 |
| B7, assembly-only branch | Stop before exact one-step gluing: prove universal class equality / `SectorIsGeometric` from the KT bordism sequence | Quotient equivalence closure and existing dC consumer | Only the source-level sequence, not a combined bordism | 20–60 |

The single hardest brick is **B2**, not the Lean packaging. It must turn a Pin\(^{-}\) nullbordism of the characteristic surface into a Pin\(^{+}\) 5-bordism with:

- a genuinely different empty-surface endpoint;
- the correct normal/framing data without assuming \(e=0\);
- a closed embedded characteristic membrane \(Q\hookrightarrow W\);
- exact compatibility with both end embeddings;
- enough handle/collar data to support the project’s chart and boundary encoding.

The sharpest acceptable freeze is therefore a per-\(p\), Type-valued `TerminalCharacteristicExtensionDatum`; it should not mention bordism-group equality, `KTKernelCard`, \(k_0\), or the final \(\mathbb Z/16\) result. Its consumer then derives `RankZeroCollapseDatum`, preserving kernel purity.

## 4. Ranked risks and unknowns

1. **Critical — source theorem versus current formal substrate.** KT supplies the geometric theorem, but no in-tree declaration constructs its combined \(W\), endpoint, and tether. Freezing only “\(\Sigma\) bounds” is too weak.

2. **Critical — normal Euler/framing.** Rank zero and `hchar` do not imply \(e=0\). A universal one-sphere index-3 handle proposal is therefore unsound without an additional framing theorem.

3. **High — exact hcolD asks for one bordism.** KT’s description is naturally staged, while the project deliberately uses quotient equivalence closure instead of implementing bordism composition. Exact hcolD needs a combined \(W\) or a new collar-gluing theorem; `SectorIsGeometric` does not.

4. **High — W-admissibility is independent work.** A topological handle attachment and T2 carrier do not produce `WAdmPinned`; the full PL/Wu row remains load-bearing ([TraceWAdm:104–144](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceWAdmPinned.lean:104)).

5. **High — rank-zero surface classification is absent.** “Finite union of spheres” is mathematically correct under the stated hypotheses, but no in-tree theorem converts the arbitrary carried surface into explicit sphere components and 3-balls.

6. **Medium — oriented GM normalization does not settle the Pin\(^{+}\), nonorientable Euler problem.** Only the oriented congruence and convention comparison were verified; no local source pins componentwise \(e\) in the required nonorientable setting.

7. **Medium — `emptySourceRealizationTied` is sometimes described too strongly in comments.** The declaration constructs a realization, not the bordism, W-admissibility, or tether. The capstone wrapper makes the missing inputs explicit ([EmptySourceRealization:302–344](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:302)).

8. **Low — source artifact pagination/OCR.** The PDF is image-only and its current page count disagrees with the extraction metadata. The terminal mechanism was OCR-verified, but symbol-perfect quotation requires visual checking.

9. **Provenance — checkout moved during review.** Opening HEAD was `d9373ba095adc0c920e8c09824e2382f9d2e2be4`; final HEAD was `ba271a11050bd50cc868cbd4643ae44c2ab5ea9b`. The intervening commit added the capstone seam-corrector lane and inventory artifacts; none of the cited hcolD, carrier, tether, demand, or source files changed. Final status and diff were clean. No build was run, because this was a read-only semantic/source audit; no files or generated artifacts were created.


tokens used
467,937
## 1. Executive verdict — winning route in five lines

- Kirby–Taylor’s terminal move is a characteristic-submanifold bordism to a different 4-manifold, not a cap inside \(M\times I\).
- The carrier splits sharply: \(v_2=0\) makes a same-carrier cap homologically plausible; \(v_2\neq0\) forces a topology-changing endpoint.
- Construct the source-oriented trace \(p'_{\emptyset}\to p\), use `emptySourceRealizationTied` plus a genuine \(Q\hookrightarrow W\) weld, then apply `symmBorTethered`.
- Reuse the generic `D⁵` attachment/capstone/weld stack; do not identify `S²×D³` with the local \(D^3\times D^2\) index-3 handle, and do not assume the normal Euler number vanishes.
- For the final assembly alone, bypass exact `hcolD`: `SectorIsGeometric` or universal class-level collapse is sufficient; `KTKernelCard` is a substantially deeper trade.

## 2. Per-question analysis

### (a) Source fidelity

#### What §5 actually does

The premise “terminal rank-zero step of an induction” is a project-level reorganization, not Kirby–Taylor’s presentation. KT instead considers

\[
F^2=V^3\pitchfork V^3\subset M^4,
\]

where \(V\) is dual to \(w_1(M)\), so \(F\) represents \(w_1^2\) and inherits the relevant Pin\(^{-}\) structure. In the Pin\(^{+}\) case, the map is the characteristic-surface map to \(\Omega_2^{\mathrm{Pin^-}}\cong\mathbb Z/8\); its kernel consists of manifolds whose \(F\) Pin\(^{-}\)-bounds. The local extraction correctly summarizes the conclusion as “any kernel element is Pin\(^{+}\)-bordant to an orientable (Spin) manifold” ([KT extraction:35–39](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:35)).

The scanned primary gives the actual mechanism. KT constructs “a Pin⁺ bordism to a new 4-manifold \(M_1\)” where “the dual to \(w_1\) has trivial normal bundle.” The resulting \(V_1\) gets a Pin\(^{+}\) structure; orienting it gives a Spin 3-manifold. Since \(\Omega_3^{\mathrm{Spin}}=0\), \(V_1\) bounds, and \(M_1\) is then Pin\(^{+}\)-bordant to an orientable endpoint. See [local KT PDF, PDF page 21/book pp. 216–217](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KirbyTaylor_PinStructures_LMS151.pdf) and the extracted \(\Omega_3^{\mathrm{Spin}}=0\) input ([KT extraction:16–21](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:16)).

Therefore:

- It is not a membrane cap \(Q\subset M\times I\) on the unchanged carrier.
- It is a characteristic-pair bordism whose new end has become orientable/spin.
- The bounding 3-manifold for \(F\) lives as the characteristic membrane inside that 5-dimensional bordism.
- The source may use more than one conceptual bordism stage; it does not identify the move with one standard index-3 handle on the original sphere.

The translation to the project’s rank-zero language is:

1. `p.2.n = 0` makes the enhancement space zero-dimensional ([KernelSector:73–82](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:73)).
2. Hence the induced quadratic enhancement has Brown class zero.
3. Since Brown/ABK classifies \(\Omega_2^{\mathrm{Pin^-}}\), \(F\) Pin\(^{-}\)-bounds.
4. KT’s characteristic-extension construction turns that nullbordism into a Pin\(^{+}\) bordism to an orientable end.

Taylor’s circle-surgery condition \(q(C)=0\) is the positive-rank surgery mechanism, not this terminal step ([GM normalization report:33–35](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/GM_structure_ABK_invariant_normalizations_20260703.md:33)). The repository has recently encoded that distinction explicitly: it rejects a same-\(M\) compression disk as a source attribution and allows a different endpoint ([KTCompletenessTether:43–52](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessTether.lean:43)).

#### PDF verification note

The local PDF is image-only. Current `pdfinfo` reports 34 two-up PDF pages, whereas the extraction says “136 scan pages” ([KT extraction:3–7](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:3)). I OCR-checked PDF page 21, containing book pp. 216–217. The mechanism is clear, but OCR corrupts some Pin superscripts; exact typography beyond the quoted short phrases should be checked visually if used in a publication.

#### What `emptySourceRealizationTied` actually supplies

At declaration level, `emptySourceRealizationTied` constructs only a `GeoRealizationTied`: compact Hausdorff \(Q\), a closed boundary embedding, empty/source and \(\Sigma\)/target boundary identifications, and an interior \(H_1\) basis ([EmptySourceRealization:112–143](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:112)). It does **not** itself construct a bordism or a tether into a bordism carrier.

Beyond that realization, a full `CharPairBorRealizedTethered` requires:

- `WAdmPinned b` and `T2Space b.W`;
- Taylor-leg vanishing and joint Lagrangian conditions for the computed kernel;
- a specific map `ιW : Q → b.W` which is a closed embedding;
- both endpoint glue equations against `b.e`;
- `chartQ : ChartedSpace MembraneModel Q`.

Those inputs are explicit in `mkCharPairBorRealizedTethered` ([BorTethered:869–902](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:869)); the tether-specific fields themselves are at [BorTethered:117–134](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:117).

The existing `TauMembraneWeldDatum` is already the correct terminal package: it adds \(Q\), the boundary embedding, kernel conditions, a 3-dimensional handle presentation, a weld into the actual \(W\), target glue, and `chartQ` ([EmptySourceRealization:392–451](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:392)). Its builder produces the membrane leaf row, not the trace or its W-admissibility ([EmptySourceRealization:453–471](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:453)).

The orientation is favorable: construct the KT trace from an empty-surface source \(p'_{\emptyset}\) to \(p\), then use `symmBorTethered`, which preserves \(Q\hookrightarrow W\) and swaps the glue equations ([BorTethered:229–242](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:229)).

### (b) Obstruction analysis

Let

\[
[\Sigma]_M=\operatorname{emb}_*[\Sigma]\in H_2(M;\mathbb F_2).
\]

For every nonempty T2 carrier, `hchar` says

\[
\langle a,[\Sigma]_M\rangle=\mu(a\smile a)
\quad\text{for all }a\in H^2(M;\mathbb F_2)
\]

([CharPairData:1455–1464](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairData.lean:1455)). The Kronecker pairing is nondegenerate in its homology argument ([PoincareDualityConstruct:69–76](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PoincareDualityConstruct.lean:69)). Therefore:

\[
[\Sigma]_M=0
\iff
\mu(a^2)=0\;\forall a.
\]

The square functional is represented by the project’s `wuClass2`; its pairing map is bijective and the defining relation identifies it with \(a\mapsto\mu(a^2)\) ([PoincareDualityWu:67–88](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PoincareDualityWu.lean:67)). Thus, on these carriers,

\[
[\Sigma]_M=0\iff v_2(M)=0.
\]

This equivalence is assembled from existing declarations, but I did not find it exposed as one named Lean theorem.

#### Sector (i): \(v_2=0\)

Here a cap \(Q\subset M\times I\) with \(\partial Q=\Sigma\) is homologically unobstructed. That is only a necessary condition:

- one still needs an embedded compact 3-manifold rather than a mod-2 chain;
- the correct Pin/characteristic extension data;
- `chartQ`;
- a closed embedding \(Q\hookrightarrow W\);
- the kernel conditions;
- the W-admissibility/relative-duality tower.

So “same-\(M\) cap plausible” is the correct verdict, not “same-\(M\) cap exists.” No in-tree theorem supplies that promotion.

#### Sector (ii): \(v_2\neq0\)

A cap in \(M\times I\) is impossible because \(M\times I\simeq M\), while the boundary of such a \(Q\) would make \([\Sigma]_M=0\).

More strongly, the same underlying carrier cannot support the required empty-surface target: an empty surface has pushed-forward class zero, so its `hchar` would force \(\mu(a^2)=0\) for every \(a\). The project proves this direction explicitly for empty-\(\Sigma\) structures ([SpinSigmaAtomReduce:84–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:84)). Hence a genuinely different carrier topology is forced.

The source-faithful replacement is KT’s characteristic extension:

\[
(M,F)\rightsquigarrow (M_1,F_1),
\]

where the dual hypersurface \(V_1\) has trivial normal bundle, followed by the Spin nullbordism of \(V_1\). The final end is orientable and therefore admits the literal empty characteristic surface.

#### Is this a 5-dimensional index-3 handle along each sphere?

Not in the generality required.

Classically, rank zero plus closedness implies that \(\Sigma\) is a finite union of \(S^2\)’s. The repository records this only as explanatory mathematics; it does not contain the closed-surface classification needed to construct those components ([SectorGate:80–93](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGate.lean:80)). Even after choosing a component:

- A standard 5-dimensional index-3 handle is \(D^3\times D^2\).
- It attaches along \(S^2\times D^2\), so it requires a framing of the normal 2-plane bundle.
- If the sphere has an oriented normal bundle of Euler number \(e\), this attaching region is a product only when \(e=0\).
- For a nonorientable ambient Pin\(^{+}\) manifold, the normal bundle need not be orientable; the appropriate obstruction is then a twisted Euler class.

Neither `hchar` nor rank zero forces \(e=0\). `hchar` sees the mod-2 characteristic class, not an integral framing. In the oriented Guillou–Marin setting,

\[
\sigma(M)\equiv F\!\cdot\!F+2\beta(F)\pmod {16},
\]

up to the documented Brown-sign convention ([GM report:48–51](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5qH/GM_structure_ABK_invariant_normalizations_20260703.md:48)). Rank zero gives \(\beta=0\), so only

\[
F\!\cdot\!F\equiv\sigma(M)\pmod {16},
\]

not \(F\!\cdot\!F=0\). It constrains total self-intersection, not each component’s Euler number. Applying this oriented formula directly to the nonorientable Pin\(^{+}\) carrier was not verified.

Therefore the one-sphere/one-3-handle route works only after supplying an honest framing hypothesis. It cannot be the universal hcolD construction. KT’s global characteristic-bordism route avoids asserting that the original sphere is framed.

#### Reusable substrate verdict

- `ktHandleAttachment` accepts a general compact handle, closed attaching region, and embedding, so its quotient/T2 floor is reusable ([SurgeryChartsConcrete:102–117](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryChartsConcrete.lean:102)).
- The `D⁵` specialization supplies the handle atlas and leaves only attaching, collar, and target-boundary data ([SurgeryHandleD5:45–80](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryHandleD5.lean:45)).
- `SurgeredEndDatum` is exactly the appropriate target-end/boundary-decomposition packaging ([SurgeryTraceCapstone:97–152](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryTraceCapstone.lean:97)).
- `HandleAttachment.Weld` is the literal membrane-to-trace substrate; it constructs a closed embedding on carriers ([SingularSurgeryWeld:34–60](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryWeld.lean:34), [119–124](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgeryWeld.lean:119)).
- `SphereDisk = S²×D³` is a whole 5-manifold with boundary \(S²\times S²\), not the local \(D^3\times D^2\) handle ([SphereProductBounding:139–160](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductBounding.lean:139)). Its atlas and W-admissibility proofs are patterns, not direct terminal-collapse witnesses.
- `sphereProdCoboundaryWAdm_sphereDisk` applies to the stock \(S²\times S²\to\varnothing\) bordism only ([SphereProdP23Close:165–190](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:165)).
- `KummerWeld` is a strong structural precedent for an exact seam relation and closed embeddings, but its smooth seam-chart descent is itself described as follow-on work ([KummerWeld:462–493](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerWeld.lean:462)). Reuse its discipline, not its carrier.

### (c) Demand narrowing

`hcolD` is quantified over **every** structured representative satisfying `IsSpinSectorStr`, and that predicate is literally only `p.2.n = 0` ([CollapseDischarge:144–157](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:144), [KernelSector:80–82](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:80)). There is no restriction to outputs of the positive-rank surgery chain, sums, or doubled representatives.

The call path is:

1. universal `hcolD` produces `RankZeroCollapsesToEmptySurf` ([CollapseDischarge:125–135](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:125));
2. that produces `SectorIsGeometric` ([SectorGeometricReduce:90–99](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGeometricReduce.lean:90));
3. dC consumes only `SectorIsGeometric` ([SpinPresentationRow:147–155](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinPresentationRow.lean:147));
4. the final assembly invokes dC at that point ([BinderDischarge:78–95](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTBinderDischarge.lean:78)).

Consequences:

- Exact `RankZeroCollapseDatum` is stronger than dC needs.
- The exact weakest existing interface is `SectorIsGeometric`.
- A convenient intermediate is the universal class-level statement:
  \[
  \forall p,\ n(p)=0\Rightarrow
  \exists p'_{\emptyset},\ [p']=[p].
  \]
  The repository already proves this is the class-level shadow of `SectorIsGeometric` ([SectorGeometricReduce:101–113](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSectorGeometricReduce.lean:101)).
- Collapse after adding an explicitly null-bordant summand is enough if it yields that class equality.
- Restricting collapse to \([\Sigma]_M=0\) is insufficient unless a separate theorem first replaces every broad rank-zero class by a representative in that sub-sector.
- A sequence of T2 bordisms is enough for class equality even without a bordism-composition implementation: `T2DataBordismGrp` uses `Quot`, whose equivalence closure supplies transitivity ([T2TangentialBordism:63–79](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/T2TangentialBordism.lean:63), [BordismGroup:263–268](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/BordismGroup.lean:263)). This is a major reason the class-level route is Lean-cheaper than exact hcolD.

#### G9-4 / `KTKernelCard`

`KTKernelCard` classifies **every Brown-kernel class** as either \(0\) or the distinguished \(k_0\) ([PinPlusKTExtension:100–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTExtension.lean:100)). The in-tree derivation requires both:

- `KernelReducesToSpin`: all Brown-zero classes admit rank-zero representatives;
- `SpinImageIsTwo`: all such representatives lie in \(\{0,k_0\}\).

That factorization is explicit ([KernelSector:266–273](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:266)). The first is already labelled the deep KT §5 completeness direction ([KernelSector:210–225](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKernelSector.lean:210)).

Verdict: G9-4 is a valid logical alternative but the wrong trade for hcolD. It replaces a terminal class-geometric overhang with a global classification of the complete Brown kernel.

## 3. Brick decomposition

The exact-hcolD route should construct the reverse trace \(p'_{\emptyset}\to p\), then reverse it. Statement freezes should be theorem parameters or per-object structures—not new Lean `axiom`s.

| Brick | Content and output | Banked substrate | Honest freeze | Estimated new LOC |
|---|---|---|---|---:|
| B0 | Prove `emb_* surfClass = 0 ↔ wuClass2 = 0`; expose the \(v_2\) split | `hchar`, `homology_eq_zero_of_kroneckerH`, `pairing_bijective` | None | 80–140 |
| B1 | `RankZeroSurfaceBoundingDatum p`: compact T2/charted \(Q^3\), exact \(\partial Q\cong\Sigma\), closed boundary embedding, induced Pin\(^{-}\) compatibility | `GeoRealizationTied`, `emptySourceRealizationTied` | Low-dimensional Pin\(^{-}\) nullbordism / closed-surface classification | 120–220 interface; 800–1,500 to prove |
| B2 | `TerminalCharacteristicExtensionDatum`: produce an empty-surface endpoint \(p'_{\emptyset}\) and a combined Pin\(^{+}\) characteristic bordism \(W:p'_{\emptyset}\to p\), with \(Q\hookrightarrow W\) and exact end glue | `ktHandleAttachmentD5`, `SurgeredEndDatum`, `HandleAttachment.Weld`; Kummer seam discipline | **KT’s characteristic-extension theorem**, with framing/normal-bundle and endpoint construction | 180–300 interface; 2,000–5,000 to prove |
| B3 | Build `TraceWAdmLeaves b`: relative fundamental class, PL duality, finite-dimensionality, Betti equalities, and `wuW2=0` | `TraceRelFundLeaves`, `TraceWAdmLeaves.toWAdmPinned` ([TraceWAdm:109–153](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceWAdmPinned.lean:109)) | Per-trace PL/Wu row until a general manifold theorem exists | 300–700; 1,000–3,000 if foundations are proved |
| B4 | Instantiate the empty-source membrane. Rank zero makes `hq` and `hlagK` essentially `Fin 0`/zero-map proofs; package `TauMembraneWeldDatum` | `taylorLegVanishes_emptySource`, `jointLagrangian_emptySource`, `ofTauMembraneWeldDatum` | No further global theorem | 120–220 |
| B5 | Combine W-admissibility and membrane leaves to obtain a genuine tethered `Bor` | `traceTethered_of_leaves` ([TraceMembranePresented:141–151](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceMembranePresented.lean:141)) | None | 30–60 |
| B6 | Apply `symmBorTethered`; assemble `RankZeroCollapseDatum p` and its universal supply | `symmBorTethered`, `rankZeroCollapsesToEmptySurf_of_datumSupply` | None | 40–80 |
| B7, assembly-only branch | Stop before exact one-step gluing: prove universal class equality / `SectorIsGeometric` from the KT bordism sequence | Quotient equivalence closure and existing dC consumer | Only the source-level sequence, not a combined bordism | 20–60 |

The single hardest brick is **B2**, not the Lean packaging. It must turn a Pin\(^{-}\) nullbordism of the characteristic surface into a Pin\(^{+}\) 5-bordism with:

- a genuinely different empty-surface endpoint;
- the correct normal/framing data without assuming \(e=0\);
- a closed embedded characteristic membrane \(Q\hookrightarrow W\);
- exact compatibility with both end embeddings;
- enough handle/collar data to support the project’s chart and boundary encoding.

The sharpest acceptable freeze is therefore a per-\(p\), Type-valued `TerminalCharacteristicExtensionDatum`; it should not mention bordism-group equality, `KTKernelCard`, \(k_0\), or the final \(\mathbb Z/16\) result. Its consumer then derives `RankZeroCollapseDatum`, preserving kernel purity.

## 4. Ranked risks and unknowns

1. **Critical — source theorem versus current formal substrate.** KT supplies the geometric theorem, but no in-tree declaration constructs its combined \(W\), endpoint, and tether. Freezing only “\(\Sigma\) bounds” is too weak.

2. **Critical — normal Euler/framing.** Rank zero and `hchar` do not imply \(e=0\). A universal one-sphere index-3 handle proposal is therefore unsound without an additional framing theorem.

3. **High — exact hcolD asks for one bordism.** KT’s description is naturally staged, while the project deliberately uses quotient equivalence closure instead of implementing bordism composition. Exact hcolD needs a combined \(W\) or a new collar-gluing theorem; `SectorIsGeometric` does not.

4. **High — W-admissibility is independent work.** A topological handle attachment and T2 carrier do not produce `WAdmPinned`; the full PL/Wu row remains load-bearing ([TraceWAdm:104–144](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceWAdmPinned.lean:104)).

5. **High — rank-zero surface classification is absent.** “Finite union of spheres” is mathematically correct under the stated hypotheses, but no in-tree theorem converts the arbitrary carried surface into explicit sphere components and 3-balls.

6. **Medium — oriented GM normalization does not settle the Pin\(^{+}\), nonorientable Euler problem.** Only the oriented congruence and convention comparison were verified; no local source pins componentwise \(e\) in the required nonorientable setting.

7. **Medium — `emptySourceRealizationTied` is sometimes described too strongly in comments.** The declaration constructs a realization, not the bordism, W-admissibility, or tether. The capstone wrapper makes the missing inputs explicit ([EmptySourceRealization:302–344](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:302)).

8. **Low — source artifact pagination/OCR.** The PDF is image-only and its current page count disagrees with the extraction metadata. The terminal mechanism was OCR-verified, but symbol-perfect quotation requires visual checking.

9. **Provenance — checkout moved during review.** Opening HEAD was `d9373ba095adc0c920e8c09824e2382f9d2e2be4`; final HEAD was `ba271a11050bd50cc868cbd4643ae44c2ab5ea9b`. The intervening commit added the capstone seam-corrector lane and inventory artifacts; none of the cited hcolD, carrier, tether, demand, or source files changed. Final status and diff were clean. No build was run, because this was a read-only semantic/source audit; no files or generated artifacts were created.
