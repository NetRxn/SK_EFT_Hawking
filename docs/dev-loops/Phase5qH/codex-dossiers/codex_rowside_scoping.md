# codex_rowside_scoping

> **Promoted from session scratchpad 2026-07-21.** The raw ~1-2 MB codex
> transcript was session-scoped and would have been lost on cleanup; this is the run's
> **final deliverable** plus its run metadata. Source transcript: `codex_rowside_scoping.md` in the
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
session id: 019f82eb-4e3b-7a02-8e67-9e1d7e46ac3d
```

## Deliverable

## Verdict

At the audited snapshot—`main` at `ba271a11050bd50cc868cbd4643ae44c2ab5ea9b`—the advertised unconditional “ROW-INSTANTIATION COLLAPSE” is not present.

Two distinct reductions appear to have been conflated:

1. `PinPlusKTSpinRowInhabit` expands an assumed `row` into the conditional inputs `a + hdvd + K3 data`; it does not inhabit them. Its headline explicitly requires `a`, `hdvd`, `g`, `hrank`, and `hk3` and then calls `spinPresentationRow_of_atoms` [PinPlusKTSpinRowInhabit.lean:81–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinRowInhabit.lean:81).

2. The landed collapse in `PinPlusKTSphereProdP23Close` eliminates `str` and weakens `hrow` to the manifold-component pin `hs2s2`; its own documentation says the surviving row cluster is exactly `{row, hCob, hBase}` [PinPlusKTSphereProdP23Close.lean:296–325](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:296).

An all-tree and all-ref search found no `Nonempty (SpinPresentationRow residualProv)`, no concrete `SpinPresentationRow residualProv := ...`, and no module or historical commit containing the quoted “ROW-INSTANTIATION COLLAPSE” phrase. The only `presentationRow` constructor remains `K3RealizingElement.presentationRow`, which still takes `a`, `hdvd`, and a conditional `K3RealizingElement a` [PinPlusKTSpinSigmaStock.lean:280–288](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:280).

## 1. Current hypothesis row

The sharpest named equivalence theorem is:

`kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDiskPinned`

Its exact binder row is [PinPlusKTSphereProdP23Close.lean:326–340](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:326):

```lean
H :
  ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
    charPairBrown residualProv
      (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
    0 < p.2.n →
    KRSResidualRow residualProv p

row : SpinPresentationRow residualProv

hCob  : row.R.HandleTradeCobordism
hBase : row.R.HyperbolicBase

hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0

hcolD :
  ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
    IsSpinSectorStr residualProv p →
    RankZeroCollapseDatum residualProv p

hker : KerPhiSubDoubles residualProv

hΦg :
  spinForgetPhi residualProv
    (DataBordismGrp.mk (spinEmptyData residualProv) row.g)
    = ktKernelRep residualProv
```

The conclusion is:

```lean
Nonempty
  (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16)
```

The Rokhlin-order twin has the identical binder row and concludes `Nat.card ... = 16` [PinPlusKTSphereProdP23Close.lean:345–359](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:345).

| Binder | Shape | Status |
|---|---|---|
| `H` | Type-valued dependent supply, because `KRSResidualRow` is a structure | Open. `KRSResidualRow` begins with actual surgery/output data, not a proposition [PinPlusTraceCapstoneResidualRow.lean:149–166](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneResidualRow.lean:149). |
| `row` | `Type`; a structure containing `R`, `hdvd`, `g`, `hrank`, `hk3` | Open [PinPlusKTSpinPresentationRow.lean:84–94](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinPresentationRow.lean:84). |
| `hCob` | `Prop` | Open; exact definition below. |
| `hBase` | `Prop` | Open; exact definition below. |
| `hs2s2` | Equality `Prop` | Open; strictly weaker than old `hrow`. |
| `hcolD` | Type-valued dependent supply | Open; `RankZeroCollapseDatum` contains `p'`, a bordism, T2, and genuine tether [PinPlusKTCollapseDischarge.lean:90–101](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:90). |
| `hker` | `Prop` | Open; `∀ x, Φx=0 → ∃w, x=w+w` [PinPlusKTKerPhiDoubles.lean:90–97](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKerPhiDoubles.lean:90). |
| `hΦg` | Equality `Prop` | Open. |

`residualProv` is not a hypothesis: it is chosen unconditionally from the proved nonempty provider [PinPlusKTAssemblyResiduals.lean:65–72](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTAssemblyResiduals.lean:65).

### Headline progression

- `...ofReducedAtoms` still has the full concrete coboundary/P23 residual while retaining `row`, `hCob`, and `hBase` [PinPlusKTSphereProdCohomology.lean:194–218](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194).
- `...ofHomologyAtoms` removes the P23 triple but retains `str`, `hrow`, and three homological inputs [PinPlusKTSphereProdP23Close.lean:201–224](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:201).
- The §4 `...sphereDisk` theorem removes the remaining coboundary homology inputs but still binds `str` and `hrow` [PinPlusKTSphereProdP23Close.lean:253–276](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:253).
- §5 produces the actual terminal form: `str` disappears, while `hrow` is replaced by `hs2s2` [PinPlusKTSphereProdP23Close.lean:317–340](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:317).
- `PinPlusKTSphereProdWAdm.lean` has only §0–§2 in the present tree. Its sharpest theorem is the older `...ofDegenerate14` row, still carrying `b`, `hWT2`, `D`, two subsingleton instances, `P23`, `pin23`, and `hv2` [PinPlusKTSphereProdWAdm.lean:208–237](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdWAdm.lean:208). The reference to a fully discharged “§4” there is a version/file-name mismatch.

### Status of the six named atoms

| Atom | Present status |
|---|---|
| `row` | Remains explicitly. No unconditional inhabitant exists in the audited tree. |
| `hCob` | Remains explicitly. |
| `hBase` | Remains explicitly. |
| `str` | Eliminated unconditionally as a binder: the theorem uses `(row.R.s2s2).2`. |
| `hrow` | Its full `StrMfd` equality is eliminated, but its manifold projection remains as `hs2s2`. Thus it is weakened, not fully discharged. |
| `a` | Absent from the abstract headline, but not geometrically eliminated. The only current row-construction route requires it. |

If the abstract `row` is β-expanded through the most packaged existing builder, the actual row-side normal form is:

```lean
a     : SpinSigmaAtoms residualProv
hdvd  : ∀ x, (16 : ℤ) ∣ a.sig x
k     : K3RealizingElement a
hCob  : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism
hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase
hs2s2 : a.s2s2.1 = sphereProdSM4 0
```

and `hΦg` is restated using `k.g`. This composition is exact from `K3RealizingElement.presentationRow`, but there is no named theorem combining it with the terminal pinned headline.

Therefore the planning shorthand `{a,hCob,hBase}` also suppresses two presently uninhabited row ingredients: the global `hdvd` and `K3RealizingElement a`.

## 2. The `a` atom

### What `a` actually is

The live binder `a` is:

```lean
a : SpinSigmaAtoms residualProv
```

It is not, strictly speaking, `CanonicalSpinSigmaAtoms`. `SpinSigmaAtoms` contains total functions over every `StrMfd (spinEmptyData prov)`:

- `fc`
- `B`
- `wu`
- `pd`
- the bordism signature hom `sig`
- `sig_eq`
- a distinguished `s2s2`
- its rank-2 and hyperbolic pins

[PinPlusKTSpinSigmaAtom.lean:52–84](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:52).

`CanonicalSpinSigmaAtoms` is a stricter extension adding the disjoint-sum coherence equations `fc_sum` and `B_sum` [PinPlusKTSpinSigmaCanonicalBundle.lean:65–85](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaCanonicalBundle.lean:65). No inhabitant of either bundle was found.

`a` is converted into `SpinSigmaPresentation` by wiring `interMatrix`, deriving even-unimodularity from `wu + pd`, and copying the signature and `s2s2` slots [PinPlusKTSpinSigmaAtom.lean:90–103](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:90). It then builds `row` only after receiving `hdvd` and the K3 rank/form data [PinPlusKTSpinSigmaAtom.lean:116–133](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:116).

The final assembly consumes `row`, not `a` directly. But it genuinely needs the global presentation on arbitrary representatives: `sig_injective` inducts on an arbitrary quotient representative and uses `R.even_unimod p`, `R.sig_eq p`, and the sphere-product realization [SpinSigmaRoute.lean:113–125](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinSigmaRoute.lean:113). Generation then applies the resulting injectivity to every class [SpinSigmaRoute.lean:127–163](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinSigmaRoute.lean:127).

### Per-element versus total bundle

These two forms are not simply ordered.

- `SpinSigmaAtomPkg p` is locally stronger: it requires an actual `IntOrientation`, basis, and integral PD on a nonempty manifold [PinPlusKTSpinSigmaAtomReduce.lean:141–165](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:141).
- A finite bank of such packages is globally much weaker than `a`: it says nothing about arbitrary representatives, signature descent, disjoint-union coherence, or the empty element.
- A total per-element provider over all `p` would actually be ill-typed at the empty representative because `IntOrientation` needs `Nonempty`; the code explicitly records this vacuity boundary [PinPlusKTSpinSigmaAtomReduce.lean:31–44](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:31).

Adjudication:

1. **Mathematically weaker/sharper:** stock-only per-element packages are weaker and sharper for S⁴, S²×S², and K3. They are insufficient for the global classification argument. The sharp global contract remains a total functional E1 core plus signature bordism invariance.
2. **Cheaper in Lean:** per-element packages are far cheaper. The S⁴ package is already constructed [PinPlusKTSpinSigmaStockElement.lean:122–169](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStockElement.lean:122). But “cheaper” does not mean consumable by the current quotient induction.
3. **Actually consumed:** the assembly consumes total data through `SpinSigmaPresentation`. `SpinSigmaAtomPkg` only certifies an individual slot; it cannot build the total bundle [PinPlusKTSpinSigmaStock.lean:226–251](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:226).

### What would discharge `a`

A real discharge requires all of:

- total `fc/B/wu/pd` on every current-carrier representative;
- compatible handling of the empty and disconnected cases;
- a concrete S²×S² slot;
- signature additivity and bordism invariance.

The canonical bundle removes elementary disjoint-union additivity as a residual, but signature bordism invariance still remains as `hbord` [PinPlusKTSpinSigmaCanonicalBundle.lean:118–143](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaCanonicalBundle.lean:118). The deepest in-tree reduction names a Novikov Lagrangian for every data-bordant pair [PinPlusKTSpinSigmaHbord.lean:63–97](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaHbord.lean:63), but the gate proves that this atom is equivalent to `hbord`; it is not itself progress unless its restriction tower comes from the actual bounding manifold [PinPlusResidualGate.lean:689–700](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusResidualGate.lean:689).

`hdvd` is also not free from `a`. The in-tree Rokhlin theorem requires the additional topological/index-theoretic `topo : 2 ∣ σ/8` field for each smooth spin manifold [SpinRokhlinInterface.lean:62–86](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinRokhlinInterface.lean:62).

### Can `a` be eliminated?

- **Interface-only:** yes; the current headline already hides it behind `row`.
- **By the existing stock witnesses:** no. S⁴ is live, S²×S² still has the orientation/Gram/basis-identification gap [PinPlusKTSpinSigmaStock.lean:173–224](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:173), and `K3RealizingElement` remains conditional [PinPlusKTSpinSigmaStock.lean:253–288](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:253).
- **By restructuring:** only by replacing it with equivalent global content—such as a direct proof that the signature hom is injective or a total canonical E1 provider. That reduces API bulk but does not remove the mathematics.
- **By enriching the carrier:** possible in principle, but it changes the present faithful carrier and merely moves total E1 coherence into `Mfd`/`Bor`. I would not take that route for close-out.

The current Kummer work has produced substantial geometric infrastructure, but the consumer-facing `b₂=22` target is still explicitly unproved [KummerK7Opener.lean:118–130](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK7Opener.lean:118), and the final package/row capstone remains K10 [KummerK3Base.lean:112–118](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK3Base.lean:112).

## 3. `hCob` and `hBase` on the faithful carrier

Their exact statements are:

```lean
def HandleTradeCobordism (R) : Prop :=
  ∀ p m E N' (_ : IsHyperbolicForm N'),
    IntCongr (R.form p)
      (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ p', R.rank p' = m ∧
      IsDataBordant ξ p (R.s2s2 ⊔ p')
```

[HandleTradeSurgery.lean:56–71](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HandleTradeSurgery.lean:56).

```lean
def HyperbolicBase (R) : Prop :=
  ∀ p, R.rank p = 0 → DataBordismGrp.mk ξ p = 0
```

[SphereProductRealization.lean:74–79](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductRealization.lean:74).

### Did the Benedetti bricks transfer?

Only at the statement/algebra level.

The generic definitions and the kernel-pure induction from `{hCob,hBase}` to `RealizesSphereProducts` transfer to any `ξ`; that algebra is live [SphereProductRealization.lean:81–116](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductRealization.lean:81).

The actual geometric witnesses did not transfer because none were constructed. On the current specialization:

- `spinEmptyData.Mfd` is a `CharPairStrBundled` with literally empty characteristic surface;
- its `Bor` is `CharPairBorRealizedTethered` together with a `T2Space b.W` certificate [PinPlusKTSpinForgetPhi.lean:73–84](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinForgetPhi.lean:73);
- the target `pinPlusCharPairData` is explicitly the post-reflip faithful tethered `T2TangentialData` [PinPlusCharPairCarrier.lean:65–93](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65).

Thus the current checked-in `#200` theorem is not quantified over the vacated thin Pin⁺ carrier: it explicitly consumes `spinEmptyData residualProv` and concludes an equivalence on `T2DataBordismGrp (pinPlusCharPairData residualProv)` [PinPlusKTFreezeDischarge.lean:184–207](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTFreezeDischarge.lean:184). An earlier transient implementation may have existed, but it is not the present theorem.

### What is actually missing?

For `hCob`, the matrix congruence does not supply:

1. embedded representatives of the hyperbolic pair;
2. the framed attaching data;
3. a smooth five-dimensional handle trace;
4. identification of the outgoing end with `S²×S² ⊔ p'`;
5. the proof that `R.rank p' = m`;
6. T2 plus `WAdmPinned`/tethered empty-surface `Bor` data on that trace.

The trace consumer only says that a raw `Bordism` plus `Nonempty (ξ.Bor ...)` gives `IsDataBordant`; its `spinTraceBordism` still takes the chart, embeddings, end identification, smoothness, and boundary equations as inputs [PinPlusKTSurgeryTraceConsumers.lean:189–219](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSurgeryTraceConsumers.lean:189). The apparent residual theorem is definitionally `rfl`; it constructs nothing [PinPlusKTSurgeryTraceConsumers.lean:221–237](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSurgeryTraceConsumers.lean:221).

For `hBase`, one must construct, for every `R.rank p = 0`, an actual current-carrier nullbordism. The empty-membrane plumbing is reusable: given a raw coboundary with `T2Space` and `WAdmPinned`, `isDataBordant_empty_of_wadm` builds the tethered `spinEmptyData` relation [PinPlusKTSphereProdBordism.lean:160–178](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdBordism.lean:160). What remains is the bordism and its W-admissibility—not quotient algebra.

So the verdict is:

- **Restatement:** largely done.
- **Current-carrier adapter:** small and reusable.
- **Underlying geometry:** genuinely new. It must produce trace/coboundary data that preserve the present bundled/tethered structure.

The characteristic-surface surgery lanes do not help: they lower enhancement rank, while `hCob/hBase` concern the E1 intersection-form `b₂` axis. The settled-fork record prohibits composing them [SETTLED_FORKS.md:340–343](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:340). The newly landed `IsotropicFramedAttachingDatum` is likewise a supplier for `H` on the characteristic-surface lane, not for `hCob` [KTCompletenessTether.lean:232–255](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessTether.lean:232).

The Benedetti attribution/application to the additional `CharPairStrBundled`/tethered structure was not independently literature-verified in this pass.

## 4. Lean-feasible brick sequence

Estimates are net new Lean lines, order-of-magnitude only.

| Brick | Content and reusable substrate | Honest freeze, if needed | Estimate |
|---|---|---|---:|
| R0. Current-carrier empty-end adapter | Generalize the existing empty-end construction from `p ↝ ∅` to `p ↝ q`; reuse `charPairBorTethered_empty` and `dataBordant_of_traceBor`. | None; pure wiring. | 40–100 |
| R1. Concrete S²×S² row slot | Build the `spinEmptyData` structure on `sphereProdSM4 0`, set `a.s2s2` to it, and obtain `hs2s2` by `rfl`. Finish the Gram/basis route using `sphereProd_s2s2_hyp_of_cross_of_congr`. | Existing `hcross` and basis-congruence atoms are acceptable temporary freezes. | 250–600 |
| R2. Sharper total E1 core | Introduce, if desired, a pre-signature canonical bundle containing total `fc/B/wu/pd`, `fc_sum/B_sum`, and the concrete slot. Build `sig` rather than storing it. | This is a Type-valued data freeze, not an axiom. | 150–300 API work |
| R3. Global E1 inhabitation | Construct the total assignments for arbitrary empty-Σ representatives, including empty/disconnected cases and sum coherence. | Existing `SpinSigmaAtoms` is the honest coarse freeze. | 1,500–4,000+ |
| R4. Genuine signature descent | Build the real restriction/relative-PD tower from each actual `spinEmptyData` bordism and discharge `hbord`. Reuse `NovikovRealPairLESAtom` only when tied to the real bounding manifold. | `NovikovRealPairLESAtom` is acceptable as an explicit tracked hypothesis, but is equivalent to `hbord`. | 700–2,000+ |
| R5. Global Rokhlin bridge | For every representative, construct the `SmoothSpinManifold4` input and its `topo` field, then prove `hdvd`. | A per-manifold topological/index datum is the honest freeze. | 300–800 adapter; underlying theorem potentially much larger |
| R6. K3 completion | Finish K7 `b₂=22`, K8 intersection form, K9 `StrMfd` packaging, and K10 `SpinSigmaAtomPkg`/`K3RealizingElement`. | Keep K7/K8 geometric Gram statements explicit until proved. | 1,500–4,000+ from current state |
| R7. Row assembly | Apply `K3RealizingElement.presentationRow`; the concrete slot makes `hs2s2` definitional. | None. | 20–60 |
| A1. Hyperbolic pair realization | Turn the `IntCongr` input into embedded, framed geometric surgery data. This is the algebra-to-geometry bridge absent from the current trace API. | A `HandleTradeGeometricInput` structure carrying actual embeddings/framing is honest. | 1,000–2,500+ |
| A2. Handle trace and outgoing-form calculation | Build the smooth trace, identify the outgoing end, prove complement rank/form, T2, and `WAdmPinned`; feed R0 to obtain `IsDataBordant`. | `HandleTradeTraceWAdm` carrying the actual bordism is an honest intermediate. | 800–2,000+ |
| A3. Rank-zero base | Produce a rank-zero current-carrier coboundary and `WAdmPinned`, then use `isDataBordant_empty_of_wadm`; convert the bordism equality to `HyperbolicBase`. | `RankZeroSpinCoboundaryWAdm` is the sharp honest geometric freeze. | 800–2,000+ |
| Z. Final wrapper | Feed the concrete row, `hCob`, `hBase`, and definitional `hs2s2` into the pinned headline. | None. | 20–50 |

The hardest single brick is A1: the present hypothesis is an algebraic congruence of intersection matrices, but the consumer needs embedded framed geometry and a structured five-dimensional trace. R3/R4 is the other major foundational wall because it is globally quantified over every representative.

## 5. Ranked risks

1. **False status premise:** there is no unconditional row instance at current head. Planning against one would conceal `a`, `hdvd`, K3, `hCob`, `hBase`, and `hs2s2`.
2. **Carrier-strength mismatch:** classical spin handle trading/nullbordism does not automatically provide the present `CharPairStrBundled` and tethered/T2 `Bor` witnesses.
3. **Algebra-to-embedded-geometry gap:** an `IntCongr` between forms does not itself produce embedded spheres, framed handles, or outgoing-end identification.
4. **Globality of `a`:** stock-element proofs do not cover arbitrary quotient representatives; total PD/coherence and Novikov bordism invariance remain.
5. **Rokhlin undercount:** `hdvd` is a separate global topological obligation, not a consequence of merely having even-unimodular forms.
6. **K3 status drift:** the welded Kummer carrier is progressing, but `b₂=22`, the K3 form, `StrMfd` packaging, and `K3RealizingElement` are not yet closed.
7. **S²×S² normalization:** the bounding theorem is discharged once the row slot’s manifold is concrete, but constructing the row with that exact slot still needs the spin structure and Gram/basis work.
8. **Live-worktree churn:** `main` advanced during the audit, and an unrelated untracked SymTFT file appeared afterward. The dossier is frozen specifically to `ba271a11`.

No files were changed and no build was run. The conclusions above come from declaration/consumer inspection and repository-wide history/search; kernel-axiom closure was not re-executed in this read-only pass.


tokens used
503,344
## Verdict

At the audited snapshot—`main` at `ba271a11050bd50cc868cbd4643ae44c2ab5ea9b`—the advertised unconditional “ROW-INSTANTIATION COLLAPSE” is not present.

Two distinct reductions appear to have been conflated:

1. `PinPlusKTSpinRowInhabit` expands an assumed `row` into the conditional inputs `a + hdvd + K3 data`; it does not inhabit them. Its headline explicitly requires `a`, `hdvd`, `g`, `hrank`, and `hk3` and then calls `spinPresentationRow_of_atoms` [PinPlusKTSpinRowInhabit.lean:81–107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinRowInhabit.lean:81).

2. The landed collapse in `PinPlusKTSphereProdP23Close` eliminates `str` and weakens `hrow` to the manifold-component pin `hs2s2`; its own documentation says the surviving row cluster is exactly `{row, hCob, hBase}` [PinPlusKTSphereProdP23Close.lean:296–325](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:296).

An all-tree and all-ref search found no `Nonempty (SpinPresentationRow residualProv)`, no concrete `SpinPresentationRow residualProv := ...`, and no module or historical commit containing the quoted “ROW-INSTANTIATION COLLAPSE” phrase. The only `presentationRow` constructor remains `K3RealizingElement.presentationRow`, which still takes `a`, `hdvd`, and a conditional `K3RealizingElement a` [PinPlusKTSpinSigmaStock.lean:280–288](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:280).

## 1. Current hypothesis row

The sharpest named equivalence theorem is:

`kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDiskPinned`

Its exact binder row is [PinPlusKTSphereProdP23Close.lean:326–340](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:326):

```lean
H :
  ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
    charPairBrown residualProv
      (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
    0 < p.2.n →
    KRSResidualRow residualProv p

row : SpinPresentationRow residualProv

hCob  : row.R.HandleTradeCobordism
hBase : row.R.HyperbolicBase

hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0

hcolD :
  ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
    IsSpinSectorStr residualProv p →
    RankZeroCollapseDatum residualProv p

hker : KerPhiSubDoubles residualProv

hΦg :
  spinForgetPhi residualProv
    (DataBordismGrp.mk (spinEmptyData residualProv) row.g)
    = ktKernelRep residualProv
```

The conclusion is:

```lean
Nonempty
  (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16)
```

The Rokhlin-order twin has the identical binder row and concludes `Nat.card ... = 16` [PinPlusKTSphereProdP23Close.lean:345–359](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:345).

| Binder | Shape | Status |
|---|---|---|
| `H` | Type-valued dependent supply, because `KRSResidualRow` is a structure | Open. `KRSResidualRow` begins with actual surgery/output data, not a proposition [PinPlusTraceCapstoneResidualRow.lean:149–166](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneResidualRow.lean:149). |
| `row` | `Type`; a structure containing `R`, `hdvd`, `g`, `hrank`, `hk3` | Open [PinPlusKTSpinPresentationRow.lean:84–94](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinPresentationRow.lean:84). |
| `hCob` | `Prop` | Open; exact definition below. |
| `hBase` | `Prop` | Open; exact definition below. |
| `hs2s2` | Equality `Prop` | Open; strictly weaker than old `hrow`. |
| `hcolD` | Type-valued dependent supply | Open; `RankZeroCollapseDatum` contains `p'`, a bordism, T2, and genuine tether [PinPlusKTCollapseDischarge.lean:90–101](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTCollapseDischarge.lean:90). |
| `hker` | `Prop` | Open; `∀ x, Φx=0 → ∃w, x=w+w` [PinPlusKTKerPhiDoubles.lean:90–97](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTKerPhiDoubles.lean:90). |
| `hΦg` | Equality `Prop` | Open. |

`residualProv` is not a hypothesis: it is chosen unconditionally from the proved nonempty provider [PinPlusKTAssemblyResiduals.lean:65–72](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTAssemblyResiduals.lean:65).

### Headline progression

- `...ofReducedAtoms` still has the full concrete coboundary/P23 residual while retaining `row`, `hCob`, and `hBase` [PinPlusKTSphereProdCohomology.lean:194–218](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdCohomology.lean:194).
- `...ofHomologyAtoms` removes the P23 triple but retains `str`, `hrow`, and three homological inputs [PinPlusKTSphereProdP23Close.lean:201–224](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:201).
- The §4 `...sphereDisk` theorem removes the remaining coboundary homology inputs but still binds `str` and `hrow` [PinPlusKTSphereProdP23Close.lean:253–276](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:253).
- §5 produces the actual terminal form: `str` disappears, while `hrow` is replaced by `hs2s2` [PinPlusKTSphereProdP23Close.lean:317–340](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdP23Close.lean:317).
- `PinPlusKTSphereProdWAdm.lean` has only §0–§2 in the present tree. Its sharpest theorem is the older `...ofDegenerate14` row, still carrying `b`, `hWT2`, `D`, two subsingleton instances, `P23`, `pin23`, and `hv2` [PinPlusKTSphereProdWAdm.lean:208–237](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdWAdm.lean:208). The reference to a fully discharged “§4” there is a version/file-name mismatch.

### Status of the six named atoms

| Atom | Present status |
|---|---|
| `row` | Remains explicitly. No unconditional inhabitant exists in the audited tree. |
| `hCob` | Remains explicitly. |
| `hBase` | Remains explicitly. |
| `str` | Eliminated unconditionally as a binder: the theorem uses `(row.R.s2s2).2`. |
| `hrow` | Its full `StrMfd` equality is eliminated, but its manifold projection remains as `hs2s2`. Thus it is weakened, not fully discharged. |
| `a` | Absent from the abstract headline, but not geometrically eliminated. The only current row-construction route requires it. |

If the abstract `row` is β-expanded through the most packaged existing builder, the actual row-side normal form is:

```lean
a     : SpinSigmaAtoms residualProv
hdvd  : ∀ x, (16 : ℤ) ∣ a.sig x
k     : K3RealizingElement a
hCob  : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism
hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase
hs2s2 : a.s2s2.1 = sphereProdSM4 0
```

and `hΦg` is restated using `k.g`. This composition is exact from `K3RealizingElement.presentationRow`, but there is no named theorem combining it with the terminal pinned headline.

Therefore the planning shorthand `{a,hCob,hBase}` also suppresses two presently uninhabited row ingredients: the global `hdvd` and `K3RealizingElement a`.

## 2. The `a` atom

### What `a` actually is

The live binder `a` is:

```lean
a : SpinSigmaAtoms residualProv
```

It is not, strictly speaking, `CanonicalSpinSigmaAtoms`. `SpinSigmaAtoms` contains total functions over every `StrMfd (spinEmptyData prov)`:

- `fc`
- `B`
- `wu`
- `pd`
- the bordism signature hom `sig`
- `sig_eq`
- a distinguished `s2s2`
- its rank-2 and hyperbolic pins

[PinPlusKTSpinSigmaAtom.lean:52–84](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:52).

`CanonicalSpinSigmaAtoms` is a stricter extension adding the disjoint-sum coherence equations `fc_sum` and `B_sum` [PinPlusKTSpinSigmaCanonicalBundle.lean:65–85](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaCanonicalBundle.lean:65). No inhabitant of either bundle was found.

`a` is converted into `SpinSigmaPresentation` by wiring `interMatrix`, deriving even-unimodularity from `wu + pd`, and copying the signature and `s2s2` slots [PinPlusKTSpinSigmaAtom.lean:90–103](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:90). It then builds `row` only after receiving `hdvd` and the K3 rank/form data [PinPlusKTSpinSigmaAtom.lean:116–133](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtom.lean:116).

The final assembly consumes `row`, not `a` directly. But it genuinely needs the global presentation on arbitrary representatives: `sig_injective` inducts on an arbitrary quotient representative and uses `R.even_unimod p`, `R.sig_eq p`, and the sphere-product realization [SpinSigmaRoute.lean:113–125](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinSigmaRoute.lean:113). Generation then applies the resulting injectivity to every class [SpinSigmaRoute.lean:127–163](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinSigmaRoute.lean:127).

### Per-element versus total bundle

These two forms are not simply ordered.

- `SpinSigmaAtomPkg p` is locally stronger: it requires an actual `IntOrientation`, basis, and integral PD on a nonempty manifold [PinPlusKTSpinSigmaAtomReduce.lean:141–165](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:141).
- A finite bank of such packages is globally much weaker than `a`: it says nothing about arbitrary representatives, signature descent, disjoint-union coherence, or the empty element.
- A total per-element provider over all `p` would actually be ill-typed at the empty representative because `IntOrientation` needs `Nonempty`; the code explicitly records this vacuity boundary [PinPlusKTSpinSigmaAtomReduce.lean:31–44](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaAtomReduce.lean:31).

Adjudication:

1. **Mathematically weaker/sharper:** stock-only per-element packages are weaker and sharper for S⁴, S²×S², and K3. They are insufficient for the global classification argument. The sharp global contract remains a total functional E1 core plus signature bordism invariance.
2. **Cheaper in Lean:** per-element packages are far cheaper. The S⁴ package is already constructed [PinPlusKTSpinSigmaStockElement.lean:122–169](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStockElement.lean:122). But “cheaper” does not mean consumable by the current quotient induction.
3. **Actually consumed:** the assembly consumes total data through `SpinSigmaPresentation`. `SpinSigmaAtomPkg` only certifies an individual slot; it cannot build the total bundle [PinPlusKTSpinSigmaStock.lean:226–251](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:226).

### What would discharge `a`

A real discharge requires all of:

- total `fc/B/wu/pd` on every current-carrier representative;
- compatible handling of the empty and disconnected cases;
- a concrete S²×S² slot;
- signature additivity and bordism invariance.

The canonical bundle removes elementary disjoint-union additivity as a residual, but signature bordism invariance still remains as `hbord` [PinPlusKTSpinSigmaCanonicalBundle.lean:118–143](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaCanonicalBundle.lean:118). The deepest in-tree reduction names a Novikov Lagrangian for every data-bordant pair [PinPlusKTSpinSigmaHbord.lean:63–97](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaHbord.lean:63), but the gate proves that this atom is equivalent to `hbord`; it is not itself progress unless its restriction tower comes from the actual bounding manifold [PinPlusResidualGate.lean:689–700](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusResidualGate.lean:689).

`hdvd` is also not free from `a`. The in-tree Rokhlin theorem requires the additional topological/index-theoretic `topo : 2 ∣ σ/8` field for each smooth spin manifold [SpinRokhlinInterface.lean:62–86](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SpinRokhlinInterface.lean:62).

### Can `a` be eliminated?

- **Interface-only:** yes; the current headline already hides it behind `row`.
- **By the existing stock witnesses:** no. S⁴ is live, S²×S² still has the orientation/Gram/basis-identification gap [PinPlusKTSpinSigmaStock.lean:173–224](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:173), and `K3RealizingElement` remains conditional [PinPlusKTSpinSigmaStock.lean:253–288](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:253).
- **By restructuring:** only by replacing it with equivalent global content—such as a direct proof that the signature hom is injective or a total canonical E1 provider. That reduces API bulk but does not remove the mathematics.
- **By enriching the carrier:** possible in principle, but it changes the present faithful carrier and merely moves total E1 coherence into `Mfd`/`Bor`. I would not take that route for close-out.

The current Kummer work has produced substantial geometric infrastructure, but the consumer-facing `b₂=22` target is still explicitly unproved [KummerK7Opener.lean:118–130](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK7Opener.lean:118), and the final package/row capstone remains K10 [KummerK3Base.lean:112–118](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK3Base.lean:112).

## 3. `hCob` and `hBase` on the faithful carrier

Their exact statements are:

```lean
def HandleTradeCobordism (R) : Prop :=
  ∀ p m E N' (_ : IsHyperbolicForm N'),
    IntCongr (R.form p)
      (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ p', R.rank p' = m ∧
      IsDataBordant ξ p (R.s2s2 ⊔ p')
```

[HandleTradeSurgery.lean:56–71](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/HandleTradeSurgery.lean:56).

```lean
def HyperbolicBase (R) : Prop :=
  ∀ p, R.rank p = 0 → DataBordismGrp.mk ξ p = 0
```

[SphereProductRealization.lean:74–79](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductRealization.lean:74).

### Did the Benedetti bricks transfer?

Only at the statement/algebra level.

The generic definitions and the kernel-pure induction from `{hCob,hBase}` to `RealizesSphereProducts` transfer to any `ξ`; that algebra is live [SphereProductRealization.lean:81–116](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProductRealization.lean:81).

The actual geometric witnesses did not transfer because none were constructed. On the current specialization:

- `spinEmptyData.Mfd` is a `CharPairStrBundled` with literally empty characteristic surface;
- its `Bor` is `CharPairBorRealizedTethered` together with a `T2Space b.W` certificate [PinPlusKTSpinForgetPhi.lean:73–84](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinForgetPhi.lean:73);
- the target `pinPlusCharPairData` is explicitly the post-reflip faithful tethered `T2TangentialData` [PinPlusCharPairCarrier.lean:65–93](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairCarrier.lean:65).

Thus the current checked-in `#200` theorem is not quantified over the vacated thin Pin⁺ carrier: it explicitly consumes `spinEmptyData residualProv` and concludes an equivalence on `T2DataBordismGrp (pinPlusCharPairData residualProv)` [PinPlusKTFreezeDischarge.lean:184–207](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTFreezeDischarge.lean:184). An earlier transient implementation may have existed, but it is not the present theorem.

### What is actually missing?

For `hCob`, the matrix congruence does not supply:

1. embedded representatives of the hyperbolic pair;
2. the framed attaching data;
3. a smooth five-dimensional handle trace;
4. identification of the outgoing end with `S²×S² ⊔ p'`;
5. the proof that `R.rank p' = m`;
6. T2 plus `WAdmPinned`/tethered empty-surface `Bor` data on that trace.

The trace consumer only says that a raw `Bordism` plus `Nonempty (ξ.Bor ...)` gives `IsDataBordant`; its `spinTraceBordism` still takes the chart, embeddings, end identification, smoothness, and boundary equations as inputs [PinPlusKTSurgeryTraceConsumers.lean:189–219](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSurgeryTraceConsumers.lean:189). The apparent residual theorem is definitionally `rfl`; it constructs nothing [PinPlusKTSurgeryTraceConsumers.lean:221–237](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSurgeryTraceConsumers.lean:221).

For `hBase`, one must construct, for every `R.rank p = 0`, an actual current-carrier nullbordism. The empty-membrane plumbing is reusable: given a raw coboundary with `T2Space` and `WAdmPinned`, `isDataBordant_empty_of_wadm` builds the tethered `spinEmptyData` relation [PinPlusKTSphereProdBordism.lean:160–178](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSphereProdBordism.lean:160). What remains is the bordism and its W-admissibility—not quotient algebra.

So the verdict is:

- **Restatement:** largely done.
- **Current-carrier adapter:** small and reusable.
- **Underlying geometry:** genuinely new. It must produce trace/coboundary data that preserve the present bundled/tethered structure.

The characteristic-surface surgery lanes do not help: they lower enhancement rank, while `hCob/hBase` concern the E1 intersection-form `b₂` axis. The settled-fork record prohibits composing them [SETTLED_FORKS.md:340–343](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:340). The newly landed `IsotropicFramedAttachingDatum` is likewise a supplier for `H` on the characteristic-surface lane, not for `hCob` [KTCompletenessTether.lean:232–255](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessTether.lean:232).

The Benedetti attribution/application to the additional `CharPairStrBundled`/tethered structure was not independently literature-verified in this pass.

## 4. Lean-feasible brick sequence

Estimates are net new Lean lines, order-of-magnitude only.

| Brick | Content and reusable substrate | Honest freeze, if needed | Estimate |
|---|---|---|---:|
| R0. Current-carrier empty-end adapter | Generalize the existing empty-end construction from `p ↝ ∅` to `p ↝ q`; reuse `charPairBorTethered_empty` and `dataBordant_of_traceBor`. | None; pure wiring. | 40–100 |
| R1. Concrete S²×S² row slot | Build the `spinEmptyData` structure on `sphereProdSM4 0`, set `a.s2s2` to it, and obtain `hs2s2` by `rfl`. Finish the Gram/basis route using `sphereProd_s2s2_hyp_of_cross_of_congr`. | Existing `hcross` and basis-congruence atoms are acceptable temporary freezes. | 250–600 |
| R2. Sharper total E1 core | Introduce, if desired, a pre-signature canonical bundle containing total `fc/B/wu/pd`, `fc_sum/B_sum`, and the concrete slot. Build `sig` rather than storing it. | This is a Type-valued data freeze, not an axiom. | 150–300 API work |
| R3. Global E1 inhabitation | Construct the total assignments for arbitrary empty-Σ representatives, including empty/disconnected cases and sum coherence. | Existing `SpinSigmaAtoms` is the honest coarse freeze. | 1,500–4,000+ |
| R4. Genuine signature descent | Build the real restriction/relative-PD tower from each actual `spinEmptyData` bordism and discharge `hbord`. Reuse `NovikovRealPairLESAtom` only when tied to the real bounding manifold. | `NovikovRealPairLESAtom` is acceptable as an explicit tracked hypothesis, but is equivalent to `hbord`. | 700–2,000+ |
| R5. Global Rokhlin bridge | For every representative, construct the `SmoothSpinManifold4` input and its `topo` field, then prove `hdvd`. | A per-manifold topological/index datum is the honest freeze. | 300–800 adapter; underlying theorem potentially much larger |
| R6. K3 completion | Finish K7 `b₂=22`, K8 intersection form, K9 `StrMfd` packaging, and K10 `SpinSigmaAtomPkg`/`K3RealizingElement`. | Keep K7/K8 geometric Gram statements explicit until proved. | 1,500–4,000+ from current state |
| R7. Row assembly | Apply `K3RealizingElement.presentationRow`; the concrete slot makes `hs2s2` definitional. | None. | 20–60 |
| A1. Hyperbolic pair realization | Turn the `IntCongr` input into embedded, framed geometric surgery data. This is the algebra-to-geometry bridge absent from the current trace API. | A `HandleTradeGeometricInput` structure carrying actual embeddings/framing is honest. | 1,000–2,500+ |
| A2. Handle trace and outgoing-form calculation | Build the smooth trace, identify the outgoing end, prove complement rank/form, T2, and `WAdmPinned`; feed R0 to obtain `IsDataBordant`. | `HandleTradeTraceWAdm` carrying the actual bordism is an honest intermediate. | 800–2,000+ |
| A3. Rank-zero base | Produce a rank-zero current-carrier coboundary and `WAdmPinned`, then use `isDataBordant_empty_of_wadm`; convert the bordism equality to `HyperbolicBase`. | `RankZeroSpinCoboundaryWAdm` is the sharp honest geometric freeze. | 800–2,000+ |
| Z. Final wrapper | Feed the concrete row, `hCob`, `hBase`, and definitional `hs2s2` into the pinned headline. | None. | 20–50 |

The hardest single brick is A1: the present hypothesis is an algebraic congruence of intersection matrices, but the consumer needs embedded framed geometry and a structured five-dimensional trace. R3/R4 is the other major foundational wall because it is globally quantified over every representative.

## 5. Ranked risks

1. **False status premise:** there is no unconditional row instance at current head. Planning against one would conceal `a`, `hdvd`, K3, `hCob`, `hBase`, and `hs2s2`.
2. **Carrier-strength mismatch:** classical spin handle trading/nullbordism does not automatically provide the present `CharPairStrBundled` and tethered/T2 `Bor` witnesses.
3. **Algebra-to-embedded-geometry gap:** an `IntCongr` between forms does not itself produce embedded spheres, framed handles, or outgoing-end identification.
4. **Globality of `a`:** stock-element proofs do not cover arbitrary quotient representatives; total PD/coherence and Novikov bordism invariance remain.
5. **Rokhlin undercount:** `hdvd` is a separate global topological obligation, not a consequence of merely having even-unimodular forms.
6. **K3 status drift:** the welded Kummer carrier is progressing, but `b₂=22`, the K3 form, `StrMfd` packaging, and `K3RealizingElement` are not yet closed.
7. **S²×S² normalization:** the bounding theorem is discharged once the row slot’s manifold is concrete, but constructing the row with that exact slot still needs the spin structure and Gram/basis work.
8. **Live-worktree churn:** `main` advanced during the audit, and an unrelated untracked SymTFT file appeared afterward. The dossier is frozen specifically to `ba271a11`.

No files were changed and no build was run. The conclusions above come from declaration/consumer inspection and repository-wide history/search; kernel-axiom closure was not re-executed in this read-only pass.
