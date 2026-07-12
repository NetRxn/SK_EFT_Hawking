# E4/E5 ASSEMBLY GAP-MAP + glue audit — 2026-07-12 (wt2, base main @ `a461fb3a`)

> Deliverable of the E4/E5 gap-map mission (worker slot 2). Method: declaration-level audit of the
> assembly chain from the current kernel-pure state to the intended target
> `omega4PinPlusGM_equiv_zmod16`, cross-checked against `HYPOTHESIS_REGISTRY`
> (`src/core/constants.py`), the atlas (`lean/atlas_view.json`), and `SETTLED_FORKS.md`.
> Every file:line below verified in this worktree.

## 0. The target and its intended shape

The literal name `omega4PinPlusGM_equiv_zmod16` does **not** exist in-tree. Per the kernel-checked
no-go `genuine-gm-carrier-eight-torsion` (`PinPlusGMDataZ16.pinPlusGMData_not_equiv_zmod16`,
`PinPlusGMDataZ16.lean:213–225`; the thin carrier is 8-torsion —
`pinPlusGMData_eight_torsion`, `:176–211`), the genuine target lives on the **enriched tied
carrier**:

```
omega4PinPlusGM_equiv_zmod16 :
  Nonempty (DataBordismGrp (pinPlusGMTiedData (𝓡 4)) ≃+ ZMod 16)
```

(or the packaged `DataBordismGrp (pinPlusGMTiedData (𝓡 4)) ≃+ ZMod 16` via the
`…_via_grade` form, `PinPlusGMDataZ16.lean:278–294`). Carrier:
`pinPlusGMTiedData` (`PinPlusGMTiedData.lean:56–93`), grade
`abkGMTied16 : DataBordismGrp (pinPlusGMTiedData (𝓡 4)) →+ ZMod 16` (`PinPlusGMTiedData.lean:95–104`).

## 1. The assembly DAG — what is DONE (kernel-pure, in-tree)

Everything below `lean_verify`s to exactly `{propext, Classical.choice, Quot.sound}`:

```
                     abkGMTied16_rp4_odd (PinPlusGMWitness.lean:101)
                              │
                    abkGMTied16_range_top_of_odd (PinPlusGMTiedData.lean:125)
                              │
              SURJECTIVITY: abkGMTied16_surjective (PinPlusGMWitness.lean:107)   ← DONE
                              │
        L2-strength: dataBordismGMTied_quotient_equiv_zmod16 (PinPlusGMWitness.lean:114)  ← DONE
                              │
      ┌───────────────────────┴─ EIGHT conditional doors to the full iso (ALL BUILT) ─────────┐
      │ D1 _of_cap  (hfin, card ≤ 16)                    PinPlusGMWitness.lean:155            │
      │ D2 _of_smith_les (Nonempty iso)                  PinPlusGMWitness.lean:196            │
      │ D3 _via_smith_les_neighbor (sm, exact, A≃ℤ/16)   PinPlusGMWitness.lean:206            │
      │ D4 _of_spin_image_card (Nat.card ker = 2)        PinPlusGMWitness.lean:223            │
      │ D5 _via_kt_lemma53 (s, s n=0↔2∣n, ker=range)     PinPlusGMWitness.lean:249            │
      │ D6 _via_kt_of_grade0 (hbound)                    PinPlusGMWitness.lean:385            │
      │ D7 _of_ker_le_spin_range (hle)                   PinPlusGMWitness.lean:345            │
      │ D8 _of_thom (hthom, GEOMETRIC form)              UnorientedThomCapstone.lean:59       │
      │    + _of_card_le_abutment / iso_iff_card_le_abutment (E5 numeric door)                │
      │      PinPlusFaithfulnessCardBridge.lean:91 / :110                                     │
      └───────────────────────────────────────────────────────────────────────────────────────┘
                              │  all keys apex-equivalent (kernel-checked:
                              │  spin_range_ge_of_grade0_inj PinPlusGMWitness.lean:359 +
                              │  grade0_bounds_of_thom UnorientedThomCapstone.lean:36 +
                              │  settled fork 5qH-injectivity-routes-all-equal-one-completeness-prop)
                              ▼
              ★ N1 — THE ONE OPEN E4 NODE: the completeness key (below)
```

Supporting DONE pieces: `g8`/`addOrderOf_g8`/`spin_range_le_ker_reduce`
(`PinPlusGMWitness.lean:281–330`), `forgetTie`/`abkGM8_forgetTie` (tied→thin comparison,
`PinPlusGMDataZ16.lean:306–367`), the KT exact-sequence algebra
(`PinPlusExactSequence.lean:27–92`), the ℝP⁴ odd witness chain (`PinPlusGMWitness.lean:29–105`),
the abstract Smith-LES transport (`PinPlusSmithLES.lean:33–64`,
`PinPlusGMDataZ16.lean:242–294`).

## 2. The open-node table (complete, current → target)

| # | Node | Where (binder/Prop) | Class | Discharges via |
|---|------|---------------------|-------|----------------|
| **N1** | **The completeness key** — equivalently `hthom` (SW-trivial certified 4-mfd bounds), `hbound` (grade-0-injectivity of `abkGMTied16`), `hfin+card≤16`, `Nat.card ker(reduce∘abk)=2`, KT-Lemma-5.3 `ker = s.range`, or the Smith-LES neighbor | `UnorientedThomCapstone.lean:40` (hthom); `PinPlusGMWitness.lean:366,390` (hbound); binder-carried, **not** a registry Prop | **genuinely-open** (the single deep geometric input) | KT §5 route (re-anchored 2026-07-06): N1a + N1b + N1c + N2, assembled from below (`0 → ℤ/2 → Ω₄^{Pin⁺} → ℤ/8 → 0`). The demoted alternative is N7 (E5 spectral). |
| N1a | `Ω₄^{Spin} ≅ ℤ` | `hyp:spin_bordism_iso_Z`, `constants.py:2814`, status `proposed` | genuinely-open | DR route (`Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md`): σ=0 spin ⟹ even-indefinite ≅ nH (Milnor–Husemoller lattice algebra — formalizable against E1's `interMatrix` substrate) ⟹ `n(S²×S²)` ⟹ bounds by 3-handle attachment (the ONE Mathlib-absent manifold-topology step). NO Rokhlin-only shortcut (settled-fork caveat 2026-07-06b). |
| N1b | geometric Smith map into the **tied** carrier | none in-tree; `SmithIsomorphism.smithDataHom` (`SmithIsomorphism.lean:220`) lands in the OLD `pinPlusData` carrier only | genuinely-open (E3) | the `PD(a)` zero-locus geometry — `ManifoldSmithPD.MSectionTransverse` / `mSectionZeroLocus_singularManifold` (`ManifoldSmithPD.lean:39,62`) is the started substrate; the synthetic emptySM shortcut is DEAD (`synthetic-smith-map-to-tied-carrier`) |
| N1c | KT Lemma 5.3 (÷32 double-cover: `ker s = 2ℤ`) | consumed abstractly by D5 (`PinPlusGMWitness.lean:249`); no geometric fragment in-tree | genuinely-open | double-cover signature `÷32` + N1a (K3 generates); algebra half is D5-ready |
| **N2** | `htopo : 2 ∣ σ/8` (the irreducibly geometric Rokhlin factor; = N1d at `F = ∅`) | `hyp:rokhlin_sigma_mod_16`, `constants.py:2588`; interface field `SmoothSpinManifold4.topo` (`SpinRokhlinInterface.lean`) | genuinely-open, E2-decomposed | `topo_of_gm_null` (`GMRokhlinDischarge.lean:51`) reduces it to `GMrelation σ 0 Q ∧ Q.brown = 0`; `sixteen_dvd_sig_of_gm_metabolic` (`:332`) closes the metabolic case; `CharSurface.gmrelation_null`/`brown_eq_zero` (`CharSurfaceBounding.lean:116,126`) reduce β=0 to the two FROZEN Props `TaylorKernelVanishing` (`:101`) + `KernelHalfLivesHalfDies` (`:109`) at a `PinCharSurface.Bounding`. Open remainder: (i) producing the `Bounding` geometry (Taylor Lem 1.2/1.3), (ii) [FK] bordism-invariance transport, (iii) the GM congruence at general spin M. |
| N3 | `d : IntOrientationData M` | `hyp:intOrientation_datum`, `constants.py:3103`, active; structure `IntOrientationSection.lean:127` | genuinely-open (E1, in progress) | the global coherent ±1-section gluing (ℤ-`hasFundClassInt` induction); ALL local inputs proven (`intLocalHomologyIso_datum` = **proven**, `constants.py:3153`) |
| N4 | `kron/hkron` (H₂ integral Kronecker duality `H₂ ≃ₗ Dual H²`) | binder in `SixteenDvdOfOrientation.lean:87` and `SixteenDvdOfOrientationSpin.lean` | genuinely-open (E1) | integral UCT at free/fg H²: the engine exists RELATIVELY (`SingularRelativeUCInt.relUCTIsoZOfFree`, `relKroneckerHInt_bijective_of_free`, `:488–516`); absolute-at-closed-M port open. NOTE the registry marks the capIso/intPD trio `superseded_on_wiring_path` (`constants.py:3299,3350,3404`) — correct for `hcoreG`, but the **class-level leg still consumes `kron` as a binder**; do not read "superseded" as "gone". |
| N5 | `B : IntH2Basis` | `hyp:intH2_basis_datum`, `constants.py:3217`, active | genuinely-open (E1) | fg/free-ness of `H₂(M;ℤ)` at closed charted 4-manifolds (finiteness tower) |
| N6 | `hv2 : wuClass2 (poincareDual4Mid_of_closed) = 0` (spin certificate, mod-2 form) | binder in `SpinWuDatumClosed.lean:54` / `SixteenDvdOfOrientationSpin.lean` | open **wiring seam** (E2↔E4 vocabulary) | per-manifold honest input; the Pin⁺ tower speaks `PinPlusCertK`/`swTotalNe` — a `w₂`-presentation bridge is needed to feed it from the carrier certificate; likely real work (Wu vs SW presentation), not pure glue |
| N7 | `pin4_abutment` (E5, DEMOTED) | `PinPlusDischarge.lean:67` (def), inhabited `:69–75`; `hyp:smith_inflow_z16`, `constants.py:2655` | open, **off critical path** (2026-07-06 re-anchor) | PT + Adams-convergence geometric faithfulness. Finite side DONE: `col4_height_eq_four` (`PinPlusHeight4.lean:61`, axioms `[]`), `adamsAbutmentEquivZMod16` (`PinPlusAdamsAbutment.lean:90`, hypothesis-free), col3/col5 sparseness. |

**Top-line:** the E4 assembly is a **one-key arch**: every brick from surjectivity through the
eight doors is kernel-pure and finished; the ONLY thing between the current state and
`omega4PinPlusGM_equiv_zmod16` is N1, whose cheapest decomposition (KT §5) is
N1a + N1b + N1c + N2 — all E1/E2/E3-geometric, none E4-assembly. **No further assembly work
exists on the E4 side**; when any single door's key arrives, the capstone is a one-line
instantiation (recommend naming it `omega4PinPlusGM_equiv_zmod16` at that moment).

Atlas caveat: `lean/atlas_view.json` still ranks `hyp:smith_inflow_z16` #1
(frontier_impact 12) and `hyp:rokhlin_sigma_mod_16` #2 (11). Post-re-anchor the *required*
keystone is N1's KT decomposition; smith_inflow ranks #1 only because the Smith-LES transport is
what is wired (execution map §0 ⚠). `spinWu_even_datum` and `intLocalHomologyIso_datum` are
`proven` in the registry (`constants.py:3255,3153`) — atlas `unknowns` entries for them are stale-by-design
(excluded from the open frontier since `b6c729e3`).

## 3. Infrastructure finds (already-built-but-unwired)

| Find | State | Action |
|------|-------|--------|
| **F1**: `SpinWuDatumClosed.spinWuDatum_of_closed` (`SpinWuDatumClosed.lean:53`) vs `SixteenDvdOfOrientation.sixteen_dvd_latticeSig_of_orientationData` (`SixteenDvdOfOrientation.lean:85`) — both LEAF modules; the σ÷16 leg still took `D : SpinWuDatum …` as a binder one commit after it became a theorem; the cross-reference existed only in a docstring (the P6 anti-pattern). The two carriers agree definitionally (`intFundamentalClassOfIntOrientation (intOrientationOfData d) ≡ intFundamentalClassOfHomology d.fundClass`). | **unwired → CLOSED** | glue shipped: `SixteenDvdOfOrientationSpin.lean` (§4) |
| **F2**: `PinPlusFaithfulnessCardBridge.iso_iff_card_le_abutment` (`:110`) — the E5→E4 numeric door (genuine-carrier iso ⟺ `card ≤ card adamsAbutment` under `Finite`) | built, LEAF (no consumer) | correct as a door; consumes N1-equivalent key; nothing to glue |
| **F3**: `UnorientedThomCapstone` (`grade0_bounds_of_thom`, `omega4PinPlusGMTied_equiv_zmod16_of_thom`) | built, LEAF | it IS the newest E4 door (D8); capstone-in-waiting |
| **F4**: `SpinWuDatumClosed.interMatrix_even_of_closed` (`:64`) — evenness of the intersection matrix at general closed oriented spin M | built, consumer = none beyond its module | E2's evenness conjunct consumer-to-be (van-der-Blij leg already takes evenness through `SpinWuDatum` inside `sixteen_dvd_latticeSigInt`; no separate glue needed now) |
| **F5**: `SingularOpenDualityUnivBij` (extracted mod-2 univ (2,1)+(3,0) bijectivity, `825fa55a`) | wired (consumed by `SingularSixteenDvdLegInt`, `SingularOpenDualityUnivBijInt`) | none |
| **F6**: `hcoreG_intrinsicInt` (`SingularHcoreGDischargeInt.lean:22`) | wired (feeds `sixteen_dvd_latticeSigInt` PD-input-free, `0240e207`) | none |
| **F7**: `poincareDual4Mid_of_closed` / `poincareDual4Lo_of_closed` (`SingularPD4Instances.lean:104,194`) | widely wired (8+ consumers) | none — the exemplar this mission generalized from |

## 4. Glue shipped this pass

* **`lean/SKEFTHawking/SixteenDvdOfOrientationSpin.lean`** —
  `sixteen_dvd_latticeSig_of_orientation_spin`: the σ÷16 leg with the `SpinWuDatum` binder
  **eliminated** (closes F1). New leg contract at a plus-oriented closed charted spin 4-manifold:
  `d : IntOrientationData M` (N3) + `kron/hkron` (N4) + `B` (N5) + `hv2` (N6) + `htopo` (N2)
  ⟹ `16 ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B)`.
  `lean_verify`: axioms exactly `{propext, Classical.choice, Quot.sound}`. Rooted in
  `SKEFTHawking.lean`.

## 5. PDWindow vs PDWindow4 — reconciliation VERDICT

**`pdWindowP4` strictly subsumes `pdWindowP` by definition; BOTH towers are needed; no
duplication exists.** Ground truth from source:

* `SingularPDWindow.pdWindowP` (`SingularPDWindow.lean:39–51`) = the **3-conjunct** deg-4
  Bott–Tu induction predicate: `Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰`, all presented from ONE
  master cycle `zM`. Apex: `pdWindowP_univ` (`:490`).
* `SingularPDWindow4.pdWindowP4` (`SingularPDWindow4.lean:29–36`) is **literally defined as**
  `pdWindowP zM hzM W hW ∧ Bij D@(1,2)` — the same predicate extended by the fourth
  `(1,2)`-duality conjunct (`H¹_c → H₃`, at the `(0,1)` upper-engine presentation of the SAME
  `zM`). Apex: `pdWindowP4_univ` (`:382`).
* Same predicate family, not parallel towers: `pdWindowP4`'s base/∅/union/monotone lemmas are
  built ON the `pdWindowP` ones (e.g. `pdWindowP4_empty` at `:48` uses `pdWindowP_empty`), and
  its MV-step consumes the 3-conjunct `(2,1)`-window **cross-wise** (module docstring,
  `SingularPDWindow4.lean:8–14`) — so the 3-conjunct tower cannot be deleted into the 4-conjunct
  one without rebuilding the cross-feed.
* Distinct consumers: `pdWindowP_univ` feeds the extracted `SingularOpenDualityUnivBij`
  (mod-2 (2,1)+(3,0) apexes, → the integral σ÷16 leg); `pdWindowP4_univ` feeds
  `SingularPD4Instances` (`poincareDual4Mid_of_closed` needs the `(1,2)`-window for
  `capH12_injective_of_closed`, `SingularPD4Instances.lean:125–147`).

**Do NOT merge or refactor either tower.** (Per mission: verdict only; none needed anyway.)

## 6. E5 status snapshot (for completeness)

Finite/decidable side **DONE, kernel-pure**: `col4_height_eq_four` (axioms `[]`),
`adamsAbutmentEquivZMod16` (hypothesis-free), col3/col5 differential-vanishing. The residual
geometric-faithfulness node is N7 (`pin4_abutment` ≙ `smith_inflow_z16`), consumed only by the
demoted PinPlusDischarge §1–§5 forms and the CommonOrigin flagship tower
(`CommonOrigin.lean:77–254`), which live on the OLD thin `Omega4PinPlusBordism` substrate — not
the genuine tied carrier. Post-2026-07-06 re-anchor E5 is an **alternative** route to N1, not
the keystone; no E5 assembly work is on the critical path.

---
## Post-round-2 refresh (lead, same day — rounds 2/3 landings)

- **N6 RETIRED** (`71f1b9f4`): the hv2 seam is CLOSED — `PinPlusCertK → wuClass2 = 0 → spinWuDatum_of_certK →
  sixteen_dvd_latticeSig_of_orientation_certK`, with `v₁ = 0` DERIVED from orientation (new
  `BocksteinIntegralLift` engine; nothing frozen). Requires N3's `IntOrientation` (mathematically necessary).
- **N1a REFINED** (`a529f6c2`..`5e894244`): the σ-route layer is in-tree — `isHyperbolicForm_congr_iff`
  (M–H σ=0 characterization), `SpinSigmaPresentation`/`dataBordismGrp_equiv_int` (the
  `spin_bordism_iso_Z` consumer shape), KT Lemma 5.3's ⟸ DERIVED. Open inside N1a: **Freeze A
  `RealizesSphereProducts`** (Benedetti handle-trading) + **Freeze B `SphereProductBounds`** (round-3
  wt3 instantiating) + `hfwd`/`h2g` (5.3 forward; 2·K3 bounds) + the K3 witness.
- **N4 (round-3 wt2 porting)**: the absolute kron/hkron under freeness hypotheses — folds N4 into
  N5-adjacent data on landing.
- **N5 scoping verdict (lead)**: the leg's witness set = SPIN manifolds only (ℝP⁴ has no `IntOrientation`
  — its H²-torsion concern is MOOT for the leg; it enters via the mod-2/GM side instead). Concrete needs:
  S⁴ (H²=0, rank-0 `IntH2Basis` — trivial once H²(S⁴;ℤ)=0 is in-tree, which it is NOT yet), `n(S²×S²)`
  (H² free rank 2n — needs in-tree computation; pairs with Freeze-B work), K3 (rank 22 — the deep witness,
  needed for N1c's ÷32 and generation). NO general-M FG required anywhere on this path
  (`5qH-fg-ek-over-Z-blocked` respected).
- **No-go substrate**: registry at 7 (`FGDualityNoGo`, `SyntheticSmithNoGo`, `5qH-injectivity-routes-apex-equivalent` added this arm), `nogo_substrate_integrity` PASS.
