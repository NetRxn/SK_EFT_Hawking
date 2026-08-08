# D4 apex retrofit — the D4→D8 boundary made concrete, and a D6 absorption that did not happen

**Date:** 2026-08-07 · Eleventh bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D4/paper_draft.tex`
(1,584 lines, every line, including §9 — which was appended after the original §1–§8 synthesis and
carries the Solovay–Kitaev content — and the commented stubs after the bibliography),
`bundle_metadata.json`, `append_log.json`, and an underscore-aware scan of all 21 drafts for the
FKLW headline names.

---

## 1. What was declared

**62 apexes → 620 declarations across 43 modules, depth 13, 82 private truncations.**

⚠️ **As first declared this was 66 apexes → 753 declarations / 61 modules / 90 truncations.** Four
`GenericSU2` apexes were **reassigned to D8** at D8's retrofit later the same day (§3), and the
closure fell accordingly. The original figures are recorded here because the *drop* is the
evidence: those four were pulling D8's entire `SU(d)` tree into D4.

| § | thread | apexes |
|---|---|---|
| §2 | Uq(sl2)/Uq(sl3) quantum groups | 5 |
| §3 | Ising MTC: six hexagons, four ribbons, knot invariants | 18 |
| §4 | Drinfeld centre: toric-code anchor + non-abelian D(S3) | 7 |
| §5 | WRT TQFT | 2 |
| §6 | doublon-SWAP substrate | 2 |
| §7 | Hayden–Preskill QEC on the horizon MTC | 11 |
| §8 | RT / Casini–Huerta knife-edge | 3 |
| §9 | Fibonacci density + quantitative Solovay–Kitaev | 14 (was 18) |

⚠️ **90 truncated walks is the highest measured.** Any statement about D4's substrate size is a
lower bound, and the figure travels with the number by design.

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Topological-quantum-computation researchers and the quantum-information end of formal methods; secondarily the holography community, for §§7–8. |
| **Venue** | Comm. Math. Phys. \| PRX Quantum, per the metadata. CMP fits §§2–5 (quantum groups, MTC, WRT); PRX Quantum fits §§7–9. **That split is itself a signal about the container.** |
| **The claim only this container can make** | **"One MTC, four faces"** — that a single SU(2)_k Chern–Simons MTC at the horizon simultaneously supplies the Drinfeld-centre anchor for D2's anomaly classification, the WRT partition function behind D3's entropy, the Hayden–Preskill code structure, and the RT/Casini–Huerta knife-edge. No sibling holds more than one face. |
| **Substrate** | 43 modules, 620 declarations, depth 13 (after the §3 reassignment): `Uqsl2*`, `Uqsl3*`, `IsingBraiding`, `QCyc16`, `FigureEightKnot`, `DrinfeldDouble*`, `S3CenterAnyons`, `WRTInvariant`, `WRTComputation`, `FermiHubbardDimer`, `QECHolographyBridge`, `RTCasiniHuertaBounds`, plus the **Fibonacci half** of the `FKLW/` tree (F.21 density, the eight-module Phase-6t SK pipeline, Path A). The `GenericSU2`/`SU(d)` layer is **D8's** — see §3. |
| **Honest size vs charter** | 1,584 lines against ~40pp. Closer to charter than most, and §9 is why: it was authored later and is the densest section in the bundle. |
| **Boundary failure?** | ⚠️ **Yes, in both directions, and they are different problems.** *Inbound:* §§7–8 consume D3's `H_HorizonBoundaryCondition` — 22 shared declarations, 17 in `BHEntropyMicroscopic`. D4's own §8 says D3 §7's falsifier "reads off" D4 §8's knife-edge, so the dependency is mutual and acknowledged. *Outbound:* §9's `GenericSU2` layer shipped **D8's chartered content**; ✅ resolved by reassignment at D8's retrofit (§3), so this direction is now closed. |

---

## 2. The closure

| pair | shared | reading |
|---|---|---|
| **D4 ∩ F** | **73** | `QCyc16` 19, `BHEntropyMicroscopic` 17, `FigureEightKnot` 16. F's §7 "one MTC, four faces" is D4's, as F says. |
| **D4 ∩ D3** | **22** | `BHEntropyMicroscopic` 17, `QECHolographyBridge` 5 — the horizon-MTC cross-bridge, mutual and acknowledged in both drafts. |
| **D4 ∩ D2** | 3 | All `PauliMatrices`. ⚠️ **Not** the Drinfeld-centre bridge both drafts describe: D2 §3.4 anchors on the toric code, D4 §4 ships it, and their *declared* closures share none of it. |
| **D4 ∩ D12** | 3 | Also `PauliMatrices`. Infrastructure; decides nothing. |
| **D4 ∩ D6** | **0** | See §3. |
| D4 ∩ D1, D9, D10, D11, L2 | **0** | |

---

## 3. ⚠️ ADR-010 §D4 evidence: the D4→D8 boundary, in concrete form

**D4 §9 ships the complete quantitative Solovay–Kitaev substrate**: F.21 density
(`fibonacci_density_F21_unconditional`), the Dawson–Nielsen length bound, the eight-module
Phase-6t `FKLW/` pipeline, and the Path-A constructive compiler across all three ε-regimes.

**D8's charter is "kernel-verified universal quantum gate compilation; alphabet-agnostic
Solovay–Kitaev across SU(d)."** That is the `FKLW/GenericSU2` layer — and D4's §9 names it.

Measured with an underscore-aware scan over all 21 drafts:

| theorem | named by |
|---|---|
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` | **D4 only** |
| `fibonacci_density_F21_unconditional` | **D4 only** |
| `skLengthExponent` | **D4 only** |
| `…quantitative_cliffordT_strict_constructive_tight_unconditional` | **D4 *and* D8** |

**Two drafts name the same theorem as their own substrate.** D4's §9 lists the Clifford+T and
trapped-ion variants among the content it ships; D8 is chartered on exactly that generalisation.
This is the D4→D8 question stated concretely, and it is now measurable from D4's side. **Not
decided here** — D8 is undeclared, and the disposition is the operator's under ADR-010 C5.

✅ **RESOLVED 2026-08-07 at D8's retrofit, on both drafts' own instructions.** D8 cedes Fibonacci
to D4 explicitly, twice (*"its universality is the subject of a companion bundle"*); D4 named the
Clifford+T/trapped-ion theorems only in a module list while D8 builds §§2–3 on them. **The four
`GenericSU2` apexes were removed from D4 and declared under D8.** The closure corroborates it
independently: D4 fell **753 → 620** declarations and **61 → 43** modules on their removal — they
were pulling D8's entire `GenericSU2`/`SU(d)` tree in. `D8 ∩ D4 = 280` remains, the shared
Lie-algebraic core, which is what an "instantiate, don't re-derive" substrate should look like.
Full working: `docs/audits/2026-08-07-d8-retrofit/FINDINGS.md` §2.

### And a D6 absorption that is not in D6's substrate

F §7's D6 description lists, as absorption item (ii), *"the Phase 6t quantitative Solovay–Kitaev
tight-ε headline retroactively absorbed as the canonical universal-compilation primitive."*

**D6 declares no Solovay–Kitaev apex.** Its eleven apexes are gauging-QEC, APM-LDPC, Shor T-counts
and W-state QFT. **`D4 ∩ D6 = 0`** — the two bundles share no declaration at all.

✅ **Corrected at D8's retrofit by D8's own text:** D8 says the sibling FT bundle *"consumes the
quantitative Solovay–Kitaev **developed here**"* — so the primitive F attributes to D6 is **D8's**,
not D4's. And `D8 ∩ D6 = 0` as well, so **D6's declared substrate contains neither**. F's absorption
claim is unbacked from both directions. Recorded in
`docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md`.

---

## 4. What D4 gets right — and it sets the disclosure bar for definitional encodings

D4 is the only draft measured so far that **labels a definitional encoding as one, in the prose,
at the point of use**:

> *"We **define** `WRTInvariant.wrtS2xS1` as `C.n` (the rank) directly … the companion theorem
> `wrt_S2xS1_eq_rank` is a definitional sanity-check (`rfl` on the definitional unfolding), **not
> a proof of the Verlinde-formula chain**."*

and again for `wrt_S3_formula` (*"encoding the standard Kirby-colour normalisation rather than
proving Kirby-move invariance from first principles"*).

**This is exactly the disclosure D10 §4.2–§4.3 does not give** for its Hohenberg–Kohn and
Levy–Lieb theorems (TODO-D12). Same structural situation — a theorem whose content sits in a
definition — and opposite handling. **D4's sentence is the template TODO-D12's fix should copy.**

Also honest, each checked against the Lean:

- **The doublon-SWAP Berry-phase layer is explicitly deferred** in the module (T13–T15) and said
  to be deferred in the paper, twice, including in "What this paper is not".
- **`H_HorizonBoundaryCondition`'s five fields are itemised**, with the note that two former
  `True` placeholders became real fields at the Wave-8 hardening — and the bundle is shown
  **satisfiable** (`fibonacci_horizon_satisfies_H_HorizonBoundaryCondition`), which is what stops
  a five-field Prop from being vacuous.
- **`native_decide` is disclosed at both figure-eight theorems.** True — both carry the
  `._native.native_decide` marker.
- **The loose constants are flagged as loose**: `C = 1000` against Dawson–Nielsen's asymptotic
  `C ≤ 4`, and the BCH constant 320 "loose by Dawson–Nielsen's own analysis".
- **The primacy claim is conservatively formed** — scoped to "instantiated for the Fibonacci-anyon
  braid representation in SU(2)" and stated to survive a concurrent generic-SU(2) announcement.

---

## 5. Also observed

- **Three more empty section stubs** after the bibliography (*SymTFT audit substrate*,
  *Lindbladian S-matrix axiomatization NO-GO*, *ETH-α productive-value refutation tableau*).
  TODO-D14 now spans **four** bundles.
- **The Drinfeld-centre bridge D2↔D4 is prose-only at declaration level.** Both drafts describe
  D2 §3.4 consuming D4's toric-code anchor; their declared closures share only `PauliMatrices`.
  Same shape as TODO-D16's Sakharov case — a described bridge without a shared declaration —
  though here the fix may simply be that D2's apex list omits the anchor.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D4/bundle_metadata.json` | `apex_theorems` added — 66 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 11 → 10 |
| **later, at D8's retrofit** | 4 apexes reassigned D4 → D8; closure 753 → 620, modules 61 → 43 |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | D4→D8 row upgraded from *not decided* to *evidence recorded, still not decided* |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D12 gains D4's sentence as its fix template; TODO-D14 → four bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V29 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 433 apexes across 11 bundles.
