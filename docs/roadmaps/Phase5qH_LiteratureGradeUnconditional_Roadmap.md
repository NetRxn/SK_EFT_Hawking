# Phase 5q.H — Literature-grade unconditional `Ω₄^{Pin⁺} ≅ ℤ/16` (durable strategic tracker)

**RE-BASED 2026-07-13** (operator planning session) after the kernel-confirmed substrate soundness
finding. This file is the **durable-only** rewrite: objective, hard constraints, the landed substrate
verdict, wave-level work breakdown, source index, no-go fences, and gates. **It deliberately contains
NO route/carrier/keystone live status** — that lives in the notebook INDEX
(`docs/dev-loops/Phase5qH/LAB_NOTEBOOK_INDEX.md` FRONTIER) and the machine atlas frontier
(`/skeft-qa:frontier`). Per-line test for edits to this file: *"true in 30 turns?"* If it can go
stale, it does not belong here.

**History:** the five superseded generations of this file (2026-07-03 §0–§9 open plan → 07-04
Option-A GO + §10 → 07-04 §9.3 correction → 07-06 keystone re-anchor → 07-13 soundness banners) are
in git history (`git log --follow` this path). The retired execution map
(`docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md`, frozen 2026-07-13) holds the E1–E5 naming
cross-walk for reading old notebook entries. Continuation of
[Phase 5q.G](Phase5qG_GenuineUnconditional_Roadmap.md).

---

## 1. Objective (route-agnostic, unchanged)

The genuine, fully **UNCONDITIONAL** `Ω₄^{Pin⁺} ≅ ℤ/16`, formalized in Lean 4 on a **FAITHFUL**
carrier — ℤ/16 genuinely **computed** (injective + surjective, zero posits) — kernel-pure
(`{propext, Classical.choice, Quot.sound}`), no project-local `axiom` / `sorry` / `native_decide` /
`maxHeartbeats`.

**Option A is SETTLED (operator ruling 2026-07-04, unchanged by the re-base):** full unconditional
discharge is the only path; disclosed-form results are stepping stones, never the endpoint.

## 2. What "faithful carrier" means (the 2026-07-13 finding, generalized — LOAD-BEARING)

The substrate collapse (no-go `nonhausdorff-bordism-collapse`, kernel-checked) plus the 07-13
carrier-linkage audit established that faithfulness has **three independent legs**. A carrier
missing ANY leg produces true-but-vacuous completeness statements:

1. **T2 on the bordism manifold `W`** (and certified on the closed carriers). Without it the
   bug-eyed interval gives every closed `s` an odd-boundary bordism and the relation collapses
   (`BordismGrp X 0 I` trivial, `[ℝP⁴] = 0`, the tied carrier = its grade). Kernel-proven; the
   generic repair layer exists (`T2TangentialBordism.lean`: `IsT2DataBordant`, `T2DataBordismGrp`).
2. **Smooth category, `k ≥ 1`** (flagship instantiation at `k = ∞`; `C¹ ⟹` unique smooth
   structure by Whitney, so `k ≥ 1` suffices mathematically). At `k = 0` the honest group is
   topological Pin⁺ bordism `≅ ℤ/2 ⊕ ℤ/8` (Kirby–Siebenmann; E₈), i.e. the WRONG group. This is
   the (2026-07-03) §9.2 decision, now promoted to a hard constraint: **the C⁰ fork must never be
   silently conflated with the ℤ/16 target.**
3. **Structure-extension `Bor` + computed invariant.** The structured relation's witness type
   `Bor b σ τ` must require a *genuine structure on `W` restricting to the ends* — NOT numerical
   bookkeeping. (The retired tied instance had `Bor := PLift (σ.grade16 = τ.grade16)` and carried
   `grade16` as a field: grade-equality bookkeeping over unoriented bordism, in which only the
   w₁⁴-parity bit was geometric. On such a carrier even a true `≃+ ZMod 16` is not the
   literature's theorem.) The ℤ/16 invariant must be a **theorem computed from the structure**
   (ABK/Brown of the characteristic-surface enhancement), never a carried tag.

**The generic frameworks are NOT implicated:** `BordismGroup.lean` (cylinders, disjoint unions,
doubling, group laws) and the `TangentialData` interface (whose `Bor` contract is exactly leg 3)
are sound and replay on the refined relation. The infidelity lived in the *instance*.

## 3. Hard constraints (every wave, every worker)

- **Kernel-purity bar** as in §1. **No new project-local `axiom` without explicit operator
  sign-off** (`feedback_axiom_sign_off_policy`). A genuinely-hard geometric input is carried as
  ONE named, tracked, disclosed `Prop` with a discharge plan — surfaced in every statement that
  consumes it until discharged.
- **The three faithfulness legs (§2)** on any carrier whose completeness/bounding statements are
  to be consumed downstream.
- **🆕 VACUITY-ATTACK GATE (encodes the 07-13 lesson):** before any completeness/bounding Prop
  (`hbound`-class: injectivity, boundedness, "grade-0 ⟹ bounds") is consumed or celebrated, a
  dedicated fresh-context attempt to **discharge it with zero geometric input** (bookkeeping,
  degenerate witnesses, relation pathologies) must FAIL. If the attack succeeds, the statement is
  too weak — restate; encode the exploit as a kernel no-go where checkable. This is a standing
  wave-gate alongside the adversarial review.
- **Genuine `revStr`:** the faithful instance must carry a non-trivial structure reversal —
  kernel no-gos `dataBordism_two_torsion_of_revStr_trivial` / `genuine-gm-carrier-eight-torsion`
  prove a reversal-trivial (or 8-torsion) carrier cannot host order-16 elements.
- **Continue-vs-stop rule (5q.G, locked):** legitimate stops are ONLY a kernel-checked no-go or a
  genuine user-only decision. "Absent from Mathlib / no foothold / multi-week" are NOT stops —
  absence is the work (`feedback_ignore_pm_estimates`).
- **Anti-spiral rules:** no frozen CURRENT-STATE blocks in durable docs; live state recomputed
  from git + notebook FRONTIER; read the ⛔ register (`SETTLED_FORKS.md` + negative frontier)
  before any impossibility reasoning; never re-derive a settled fork.
- **Preemptive-strengthening checklist** (CLAUDE.md) before every theorem statement;
  **search-before-build** (`lean_local_search` + namespace grep) before any new lemma.

## 4. The substrate verdict (LANDED — operator decision, 2026-07-13)

**Layered rebuild** (not full clean-slate, not minimal patch):

| Layer | Verdict |
|---|---|
| `BordismGroup.lean` relation machinery + `TangentialData` framework + `T2TangentialBordism` generic refinement | **KEEP** (sound; group laws replay on the refined relation) |
| Relation-free base: E1 integral topology (cohomology→cup→cap→Kronecker→σ÷16, `[M]`/orientation), K3 lattice, Brown/ABK/Rokhlin algebra, Smith double-cover tower, D³/S²×D³ atlases (k-generic) | **KEEP** (genuine, zero refs to the degenerate relation) |
| The Pin⁺ instance (retired: `pinPlusGMTiedData` grade-as-data) | **REBUILD**: `Mfd s` = genuine Pin⁺/GM structure as geometric data; `Bor` = structure on `W` restricting to the ends; ABK **computed** from the structure; genuine `revStr` |
| ℝP⁴ witness (Cω — smooth at every `k`, `rp4SM_k`) | **DONE (2026-07-21):** surjectivity onto ℤ/8 on the honest smooth carrier is unconditional (`charPairBrown_surjective_smooth`) |
| Keystone completeness statement | **RESTATE** on the rebuilt instance (absorbs the containment audit of the vacated bricks) |

**Regularity (leg 2) — DISCHARGED 2026-07-21, via route (b) = re-declaration (NOT transport).** The KT
provider is now `k`-generic (`PinPlusKTAssemblyResiduals.residualProvK`); the assembly of record
instantiates at `k = ⊤` (`kt_equiv_zmod16_of_residuals_smooth`), carrying the same open binders as the
`k = 0` form, and every `k = 0` statement is kept verbatim as a corollary (`residualProv = residualProvK 0`).
Verified at merge: at `k = ⊤` the carrier's `StrMfd` genuinely requires `IsManifold (𝓡 4) ⊤` (instance
synthesizes at `⊤`, fails on the `k = 0` control) — the `k = 0` binder was *free*
(`PinPlusRegularityFence.isManifoldZero_free`), which is the whole reason the lift was needed. A generic
`k=0 → k≥1` transport is kernel-refuted — see §9; never attempt one. **The one residual `C⁰`-tied input is
a smooth handle attachment for the surgery trace** (`SurgeryFoundation.SmoothSurgeryChartDatum.ofC0` sets
`k := 0`; `SingularSurgeryChartsConcrete.ambientTraceBordism_concrete` builds the boundary embedding's
"smoothness" as continuity) — Mathlib-absent, and on the completeness (W-D / KRS) leg's critical path
regardless, so it is not new work.

**Blast radius of the collapse (07-13 linkage audit, conclusive):** the σ-route door + L3
(`omega4PinPlusGMTied_equiv_zmod16_*`) are fully vacated (definitionally the collapsed carrier);
L2's substance (surjectivity) survives and is already re-proven on the T2 carrier
(`abkGMTied16T2_surjective`); Freeze-B's geometric witness (`S²×D³`, Hausdorff, k-generic)
survives and needs only restating.

## 5. Work breakdown (wave-level, route-agnostic — sequencing/status live in the notebook)

- **W-A — the faithful instance.** Define the genuine Pin⁺/GM structure type + the
  structure-extension `Bor` over the T2 relation (per §2 leg 3, §3 `revStr`). **The definition
  itself gates through fresh-context adversarial review + the vacuity attack BEFORE anything is
  built on it.** Absorbs the honest restatement of vacated bricks (containment task).
- **W-B — smooth witnesses + surjectivity.** ℝP⁴ smooth atlas (+ its structure); the even-grade
  realizations; surjectivity of the computed invariant on the honest carrier.
- **W-C — the computed invariant + bordism invariance.** ABK/Brown computed from the
  characteristic-surface enhancement (consumes the in-tree Brown/ABK algebra + E1 topology);
  invariance along structured T2 bordisms; additivity. Conventions: §7.
- **W-D — completeness (the summit).** `invariant = 0 ⟹ bounds` on the faithful carrier.
  Route selection is a **live-layer decision** (§6) — both candidate architectures bottom out in
  Rokhlin-content + `Ω₄^{Spin} ≅ ℤ`-class deep inputs, so W-A/B/C and the Rokhlin leg are on the
  critical path regardless.
- **W-E — deep-input discharge.** The Rokhlin-content leg (`hyp:rokhlin_sigma_mod_16`; the σ÷16
  lattice leg + E2 assembly survive and feed it) and whichever `Ω₄^{Spin} ≅ ℤ`-class input the
  selected route requires — each carried as a named tracked Prop until discharged in-tree.
- **W-F — capstone + integration.** The literature-grade statement at the `k = ∞` instantiation;
  Ω₅/`CommonOrigin.sixteen_convergence_*` recast; retired carriers documented as stepping stones;
  bundle freshness pass (`LATE_PHASE6_ABSORPTION_PROTOCOL` if any bundle drafted against old forms).

**Interface caveat (durable scope fence):** the target form is the GM characteristic-surface
package (Kirby–Taylor-equivalent), NOT principal-Pin⁺(4)-bundle structures; the bundle-level
equivalence is a possible 5q.I, recorded not claimed.

## 6. Completeness-leg route candidates (named, NOT pinned — selection = notebook FRONTIER)

Two live architectures, both primary-source-grounded in `Lit-Search/Phase-5qH/`:

- **KT §5 direct** (`KT_LMS_Section5_completeness_proof_extracted.md`, primary PDF in-corpus):
  the extension `0 → ℤ/2 → Ω₄^{Pin⁺} → ℤ/8 → 0` + the ψ non-split witness; four named geometric
  inputs (Ω₄^{Spin} ≅ ℤ + Ω₄^{Pin⁻} = 0; Lemma 5.3's ÷32 [Rokhlin-content]; the μ/α invariants
  for ψ; the `[∩w₁²]` map to Ω₂^{Pin⁻} ≅ ℤ/8 [in-tree]); **no external stable ℤ/16 input**.
- **Smith-LES** (`ABK_injectivity_routes_lemma_DAG_20260703.md`): three explicit geometric
  constructions + ONE external stable input (`smith_inflow_z16`: Ω₆^{Pin⁻} ≅ ℤ/16-class — no
  published elimination).

Route-decision provenance, for the record: the 07-03 "BINDING Smith-LES" adoption predated the
KT §5 fetch (07-04) and was already superseded by the 07-06 keystone re-anchor toward the KT
geometric close. As of 2026-07-13 the operator-confirmed posture is **live-layer selection with a
KT-lean read**. Do not re-pin a route in this file.

## 7. Conventions locked (durable statement shapes — 2026-07-03 DR, unchanged)

β-sign: **the project's operative convention is GL/FK** (`σ − F·F = +2β mod 16` — what the shipped
kernel-pure `GuillouMarinBridge.GMrelation`/`doubleBrown` encode; W-A gate reconciliation 2026-07-13,
review finding M-4). KT's convention is the opposite (`2β = F·F − σ`, i.e. `β ↔ −β`); statements
consuming the congruence carry the KT-translation note in their docstrings. ℝP⁴'s two Pin⁺
structures = ±1 ∈ ℤ/16 (exchanged by twisting with the orientation line). ℝP²'s two enhancements:
generator ↦ 1, 3 ∈ ℤ/4 (β = ±1 ∈ ℤ/8). Enhancement axiom: `q(x+y) = q(x) + q(y) + 2(x·y)`,
`2· : ℤ/2 ↪ ℤ/4`. The GM surface package computes the invariant **mod 8 only** (the {0,8} kernel
is invisible to (Σ,q) — fake-ℝP⁴ 9-vs-1); the odd/16 content lives at the extension/architecture
level. Known trap: the Smith-paper Fig. 3(g) pin± label swap.

## 8. Verified-source index (`Lit-Search/Phase-5qH/` — read directly, never via summary)

`KirbyTaylor_PinStructures_LMS151.pdf` (primary, fetched 07-04) + `KT_LMS_Section5_completeness_
proof_extracted.md` · `ABK_injectivity_routes_lemma_DAG_20260703.md` ·
`GM_structure_ABK_invariant_normalizations_20260703.md` ·
`Rokhlin_16_sigma_elementary_blueprint_20260703.md` · `Omega4Spin_Z_formalization_route_20260706.md`
· `FG_via_PD_duality_forcing_verdict_20260712.md`. External primaries verified 07-04
(reconciliation audit §2): Taylor `0802.0111`, Klug `2011.12418`, DDK⁺ `2405.04649`,
HKT `1910.14039`, `2406.08237`. Outstanding fetch: Matsumoto's elementary Rokhlin proof
(À la recherche volume).

## 9. Kernel no-go fences (never re-derive; machine-enforced)

Registry = `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`) → generated
`lean/SKEFTHawking/KernelNoGos.lean` (compile-time fence) → `validate.py --check
nogo_substrate_integrity`; prose register = `docs/dev-loops/SETTLED_FORKS.md`. Binding on this
phase's design space: **`nonhausdorff-bordism-collapse`** (T2-less relation collapses — leg 1);
**`dataBordism_two_torsion_of_revStr_trivial`** + **`genuine-gm-carrier-eight-torsion`**
(reversal-trivial/8-torsion carriers can't be ℤ/16); **`synthetic-grade-ker-bot-nogo`** (free
grade has no `ker = ⊥`); **`lattice_arf_bridge_refuted`** (σ/8 ≢ Arf mod 2 — Rokhlin mod-16 is
irreducibly geometric); **`k0-to-k1-transport-refuted`** (no generic `C⁰→C¹` manifold transport exists —
at `k = 0` the `IsManifold` binder is FREE, so a smooth-category result must be re-declared `k`-generically,
never lifted from `k = 0`; the regularity leg is discharged that way — §4. SCOPE, do not overstate: this
separates OBJECT CLASSES, not bordism groups, and is NOT a refutation of the KT ℤ/16 mathematics). Spectral
machinery (β-fork) remains a policy fence in `SETTLED_FORKS.md`:
revisit only on substrate shift (coupled Mathlib pin-set bump per
`feedback-mathlib-physlib-bump-coupled-authorization`).

## 10. Gates & wave mechanics (the DONE definition — inherited 5q.G discipline)

Per wave: fresh-context adversarial review (0-BLOCKER/0-MAJOR) **+ the §3 vacuity attack on any
new completeness Prop** → merge to LOCAL main → trusted rebuild (`rm -rf .lake/build && lake build
SKEFTHawking.ExtractDeps` exit 0) → `validate.py` N/N → counts/inventory/INDEX sync → **never
push**. Venue: worktree slots via `/skeft-qa:reset-slot` + `lean-worker` fan-out when the DAG
genuinely branches (workers get the §9 no-gos named in their briefs); solo MCP-first otherwise.
Aristotle: algebra-only candidates, batch at ≥3, operator first & last call. **Phase DONE** = W-F
merged, all tracked Props discharged, zero posits, full gate green, fresh adversarial review PASS.

## 11. Where live state lives (division of labor — the process fix)

| Content | Home |
|---|---|
| Route/carrier/keystone selection, brick-by-brick status, frontier | notebook `LAB_NOTEBOOK_INDEX.md` (FRONTIER + DECISIONS) + shards |
| Machine truth of open/settled nodes | atlas (`/skeft-qa:frontier`, both fronts) |
| Kernel-checked impossibilities | `KERNEL_NOGO_REGISTRY` → `KernelNoGos.lean` (+ `SETTLED_FORKS.md` prose) |
| Objective, constraints, verdicts, gates, sources | **this file (durable only)** |

Editing rule for this file: additions must pass *"true in 30 turns?"*; status/route content goes to
the notebook. The exec map is retired — do not resurrect it.
