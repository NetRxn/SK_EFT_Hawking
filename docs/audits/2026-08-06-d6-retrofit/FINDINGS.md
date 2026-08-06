# D6 apex retrofit — and what the closure found on the way

**Date:** 2026-08-06 · First bundle retrofitted under ADR-010 §D5a.
**Context reviewed before declaring anything:** `papers/D6/paper_draft.tex` (1 103 lines, in full),
`bundle_metadata.json`, `source_manifest.md`, `docs/PAPER_DRAFT_MAPPING.md` (D6 + D9 rows),
`papers/D9/paper_draft.tex` structure, the four cited `lean/SKEFTHawking/FaultTolerance/*` modules,
the whole `FaultTolerance` tree, and the git history of both drafts.

---

## 1. What was declared

**11 apexes → 51 declarations across 4 modules, depth 3, zero private truncations.**

One per substantive claim the abstract makes, plus the falsifiers it explicitly claims ("each
kernel-verified achievement is paired with a falsifier that fails the corresponding baseline"):

| § | apexes |
|---|---|
| §3 gauging-QEC (6v.1) | `wave_6v_1_substantive_closure`, `williamsonYoder_beats_quadratic_for_W_ge_two` |
| §4 APM-LDPC (6v.5/6v.5b) | `wave_6v_5_substantive_closure`, `apmLdpc_quEraHarvard_not_achievable_at_one_half_noise`, `apmLdpc_hashing_bound_at_zero_noise` |
| §5 Shor T-counts (6v.2) | `shor_ecc256_tgate_count_le`, `shor_ecc256_falls_within_megagate_envelope_at_1G`, `wave_6v_2_substantive_closure` |
| §6 W-state QFT (6v.6/6v.6b) | `n_qubit_w_state_basis_strictly_smaller_than_full_hilbert`, `wState_basis_isCyclotomic_at_QCyc_sizes`, `wave_6v_6_substantive_closure` |

**The `wave_*_substantive_closure` theorems do NOT subsume their sections** — checked, not assumed.
Most sharply, `wave_6v_2_substantive_closure` does **not** cover `shor_ecc256_tgate_count_le`, which
is §5's headline. Declaring only the wave-closure theorems, the obvious shortcut, would have left
D6's own headline result outside its substrate.

§2 (Solovay–Kitaev) gets **no apex, correctly**: it names zero Lean and says so — D6 *consumes*
D8's primitive. The closure agrees, returning 0 for that section.

---

## 2. ⚠️ The finding: §5.4 is D9's paper, sitting inside D6

D6 §5.4 (`sec:wstate:envelope`, lines 504–991 — **44 % of the draft**) presents Phases 6AA–6AK: the
fidelity envelope, BBPSSW/DEJMPS, BB84, teleportation, the mixed-state/channel layer, trace norm,
Uhlmann fidelity, diamond distance, the Watrous Choi-SDP, negativity/PPT, distillation bounds.

`docs/PAPER_DRAFT_MAPPING.md:106` charters **D9** — *"Kernel-Verified Quantum-Network and
Device-Characterization Certification Substrate"*, authorized **2026-06-10** — as
*"consolidat[ing] Phases 6AA–6AL"*: the diamond-norm program, the negativity ladder, the network
envelopes, the device-characterization family. That is §5.4's content, item for item.

### The measurements

| | |
|---|---|
| theorems D6 names, whole draft | 147 |
| — in the four headline sections | **28** |
| — in §5.4 | **119** |
| **D6 ∩ D9 (directly named)** | **78** |
| — of that overlap, from §5.4 | **78** |
| — of that overlap, from §2–§6 | **0** |
| §5.4 theorems D9 does not name | 41 — **all 41 in `SKEFTHawking.QuantumNetwork.*`** |

**Every theorem D6 and D9 share is in §5.4. The four headline sections overlap D9 in nothing.**

This re-frames §M4(a). The 78-theorem overlap — the number the D6/D9 merge hypothesis rests on — is
not a subject blur between "FT-QC substrate" and "network certification". **D6 and D9 do not
overlap. §5.4 and D9 overlap, because §5.4 is D9's content.** A merge would have been the wrong
remedy for a correctly-measured symptom.

### Substrate mass, per section

| section | seeds | closure | modules |
|---|---|---|---|
| §2 Solovay–Kitaev | 0 | 0 | 0 |
| §3 gauging-QEC | 5 | 10 | 1 |
| §4 APM-LDPC | 11 | 23 | 1 |
| §5 Shor T-counts | 5 | 10 | 1 |
| §6 W-state QFT | 7 | 11 | 1 |
| **§5.4 network envelope** | **119** | **682** | **70** |

**93 % of D6's substrate hangs off a subsection of §6.** The bundle's title and abstract describe
the other 7 %.

### How it happened — dated, from git

- **2026-06-01** `4c9ebba5` *"docs(D6 §6): absorb Phase 6AA verified-network-fidelity envelope into
  the W-state section"*
- **2026-06-10** `4c17ece5` *"D9 initial draft (sourceless synthesis): QN + device-characterization
  certification substrate"*

The envelope was absorbed into the nearest available bundle **nine days before a home for it
existed**. When D9 was authorized for exactly that corpus, D6's copy was never removed — and kept
growing, through Phases 6AF, 6AG, 6AI, 6AJ and 6AK.

This is the late-phase-absorption pathology in a dated, specific instance, and it is precisely what
`LATE_PHASE6_ABSORPTION_PROTOCOL.md` exists to prevent.

---

## 3. ⚠️ The constructive half: D6's real deep substrate is un-homed

`SKEFTHawking.FaultTolerance` holds **16 modules / 241 author-written declarations**. D6's draft
reaches **4 modules / 63**. Two more go to I3 as methodology examples. **Ten modules / 143
declarations reach no bundle at all:**

| module | decls | what it is |
|---|---|---|
| `AGP.Threshold` | 8 | the **Aliferis–Gottesman–Preskill threshold theorem** for Steane, with `steaneAGPThreshold > 2.73e-5` |
| `Counting` | 16 | AGP-rigorous Steane malignant-pair counts (`A_CNOT = 35 235`, PDF-pinned) with `≤ choose 2` well-formedness |
| `NoiseModelMT` | 24 | Bernoulli-product / local-stochastic noise, joint-failure bounds |
| `SteaneCode` | 15 | the [[7,1,3]] code: distance-three, single-logical |
| `Basic` | 34 | Pauli / circuit-op algebra |
| `Malignant` | 13 | malignant-pair attestation |
| `NoiseModel` | 12 | local-stochastic noise model |
| `Chernoff` | 9 | pair-failure bounds, AGP recursion step |
| `Concatenation` | 6 | AGP level sequence, below-threshold behaviour |
| `DoubleExp` | 3 | `agp_double_exp_bound_unconditional` — double-exponential suppression |

That is the canonical fault-tolerance threshold chain — threshold theorem, concatenation,
double-exponential suppression, malignant-pair counting, noise models, the Steane code — **more
than twice the substrate D6 currently cites, and exactly what a paper titled "Formally Verified
Fault-Tolerant Quantum Computation Substrate" should be about.**

So the reading is *not* "D6 is thin, demote it". It is: **D6 is holding someone else's paper and
not holding its own.**

---

## 4. What this implies (recommendation, with the action separated)

1. **§5.4 → a cross-reference to D9.** The idiom already exists in this very draft: §2 is a
   15-line pointer saying D8 owns the SK primitive and D6 consumes it. §5.4 should have the same
   shape. The 41 theorems D9's prose does not name are in D9's own namespace and will enter D9's
   substrate automatically once D9 declares apexes — which is the closure design's entire point.
2. **Home the AGP threshold chain into D6.** That is a content lift, and the remediation principle
   is to build the claim true rather than narrow it.
3. Only then is D6's tier answerable. As drafted-minus-§5.4 it is **51 declarations / 4 modules /
   depth 3** — letter-shaped. With the threshold chain it is a genuine Tier-1 deep paper.

**Declared in this pass: the 11 apexes only.** Items 1–3 change the manuscript and are tracked
separately; the apexes above describe what D6 claims *today*, which is the honest starting point.

`UNDECLARED_APEX_CEILING` 21 → 20 in the same commit.
