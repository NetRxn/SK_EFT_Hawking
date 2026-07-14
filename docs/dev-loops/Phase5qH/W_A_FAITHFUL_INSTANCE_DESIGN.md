# W-A — The faithful Pin⁺ instance: design note (v4 — GATE PASSED, statement shapes FROZEN)

> STATUS: v1 → fidelity review PASS-WITH-CORRECTIONS (0B/4M/3m → v2) → Fable attack round 1: FAIL
> (2 kernel no-gos encoded: `comp-twist-doubling-incompatible`, `membrane-level-nonhausdorff-collapse`)
> → v3 redesign → **Fable re-gate round 2: PASS-WITH-AMENDMENTS** (architecture survived all six
> vectors; 1 kernel-checked precision exploit → no-go `taylor-leg-end-convention-trap`,
> `PinPlusTaylorConventionNoGo.lean`; amendments A-1…A-7 ALL APPLIED below, ▲-marked) → **v4 = the
> FROZEN definition. The Lean build is OPEN** (tower slices + the instance structure).
> Gitignored working doc; durable content moves into the Lean module docstrings as built.
>
> Re-gate highlights (recorded): the K3/{0,8} exploit now genuinely REDUCES to the honest Rokhlin
> ÷32 content (kernel ≅ ℤ/2 exactly); Brown/abk8 invariance is FORCED under the A-1 Taylor form
> (Lagrangian + Gauss factorization, in-tree `brown_orthSum`); all 12 ops hand-verified to
> instantiate; both round-1 no-gos genuinely evaded.

## 0. Changelog v2 → v3 (the amendment spec, applied)

- **A4 — `comp` DROPPED.** The H¹-coordinate + `+w₁`-twist is kernel-proven jointly uninstantiable
  with the op interface (negBor/doubling forces end-comps equal; cylBor kills the uniform twist),
  and its coherence anchor is unstateable in-substrate (basepoint problem → free-field ghosts).
  The odd-bit content lives where KT §5 puts it: the w₁-dual 3-manifold `V` and the ψ/μ invariants —
  **W-D assembly inputs, not carrier fields.** `revStr` = enhancement negation alone (non-trivial on
  ℝP⁴: `q(gen) : 1 ↔ 3`; β ∈ {0,4} on the oriented sector matches its genuine 2-torsion).
- **A1 — per-datum certificates.** EVERY manifold-typed datum (Σ, and Q inside `Bor`) carries its own
  `T2Space` + `CompactSpace` + charted structure (no-go `membrane-level-nonhausdorff-collapse`: the
  bug-eyed collapse is dimension-generic; the W-level fence does not propagate). Duality/Taylor legs
  are stated against CANONICAL fundamental classes, never a chosen homology class.
- **A2 — W-admissibility in `Bor`.** The relation requires the bordism `W` itself Pin⁺-admissible:
  relative `w₂(W) = 0` (Wu-based) on the compact 5-manifold-with-boundary. This blocks the v2
  exploit `[K3] = 0` (a plain unoriented null-bordism of K3 exists, but no `w₂ = 0` one without the
  Rokhlin ÷32 content — which is exactly KT Lemma 5.3, i.e. the completeness leg's honest work).
- **A5 + cost surfacing** — the NEW-BUILD list now names the two substrate towers the definition
  itself consumes: (i) the **relative (Lefschetz) PD/Wu tower on compact 5-manifolds-with-boundary**
  (needed for `w₁(W)`, `w₂(W)`, and the relative characteristic condition — on the critical path for
  ANY honest Bor, independent of this design); (ii) **2-dim PD instances** (Σ's mod-2 fundamental
  class + intersection form) for `hchar`/`hpolar`.
- Fable's HOLDS results kept: W-level T2 + compact + charted ⟹ metrizable (no further W-side
  pathology); `hchar` in ∀-pairing form against canonical mod-2 fundamental classes is effective;
  no k = 0 pinning; `emb` continuous suffices for `hchar`/Brown but NOT for geometric `Σ·Σ` — we
  keep the v2/M-3 commitment (smooth + injective; `Σ·Σ` cohomological if ever consumed).

## 1. Requirements (unchanged from v2: R1–R6, roadmap §2/§3)

Structure-extension `Bor`; genuine `revStr`; no free invariant-valued field; mod-8 computed /
ℤ/16-at-extension-level; T2 + smooth k-generic; vacuity-resistance. NEW (from the attack):
**R7 — per-datum honesty**: every manifold-typed field carries T2 + compactness + charted structure;
**R8 — W-admissibility**: the relation's bordisms are themselves certified Pin⁺-admissible.

## 2. The v3 design — the certified characteristic-pair datum

`Mfd s` for `s : SingularManifold PUnit k (𝓡 4)`:

| field | content | anchor |
|---|---|---|
| `t2` | `T2Space s.M` | leg 1 / feeds `t2Str` |
| `cert` | `PinPlusCertK I s` (k-generic; ops via `PinPlusCertK.sum` / `pinPlusCertK_empty`) | EXISTS (5q.G) |
| `surf` | ▲A-4: `Σ : SingularManifold PUnit k (𝓡 2)` — the model is **PINNED to `𝓡 2` (Boundaryless)**, never existential (an unpinned model breaks `cylBor` totality by invariance of domain) — with **`T2Space Σ.M`** (R7), `emb : Σ.M → s.M` smooth (`ContMDiff (𝓡 2) I k`) + injective | genuine geometry |
| `hchar` | the characteristic condition in **∀-pairing form**: the `emb`-pushforward of Σ's canonical mod-2 fundamental class is PD-dual to `w₁(s.M)²` (`cert` ⟹ `w₂ + w₁² = w₁²`), stated against the canonical classes via the in-tree cup/PD/Wu stack + the NEW 2-dim PD instances | ties `surf` to `s`; effective (rp4 Wu computations make `PD(w₁²) ≠ 0` checkable) |
| `enh` | `n : ℕ`, ▲A-5: the basis datum is a **ℤ/2-linear equiv** `H₁(Σ;ℤ/2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)` (pins `n`; canonical `q`-transport), `q : Brown.Z4Quadratic (Fin n)` | in-tree Brown algebra |
| `hpolar` | ANCHOR: `q`'s polar form = Σ's mod-2 intersection form under the basis (2-dim PD instances) | kills free-`q` |

NO `comp` field (§0/A4). NO grade field of any modulus. ▲A-7 — **THE TARGET, NAMED HONESTLY**: the
carrier is the **KT §6 characteristic-pair bordism group** (Thm 6.11 / Rem 6.15 territory) — NOT the
raw structure-torsor of Pin⁺ structures. On a fixed `(M, Σ)` the structure set is the full
polar-anchored enhancement torsor (`H¹(Σ)`), a strict SUPERSET of the Pin⁺-descent image whenever
`H¹(M;ℤ/2) → H¹(Σ;ℤ/2)` is not surjective (onto for the ℝP⁴/ℝP² headline). This is the group KT's
own §5 proof and the W-D ψ-assembly route through; the W-D completeness leg MUST be written against
this group (fiber-excess is part of its statement, not an error). H¹-fiber-LOSS (the old GM-shadow
defect) is recovered at the quotient by the relation + W-admissibility; fiber-EXCESS is the
characteristic-pair semantics. W-D's V/ψ inputs inherit the per-datum certificate discipline.

`Bor b σ τ` — the certified bordism-level characteristic pair:

0. ▲A-2: **`T2Space b.W` explicit** — the relation is the T2-refined one (`IsT2DataBordant`-style);
   a literal transcription of items 1–4 onto the plain relation re-opens the W-level collapse.
1. **W-admissibility (R8/A2):** ▲A-3: the **absolute** class `w₂(TW) ∈ H²(W;ℤ/2)` — defined via the
   Lefschetz/Wu tower (`PoincareLefschetzWu5.wuW2` of the datum) — **vanishes**, stated in ∀-pairing
   form. This is what makes `w₂(W) = 0 ⟺ Pin⁺ exists on W`, the load-bearing equivalence; with the
   ends' `cert`s the dual class below is honestly the characteristic class.
2. **The membrane datum (R7/A1):** `Q` — a compact, **T2**, charted 3-manifold-with-boundary datum,
   ▲A-4: model **PINNED** (`(𝓡 2).prod (𝓡∂ 1)`-style), with a smooth injective ▲A-6: **proper
   (interior → interior)** map to `b.W`, boundary identification hitting exactly `Σ_σ ⊔ Σ_τ`
   (through `b.e`), encoded in the `BordismGroup.lean` injection-onto-image style PLUS the
   certificates the no-go demands.
3. **Relative characteristic condition:** `Q` dual to `w₂(W) + w₁(W)²` (= `w₁(W)²` by 1.), stated
   against Q's CANONICAL rel fundamental class (never a chosen class).
4. **Structure extension (Taylor Thm 1.1), ▲A-1 — the EXACT form (kernel-forced, no-go
   `taylor-leg-end-convention-trap`):** the joint enhancement with the **τ-end NEGATED** —
   `q_σ ⊕ (Brown.Z4Quadratic.neg q_τ)`, transported to `H₁(∂Q;ℤ/2)` through the boundary
   identification — **vanishes on `ker(H₁(∂Q;ℤ/2) → H₁(Q;ℤ/2))`**. Negation is per Bor-END, never
   per boundary component. (Plain-joint kills the ℝP² witness through the honest cylinder;
   σ-side-only collapses the torsor through the honest cylinder — both kernel-checked. Under this
   form all 12 ops instantiate and Brown-invariance is forced: q-vanishing on the kernel ⟹ isotropic
   ⟹ Lagrangian for the joint polar (honest Q: half-lives-half-dies) ⟹ Gauss factorization ⟹
   `β(q_σ) = β(q_τ)`.) ⚠ TEST DISCIPLINE: `cylBor` is the discriminating op for extension-condition
   conventions — `negBor` self-tests are blind to end-conventions (both copies sit on one end).

`revStr σ` = `σ` with `q ↦ Brown.Z4Quadratic.neg q` (`β ↦ −β`). `negBor` instantiation check
(v3 self-test): `W = s.M × [0,1]`, `Q = Σ × [0,1]`, ends `(Σ, q) ⊔ (Σ, −q)` — `ker(H₁(∂Q) → H₁(Q))`
is the anti-diagonal, on which `q ⊕ (−q)` vanishes ✓; the relative characteristic condition inherits
from `hchar` ✓; W-admissibility inherits from `cert` ✓. Evades both kernel no-go hypotheses (no comp
field; Q certified). All 12 ops instantiate by the same cylinder/sum patterns with certificates.

Computed maps OUT (W-C): `abk8 := Brown of q : → ZMod 8` (bordism invariance = a theorem against
Bor's items 1–4); w₁⁴-parity (`swNumberW14`, k-agnostic). The ℤ/16 = the KT §5 extension assembly
(W-D): surjection `abk8`∘..., kernel from the Spin sector (Lemma 5.3 ÷32 = Rokhlin content, W-E),
ψ non-split witness on the w₁-dual `V` — GROUP-level, never pointwise.

## 3. New-build list (v3, honest)

1. **Relative PD/Wu tower on compact 5-manifolds-with-boundary** (`w₁(W)`, `w₂(W)`, relative duality,
   Lefschetz) — the big one; route-independent critical path (ANY honest Bor needs it).
2. **2-dim PD instances** (Σ mod-2 fundamental class, intersection form) — feeds `hchar`/`hpolar`.
3. The `Mfd`/`Bor` structures + the 12 op witnesses (cylinder/sum patterns + certificates).
4. ℝP⁴ instance: Σ = ℝP² (n = 2 Smith tower re-instantiation for `H₁(ℝP²)`), `q(gen) = 1`,
   `hchar` from the 5q.G Wu computations; smooth atlas from wt2's W-B work.

## 4. Gate record (CLOSED — two full adversarial rounds)

Round 1 (v2): FAIL — 3 exploits, 2 kernel-checked → no-gos `comp-twist-doubling-incompatible`,
`membrane-level-nonhausdorff-collapse`. Round 2 (v3): PASS-WITH-AMENDMENTS — architecture survived
all six vectors; 1 kernel-checked precision exploit → no-go `taylor-leg-end-convention-trap`;
verified affirmatively: K3 exploit reduces to honest Rokhlin ÷32 (kernel ≅ ℤ/2 exactly), Brown
invariance forced, all 12 ops instantiate, round-1 no-gos evaded, `SingularManifold` confirmed
NOT to bundle T2 (R7 necessary). Amendments A-1…A-7 applied above. **v4 = FROZEN. Build OPEN:**
tower slices (1a–1e, running) + the instance structure (item 3) + the ℝP⁴ witness (item 4).
Any statement-shape deviation discovered during the build that WEAKENS a gate-checked condition
re-opens the gate (vacuity attack on the changed shape); mechanical strengthening does not.
