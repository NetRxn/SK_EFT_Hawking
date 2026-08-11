# D8 apex retrofit — the D4→D8 declaration conflict RESOLVED, on the drafts' own instructions

**Date:** 2026-08-07 · Thirteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4:
`papers/D8/paper_draft.tex` (796 lines, every line, including the appendix's
verification-status inventory), `bundle_metadata.json`, and — because this bundle resolves a
conflict — the relevant sections of `papers/D4/paper_draft.tex` re-read against it.

---

## 1. What was declared

**35 apexes → 2,290 declarations across 289 modules, depth 24, 103 private truncations.**

**By far the largest closure in the portfolio** (next is D4 at 620/43). The reason is visible in
the draft: §9's Ross–Selinger layer pulls in a full algebraic-number-theory substrate — a
Euclidean `ℤ[ζ₈]`, the Appendix-C Diophantine solvability chain, Lagrange's four-square theorem —
none of which any other bundle touches.

| § | thread | apexes |
|---|---|---|
| §2 | the alphabet-agnostic substrate + Clifford+T validation | 2 |
| §3 | the lift to SU(d) + the concrete-radius matrix logarithm | 2 |
| §4–§5 | five alphabets; two SU(8) density mechanisms + the converse | 5 |
| §6 | the unconditional Toffoli lower bound | 2 |
| §7 | the correct-by-construction compiler contract | 5 |
| §8–§9 | Ross–Selinger grid route, Appendix-C chain, KMM ancilla route, purity | 13 |
| §10 | the end-to-end diamond certificate | 6 |

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Quantum-compilation researchers and the formal-methods-for-QC community. The draft positions itself precisely against VOQC/SQIR and the Why3/Qbricks landscape: those verify *exact* circuit optimization, D8 verifies *quantitative approximation*. |
| **Venue** | PRX Quantum \| Quantum. Appropriate — the content is compilation theory with a resource lower bound, not physics. |
| **The claim only this container can make** | **Universal compilation as a *theory* rather than an algorithm.** The substrate is parametrized over an abstract generating set, so a new alphabet ships its verified quantitative compiler by *instantiation*; the lift to arbitrary `SU(d)` is enabled by a concrete-radius matrix logarithm that is itself a library contribution. No sibling makes an alphabet- or dimension-agnostic claim. |
| **Substrate** | 289 modules, 2,290 declarations, depth 24: `FKLW/GenericSUd*`, `FKLW/GenericSU2*`, `FKLW/CliffordCCZSU8*`, `FKLW/TrappedIonSU4*`, `FKLW/ReadRezayi*`, `FKLW/Mukhopadhyay*`, `FKLW/CliffordT*`, `RossSelinger/*` (including the Euclidean `ℤ[ζ₈]`, `GridExistenceSharp`, `SU2Euler`, `KMMUniversal`), `FKLW/CompiledGateDiamond`, and `QuantumNetwork/{KroneckerOpNorm, UnitaryDiamond, MatrixNormBridge}`. |
| **Honest size vs charter** | 796 lines against ~40pp — short in prose, and the ratio to substrate (35 apexes over 2,290 declarations) is the inverse of D5's. **This is the most substrate-per-page in the portfolio.** |
| **Boundary failure?** | **No, and the draft is the reason.** It cedes Fibonacci to D4 explicitly (twice) and states that the sibling FT bundle consumes D8's SK as its universal-compilation primitive. Its own purpose — alphabet- and dimension-agnostic compilation theory — is statable without any sibling's substrate. `D8 ∩ D9 = 14` and `D8 ∩ D10 = 8` are `QuantumNetwork` diamond-norm infrastructure consumed for §10, acknowledged in the text. |

---

## 2. ✅ The D4→D8 declaration conflict is RESOLVED — and both drafts dictate the resolution

The D4 retrofit flagged four `GenericSU2` apexes for revisit: D4 §9's substrate list and D8 §2
name the same Clifford+T theorems. Reading D8 in full settles it, because **D8 says so in as many
words, twice**:

> §4: *"Fibonacci is the topological anchor and the origin point of the substrate; **its
> universality is the subject of a companion bundle** and is cross-referenced here."*
>
> §Relationship to companion work: *"The Fibonacci-universality and topological/categorical
> foundations are developed in a companion bundle, which this paper cites for the Fibonacci anchor
> and **generalizes**."*

**The split the drafts themselves draw:**

| content | owner | basis |
|---|---|---|
| F.21 Fibonacci density, `…quantitative_fibonacci_strict`, Path A | **D4** | D8 explicitly cedes it; D4 §9 develops it as its own section |
| Clifford+T, trapped-ion, `GenericSU2`, `GenericSUd`, SU(d) | **D8** | D8's §§2–3 are built on them; D4 named them only in a module list |

**Action taken:** four apexes removed from D4 and declared under D8 —
`cliffordT_accPt_one_unconditional`, the two Clifford+T bundled-strict headlines, and the
trapped-ion one.

**The closure corroborates the reassignment independently.** D4's closure fell **753 → 620**
declarations and **61 → 43** modules on removing those four — they were pulling D8's entire
`GenericSU2`/`SU(d)` tree into D4. **`D8 ∩ D4 = 280`** remains, concentrated in
`OneParameterSubgroupSU2` (108), `SU2LieAlgebra` (30), `SolovayKitaevPathA` (27): the shared
Lie-algebraic core, which is exactly what an "instantiate, don't re-derive" substrate should look
like from both sides.

### And F's D6-absorption attribution is corrected by D8's own text

F §7 says D6 absorbed *"the Phase 6t quantitative Solovay–Kitaev tight-ε headline"*. D8 says:

> *"the fault-tolerant-computation substrate (codes, measurement, gauging) is developed in a
> sibling bundle that consumes the quantitative Solovay–Kitaev **developed here** as its
> universal-compilation primitive."*

So the primitive D6 is said to consume is **D8's**, not D4's. `D8 ∩ D6 = 0` and `D4 ∩ D6 = 0` —
**D6's declared substrate contains neither**, which leaves F's absorption claim unbacked from
either direction. Recorded in the §D4 evidence ledger; not decided here.

---

## 3. D8's kernel-purity claim is scoped, and it verifies

§9.3 claims *"the entire compilation corpus this paper reports … is verified to the kernel with
the standard axiom set and **zero** compiler-trust escape hatches; every remaining finite check is
kernel-checked."* The appendix repeats it.

**Measured inside D8's own closure: 0 declarations carry a `native_decide` marker.** For contrast,
**D4's closure carries 19** (the figure-eight and trefoil knot invariants, which D4 discloses).

The claim is **correctly scoped and true as stated** — it is about D8's corpus, not the project's,
and D8 never says otherwise. §9.3 also explains *how* it became true: four `native_decide` sweeps
(the largest over ~16.7 M tuples) were eliminated by structural reproofs, one of which
**strengthened** the statement by dropping a hypothesis.

⚠️ **I record this measurement with the V26 correction in mind.** The instrument is
`axiom_deps_project`, the field that actually carries `._native.native_decide`, and it was
validated on this same run by finding **19** in D4's closure. An absence measured with an
instrument shown to detect presence.

---

## 4. What D8 gets right

- **The length exponent is stated honestly against the literature's more flattering one:** *"the
  often-quoted exponent log5/log2 ≈ 2.32 would require a quadratic contraction, which our
  construction does not establish; we report the honest 3.97."*
- **The open number-theoretic gap is carried as an explicit hypothesis in the theorem statement,
  never as an axiom** — with the hypothesis isolated to one precise existence
  (`gridFindT_isSome_of_residual`), its status in the literature described, and a second,
  unconditional mechanism (KMM) shipped alongside that removes the wall.
- **A known caveat ships as a theorem rather than as prose**: `diamondDist_unitary_smul_phase`
  proves the diamond bound is not sharp under global phase.
- **Route A's own weakness is flagged:** *"in Route A, CCZ is **not** load-bearing."*
- **A planning error is recorded rather than quietly dropped:** an earlier roadmap targeted a
  Euclidean-domain structure on `ℤ[√2][i]`, *"which is mathematically impossible."*
- **The scope boundary is stated twice and specifically** — verified existence/algorithm/synthesis
  theory, *not* a runnable, hardware-tuned, length-optimal compiler.

---

## 5. Ledger

| artifact | change |
|---|---|
| `papers/D8/bundle_metadata.json` | `apex_theorems` added — 35 entries |
| `papers/D4/bundle_metadata.json` | **4 apexes removed** (the `GenericSU2` alphabet-agnostic set) — closure 753 → 620, modules 61 → 43 |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 9 → 8 |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | D4→D8 upgraded to **RESOLVED at declaration level**; D6-absorption attribution corrected |
| `docs/audits/2026-08-07-d4-retrofit/FINDINGS.md` | §3's flag closed with the resolution |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V31 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 534 apexes across 13 bundles.
