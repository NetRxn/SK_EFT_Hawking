# I2 apex retrofit — a software paper whose per-theorem purity claims all verify

**Date:** 2026-08-07 · Sixteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/I2/paper_draft.tex`
(1,016 lines, every line, including the commented lift stub after the bibliography),
`bundle_metadata.json`, and — for the purity claims — the `axiom_deps_project` marker on each
named theorem.

---

## 1. What was declared

**20 apexes → 223 declarations across 10 modules, depth 5, zero private truncations.**

| § | component | apexes |
|---|---|---|
| §2 | `VerifiedJackknife` — the four statistical theorems | 4 |
| §6.1 | SU(2)_k Verlinde formula: representative cases and the complete k=3,4,5 tables | 9 |
| §6.4 | Fibonacci MTC — pentagon, and both hexagon orientations | 7 |

I2 names 21 theorems in monospace across the draft; 20 are declared (the twenty-first resolves to
a `Collar.ContMDiffPartitionOfUnity.sum_nonneg` token collision with the Mathlib lemma the draft
cites by bare name).

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Two disjoint halves, and the draft says so: applied physicists who need verified lattice-statistics or topological-QFT infrastructure, and proof-assistant library maintainers who care about upstream strategy and AI-assistance disclosure. |
| **Venue** | JOSS, per the metadata. Correct — this is a software paper with a released Apache-2.0 artifact, not a results paper. |
| **The claim only this container can make** | **That two pieces of reusable infrastructure exist, ship, and can be adopted without rebuilding the substrate** — verified jackknife/autocorrelation estimators, and a 27-module tensor-category library carrying the Pivotal→Modular hierarchy, three quantum groups, nine decidable number fields, and eight concrete MTC instances. Its siblings *consume* this substrate; only I2 documents it as software with a licence, an extraction repo, and an upstream plan. |
| **Substrate** | 10 modules, 223 declarations, depth 5 as *declared*: `VerifiedJackknife`, `SU2kSMatrix`, `FibonacciMTC`, `FibonacciBraiding`, `PolyQuotQ`, and dependencies. ⚠️ The **library** is larger than the declaration — see §3. |
| **Honest size vs charter** | 1,016 lines. For a JOSS software paper that is on the long side, not short; JOSS papers are typically 1–2 pages plus the artifact. The charter mismatch here runs the *other* way from every other bundle measured. |
| **Boundary failure?** | **No.** `I2 ∩ D4 = 6`, `I2 ∩ F = 5`, zero elsewhere — I2 *supplying* substrate its siblings consume, which is exactly a library paper's shape. |

---

## 2. ✅ Every per-theorem purity claim verifies — including the mixed ones

I2 makes claims in **both** directions about compiled evaluation, in adjacent sections. Each was
measured against `axiom_deps_project`, the field that carries the `._native.native_decide` marker:

| I2 says | measured |
|---|---|
| §6.1: the SU(2)_k proofs are *"all kernel-pure (`decide` / `norm_num` / `ring` / `linear_combination`; **no `native_decide`**)"* | `verlinde_k3_full` **no marker** ✓; `verlinde_k5_full` **no marker** ✓ |
| §6.4: `fib_pentagon` *"by `native_decide` on the 512-case F-symbol catalog"* | **marker present** ✓ |
| §6.4: the hexagons are *"named, kernel-pure theorems"* | `fib_hexagon_R_vacuum` **no marker** ✓ |

**A draft that says "kernel-pure here, `native_decide` there" and is right on both counts is the
strongest form of this disclosure in the corpus.** D8 claims corpus-wide purity and verifies; D4
discloses `native_decide` where it uses it; **I2 does both, in adjacent subsections, and the
distinction tracks the actual markers theorem by theorem.**

⚠️ **This is the check my V26 correction was about, run correctly.** The instrument is the right
field, and it was validated on the same run by returning `True` for `fib_pentagon`.

---

## 3. The declaration measures what the paper names, not what the library holds

I2's abstract describes *"a 27-module library (~949 declarations)"*; the declared closure is
**223 declarations across 10 modules**. That is not a discrepancy — it is the apex model working
as intended:

- I2 gives **per-module declaration counts in prose** for all 27 modules (`KLinearCategory` 23,
  `FusionCategory` 20, `SphericalCategory` 22, `RibbonCategory` 14, `Uqsl2Hopf` 28,
  `Uqsl3Hopf` 40, the nine number fields totalling 207, and so on) — so the library's size is
  disclosed and traceable.
- But it **names individual theorems** only for `VerifiedJackknife` and the Verlinde/Fibonacci
  instances. An apex is a named claimed result; a module described by declaration count presents
  no statement to declare.

**Compare D7 §2**, which describes 24 theorems in aggregate and names none — there the same rule
yielded *zero* apexes for the section. **I2 is the benign version of that pattern**: a software
paper legitimately describes an artifact by its shape rather than theorem-by-theorem, and it
supplies the counts that let a reader check the shape.

The consequence to record: **for a library paper, closure size measures citation practice, not
artifact size.** Do not read I2's 223 as the library's extent — the paper's own per-module table is
the better figure, and it is prose, not a derived count.

---

## 4. What I2 gets right

- **A scope boundary stated as a section**: §2.3, *"What is not formalized"* — the estimators are
  deterministic functions of finite samples, **not** random variables; unbiasedness *"require\[s\]
  a probability measure … and \[is\] not part of `VerifiedJackknife`."* The claim is *"the
  estimators are deterministically what they are claimed to be … not that they are unbiased
  estimators of population quantities the user did not ask the library to know about."*
- **A worked number labelled as fabricated for illustration**: *"τ_int = 17.4 ± 0.3"* is flagged
  in the same sentence as *"a worked-example value, not a measured one in this paper."*
- **Deferred content named at the point of use**: the SU(3)_2 F-symbol catalog and the full
  hexagon/pentagon discharges are *"deferred per the module's docstring"*, with the `F² = I`
  involution shipped.
- **A known architectural wart is disclosed rather than hidden**: `RibbonCategory` carries duals
  through a `RigidCategory` parameter instead of `PivotalCategory` inheritance, and *"a refactor to
  align with the textbook presentation … is a separate planned task."*
- **A mathematical obstruction is named, not smoothed over**: the k=5 entries live in the totally
  real cubic ℚ(2cos(π/7)), which admits **no** quadratic radical form (*casus irreducibilis*), so
  the cubic minimal polynomial is itself proven and drives all power reduction.
- **The AI-disclosure protocol asks for no special treatment**: *"We expect Mathlib's acceptance
  threshold to be the same for AI-assisted contributions as for unassisted ones — the standard is
  correctness, mathematical relevance, and engineering quality, not the provenance of the typing."*

---

## 5. Also observed

- **One more empty lift stub** (SymTFT audit substrate). TODO-D14 now spans **seven** bundles.
- **`\input{docs/counts.tex}` is present but no count macro is used in the body.** I2 states its
  figures as literals from per-module prose instead. That avoids TODO-D9's project-scoped-macro
  defect but substitutes hand-maintained counts — 27 modules, ~949 declarations, and ~20 per-module
  figures — none of which any check covers. Recorded, not filed: it is the same
  hand-maintained-roster class as TODO-D10, and the fix shape is the same.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/I2/bundle_metadata.json` | `apex_theorems` added — 20 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 6 → 5 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D14 → seven bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V34 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 568 apexes across 16 bundles.
