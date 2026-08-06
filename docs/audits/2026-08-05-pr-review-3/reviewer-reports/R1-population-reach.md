# R1 — Population-reach audit

**Branch:** `infra/adr-009-validation-modularization` · **Head:** `db430c65` ·
**Worktree:** `.claude/worktrees/rv1` · **Date:** 2026-08-05

**Dimension:** for every instrument that greps, globs, walks a tree, parses a format or
filters a set — what population does it CLAIM, what population does it REACH, and do they
differ. Method per the brief: measure the corpus independently first, then compare to what
the instrument reports. Every number below has its predicate and its command.

---

## Verdict: **NO**

Two CRITICAL findings, both of the branch's own signature class (a PASS reported over a
population the instrument does not reach), one of them **inside the very check repaired
twice this week for exactly this defect** and larger than either shipped repair
(336 occurrences vs 288 and 276).

The branch's central claim — that the modularized suite measures what its names and
descriptions say — is not yet true. `prose_theorem_reference_coverage` is effectively
vacuous for 2 of 21 bundles (D12 resolves **4** tokens across a draft carrying 197 Lean
references), and 27 project Lean modules sit outside `lean_deps.json`, the derived-truth
substrate that ~15 checks, `counts.json`, the atlas and the graph all read — with no
instrument reporting that they were not measured.

**The verdict flips to YES-WITH-FIXES** when C1 and M1 land (both are small, localized
changes) and C2 gets a *coverage gate* — a check asserting `|modules on disk| ==
|modules in lean_deps.json|` — even if the 27 modules themselves are dispositioned later.

| Severity | Count |
|---|---|
| CRITICAL | 2 |
| MAJOR | 4 |
| IMPORTANT | 3 |
| MINOR | 3 |

---

# CRITICAL

## C1 — `prose_theorem_reference_coverage` cannot see D11/D12's `\thm{}` alias: **336 references, 227 candidate tokens, unscanned while the check reports PASS**

**File:** `scripts/validation/checks/prose_lean_refs.py:66-68` (`_PROSE_VERBATIM_ALIAS_DEF_RE`),
consumed at `:71-82` (`_prose_verbatim_macros` / `_prose_verbatim_re`).

### Claimed population
The registered description (`:461-463`) and the module docstring (`:23-32`):

> "Bundle-draft verbatim Lean references — `\texttt{}`, preamble aliases for it (D8/D9's
> `\lean{}`), and `\verb` (D6) — resolve in lean_deps.json"

> "**'Verbatim' means THREE syntactic forms, and the corpus uses all three.** … If a fourth
> appears, it will be for the same reason: **the count of things scanned is not evidence
> that the population was reached.**"

### Actual population
The alias-discovery regex requires the macro body to be **exactly** one of
`\texttt|\mathtt|\verb|\url|\path|\code` wrapping `#1`:

```python
r"\\(?:newcommand|renewcommand|providecommand)\s*\{?\s*\\([A-Za-z]+)\s*\}?"
r"\s*\[1\]\s*\{\s*\\(?:texttt|mathtt|verb|url|path|code)\s*\{\s*#1\s*\}\s*\}"
```

D10 defines `\newcommand{\thm}[1]{\texttt{#1}}` → **matched, 37 uses reached**.
D11 and D12 define the *same macro name* with a line-breaking wrapper:

```latex
\newcommand{\thm}[1]{{\def\_{\char`\_\allowbreak}\texttt{#1}}}
```

→ **not matched**. `_prose_verbatim_macros` returns `{'texttt'}` for both drafts.

### The gap, measured

| draft | `\thm{` occurrences | macros the check discovers | candidate tokens the check sees | candidate tokens present via `\thm` |
|---|---|---|---|---|
| D10 | 37 | `texttt`, `thm` | 41 | 33 (all reached) |
| **D11** | **139** | `texttt` only | **5** | **95 — none reached** |
| **D12** | **197** | `texttt` only | **4** | **132 — none reached** |

D12's entire visible population is `['Classical.choice', 'Quot.sound', 'native_decide',
'norm_num']` — three of which are Mathlib/tactic names that resolve trivially. The check
reports PASS on a draft whose ~197 Lean references it has never read.

**Command:**
```bash
grep -rn 'newcommand{\\thm}' papers --include='*.tex'
python - <<'EOF'
import sys; sys.path.insert(0,'scripts'); sys.path.insert(0,'.')
from validation.checks.prose_lean_refs import _extract_prose_lean_candidates, _prose_verbatim_macros
from pathlib import Path
for b in ("D10","D11","D12"):
    s = Path(f'papers/{b}/paper_draft.tex').read_text()
    print(b, sorted(_prose_verbatim_macros(s)),
          "thm_uses=", s.count("\\thm{"),
          "prod_tokens=", len({t for t,_ in _extract_prose_lean_candidates(s)}))
EOF
```

### How verified
Ran the **production** `_extract_prose_lean_candidates` and `_prose_verbatim_macros` against
the production drafts, then re-ran the same extractor over a synthetic source containing only
the `\thm` spans, and took the set difference. Resolved each missed token through the
production `_resolve_prose_ref` against the live `lean_deps.json`.

### Blast radius today
**All 227 missed tokens currently resolve** — so this is a latent exposure, not a live wrong
answer. That is precisely the posture of the `\lean{}` and `\verb` holes when they were
found. The check is the branch's declared guard against Class-TN theorem-name drift; for D11
and D12 it is not guarding.

### Secondary: a **second-order** alias also escapes
D12 defines `\newcommand{\mthm}[1]{\thm{#1}}` (7 uses) — an alias *of an alias*. Even with
`\thm` discovered, the regex's body allow-list contains no user macros, so `\mthm` stays
invisible. A discovery pass that resolves aliases transitively (fixed point over the preamble)
is the durable form; enumerating bodies is what produced four rounds of this defect.

---

## C2 — 27 project Lean modules are absent from `lean_deps.json`; 16 have never been compiled. No instrument reports the omission.

**Files:** `lean/SKEFTHawking.lean` (root aggregate, 5 226 lines, 1 937 `import` lines);
`lean/lakefile.toml:[[lean_lib]] name = "SKEFTHawking"` (**no `globs` key** → Lake's default
is the root module and its transitive imports); `lean/SKEFTHawking/ExtractDeps.lean:9-12`.

### Claimed population
`ExtractDeps.lean:9-12`, in its own words:

> `-- Import the root module which transitively imports ALL project modules.`
> `import SKEFTHawking`

`counts.json` publishes `lean.modules = 2012` as the project's module count. `lean_build`'s
description is "Lean project builds cleanly (requires lake)". `axiom_closure_allowlist` claims
"**Every** SKEFTHawking declaration's transitive axiom closure…" — and `AxiomAudit.lean:34`
likewise imports only `SKEFTHawking`.

### Actual population

```
project module files on disk (lean/SKEFTHawking/**/*.lean) : 2039
transitively reachable from lean/SKEFTHawking.lean         : 2011
modules present in lean/lean_deps.json                     : 2012
modules on disk but ABSENT from lean_deps.json             :   27
source modules with NO .olean in lean/.lake/build          :   16
```

The two derivations agree exactly: the set-difference `{on-disk} − {in lean_deps}` and the
independently-computed unreachable-from-root set are the **same 27 modules** (plus
`ExtractDeps`, which is its own entry point).

The 27 (grouped):

- `AtlasAttr`, `AxiomAudit`, `AxiomClosure` — infrastructure, plausibly intentional
- `FKLW/{BinaryTetrahedral, StandardTorusSU2, TrappedIonAlphabet, TrappedIonSU4Calibration}`
- `FaultTolerance/{AGP.Threshold, Chernoff, Concatenation, Counting, DoubleExp, ExRec, Malignant, StabilizerCode, SteaneCode}`, `FaultTolerantUQC`
- `Singular{CapCastChain, CapHomologySubdiv, ChainComplexCat, ConnSquareCloseUncond, ConnSquareCrossReal, PDWindow2, SurfaceIntersectionFormInstances}`
- `SymTFT/{CenterLinear, ElectricSeparable, VecGLinear}`

**Content:** 5 896 source lines, **239 `theorem`/`lemma` declarations**, largest being
`FKLW/BinaryTetrahedral` (74) and `FKLW/StandardTorusSU2` (47).

**Commands:**
```bash
# module-name set difference
python - <<'EOF'
import json; from pathlib import Path
src={'.'.join(p.relative_to(Path('lean')).with_suffix('').parts)
     for p in Path('lean').glob('SKEFTHawking/**/*.lean')}
dep={e.get('module','') for e in json.loads(Path('lean/lean_deps.json').read_text())}
print(len(src), len(dep), len(src-dep)); print(sorted(src-dep))
EOF
# never-compiled set
python - <<'EOF'
from pathlib import Path
S=Path('lean/SKEFTHawking'); B=Path('lean/.lake/build/lib/lean/SKEFTHawking')
s={'/'.join(p.relative_to(S).with_suffix('').parts) for p in S.rglob('*.lean')}
o={'/'.join(p.relative_to(B).with_suffix('').parts) for p in B.rglob('*.olean')}
print(len(s), len(o), sorted(s-o))
EOF
```

### How verified
1. Two independent derivations (name set-difference; transitive import closure) landed on the
   identical 27-module set.
2. **Rule 6 self-check applied and it caught my own instrument.** My first import regex was
   `[A-Za-z0-9_.]+`, which cannot match `SKEFTHawking.Itô.*` — it produced 34 "unreachable"
   modules including six `Itô/` files that are in fact reachable and *are* in `lean_deps.json`.
   Re-running with `\S+` reduced the set to 27 and made it agree exactly with the set-difference.
   The six `Itô` modules are **not** part of this finding.
3. Build-recency control: `lean/.lake/build/lib/lean/SKEFTHawking.olean` is dated **2026-08-01
   00:13**; the newest never-compiled source (`SymTFT/VecGLinear.lean`) is **2026-07-27**. The
   default target was built after these files existed and produced no `.olean` for them.

### What is *not* claimed
The 14 `sorry` tokens I first counted in these files are **all inside doc-comments**
("Zero sorry. Zero axioms."), not live proofs — checked line by line. There is **no** live
`sorry` and **no** project `axiom` in the 27. So Invariants #4 and #15 are not currently being
violated in the blind spot; what is true is that **no instrument would tell us if they were**.

### Why CRITICAL
`lean_deps.json` is the derived-truth substrate for roughly a quarter of the suite —
`graph_integrity`, `atlas_integrity`, `axiom_closure_allowlist`, `formula_grounding`,
`placeholder_not_cited`, `vacuous_statement_audit`, `native_decide_regression`,
`theorems`, `prose_theorem_reference_coverage`, `theorem_name_embedded_citations`,
`counts_fresh` — plus `counts.json`, `atlas_view.json` and the provenance graph. Every one of
them computes over 2 012 modules and none of them says "27 were not measured". This is the
textbook self-sealing denominator: the substrate defines its own population, so it can never
report a member it never ingested.

**Minimum fix (not the full disposition):** a check asserting
`|{p.stem for p in lean/SKEFTHawking/**/*.lean}| == |{e.module for e in lean_deps.json}|`,
failing loudly on any difference. That converts a silent omission into a decision.

---

# MAJOR

## M1 — `extract_lean_deps.compute_lean_hash()` is blind to the root aggregate; the identical bug was fixed in `_memo` during pass 2 and left here

**File:** `scripts/extract_lean_deps.py:62-79` (`compute_lean_hash`), `:25` (`LEAN_DIR = PROJECT_ROOT / "lean" / "SKEFTHawking"`), consumed by `_needs_refresh()` at `:81-89`.

**Claimed:** the docstring says *"SHA-256 hash (16 hex chars) of **all** .lean source files
(recursive)"*.

**Actual:** `LEAN_DIR.rglob("*.lean")` walks `lean/SKEFTHawking/` only.
`lean/SKEFTHawking.lean` is its **sibling**, not its child — and it is the file whose `import`
lines decide which modules land in `lean_deps.json` at all (see C2).

`scripts/validation/_memo.py:204-214` documents this exact hazard and fixes it:

> "⚠️ **THE ROOT AGGREGATE IS A SIBLING, NOT A CHILD** (fixed 2026-08-05, reviewer R6) …
> `glob("**/*.lean")` over the directory missed it entirely (verified: 2,039 files matched,
> the root file not among them). Adding or removing an `import SKEFTHawking.Foo` therefore
> changed the verified surface without moving the key."

The memo key was repaired. The **production skip-cache that decides whether
`lean_deps.json` is regenerated at all** was not.

**How verified — seeded defect in the production artifact, per QI-30:**

```
baseline compute_lean_hash():                              5c500bf3cc4b9d92
after appending a line to lean/SKEFTHawking.lean:           5c500bf3cc4b9d92   UNCHANGED (BLIND)
after appending a line to SKEFTHawking/AcousticMetric.lean: 0beda2bf0ee01eb1   changed (detected)
```

Run in the rv1 worktree against the real files; both files restored immediately
(`git status --porcelain lean/` clean afterwards).

**Consequence:** editing the root aggregate alone — the canonical way to bring a module into
or out of the verified surface — leaves `_needs_refresh()` False, so `lean_deps.json` is not
regenerated and every derived artifact silently describes the previous import surface.
This is a *mechanism* for C2, not merely adjacent to it.

---

## M2 — `cluster_detect.py` excludes every bundle: 1 316 of 3 432 v2 sentences (38 %) never clustered; `bundle_consistency` verifies only legacy snapshots

**Files:** `scripts/cluster_detect.py:108-109`; mirrored in
`scripts/validation/checks/freshness.py:357-358` (`_claim_clusters_is_stale`).

```python
for p in sorted(PAPERS_ROOT.iterdir()):
    if not p.is_dir() or not p.name.startswith('paper'):
        continue
```

**Claimed:** `cluster_detect.py:6-8` — *"Walks **every** `papers/<paper>/claims_review.json`
v2 schema"*. `claim_clusters_fresh`'s description — *"papers/claim_clusters.json is up-to-date
vs. **the** v2 claims_review.json files"*. `bundle_consistency`'s description — *"**Cross-bundle**
clusters' member sentences agree on numerical content **across bundle boundaries**"*.

**Actual:** publication-bundle directories are named `F`, `D1`–`D12`, `I1`–`I3`, `L1`–`L3`,
`E1`, `E2` — none starts with `paper`.

```
v2 claims_review.json REACHED (paper*/):  27 files / 2 116 sentences
v2 claims_review.json EXCLUDED (bundles): 19 files / 1 316 sentences
true corpus:                              46 files / 3 432 sentences   → reach 61.7 %
```

Excluded: `D1 D2 D3 D4 D5 D7 D8 D10 D11 D12 E1 E2 I1 I2 I3 L1 L2 L3 note_rt_ch_bounds`.

The live run confirms it end to end: `claim_clusters_fresh` reports
`3 cluster(s) across 6 paper(s)`; `claim_clusters.json`'s `member_papers` union is
`{paper9, paper10, paper11, paper16, paper20, paper33}` — **zero bundle members**.

`bundle_consistency` then reads `cluster_bundle_index.json`, whose `cross_bundle` flag is
computed by *projecting legacy paper keys through `PAPER_DRAFT_MAPPING.md`*. So it reports
`2 cross-bundle clusters … spans D2,D4,L2 … guaranteed consistent` while every member sentence
is from a historical snapshot draft. **The shipped bundle prose — the thing whose
cross-bundle consistency the check is named for — is not in the corpus.**

**Commands:**
```bash
python - <<'EOF'
import json,glob
tp=tb=np_=nb=0
for f in glob.glob('papers/*/claims_review.json'):
    d=f.split('/')[1]
    try: s=json.load(open(f)).get('sentences')
    except Exception: continue
    if not isinstance(s,list): continue
    (globals().__setitem__('tp',tp+len(s)) or globals().__setitem__('np_',np_+1)) if d.startswith('paper') else None
EOF
uv run python scripts/validate.py --check claim_clusters_fresh
python -c "import json;d=json.load(open('papers/claim_clusters.json'));print(sorted({p for c in d['clusters'] for p in c['member_papers']}))"
```

**Cascade:** (a) a bundle's `claims_review.json` can change without `claim_clusters_fresh`
ever going stale; (b) `bundle_consistency` is structurally unable to compare two bundles'
own sentences; (c) the graph's `ClaimCluster`/`MEMBER_OF` extractors — and therefore
`graph_integrity.claim_cluster_inconsistency` — inherit the truncated member sets.

---

## M3 — `check_bundle_source_freshness`: the `9f62deaa` repair closed the 100 %-absent case and left the 75–80 %-absent case as a silent green PASS

**File:** `scripts/check_bundle_source_freshness.py:175-199, 227-239`.

The repair is **correct for what it targets**: `sources and not measurable` now yields
`warning=True` + an "UNMEASURABLE" message, and the 9 fully-synthetic-source bundles are no
longer vacuous. Verified by reading and by re-running the mapping.

The residual: when *some* sources are absent, control falls to the `else` at `:227` and emits
`passed=True, warning=False` — an unqualified green. `--strict` promotes only `warning=True`,
so the submission gate does not catch it either. The message does append
`"; N further declared source(s) name an absent directory and were NOT measured"`, which is
honest text attached to a verdict that contradicts it.

**Measured (predicate: a declared `(bundle, source)` pair in `PAPER_DRAFT_MAPPING.md` whose
`papers/<source>/` is not a directory):**

| bundle | absent / declared | fraction unmeasured |
|---|---|---|
| E1 | 4 / 5 | 80 % |
| I1 | 6 / 8 | 75 % |
| E2 | 3 / 4 | 75 % |
| L3 | 3 / 4 | 75 % |
| D1 | 7 / 12 | 58 % |
| D4 | 5 / 12 | 42 % |
| D5 | 4 / 9 | 44 % |
| F  | 22 / 63 | 35 % |
| D2 | 2 / 6 | 33 % |
| D3 | 9 / 31 | 29 % |
| L1 | 1 / 2 | 50 % |

**Portfolio: 89 of 180 declared assignments name an absent directory** — the same 89/180 the
ADR-010 measurement recorded, so that number is confirmed; what is not yet true is the
implication that the repair covers it. E1 declares 5 sources, measures 1, and reports green.

**Command:**
```bash
python - <<'EOF'
import sys; sys.path.insert(0,'scripts'); from pathlib import Path
from bundle_migration import parse_mapping
from sentence_state import _VALID_BUNDLE_TARGETS
a=parse_mapping(Path('docs/PAPER_DRAFT_MAPPING.md').read_text()); P=Path('papers')
for b in sorted(_VALID_BUNDLE_TARGETS):
    s=[p for p,v in a.items() if b in v['bundle_destinations']]
    x=[p for p in s if not (P/p).is_dir()]
    if s and x and len(x)<len(s): print(b, len(x), '/', len(s))
EOF
```

**Fix shape:** any bundle with `absent_sources` should carry `warning=True`, so `--strict`
reddens it and the default run marks it advisory rather than clean.

---

## M4 — `update_counts.py` counts 42 of 64 drafts; `\papercount` ships 34 % low into two papers

**File:** `scripts/update_counts.py:250`

```python
papers = list(PAPERS_DIR.glob("paper*/paper_draft.tex")) if PAPERS_DIR.exists() else []
```

**Claimed:** `counts.json → python.papers`, surfaced as `\papercount` in `docs/counts.tex`,
which papers `\input` precisely so counts cannot go stale (Invariants #1/#2, and the whole
premise of `count_literals`).

**Actual:** `paper*/` matches the legacy `paperNN_<slug>/` layout only.

```
glob paper*/paper_draft.tex  : 42
true corpus */paper_draft.tex: 64
missed: D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 E1 E2 F I1 I2 I3 L1 L2 L3 note_rt_ch_bounds
docs/counts.tex: \newcommand{\papercount}{42}
```

This is the same glob defect that `check_numerical_literals` and `check_count_literals` fixed
on 2026-07-31 (their in-code comments name it) and that `bundle_registry_consistency` leg C
fixed on 2026-08-04 — the sibling instance in the counts generator was not swept.

`\papercount` is consumed in `papers/paper15_methodology/paper_draft.tex` and
`papers/I1/paper_draft.tex`. Both state 42 where the repo has 64.

**Command:**
```bash
ls papers/paper*/paper_draft.tex | wc -l ; ls papers/*/paper_draft.tex | wc -l
grep papercount docs/counts.tex ; grep -rl papercount papers --include='*.tex'
```

---

# IMPORTANT

## I1 — `bundle_figure_integrity` reaches 7 of 42 bundle figures (17 %); the scope limit appears in neither the description nor the summary

**File:** `scripts/validation/checks/bundles_readiness.py:132`
(`if not fs.name.startswith(("d11_", "d12_")): continue`) and the 7-entry hardcoded fallback
at `:141-148`.

**Claimed:** "Bundle figures match a fresh render and are legible at typeset size."

**Actual:** figures whose registry name begins `d11_`/`d12_`.

**Measured — `\includegraphics` in the 21 bundle drafts:**
`D5 7, I1 6, I2 5, D9 4, D11 4, E2 4, D8 3, D12 3, L2 2, E1 2, L1 1, L3 1` — **42 total,
7 of them D11/D12 → 17 % reach.**

Contrast `notebook_stored_outputs_current` (same module family, `freshness.py:466-470`), which
states its scope limit explicitly in the summary line *and* FAILs when its glob empties. This
check does neither: the description promises all bundle figures and the summary does not
qualify it.

*Caveat:* I could not execute this check in the rv1 worktree — its venv lacks `numpy`, so it
returned "visualizations import failed — skipped". The 42-vs-7 figure count is from the
drafts themselves and the 7-entry scope from the source; the reach ratio is not in dispute,
but I have not watched the check run.

## I2 — the table pipeline's freshness predicates glob `paper*_*`; for all 21 bundles the readiness table-staleness leg is a structural zero

**Files:** `scripts/validation/checks/freshness.py:264, 271`
(`glob("paper*_*/tables.py")`, `glob("paper*_*/tables/*.tex")`);
`scripts/readiness_gates.py:658-661`.

`tables_fresh`'s description is "Paper tables (tables/\*.tex) are up-to-date vs. pipeline
sources" — unqualified. Measured: **14 `tables/*.tex` exist under `papers/`; the glob reaches
13.** The 14th is `papers/I1/tables/table1_stages.tex`, which the I1 draft does
`\input{tables/table1_stages.tex}` at line 708 — a shipped bundle table outside the
staleness denominator. (It is hand-authored, per its own header, which is separately the
subject of `bundle_tables_use_pipeline`; the reach gap is that it is invisible to the
`min(mtime)` computation regardless.)

`readiness_gates._eval_numerical_freshness` guards its table leg with
`if tables_py.exists() and tables_dir.exists()`. `bundle_tables_use_pipeline`'s own docstring
records that **zero of 21 bundles have a `tables.py`** — so for every bundle this leg
contributes a hardcoded `0 stale tables/*.tex files` to the gate's evidence line and zero
blockers, forever. Missing input rendered as OK.

## I3 — a fourth and fifth verbatim form: `\mathtt{}` and `lstlisting`/`verbatim` environments

**File:** `scripts/validation/checks/prose_lean_refs.py:58, 92`.

`\mathtt` appears in the alias regex's *body* allow-list but is never a directly-matched
macro, so `\mathtt{X}` written inline is unread.

- **Bundle leg:** 7 `\mathtt` occurrences, 2 candidate tokens (`Classical.choice`,
  `Quot.sound`, both D7) — both would resolve. Low impact.
- **Legacy leg:** 30 unreached `\mathtt`/`\thm` occurrences yielding 4 extra candidate tokens
  (`H_EinsteinCartanExtensionHolds` in paper43, `Pi.zero_apply` / `map_neg` / `map_zero` in
  paper44), of which **2 are unresolved** — i.e. the frozen
  `LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 79` was calibrated against an extractor that does
  not reach the whole legacy corpus. A ratchet whose baseline is a partial measurement
  ratchets the wrong number.
- **`lstlisting`/`verbatim` environments:** 5 in bundle drafts (all I3), containing real
  declaration names — `wave_3b_ldp_overall_closure`, `LDPCompatibleSKEFT`,
  `linearResponseRateFunctionCentered`, `SKEFTHawking.Itô.StochasticIntegral`. Never scanned.

**Command:**
```bash
grep -rhoE '\\mathtt\{[^}]{4,}\}' papers --include='*.tex' | sort -u
grep -rc 'begin{lstlisting}\|begin{verbatim}' papers --include='*.tex' | grep -v ':0'
```

**Recommendation (durable form):** stop enumerating macro bodies. Resolve preamble aliases to
a fixed point (so `\mthm → \thm → \texttt` is discovered), add `\mathtt` as a base form, and
treat `verbatim`/`lstlisting` bodies as verbatim spans. Enumeration is what produced rounds
one through five of this defect.

---

# MINOR

## m1 — `line.startswith('theorem ')` misses `lemma` and every modifier-prefixed declaration

**Files:** `scripts/update_counts.py:326, 329, 509, 560`;
`scripts/validation/checks/lean_substrate.py:104`.

Measured over `lean/SKEFTHawking/**/*.lean`:

```
lines starting 'theorem '                                : 19 678   (reached)
lines starting 'lemma '                                  :    714   (missed)
indented theorem/lemma                                   :     37   (missed)
private/protected/noncomputable/@[...]-prefixed same-line:  1 804   (missed)
```

The headline `theorems_total = 26 103` comes from `lean_deps.json`, not this grep, so the
published total is unaffected. What *is* affected is `update_counts`'s per-module block counts
(the `\providecommand{\tetradFormalismThms}{5}` family, 20 such macros in the drafts) and
`check_formulas_to_theorems`'s resolution set. The latter fails *closed* (a missed name reads
as absent), so it is a false-FAIL risk rather than a false PASS.

## m2 — `paper_provenance`: the `\fbox` branch makes the figure-resolution leg unreachable

**File:** `scripts/validation/checks/papers_prose.py:148-154`. The `\includegraphics`
resolution is an `elif` on the `\fbox{\parbox` placeholder test, so any draft carrying a
placeholder box has **zero** of its figure references resolved. No draft currently trips it,
so this is latent — but the two conditions are independent questions and the second is
silently skipped when the first fires.

## m3 — one orphan `.tex` under `papers/` is reached by no check

`papers/experimental_predictions/prediction_tables.tex` — the only `.tex` under `papers/`
that is neither a `paper_draft.tex` nor under a `tables/` directory, and whose directory has
no `paper_draft.tex`. Every prose check keys on `all_paper_drafts()`
(`PAPERS_DIR.glob("*/paper_draft.tex")`, 64 files), so this file is outside all of them.

---

# Coverage table — every check audited, including the ones that passed

Reach verdict is about **population**, not about whether the check passed. "lean_deps"
means the check inherits C2's 27-module blind spot through `lean_deps.json` and reports no
coverage figure of its own.

| # | check | claimed population | reach verdict |
|---|---|---|---|
| 1 | `formulas` | Lean names from source + ARISTOTLE_THEOREMS | ⚠ m1 (`startswith('theorem ')`; fails closed) |
| 2 | `placeholder_not_cited` | project theorems | ⚠ lean_deps (C2) |
| 3 | `disclosure_consistency` | disclosed theorems × papers | ⚠ lean_deps (C2) |
| 4 | `proxy_body_audit` | structurally-named theorems | ⚠ lean_deps (C2) |
| 5 | `tracked_hypothesis_ledger` | consumed tracked-hypothesis Props | ⚠ lean_deps (C2) |
| 6 | `tracked_hypotheses_fresh` | HYPOTHESIS_REGISTRY ↔ doc | ✓ matches |
| 7 | `formula_grounding` | every formulas.py Lean ref | ⚠ lean_deps (C2) |
| 8 | `vacuous_statement_audit` | every project theorem/lemma | ⚠ lean_deps (C2) |
| 9 | `nogo_substrate_integrity` | KERNEL_NOGO_REGISTRY entries | ✓ matches (registry-keyed) |
| 10 | `native_decide_regression` | decl closure | ⚠ lean_deps (C2) |
| 11 | `numerical` | PARAMETER set | ✓ matches |
| 12 | `identities` | enumerated identities | ✓ matches (explicit list) |
| 13 | `paper_table` | Paper 1 Table 1 cells | ✓ matches (named artifact) |
| 14 | `d1_hierarchy_table` | D1 hierarchy table | ✓ matches |
| 15 | `f_hierarchy_claims` | F inline BEC corrections | ✓ matches |
| 16 | `theorems` | ARISTOTLE_THEOREMS keys | ⚠ lean_deps (C2) |
| 17 | `notebooks` | `notebooks/*.ipynb` | ✓ **91/91 measured** — no nested notebooks exist |
| 18 | `lean_source` | key theorem names in source | ✓ `LEAN_DIR.rglob` reaches all 2 039 files |
| 19 | `cgl_fdr` | CGL derivation | ✓ matches |
| 20 | `lean_build` | "Lean project builds cleanly" | ✗ **C2** — default target excludes 27 modules; 16 never compiled |
| 21 | `axiom_closure_allowlist` | "**Every** SKEFTHawking declaration" | ✗ **C2** — `AxiomAudit.lean:34` imports the root aggregate only |
| 22 | `elaboration_knob_watchlist` | proof-body knobs in Lean source | ✓ `LEAN_DIR.rglob`, all 2 039 |
| 23 | `bundle_figure_integrity` | "Bundle figures" | ✗ **I1** — 7 of 42 (17 %) |
| 24 | `viz_consistency` | `notebooks/*.ipynb` | ✓ 91/91 |
| 25 | `notebook_exec` | `notebooks/*.ipynb` | ✓ 91/91 |
| 26 | `physical_bounds` | computed quantities | ✓ matches |
| 27 | `cross_path_consistency` | enumerated path pairs | ✓ matches |
| 28 | `paper_provenance` | "All 64 drafts" | ✓ 64/64 via `all_paper_drafts()`; ⚠ m2 `elif` branch |
| 29 | `parameter_provenance` | PARAMETER_PROVENANCE | ✓ matches |
| 30 | `counts_fresh` | counts.json vs sources | ⚠ **M4** (`\papercount` 42/64); root aggregate not in `_COUNTS_SOURCES` |
| 31 | `tables_fresh` | "Paper tables (tables/*.tex)" | ✗ **I2** — 13 of 14 |
| 32 | `claim_clusters_fresh` | "v2 claims_review.json files" | ✗ **M2** — 27 of 46 files, 62 % of sentences |
| 33 | `numerical_literals` | all drafts | ✓ 64/64 (`all_paper_drafts()`; glob widened 2026-07-31) |
| 34 | `bundle_tables_use_pipeline` | BUNDLE_CODES drafts | ✓ 21/21; FAILs on empty scope |
| 35 | `graph_integrity` | knowledge graph | ⚠ lean_deps (C2) + M2 cluster members |
| 36 | `atlas_integrity` | derived atlas | ⚠ lean_deps (C2) |
| 37 | `atlas_hypothesis_discipline` | tracked-hypothesis distribution | ⚠ lean_deps (C2), advisory |
| 38 | `count_literals` | all drafts | ✓ 64/64 |
| 39 | `recurrence_reopens_closures` | review docs + ledger | ✓ 273/273 review `.md` (see 40) |
| 40 | `review_severity_declared` | `AutomatedReviews/*/*.md` | ✓ **273 of 273** — measured: 0 files at depth 1 or ≥3 |
| 41 | `review_docs_mint_findings` | bundle Stage-13 review docs | ✓ same corpus, FAILs on zero nodes |
| 42 | `accepted_findings_carry_rationale` | supersession records | ✓ matches |
| 43 | `bundle_metadata_matches_graph` | bundle_metadata vs graph | ✓ 21/21 |
| 44 | `notebook_stored_outputs_current` | `D1[12]_*.ipynb` | ✓ **scope-limited but declared** — states the limit in its summary and FAILs on an empty glob |
| 45 | `readiness_verdicts_agree` | heatmap vs gate | ✓ 21/21; ⚠ shares I2's dead table leg |
| 46 | `readiness_submission_gate` | every paper's P1 gates | ⚠ **I2** — table-staleness leg structurally 0 for all 21 bundles |
| 47 | `citation_primary_sources_present` | `\cite*{}` in all drafts | ✓ 64/64; verified **no draft `\input`s a section file**, so draft-only scope is complete |
| 48 | `provenance_doi_in_registry` | PARAMETER_PROVENANCE DOIs | ✓ matches |
| 49 | `bundle_consistency` | "across bundle boundaries" | ✗ **M2** — zero bundle sentences in the corpus |
| 50 | `bundle_source_freshness` | bundle sources vs last_lift | ✗ **M3** — 11 bundles green with 29–80 % of sources unmeasured |
| 51 | `bibitem_title_primary_source` | registry titles vs cached PDFs | ✓ matches |
| 52 | `quantum_network` | `QuantumNetwork/**/*.lean` | ✓ rglob reaches the subtree |
| 53 | `bundle_registry_consistency` | roster consumers + `scripts/**/*.py` | ✓ **rglob fixed 2026-08-04**; reaches the 12 check modules |
| 54 | `paper_latex_compiles` | BUNDLE_CODES drafts | ✓ 21/21; input closure is a deliberate superset |
| 55 | `axiom_count_prose_consistency` | prose axiom counts vs counts.json | ⚠ inherits C2 via counts.json |
| 56 | `prose_theorem_reference_coverage` | "THREE syntactic forms" | ✗ **C1** (`\thm`, 336 refs) + **I3** (`\mathtt`, `lstlisting`, `\mthm`) |
| 57 | `theorem_name_embedded_citations` | year-token decl names × drafts | ⚠ lean_deps (C2); prose match is raw + `\_`-escaped, so alias-independent |
| 58 | `inventory_index_autogen_fresh` | autogen blocks vs counts.json | ⚠ inherits C2 via counts.json; advisory |
| 59 | `lean_docstring_refs_resolve` | Lean docstring backticked names | ✓ `LEAN_DIR.rglob`, all 2 039 files |
| 60 | `paper_toolchain_pin_drift` | all drafts + `preprint_draft.md` | ✓ 64 + 1, complete |

**Non-check scripts audited:** `atlas_view.py` (derives from `lean_deps.json` — inherits C2,
cannot drift otherwise), `readiness_gates.py` (**I2**), `bundle_readiness.py` (21/21, ✓),
`update_counts.py` (**M4**, **m1**), `extract_lean_deps.py` (**M1**), `review_runner.py`
(registry-derived, ✓), `sentence_state.py` (registry-derived, ✓),
`bundle_source_manifest.py` (`rglob("*")` with dot/`__pycache__` exclusion, ✓),
`cluster_detect.py` (**M2**), `check_bundle_source_freshness.py` (**M3**),
`render_paper_tables.py` (**I2**).

---

## Rule 6 self-audit — where my own instrument was wrong

1. **Import regex, C2.** `[A-Za-z0-9_.]+` cannot match `SKEFTHawking.Itô.*`. My first pass
   reported 34 unreachable modules including six `Itô/` files that are reachable *and* present
   in `lean_deps.json`. Corrected to `\S+`; the result then agreed exactly with the
   independent name set-difference (27 = 27). Had I filed the first number, six modules would
   have been wrongly accused.
2. **`sorry` counting, C2.** My regex found 14 `sorry` tokens in the 27 modules. Reading each
   line showed **all** are inside doc-comments ("Zero sorry. Zero axioms."). No live `sorry`.
   I removed the Invariant-#4-violation claim I had been about to make.
3. **`grep -c` vs occurrence count, C1.** `grep -c` counts matching *lines*; the `\thm` totals
   in this report are occurrence counts from `re.findall`, which is why D10 reads 37 here and
   36 under a naive `grep -c`.
4. **Unverified by execution and flagged as such:** `bundle_figure_integrity` (I1) — the rv1
   worktree venv lacks `numpy`, so the check skipped. Reach ratio is from the corpus and the
   source, not from a run.
5. **Confirmed rather than re-derived:** M3's `89 of 180` reproduces the ADR-010 measurement
   exactly. That number is trustworthy; the *implication* drawn from it — that the repair
   covers the population — is what does not hold.

## On the branch's own account of itself

`prose_lean_refs.py:30-32` says: *"If a fourth appears, it will be for the same reason: **the
count of things scanned is not evidence that the population was reached.**"* A fourth
(`\mathtt`), a fifth (`lstlisting`), and a much larger third-and-a-half (`\thm`, 336 refs —
bigger than either repair that prompted the sentence) all appeared. The docstring diagnosed
the class correctly and the fix did not act on the diagnosis: it enumerated three forms rather
than removing the enumeration.

The same shape recurs across findings: `_memo` fixed the sibling-root bug and
`extract_lean_deps` kept it (M1); `numerical_literals` and `count_literals` fixed the
`paper*` glob and `update_counts` kept it (M4); `notebook_stored_outputs_current` FAILs on an
empty glob and `bundle_figure_integrity` does not (I1). **The durable remedy is not another
list — it is a coverage assertion per instrument: every check that scans a population should
state the size it reached and fail when that size is not the size of the corpus.** C2 is the
clearest case: one assertion, `|on disk| == |in lean_deps.json|`, converts a silent 27-module
omission into a decision someone has to make.
