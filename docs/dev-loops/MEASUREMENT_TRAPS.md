# Measurement traps — when a live thing scans as absent

Read before filing any finding whose evidence is a **zero**, a count, or the word *no*.

Every trap below produced a wrong finding against working code. Several became committed
corrections that had to be withdrawn.

---

## The rule

**Before filing "X does not exist", name the field or tool that would show X's presence, and prove
it can — by finding a known-present instance with it.**

An absence measured with an instrument never demonstrated to detect the thing is not evidence about
X. It is a null result about the instrument.

**And check whether a registered check already measures it.** `validate.py --list`, first, always.

## The tell that is easiest to ignore

⚠️ **A conclusion that is surprising in a *flattering* direction deserves the scrutiny reserved for
one that is surprising in a damaging direction.**

The worst instance: a scan reported that a kernel-purity marker appeared on zero declarations, so
nothing load-bearing used `native_decide`. That reading made the corpus look purer than its own
authors claimed. It was false — the scan probed the wrong field, `axiom_deps_core` instead of
`axiom_deps_project`, and a registered check already measured the real figure and had not been run.
The claim was then widened three times, each step making it more valuable and adding no evidence.
**Every widening should have lowered confidence.**

---

## Traps that produce false ABSENCE

| trap | what it missed | use instead |
|---|---|---|
| probing the wrong field | a marker recorded in a *different* dependency set than the one scanned | name the field that carries it, and confirm on a known-present instance |
| `ast.Assign` only | `X: T = v` is an **`AnnAssign`** — reported live, load-bearing module constants as absent | walk `Assign` **and** `AnnAssign` |
| `^NAME\s*=` grep | the same annotated form: the annotation sits between the name and `=` | AST, or `^NAME\s*[:=]` |
| raw identifier in `.tex` | drafts escape underscores as `foo\_bar`; a raw scan reported **0** manuscript hits against a true 14 drafts / 25 hits | unescape `\_` first, or scan both forms |
| counting references as writes | a module *mentions* a flag three times and writes it zero times — all three are comments saying it deliberately does not | read the lines; a reference is not a write |
| narrow regex alternation | `was wrong` misses `were wrong` | enumerate the inflections, then re-scan |
| digits for a number written as words | sweeping stale timings by digit reported clean while two documents said *"forty-five minutes"* | grep the spelled form, or scan for the **unit** and read the hits |
| a prose name for a deleted file | path-resolution gates match *path-like* refs; a document routed readers to a deleted pair **by name**, and the gate stayed green | after a deletion, grep the prose noun-phrase, not only the path |
| a truncating pipe | `… \| head -12` over sixteen rows reported the last three absent | never `head` a scan you are about to call complete; `wc -l` first |
| a phrase spanning a line break | a per-line prose gate cannot see `"…and have / not inspected its text"`, and the same class silently broke verification of a quote verbatim present in its source | join lines before matching; keep an offset→line index for reporting. Wrapped prose has no stable line semantics — only the paragraph does |
| a non-UTF-8 source file | an ISO-8859 `.tex` returns nothing at all from plain `grep`, including for words plainly in it. It scans as an **empty file**, so every absence over it is vacuous | `LC_ALL=C grep -a`, and sanity-check with a word you know is present before trusting any zero |
| one level of a nested tree | `docs/dev-loops/*/` as a proxy for *notebook homes* missed every sub-loop notebook; `.gitignore` matches `**/` at any depth and so must the scan | enumerate by finding the artifact, not by listing a directory |
| one tree, one spelling | the same population lived in three trees under two naming conventions; each scan was correct and collectively they were narrow | search by what the thing **is**, then confirm the tree list is complete |
| **a required trailing delimiter** | a declaration scanner matched `name` only when followed by a space or colon, so a name ending its line — signature beginning below — was invisible, and with it the whole namespace. 7.2% of one Lean corpus | anchor on what actually ends the token, and remember that **end-of-line ends it too**: `(?:\s|:\|$)` |
| **the new code's spelling for an old capability** | asked whether a tool had auth support by grepping the constant `AUTH_TOKEN_ENV`, which only exists after a refactor. The capability was there all along under its literal value `LEAN_LSP_MCP_TOKEN` | grep the **value**, not the identifier a later version gave it |
| **a path filter naming a layout that changed** | `git grep … -- src/` against a revision predating the `src/` move searches a path that does not exist there, and reports clean | confirm the tree shape at the revision you are searching, not at HEAD |

## Traps that produce false PRESENCE

- **Sentence-splitting on `.`** truncates at a dotted filename (`Foo.lean`), cutting the qualifier
  that follows. Produced a filed-then-withdrawn finding.
- **Hex-pattern scans** for a revision collide with ISBNs, run IDs and dates. Scan the version
  string instead.
- **A right-looking number from the wrong convention.** An extractor attributed 194 theorems where a
  draft claimed 114; running the script the draft *named* reproduced 114 exactly. Two conventions,
  and the draft was right. **Run the tool a claim names before filing against it** — especially when
  the contradicting number is already in hand.

## Not a trap, but a bound

**Ambiguous short names are unresolvable, not wrong.** A link canonicaliser that skips `zero`, `A`,
`F` because each has many candidates yields an **upper bound**, and any count built on it inherits
that status. Say so rather than reporting it as exact.

---

*Companion rules: `PRE_DECISIONS.md` (what the loop applies without asking), `SETTLED_FORKS.md`
(routes not to re-open). The kernel-checkable negative frontier is machine-enforced instead —
`KERNEL_NOGO_REGISTRY` in `src/core/constants.py`.*
