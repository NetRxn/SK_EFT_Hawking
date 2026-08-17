## Symptom

`lean_local_search` returns `{"items":[]}` — no error, no warning — for declarations that exist, are built, and are present as source text. A caller cannot distinguish this from the declaration not existing.

Whole namespaces vanish. Querying the bare prefix `SKEFTHawking.DKMBootstrap`, which covers 171 built declarations, also returned `[]`.

## Root cause

`src/lean_lsp_mcp/search_utils.py`, the ripgrep pattern:

```python
+ rf"(?:[A-Za-z0-9_'.]+\.)*{re.escape(query)}[A-Za-z0-9_'.]*(?:\s|:)"
```

The trailing `(?:\s|:)` requires a character after the declaration name. Lean permits a long signature to begin on the line below its name:

```lean
theorem zeroCommutatorNorm_hasOperatorGrowthBound
    (n : ℕ) (h : 0 < n) : … := by
```

That line ends immediately after the name, so the pattern never matches it.

The predicate asserts "a delimiter follows the name" as a proxy for "the name ends here" — but end-of-line ends it too.

## Reproduction

```lean
namespace Demo
theorem ends_the_line
    (h : True) : True := h
theorem has_a_trailing_space (h : True) : True := h
end Demo
```

`lean_local_search("has_a_trailing_space")` → found. `lean_local_search("ends_the_line")` → `[]`.

## Blast radius

Measured on the SK_EFT_Hawking Lean corpus, 2026-08-17:

| | count |
|---|---|
| declaration lines under `SKEFTHawking/` | 25,955 |
| whose name ends the line | **1,868** |
| share unreachable | **7.2%** |

Roughly one declaration in fourteen. The cost is not only a failed lookup: `lean-worker` agents are instructed to search before proving and to reuse rather than re-prove, so a silent empty reads as *nothing to reuse* and sends a worker to re-prove a theorem that already exists.

## Fix

`(?:\s|:)` → `(?:\s|:|$)`, in `8b44970`. Regression test in `tests/unit/test_search_utils.py` asserts both directions, with a control case that fails first if the fixture stops exercising the search path. 272 unit tests pass.

## Upstream

Present in upstream `oOo0oOo/lean-lsp-mcp` through v0.29.0 (line 208), unchanged. Filed here rather than upstream because it is unclear how far our line-continuation style generalizes to their users — worth offering upstream if it does.
