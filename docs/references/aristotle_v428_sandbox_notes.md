# Aristotle v4.28.0 sandbox — standing submission note

Auto-prepended to every Aristotle submission prompt by `src/core/aristotle_submit.py`
(`submit_async`). This is **append-only knowledge**: what we have learned about
building this project in Aristotle's v4.28.0 sandbox. Editing this file changes
future submission prompts; it touches **no project source** — our code stays on
v4.29.1 deliberately (see ADR-006 Amendment B). The point is to hand Aristotle the
*down-shift knowledge* up front so it spends budget on the mathematics, not on
re-deriving the environment — without us maintaining a parallel v4.28 code shadow.

---

## Environment (read first)

- Aristotle's sandbox is provisioned for **Lean / Mathlib v4.28.0**: the vendored
  dependencies are prebuilt at v4.28.0 (mathlib `8f9d9cff`, with Batteries / Aesop /
  Qq at their v4.28.0 revs). This project pins **v4.29.1** (mathlib `5e932f97`).
- The sandbox's v4.29.1 toolchain may be **incomplete** (missing oleans), so asking
  lake to rebuild our v4.29.1 deps from source can fail. **The reliable path is to
  align `lean-toolchain` to `leanprover/lean4:v4.28.0` and use the vendored v4.28.0
  dependencies as-is** — do NOT rebuild mathlib / Batteries from source. Changing the
  root toolchain to match the vendored deps revalidates the entire prebuilt dep tree
  (mathlib + Batteries + Aesop + Qq) in one move.
- This is **environment repair only**. Never change a theorem statement, signature,
  or docstring to make it build; only repair the prerequisite build-breaks.

## Known v4.28 ↔ v4.29 source-drift repairs (minimal, statement-preserving)

- **`SingularCohomologyMod2.lean` — `SimplexCategory` simp-normal-form drift.** Under
  v4.28 the v4.29 simp set does not reduce `(SimplexCategory.mk n).len` or
  `toOrderHom (mkHom f)`, so the downstream `omega`/`simp` goals fail. Repair each by
  `change`-ing to the defeq form and closing with `split_ifs <;> (first | rfl | omega)`,
  or by adding `SimplexCategory.len_mk` + folded `toOrderHom_mkHom` application lemmas.
  (The `change` form is toolchain-agnostic — works identically under v4.28 and v4.29.)
- **`preservesMonomorphisms_of_adjunction`** is `Functor.preservesMonomorphisms_of_adjunction`
  under v4.28 (affects `SingularRelativeHomologyMod2.lean` and similar adjunction sites).
- _(append new drift patterns here as they are encountered)_

## Policy (why we don't ship a v4.28 down-port)

- We keep our real source on **v4.29.1 on purpose** — we depend on ≥4.29 features, and
  down-shifting is the inverse of why we upgraded. A maintained v4.28 down-port would
  be a shadow that drifts further with every Mathlib/toolchain bump and breaks the
  moment a closure uses a genuine 4.29-only feature. We accept the per-submission
  environment friction instead.
- If a closure genuinely requires a 4.29-only feature with no 4.28 path, it may simply
  not be Aristotle-doable on the 4.28 sandbox — close it ourselves via the MCP loop.
- If Aristotle closes a goal using a v4.28 construct that would be cleaner / faster /
  more elegant in v4.29 (e.g. a tactic improvement), we upgrade it **case-by-case at
  graft time** — never by down-shifting our source.
