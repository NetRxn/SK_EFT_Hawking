# Lean proof-mechanics friction catalog

A symptom-indexed catalog of recurring tactic/elaboration frictions in this project's hand-rolled
substrate (singular homology, RingQuot algebras, EuclideanSpace, quotient homology). **On a recurring
error, grep this file for the symptom string** rather than re-deriving the fix. Each entry: SYMPTOM →
FIX. Add a new entry the *first* time a pattern recurs (don't re-solve it per-instance).

## Quotients / instance synthesis / coercions

- **`Submodule.Quotient.mk` (from `mk_surjective`) doesn't `rw`-match `RelativeHomology.mk` /
  `QHomology.mk`.** Those are non-reducible defs. → `rw [show <Submodule.Quotient.mk form> = <RHS> from
  <lemma-with-RelativeHomology.mk>]` — the map's *domain* pins the submodule. A standalone
  `(Submodule.Quotient.mk a, …)` has an ambiguous `?p`.
- **Homology-class equality needs `relHomology_mk_eq_of`, not chain equality** — `[mk_U wc] = [↑a]` when
  they differ by a boundary; don't try to prove the chains equal.
- **Quotient/instance-synthesis friction recurs across a proof family (E1/E2/E3-style).** After resolving
  it once, build a **helper-lemma family upfront** (`relHomology_mk_eq_of`, the `show … = … from <mk-lemma>`
  shape) rather than re-patching each member.
- **Instance synthesis fails mixing a `QChain`-style wrapper vs the raw quotient.** Make the wrapper a
  reducible `abbrev` — **BUT** then structural tactics over-unfold: `ext c` drives through the reducible
  quotient → use `refine LinearMap.ext fun c => ?_` to control unfolding. (Reducibility changes how `ext` /
  `simp` / `unfold` behave at the proof site — test downstream immediately and note the expected unfolding.)
- **Private helper not exported** (e.g. `eq_of_add_eq_zero_two` in another module) → **inline** the small
  proof locally (`neg_eq_of_add_eq_zero_left` + `ZModModule.add_self`) rather than blocking. If it recurs at
  scale, export it.

## Rewrites / motives

- **`rw [add_comm]` / `add_assoc` / `ZModModule.add_self` (no args) match the NAT degree `k+1`, not the
  chain add → "motive is not type correct".** **Always pin the arguments** of generic rewrites on
  subtype-with-proof goals. After the *first* such instance, pin the target idiom (fully-qualify + pin the
  argument) instead of patching per-instance.
- **`rw` on a `⟨val, dependent-proof⟩` subtype breaks the motive.** `change` / `show` to reduce the coercion
  first, then rewrite.
- **`set c := …` does NOT auto-fold later-appearing occurrences of its RHS** (e.g. `(↑p) 0`). Use
  `change c ↑a = c ↑b` (defeq) to re-fold before applying lemmas stated about `c`.
- **`rw [hUc_eq] at (a.2 : ↑a ∈ Uᶜ)` fails "motive not type correct"** because `a`'s type depends on `Uᶜ`.
  Reformulate the lemma over `¬(0 < c p)` so `a.2` applies directly, instead of rewriting the membership.

## Char-2 / module (NOT ring) algebra

- **`CharTwo.*` lemmas fail** — chains here are ℤ/2-**modules**, not rings. Use `ZModModule.add_self` /
  `neg_eq_of_add_eq_zero_left`. Char-2 `a+u=b+v` from `u+v=a+b`: `(a+u)+(b+v)=(u+v)+(a+b)=0` via
  `abel`+`ZModModule.add_self`, then `←sub_eq_zero`+`neg_eq_of_add_eq_zero_left`.
- **`ring` fails on a scalar-product `•`** (e.g. from `gauge_smul_of_nonneg`) — `•` is not ring
  multiplication. Use `smul_eq_mul` + `inv_mul_cancel₀`, or explicit `smul` rewrites.
- **Non-commutative ring types** (`Uqsl2Aff`, `Uqsl3`, Clifford): `noncomm_ring`, never `ring`/`ring_nf`.
- **`RingQuot` types:** `rw` "did not find pattern" → `erw` (pipeline `rw` runs at `.reducible`).

## EuclideanSpace / PiLp

- **Coordinate eval continuity** `Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i)` → `by fun_prop`
  (NOT `continuous_apply` — the PiLp wrapper blocks it).
- **`Subsingleton (EuclideanSpace ℝ (Fin 0))`** — `inferInstance` takes the wrong Pi path (`Subsingleton ℝ`).
  Use `⟨fun a b => by ext i; exact Fin.elim0 i⟩`.
- **`ext z` over-applies through a `ContinuousMap`-to-EuclideanSpace into coordinates → `Subsingleton ℝ`.**
  Use `ContinuousMap.ext fun z => …` (one level) instead of bare `ext`.
- **Norm in `Fin 1`:** `‖x‖ = |x 0|` via `EuclideanSpace.norm_eq` + `Fin.sum_univ_one` + `Real.norm_eq_abs`
  + `sq_abs` + `Real.sqrt_sq_eq_abs`; then `abs_eq` for `±1`. `EuclideanSpace.single_apply`/`norm_single`
  are deprecated → `PiLp.*` (warnings only, still compile).

## Scoping / sections / anonymous constructors

- **Free-variable capture: inline `by` in an anonymous constructor `⟨_, by …⟩`** → "unknown free variable".
  **Extract the tactic proof to a named lemma.**
- **Shadowed hypotheses** in a nested scope (e.g. `homotopyComplA`) → rename explicitly.
- **Section `variable`s are NOT auto-included** on a theorem whose *type* doesn't mention them → pass them
  explicitly per-lemma. `local notation` with set-builder can break `quotPrecheck`.
- **`unitInterval` bounds** `t∈[0,1] ⟹ 0 ≤ t-0` need explicit `sub_nonneg`; `omega`/`linarith` don't bridge.
- **`unknown constant`/`unknown identifier` for a cross-module map** (`Homology.map`, `RelativeHomology.map`)
  → the `*.map` lives in a *Functoriality* module you didn't `open` (`SingularFunctoriality`,
  `SingularRelativeFunctoriality`). `lean_local_search`/`lean_hover_info` the identifier BEFORE writing a
  cross-module body, then add the missing `open`.

## simp / unfolding

- **`simp` doesn't unfold module-local composition defs** (`inclMap`/`pushMap`) → mark `@[simp]` or add to a
  local simp-set, or do the manual rewrite across each slice.

## Tooling / environment

- **`lake build` from the wrong cwd** (cwd resets between Bash calls) → `cd …/lean` first; assert cwd before
  building.
- **`lake build` fails with a Physlib (or other dep) revision mismatch** after an import-graph change
  re-resolves the dependency graph → `git -C lean/.lake/packages/Physlib checkout -f <manifest pin>` (the
  guardrail-safe re-pin; `reset --hard`/`clean` are denied by the auto-mode classifier). The pin lives in
  `lean/lake-manifest.json`. Re-triggers each time the import graph changes — re-pin, don't fight it.
- **MCP `lean_goal` reports the DECLARATION line, not the `sorry` line** — query at the line containing the
  `sorry` tactic itself, not the `theorem`/`def` header.
- **`Σ` is reserved (Sigma)** — never use it in identifiers (`hΣ` → `hsum`).
- **The word "push" in a `git commit` command** (math `pushMap`/push-out) can trip the **Claude Code
  permission classifier** — it reads "push" as a possible `git push` and prompts/holds. It is a
  tool-permission heuristic, **NOT** the pre-commit hook (which greps only the exact private dir name and
  never mutates staging). Reword the math term in the commit *command*, or confirm the action. Same
  phantom-guardrail family as the worktree-reset denial (see `parallel-worktrees.md`).
- **"do nothing" / "never executed" tactic warnings** → the proof assumed a goal state that closed
  prematurely. Use `lean_goal` at that line and restructure; don't defer — it cascades.

## ℝP³/Euclidean-carrier + Hmap batch (2026-07-21, wt3 termination-input block)

- **`Fin.insertNth` on constant families** — implicit-family unification fails → pin `(α := fun _ => ℝ)`; its application lemmas mismatch implicitly, close with `simp` not `rw`.
- **Higher-order `rw` on `Hmap`-shaped functoriality lemmas NEVER matches** (reconfirmed twice) → instantiate the lemma as a `have` with explicit args and chain with `.trans`; defeq does what the syntactic matcher can't.
- **Maps INTO `WithLp`/EuclideanSpace** → `continuous_induced_rng.mpr` + a `show` line pinning the family (application side: `fun_prop`, already recorded).
- **Pin-name drift on this Mathlib pin**: `Set.eq_empty_iff_forall_notMem`, `convex_halfSpace_gt/lt` (capital S), `Equiv.toHomeomorphOfContinuousOpen`; `Finset.not_mem_empty` gone (use `simp`); `push_neg` deprecated.
- **`cases hb : ε j` AFTER the goal specialized** breaks `rw` with the pre-case hypothesis → extract per-`Bool` helper lemmas (e.g. `isOpen_signSet`/`convex_signSet`) instead of casing inline.
- **ℕ-vs-ℤ numeral-smul mismatch** (`2 • c = 2 • c` refusing rfl) → `rw [two_smul, two_smul]`.
- **`sub`'s implicit `TopCat` won't infer from a bare `Set`** → ascribe `(… : Set ↑Xtop)` at use sites.

## K7 fiber-flow batch (2026-07-21, wt3 #299)

- **`attribute [irreducible]` on ℝ-arithmetic geometric defs** (flow scalars/disks) after banking their lemmas — otherwise `Continuous.comp` unification whnf-dives into real arithmetic (deterministic timeout). Same medicine as homology equiv-builders.
- **`sub` needs `(X := <TopCat>)` as a NAMED argument** — a `(… : Set ↑X)` ascription inside another named argument cannot be inverted (`Set K =?= Set ↑?m`).
- **Type ascription `(h : P')` on a defeq hypothesis is a NO-OP for `linarith`** (the fvar keeps its stored type) → `have h' : P' := h`.
- `squeeze_zero_norm`'s bound is named `a` (not `g`); `ContinuousAt.min` doesn't exist — use `Filter.Tendsto.min`.
- **Junk-value bonus**: `1/0 = 0` makes radial flow scalars like `min(1/‖w‖, 2−t)` total with the CORRECT value at the fiber origin; continuity there via `squeeze_zero_norm`.

## Q-side transfer batch (2026-07-21, wt3 #300)

- **Stale-import snapshots**: after rebuilding a dependency's olean, an already-open file's LSP worker keeps the OLD import environment — apparent type mismatches that survive touches. Only `lean_build` (LSP restart) clears them; do NOT debug those "errors" as real.
- **TopCat carrier defs**: keep the carrier a `def` (not `abbrev` — eager unfolding breaks `mapSimplex` unification) and build `C(X, X)` maps from functions + continuity lemmas pre-proven at the SUBTYPE level (instance resolution won't unfold `↑Xtop` for `SMul` etc.).
- **`fin_cases` + simp/rw don't mix**: `fin_cases` produces `⟨0,⋯⟩`-form Fin literals that keyed matching won't unify with OfNat-literal lemmas — use match-based theorem definitions (`| 0, 1 => by rw [...]`) or `exact`-dispatch.
- **`push_cast` on Circle-coe inverses**: normalizes `↑(z⁻¹)` to `(↑z)⁻¹` in the goal — normalize hypotheses too (`push_cast at h ⊢`) or `linarith` atoms mismatch.
- Pin renames: `Prod.dist_eq` named args are `x`/`y`; `ContinuousAt.max/min` absent — `Filter.Tendsto.max/min`; `div_le_div_iff` → `div_le_div_iff₀`; `le_or_lt` → `le_total`.

## Puncture-MV batch (2026-07-21, wt3 #301)

- **`attribute [local irreducible]` on flow-profile defs BEFORE any unification against them** — not just after banking their lemmas in the defining file. `ContinuousOn.comp_continuous`/`Continuous.comp` at such terms hit deterministic isDefEq/whnf heartbeat walls (the unifier dives into max/min/sqrt/• instance towers). Consume only through banked lemmas.
- **`hΣ` is an illegal binder name** — `Σ` is a notation token; the parse error surfaces far downstream as "unknown identifier".
- **`open Classical in` must PRECEDE the doc comment**, not follow it.

## hcross MV cup-Stokes peel batch (2026-07-21, wt1 #289 — harvested post-mortem)

- **UCT/`Module.Free` instance-key shape mismatch at `(0 + 1)`**: instance search asks for the LITERAL degree shape it was called with, so an existing `Module.Free ℤ (Homology X 1)` does NOT fire for a goal at `Homology X (0 + 1)`. Fix — register a second instance keyed at the un-reduced shape:
  `instance : Module.Free ℤ (Homology (Sph 2) (0 + 1)) := inferInstanceAs (Module.Free ℤ (Homology (Sph 2) 1))`.
  Bit twice in one session (`Sph 2`, `Apunc 2 u`). Expect it anywhere a dimension-reduction/suspension iso is applied at degree `n+1`.
- **A `sorry` in a `lean_goal` display during instance-synthesis failure is an LSP PLACEHOLDER**, not a project `sorry` (e.g. `h0 : sorry = 0`). Fix the failing instance and it evaporates — do NOT chase it as a soundness regression, and do NOT let a `grep sorry` over live goal output masquerade as a review.
- **`p.add q` vs `p + q` elaboration mismatch**: `rewrite` fails to locate `mapChainInt f (p.add q)` when the implicit degree unified to the projection form rather than the notation form. Fix: pin the implicit — `lemma (m := p + q) ...`.
- **Deep defeq chains blow `maxRecDepth` inside a big `have`**: extract a standalone lemma decorated `set_option maxRecDepth 4000 in` and route through an `_apply` lemma instead of the raw defeq chain. `maxRecDepth` is metaprogram DEPTH (permitted, 23-file in-tree precedent); `maxHeartbeats` is compute budget (banned in proof bodies). Worked example: `SphereProdCrossWitnessInt.coverInterHThreeEquivInt_mvDelta_fundClass`.
- **`@[simp]` bilinear-form `_apply` lemmas unfold before hand-proved hypotheses can fire**: a plain `simp [..., hαα, hββ, hβα]` unfolds `interFormInt` first and strands the named hypotheses. Fix: `simp only` with a narrow structural list (`Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'`), then close each `fin_cases` goal by hand with `exact h…`.
- **Verify a name's home module before trusting it** (`grep -n '^namespace'` on the source): `frontIncl`/`backIncl` are NOT in `SKEFTHawking.SingularCupInt` (that file extends `namespace SKEFTHawking.SingularCohomologyInt`); `Tor` lives in `KummerTorusStep`, not `TorusCrossPeel`. Also: the Int-cohomology side needs the Int `face`/`coboundary` shape, not the mod-2 `SingularCohomologyMod2.face` pattern.
- **Rebasing a hand-built embedding onto banked machinery can DELETE an argument, not just tidy it**: replacing a hand-rolled `eqVec`/`eqIncl` (explicit `EuclideanSpace.single` + norm computation) with `eqSeam := (equatorMapInv vN).comp (incl (n:=2))` made the non-degeneracy proofs fall out of `normalize_comp_incl` + `equatorMap_comp_equatorMapInv` "on the nose" — eliminating an entire winding-number argument. Look for the banked composite BEFORE hand-building a sphere embedding.
- Pin rename: `EuclideanSpace.single_apply` → `PiLp.single_apply`.

## Revival/harness batch (2026-07-21, all three slots)

- **Standalone `sleep` is blocked by the harness** — use `run_in_background: true` + polling, or `lean_diagnostic_messages` with an explicit `timeout`.
- **Shell: do not chain `sed -n` segments with `&&`/`echo ====` separators** — the chain dies as `=== not found` and only the first segment's output returns. Use `;` or separate calls. (Hit independently by two different workers the same day.)
- **Reviving a quota-killed worker: distill, don't resume.** Resume caps around ~400k tokens, which silently truncates a large worker's context. Instead send a cheap Explore agent through the dead worker's subagent JSONL (`~/.claude/projects/<slug>/<sid>/subagents/agent-<taskid>.jsonl`) for a resume dossier — landed decls with file:line, exact in-flight state, settled route decisions, dead ends, and whether anything reached disk — then fold it into the replacement's brief as a "§A HARVESTED — do not re-derive" block. Three-for-three clean; replacements start writing Lean on turn one.

## K7 torsion / quotient-coordinate batch (2026-07-21, wt3 KummerK3TorsionFree)

- **`Submodule.Quotient.mk x` vs `N.mkQ x` are defeq but NOT `rw`-interchangeable.** State `@[simp]` bridge lemmas in the `Quotient.mk` form — that is the form `Submodule.Quotient.mk_surjective` hands you, so it is what downstream goals actually contain.
- **Reach for structural `simp only` before `rfl` on MV-composite definitions.** `rfl` on `exceptionalEmbed v = Σ₂ (0, …)` blows `maxRecDepth`; `simp only [exceptionalEmbed, LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_toLinearMap]` is instant. The composite's defeq chain is deep even when the structural rewrite is one step.
- **A `DecidableEq` on an index type may be a SCOPED instance** (`DecidableEq EIndex` in `KummerK7Delta1Image`): a selective `open Ns (name)` does NOT bring it in — you need `open scoped Ns`. Symptom is a `Decidable`-synthesis failure at a point where the type is obviously decidable.
- **Search the PROJECT, not the file, before declaring a lemma missing.** A worker reported integral pair-LES exactness at `Hₙ(X)` "absent" after scanning `SingularLocalHomologyInt.lean` (which holds the other two legs); it exists as `SingularSphereHomologyInt.exact_homIncl_homProjInt`, generic in `S`. Use `lean_local_search` on the lemma-shape prefix (`exact_homIncl`) — a one-file scan is not a project search, and "this infrastructure is missing" is a direction-shifting claim that must be traced before it is reported.

## ℤ-coordinate / generator batch (2026-07-21, wt1 SphereProdHemiUnitInt + SphereProdBasisIdInt)

- **When a coordinate iso ends in an arbitrary `Nonempty` choice, go coordinate-FREE.** `circleH1EquivInt` bottoms out in `augHInt_ker_punc1_iso_int.some`, so there is no concrete generator to land on and any "chase to the generator" plan is unimplementable. The right criterion: for ANY `e : M ≃ₗ[ℤ] ℤ`, a linear functional taking a unit value at `x` forces `IsUnit (e x)` (because `g : ℤ →ₗ[ℤ] ℤ` is multiplication by `g 1`). One lemma replaces the whole normalization chase.
- **`map_smul` fails instance synthesis on `LinearMap`/`LinearEquiv` over ℤ** (`MulActionHomClass (M →ₗ[ℤ] ℤ) ℤ M ℤ`). Pin it: `show f (c • x) = c • f x from f.map_smul _ _`.
- **The zsmul-vs-Module-smul diamond.** With `[AddCommGroup M] [Module ℤ M]`, a `(c : ℤ) • (x : M)` written in a STATEMENT elaborates through `SubNegMonoid.toZSMul`, which then refuses to unify with `LinearMap.map_smul`'s `DistribMulAction` path. **Fix: state the lemma over generic `[CommRing R] [Module R M]` and instantiate `R := ℤ`.** Worth doing pre-emptively for any ℤ-coefficient linear-algebra lemma.
- **Degree literals `0 + 1` / `0 + 2` survive `LinearEquiv.trans_apply`** on `dimReductionEquivInt`, and `simp only [Nat.zero_add]` does NOT fire on them. Use a `show` restating the whole goal at reduced degrees (defeq). Cousin of the `Module.Free (0+1)` instance-key law above — the un-reduced literal is a recurring shape in this substrate.
- **`rw` inside `RelHomologyInt.mk ⟨_, proof⟩` gives "motive is not type correct".** Fix: `refine congrArg (RelHomologyInt.mk ..) (Subtype.ext ?_)` FIRST, then `show` the value-level equation, then `rw`.
- **Nested `LinearEquiv.ofBijective` inside a `.trans`**: one `rw [LinearEquiv.ofBijective_apply]` unfolds only the outer layer — use `simp only [LinearEquiv.ofBijective_apply, LinearMap.comp_apply]`.
- **Never state an auxiliary `X.det = v` lemma to feed `IsUnit X.det`** — `rw` fails to locate `X.det` inside `IsUnit X.det`. State `IsUnit X.det` directly.
- **A recorded "pinned only up to X" obstruction may not BIND.** The basis-ID wall said `deltaGen` is a choice pinned only modulo `sumInto`, so its factor-projections are not forced. But the ambiguity lived exactly in the KERNEL of the projection being used (`sumInto_prodSnd`), and the projection's value was pinned by counting (split-surjectivity + spanning), not by normalization. Before accepting a recorded obstruction, check whether the ambiguity survives the specific map you apply.

## Implicit-TopCat elaboration wall (2026-07-21, wt3 KummerPairTubeSeparation) — HIGH VALUE

- **Pin the ambient `TopCat` implicit or the elaborator diverges.** Any call taking `{X : TopCat}` implicitly — `homProjInt`, `homIncl`, `connectingInt`, `ambIncl`, `excisionEquivInt`, `seamHomologyEquivInt`, `excisionMap_homProjInt`, `Homology.mapInt_ambIncl`, the `exact_*` family — must be written with the implicit given: `(X := KummerK3top)`, `(X := ESub)`. Left to unification it has to solve `↑?X ≟ KummerK3`, fails first-order, and then unfolds the `RelHomologyInt` module instances into a **200k-heartbeat `isDefEq` wall**.
- **The diagnostic symptom: `(deterministic) timeout at isDefEq` on a one-line `def` that is a plain `LinearMap.comp`.** If a trivial definition times out, suspect an unpinned implicit, not proof architecture.
- **This is NOT a heartbeat-architecture problem and `maxHeartbeats` would be the WRONG fix** — the project rule ("a heartbeat wall means wrong proof architecture, decompose") does not apply to an elaboration-unification wall. Pin the implicit instead. Worth knowing before reaching for a decomposition that won't help.
- Corollaries: `show` on such a term also walls; `simp only [<def>, LinearMap.comp_apply]` is the reliable unfolder; and `simp only` beats `rw` for `LinearEquiv.map_eq_zero_iff` chains (which hit `maxRecDepth` instead).
