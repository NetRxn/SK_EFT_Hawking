# Mathlib bump playbook — repair patterns + process

**Read this before starting any Mathlib/PhysLib/toolchain bump.** Two parts, and the second is
the one that saves days:

- **§ Patterns** — the concrete v4.29.1 → v4.32.0 repair library. Version-specific, but the
  *shapes* recur: instance diamonds, transparency changes at `rw`/`simp`, `def`-vs-`abbrev`
  delta-unfolding, deprecated aliases stopping a simp set one step short. Skim it at the next
  bump even if the version pair differs.
- **§ Process rules for a bump** (at the bottom) — version-INDEPENDENT. These are the ones that
  cost real time here. Read them first.

## Provenance

Derived from the v4.29.1 → v4.32.0 bump executed 2026-07-28/29 across both repos:
Mathlib `5e932f97` → `81a5d257`, PhysLib `085dab8f` → `c4843367`, repl `v4.29.0` → `v4.32.0`,
toolchain `leanprover/lean4:v4.29.1` → `v4.32.0`. ~23 waves, ~150 files, 430+ errors.
Outcome: public `lake build SKEFTHawking.ExtractDeps` 10785/10785 green, private 8860/8860 green,
`validate.py` 49/49, zero `sorry`, zero new axioms, zero statements weakened.

The library below was accumulated live during that bump. **Try these before deriving anything.**
Ordered roughly by yield.

## Patterns

## The two highest-yield rules

**P1 — MASTER RULE. v4.32 unifies instance paths less eagerly at `rw`'s *reducible*
transparency.** When `rw [lem]` fails on a pattern that is visibly present, the lemma usually
still applies as a **term** at default transparency. Escape to term mode rather than fighting it:
`(congrArg f eq).trans lem` · `congrArg (· * X) lem` · `h.trans_eq (by ring)` ·
`exact h.congr_deriv (by ring)` · explicit `congrArg₂` · or plain `exact` (defeq often closes it).

**P1b — P1 also reaches DOT-NOTATION resolution, and it can fail *silently*.** With
`hBcl : LinearPMap.IsClosed B` (a plain `def` unfolding to `_root_.IsClosed ↑B.graph`),
`hBcl.closure_eq` used to reach the topological `IsClosed.closure_eq`. At v4.32 it resolves
differently: the `rw` **succeeds** but produces a *different, wrong* goal, and the error surfaces
one tactic later on an unrelated lemma. Fix: bind the type you mean and use that —
`have hBset : _root_.IsClosed (↑B.graph : Set (H × H)) := hBcl`.
⚠ Verified 2026-07-28: this is NOT a new-namesake collision. Both `IsClosed.closure_eq`
declarations (`Order/Closure.lean`, `Topology/Closure.lean`) and `LinearPMap.IsClosed`'s
definition are **byte-identical at v4.29.1 and v4.32** — so do not go hunting for a newly-added
lemma. It is the reducibility change in P1 applied to dot notation. Same escape: make it explicit.

**P1a — try bare `exact` FIRST.** It beat `simpa` / `convert` / `rw` at least eight separate
times across waves 1–2. Only build a chain if `exact` fails. Do not construct machinery you
don't need.

**P2 — `convert … using 1` now spawns INSTANCE-EQUALITY goals first** (on `≤`, on `HasDerivAt`,
on tensor/`MulOpposite.op` normalization), so a trailing `ring`/`simp`/`field_simp` fires on the
wrong goal and the real residual is left open. Replace with a closed `show` + named-rewrite
chain — *after* P1a fails.

## Tactic-behaviour changes

- **P3** — `congrArg` results now arrive **beta-reduced**, so a following `simp only … at h`
  makes no progress and is a hard error. Delete the line. Same for `rw [show (fun z => f z) a = 0 from rfl]`
  (drop the redex).
- **P4** — `simp` no longer unfolds `Function.comp` (add `Function.comp_def`) nor a
  partially-applied def (drop to `exact`; defeq closes it).
- **P14** — `simp` no longer reduces a `match` on a `ZMod n` literal. `decide` or `rfl` does.
- **P5 — heartbeat wall?** Look for `positivity` / `nlinarith` over a **matrix or operator norm**
  before assuming bad architecture. One such call ate an entire 200 000 budget and made every
  later step in the file report as a timeout. Swap for `linarith` + the `norm_nonneg` hypothesis
  already in scope. **NEVER add `set_option maxHeartbeats`** (Invariant #10).

## Instance diamonds — the recurring theme

- **P6** — diamonds beat `rw`/TC but not `exact`: bind the instance (`haveI hcs : … := ⟨…⟩`) and
  pass it **positionally** via `@f _ _ _ _ _ hcs _ …`; or ascribe a `have`'s type up front to
  force the goal's instances rather than TC's.
- **P12** — or pin the path by **named argument**:
  `UniformSpace.firstCountableTopology (uniformSpace := PseudoMetricSpace.toUniformSpace) _`.
- **P7 — `erw` rescues an IRREDUCIBLE instance, not an ABSENT one.** If `erw` also fails on a
  visible pattern, stop trying transparency tricks and check whether the instance still *exists*.
  Confirmed gone: `LieRing (Matrix …)` (only `Bracket` survives → `simp only [Ring.lie_def]` then
  `noncomm_ring`/`abel`); `FirstCountableTopology (Matrix …)`.
- **RingQuot `Neg` diamond** — `-` at `Uqsl2Aff k` carries `RingQuot.instNeg`, no longer matched
  against the `Neg` from `HasDistribNeg`, so `neg_mul`/`mul_neg`/`map_neg` fail with the
  misleading "did not find the pattern" and `erw` does not help. Escape: name it as a **term**
  first (`have hneg : ∀ a, f (-a) = -(f a) := fun a => map_neg f a`) then `rw [hneg]`; or `grind`
  (works at default transparency). ⚠ `noncomm_ring` turns `-x` into an Int-`smul` with no
  `IsScalarTower` on RingQuot and leaves an unprovable residue — and rewrites *inside* `T (-2)`.
- **P8** — `LieRing.ofAssociativeRing` demoted to a `def`; re-enable with
  `attribute [local instance 100] LieRing.ofAssociativeRing`, as Mathlib's own file does.
- **P15** — `Matrix` has no `FirstCountableTopology` and the Pi one no longer matches. Two-step:
  `inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℂ))`, then apply
  `TopologicalSpace.Subtype.firstCountableTopology _` **explicitly**.
- **P13** — `Submodule.hasQuotient` may stop matching on a concrete module instance; pin with an
  instance alias. Watch for **new** v4.32 instances shadowing (e.g. `AddSubgroupClass.instZModModule`).

## `instance` declarations v4.32 now rejects — SYSTEMATIC (4 occurrences so far)

Lean 4.32's `checkImpossibleInstance` runs **unconditionally** (`Lean/Meta/Instances.lean`; skipped
only when the type `hasSorry`) — no option gates it, `synthInstance.checkSynthOrder` and
`checkBinderAnnotations` do nothing. It hard-errors on an `instance` with a non-instance binder
that appears in neither the return type nor an instance-implicit argument:
*"This instance has N arguments that cannot be inferred using typeclass synthesis"*.

Such a declaration **could never have fired by synthesis anyway**, so the fix is almost always
`instance` → `theorem` (or `@[reducible] def` when it must still be applied as a term), leaving
the statement, name and hypotheses byte-identical. **Before demoting, check every use site**: they
must already apply it explicitly (`haveI := foo hf`, or as a positional argument). Confirmed at:
`LDPLinearResponse.nonGaussianRateFunction_isLDPRateFunction`,
`SmithRegularValue.affineChartedSpace` (→ `@[reducible] def`),
`ManifoldRegularValue.instCompactSpace_mZeroLocus`, and the `LocPathConnectedSpace` alias case
(there the return type is a deprecated `def`, not a class — same hard error, different cause).

Wrapping the hypotheses in `Fact` is the only way to keep it an `instance`, and that **does**
change the signature — prefer demotion.

## The deep tail (waves 14–23) — patterns that only surfaced once earlier files went green

- **P16 — `simp` no longer delta-unfolds a plain `def`.** THE highest-yield tail pattern (25+ sites).
  It fires on a hypothesis holding the literal term but NOT on a goal that spells the same thing
  through the def, so the two sides end at different normal forms and the closing step fails.
  Two opposite fixes — pick by which side must move:
  * goal is folded, hypothesis unfolded ⇒ **name the def in the simp set**
    (`simpa [eH01, …]`, `simpa [zeroPt, zeroFiber]`);
  * goal must STAY folded ⇒ **drop the def from the set** (`simpa [phiLin, gen4]` →
    `simpa [phiLin]`, since `gen4` unfolded only in the hypothesis).
  Same cause for `abbrev`: it is already delta-reduced in the goal, so `simp only [thatLemma]`
  finds no pattern — re-fold by type ascription (`have h : … (realize4 τ) … := by rw [lemma]; …`).
- **P17 — TWO `EquivLike` instances for `LinearEquiv` in v4.32**
  (`LinearEquiv.instEquivLike` and `DFinsupp.instEquivLikeLinearEquiv`; confirm with
  `#check @DFinsupp.instEquivLikeLinearEquiv`). A goal and a hypothesis can carry different ones
  and **print character-for-character identically**. `simpa`'s closing step unifies at reducible
  transparency and cannot bridge them. Fix = P11: `simp only […] at h` then a bare `exact h`.
  ⚠ **When two types print identically, stop reading the message and diff them under
  `set_option pp.explicit true in`** — pipe both blocks to files and `diff` word-by-word. That is
  the only way to see it, and it takes one build.
- **P18 — `decide` now refuses a goal whose context carries free variables**, and the error names
  the fix: `decide +revert`.
- **P19 — the `AddSubgroupClass` sub/add diamond.** Subtraction on `↥p` carries
  `AddSubgroupClass.sub` while `map_sub` elaborates its own at `AddGroup.toSubNegMonoid.toSub`, so
  `rw [map_sub]` AND a bare `map_sub _ _ _` term both fail. `simp` normalizes across it: state the
  bridge as `have … := by simp`, then rewrite with it.
- **P20 — whnf budget from an EXPLICIT argument.** Passing a submodule explicitly to
  `Submodule.Quotient.mk_surjective` makes the unifier compare two fully-elaborated closed types
  through the `def`-wrapped `Homology` alias → deterministic timeout. Passing **`_`** leaves a
  metavariable to assign after one delta step. Generalizes P-"expected type drives unification":
  when a `def` alias wraps the type, supply LESS, not more. (Never `set_option maxHeartbeats`.)
- **P21 — bundled coercion vs eta-expanded lambda.** `ContinuousLinearMap.contDiff` gives
  `ContDiff … ⇑Complex.reCLM`; the goal wants `fun x => x.re`. Defeq only through `DFunLike`, which
  the closing step will not unfold, and a type ascription does NOT force it. Hand simp the
  funext-derived equation for the **unapplied** coercion:
  `simpa [show (⇑Complex.reCLM : ℂ → ℝ) = fun x => x.re from funext Complex.reCLM_apply] using …`.

| more v4.32 signature changes | |
|---|---|
| `Matrix.det_zero h` | `Matrix.det_zero` — `Nonempty` went explicit → **instance**-implicit |
| `continuous_id` | `continuous_id'` when the goal is `fun x => x` (simp no longer eta-contracts) |
| `LinearMap.BilinForm.isOrtho_def` rewrites | now redundant — membership arrives already unfolded to `B x y = 0`; delete the rewrite (`exact` closes by defeq) |

**⚠ `unfold latticeSig` is a v4.32 landmine (7 sites).** `latticeSig` is defined with
`toQuadraticForm'` while ~37 files state their API in `toQuadraticMap'`, so unfolding hands `omega`
two atom sets for one quantity ("a possible counterexample may satisfy…" listing `sigPos …Map'` and
`sigPos …Form'` as separate atoms). Fix = restate the hypothesis, or `show` the goal, in the
**statement's own** spelling — typechecks by defeq, no statement edit. All 7 vanish with the
scheduled whole-component rename.

## Diagnostic heuristics — read these when the error makes no sense

- **"Unknown identifier" for a declaration that demonstrably exists ⇒ look for a whnf timeout in
  that declaration's own STATEMENT.** An `_` for an explicit type argument that must be solved
  against a `noncomputable def` sends the unifier into the def body; the symptom surfaces
  downstream as a missing name. Fill the `_` explicitly.
- **A goal can be ill-typed at `instances` transparency, and then every `rw`/`simp` on it fails
  SILENTLY** with "made no progress" rather than a type error. v4.32 says so explicitly — *"The
  target expression is not type-correct under the `instances` transparency level"*. **Read that
  note; it names the real problem.** Fix by `unfold` (delta at default transparency) and staying
  at the CLM level rather than going pointwise.
- **Let the expected type drive unification.** Comparing two fully-elaborated *closed* types
  through a `def`-wrapped alias blows the whnf budget; ascribing the term to the alias leaves a
  metavariable, so the unifier takes one delta step and assigns. Instant.
- **P10 — a deprecated `alias` stops `simp only [oldName]` one delta step short.** It unfolds the
  alias but not the real def, so every downstream apply-lemma in that simp set silently goes
  unused → "made no progress" / "unused simp argument", which reads like your lemma is wrong when
  it isn't. Add the **new** name alongside. Distinct from a plain rename: the old name still
  elaborates.
- **P11** — `simpa`'s closing step no longer unifies through a typeclass-instance projection.
  Ascribe an intermediate `have` at the **simp-normal** type and close with a bare `exact`.

## Signature / name changes confirmed at v4.32

| old | new |
|---|---|
| `extDerivFun f x v` | `extDerivFun I f x v` (deprecated alias of `mvfderiv`; `I` now explicit) |
| `schwartzIncl` / `schwartzEquiv` / `schwartzSubmodule` | `schwartzIncl μ` / `schwartzEquiv μ` / **`SchwartzSubmodule`** (capital S, explicit measure — thread `MeasureTheory.volume`) |
| `DFunLike.coe_injective'` | `coe_injective` |
| `Real.exp_lt_exp_of_lt` | `Real.exp_lt_exp.mpr` |
| `Matrix.toQuadraticMap'` | `toQuadraticForm'` — ⚠ see boundary note below |
| `commutative_ring_iff_abelian_lie_ring` | `isMulCommutative_iff_isLieAbelian` (and `⟨mul_comm⟩` → `⟨⟨mul_comm⟩⟩`) |
| `NatTrans.naturality` + `congrFun` | `ConcreteCategory.congr_hom` |
| `LocPathConnectedSpace` | `LocallyPathConnectedSpace` (old is a deprecated *alias*, i.e. a `def` — an `instance` returning it is a hard error) |
| `Mathlib.Analysis.ODE.PicardLindelof` | existence theorems moved to `Mathlib.Analysis.ODE.ExistUnique` |
| `padicValRat.pow` | lost its `q ≠ 0` hypothesis; `q` now explicit |
| `Continuous.smul` | now concludes Pi-smul; `apply` no longer unifies — use `exact`, or `Continuous.const_smul` for a constant scalar |
| `HasDerivAt.hasFDerivAt.fderiv` | lands on `ContinuousLinearMap.toSpanSingleton ℝ 0`; tail lemma `ContinuousLinearMap.toSpanSingleton_zero ℝ` |

⚠ **`toQuadraticMap'` boundary — do NOT propagate this rename into theorem STATEMENTS.** The tree
is deliberately in a mixed state: `LatticeSignature` is converted, `BlockSignature` + ~37 files
still state their API in the old name. A partial rename breaks the interface (already tried and
reverted once). Fix simp *sets* per P10; bridge colliding conventions with a local `show`/`have`
inside the proof body. A dedicated whole-component pass is scheduled separately.

## Hard rules (unchanged, non-negotiable)

Kernel-pure `{propext, Classical.choice, Quot.sound}` · ZERO `sorry` · ZERO new project-local
`axiom` · no `maxHeartbeats` in proof bodies · never `ring`/`ring_nf` on non-commutative types ·
never commit `exact?`/`apply?` as a proof — name the lemma it resolved to.

**`native_decide`:** add **no new ones**. Note the tree already carries a large *gated* baseline
(525 occurrences / 47 files) tracked as `native_decide_decl_closure` in `docs/counts.json` under
ADR-002's ratchet — that surface is known and managed, not a defect. Do not treat encountering
one as a violation; just don't grow it.

## Statement edits

Proofs only. **Exception:** where an upstream signature change makes a statement uncompilable as
written (the explicit `I`, the explicit measure), make the minimal meaning-preserving edit and
**call it out** in your report. If a statement genuinely cannot be proven as written, **STOP and
report** rather than weakening it.

## Search discipline

`lean_leansearch` / `loogle` / `leanfinder` query a **hosted Mathlib snapshot that is NOT our
pin** — their hits are *candidates*, not facts. Confirm every one with `lean_local_search` before
use. Search the concept **stem**, never a guessed full name, and never a `^theorem` grep anchor
(blind to `lemma`).

**Grep the PINNED Mathlib source in `.lake/packages/mathlib/` — it is the ground truth.** It
settled every signature question in waves 14–23 in one command, and it shows Mathlib's own idiom
for the lemma, which is usually the fix you want (e.g. `Matrix/PosDef.lean`'s
`simpa [toQuadraticForm', toLinearMap₂'_apply']` was exactly the missing simp set). Note some
instances are **auto-named** and grep-invisible in source — ask Lean directly with `#check @Name`
in a scratch file run through `lake env lean`.

## Process rules for a bump (learned the hard way here)

1. **Read persistent errors from the BUILD LOG, never a standalone `lake env lean`.** A per-file
   check elaborates against whatever oleans exist, so it can report a file clean while the full
   build still fails on it. Use a standalone check only to confirm a fix you just made.
2. **The tail reveals itself incrementally.** Each green wave unblocks deeper modules that were
   never elaborated before, so "N errors left" is a floor, not an estimate. Ten waves ran here
   after the build first looked nearly done.
3. **When a pattern repeats, `grep` the whole tree for it BEFORE the next build** — do not fix one
   file per wave. Sweeping `unfold latticeSig`, `apply Continuous.smul`, and
   `simp [Matrix.toQuadraticMap'` up front would have saved several full rebuild cycles. When the
   sweep shows sites that are still green, note that mixing alone is not sufficient to break — but
   fix every *unbuilt* one in the same wave rather than waiting for it to surface.
4. **Always `cd` with an absolute path in a build command.** A bare `lake build` inherited a cwd
   left inside `.lake/packages/mathlib` and cloned Mathlib's own deps there (1.0 GB of nested
   packages) while reporting a cheerful success.
