"""Statement-level substrate analysis — ADR-009 Phase 2 (split 2026-08-04).

Does a theorem's STATEMENT prove anything? `formula_grounding`,
`vacuous_statement_audit` and `nogo_substrate_integrity` — the three checks that
judge the ELABORATED TYPE from `lean_deps.json` rather than a name, a proof body
or paper prose.

WHY THIS IS A SEPARATE MODULE FROM `lean_substrate`
---------------------------------------------------
`lean_substrate` measured 1,079 lines, failing D1's *readable in one pass*. The
seam is the one that module's own header already articulated: the **type-thinness
classifier** is name-agnostic and tactic-agnostic *by design*, because
`proxy_body_audit` is name-gated and excludes `norm_num`/`decide` bodies, so a
theorem whose STATEMENT proves nothing slips past it. That classifier plus its
three consumers form a cohesive unit; what remains in `lean_substrate` is
name-gated, body-gated, prose-gated and registry-gated.

Measured before the move: the two halves share **zero** module-level names, and
the split is ~493 moved / ~586 remaining. Same method as the three Phase-2 splits
(`lean_substrate`/`lean_toolchain`, `papers_prose`/`prose_lean_refs`,
`bundles_readiness`/`reviews`) — seam first, size second.

⚠️ NOTE ON SIZE AS A CRITERION. 1,079 was not an outlier: `citations` (965) and
`bundles_readiness` (904) sit in the same band. This split is justified by
COHESION, not by line count alone; the reduction is a consequence.

FIVE OF THIS MODULE'S NAMES ARE IN THE FROZEN EXTERNAL SURFACE
---------------------------------------------------------------
`_THIN_HARD`, `_is_autogen_decl`, `_thin_type_label`, `_is_vacuous_identity_wrapper`
and `_parse_formula_lean_refs` are imported by name from `validate` by
`tests/test_substrate_integrity_gates.py`, as is `check_formula_grounding`.
`scripts/validate.py` re-exports every one of them from here (ADR-009 D2 item 8);
`tests/test_validate_public_surface.py` freezes the list.

MOVED VERBATIM. No body edited, no policy unified, no threshold retuned — the
only changes are this header and the import block (ADR-009 D4).
"""
from __future__ import annotations

import re
from typing import List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1e: Formula content-grounding (R1, Invariant #4 with teeth)
# ═══════════════════════════════════════════════════════════════════════

# ═══════════════════════════════════════════════════════════════════════
# Type-thinness classifier (ADR-004 reconcile #45/#54/#25/#14) — shared by
# `vacuous_statement_audit` and the `formula_grounding` hardening. Operates on
# the ELABORATED type from lean_deps.json (name-agnostic, tactic-agnostic), so
# it catches statements that prove nothing regardless of the proof tactic or the
# theorem's name — the gap that let bare-arithmetic / reflexive theorems slip the
# name-gated, norm_num-excluding `proxy_body_audit`.
# ═══════════════════════════════════════════════════════════════════════

# Tokens that carry NO physics content (operators, relations, numeric base types,
# logical connectives). A statement whose ONLY identifiers are these (+ numeric
# literals) is a closed decidable fact — "ground arithmetic dressed as physics".
_ARITH_TOKENS = frozenset({
    "Eq", "Ne", "GT.gt", "LT.lt", "LE.le", "GE.ge",
    "HMul.hMul", "instHMul.hMul", "HAdd.hAdd", "instHAdd.hAdd",
    "HSub.hSub", "instHSub.hSub", "HDiv.hDiv", "instHDiv.hDiv",
    "HPow.hPow", "instHPow", "Neg.neg", "OfNat.ofNat", "OfScientific.ofScientific",
    "Nat", "Int", "Real", "Rat", "ℝ", "ℕ", "ℤ", "ℚ",
    "And", "Or", "Iff", "Not", "True", "False", "Prop",
})
_NUMLIT_RE = re.compile(r"^-?\d+(\.\d+)?(e-?\d+)?$", re.IGNORECASE)
_TYPE_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
# A "simple" Eq-argument = a single token with no internal structure (numeric
# literal or a bare identifier / bound variable). Reflexive `Eq X X` is reliable
# ONLY for simple args: a COMPOUND arg (`Eq (f a) (f a)`) may be a FALSE reflexive
# because lean_deps' pretty-printed type ELIDES implicit args — e.g.
# `sigPos_cast_pos : … sigPos (A.map (Int.cast:ℤ→ℝ)) → … sigPos (A.map (Int.cast:ℤ→ℚ))`
# prints both sides as `sigPos (A.map Int.cast)` (the ℝ/ℚ codomain is elided), so a
# genuine ℝ→ℚ transfer LOOKS reflexive. Restricting to simple args removes this
# whole elision false-positive class (reconcile 2026-06-13).
_SIMPLE_ARG_RE = re.compile(r"^-?[\w.]+'?$")
_THIN_HARD = {"True", "reflexive (X=X)"}


def _top_tokens(s: str) -> List[str]:
    """Split into top-level tokens (bracket-balanced groups or maximal
    non-space runs), respecting ()[]{}⟨⟩."""
    toks, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨":
            depth += 1; cur += ch
        elif ch in ")]}⟩":
            depth -= 1; cur += ch
        elif ch == " " and depth == 0:
            if cur:
                toks.append(cur); cur = ""
        else:
            cur += ch
    if cur:
        toks.append(cur)
    return toks


def _top_arrow_split(s: str) -> List[str]:
    """Split on top-level `→` (function arrows), respecting brackets."""
    parts, depth, last, i = [], 0, 0, 0
    while i < len(s):
        ch = s[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and ch == "→":
            parts.append(s[last:i].strip()); last = i + 1
        i += 1
    parts.append(s[last:].strip())
    return parts


def _strip_leading_binders(t: str) -> str:
    """Drop leading `∀ … ,` / `∃ … ,` binder groups to reach the proposition."""
    t = t.strip()
    while t.startswith("∀") or t.startswith("∃"):
        depth, ci = 0, None
        for i, ch in enumerate(t):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif ch == "," and depth == 0:
                ci = i; break
        if ci is None:
            break
        t = t[ci + 1:].strip()
    return t


# Lean/Mathlib compiler-EMITTED lemmas (congruence, constructor, recursor,
# equation lemmas) carry trivial/structural types by construction and are NOT
# authored claims — exclude them (e.g. `Padic.congr_simp`, `Foo.mk.congr_simp`).
_AUTOGEN_SHORT = frozenset({
    "congr_simp", "congr", "injEq", "mk", "rec", "recOn", "casesOn", "below",
    "brecOn", "ind", "binductionOn", "noConfusion", "noConfusionType",
    "sizeOf_spec", "eq_def", "eq_mp", "eq_mpr", "fst", "snd",
})
_AUTOGEN_RE = re.compile(r"^(eq|proof|match|fun)_\d+$")


def _is_autogen_decl(name: str) -> bool:
    short = name.split(".")[-1]
    return (short in _AUTOGEN_SHORT or bool(_AUTOGEN_RE.match(short))
            or ".mk." in name or name.endswith(".congr_simp"))


def _thin_type_label(type_str: str):
    """Classify a declaration's elaborated type as content-thin, or None.

    Returns a label string; `label in _THIN_HARD` ⇒ unambiguously vacuous
    (hard-fail). `'ground-arith'` ⇒ closed numeric fact (advisory — the class
    legitimately mixes vacuous physics-dressing with real counting identities
    like `4*5/2 = 10`, with no syntactic separator). Operates on the elaborated
    lean_deps type. Order: True ▸ reflexive ▸ ground-arith.

    NOTE type-based `P→P` (hypothesis-return) detection is DELIBERATELY omitted:
    lean_deps elides implicit args, so a genuine transfer `P_ℝ → P_ℚ` prints as
    `P → P` (e.g. `sigPos_cast_pos`). The genuine `P→P` tautologies are caught
    body-wise by `proxy_body_audit` (identity-return), which is elision-immune."""
    if not type_str:
        return None
    t = type_str.replace("\n", " ").strip()
    while "  " in t:
        t = t.replace("  ", " ")
    if t == "True":
        return "True"
    core = _strip_leading_binders(t)
    concl = _top_arrow_split(core)[-1].strip()
    # reflexive `Eq X X` (prefix) / `X = X` (infix) — SIMPLE args only (a compound
    # arg may be a pretty-print elision false-reflexive; see `_SIMPLE_ARG_RE`).
    toks = _top_tokens(concl)
    if len(toks) == 3 and toks[0] == "Eq" and toks[1] == toks[2] \
            and _SIMPLE_ARG_RE.match(toks[1]):
        return "reflexive (X=X)"
    if len(toks) == 3 and toks[1] == "=" and toks[0] == toks[2] \
            and _SIMPLE_ARG_RE.match(toks[0]):
        return "reflexive (X=X)"
    # ground arithmetic: conclusion's only identifiers are operators/literals
    leftover = [x for x in _TYPE_IDENT_RE.findall(concl)
                if x not in _ARITH_TOKENS and not _NUMLIT_RE.match(x)]
    has_rel = (any(r in concl for r in ("Eq", "GT.gt", "LT.lt", "LE.le", "GE.ge", "Ne"))
               or any(op in concl for op in ("=", "<", ">", "≤", "≥")))
    if has_rel and not leftover:
        return "ground-arith"
    return None


def _is_vacuous_identity_wrapper(type_str: str) -> bool:
    """True iff the elaborated type is a DOUBLY-vacuous identity wrapper: an
    implication `P → P` whose antecedent equals its consequent AND that shared
    `P` is itself a reflexive equality `Eq X X` / `X = X`. This is the
    `dd_simples_count` evidence-laundering shape (`… (h : Σ = Σ) : Σ = Σ := h`
    — returns its hypothesis, proves nothing).

    Requiring the reflexive body is what makes this false-positive-free: a
    genuine transfer `P_ℝ → P_ℚ` also prints `P → P` after implicit-arg elision
    (the reason `_thin_type_label` omits bare `P→P`), but there `P` is a
    substantive proposition, not `Eq X X`. Only the reflexive-body case is
    unambiguously content-free."""
    if not type_str:
        return False
    core = _strip_leading_binders(type_str.replace("\n", " ").strip())
    parts = _top_arrow_split(core)
    if len(parts) < 2 or parts[-1].strip() != parts[-2].strip():
        return False
    toks = _top_tokens(parts[-1].strip())
    return ((len(toks) == 3 and toks[0] == "Eq" and toks[1] == toks[2])
            or (len(toks) == 3 and toks[1] == "=" and toks[0] == toks[2]))


# Bare definitional closers: an `rfl`-family proof of an equality means the two
# sides are DEFINITIONALLY equal (the theorem unfolds a definition, deriving
# nothing). `simp`/`norm_num`/`decide` are deliberately NOT here — those can
# discharge substantive computations.
_BARE_RFL_RE = re.compile(r"^(by\s+)?(exact\s+)?(rfl|Iff\.rfl|Eq\.refl(\s+\S+)?)$")


def _lean_decl_proof_body(short_name: str, module: str):
    """Normalized proof body of ``short_name`` in its Lean ``module`` file, or
    None. ``module`` is the lean_deps form ``SKEFTHawking.<Path.To.Module>`` and
    maps to ``_H.LEAN_DIR/<Path>/<To>/<Module>.lean``. Reads a single file."""
    if not module:
        return None
    try:
        from build_graph import _scan_lean_theorem_bodies
    except Exception:  # pragma: no cover - import guard
        return None
    segs = str(module).split(".")
    if segs and segs[0] == "SKEFTHawking":
        segs = segs[1:]
    if not segs:
        return None
    f = _H.LEAN_DIR.joinpath(*segs).with_suffix(".lean")
    if not f.exists():
        return None
    try:
        source = f.read_text()
    except (OSError, UnicodeDecodeError):
        return None
    for name, _ln, body in _scan_lean_theorem_bodies(source):
        if name.split(".")[-1] == short_name:
            return " ".join(body.split())
    return None


def _grounding_is_definitional(decl: dict) -> bool:
    """A grounding theorem is a 'definitional record' iff its elaborated type is
    a vacuous identity wrapper OR its Lean proof body is a bare `rfl`-family
    closer (definitional equality). Used by `formula_grounding` to keep the
    `FORMULA_GROUNDING_KIND` declarations honest."""
    if _is_vacuous_identity_wrapper(decl.get("type", "")):
        return True
    body = _lean_decl_proof_body(decl.get("name", "").split(".")[-1], decl.get("module", ""))
    return bool(body and _BARE_RFL_RE.match(body))


def _parse_formula_lean_refs(src: str) -> set:
    """Extract Lean theorem-name tokens from `Lean: …` docstring lines in
    formulas.py, dropping non-decl artifacts (file names, `pending`, fragments,
    all-caps matrix labels)."""
    refs = set()
    for m in re.finditer(r"Lean:\s*(.+)", src):
        line = re.split(r"[—–]\s|\s-\s", m.group(1))[0]  # drop trailing description
        for tok in line.split(","):
            tok = re.sub(r"\(.*?\)", "", tok).strip().rstrip(".").strip()
            if not re.fullmatch(r"[A-Za-z_][\w.]*", tok) or len(tok) <= 2:
                continue
            if tok.endswith(".lean") or tok == "pending" or tok.startswith("_"):
                continue
            if re.fullmatch(r"[A-Z][A-Z0-9]{0,4}", tok):  # matrix-element labels (K0E0)
                continue
            refs.add(tok)
    return refs


@register_check(
    "formula_grounding",
    "Every formulas.py Lean reference resolves to a real, non-placeholder theorem (Invariant #4, R1)")
def check_formula_grounding() -> CheckResult:
    """Content-grounding for Pipeline Invariant #4: each `Lean:` reference in
    `formulas.py` must resolve to a real Lean declaration that is NOT a
    `True`/placeholder stub (a formula must not be 'grounded' on a theorem that
    proves nothing — the δ_diss-class hazard, audit 2026-06-13 #14). Extends the
    7-pair name-presence `formulas` check to ALL ~390 references.
    HARD-FAIL: placeholder-grounded refs. ADVISORY: dangling (unresolved) refs —
    a stale-name drift backlog the gate surfaces (FormulaRefSweep follow-up)."""
    from src.core.constants import PLACEHOLDER_LEAN_NAMES
    formulas_path = _H.SRC_DIR / "core" / "formulas.py"
    # ⚠️ These were `TODO(semantic-review, ADR-009 Phase 3)` until 2026-08-04
    # (audit finding QI-15). Phase 3 is COMPLETE and its §Deferred item 4
    # explicitly DECLINED converting these sites wholesale: 5 are
    # optional-toolchain-absent, 3 advisory by design, 8 are this `lean_deps`
    # divergence kept VISIBLE on purpose, 2 are the annotated H1-silent sites.
    # A TODO pointing at a finished phase reads as unfinished work; the
    # population is frozen instead by `tests/test_cannot_measure_baseline.py`,
    # which fails both on a NEW silent PASS and on a converted site left stale
    # in the baseline.
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> PASS (see the note at
    # tracked_hypothesis_ledger; the eight loaders disagree).
    if not formulas_path.exists() or not _H.lean_deps_present():
        return CheckResult(passed=True, measured=False, details=[Detail("inputs", True, "formulas.py / lean_deps.json absent")])

    deps = _H.load_lean_deps()
    names, dotted, shorts, by_short, by_full = set(), set(), set(), {}, {}
    for d in deps:
        n = d.get("name", "")
        if not n:
            continue
        names.add(n); by_full[n] = d
        segs = n.split("."); shorts.add(segs[-1]); by_short.setdefault(segs[-1], d)
        for i in range(1, len(segs)):
            dotted.add(".".join(segs[i:]))

    refs = _parse_formula_lean_refs(formulas_path.read_text())

    def resolves(t):
        return t in names or t in dotted or t in shorts

    def decl(t):
        return by_full.get(t) or by_short.get(t.split(".")[-1])

    placeholder_grounded, dangling, thin_grounded = [], [], []
    for t in sorted(refs):
        if not resolves(t):
            dangling.append(t)
            continue
        d = decl(t)
        if not d:
            continue
        if d.get("type") == "True" or d["name"].split(".")[-1] in PLACEHOLDER_LEAN_NAMES:
            placeholder_grounded.append(t)
            continue
        # ADR-004 reconcile #14 (the real Wave-21 semantic audit): a formula must
        # not be "grounded" on a theorem whose CONCLUSION proves nothing — a
        # reflexive `Eq N N` / `P→P` tautology (the δ_diss-class hazard, where the
        # cited theorem merely mentions the quantity instead of relating it). The
        # 7-9-order δ_diss units bug hid precisely because grounding meant "a named
        # theorem exists", not "the theorem's conclusion pertains to the formula".
        # NOTE this is STRUCTURAL substance (the statement is non-tautological),
        # not full semantic "conclusion ⟹ float-computation" (undecidable); it
        # catches the prove-nothing class. Ground-arith groundings are allowed —
        # a formula computing a count may legitimately ground on `… = N`.
        if _thin_type_label(d.get("type", "")) in _THIN_HARD:
            thin_grounded.append(t)

    # ── R-05: grounding-kind honesty (definitional-record vs derivation) ──
    # A formula must not present a DEFINITIONAL record (identity wrapper / rfl
    # equality) as an independent DERIVATION. FORMULA_GROUNDING_KIND is the
    # authoritative per-ref claim; this cross-checks it against the Lean.
    from src.core.constants import FORMULA_GROUNDING_KIND
    kind_violations: List[tuple] = []

    # Leg B (false-positive-free, ALL refs): a vacuous identity wrapper (`P → P`
    # with reflexive body — proves nothing) MUST be declared a definitional
    # record; grounding a formula on one as a derivation is forbidden.
    for t in sorted(refs):
        if not resolves(t):
            continue
        d = decl(t)
        if not d or not _is_vacuous_identity_wrapper(d.get("type", "")):
            continue
        meta = FORMULA_GROUNDING_KIND.get(t.split(".")[-1])
        if not meta or meta.get("kind") != "definitional-record":
            kind_violations.append((t,
                "vacuous identity wrapper (`P → P`, reflexive body — proves nothing) grounds "
                "a formula; declare grounding_kind='definitional-record' in FORMULA_GROUNDING_KIND "
                "or reground on a substantive theorem"))

    # Legs A/C (the declared entries): the declared kind must MATCH the Lean.
    # 'definitional-record' that is actually substantive → mislabel; 'derivation'
    # that is actually an identity wrapper / rfl-definitional equality → the R-05
    # relabel we forbid (a definitional record cannot be re-labeled a derivation).
    for short, meta in FORMULA_GROUNDING_KIND.items():
        d = by_short.get(short)
        if not d:
            kind_violations.append((short,
                "FORMULA_GROUNDING_KIND entry resolves to no Lean declaration"))
            continue
        kind = meta.get("kind")
        is_defl = _grounding_is_definitional(d)
        if kind == "definitional-record" and not is_defl:
            kind_violations.append((short,
                "declared grounding_kind='definitional-record' but the Lean is neither an identity "
                "wrapper nor an rfl-definitional equality — inaccurate label (do not hide a "
                "substantive or open theorem behind a definitional record)"))
        elif kind == "derivation" and is_defl:
            kind_violations.append((short,
                "declared grounding_kind='derivation' but the Lean IS an identity wrapper / "
                "rfl-definitional equality — a definitional record cannot be re-labeled a "
                "derivation (R-05 evidence-laundering)"))
        elif kind not in ("definitional-record", "derivation"):
            kind_violations.append((short,
                f"kind={kind!r} is not 'definitional-record' or 'derivation'"))

    ok = not (placeholder_grounded or dangling or thin_grounded or kind_violations)
    details: List[Detail] = []
    details.append(Detail(
        "coverage", ok,
        f"{len(refs)} Lean refs; {len(refs) - len(dangling)} resolve; "
        f"{len(placeholder_grounded)} placeholder-grounded; {len(thin_grounded)} thin-grounded; "
        f"{len(dangling)} dangling; {len(FORMULA_GROUNDING_KIND)} grounding-kind declared; "
        f"{len(kind_violations)} grounding-kind violation(s)"))
    for t, msg in kind_violations:
        details.append(Detail(t, False, msg))
    for t in placeholder_grounded:
        details.append(Detail(t, False, "formula grounded on a placeholder/True stub (Invariant #4)"))
    for t in thin_grounded:
        details.append(Detail(
            t, False,
            "formula grounded on a reflexive/tautological theorem (proves nothing; "
            "Invariant #4 content-grounding) — reground on a substantive theorem"))
    # Dangling refs are HARD-FAIL since the 2026-06-13 FormulaRefSweep drove the
    # count to 0 (ratchet — a NEW stale/renamed formula ref must be fixed, not
    # left to rot). Replace the dangling name with the current theorem, drop the
    # ref if no theorem grounds the formula, or (if it is a legitimate Mathlib /
    # external name) it should still resolve in lean_deps — if not, it is drift.
    for t in dangling:
        details.append(Detail(
            t, False,
            "formula Lean-ref does not resolve (stale/renamed) — fix the name or drop the ref"))
    return CheckResult(passed=ok, details=details)


@register_check(
    "vacuous_statement_audit",
    "No project theorem/lemma has a content-thin (reflexive / tautological) statement (R2 type-companion)")
def check_vacuous_statement_audit() -> CheckResult:
    """Type-based companion to `proxy_body_audit` (ADR-004 reconcile #45/#54/#25).
    `proxy_body_audit` is name-gated (`_STRUCTURAL_NAME_RE`) and excludes
    `norm_num`/`decide` bodies, so a theorem whose STATEMENT proves nothing slips
    if its name isn't structural or its proof is `by norm_num` (e.g.
    `tetrad_components : 4*4=16`, `hom_tensor_adjunction_dim : ∀ rank, rank=rank`).
    This check classifies the ELABORATED type (lean_deps.json), name- and
    tactic-agnostic.

    HARD-FAIL: reflexive `Eq X X` and `True` (the unambiguously-vacuous classes)
    NOT in `VACUOUS_STATEMENT_BASELINE`. ADVISORY: ground-arithmetic (closed
    numeric facts — the class legitimately mixes vacuous physics-dressing with
    real counting identities like `4*5/2=10`) AND the grandfathered baseline (the
    ~48 pre-existing content-thin theorems un-hid by the SIG-gate blind-spot fixes,
    visible tracked debt — a name leaves the set only by being dispositioned). A
    flagged decl is COMPLIANT iff registered in `PLACEHOLDER_THEOREMS` /
    `MODELING_ASSUMPTION_THEOREMS` (reason+discloses), self-disclosed via a
    `_DEFINITIONAL` name suffix, or in the baseline. NEW (non-baseline) thin
    statements HARD-FAIL — closing the generator (ADR-004 pathway #2)."""
    from src.core.constants import PLACEHOLDER_LEAN_NAMES
    try:
        from src.core.constants import MODELING_ASSUMPTION_THEOREMS
    except ImportError:
        MODELING_ASSUMPTION_THEOREMS = {}
    try:
        from src.core.constants import VACUOUS_STATEMENT_BASELINE as BASELINE
    except ImportError:
        BASELINE = frozenset()
    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> PASS (loaders disagree).
    if not _H.lean_deps_present():
        return CheckResult(passed=True, measured=False, details=[Detail("inputs", True, "lean_deps.json absent")])

    exempt = set(PLACEHOLDER_LEAN_NAMES.keys())
    for k, v in MODELING_ASSUMPTION_THEOREMS.items():
        if v.get("reason") and v.get("discloses"):
            exempt.add(v.get("lean_name", k))

    deps = _H.load_lean_deps()
    new_hard: List[tuple] = []
    grandfathered: List[str] = []
    advisory: List[tuple] = []
    for d in deps:
        if d.get("kind") not in ("theorem", "lemma"):
            continue
        name = d.get("name", "")
        if _is_autogen_decl(name):
            continue
        short = name.split(".")[-1]
        if short in exempt or short.endswith("_DEFINITIONAL"):
            continue
        label = _thin_type_label(d.get("type", ""))
        if label is None:
            continue
        if label not in _THIN_HARD:
            advisory.append((name, label))
        elif short in BASELINE:
            grandfathered.append(short)
        else:
            new_hard.append((name, label))

    details: List[Detail] = []
    if advisory:
        details.append(Detail(
            "ground_arithmetic", True,
            f"{len(advisory)} closed-arithmetic theorem(s) (verify load-bearing or delete/disclose) — "
            f"e.g. {', '.join(n.split('.')[-1] for n, _ in advisory[:5])}", warning=True))
    if grandfathered:
        details.append(Detail(
            "baseline", True,
            f"{len(grandfathered)} grandfathered content-thin theorem(s) in VACUOUS_STATEMENT_BASELINE "
            f"(visible tracked debt → Vacuous Statement Sweep)", warning=True))
    for name, label in new_hard:
        short = name.split(".")[-1]
        details.append(Detail(
            short, False,
            f"NEW content-thin statement `{short}` [{label}] not in baseline — strengthen, delete, "
            f"or register in MODELING_ASSUMPTION_THEOREMS (reason+discloses)"))
    if new_hard:
        return CheckResult(passed=False, details=details)
    details.append(Detail(
        "all_theorems", True,
        f"no NEW content-thin statements ({len(grandfathered)} baselined, "
        f"{len(advisory)} ground-arith advisory)"))
    return CheckResult(passed=True, details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK 1e′: kernel no-go substrate integrity (ADR-007 N-C, Invariant #17)
# ═══════════════════════════════════════════════════════════════════════

@register_check(
    "nogo_substrate_integrity",
    "Every provably-false no-go has a live, kernel-pure, non-vacuous backing theorem (Invariant #17, ADR-007 N-C)")
def check_nogo_substrate_integrity() -> CheckResult:
    """The negative-front mirror of ``tracked_hypothesis_ledger`` (ADR-007 N-C).
    For every ``KERNEL_NOGO_REGISTRY`` entry, each backing theorem must (1) EXIST
    in ``lean_deps.json``, (2) be KERNEL-PURE (core-axiom closure ⊆
    ``{propext, Classical.choice, Quot.sound}``, no ``sorryAx`` / genuine project
    axiom), and (3) be NON-VACUOUS (its elaborated type is not ``True`` / reflexive
    ``X=X`` — a self-discharging no-go blocks nothing; reuses
    ``vacuous_statement_audit``'s ``_thin_type_label``). Any failure = **BLOCKER**
    (this plugs the atlas ``"never touches OBSTRUCTION"`` hole — Hole A/B, ADR-007).
    ADVISORY: every ``SETTLED_FORKS`` fork field-authored ``kernel-no-go`` that has
    no registry entry — the *refutable-but-unencoded* one-time audit (ADR-007
    Costs/risks #1; encode per N-E). SCOPE: provably-false no-gos only; policy /
    route / preference bans are OUT of scope (N-B) and remain prose-only."""
    from src.core import constants as _c
    REG = getattr(_c, "KERNEL_NOGO_REGISTRY", {})
    KERNEL = {"propext", "Classical.choice", "Quot.sound"}
    _ND = re.compile(r"\._native\.native_decide")

    # H4 DIVERGENCE, deliberately preserved (ADR-009 §Deferred item 4 — DECLINED). absence -> PASS (loaders disagree).
    if not _H.lean_deps_present():
        return CheckResult(passed=True, measured=False, details=[Detail("inputs", True, "lean_deps.json absent")])
    by_name = {d.get("name", ""): d for d in _H.load_lean_deps()}

    def _kernel_pure(rec: dict) -> bool:
        """Strict kernel purity for a NO-GO's backing theorem.

        ⚠️ TWO CORRECTIONS, 2026-08-05 (PR-review R4-I5), both validated against the
        live substrate before changing:

        (a) `native_decide` axioms were STRIPPED from the project-axiom list before
            the test, so a `native_decide`-backed refutation scored kernel-pure. That
            contradicts the bar this project states everywhere else: CLAUDE.md's
            target set is `{propext, Classical.choice, Quot.sound}`, and
            `atlas_view._is_kernel_pure` says in as many words that *"native_decide is
            policy-OK but not strictly kernel-pure"*. A no-go is a self-enforcing
            blocker — the one place the stricter reading has to hold.
            Measured: **546 declarations use native_decide; 0 of the registry's 126
            backing theorems do.** So this was LATENT, and it is fixed while it is.

        (b) The `sorryAx` conjunct was DEAD. `KERNEL` does not contain `sorryAx`, so
            `core.issubset(KERNEL)` is already False whenever `sorryAx` is in the core
            set — verified exhaustively over the live substrate: no record can satisfy
            the first conjunct and fail the third. Rather than delete the intent, it
            now also scans `axiom_deps_project`, where nothing was checking for it at
            all. A dead conjunct that reads as a second safeguard is worse than none.
        """
        core = set(rec.get("axiom_deps_core", []))
        proj = list(rec.get("axiom_deps_project", []))
        return (core.issubset(KERNEL) and not proj
                and not any("sorryAx" in a for a in core | set(proj)))

    details: List[Detail] = []
    hard = False
    for fork_id, e in sorted(REG.items()):
        bts = e.get("backing_theorems", []) or []
        if not bts:
            # ⚠️ WAS A FREE PASS (fixed 2026-08-05, PR-review R4-I5). An entry with no
            # backing theorem returned `passed=True` and `continue`d — the escape hatch
            # on Invariant #17, whose whole content is that a machine-enforced no-go is
            # backed by a kernel-pure refutation. Adding an unbacked entry bought a
            # pass, and the registry is exactly where a prose hope would be laundered
            # into a "self-enforcing blocker".
            #
            # Measured before changing: **0 of 45 entries have empty backing**, so this
            # closes the hatch at zero cost rather than turning a live population red.
            # If a construction-level no-go genuinely cannot carry a theorem, that needs
            # an explicit exemption field and a stated reason — not a silent branch.
            hard = True
            details.append(Detail(
                fork_id, False,
                "registry entry carries NO backing theorem. Invariant #17 is that a "
                "KERNEL_NOGO_REGISTRY entry is backed by a kernel-pure refutation; an "
                "unbacked entry is a prose hope wearing a machine-enforced label. Add "
                "the theorem, or remove the entry and record the fork in "
                "docs/dev-loops/SETTLED_FORKS.md where prose bans belong."))
            continue
        for bt in bts:
            rec = by_name.get(bt)
            if rec is None:
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` ABSENT from lean_deps.json (renamed/deleted — the blocker rotted; Hole B)"))
                continue
            if not _kernel_pure(rec):
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` NOT kernel-pure (core={sorted(set(rec.get('axiom_deps_core', [])))}, "
                    f"proj={rec.get('axiom_deps_project', [])}) — a tainted refutation is not self-enforcing"))
                continue
            label = _thin_type_label(rec.get("type", ""))
            if label in _THIN_HARD:
                hard = True
                details.append(Detail(
                    fork_id, False,
                    f"backing `{bt}` is VACUOUS [{label}] — a self-discharging no-go blocks nothing (Hole A)"))
                continue
            details.append(Detail(
                fork_id, True,
                f"backing `{bt}` [{e.get('nogo_kind', '?')}] exists, kernel-pure, non-vacuous"))

    # Hole-B audit (advisory): field-authored `kernel-no-go` SETTLED_FORKS forks lacking a registry entry.
    forks_path = _H.PROJECT_ROOT / "docs" / "dev-loops" / "SETTLED_FORKS.md"
    if forks_path.exists():
        text = forks_path.read_text(errors="ignore")
        knogo = []
        for block in re.split(r"^## +", text, flags=re.M)[1:]:
            fid = block.splitlines()[0].strip()
            if re.search(r"authored_by:\s*kernel-no-go", block):
                knogo.append(fid)
        reg_forks = {e.get("fork_id") for e in REG.values()}
        unencoded = [f for f in knogo if f not in reg_forks]
        details.append(Detail(
            "audit", True,
            f"{len(REG)} registry entries; {len(knogo)} field-authored kernel-no-go forks; "
            f"{len(unencoded)} refutable-but-unencoded (advisory — encode per N-E): "
            f"{', '.join(unencoded) or 'none'}",
            warning=bool(unencoded)))

    return CheckResult(passed=not hard, details=details)
