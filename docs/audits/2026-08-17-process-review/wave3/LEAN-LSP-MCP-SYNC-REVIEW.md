
# lean-lsp-mcp sync review — v0.26.1 → upstream/main (v0.29.0)

**Scope.** Security/supply-chain review of syncing the operator's fork
(`github.com/NetRxn/lean-lsp-mcp`, pinned at `v0.26.1`, zero local divergence)
to upstream `main` (v0.29.0, 71 commits ahead). Read-only review performed
against a clone at
`/private/tmp/.../scratchpad/llm-fork` (`HEAD` = v0.26.1, `upstream/main` =
target), via `git diff HEAD upstream/main` and per-commit `git show`. Nothing
in the reviewed repo was executed.

---

## 1. Execution surface

Every subprocess/process-spawn site in upstream/main:

| File:line | Command | Args origin | Shell involved? |
|---|---|---|---|
| `src/lean_lsp_mcp/search_utils.py:77` (`_create_ripgrep_process`) | `rg --json ... <pattern> <root>` | `pattern` built via `re.escape(query)` where `query` is model-supplied; passed as one element of an argv **list** | No — `subprocess.Popen(command, ...)`, `shell=True` is never passed |
| `src/lean_lsp_mcp/repl.py:143` | `lake env <repl_path>` | `repl_path` resolved from disk/env, not model input | No — `asyncio.create_subprocess_exec` |
| `src/lean_lsp_mcp/loogle.py:163,324` | git clone/fetch/checkout, `lake build loogle`, `lake env <loogle-bin> ...` | argv list; `ELAN_TOOLCHAIN` env value is read from the **scanned project's** `lean-toolchain` file (see §3) | No |
| `src/lean_lsp_mcp/profile_utils.py:164` | `lake env lean --profile ...` | fixed flags + validated file path | No |
| `src/lean_lsp_mcp/server.py:584-677` (`lean_build` tool) | `lake clean` / `lake exe cache get` / `lake build` | fixed literal argv; only `cwd` varies, and `cwd` is a project path validated by `require_lean_project_path` (must contain `lean-toolchain` + a `lakefile.*`) | No |
| `src/lean_lsp_mcp/verify.py:52` (unchanged, byte-identical to v0.26.1) | `lake ...` | fixed | No |

**Widened?** No. `search_utils.py` is the only place a model-supplied string
(`query` in `lean_local_search`) reaches a command line, and that was already
true in v0.26.1. The diff there (`git diff HEAD upstream/main --
src/lean_lsp_mcp/search_utils.py`) only reworks the *result-line parser*
(regex now understands `@[attr]`/`protected`/`noncomputable` prefixes so
declaration parsing doesn't silently mis-extract names) — the search pattern
itself is still built with `re.escape(query)` and still passed as a single
argv element, never through a shell interpreter. No shell-mode subprocess
call was added, no `os` dot `system`, no string-concatenated command line
anywhere in the diff.

One net-new fact worth flagging even though it isn't shell injection: in the
rewritten `LoogleManager` (`loogle.py`), the toolchain string used to build
the local Loogle binary now comes from `self.project_path / "lean-toolchain"`
— i.e., a file inside whatever repository is currently open — rather than
Loogle's own pinned `lean-toolchain` (v0.26.1 behavior). It's placed in an
env var (`ELAN_TOOLCHAIN`) passed to the build/run commands, never
shell-interpolated, so it isn't an injection vector by itself. But `elan`
treats a `lean-toolchain` value as a toolchain *source specifier*, including
`owner/repo:tag` GitHub syntax — so a project with a malicious
`lean-toolchain` line can already cause `elan`/`lake` to fetch and run a
release from an arbitrary GitHub repo. That risk is **not new**: the
existing `lean_build` tool already runs `lake build` directly against the
scanned project's own `lean-toolchain`/`lakefile`, which is itself a
Turing-complete build script. This is inherent to pointing any Lean tool at
an untrusted repo, not something this sync introduces — it only applies when
`--loogle-local` is enabled (an opt-in flag), and it makes the *implicit*
project-driven toolchain selection explicit rather than adding a new one.
Not a blocker for a project we control, worth
remembering if this fork is ever pointed at a third-party Lean project.

## 2. Network surface

All literal URLs in `src/` on each side:

**v0.26.1 (HEAD):** `loogle.lean-lang.org`, `github.com/nomeata/loogle.git`,
`github.com/leanprover/elan`, `github.com/BurntSushi/ripgrep`,
`leansearch.net/search`, HuggingFace endpoint
`bxrituxuhpc70w8w.us-east-1.aws.endpoints.huggingface.cloud` (leanfinder),
`leanprover-community.github.io/mathlib4_docs`, `premise-search.com`,
`leanpremise.net`, `github.com/leanprover-community/repl`,
`http://localhost/dummy-issuer` + `dummy-resource` (local OAuth stub for the
existing pre-shared-token auth path), `microsoft.github.io/.../lsp` (appears
only in a comment, never fetched).

**upstream/main:** identical set, **minus** the `mathlib4_docs` link (a
doc-link helper appears to have been dropped, not added), all centralized in
the new `config.py` (`DEFAULT_LOOGLE_URL`, `DEFAULT_STATE_SEARCH_URL`,
`DEFAULT_HAMMER_URL`, `DEFAULT_LEANFINDER_URL`).

**Verdict: zero new hosts.** No telemetry, analytics, crash reporting, or
auto-update was added — nothing in the diff references Sentry, PostHog,
update-check endpoints, or similar. The `leansearch` client-side rate limit
went from 3/30s to 90/30s (`config.py:38` `RATE_LIMITS`), per an inline
comment citing the upstream service's own capacity increase and per-IP
server-side limiting — a policy change, not a new endpoint. `LOOGLE_URL`,
`LEAN_STATE_SEARCH_URL`, `LEAN_HAMMER_URL`, `LOOGLE_HEADERS` remain
operator-controlled env-var overrides, same as before.

## 3. Filesystem surface

- **Path containment is untouched.** `src/lean_lsp_mcp/file_utils.py` —
  which defines `LeanPathPolicy` (`validate_path`, `contains`,
  `display_path`, `allowed_roots`) and `require_lean_project_path` (a
  project root must contain `lean-toolchain` + `lakefile.lean`/`.toml`) — has
  **zero diff** between HEAD and upstream/main
  (`git diff HEAD upstream/main -- src/lean_lsp_mcp/file_utils.py` is empty).
  All new tool modules (`tools/search.py`, `tools/navigation.py`, etc.) route
  through this same, unmodified policy object.
- **`config.py` (new file) is environment-only.** Every accessor in it reads
  from `os.environ` with a hardcoded default; nothing in it reads a file from
  the scanned repository, so a file placed in the project cannot influence
  server *configuration* through this module.
- **Two things in the scanned repo *do* influence behavior**, both
  pre-existing patterns extended rather than newly introduced: (a) the
  project's `lean-toolchain`, read by `LoogleManager._get_project_toolchain()`
  (`loogle.py:104`) to select a build toolchain — see §1; (b) `lean_build`
  running `lake build`/`lake clean`/`lake exe cache get` directly against the
  project, which was already the case in v0.26.1.
- **Temp files.** `profile_utils.py:213` creates a `NamedTemporaryFile(...,
  dir=project_path, delete=False)` — unchanged from v0.26.1 aside from an
  added post-hoc compile-error check (a ~15-line addition); the temp file
  name is OS-randomized, not model-supplied, and is unlinked in a `finally`
  block.
- **`docs/adding-a-tool.md`** documents that no tool should escape
  `LeanPathPolicy`; consistent with what the code does.
- Nothing writes outside `allowed_roots` (project root, `.lake/packages`
  dependencies, and the resolved Lean stdlib root) anywhere in the diff.

## 4. Code execution / deserialization

No bare `eval`, no dynamic code compilation, no object-pickling module use,
no `marshal` module use, and no unguarded YAML loading (`yaml` isn't even
imported by any runtime module) anywhere in `src/` on either side.
`getattr(...)` usage is all on trusted internal objects (`lifespan`,
`AsyncLeanLSPClient`, `asyncio.subprocess.Process`) for optional-attribute
probing (e.g. `getattr(lifespan, "client", None)`) — never dispatch on a
model-supplied name. The one place model input becomes "code" is
`lean_run_code` / the Lean REPL (`repl.py`) — feeding Lean source into `lake
env repl`/`lean --profile` for elaboration by the Lean compiler. That is the
tool's actual purpose (a Lean proof assistant runs Lean code) and is
unchanged in kind from v0.26.1; the diff only adds a `ReplProcessError`
class, a memory-limit refactor, and better error surfacing on REPL
desync/timeout. `PyYAML` is an **optional** extra
(`pyproject.toml` `[project.optional-dependencies] yaml`) not in the default
dependency set, and no code path in either tree imports it at all.

One dev-only item, not shipped in the installed package: `tests/manual/drive.py`
(new) is a manual MCP driver harness whose call-file format supports a
"run a shell command between tool calls" directive dispatched through
`subprocess`. It lives under `tests/`, which `pyproject.toml`'s
`[tool.setuptools.packages.find] where = ["src"]` excludes from the built
wheel — unreachable via `uvx lean-lsp-mcp` or normal MCP operation; only
runnable by someone manually invoking that script from a checkout.

## 5. Dependency delta

`pyproject.toml`: `leanclient==0.9.4` → `leanclient>=0.13.0` (floor, no
ceiling); `mcp[cli]==1.27.0` → `==1.28.1` (still an exact pin); `orjson>=3.11.1`
→ `>=3.11.9`; `certifi>=2024.0.0` → `>=2026.7.22`.

**`uv.lock` diff — only one net-new package across the entire tree:** `ty`
(Astral's type checker, `ty>=0.0.64`), and it is dev/lint-only
(`[project.optional-dependencies] lint`/`dev`, plus a new `uv run ty check
src/` CI step) — not part of the default runtime install. No typosquat- or
unmaintained-looking transitive package appears; diffing the sorted package
names between the two lockfiles shows exactly that one addition and nothing
else.

**The `leanclient` floor is the one finding that matters.** At the moment
upstream cut this release, the floor and the locked resolution agree
(`uv.lock` resolves `leanclient==0.13.0` in upstream/main, same as what a
fresh lock would pick today). But `==0.9.4` meant every install — via `uvx`
or otherwise — reproduced exactly the same, already-reviewed `leanclient`
bytes. `>=0.13.0` means any **future** `leanclient` release (a separate PyPI
project, own release cadence, not gated by this fork's git history) becomes
installable without any commit to this repo, *if* the invocation re-resolves
dependencies instead of honoring the committed `uv.lock`. Whether that
happens depends on how `uvx` is being invoked:
- `uv run` inside a checkout of the fork **honors `uv.lock`** by default (locked, reproducible).
- `uvx --from git+<url>@<rev> lean-lsp-mcp` (a bare tool install, no working
  directory) is **not guaranteed to reuse the repo's `uv.lock`** — as a
  standalone tool install it can re-resolve against PyPI's current
  `leanclient` releases satisfying `>=0.13.0`, especially on a fresh
  environment/cache.

For a server with local filesystem access and no code-review gate of its own
on `leanclient` releases, this is the change that most alters the trust
model: it moves `leanclient` from "reviewed once, pinned forever" to
"whatever satisfies the floor at resolve time, if uvx re-resolves." This is
squarely what the operator asked to have flagged, and is the basis for the
"SYNC WITH NOTED CAVEATS" verdict below — correctness of the code itself is
fine; the *pin looseness* is the residual risk.

## 6. Secrets / environment

`config.py` centralizes every env var the server reads (`AUTH_TOKEN_ENV =
"LEAN_LSP_MCP_TOKEN"`, plus project path, transport, tool-config overrides,
Loogle/REPL/search-backend settings) — all pure refactor of what `server.py`
read directly in v0.26.1; no new env var reads secrets or credentials. The
pre-shared-token HTTP-auth path (`PreSharedTokenVerifier`, `server.py:467-473`,
`http://localhost/dummy-issuer`/`dummy-resource` as inert OAuth-metadata
stand-ins) is byte-for-byte the same mechanism as v0.26.1, just reading
through `config.auth_token()` instead of `os.environ.get(...)` directly. No
token, credential, or env value is ever written into a URL, logged beyond
truncated stderr on process failures, or forwarded to a third party.

---

## Overall verdict: **SYNC WITH NOTED CAVEATS**

The three facts that drive this:

1. **No new execution, network, or filesystem surface.** Every subprocess
   call is argv-list-based (no shell-mode invocation anywhere); the set of
   contacted hosts is identical to v0.26.1 minus one removed link; and the
   path-containment policy (`file_utils.py`) that gates every file
   read/write is byte-for-byte unchanged. The 71 commits are overwhelmingly
   a `server.py` → `tools/*.py` refactor, an async `leanclient` migration,
   bug fixes (declaration-name parsing, Loogle search-path clobbering, REPL
   error surfacing), and two genuinely new but narrow, sandboxed features
   (`lean_minimal_hypotheses` — pure regex/string parsing, no I/O; a
   `format=structured` option on `lean_goal`).
2. **Dependency graph is clean except one pin.** Only one new transitive
   package (`ty`, dev-only, Astral-published) entered `uv.lock`; no
   typosquat-shaped or unmaintained addition anywhere.
3. **`leanclient==0.9.4` → `>=0.13.0` removes the exact-pin guarantee** for a
   package with the same filesystem/process access as the MCP server itself.
   This is real and worth fixing at sync time, not a reason to block the
   sync: either pin the fork's `pyproject.toml` to `leanclient==0.13.0`
   explicitly, or confirm the launch config invokes `uv run` (or a
   `--locked`/frozen `uvx` mode) that honors this repo's committed
   `uv.lock` rather than a bare floating `uvx --from git+...` resolution.

Recommended action alongside the sync: change `leanclient>=0.13.0` to
`leanclient==0.13.0` in the fork (matching what `uv.lock` already resolves to
today), so the exact-pin discipline v0.26.1 had is preserved going forward.
