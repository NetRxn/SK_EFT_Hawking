#!/usr/bin/env bash
# Execute working notebooks named by the committing index (ACM), without env sync.
# Preserve GIT_DIR; notebook commits require an absolute existing interpreter in
# SKEFT_NOTEBOOK_PYTHON, separately admitted by ROOT. No source/index writes.
# Standalone/symlink calls require the same explicit committing Git context.
set -euo pipefail
exec python3 -I -S -B - <<'SKEFT_NOTEBOOK_BOOTSTRAP'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import traceback


class Refusal(RuntimeError):
    pass


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_path(data):
    if not data.endswith(b"\n") or b"\0" in data:
        raise Refusal("unavailable or malformed Git path")
    return Path(os.fsdecode(data[:-1]))


incoming = os.environ.copy()
launch = Path.cwd()
env = dict(incoming, GIT_OPTIONAL_LOCKS="0")
checkout = launch
guarded_index = None
guarded_index_sha256 = None


def assert_index_unchanged():
    if guarded_index is not None and digest(guarded_index) != guarded_index_sha256:
        raise Refusal("active index bytes changed during query/execution; no acceptance")


def git(*args, allowed=(0,)):
    assert_index_unchanged()
    result = subprocess.run(["git", "--no-pager", "-c", "diff.autoRefreshIndex=false", *args],
                            cwd=checkout, env=env, capture_output=True)
    assert_index_unchanged()
    if result.returncode not in allowed:
        raise Refusal("Git context/query failed: " + repr(args) + "\n" + os.fsdecode(result.stderr))
    return result


def target():
    # Preserve committing context; refuse unsupported selectors rather than clearing it.
    supported = {"GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_PREFIX",
                 "GIT_OPTIONAL_LOCKS", "GIT_CONFIG_NOSYSTEM", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM",
                 "GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL", "GIT_AUTHOR_DATE",
                 "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL", "GIT_COMMITTER_DATE", "GIT_EDITOR", "GIT_PAGER"}
    unsupported = sorted(k for k in incoming if k.startswith("GIT_") and k not in supported)
    if unsupported:
        raise Refusal("unsupported inherited Git selectors: " + repr(unsupported))
    for key in ("GIT_COMMON_DIR", "GIT_CONFIG_GLOBAL", "GIT_CONFIG_SYSTEM"):
        if incoming.get(key) and not Path(incoming[key]).is_absolute():
            raise Refusal("ambiguous relative inherited Git path: " + key)
    raw_dir = incoming.get("GIT_DIR")
    if not raw_dir:
        raise Refusal("preserved explicit GIT_DIR required; target cannot be guessed from cwd")
    gd = line_path(git("rev-parse", "--path-format=absolute", "--git-dir").stdout).resolve()
    common = line_path(git("rev-parse", "--path-format=absolute", "--git-common-dir").stdout).resolve()
    if common.name != ".git" or not common.is_dir():
        raise Refusal("only an ordinary common .git directory is supported")
    if gd != common:
        if not Path(raw_dir).is_absolute():
            raise Refusal("linked GIT_DIR must be absolute after a shared caller changes cwd")
        backlink = line_path((gd / "gitdir").read_bytes())
        declared_common = line_path((gd / "commondir").read_bytes())
        if not backlink.is_absolute() or (gd / declared_common).resolve() != common:
            raise Refusal("inconsistent linked administration directory")
        tree = backlink.parent.resolve()
        pointer = tree / ".git"
        data = pointer.read_bytes()
        if backlink.name != ".git" or pointer.is_symlink() or not data.startswith(b"gitdir: "):
            raise Refusal("unsupported linked worktree pointer")
        pointed = line_path(data[8:])
        if (tree / pointed).resolve() != gd:
            raise Refusal("worktree backlink is not reciprocal")
    else:
        tree = gd.parent.resolve()
        if gd.name != ".git" or not (tree / ".git").is_dir() or (tree / ".git").resolve() != gd:
            raise Refusal("only ordinary primary and linked checkouts are supported")
    supplied_tree = incoming.get("GIT_WORK_TREE")
    if supplied_tree and (not Path(supplied_tree).is_absolute() or Path(supplied_tree).resolve() != tree):
        raise Refusal("explicit GIT_WORK_TREE does not identify the committing checkout")
    supplied_index = incoming.get("GIT_INDEX_FILE")
    index = Path(supplied_index) if supplied_index else gd / "index"
    if not index.is_absolute():
        index = launch / index
        if gd != common or index.resolve() != (gd / "index").resolve():
            raise Refusal("alternate indices must be absolute; relative linked index is ambiguous")
    if index.is_symlink() or not index.is_file():
        raise Refusal("committing index must be an existing regular file")
    return tree, gd, common, index.resolve()


DRIVER = r"""

import json
import os
from pathlib import Path
import sys
import traceback
GUARD_TEMPLATE = "def __skeft_commit_origin_guard():\n    import json, os, sys\n    from pathlib import Path\n    c = json.loads(%s)\n    root = Path(c['checkout']).resolve()\n    from importlib.machinery import SourceFileLoader\n    cache = Path(c['kernel_pycache_prefix'])\n    if sys.pycache_prefix != str(cache) or not sys.dont_write_bytecode or any(cache.iterdir()):\n        raise RuntimeError('kernel fresh empty-prefix/no-write cache policy mismatch')\n    if c['label'] == 'start' and any(n == 'src' or n.startswith('src.') for n in sys.modules):\n        raise RuntimeError('candidate src was imported before the kernel guard')\n    sys.path.insert(0, str(root))\n    import src.core.constants\n    import src.core.formulas\n    if os.path.abspath(sys.executable) != c['python'] or str(Path(sys.prefix).resolve()) != c['prefix']:\n        raise RuntimeError('kernel interpreter/prefix mismatch')\n    history_file = str(get_ipython().history_manager.hist_file)\n    if history_file != ':memory:':\n        raise RuntimeError('kernel history persistence policy mismatch')\n    allowed = set(c['tracked_source_files'])\n    origins = {}\n    for name, module in list(sys.modules.items()):\n        if name == 'src' or name.startswith('src.'):\n            filename = getattr(module, '__file__', None)\n            if filename:\n                if type(getattr(module, '__loader__', None)) is not SourceFileLoader:\n                    raise RuntimeError('unsupported candidate source loader: ' + name)\n                location = str(Path(filename).resolve())\n                if location not in allowed:\n                    raise RuntimeError('untracked or wrong-checkout source: ' + name)\n                origins[name] = location\n            for directory in getattr(module, '__path__', ()):\n                if not Path(directory).resolve().is_relative_to(root / 'src'):\n                    raise RuntimeError('wrong-checkout package search path: ' + name)\n    result = {'interpreter': sys.executable, 'prefix': str(Path(sys.prefix).resolve()),\n              'checkout': str(root), 'modules': origins, 'pycache_prefix': sys.pycache_prefix,\n              'dont_write_bytecode': sys.dont_write_bytecode, 'cache_prefix_empty': not any(cache.iterdir()),\n              'history_file': history_file}\n    Path(c['output'], c['label'] + '-origins.json').write_text(json.dumps(result, sort_keys=True))\n__skeft_commit_origin_guard()\ndel __skeft_commit_origin_guard\n"
ctx = json.loads(sys.argv[1])
out = Path(ctx['output'])
nb = km = client = None
receipt = {'status': 'failed', 'notebook': ctx['notebook']}
code = 1
try:
    def check_driver_start():
        cache = Path(ctx['driver_pycache_prefix'])
        if sys.pycache_prefix != str(cache) or not sys.dont_write_bytecode or any(cache.iterdir()):
            raise RuntimeError('driver fresh empty-prefix/no-write cache policy mismatch')
        if any(n == 'src' or n.startswith('src.') for n in sys.modules):
            raise RuntimeError('candidate src imported before driver/kernel source policy')
    check_driver_start()
    import nbformat
    from nbclient import NotebookClient
    from jupyter_client import KernelManager
    from jupyter_client.kernelspec import KernelSpecManager
    check_driver_start()
    if os.path.abspath(sys.executable) != ctx['python']:
        raise RuntimeError('driver executable differs from selected interpreter')
    prefix = str(Path(sys.prefix).resolve())
    receipt.update(interpreter=sys.executable, prefix=prefix,
                   cache_policy={'driver_prefix': sys.pycache_prefix,
                                 'kernel_prefix': ctx['kernel_pycache_prefix'],
                                 'dont_write_bytecode': sys.dont_write_bytecode,
                                 'scope': 'ordinary tracked src SourceFileLoader imports; no preexisting src'})
    kernel_name = 'skeft-commit-' + out.parent.name.rsplit('-', 1)[-1]
    kernels = out / 'kernels'
    spec = kernels / kernel_name
    spec.mkdir(parents=True)
    (spec / 'kernel.json').write_text(json.dumps({
        'argv': [ctx['python'], '-I', '-B', '-X', 'pycache_prefix=' + ctx['kernel_pycache_prefix'],
                 '-m', 'ipykernel_launcher', '-f', '{connection_file}', '--HistoryManager.hist_file=:memory:'],
        'display_name': 'Explicit notebook commit interpreter', 'language': 'python'}))
    def guard_cell(label):
        data = json.dumps(dict(ctx, prefix=prefix, label=label))
        return nbformat.v4.new_code_cell(GUARD_TEMPLATE % repr(data))
    nb = nbformat.read(Path(ctx['checkout']) / ctx['notebook'], as_version=4)
    nb.cells.insert(0, guard_cell('start'))
    nb.cells.append(guard_cell('end'))
    manager = KernelSpecManager(kernel_dirs=[str(kernels)], ensure_native_kernel=False)
    km = KernelManager(kernel_name=kernel_name, kernel_spec_manager=manager,
                       connection_file=str(out / 'connection.json'))
    client = NotebookClient(nb, km=km, timeout=120, kernel_name=kernel_name,
                            resources={'metadata': {'path': str((Path(ctx['checkout']) / ctx['notebook']).parent)}})
    client.execute()
    receipt['origins'] = {label: json.loads((out / (label + '-origins.json')).read_text())
                          for label in ('start', 'end')}
    receipt['status'] = 'passed'
    code = 0
except Exception:
    receipt['error'] = traceback.format_exc()
    sys.stderr.write(receipt['error'])
finally:
    try:
        if km is not None and km.has_kernel:
            km.shutdown_kernel(now=True)
        if client is not None and client.kc is not None:
            client.kc.stop_channels()
        if km is not None:
            km.cleanup_resources()
    except Exception:
        code = 1
        receipt['status'] = 'failed'
        receipt['cleanup_error'] = traceback.format_exc()
        sys.stderr.write(receipt['cleanup_error'])
    try:
        if nb is not None:
            nbformat.write(nb, out / 'executed.ipynb')
        (out / 'driver.json').write_text(json.dumps(receipt, indent=2))
    except Exception:
        code = 1
        traceback.print_exc()
sys.exit(code)
"""


def main():
    global checkout, env, guarded_index, guarded_index_sha256
    checkout, gd, common, index = target()
    # Bind the original raw index before queries can inspect its staged population.
    guarded_index = index
    guarded_index_sha256 = digest(index)
    env.update(GIT_DIR=str(gd), GIT_COMMON_DIR=str(common),
               GIT_WORK_TREE=str(checkout), GIT_INDEX_FILE=str(index))
    if line_path(git("rev-parse", "--path-format=absolute", "--git-path", "index").stdout).resolve() != index:
        raise Refusal("Git did not retain the selected index")
    if git("rev-parse", "--is-bare-repository").stdout != b"false\n":
        raise Refusal("bare repositories are unsupported")
    head = git("rev-parse", "--verify", "HEAD").stdout.decode().strip()
    if git("ls-files", "--unmerged", "-z").stdout:
        raise Refusal("unmerged index cannot certify working notebooks")
    staged = git("diff", "--no-ext-diff", "--no-textconv", "--cached", "--name-only", "--diff-filter=ACM", "-z", "--").stdout
    names = [os.fsdecode(x) for x in staged.split(b"\0") if x.endswith(b".ipynb")]
    if not names:
        return 0
    python = incoming.get("SKEFT_NOTEBOOK_PYTHON", "")
    if not Path(python).is_absolute() or not Path(python).is_file() or not os.access(python, os.X_OK):
        raise Refusal("SKEFT_NOTEBOOK_PYTHON must select an absolute admitted existing executable")
    python = os.path.abspath(python)
    # Quiet-diff can report stat-cache suspicion; exact blob comparisons decide byte equality.
    git("--literal-pathspecs", "diff", "--no-ext-diff", "--no-textconv", "--quiet", "--", "src", allowed=(0, 1))
    source_names = [os.fsdecode(x) for x in git("ls-files", "-z", "--", "src").stdout.split(b"\0") if x]
    def regular(relative):
        path = checkout / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(checkout):
            raise Refusal("missing, escaping, symlink or nonregular working input: " + repr(relative))
        return path
    for name in names:
        regular(name)
        git("--literal-pathspecs", "diff", "--no-ext-diff", "--no-textconv", "--quiet", "--", name, allowed=(0, 1))
    selected = source_names + names
    mode_records = git("--literal-pathspecs", "ls-files", "--stage", "-z", "--", *selected).stdout
    staged_modes = {}
    for record in mode_records.split(b"\0"):
        if not record:
            continue
        header, relative = record.split(b"\t", 1)
        mode, object_id, stage = header.split()
        relative = os.fsdecode(relative)
        if stage != b"0" or mode not in (b"100644", b"100755") or relative in staged_modes:
            raise Refusal("unsupported or duplicate active-index regular-file mode")
        staged_modes[relative] = mode.decode("ascii")
    if set(staged_modes) != set(selected):
        raise Refusal("active-index mode roster differs from selected inputs")
    def working_mode(relative):
        return "100755" if regular(relative).stat().st_mode & 0o100 else "100644"
    if any(working_mode(relative) != staged_modes[relative] for relative in selected):
        raise Refusal("working file mode differs from the active index; partial staging unsupported")
    def snapshot():
        return {'index_sha256': digest(index),
                'sources': {name: digest(regular(name)) for name in source_names},
                'notebooks': {name: digest(regular(name)) for name in names},
                'modes': {name: working_mode(name) for name in selected}}
    # Compare actual bytes too: diff-only predicates can trust assume-unchanged/stat cache.
    # These index blobs are compared, never executed or materialized as another source tree.
    for relative in source_names + names:
        if regular(relative).read_bytes() != git("show", ":0:" + relative).stdout:
            raise Refusal("working bytes differ from the active index: " + repr(relative))
    assert_index_unchanged()
    before = snapshot()
    output = Path(tempfile.mkdtemp(prefix="skeft-notebook-commit-"))
    receipt = {'checkout': str(checkout), 'git_dir': str(gd), 'common_dir': str(common),
               'index': str(index), 'head': head, 'python': python,
               'semantics': 'staged ACM names; working files; partial notebook/src staging refused',
               'before': before, 'results': [], 'status': 'failed'}
    try:
        for number, name in enumerate(names):
            directory = output / str(number)
            directory.mkdir()
            # Initially empty, distinct prefixes are passed as interpreter options before startup.
            driver_cache = directory / 'driver-pycache'
            kernel_cache = directory / 'kernel-pycache'
            driver_cache.mkdir()
            kernel_cache.mkdir()
            context = {'checkout': str(checkout), 'notebook': name, 'python': python,
                       'tracked_source_files': [str(regular(x).resolve()) for x in source_names],
                       'output': str(directory), 'driver_pycache_prefix': str(driver_cache),
                       'kernel_pycache_prefix': str(kernel_cache)}
            (directory / 'context.json').write_text(json.dumps(context, indent=2))
            result = subprocess.run([python, '-I', '-B', '-X', 'pycache_prefix=' + str(driver_cache),
                                     '-c', DRIVER, json.dumps(context)],
                                    cwd=checkout, env=env, capture_output=True)
            (directory / 'stdout.log').write_bytes(result.stdout)
            (directory / 'stderr.log').write_bytes(result.stderr)
            try:
                observed = json.loads((directory / 'driver.json').read_text())
            except (OSError, ValueError) as exc:
                observed = {'status': 'failed', 'receipt_error': str(exc)}
            if not isinstance(observed, dict):
                observed = {'status': 'failed', 'receipt_error': 'driver receipt is not an object'}
            ok = result.returncode == 0 and observed.get('status') == 'passed'
            receipt['results'].append({'notebook': name, 'returncode': result.returncode,
                                       'driver': observed, 'passed': ok})
            print('Notebook ' + json.dumps(name) + (': passed' if ok else ': FAILED'))
            if not ok:
                sys.stderr.buffer.write(result.stdout + result.stderr)
                break
        receipt['after'] = snapshot()
        if receipt['after'] != before:
            raise Refusal('index/source/notebook bytes changed during execution; no acceptance')
        success = len(receipt['results']) == len(names) and all(x['passed'] for x in receipt['results'])
        receipt['status'] = 'passed' if success else 'failed'
        return 0 if success else 1
    except Exception:
        receipt['protocol_error'] = traceback.format_exc()
        raise
    finally:
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2))
        print('Notebook commit artifacts: ' + json.dumps(str(output)), flush=True)


try:
    sys.exit(main())
except Exception as exc:
    print('Notebook commit refused: ' + str(exc), file=sys.stderr)
    sys.exit(2)
SKEFT_NOTEBOOK_BOOTSTRAP
