---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: publication-chat-lead
review_date: 2026-10-15T00:00:00Z
kind: focused-test-hygiene
---

# Missing-bibkey extractor test output isolation

Author finding record. Independent acceptance is recorded in `SCOPED_REVIEW.md`; the supersession ledger controls closure status. The citation test itself remains failing.

### 2.1 — REQUIRED — A failing citation test must leave its output in pytest temporary storage

- **Severity:** required
- **Lane:** `infra`
- **Target:** `tests/test_phase6i_wave1.py::test_extract_missing_bibkeys_emits_no_orphans`
- **Location:** `tests/test_phase6i_wave1.py:197`, extractor output path and cleanup after assertions.
- **Gate:** none
- **Verify:** `python3 -c 'import ast,subprocess; from pathlib import Path; p="tests/test_phase6i_wave1.py"; name="test_extract_missing_bibkeys_emits_no_orphans"; old=ast.parse(subprocess.check_output(["git","show","953dbfc7e4f55436f3926f27a03436759e34ef9e:"+p],text=True)); new=ast.parse(Path(p).read_text()); get=lambda t: next(n for n in t.body if isinstance(n,ast.FunctionDef) and n.name==name); a,b=get(old),get(new); asserts=lambda n:[ast.dump(x) for x in ast.walk(n) if isinstance(x,ast.Assert)]; assert len(asserts(a))==3 and asserts(a)==asserts(b); assert [x.arg for x in b.args.args]==["tmp_path"]; expected=ast.dump(ast.parse("output = tmp_path / "+repr("missing_stubs.json")).body[0]); assert any(ast.dump(x)==expected for x in b.body); text=ast.unparse(b); assert "str(output)" in text and "output.read_text" in text and ".test_missing_stubs.json" not in text; assert not Path("docs/.test_missing_stubs.json").exists()'`
- **Observed at base:** The slow test writes docs/.test_missing_stubs.json and unlinks it only after its assertions. A real citation failure therefore leaves generated output in the repository. Output isolation must not suppress the failure or weaken its assertions.
- **Expected:** Use pytest tmp_path for the generated report and read that same path, preserving all three original assertion ASTs and the extractor invocation's real result.
- **Evidence:** The lead's actual slow-test run still fails on 10 unregistered stubs and reports 3 orphans. Its report is in pytest temporary storage, while docs/.test_missing_stubs.json is absent. The lead separately compared all three assertion ASTs against the base and found them unchanged. This underlying citation failure remains open and unwaived.
- **Baseline:** The base function has no tmp_path parameter and uses repository output followed by post-assertion cleanup. This newly declared Verify was not executed on an isolated baseline by the report author.
- **Limits:** The Verify checks output isolation and preservation of assertions without running the slow extractor. It is not a passing result for the citation test. The exact declared command must run before closure; independent review must assess the real slow-test failure and artifact location.
