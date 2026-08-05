"""Suite-wide fixtures.

THE ONE THING IN HERE, AND WHY IT IS NOT OPTIONAL
-------------------------------------------------
`scripts/validation/_memo.py` caches a PASS verdict for the two most expensive
checks, keyed on a fingerprint of their real inputs. Dozens of tests call those
checks with their internals monkeypatched — a stubbed `subprocess.run`, a fake
`lean_deps.json`, an empty allow-list. Without this, such a test writes a cache
entry keyed on the **real** tree while holding a verdict reached under the
**patch**, and the developer's next `validate.py` reads it back as a genuine PASS.

That is the fixture-vs-production confusion QI-30 named, aimed at the cache: a
result obtained against a patched fixture standing in for a production
measurement. Bypassing the memo for the whole suite removes the possibility
rather than relying on each test to remember.

It is set as an environment variable, not by patching `_config`, so it also
covers checks invoked in a SUBPROCESS (`tests/test_ci_mode.py` and the mutation
harness both shell out to `validate.py`), where a patched module attribute in
this process would not travel.
"""
from __future__ import annotations

import os

os.environ["SKEFT_VALIDATION_NO_MEMO"] = "1"
