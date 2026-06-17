# SK_EFT_Hawking/tests/test_validate_unknown_check.py
import subprocess
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent


def test_unknown_check_name_hard_errors():
    r = subprocess.run([sys.executable, "scripts/validate.py", "--check", "does_not_exist_zzz"],
                       cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 2, f"expected rc2 for an unknown check, got {r.returncode}\n{r.stderr}"


def test_list_still_works():
    r = subprocess.run([sys.executable, "scripts/validate.py", "--list"],
                       cwd=ROOT, capture_output=True, text=True)
    assert r.returncode == 0 and r.stdout.strip()
