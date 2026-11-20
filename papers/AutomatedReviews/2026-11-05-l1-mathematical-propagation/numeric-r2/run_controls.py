"""Scratch-only isolated scientific mutation receipts; never edits repository."""
from pathlib import Path
import json
import os
import subprocess
import sys

ROOT = Path('/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103')
OUT = Path('/tmp/l1-numeric-acceptance-author-20261105-r2')
PYTHON = ROOT.parent / 'SK_EFT_Hawking/.venv/bin/python'
BOOT = '''
import sys
sys.path.insert(0, {root!r})
mode = {mode!r}
if mode != 'baseline':
    from src.core.provenance import PARAMETER_PROVENANCE
    for arm in ('LOWER', 'UPPER'):
        record = PARAMETER_PROVENANCE[f'GW.C_GW_DEVIATION_{{arm}}_BOUND']
        record['source'] = record['source'].replace('Eq. (5)', 'Eq. (1)')
if mode == 'wrong-cap':
    from src.core.constants import GW_PARAMS
    GW_PARAMS['C_GW_TWO_SIDED_CAP'] = 7e-16
if mode == 'swapped-star':
    import src.core.visualizations as visualizations
    original = visualizations.fig_c_GW_vs_ligo_constraint
    def wrong_star():
        figure = original()
        figure.data[2].x = [0.0]
        figure.data[2].y = [1.0]
        return figure
    visualizations.fig_c_GW_vs_ligo_constraint = wrong_star
if mode == 'rounded-deviation':
    import src.gravitational_waves as gw
    original = gw.ligo_compatibility_check
    def rounded_deviation(chi):
        verdict = original(chi)
        verdict.deviation = round(verdict.deviation, 2)
        return verdict
    gw.ligo_compatibility_check = rounded_deviation
import pytest
raise SystemExit(pytest.main(['-c', {config!r}, {test!r}, '-q', '-k', {selector!r}]))
'''
receipts = []
for mode, selector, expected in [
    ('baseline', 'L1HeadlineNumerics or L1FigureScientificInputs', 1),
    ('source-corrected', '', 0),
    ('wrong-cap', 'conservative_cap', 1),
    ('swapped-star', 'curve_cap_band', 1),
    ('rounded-deviation', 'endpoint_deviation_rounding', 1),
    ('restored', '', 0),
]:
    program = BOOT.format(root=str(ROOT), mode=mode, config=str(ROOT/'pyproject.toml'),
                          test=str(OUT/'test_gravitational_waves.py'), selector=selector)
    script = OUT / f'control-{mode}.py'
    script.write_text(program)
    result = subprocess.run([str(PYTHON), str(script)], cwd=ROOT, text=True, capture_output=True)
    log = OUT / f'{mode}.log'
    log.write_text(result.stdout + result.stderr)
    receipts.append(dict(mode=mode, argv=[str(PYTHON), str(script)], cwd=str(ROOT),
                         exit_code=result.returncode, expected_exit_code=expected, log=str(log)))
    print(mode, 'exit', result.returncode)
    if result.returncode != expected:
        print(result.stdout + result.stderr)
        raise SystemExit('unexpected control outcome')
(OUT / 'execution-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
