"""Selected consumer controls; full real numerical replay and transport are separate."""
import ast
from copy import deepcopy
from dataclasses import replace
from pathlib import Path

import pytest

from scripts import review_figures as rf
from src.core import formulas as f
from src.core import visualizations as viz


SPEC29 = next(s for s in rf.FIGURE_REGISTRY if s.name == 'fig29_adw_phase_diagram')
SPEC30 = next(s for s in rf.FIGURE_REGISTRY if s.name == 'fig30_adw_ng_modes')


@pytest.fixture(scope='module')
def real_fig29():
    # The original complete grid and policy, not a synthetic certificate fixture.
    return viz.fig_adw_phase_diagram().to_dict()


@pytest.fixture(scope='module')
def real_fig30():
    return viz.fig_adw_ng_mode_decomposition().to_dict()


def assert_red(spec, data, match=None):
    issues = rf._paper5_selected_consistency_issues(spec, data)
    assert len(issues) == 1 and issues[0].severity == 'error'
    assert issues[0].check == 'paper5_selected_consistency'
    if match is not None:
        assert match in issues[0].message
    return issues[0]


def test_full_original_hundred_rows_actual_capped_decode_and_semantic_replay(real_fig29, monkeypatch):
    decoder, verifier = f.adw_scalar_enclosure_from_dict, f.adw_validate_scalar_enclosure
    decoded, verified = [], []

    def decode(record, **caps):
        assert caps == dict(max_work=200000, max_bits=100000)
        result = decoder(record, **caps)
        decoded.append(result)
        return result

    def verify(cert, G, cutoff, species, **policy):
        assert policy == dict(atol=0, rtol=1e-10, energy_atol=0, energy_rtol=1e-8,
                              max_work=200000, max_bits=100000)
        assert cutoff == 1.0 and species == 4
        assert cert is decoded[-1]
        verified.append((cert, G))
        return verifier(cert, G, cutoff, species, **policy)

    monkeypatch.setattr(f, 'adw_scalar_enclosure_from_dict', decode)
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', verify)
    assert rf._paper5_selected_consistency_issues(SPEC29, real_fig29) == []
    assert len(decoded) == len(verified) == 100
    assert sum(c.branch == 'origin' for c in decoded) == 19
    assert sum(c.branch == 'positive' for c in decoded) == 81
    assert all(c.C < 1 for c in decoded)  # above-cutoff scalar control is separate


def test_real_fig30_and_unrelated(real_fig30):
    assert rf._paper5_selected_consistency_issues(SPEC30, real_fig30) == []
    assert rf._paper5_selected_consistency_issues(replace(SPEC29, name='unrelated'), None) == []


def test_real_structural_call_and_both_maps_present():
    tree = ast.parse(Path(rf.__file__).read_text())
    body = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'run_structural_checks')
    calls = [n for n in ast.walk(body) if isinstance(n, ast.Call) and
             isinstance(n.func, ast.Name) and n.func.id == '_paper5_selected_consistency_issues']
    assert len(calls) == 1
    assert [a.id for a in calls[0].args] == ['spec', 'fig_dict']
    # Each actual generation and structural map must bind both canonical producers.
    for name in ('fig_adw_phase_diagram', 'fig_adw_ng_mode_decomposition'):
        maps = [n for n in ast.walk(tree) if isinstance(n, ast.Dict) and
                any(isinstance(k, ast.Constant) and k.value == name and
                    isinstance(v, ast.Name) and v.id == name for k, v in zip(n.keys, n.values))]
        assert len(maps) == 2


@pytest.mark.parametrize('key', ['schema','Lambda','N_f','G_c','accuracy','accuracy_rationals','ratios','rows'])
def test_all_metadata_fields_required(real_fig29, key):
    data = deepcopy(real_fig29)
    del data['layout']['meta']['paper5_scalar_scan'][key]
    assert_red(SPEC29, data)


@pytest.mark.parametrize('key', ['index','ratio','G','represented_ratio','status','r_interval','C','V_eff',
    'magnitude_error','energy_error','display_error','C_over_Lambda','diagnostics','certificate'])
@pytest.mark.parametrize('index', [0,19])
def test_every_row_field_required(real_fig29, key, index, monkeypatch):
    # Transport population only; real numerical replay is the separate test above.
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', lambda c,*a,**kw:c)
    data = deepcopy(real_fig29)
    del data['layout']['meta']['paper5_scalar_scan']['rows'][index][key]
    assert_red(SPEC29, data, f'row {index}')


@pytest.mark.parametrize('key', ['search_attempted','bounds','candidate_cutoff','optimizer_success',
    'optimizer_status','optimizer_message','C','V_eff','C_validity','V_eff_validity','candidate_window',
    'selected','stationarity','globality','certificate'])
@pytest.mark.parametrize('index', [0,19])
def test_every_diagnostic_field_required(real_fig29, key, index, monkeypatch):
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', lambda c,*a,**kw:c)
    data = deepcopy(real_fig29)
    del data['layout']['meta']['paper5_scalar_scan']['rows'][index]['diagnostics'][key]
    assert_red(SPEC29, data, f'row {index}')


@pytest.mark.parametrize('kind', ['duplicate','reorder','short','synchronized_grid','ordinate','ordinate_bool',
    'C_int','index_bool','G_bool','ratio_bool','error_zero','error_unreduced','error_integer',
    'trace_missing','trace_duplicate','x_bool','extra_meta','extra_row','selected_int','optimizer_false',
    'hover_template','qualification','title','xaxis','yaxis','schema','cutoff_int','species_float',
    'trace_name','trace_type','trace_mode'])
def test_transport_visible_and_population_refusals(real_fig29, kind, monkeypatch):
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', lambda c,*a,**kw:c)
    data = deepcopy(real_fig29)
    meta = data['layout']['meta']['paper5_scalar_scan']; row = meta['rows'][19]; trace = data['data'][0]
    if kind == 'duplicate': meta['rows'][20] = deepcopy(row)
    elif kind == 'reorder': meta['rows'][19:21] = meta['rows'][19:21][::-1]
    elif kind == 'short': meta['rows'].pop()
    elif kind == 'synchronized_grid':
        meta['ratios'][19] = trace['x'][19] = row['ratio'] = 1.1
    elif kind == 'ordinate': trace['y'][19] += .01
    elif kind == 'ordinate_bool': trace['y'][0] = False
    elif kind == 'C_int': meta['rows'][0]['C'] = 0
    elif kind == 'index_bool': meta['rows'][0]['index'] = False
    elif kind == 'G_bool': row['G'] = True
    elif kind == 'ratio_bool': row['ratio'] = True
    elif kind == 'error_zero': row['display_error'] = dict(numerator='0', denominator='1')
    elif kind == 'error_unreduced': row['display_error'] = dict(numerator='2', denominator='2')
    elif kind == 'error_integer': row['display_error']['numerator'] = 1
    elif kind == 'trace_missing': data['data'] = []
    elif kind == 'trace_duplicate': data['data'].append(deepcopy(trace))
    elif kind == 'x_bool': trace['x'][0] = True
    elif kind == 'extra_meta': meta['unreviewed'] = True
    elif kind == 'extra_row': row['unreviewed'] = True
    elif kind == 'selected_int': row['diagnostics']['selected'] = 1
    elif kind == 'optimizer_false': row['diagnostics']['optimizer_success'] = False
    elif kind == 'hover_template': trace['hovertemplate'] = trace['hovertemplate'].replace('customdata[6]', 'customdata[7]')
    elif kind == 'qualification': data['layout']['annotations'][-1]['text'] += ' Physical gravity established.'
    elif kind == 'title': data['layout']['title']['text'] = 'Physical ADW phase'
    elif kind == 'xaxis': data['layout']['xaxis']['title']['text'] = 'True physical coupling'
    elif kind == 'yaxis': data['layout']['yaxis']['title']['text'] = 'Metric phase'
    elif kind == 'schema': meta['schema'] = 'bounded-scalar-v1'
    elif kind == 'cutoff_int': meta['Lambda'] = 1
    elif kind == 'species_float': meta['N_f'] = 4.0
    elif kind == 'trace_name': trace['name'] = 'Physical tetrad VEV'
    elif kind == 'trace_type': trace['type'] = 'bar'
    elif kind == 'trace_mode': trace['mode'] = 'text'
    assert_red(SPEC29, data)


@pytest.mark.parametrize('position', range(8))
def test_all_hover_positions_bound(real_fig29, position, monkeypatch):
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', lambda c,*a,**kw:c)
    data = deepcopy(real_fig29)
    data['data'][0]['customdata'][19][position] = 'false-visible-field'
    assert_red(SPEC29, data, 'row 19')


@pytest.mark.parametrize('kind', ['model','input','request','caps','bool_cap','huge_integer','noncanonical','binary_bool'])
def test_receipt_policy_and_type_preflight_precedes_replay(real_fig29, kind, monkeypatch):
    data = deepcopy(real_fig29); meta = data['layout']['meta']['paper5_scalar_scan']
    c = meta['rows'][0]['certificate']
    if kind == 'model': c['model'] = 'exact-ratio'
    elif kind == 'input': c['inputs'][0] = dict(numerator='1', denominator='1')
    elif kind == 'request': c['requested_rtol'] = dict(numerator='1', denominator='1')
    elif kind == 'caps': c['max_work'] = 200001
    elif kind == 'bool_cap': c['max_bits'] = True
    elif kind == 'huge_integer': c['inputs'][0]['numerator'] = '9'*100001
    elif kind == 'noncanonical': c['inputs'][0] = dict(numerator='02', denominator='1')
    elif kind == 'binary_bool': c['C'] = False
    def forbidden(*args, **kwargs):
        pytest.fail('untrusted policy/type admitted to costly semantic replay')
    monkeypatch.setattr(f, 'adw_validate_scalar_enclosure', forbidden)
    assert_red(SPEC29, data, 'row 0')


@pytest.mark.parametrize('kind', ['pi','trace','energy','rounding','ratio'])
def test_real_semantic_replay_rejects_coherent_mirror_forgery(real_fig29, kind):
    data = deepcopy(real_fig29); row = data['layout']['meta']['paper5_scalar_scan']['rows'][19]
    c = row['certificate']
    if kind == 'pi': c['pi_interval'] = [dict(numerator='3',denominator='1')]*2
    elif kind == 'trace': c['trace'][0]['flo'] = dict(numerator='0',denominator='1')
    elif kind == 'energy': c['energy_interval'][0] = dict(numerator='-1',denominator='1')
    elif kind == 'rounding': c['energy_rounding_error'] = dict(numerator='0',denominator='1')
    elif kind == 'ratio': c['r_interval'] = [dict(numerator='2',denominator='1')]*2
    # Keep all scalar mirrors coherent so real numerical replay must refuse.
    cert = f.adw_scalar_enclosure_from_dict(c)
    row['diagnostics']['certificate'] = deepcopy(c)
    row['r_interval'] = deepcopy(c['r_interval'])
    error = cert.energy_rounding_error+cert.energy_gap_upper
    row['energy_error'] = dict(numerator=f._adw_decimal(error.numerator),denominator=f._adw_decimal(error.denominator))
    data['data'][0]['customdata'][19][4:6] = [f._adw_decimal(q.numerator)+'/'+f._adw_decimal(q.denominator) for q in cert.r_interval]
    data['data'][0]['customdata'][19][7] = f._adw_decimal(error.numerator)+'/'+f._adw_decimal(error.denominator)
    assert_red(SPEC29, data, 'row 19')


def test_replay_exhaustion_is_error(real_fig29, monkeypatch):
    def refuse(*args,**kwargs):
        raise f.ADWScalarUnresolved('independent verifier work exhausted')
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',refuse)
    assert_red(SPEC29, real_fig29, 'exhausted')


@pytest.mark.parametrize('kind', ['schema','dimension_bool','count_bool','pair','label','id','text','total','qualification','title'])
def test_fig30_assignment_refusals(real_fig30, kind):
    data = deepcopy(real_fig30); m = data['layout']['meta']['paper5_component_count']; t = data['data'][0]
    if kind == 'schema': m['schema'] = 'physical-spectrum'
    elif kind == 'dimension_bool': m['dimension'] = True
    elif kind == 'count_bool': t['y'][1] = True
    elif kind == 'pair': t['y'][1:3] = t['y'][1:3][::-1]
    elif kind == 'label': t['x'][1] = 'Physical graviton'
    elif kind == 'id': t['customdata'][1] = 'absorbed'
    elif kind == 'text': t['text'][0] = '16'
    elif kind == 'total': data['layout']['annotations'][0]['text'] = 'Total assigned components: 15'
    elif kind == 'qualification': data['layout']['annotations'][-1]['text'] = 'Physical spectrum established'
    elif kind == 'title': data['layout']['title']['text'] = 'Physical graviton spectrum'
    assert_red(SPEC30, data)


# These execute real source files in fresh children, not a mutated figure fixture.
# The registry restriction is a test-only cost boundary; the unchanged full CLI
# is separately executed with all FigureSpecs for its actual exit-code evidence.
_SELECTED_ROUTE = r'''
import hashlib,json,pathlib,sys
from dataclasses import asdict
from scripts import review_figures as rf
from src.core import visualizations as v, formulas as f
from src.adw import gap_equation as ge
A=pathlib.Path.cwd().resolve()
origins={m.__name__:str(pathlib.Path(m.__file__).resolve()) for m in (rf,v,f,ge)}
assert all(pathlib.Path(p).is_relative_to(A) for p in origins.values()), origins
observed={}
for name in ('fig_adw_phase_diagram','fig_adw_ng_mode_decomposition'):
    original=getattr(v,name)
    def capture(original=original,name=name):
        fig=original();d=fig.to_dict()
        observed[name]={'sha256':hashlib.sha256(json.dumps(d,sort_keys=True).encode()).hexdigest(),
            'x':list(d['data'][0]['x']),'y':list(d['data'][0]['y']),
            'meta_sha256':hashlib.sha256(json.dumps(d['layout'].get('meta'),sort_keys=True).encode()).hexdigest(),
            'hover':d['data'][0].get('hovertemplate'),
            'annotations':[a.get('text') for a in d['layout'].get('annotations',[])]}
        return fig
    setattr(v,name,capture)
rf.FIGURE_REGISTRY=[s for s in rf.FIGURE_REGISTRY if s.name in ('fig29_adw_phase_diagram','fig30_adw_ng_modes')]
issues=rf.run_structural_checks()
print(json.dumps({'origins':origins,'observed':observed,'issues':[asdict(i) for i in issues]}))
raise SystemExit(1 if any(i.severity=='error' for i in issues) else 0)
'''


def _production_seed(kind, text):
    if kind == 'helper_call':
        old = '        issues.extend(_paper5_selected_consistency_issues(spec, fig_dict))'
        assert text.count(old) == 1
        return text.replace(old, '        # selected binding omitted by production seed', 1)
    if kind == 'grid':
        start = text.index('def fig_adw_phase_diagram(')
        end = text.index('\ndef fig_adw_ng_mode_decomposition(',start)
        part = text[start:end]
        old = 'ratios = np.linspace(0.1, 5.0, 100)'
        assert part.count(old) == 1
        return text[:start]+part.replace(old,'ratios = np.linspace(0.2, 5.0, 100)',1)+text[end:]
    if kind in ('request','caps','hover','qualification'):
        start = text.index('def fig_adw_phase_diagram(')
        end = text.index('\ndef fig_adw_ng_mode_decomposition(',start)
        part = text[start:end]
        old,new = {
            'request':('rtol=1e-10, energy_atol=0','rtol=1e-8, energy_atol=0'),
            'caps':('max_work=200000, max_bits=100000','max_work=200001, max_bits=100000'),
            'hover':('magnitude error=%{customdata[6]}','magnitude error=%{customdata[7]}'),
            'qualification':('or physical gravity.','or physical gravity is established.'),
        }[kind]
        assert part.count(old) == 1
        return text[:start]+part.replace(old,new,1)+text[end:]
    function = 'fig_adw_ng_mode_decomposition' if kind == 'fig30_pair' else 'fig_adw_phase_diagram'
    start = text.index('def '+function+'(')
    end = text.index('\ndef ',start+5)
    part = text[start:end]
    assert part.count('    return fig') == 1
    injection = {
        'ordinate':"    fig.data[0].y = [y+0.01 if i == 19 else y for i,y in enumerate(fig.data[0].y)]\n",
        'receipt':"    row = fig.layout.meta['paper5_scalar_scan']['rows'][19]\n    row['certificate']['trace'][0]['flo'] = dict(numerator='0', denominator='1')\n    row['diagnostics']['certificate'] = row['certificate']\n",
        'fig30_pair':"    fig.data[0].y = [6,4,2,4]\n",
    }[kind]
    return text[:start]+part.replace('    return fig',injection+'    return fig')+text[end:]


def _run_production_control(kind):
    import datetime
    import hashlib
    import json
    import os
    import subprocess
    import sys
    from scripts import seed_journal as journal
    A = Path(rf.__file__).resolve().parent.parent
    path = Path(rf.__file__) if kind == 'helper_call' else Path(viz.__file__)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONPATH=str(A), GIT_OPTIONAL_LOCKS='0')
    def state():
        st = path.stat()
        return dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), mode=st.st_mode,
                    mtime_ns=st.st_mtime_ns, ctime_ns=st.st_ctime_ns)
    def execute(code=None):
        argv = ([sys.executable,'-B','-m','pytest','-p','no:cacheprovider',
                 'tests/test_adw_selected_figure_consistency.py::test_real_structural_call_and_both_maps_present','-q']
                if code is None else [sys.executable,'-B','-c',code])
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        child = subprocess.run(argv,cwd=A,env=env,capture_output=True,text=True)
        return dict(argv=argv,cwd=str(A),start=start,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    returncode=child.returncode,stdout=child.stdout,stderr=child.stderr)
    before = state()
    baseline = execute(_SELECTED_ROUTE)
    assert baseline['returncode'] == 0, baseline
    with journal.seeded_mutation(path,lambda t:_production_seed(kind,t),reason='ADW selected checker '+kind):
        seeded = state()
        assert seeded['sha256'] != before['sha256']
        red = execute(None if kind == 'helper_call' else _SELECTED_ROUTE)
        assert red['returncode'] == 1, red
        if kind == 'helper_call':
            assert 'test_real_structural_call_and_both_maps_present' in red['stdout'] and 'assert 0 == 1' in red['stdout']
        else:
            consumed = json.loads(red['stdout'].splitlines()[-1])
            initial = json.loads(baseline['stdout'].splitlines()[-1])
            assert consumed['observed'] != initial['observed'], 'seed did not change consumed figure'
            intended = [i for i in consumed['issues'] if i['check'] == 'paper5_selected_consistency']
            assert len(intended) == 1 and intended[0]['severity'] == 'error', consumed
            assert not any(i['check'] == 'generation' for i in consumed['issues']), consumed
    restored = state()
    assert all(restored[k] == before[k] for k in ('sha256','mode','mtime_ns'))
    green = execute(_SELECTED_ROUTE)
    assert green['returncode'] == 0, green
    seam_green = execute(None) if kind == 'helper_call' else None
    if seam_green is not None:
        assert seam_green['returncode'] == 0, seam_green
    outstanding = list(journal.JOURNAL_DIR.glob('*.json'))
    assert outstanding == [], outstanding
    return dict(kind=kind,path=str(path),before=before,seeded=seeded,restored=restored,
                baseline=baseline,red=red,green=green,seam_green=seam_green,outstanding_entries=[],
                ctime_restored=False,lockfiles_retained=[str(p) for p in journal.JOURNAL_DIR.glob('*.lock')])


@pytest.mark.parametrize('kind', ['helper_call','grid','ordinate','receipt','request','caps','hover','qualification','fig30_pair'])
def test_real_production_mutation_restoration(kind):
    import json
    result = _run_production_control(kind)
    print('ADW_PRODUCTION_CONTROL='+json.dumps(result))


@pytest.mark.parametrize('key', ['atol','rtol','energy_atol','energy_rtol','max_work','max_bits'])
@pytest.mark.parametrize('bad', [False, None, '1', -1])
def test_external_policy_meta_value_and_type_preflight(real_fig29, key, bad, monkeypatch):
    data = deepcopy(real_fig29)
    data['layout']['meta']['paper5_scalar_scan']['accuracy'][key] = bad
    def forbidden(*args,**kwargs):
        pytest.fail('metadata-defined policy reached replay')
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',forbidden)
    assert_red(SPEC29,data)


@pytest.mark.parametrize('field', list(f.ADWScalarEnclosure.__dataclass_fields__))
def test_every_canonical_receipt_field_required_before_replay(real_fig29, field, monkeypatch):
    data = deepcopy(real_fig29)
    del data['layout']['meta']['paper5_scalar_scan']['rows'][0]['certificate'][field]
    def forbidden(*args,**kwargs):
        pytest.fail('incomplete certificate reached replay')
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',forbidden)
    assert_red(SPEC29,data,'row 0')


def _visible_poison(data, kind, *, bar=False):
    layout, trace = data['layout'], data['data'][0]
    if kind == 'annotation_false': layout['annotations'][-1]['visible'] = False
    elif kind == 'annotation_opacity': layout['annotations'][-1]['opacity'] = 0
    elif kind == 'reference_hidden': layout['annotations'][0]['visible'] = False
    elif kind == 'annotation_click': layout['annotations'][-1]['clicktoshow'] = 'onoff'
    elif kind == 'trace_false': trace['visible'] = False
    elif kind == 'trace_legendonly': trace['visible'] = 'legendonly'
    elif kind == 'trace_opacity': trace['opacity'] = 0
    elif kind == 'hover_skip': trace['hoverinfo'] = 'skip'
    elif kind == 'hover_none': trace['hoverinfo'] = 'none'
    elif kind == 'point_hover': trace['hoverinfo'] = ['all']*(4 if bar else 100); trace['hoverinfo'][-1] = 'skip'
    elif kind == 'layout_hover': layout['hovermode'] = False
    elif kind == 'extra_annotation': layout['annotations'].append(dict(text='Physical gravity and a fluctuation spectrum are established.',x=0,y=0))
    elif kind == 'extra_trace': data['data'].append(dict(type='scatter',x=[0],y=[0],mode='text',text=['Physical gravity established']))
    elif kind == 'trace_hovertext': trace['hovertext'] = 'Physical gravity established'
    elif kind == 'trace_text': trace['text'] = ['Physical gravity established']*(4 if bar else 100)
    elif kind == 'subtitle': layout['title']['subtitle'] = dict(text='Physical gravity established')
    elif kind == 'axis_hidden': layout['xaxis']['visible'] = False
    elif kind == 'axis_labels_hidden': layout['xaxis']['showticklabels'] = False
    elif kind == 'axis_text': layout['xaxis'].update(tickmode='array',tickvals=[0],ticktext=['Physical gravity established'])
    elif kind == 'other_axis_text': layout['xaxis2'] = dict(title=dict(text='Physical gravity established'))
    elif kind == 'legend_title': layout['showlegend'] = True; layout['legend'] = dict(title=dict(text='Physical gravity established'))
    elif kind == 'shape_label': layout.setdefault('shapes',[]).append(dict(type='line',x0=0,x1=1,y0=0,y1=1,label=dict(text='Physical gravity established')))
    elif kind == 'control_text': layout['updatemenus'] = [dict(buttons=[dict(label='Physical gravity established',method='skip')])]
    elif kind == 'template_annotation_false': layout['template']['layout']['annotationdefaults']['visible'] = False
    elif kind == 'template_annotation_opacity': layout['template']['layout']['annotationdefaults']['opacity'] = 0
    elif kind == 'template_trace_false': layout['template']['data'][trace['type']][0]['visible'] = False
    elif kind == 'template_trace_opacity': layout['template']['data'][trace['type']][0]['opacity'] = 0
    elif kind == 'template_hover': layout['template']['data'][trace['type']][0]['hoverinfo'] = 'none'
    elif kind == 'template_layout_hover': layout['template']['layout']['hovermode'] = False
    elif kind == 'template_extra_annotation': layout['template']['layout']['annotations'] = [dict(name='unreviewed',text='Physical gravity established',x=0,y=0)]
    elif kind == 'annotation_hovertext': layout['annotations'][-1]['hovertext'] = 'Physical gravity established'
    elif kind == 'off_axes': trace['xaxis'] = 'x2'
    elif kind == 'bar_hidden_labels': trace['textposition'] = ['outside','none','outside','outside']
    elif kind == 'bar_texttemplate': trace['texttemplate'] = 'Physical gravity established'
    elif kind == 'bar_hovertemplate': trace['hovertemplate'] = 'Physical gravity established'
    elif kind == 'bar_name': trace['name'] = 'Physical gravitational modes'
    elif kind == 'bar_marker_opacity': trace['marker']['opacity'] = [1,0,1,1]
    elif kind == 'scalar_hoveron': trace['hoveron'] = 'fills'
    else: raise AssertionError(kind)


@pytest.mark.parametrize('bar', [False, True])
@pytest.mark.parametrize('kind', ['annotation_false','annotation_opacity','reference_hidden','annotation_click',
    'trace_false','trace_legendonly','trace_opacity','hover_skip','hover_none','point_hover','layout_hover',
    'extra_annotation','extra_trace','trace_hovertext','trace_text','subtitle','axis_hidden','axis_labels_hidden',
    'axis_text','other_axis_text','legend_title','shape_label','control_text','template_annotation_false',
    'template_annotation_opacity','template_trace_false','template_trace_opacity','template_hover',
    'template_layout_hover','template_extra_annotation','annotation_hovertext','off_axes'])
def test_effective_visible_consumer_refuses_actual_legal_plotly_mutations(real_fig29,real_fig30,kind,bar,monkeypatch):
    import plotly.graph_objects as go
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)  # transport only
    data = deepcopy(real_fig30 if bar else real_fig29)
    _visible_poison(data,kind,bar=bar)
    actual = go.Figure(data).to_dict()  # all mutations are legal at the real Plotly interface
    assert_red(SPEC30 if bar else SPEC29,actual)


@pytest.mark.parametrize('kind',['bar_hidden_labels','bar_texttemplate','bar_hovertemplate','bar_name','bar_marker_opacity'])
def test_assignment_visible_text_and_bar_opacity(real_fig30,kind):
    import plotly.graph_objects as go
    data = deepcopy(real_fig30)
    _visible_poison(data,kind,bar=True)
    assert_red(SPEC30,go.Figure(data).to_dict())


def test_scalar_hoveron_fill_does_not_expose_authenticated_points(real_fig29,monkeypatch):
    import plotly.graph_objects as go
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)
    data=deepcopy(real_fig29);_visible_poison(data,'scalar_hoveron')
    assert_red(SPEC29,go.Figure(data).to_dict())


@pytest.mark.parametrize('bar',[False,True])
@pytest.mark.parametrize('style',['defaults','explicit','partial_opacity','unrelated_style','hidden_extra',
                                  'template_overridden','template_hidden_extra','perpoint_hover'])
def test_default_valid_visible_plotly_properties_and_styling_are_preserved(real_fig29,real_fig30,bar,style,monkeypatch):
    import plotly.graph_objects as go
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)  # transport only
    data=deepcopy(real_fig30 if bar else real_fig29);l=data['layout'];t=data['data'][0]
    if style=='explicit':
        t.update(visible=True,opacity=1,hoverinfo='all');l['hovermode']='closest'
        for a in l['annotations']:a.update(visible=True,opacity=1,clicktoshow=False)
        for key in ('xaxis','yaxis'):l[key].update(visible=True,showticklabels=True)
    elif style=='partial_opacity':
        t['opacity']=.5
        for a in l['annotations']:a['opacity']=.5
    elif style=='unrelated_style':
        l.update(width=900,height=700,paper_bgcolor='ivory',hovermode='x unified');l['xaxis']['showgrid']=False
    elif style=='hidden_extra':
        l['annotations'].append(dict(text='Unreviewed hidden text',visible=False,x=0,y=0))
        data['data'].insert(0,dict(type='scatter',visible=False,name='Unreviewed hidden trace',x=[0],y=[0]))
    elif style=='template_overridden':
        l['template']['layout']['annotationdefaults'].update(visible=False,opacity=0)
        for a in l['annotations']:a.update(visible=True,opacity=1)
        l['template']['data'][t['type']][0].update(visible=False,opacity=0,hoverinfo='none')
        t.update(visible=True,opacity=1,hoverinfo='all')
    elif style=='template_hidden_extra':
        l['template']['layout']['annotations']=[dict(name='hidden_note',visible=False,text='Unreviewed hidden text',x=0,y=0)]
    elif style=='perpoint_hover':
        t['hoverinfo']=['all']*(4 if bar else 100)
        if bar:t['marker']['opacity']=[1,.5,1,.5];t['textposition']=['outside']*4;t['texttemplate']='%{text}'
    assert rf._paper5_selected_consistency_issues(SPEC30 if bar else SPEC29,go.Figure(data).to_dict())==[]


def _visibility_production_seed(figure, kind, text):
    function='fig_adw_phase_diagram' if figure=='fig29' else 'fig_adw_ng_mode_decomposition'
    start=text.index('def '+function+'(');end=text.index('\ndef ',start+5);part=text[start:end]
    injection={
        'annotation_false':"    fig.layout.annotations[-1].visible = False\n",
        'annotation_opacity':"    fig.layout.annotations[-1].opacity = 0\n",
        'trace_false':"    fig.data[0].visible = False\n",
        'trace_legendonly':"    fig.data[0].visible = 'legendonly'\n",
        'trace_opacity':"    fig.data[0].opacity = 0\n",
        'hover_skip':"    fig.data[0].hoverinfo = 'skip'\n",
        'hover_none':"    fig.data[0].hoverinfo = 'none'\n",
        'extra_annotation':"    fig.add_annotation(text='Physical gravity and a fluctuation spectrum are established.',x=0,y=0,showarrow=False)\n",
    }[kind]
    assert part.count('    return fig')==1
    return text[:start]+part.replace('    return fig',injection+'    return fig')+text[end:]


def _visibility_production_control(figure,kind):
    import datetime,hashlib,json,os,subprocess,sys
    from scripts import seed_journal as j
    A=Path(rf.__file__).resolve().parent.parent;path=Path(viz.__file__)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONPATH=str(A),GIT_OPTIONAL_LOCKS='0')
    def state():
        s=path.stat();return dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),mode=s.st_mode,mtime_ns=s.st_mtime_ns,ctime_ns=s.st_ctime_ns)
    def execute():
        argv=[sys.executable,'-B','-c',_SELECTED_ROUTE];start=datetime.datetime.now(datetime.timezone.utc).isoformat()
        p=subprocess.run(argv,cwd=A,env=env,capture_output=True,text=True)
        return dict(argv=argv,cwd=str(A),start=start,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),returncode=p.returncode,stdout=p.stdout,stderr=p.stderr)
    before=state();baseline=execute();assert baseline['returncode']==0,baseline
    with j.seeded_mutation(path,lambda t:_visibility_production_seed(figure,kind,t),reason='ADW M1 '+figure+' '+kind):
        seeded=state();red=execute();assert red['returncode']==1,red
        b=json.loads(baseline['stdout'].splitlines()[-1]);r=json.loads(red['stdout'].splitlines()[-1])
        producer='fig_adw_phase_diagram' if figure=='fig29' else 'fig_adw_ng_mode_decomposition'
        assert b['observed'][producer]['sha256']!=r['observed'][producer]['sha256'],'visibility seed not consumed'
        for name in b['observed']:
            for field in ('x','y','meta_sha256'):
                assert b['observed'][name][field]==r['observed'][name][field],(name,field,'numerical/certificate data changed')
        selected=[i for i in r['issues'] if i['check']=='paper5_selected_consistency']
        assert len(selected)==1 and selected[0]['figure']==('fig29_adw_phase_diagram' if figure=='fig29' else 'fig30_adw_ng_modes'),r
        assert not any(i['check']=='generation' for i in r['issues']),r
    restored=state();assert all(before[k]==restored[k] for k in ('sha256','mode','mtime_ns'))
    green=execute();assert green['returncode']==0,green
    assert list(j.JOURNAL_DIR.glob('*.json'))==[]
    return dict(figure=figure,kind=kind,path=str(path),before=before,seeded=seeded,restored=restored,
                baseline=baseline,red=red,green=green,numerical_receipt_data_unchanged=True,journal_empty=True,ctime_restored=False,
                lockfiles_retained=[str(p) for p in j.JOURNAL_DIR.glob('*.lock')])


@pytest.mark.parametrize('figure',['fig29','fig30'])
@pytest.mark.parametrize('kind',['annotation_false','annotation_opacity','trace_false','trace_legendonly',
                                 'trace_opacity','hover_skip','hover_none','extra_annotation'])
def test_visibility_only_real_producer_mutation_restoration(figure,kind):
    import json
    print('ADW_VISIBILITY_CONTROL='+json.dumps(_visibility_production_control(figure,kind)))


@pytest.mark.parametrize('bar',[False,True])
@pytest.mark.parametrize('kind',['marker_colorbar_title','coloraxis_title','legend_group_title',
    'axis_labelalias','axis_tickprefix','axis_ticksuffix','shape_template_label','shape_legend_name'])
def test_expected_inventory_includes_nested_visible_titles_and_label_overrides(real_fig29,real_fig30,bar,kind,monkeypatch):
    import plotly.graph_objects as go
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)
    data=deepcopy(real_fig30 if bar else real_fig29);l=data['layout'];t=data['data'][0];claim='Physical gravity established'
    if kind=='marker_colorbar_title':
        t['marker'].update(color=list(range(len(t['x']))),showscale=True,colorbar=dict(title=dict(text=claim)))
    elif kind=='coloraxis_title':
        t['marker'].update(color=list(range(len(t['x']))),coloraxis='coloraxis')
        l['coloraxis']=dict(colorbar=dict(title=dict(text=claim)))
    elif kind=='legend_group_title':
        l['showlegend']=True;t.update(showlegend=True,legendgroup='claim',legendgrouptitle=dict(text=claim))
    elif kind=='axis_labelalias':l['yaxis']['labelalias']={'0':claim}
    elif kind=='axis_tickprefix':l['yaxis']['tickprefix']=claim
    elif kind=='axis_ticksuffix':l['yaxis']['ticksuffix']=claim
    elif kind in ('shape_template_label','shape_legend_name'):
        l.setdefault('shapes',[]).append(dict(type='line',x0=0,x1=1,y0=0,y1=1))
        if kind=='shape_template_label':l['template']['layout']['shapedefaults']['label']=dict(text=claim)
        else:l['showlegend']=True;l['shapes'][-1].update(showlegend=True,name=claim)
    assert_red(SPEC30 if bar else SPEC29,go.Figure(data).to_dict())


@pytest.mark.parametrize('bar',[False,True])
def test_valid_real_opacity_style_scalars_remain_supported(real_fig29,real_fig30,bar,monkeypatch):
    import plotly.graph_objects as go
    import numpy as np
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)
    data=deepcopy(real_fig30 if bar else real_fig29);data['data'][0]['opacity']=np.float64(.5)
    for a in data['layout']['annotations']:a['opacity']=np.float64(.5)
    assert rf._paper5_selected_consistency_issues(SPEC30 if bar else SPEC29,go.Figure(data).to_dict())==[]


@pytest.mark.parametrize('bar',[False,True])
@pytest.mark.parametrize('kind',['extra_legendonly','extra_transparent_trace','transparent_annotation_hover',
                                 'hidden_annotation_click','transparent_shape_label'])
def test_opacity_or_legendonly_does_not_hide_unrecognized_hover_or_legend_text(real_fig29,real_fig30,bar,kind,monkeypatch):
    import plotly.graph_objects as go
    monkeypatch.setattr(f,'adw_validate_scalar_enclosure',lambda c,*a,**kw:c)
    data=deepcopy(real_fig30 if bar else real_fig29);l=data['layout'];claim='Physical gravity established'
    if kind in ('extra_legendonly','extra_transparent_trace'):
        t=dict(type='scatter',x=[0],y=[0],name=claim,showlegend=True,hovertext=claim)
        if kind=='extra_legendonly':t['visible']='legendonly'
        else:t['opacity']=0
        data['data'].append(t);l['showlegend']=True
    elif kind=='transparent_annotation_hover':
        l['annotations'].append(dict(text='Transparent note',opacity=0,hovertext=claim,x=0,y=0))
    elif kind=='hidden_annotation_click':
        l['annotations'].append(dict(text=claim,visible=False,clicktoshow='onoff',x=0,y=0))
    elif kind=='transparent_shape_label':
        l.setdefault('shapes',[]).append(dict(type='line',x0=0,x1=1,y0=0,y1=1,opacity=0,label=dict(text=claim)))
    assert_red(SPEC30 if bar else SPEC29,go.Figure(data).to_dict())
