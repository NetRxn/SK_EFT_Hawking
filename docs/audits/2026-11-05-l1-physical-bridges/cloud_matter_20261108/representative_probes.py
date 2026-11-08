"""Prospective bounded six-case feasibility sample. Execution requires source review."""
import argparse
import ast
from collections import Counter
from contextlib import redirect_stdout, redirect_stderr
from fractions import Fraction as F
import hashlib
import inspect
from itertools import combinations_with_replacement
import json
from math import factorial, prod
import os
from pathlib import Path
import resource
import signal
import sys
import tempfile
import time
import traceback

import remote_source_adapter as R
import remote_source_dirac_loop as B

MIB = 1024 * 1024
ROW_CAP, PAIR_CAP = 120000, 3000000
CASES = (
    ('A', 'U', (0, 0), (16, 16, 28, 28, 45, 45), {2: 6, 4: 4, 6: 1}, 8),
    ('B', 'U', (0, 0), (17, 17, 28, 28, 45, 45), {2: 6, 4: 3, 6: 2}, 8),
    ('C', 'U', (0, 1), (18, 19, 26, 26, 39, 39), {2: 8, 4: 4}, 4),
    ('D', 'U', (1, 1), (19, 19, 26, 26, 39, 39), {2: 8, 4: 4}, 8),
    ('E', 'UV', (0, 2), (18, 21, 33, 33, 39, 48), {2: 10, 4: 2, 6: 1}, 2),
    ('F', 'UV', (1, 2), (19, 21, 33, 33, 39, 48), {2: 10, 4: 2, 6: 1}, 2),
)


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + '.partial')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True, default=str) + '\n')
    os.replace(temporary, path)


def memory(pid):
    """Linux process evidence; RSS values are bytes, not virtual memory."""
    try:
        lines = Path(f'/proc/{pid}/status').read_text().splitlines()
    except OSError as exc:
        return {'observation_error': f'{type(exc).__name__}: {exc}'}
    return {line.split(':')[0]: int(line.split()[1]) * 1024
            for line in lines if line.startswith(('VmRSS:', 'VmHWM:', 'VmSize:'))}


def caches(C):
    result = {}
    for module in (C, C.L, B):
        for name, value in vars(module).items():
            if callable(getattr(value, 'cache_info', None)):
                result[f'{module.__name__}.{name}'] = value.cache_info()._asdict()
    return result


def degree6_controls(C):
    import controls as old
    source = inspect.getsource(old.moments)
    outer = ast.parse(source).body[0]
    nodes = [node for node in outer.body if isinstance(node, ast.FunctionDef)
             and node.name in ('sphere', 'sequence')]
    assert [node.name for node in nodes] == ['sphere', 'sequence']
    namespace = dict(old.__dict__)
    namespace['C'] = C
    transported = ast.Module(body=nodes, type_ignores=[])
    exec(compile(ast.fix_missing_locations(transported), '<exact-degree6-control-transport>', 'exec'), namespace)
    count = nonzero = 0
    for coordinates in combinations_with_replacement(range(8), 6):
        namespace['sequence'](coordinates)
        namespace['sequence'](tuple(reversed(coordinates)))
        count += 1
        nonzero += all(coordinates.count(q) % 2 == 0 for q in range(8))
    assert count == 1716 and nonzero == 120
    R.emit(event='degree6-moment-controls',multisets=count,reverse_checks=count,
           nonzero=nonzero,original_moments_sha256=hashlib.sha256(source.encode()).hexdigest(),
           extracted_ast_sha256=hashlib.sha256(ast.dump(transported).encode()).hexdigest())


def descriptor(C, case):
    name, channel, anchors, indices, expected_histogram, expected_factorial = case
    components = ((0, 2), (0 if channel == 'U' else 1, 2))
    paired_anchors = ((anchors[0], 0), (anchors[1], 0))
    source_edges = ((anchors[0], 0), (0, 2),
                    (anchors[1], 0 if channel == 'U' else 1), (0, 2))
    incidence = Counter(source_edges)
    word = tuple(C.S.TERMS[i][2] for i in indices)
    action_degrees = Counter()
    action_parity = 0
    for i in indices:
        parity, degrees, label = C.S.TERMS[i]
        action_parity ^= parity
        action_degrees.update({x: d for x, d in enumerate(degrees)})
        x, k, l, u, v = label
        m, n = (d for d in range(4) if d not in (k, l))
        incidence.update(((x, k), (C.S.forward(x, k), l),
                          (C.S.forward(x, l), k), (x, l), (u, m), (v, n)))
    expected_degrees = (2, 6, 8, 8) if channel == 'U' else (2, 7, 7, 8)
    assert tuple(action_degrees[x] for x in range(4)) == expected_degrees
    assert action_parity == C.S.link(anchors[0], 0) ^ C.S.link(anchors[1], components[1][0])
    assert all(n % 2 == 0 for n in incidence.values())
    histogram = Counter(n for edge, n in incidence.items() if edge not in C.TREE)
    assert histogram == expected_histogram
    multiplicity = prod(factorial(n) for n in Counter(indices).values())
    assert multiplicity == expected_factorial
    haar = prod(C.L.haar_scale(n) for edge, n in incidence.items() if edge not in C.TREE)
    return {'case': name, 'channel': channel, 'anchors': paired_anchors,
            'components': components, 'indices': indices, 'word': word,
            'source_edges': source_edges, 'action_degrees': expected_degrees,
            'incidence': [(edge, n) for edge, n in sorted(incidence.items())],
            'histogram': dict(histogram), 'haar_divisor': haar,
            'multiplicity_factorial': multiplicity, 'divisor': 4**16 * haar * multiplicity}


def anchor_controls(C, factor, description):
    """Evaluate actual source rows versus independently assembled matrix coframes."""
    import controls as old
    L = C.L
    free_edges = [edge for edge in description['source_edges'] if edge not in C.TREE]
    assert len(factor[0]) == len(free_edges)
    source_degrees = (6, 2, 0, 0) if description['channel'] == 'U' else (6, 1, 1, 0)
    assert tuple(factor[2].get(x, 0) for x in range(4)) == source_degrees
    fixtures = []
    for sl, sr in ((0, 1), (1, 2), (2, 3), (3, 0)):
        _, coordinates = old.fixtures(sl, sr, C.TREE)
        fixtures.append((f'Spin4-{sl}-{sr}', coordinates))
    assert len(factor[1]) >= 3, 'three nonzero source-coordinate polarizations required'
    for number, key in enumerate(sorted(factor[1])[:3]):
        coordinates = {edge: [0] * 8 for edge in set(description['source_edges'])}
        for edge, q in zip(free_edges, key):
            coordinates[edge][q] = 1
        fixtures.append((f'nonzero-key-{number}', coordinates))
    for label, coordinates in fixtures:
        metrics = []
        for axes, anchors in zip(description['components'], description['anchors']):
            frames = []
            for axis, anchor in zip(axes, anchors):
                edge = (anchor, axis)
                U = L.eye(4) if edge in C.TREE else sum(
                    (coordinates[edge][q] * C.basis()[q] for q in range(8)), L.zeros(4))
                Ud = U.H
                end = C.S.forward(0, axis)
                if end == 0:
                    delta = Ud - U
                    frame = tuple(L.bilinear(g * delta + delta * g, 0, 0) for g in L.gamma)
                elif anchor == 0:
                    frame = tuple(L.add(L.bilinear(g * Ud, 0, end),
                                  L.scale(L.bilinear(U * g, end, 0), -1)) for g in L.gamma)
                else:
                    assert anchor == end
                    frame = tuple(L.add(L.bilinear(Ud * g, end, 0),
                                  L.scale(L.bilinear(g * U, 0, end), -1)) for g in L.gamma)
                frames.append(frame)
            metrics.append(L.add(*(L.wedge(a, b) for a, b in zip(*frames))))
        expected = L.sparse_int(L.wedge(*metrics))
        actual = {}
        for key, row in factor[1].items():
            weight = prod(coordinates[edge][q] for edge, q in zip(free_edges, key))
            if weight:
                actual = old.addpairs(actual, row, weight)
        assert actual == expected, (description['case'], label)
        R.emit(event='new-anchor-control',case=description['case'],fixture=label,rows=len(expected))


def child_case(C, assemble, case, output):
    resource.setrlimit(resource.RLIMIT_AS, (768 * MIB, 768 * MIB))
    signal.signal(signal.SIGALRM, R.alarm)
    signal.setitimer(signal.ITIMER_REAL, 30)
    started = time.monotonic()
    record = {'case': case[0], 'status': 'started', 'phase':'source-assembly', 'cache_before': caches(C)}
    joins = []
    source_candidates = 0
    join_products = 0
    original_join = C.L.indexed_join
    original_wedge = R.bounded_wedge

    def join(left, right, closed, row_cap, pair_cap):
        nonlocal join_products
        assert row_cap <= ROW_CAP and pair_cap <= PAIR_CAP
        remaining = PAIR_CAP - join_products
        if remaining <= 0:
            raise RuntimeError('aggregate compatible join budget exhausted')
        event = {'left_rows': sum(map(len, left[1].values())),
                 'right_rows': sum(map(len, right[1].values())),
                 'remaining_products': remaining, 'closed': closed}
        joins.append(event)
        begin = time.monotonic()
        try:
            axes, rows, visits = original_join(left, right, closed, row_cap, min(pair_cap, remaining))
        except BaseException as exc:
            event.update(status='failed',type=type(exc).__name__,reason=str(exc),seconds=time.monotonic()-begin)
            raise
        join_products += visits
        event.update(status='complete',products=visits,rows=sum(map(len, rows.values())),seconds=time.monotonic()-begin)
        return axes, rows, visits

    def wedge(L, A, Bpoly, stats):
        nonlocal source_candidates
        source_candidates += len(A) * len(Bpoly)
        if source_candidates > PAIR_CAP:
            raise RuntimeError('aggregate source-factory candidate budget exceeds 3000000')
        return original_wedge(L, A, Bpoly, stats)

    C.L.indexed_join = join
    R.bounded_wedge = wedge
    try:
        description = descriptor(C, case)
        record['description'] = description
        begin = time.monotonic()
        factors, divisor, metadata = assemble(description['components'], description['anchors'], None, description['word'])
        record.update(assembly_seconds=time.monotonic()-begin,metadata=metadata,divisor=divisor)
        assert metadata['frames'] == 16 and metadata['curvature_vertices'] == 6
        assert metadata['curvature_quarters'] == 0
        assert metadata['haar_divisor'] == description['haar_divisor']
        assert metadata['multiplicity_factorial'] == description['multiplicity_factorial']
        assert divisor == description['divisor']
        record['phase'] = 'new-anchor-controls'
        begin = time.monotonic()
        anchor_controls(C, factors[0], description)
        record['anchor_control_seconds'] = time.monotonic()-begin
        record['phase'] = 'contraction'
        begin = time.monotonic()
        raw, peak, visits = C.contract(factors)
        record.update(status='complete',raw_complex=raw,real=str(F(raw[0],divisor)),
                      imag=str(F(raw[1],divisor)),peak_rows=peak,contract_reported_products=visits,
                      contraction_seconds=time.monotonic()-begin)
        code = 0
    except BaseException as exc:
        record.update(status='assertion-failure' if isinstance(exc, AssertionError) else 'incomplete',
                      type=type(exc).__name__,reason=str(exc))
        traceback.print_exc()
        code = 20 if isinstance(exc, AssertionError) else 10
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        record.update(seconds=time.monotonic()-started,joins=joins,
                      aggregate_join_products=join_products,source_factory_candidates=source_candidates,
                      cache_after=caches(C),memory=memory(os.getpid()))
        atomic_json(output,record)
    return code


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    args = parser.parse_args()
    assert not sys.flags.optimize and sys.platform.startswith('linux')
    assert len(os.listdir('/proc/self/task')) == 1, 'fork parent must be single-threaded'
    args.output_dir.mkdir(parents=True,exist_ok=False)
    started = time.monotonic()
    summary = {'scope':'six prospectively selected feasibility cases; no full-channel admission',
               'status':'preparation','cases':[],'limits':{'cold_seconds':600,'warm_seconds':180,
               'case_seconds':30,'whole_seconds':700,'rss_bytes':384*MIB,
               'conservative_parent_plus_child_rss_bytes':512*MIB,'child_as_bytes':768*MIB,
               'rows':ROW_CAP,'aggregate_case_join_products':PAIR_CAP,'source_factory_candidates':PAIR_CAP},
               'source_sha256':{str(p.name):hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in (Path(__file__),Path(R.__file__),Path(B.__file__),R.ARCHIVE)}}
    owned_pid = None
    active_case = None
    signal.signal(signal.SIGALRM,R.alarm)
    signal.setitimer(signal.ITIMER_REAL,600)
    try:
        with tempfile.TemporaryDirectory(prefix='l1-representative-') as tmp:
            directory = Path(tmp)
            with (args.output_dir/'cold.stdout.partial').open('w') as stream, redirect_stdout(stream), redirect_stderr(stream):
                C, original = R.load_archive(directory)
                assert C.ROW_CAP == ROW_CAP and C.PAIR_CAP == PAIR_CAP
                R.controls(C,original,directory)
                assemble = B.bind_assembly(C)
                B.loop_controls(C,assemble,directory)
                degree6_controls(C)
                descriptions = [descriptor(C,case) for case in CASES]
            os.replace(args.output_dir/'cold.stdout.partial',args.output_dir/'cold.stdout')
            cold_elapsed = time.monotonic()-started
            warm_deadline = min(started+700,time.monotonic()+180)
            signal.setitimer(signal.ITIMER_REAL,max(0.001,started+700-time.monotonic()))
            summary.update(status='warm',cold_seconds=cold_elapsed,parent_baseline=memory(os.getpid()),
                           parent_cache_baseline=caches(C),manifest=descriptions)
            atomic_json(args.output_dir/'summary.json',summary)
            for case in CASES:
                if time.monotonic() >= warm_deadline:
                    summary['status']='aggregate-warm-budget-exhausted'
                    break
                assert all(hashlib.sha256(p.read_bytes()).hexdigest()==summary['source_sha256'][p.name]
                           for p in (Path(__file__),Path(R.__file__),Path(B.__file__),R.ARCHIVE)), 'source drift before case'
                assert len(os.listdir('/proc/self/task')) == 1
                partial = args.output_dir/f'case-{case[0]}.stdout.partial'
                child_output = args.output_dir/f'case-{case[0]}.child.json'
                sys.stdout.flush();sys.stderr.flush()
                begin = time.monotonic()
                active_case = case[0]
                owned_pid = os.fork()
                if owned_pid == 0:
                    try:
                        with partial.open('w') as stream, redirect_stdout(stream), redirect_stderr(stream):
                            code = child_case(C,assemble,case,child_output)
                            stream.flush()
                    except BaseException:
                        code = 21
                    os._exit(code)
                samples=[];cause=None;killed=False
                while True:
                    waited,status,usage=os.wait4(owned_pid,os.WNOHANG)
                    if waited:
                        break
                    now=time.monotonic();child_memory=memory(owned_pid);parent_memory=memory(os.getpid())
                    sample={'seconds':now-begin,'child':child_memory,'parent':parent_memory}
                    samples.append(sample)
                    if 'VmRSS' not in child_memory or 'VmRSS' not in parent_memory:
                        # A child may exit between wait4 and /proc reads. Reap
                        # that race; a still-live child requires fail-closed stop.
                        waited,status,usage=os.wait4(owned_pid,os.WNOHANG)
                        if waited:
                            break
                        if cause is None:cause='memory-observation-unavailable'
                        rss=combined=None
                    else:
                        rss=child_memory['VmRSS']
                        combined=rss+parent_memory['VmRSS']
                    if cause is None:
                        if rss>384*MIB:cause='child-rss-observed-limit'
                        elif combined>512*MIB:cause='conservative-combined-rss-observed-limit'
                        elif now-begin>=30:cause='case-wall-limit'
                        elif now>=warm_deadline:cause='aggregate-warm-limit'
                    if cause and not killed:
                        try:os.kill(owned_pid,signal.SIGKILL)
                        except ProcessLookupError:pass
                        killed=True
                    time.sleep(0.05)
                owned_pid=None
                record=json.loads(child_output.read_text()) if child_output.exists() else {'case':case[0],'status':'incomplete','reason':'no child result artifact'}
                observed_rss=[s['child']['VmRSS'] for s in samples if 'VmRSS' in s['child']]
                observed_max=max(observed_rss) if observed_rss else None
                record.update(parent_observed_seconds=time.monotonic()-begin,wait_status=status,
                              exit_code=os.waitstatus_to_exitcode(status),stop_cause=cause,
                              samples=samples,wait4={'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,
                              'ru_maxrss_kib':usage.ru_maxrss,'ru_maxrss_bytes':usage.ru_maxrss*1024},
                              sampling_interval_seconds=0.05,
                              max_observed_rss_bytes=observed_max)
                record['rss_overshoot_bytes']=max(0,observed_max-384*MIB) if observed_max is not None else None
                record['wait4_rss_overshoot_bytes']=max(0,usage.ru_maxrss*1024-384*MIB)
                if cause:record['status']='incomplete'
                atomic_json(args.output_dir/f'case-{case[0]}.json',record)
                if partial.exists():os.replace(partial,args.output_dir/f'case-{case[0]}.stdout')
                active_case=None
                summary['cases'].append({k:record.get(k) for k in ('case','status','exit_code','stop_cause','parent_observed_seconds')})
                atomic_json(args.output_dir/'summary.json',summary)
                if record.get('type')=='AssertionError' or record['exit_code'] in (20,21):
                    raise AssertionError('scientific assertion or unclassified child setup failure halts sample')
            if summary['status']=='warm':summary['status']='sample-finished'
    except BaseException as exc:
        summary.update(status='halted',type=type(exc).__name__,reason=str(exc))
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
        if owned_pid:
            try:os.kill(owned_pid,signal.SIGKILL)
            except ProcessLookupError:pass
            _,status,usage=os.wait4(owned_pid,0)
            child_path=args.output_dir/f'case-{active_case}.child.json'
            record=json.loads(child_path.read_text()) if child_path.exists() else {'case':active_case}
            record.update(status='incomplete',stop_cause='parent-terminal-cleanup',
                          exit_code=os.waitstatus_to_exitcode(status),wait_status=status,
                          wait4={'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,
                                 'ru_maxrss_kib':usage.ru_maxrss,'ru_maxrss_bytes':usage.ru_maxrss*1024},
                          wait4_rss_overshoot_bytes=max(0,usage.ru_maxrss*1024-384*MIB))
            atomic_json(args.output_dir/f'case-{active_case}.json',record)
            partial=args.output_dir/f'case-{active_case}.stdout.partial'
            if partial.exists():os.replace(partial,args.output_dir/f'case-{active_case}.stdout')
            summary['cases'].append({'case':active_case,'status':'incomplete','stop_cause':'parent-terminal-cleanup'})
        summary['source_hashes_unchanged'] = all(
            hashlib.sha256(p.read_bytes()).hexdigest()==summary['source_sha256'][p.name]
            for p in (Path(__file__),Path(R.__file__),Path(B.__file__),R.ARCHIVE))
        if not summary['source_hashes_unchanged']:
            summary.update(status='halted',type='SourceDrift',reason='consumed source changed')
        summary['whole_seconds']=time.monotonic()-started
        summary['parent_final_memory']=memory(os.getpid())
        attempted={record['case'] for record in summary['cases']}
        summary['unattempted_cases']=[{'case':case[0],'reason':summary['status']}
                                      for case in CASES if case[0] not in attempted]
        atomic_json(args.output_dir/'summary.json',summary)


if __name__=='__main__':
    main()
