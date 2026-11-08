"""Prospective22-word diagonal T subfamily, independently integrated Q sources."""
from time import perf_counter
STARTED = perf_counter()
import argparse
from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction as F
import hashlib
import inspect
import io
from itertools import product
from pathlib import Path
import resource
import signal
import tempfile
import traceback
import nearest_trace as N
import remote_source_dirac_loop as D
from l1_reduced_wedge_reference import wedge_sign
R = D.R
ROW_CAP, PRODUCT_CAP, WHOLE_SECONDS = 120000, 3000000, 60
PILOT = ((1, 0, 1, 1, 1),) * 2 + ((2, 2, 3, 2, 2),) * 4


def deadline(signum=None, frame=None):
    raise TimeoutError('whole-process60-second cap')


def emit(**record):
    R.emit(**record)


def inventory():
    with redirect_stdout(io.StringIO()):
        import l1_diagonal_classes as S
    full = set(S.out)
    assert len(full) == 310
    import l1_interacting_support as support
    assert support.match(support.half(3), 0, (4, 8, 8, 4))[0] == 117120
    incidence = lambda ii: tuple(sum((x, a) in S.links(ii) for a in (2, 3)) for x in (0, 3))
    both = {ii for ii in full if incidence(ii) == (0, 0)}
    simple = {ii for ii in full if incidence(ii) in ((0, 2), (2, 0)) and sorted(Counter(ii).values()) == [2, 2, 2]}
    mixed_unused = {ii for ii in full - both - simple if incidence(ii) in ((0, 2), (2, 0))}
    touched = full - both - simple - mixed_unused
    assert tuple(map(len, (both, simple, mixed_unused, touched))) == (22, 128, 32, 128)
    assert all(all(n > 0 for n in incidence(ii)) for ii in touched)
    partitions = Counter(tuple(sorted(Counter(ii).values())) for ii in both)
    assert partitions == {(2, 2, 2): 12, (2, 4): 8, (1, 1, 1, 1, 2): 2}
    orbits = {}
    for ii in both:
        images = {S.transform(ii, dx, sw, st) for dx, sw, st in product((0, 3), (0, 1), (0, 1))}
        assert images <= both
        orbits[min(images)] = images
        assert N.charge(S, ii) == 0
    seen = set()
    for images in orbits.values():
        assert not seen & images
        seen.update(images)
    assert seen == both and len(orbits) == 8
    emit(event='both-unused-support', full=310, selected=22, simple_disjoint=128,
         mixed_unused_disjoint=32, both_touched_disjoint=128, orbits=8,
         partitions=sorted(partitions.items()), all_source_charges=0)
    return S, sorted(orbits.items())


def bind_q_assembly(C):
    source = inspect.getsource(C.assemble)
    old_curvature = """        rows = curvature_table(fixed)
        if sign == -1:
            rows = {key: {0: (-value[0][0], -value[0][1])} for key, value in rows.items()}
        factors.append(bounded(tuple(leg for leg in legs if leg is not None) + (a, b), rows, {}))
"""
    new_curvature = """        spins=tuple(('D',internal()[1]) for _ in range(5))
        factors.extend(D.curvature_factors(C,legs,(a,b),sign,spins))
"""
    insertion = """    assert component is None and determinant is None and len(word)==6
    for site in (0,3):
        factors.append(bounded((), {(): {m<<(8*site):(c,0) for m,c in N.Q.items()}}, {site:4}))
    degree_sum = Counter()
"""
    replacements = ((old_curvature, new_curvature), ('    degree_sum = Counter()\n', insertion),
                    ('divisor = 4 ** (frame_count + curvature_count) * haar_divisor * multiplicity',
                     'divisor = 4 ** frame_count * haar_divisor * multiplicity'),
                    ("'curvature_quarters': curvature_count,", "'curvature_quarters': 0, 'curvature_vertices': curvature_count, 'physical_Q_sources': 2,"))
    for old, new in replacements:
        assert source.count(old) == 1
        source = source.replace(old, new)
    source = source.replace('def assemble(', 'def assemble_both_unused(', 1)
    ns = dict(C.__dict__)
    ns.update(C=C, D=D, N=N)
    exec(compile(source, '<closed-loop-with-independent-Q-sources>', 'exec'), ns)
    emit(event='both-unused-binding', producer_sha256=hashlib.sha256(source.encode()).hexdigest())
    return ns['assemble_both_unused']


def install_guard(C):
    original = C.L.indexed_join
    stats = {'products': 0, 'peak_rows': 0, 'calls': 0}
    def guarded(left, right, closed, row_cap, pair_cap):
        remaining = PRODUCT_CAP - stats['products']
        if remaining <= 0:
            raise RuntimeError('global compatible-product budget exhausted')
        stats['peak_rows'] = max(stats['peak_rows'], *(sum(map(len, f[1].values())) for f in (left, right)))
        axes, rows, count = original(left, right, closed, min(row_cap, ROW_CAP), min(pair_cap, remaining))
        stats['products'] += count
        stats['calls'] += 1
        stats['peak_rows'] = max(stats['peak_rows'], sum(map(len, rows.values())))
        assert stats['products'] <= PRODUCT_CAP and stats['peak_rows'] <= ROW_CAP
        return axes, rows, count
    C.L.indexed_join = guarded
    return stats


def controls(C, loop_assembly):
    word = tuple((x, 0, 1, x, x) for x in range(4) for _ in range(2))
    factors, divisor, metadata = loop_assembly(None, None, None, word)
    raw, peak, visits = C.contract(factors)
    assert raw[1] == 0 and F(raw[0], divisor) == 104978
    emit(event='unchanged-loop-normalization-control', value='104978', peak=peak, products=visits)
    # Scalar Q complement closures use the archived orientation, independently
    # checked for all six masks at both physical source sites.
    for site in (0, 3):
        for mask, coefficient in N.Q.items():
            shifted = mask << (8 * site)
            complement = (255 ^ mask) << (8 * site)
            a = C.bounded((), {(): {shifted: (coefficient, 0)}}, {site: 4})
            b = C.bounded((), {(): {complement: (1, 0)}}, {site: 4})
            raw, _, _ = C.contract([a, b])
            assert raw == (coefficient * wedge_sign(shifted, complement), 0)
    emit(event='independent-Q-signed-closures', count=12)


def evaluate(C, assemble, word, scope):
    factors, divisor, metadata = assemble(None, None, None, word)
    assert metadata['frames'] == 12 and metadata['curvature_vertices'] == 6
    assert metadata['curvature_quarters'] == 0 and metadata['physical_Q_sources'] == 2
    assert divisor == 4 ** 12 * metadata['haar_divisor'] * metadata['multiplicity_factorial']
    emit(event='both-unused-built', scope=scope, word=word, divisor=divisor, metadata=metadata)
    raw, peak, visits = C.contract(factors)
    assert raw[1] == 0
    value = F(raw[0], divisor)
    emit(event='both-unused-result', scope=scope, raw=raw, value=str(value), peak=peak, products=visits)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--controls', action='store_true')
    group.add_argument('--pilot', action='store_true')
    group.add_argument('--all', action='store_true', help='prospective reviewed22-word subset only')
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, deadline)
    signal.setitimer(signal.ITIMER_REAL, max(.001, WHOLE_SECONDS - (perf_counter() - STARTED)))
    stats = None
    try:
        emit(event='both-unused-caps', rows=ROW_CAP, products=PRODUCT_CAP, whole_seconds=WHOLE_SECONDS)
        S, orbits = inventory()
        _, transverse, haar, _ = N.machinery()
        N.source_tensor(transverse, haar)
        with tempfile.TemporaryDirectory(prefix='l1-both-unused-') as tmp:
            C, _ = R.load_archive(Path(tmp))
            stats = install_guard(C)
            loop_assembly = D.bind_assembly(C)
            controls(C, loop_assembly)
            assemble = bind_q_assembly(C)
            if args.pilot:
                evaluate(C, assemble, PILOT, 'one(2,4)representative only')
            elif args.all:
                total = F(0)
                for index, (ii, orbit) in enumerate(orbits):
                    value = evaluate(C, assemble, tuple(S.TERMS[i][2] for i in ii), f'selected orbit{index}')
                    total += len(orbit) * value
                emit(event='PARTIAL-22-word-diagonal', raw_subcontribution=str(total), full_words=310,
                     selected_words=22, numerator_j=0, numerator_jj=0)
    except BaseException as exc:
        emit(event='both-unused-failure', type=type(exc).__name__, reason=str(exc))
        traceback.print_exc()
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        emit(event='both-unused-resource-summary', seconds=perf_counter()-STARTED,
             maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, indexed_join=stats)


if __name__ == '__main__':
    main()
