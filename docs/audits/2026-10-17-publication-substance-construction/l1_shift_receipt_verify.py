from pathlib import Path
from re import search
from collections import Counter

def receipts(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        m=search(r'exact slice (\d+) (\d+) (\d+) (\d+) scaled Gaussian \((-?\d+),(-?\d+)\)/5308416',line)
        if m:
            *key,r,i=map(int,m.groups())
            assert tuple(key) not in rows
            rows[tuple(key)]=(r,i)
    return rows
baseline=receipts(str(Path(__file__).with_name('l1_sparse_mixed_projection_indexed.txt')))
assert len(baseline)==608
for family in range(2):
    for shift in (1,2,3):
        p=str(Path(__file__).with_name(f'l1_shift_{family}_{shift}'))
        expected={tuple(map(int,line.split()[1:])) for line in Path(p+'.slices.txt').read_text().splitlines() if line.startswith('slice ')}
        actual=receipts(p+'.out.txt')
        assert expected==actual.keys()
        if family:
            assert actual==baseline
        else:
            assert not any(any(v) for v in actual.values())
        print('family',family,'shift',shift,'rows',len(actual),'nonzero',sum(any(v) for v in actual.values()))
