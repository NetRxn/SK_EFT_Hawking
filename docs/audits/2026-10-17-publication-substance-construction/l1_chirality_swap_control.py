"""Exact read-only structural check for the dominant chirality-exchange involution."""
import json
from argparse import ArgumentParser
from hashlib import sha256
from itertools import combinations_with_replacement, product
from pathlib import Path

from l1_unpaired_A_dominant_spin_orbits import PRIMITIVE, digest
from l1_unpaired_A_site10 import COMPONENT_MANIFEST_DIGEST, ORBIT_MANIFEST_DIGEST
from l1_unpaired_offset_factors import FRAME_PLANES, action_centers
from l1_extended_offset_witness import coframe
from l1_extended_mixed_frame_moment import moment

parser = ArgumentParser(description=__doc__)
parser.add_argument("component_path", type=Path)
parser.add_argument("orbit_path", type=Path)
parser.add_argument("primitive_path", type=Path)
args = parser.parse_args()
component_path = args.component_path
orbit_path = args.orbit_path
primitive_path = args.primitive_path
assert digest(component_path) == COMPONENT_MANIFEST_DIGEST
assert digest(orbit_path) == ORBIT_MANIFEST_DIGEST

def records(path):
    return map(json.loads, path.read_text().splitlines())

def swap_mask(mask):
    indices = [i ^ 2 for i in range(mask.bit_length()) if mask >> i & 1]
    inversions = sum(a > b for j, a in enumerate(indices) for b in indices[j+1:])
    return sum(1 << i for i in indices), (-1) ** inversions

primitive, = (r for r in records(primitive_path) if r['primitive_sha256'] == PRIMITIVE)
pinned_rows = tuple((m, tuple(v)) for m,v in primitive['primitive_rows'])
assert sha256(repr(pinned_rows).encode()).hexdigest() == PRIMITIVE
raw = dict(pinned_rows)
swapped = {}
for m,(x,y) in raw.items():
    n,sign=swap_mask(m)
    swapped[n]=(sign*x,sign*y)
assert len(raw)==208 and raw==swapped
print('B primitive exact rows',len(raw))

center_rows=[]
for site,(keys,rows,grade) in zip(sorted(FRAME_PLANES),action_centers(),strict=True):
    if site & 4:
        continue
    transformed={}
    for key,row in rows.items():
        new=tuple(v ^ 4 if k[0]=='coordinate' else v for k,v in zip(keys,key,strict=True))
        sign=(-1)**sum(i<3 for k,v in zip(keys,key,strict=True) if k[0]=='gamma' for i in v)
        assert new not in transformed
        transformed[new]={m:(sign*x,sign*y) for m,(x,y) in row.items()}
    assert transformed==rows
    center_rows.append((site,len(rows)))
print('A exact centers',center_rows)

for center,anchor,coordinate,gamma in product(range(2),range(2),range(8),range(4)):
    sign=-1 if gamma<3 else 1
    out={}
    for m,c in coframe(center,anchor,coordinate,gamma).items():
        n,w=swap_mask(m)
        out[n]=w*c
    assert out=={m:sign*c for m,c in coframe(center,anchor,coordinate^4,gamma).items()}
print('raw directed coframe controls',128)
n=0
for degree in range(5):
    for labels in combinations_with_replacement(range(8),degree):
        assert moment(labels)==moment(tuple(sorted(x^4 for x in labels)))
        n+=1
print('frame Haar moment controls',n)

components = {(r['block'],r['component']):
              {tuple(w):scale for _,g in r['fixed_groups'] for w,scale,_ in g}
              for r in list(records(component_path))[1:]}
owner={w:key for key,words in components.items() for w in words}
assert len(owner)==9216 and len(components)==2080
swap={}
for key,words in components.items():
    changed={tuple(x^4 for x in word):scale for word,scale in words.items()}
    destination,={owner[word] for word in changed}
    assert components[destination]==changed
    swap[key]=destination
assert all(swap[swap[key]]==key for key in swap)
orbits={tuple(r['representative']):r for r in records(orbit_path) if r['kind']=='component_orbit'}
orbit_owner={tuple(m['component']):key for key,r in orbits.items() for m in r['members']}
pairs={}
for key,r in orbits.items():
    other,={orbit_owner[swap[tuple(m['component'])]] for m in r['members']}
    assert len(r['members'])==len(orbits[other]['members'])
    pairs[key]=other
assert len(pairs)==148 and all(key!=value and pairs[value]==key for key,value in pairs.items())
print('signed component and orbit exchange',len(swap),len(pairs),len(pairs)//2)
for key in ((16,3),(20,7),(9,7),(13,3)):
    print(key,'component and orbit images',swap[key],pairs[key])
