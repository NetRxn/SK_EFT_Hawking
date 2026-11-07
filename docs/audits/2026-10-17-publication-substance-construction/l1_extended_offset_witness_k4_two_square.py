"""Exact selected paired k4 words with two independent protected squares.

Both ordered source insertions and all fifteen paired action vertices remain.
Thirteen curvature pairs peel; the two explicit square factors retain distinct
component and live-holonomy probe indices. This selected finite-lattice
population does not supply the full source/action ensemble, common partition
normalization or physical retarded response.
"""
from argparse import ArgumentParser
from pathlib import Path
from collections import Counter, defaultdict, namedtuple
from fractions import Fraction
from itertools import product
from hashlib import sha256
from time import perf_counter
import importlib
import json
import sys

AUDIT = Path(__file__).resolve().parent
if (AUDIT / 'l1_extended_offset_witness_k3.py').is_file():
    sys.path.insert(0, str(AUDIT))
import l1_extended_offset_witness_k3 as k3
import l1_extended_offset_witness_k4 as k4
import l1_extended_offset_witness_k2 as k2
from l1_extended_four_face_gauge_join import IDENTITY
from l1_direct_b_haar import add
from l1_extended_two_mixed_centers import remap

EXPECTED_WORDS = (28,63,114,149,194,219,253,268)
EXPECTED_MANIFEST_SHA256 = 'ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'
assert k2.ROW_CAP == 120000 and k2.PAIR_CAP == 3000000
assert all(Path(m.__file__).parent == AUDIT for m in (k2,k3,k4,k3.witness))
import hashlib
def base(row):
 f=dict.fromkeys((x for x in range(16) if x!=row['omitted']),(0,1)); f.update((x,tuple(a)) for x,a in row['changes'])
 sources=((0,row['axes'][0]),(1,row['axes'][1])); edges=defaultdict(list); faces={}
 for x,axes in sorted(f.items()):
  for a in axes:
   y=x^(1<<a); edges[min(x,y),max(x,y),a].append((x,a))
  a,b=(a for a in range(4) if a not in axes)
  faces[x,a,b]={(x,a),(x^(1<<a),b),(x^(1<<b),a),(x,b)}
 prot=set(sources)|{(v,a) for x,y,a in edges for v in (x,y)}
 removed=[]
 while faces:
  counts=Counter(e for b in faces.values() for e in b)
  deletions=[f for f,b in faces.items() if any(counts[e]==1 and e not in prot for e in b)]
  if not deletions: break
  for face in deletions: removed.append(face); del faces[face]
 return f,sources,edges,faces,prot,removed
MultiGeometry=namedtuple('MultiGeometry','frame edges sources squares lives fixed_square fixed_edges joined_source divisor')

def two_geometry(row):
 frame,sources,edges,faces,protected,removed=base(row)
 assert len(frame)==15 and len(row["changes"])==4
 endpoints=Counter(v for q,a in sources for v in (q,q^(1<<a)))
 incoming=Counter(q^(1<<a) for q,axes in frame.items() for a in axes)
 assert all(4*(q in frame)+2*incoming[q]+2*endpoints[q]==8 for q in range(16))
 assert len(removed)==13
 assert len(faces)==2 and all(boundary<=protected for boundary in faces.values())
 assert not(set(sources)&set.union(*faces.values()))
 assert not(set.intersection(*faces.values()))
 squares=tuple(sorted(faces));lives=tuple((q,a) for q,a,b in squares)
 fixed_square={s:dict.fromkeys(faces[s]-{live},IDENTITY) for s,live in zip(squares,lives,strict=True)}
 parent={}
 def root(q):
  while q in parent:q=parent[q]
  return q
 fixed_edges={};live_edges={}
 for index,live in enumerate(lives):
  q,a=live;y=q^(1<<a);key=min(q,y),max(q,y),a
  assert len(edges[key])==1
  assert key not in live_edges;live_edges[key]=index
 for fixed in fixed_square.values():
  for q,a in fixed:
   u,v=root(q),root(q^(1<<a));assert u!=v;parent[u]=v
   y=q^(1<<a);key=min(q,y),max(q,y),a
   assert key not in fixed_edges and key not in live_edges
   fixed_edges[key]=int(q>y)
 joined={}
 for q,a in sources:
  y=q^(1<<a);key=min(q,y),max(q,y),a
  if key in edges:
   assert len(edges[key])==1 and key not in fixed_edges and key not in live_edges
   joined[key]=int(q!=edges[key][0][0])
 divisor=(k3.witness.SCALE**2)**len(edges)*4**64*k3.witness.SCALE**(2-len(joined))*48**13*2**15
 return MultiGeometry(frame,edges,sources,squares,lives,fixed_square,fixed_edges,joined,divisor)

def two_prepare(g,restrict=None):
 restrict={} if restrict is None else restrict
 square_rows={i:k3.square_factor(s,l,g.fixed_square[s]) for i,(s,l) in enumerate(zip(g.squares,g.lives,strict=True))}
 square_keys={i:('square',i,'component') for i in square_rows};probe_keys={i:('square',i,'probe') for i in square_rows}
 live_edges={(min(q,q^(1<<a)),max(q,q^(1<<a)),a):i for i,(q,a) in enumerate(g.lives)}
 at_center={s[0]:i for i,s in enumerate(g.squares)}
 changed=set(g.fixed_edges)|set(g.joined_source)|set(live_edges)
 exclusive={label for e,labels in g.edges.items() if len(labels)==1 and e not in changed for label in labels}
 choices={};factors=[]
 for q,axes in sorted(g.frame.items()):
  keys=tuple((q,a) for a in axes);index=at_center.get(q)
  domains=(None,) if index is None else sorted({labels for labels,probe in square_rows[index]})
  rows={}
  for comp in domains:
   weights=k3.witness.center_weights(None if index is None else (comp,))
   for gamma,weight in weights.items():
    if q in restrict and gamma!=restrict[q]:continue
    if any(gamma[j][0]!=gamma[j][1] for j,key in enumerate(keys) if key in exclusive):continue
    rows[gamma+(() if index is None else (comp,))]={0:(weight,0)}
  if not rows:return None
  choices[q]=rows;factors.append((keys+(() if index is None else (square_keys[index],)),rows,{}))
 for edge,keys in sorted(g.edges.items()):
  lo,hi,a=edge;centers=tuple(int(q==hi) for q,axis in keys)
  domains=[sorted({row[g.frame[q].index(axis)] for row in choices[q]}) for q,axis in keys];rows={}
  for gamma in product(*domains):
   if edge in live_edges:
    index=live_edges[edge]
    for probe in sorted({p for labels,p in square_rows[index]}):
     row=k3.probed_action_edge(gamma[0],centers[0],int(g.lives[index][0]==hi),probe)
     if row:rows[gamma+(probe,)]=k3.witness.gaussian(remap(row,(lo,hi)))
    continue
   if edge in g.fixed_edges:row=k3.fixed_action_edge(gamma,centers,g.fixed_edges[edge])
   elif edge in g.joined_source:
    row=k3.joint_source(gamma[0],g.joined_source[edge])
    if centers[0]:row=remap(row,(1,0))
   else:row=k3.witness.local_edge(gamma,centers)
   if row:rows[gamma]=k3.witness.gaussian(remap(row,(lo,hi)))
  if not rows:return None
  degree=2*(len(keys)+int(edge in g.joined_source))
  factors.append((tuple(keys)+(() if edge not in live_edges else (probe_keys[live_edges[edge]],)),rows,{lo:degree,hi:degree}))
 for index,rows in square_rows.items():
  factors.append(((square_keys[index],probe_keys[index]),{key:{0:(weight,0)} for key,weight in rows.items()},{}))
 for q,a in g.sources:
  y=q^(1<<a);edge=min(q,y),max(q,y),a
  if edge in g.joined_source:continue
  row=add(*(k3.witness.anchored(0,(),(),gamma) for gamma in range(4)))
  factors.append(((),{():k3.witness.gaussian(remap(row,(q,y)))},{q:2,y:2}))
 assert {q:sum(f[2].get(q,0) for f in factors) for q in range(16)}==dict.fromkeys(range(16),8)
 assert set(Counter(key for f in factors for key in f[0]).values())=={2}
 return factors,g.divisor,exclusive

def two_contraction(g,restrict=None):
 prepared=two_prepare(g,restrict)
 if prepared is None:return Fraction(),0
 factors,divisor,exclusive=prepared;raw,peak=k3.eliminate_components(factors,exclusive)
 return Fraction(raw,divisor),peak

def data():
 manifest,_=k4.data()
 encoded=json.dumps(manifest,sort_keys=True,separators=(',',':')).encode()
 assert hashlib.sha256(encoded).hexdigest()=='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'
 found={}
 for row in manifest['rows']:
  f,s,e,faces,p,r=base(row)
  if len(faces)!=2:continue
  if not all(b<=p for b in faces.values()):continue
  if set.intersection(*faces.values()):continue
  if set(s)&set.union(*faces.values()):continue
  found[row['index']]=(row,two_geometry(row))
 assert tuple(found)==(28,63,114,149,194,219,253,268)
 return found

def describe(row,g):
 return dict(word=row,squares=g.squares,lives=g.lives,fixed_edges=sorted(g.fixed_edges),joined_source=sorted(g.joined_source),sources=g.sources,action_edges=len(g.edges),peeled=13,divisor=g.divisor)

def source_hashes():
    names = ('l1_extended_offset_witness_k2', 'l1_extended_offset_witness_k3',
             'l1_extended_offset_witness_k4', 'l1_extended_offset_square',
             'l1_extended_offset_witness', 'l1_extended_mixed_frame_moment',
             'l1_extended_mixed_center_gamma', 'l1_extended_mixed_curvature_core',
             'l1_extended_opposed_source', 'l1_extended_two_mixed_centers',
             'l1_extended_four_face_gauge_join', 'l1_direct_b_haar')
    modules = [importlib.import_module(n) for n in names]
    assert all(Path(m.__file__).parent == AUDIT for m in modules)
    result = {Path(m.__file__).name: sha256(Path(m.__file__).read_bytes()).hexdigest()
              for m in modules}
    result['evaluator'] = sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--word', type=int, choices=EXPECTED_WORDS)
    modes.add_argument('--controls-only', action='store_true')
    args = parser.parse_args()
    found = data()
    binding = {'manifest_sha256': EXPECTED_MANIFEST_SHA256,
               'source_sha256': source_hashes(),
               'row_cap': k2.ROW_CAP, 'pair_cap': k2.PAIR_CAP}
    if args.controls_only:
        k3.check_local_moments()
        for row, geom in found.values():
            for square, live in zip(geom.squares, geom.lives, strict=True):
                k3.square_control(square, live, geom.fixed_square[square])
            restrict = dict.fromkeys(geom.frame, k3.witness.FIXED_GAMMAS)
            value, peak = two_contraction(geom, restrict)
            print(json.dumps({'kind':'fixed-label', 'word':row['index'],
                              'coefficient':[value.numerator,value.denominator],
                              'peak_rows':peak, **binding}, sort_keys=True), flush=True)
        return
    if args.word is None:
        print(json.dumps({'kind':'two-square-census', 'origins':[0,1],
                          'valid_words':list(EXPECTED_WORDS),
                          'entries':[describe(*pair) for pair in found.values()],
                          **binding}, sort_keys=True), flush=True)
        return
    row, geom = found[args.word]
    began = perf_counter()
    value, peak = two_contraction(geom)
    raw = value * geom.divisor
    assert raw.denominator == 1
    print(json.dumps({'kind':'exact-word', 'replay_geometry':'two-independent-squares',
                      **describe(row,geom),
                      'coefficient':[value.numerator,value.denominator],
                      'raw_numerator':raw.numerator, 'peak_rows':peak,
                      'seconds':round(perf_counter()-began,3), **binding},
                     sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
