"""Exact paired k4 words with two independently source-bearing tori.

Both ordered sources and all fifteen paired action vertices remain. Seven
curvature pairs peel, while each residual four-face torus uses all fifteen
protected branches, with their full independent Cartesian product retained.
Both sources are jointly fixed on a two-edge gauge forest and remain explicit
source polynomials. This selected population is not a full physical response.
"""
import sys,json,hashlib,signal
from pathlib import Path
from collections import Counter,defaultdict,namedtuple
from fractions import Fraction
from itertools import product
from time import perf_counter
AUDIT=Path(__file__).resolve().parent
if (AUDIT/'l1_extended_offset_witness_k3.py').is_file():
 sys.path.insert(0,str(AUDIT))
import l1_extended_offset_witness_k3 as k3
import l1_extended_offset_witness_k4 as k4
import l1_extended_offset_witness_k2 as k2
import l1_extended_offset_witness_k4_two_square as two
from l1_extended_four_face_gauge_join import IDENTITY
from l1_direct_b_haar import add
from l1_extended_two_mixed_centers import remap
assert k2.ROW_CAP==120000 and k2.PAIR_CAP==3000000
assert all(Path(m.__file__).parent==AUDIT for m in (k2,k3,k4,two,k3.witness))
Torus=namedtuple('Torus','faces fixed_source linked other')
Geometry=namedtuple('Geometry','frame edges sources squares lives fixed_square fixed_edges joined_source divisor fixed_sources tori')

def geometry(row):
 frame,sources,edges,faces,protected,removed=two.base(row)
 assert len(frame)==15 and len(row['changes'])==4 and len(removed)==7 and len(faces)==8
 assert all(f[1:]==(2,3) for f in faces)
 groups=[{f:b for f,b in faces.items() if f[0]&3==c} for c in sorted({f[0]&3 for f in faces})]
 assert len(groups)==2 and all(len(g)==4 for g in groups)
 assert not set.union(*groups[0].values())&set.union(*groups[1].values())
 tori=[]
 for core in groups:
  fixed,=set.union(*core.values())&protected
  assert fixed in sources and sum(fixed in b for b in core.values())==2
  q,a=fixed;linked=q,q^(1<<a);other=tuple(f[0] for f in core if f[0] not in linked)
  assert len(other)==2 and set(linked)<=set(f[0] for f in core)
  tori.append(Torus(core,fixed,linked,other))
 tori=tuple(sorted(tori,key=lambda t:t.fixed_source))
 fixed_sources={t.fixed_source for t in tori};assert fixed_sources==set(sources)
 parent={}
 def root(q):
  while q in parent:q=parent[q]
  return q
 for q,a in fixed_sources:
  u,v=root(q),root(q^(1<<a));assert u!=v;parent[u]=v
 assert all((min(q,q^(1<<a)),max(q,q^(1<<a)),a) not in edges for q,a in sources)
 endpoints=Counter(v for q,a in sources for v in (q,q^(1<<a)))
 incoming=Counter(q^(1<<a) for q,axes in frame.items() for a in axes)
 assert all(4*(q in frame)+2*incoming[q]+2*endpoints[q]==8 for q in range(16))
 assert len(edges)==(19 if row['index'] in (243,245) else 20)
 divisor=k3.witness.SCALE**(2*len(edges)+2)*4**64*48**7*2**15
 return Geometry(frame,edges,sources,(),(),{},{},{},divisor,fixed_sources,tori)

def data():
 manifest,_=k4.data();found={}
 assert hashlib.sha256(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode()).hexdigest()=='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'
 for row in manifest['rows']:
  frame,sources,edges,faces,protected,removed=two.base(row)
  if len(faces)!=8 or any(f[1:]!=(2,3) for f in faces):continue
  groups=[{f:b for f,b in faces.items() if f[0]&3==c} for c in sorted({f[0]&3 for f in faces})]
  if len(groups)!=2 or any(len(g)!=4 for g in groups):continue
  incidence=[set.union(*g.values())&protected for g in groups]
  if not all(len(s)==1 and s<=set(sources) for s in incidence):continue
  found[row['index']]=(row,geometry(row))
 assert tuple(found)==(243,245,257,270)
 return found
def prepare(g,core,restrict=None):
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
   weights=k3.witness.center_weights(core.get(q) if index is None else (comp,))
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
  row=add(*(k3.witness.anchored(0,(),None if (q,a) in g.fixed_sources else (),gamma) for gamma in range(4)))
  factors.append(((),{():k3.witness.gaussian(remap(row,(q,y)))},{q:2,y:2}))
 assert {q:sum(f[2].get(q,0) for f in factors) for q in range(16)}==dict.fromkeys(range(16),8)
 assert set(Counter(key for f in factors for key in f[0]).values())=={2}
 return factors,g.divisor,exclusive
def contraction(g,core,restrict=None):
 p=prepare(g,core,restrict)
 if p is None:return Fraction(),0
 factors,divisor,exclusive=p;raw,peak=k3.eliminate_components(factors,exclusive)
 return Fraction(raw,divisor),peak

def branches(g):
 domains=[list(k2.protected_branches(t.linked,t.other)) for t in g.tori]
 assert [len(d) for d in domains]==[15,15]
 for left,right in product(*domains):
  weight,core=left;other_weight,other_core=right
  assert not set(core)&set(other_core)
  yield weight*other_weight,core|other_core

def solve(g,restrict=None):
 total=Fraction();peak=0;n=0
 for weight,core in branches(g):
  value,size=contraction(g,core,restrict);total+=weight*value;peak=max(peak,size);n+=1
 assert n==225
 return total,peak


EXPECTED_WORDS=(243,245,257,270)
EXPECTED_MANIFEST_SHA256='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'

def describe(row,g):
 return {'word':row,'sources':g.sources,'fixed_sources':sorted(g.fixed_sources),
         'tori':[{'faces':sorted(t.faces),'fixed_source':t.fixed_source,
                  'linked':t.linked,'other':t.other} for t in g.tori],
         'action_edges':len(g.edges),'joined_edges':sorted(g.joined_source),
         'peeled':7,'divisor':g.divisor}

def source_hashes():
 import importlib
 names=('l1_direct_b_haar', 'l1_extended_four_face_gauge_join', 'l1_extended_mixed_center_gamma', 'l1_extended_mixed_curvature_core', 'l1_extended_mixed_frame_moment', 'l1_extended_offset_square', 'l1_extended_offset_witness', 'l1_extended_offset_witness_k2', 'l1_extended_offset_witness_k3', 'l1_extended_offset_witness_k4', 'l1_extended_offset_witness_k4_free_torus', 'l1_extended_offset_witness_k4_peeled', 'l1_extended_offset_witness_k4_single_square', 'l1_extended_offset_witness_k4_two_square', 'l1_extended_opposed_source', 'l1_extended_two_mixed_centers')
 modules=[importlib.import_module(n) for n in names]
 assert all(Path(m.__file__).parent==AUDIT for m in modules)
 result={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in modules}
 result['evaluator']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 return result

def main():
 from argparse import ArgumentParser
 parser=ArgumentParser(description=__doc__)
 modes=parser.add_mutually_exclusive_group()
 modes.add_argument('--word',type=int,choices=EXPECTED_WORDS)
 modes.add_argument('--controls-only',action='store_true')
 args=parser.parse_args();found=data()
 binding={'manifest_sha256':EXPECTED_MANIFEST_SHA256,'source_sha256':source_hashes(),
          'row_cap':k2.ROW_CAP,'pair_cap':k2.PAIR_CAP}
 if args.controls_only:
  for word,(row,g) in found.items():
   value,peak=solve(g,dict.fromkeys(g.frame,k3.witness.FIXED_GAMMAS))
   print(json.dumps({'kind':'fixed-label','scope':'Fixedgamma control only',
                     'word':word,'coefficient':[value.numerator,value.denominator],
                     'branches':225,'peak_rows':peak,**binding},sort_keys=True),flush=True)
  return
 if args.word is None:
  print(json.dumps({'kind':'two-source-bearing-tori-census','origins':[0,1],
                    'valid_words':list(EXPECTED_WORDS),
                    'entries':[describe(row,g) for row,g in found.values()],
                    **binding},sort_keys=True),flush=True)
  return
 row,g=found[args.word];began=perf_counter();value,peak=solve(g)
 raw=value*g.divisor;assert raw.denominator==1
 print(json.dumps({'kind':'exact-word','replay_geometry':'two-source-bearing-tori',
                   **describe(row,g),'coefficient':[value.numerator,value.denominator],
                   'raw_numerator':raw.numerator,'branches':225,'peak_rows':peak,
                   'seconds':round(perf_counter()-began,3),**binding},sort_keys=True),flush=True)

if __name__=='__main__':main()
