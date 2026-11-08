"""Exact paired k4 words with a shared-source square and protected/free tori.

Both ordered sources and all fifteen paired action vertices remain. A joint
three-link forest fixes both sources; one square, its source-bearing torus and
one free torus retain nine curvature pairs. All fifteen protected and three
free branches form the full independent 45-term product. The gamma/Grassmann
factor graph stays coupled. These selected words leave the full response open.
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
Geometry=namedtuple('Geometry','frame edges sources squares lives fixed_square fixed_edges joined_source divisor fixed_sources linked other protected_torus shared_source free_tori')

def geometry(row):
 frame,sources,edges,faces,protected,removed=two.base(row)
 assert len(frame)==15 and len(row['changes'])==4 and len(removed)==6 and len(faces)==9
 squares=tuple(f for f,b in faces.items() if b<=protected);assert len(squares)==1
 square,=squares;others={f:b for f,b in faces.items() if f!=square}
 assert set(sources)<=faces[square] and all(f[1:]==(2,3) for f in others)
 groups=[{f:b for f,b in others.items() if f[0]&3==c} for c in sorted({f[0]&3 for f in others})]
 assert len(groups)==2 and all(len(g)==4 for g in groups)
 connected=[t for t in groups if set.union(*t.values())&protected]
 free=[t for t in groups if not set.union(*t.values())&protected]
 assert len(connected)==len(free)==1;torus,free=connected[0],free[0]
 shared_source,=faces[square]&set.union(*torus.values())
 assert shared_source in sources and set.union(*torus.values())&protected=={shared_source}
 assert sum(shared_source in b for b in torus.values())==2
 assert not set.union(*free.values())&(faces[square]|set.union(*torus.values()))
 live=square[0],square[1];fixed=dict.fromkeys(faces[square]-{live},IDENTITY)
 assert set(sources)<=set(fixed) and shared_source in fixed
 parent={}
 def root(q):
  while q in parent:q=parent[q]
  return q
 for q,a in fixed:
  u,v=root(q),root(q^(1<<a));assert u!=v;parent[u]=v
 fixed_edges={}
 for q,a in fixed:
  y=q^(1<<a);fixed_edges[min(q,y),max(q,y),a]=int(q>y)
 q,a=live;y=q^(1<<a);live_key=min(q,y),max(q,y),a
 assert len(edges[live_key])==1 and edges[live_key][0][0] in {f[0] for f in torus}
 fixed_action=[(e,l) for e,l in edges.items() if e in fixed_edges]
 assert len(fixed_action)==1 and len(fixed_action[0][1])==1 and fixed_action[0][1][0][0] in {f[0] for f in torus}
 assert row['omitted'] in (4,5) and row['omitted'] in {v for q,a in sources for v in (q,q^(1<<a))}
 assert all((min(q,q^(1<<a)),max(q,q^(1<<a)),a) not in edges for q,a in sources)
 endpoints=Counter(v for q,a in sources for v in (q,q^(1<<a)))
 incoming=Counter(q^(1<<a) for q,axes in frame.items() for a in axes)
 assert all(4*(q in frame)+2*incoming[q]+2*endpoints[q]==8 for q in range(16))
 torus_sites={f[0] for f in torus};free_sites={f[0] for f in free}
 assert len(edges)==20 and not torus_sites&free_sites and square[0] not in torus_sites|free_sites
 q,a=shared_source;linked=q,q^(1<<a);other=tuple(f[0] for f in torus if f[0] not in linked)
 assert len(other)==2 and set(linked)<=torus_sites
 divisor=k3.witness.SCALE**(2*len(edges)+2)*4**64*48**6*2**15
 return Geometry(frame,edges,sources,squares,(live,),{square:fixed},fixed_edges,{},divisor,set(sources),linked,other,torus,shared_source,[free])

def data():
 manifest,_=k4.data();found={}
 assert hashlib.sha256(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode()).hexdigest()=='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'
 for row in manifest['rows']:
  frame,sources,edges,faces,protected,removed=two.base(row)
  if len(faces)!=9:continue
  squares=[f for f,b in faces.items() if b<=protected]
  if len(squares)!=1:continue
  square,=squares
  if not set(sources)<=faces[square]:continue
  others={f:b for f,b in faces.items() if f!=square}
  if any(f[1:]!=(2,3) for f in others):continue
  groups=[{f:b for f,b in others.items() if f[0]&3==c} for c in sorted({f[0]&3 for f in others})]
  if len(groups)!=2 or any(len(g)!=4 for g in groups):continue
  connected=[t for t in groups if set.union(*t.values())&protected];free=[t for t in groups if not set.union(*t.values())&protected]
  if len(connected)!=1 or len(free)!=1:continue
  shared=faces[square]&set.union(*connected[0].values())
  if len(shared)!=1 or not shared<=set(sources) or set.union(*connected[0].values())&protected!=shared:continue
  found[row['index']]=(row,geometry(row))
 assert tuple(found)==(110,153)
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
 protected=list(k2.protected_branches(g.linked,g.other))
 free=list(k2.free_branches(g.free_tori[0]))
 assert len(protected)==15 and len(free)==3
 for (weight,core),(free_weight,free_core) in product(protected,free):
  assert not set(core)&set(free_core)
  assert g.squares[0][0] not in set(core)|set(free_core)
  yield weight*free_weight,core|free_core

def solve(g,restrict=None):
 total=Fraction();peak=0;n=0
 for weight,core in branches(g):
  value,size=contraction(g,core,restrict);total+=weight*value;peak=max(peak,size);n+=1
 assert n==45
 return total,peak
EXPECTED_WORDS=(110,153)
EXPECTED_MANIFEST_SHA256='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'

def describe(row,g):
 fixed_action=[(edge,labels) for edge,labels in sorted(g.edges.items()) if edge in g.fixed_edges]
 q,a=g.lives[0];live_key=min(q,q^(1<<a)),max(q,q^(1<<a)),a
 return {'word':row,'sources':g.sources,'squares':g.squares,'lives':g.lives,
         'fixed_sources':sorted(g.fixed_sources),'fixed_forest':sorted(g.fixed_square[g.squares[0]]),
         'shared_source':g.shared_source,'protected_torus':sorted(g.protected_torus),
         'free_torus':sorted(g.free_tori[0]),'linked':g.linked,'other':g.other,
         'live_action_labels':g.edges[live_key],'fixed_action_edges':fixed_action,
         'omitted_action_center_retained_site':row['omitted'],'Grassmann_sites':list(range(16)),
         'action_edges':len(g.edges),'joined_edges':sorted(g.joined_source),
         'peeled':6,'divisor':g.divisor}

def source_hashes():
 import importlib
 names=('l1_direct_b_haar', 'l1_extended_four_face_gauge_join', 'l1_extended_mixed_center_gamma', 'l1_extended_mixed_curvature_core', 'l1_extended_mixed_frame_moment', 'l1_extended_offset_square', 'l1_extended_offset_witness', 'l1_extended_offset_witness_k2', 'l1_extended_offset_witness_k3', 'l1_extended_offset_witness_k4', 'l1_extended_offset_witness_k4_free_torus', 'l1_extended_offset_witness_k4_peeled', 'l1_extended_offset_witness_k4_single_square', 'l1_extended_offset_witness_k4_two_square', 'l1_extended_opposed_source', 'l1_extended_two_mixed_centers')
 modules=[importlib.import_module(n) for n in names]
 assert all(Path(m.__file__).parent==AUDIT for m in modules)
 result={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in modules}
 result['evaluator']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 return result

def prepare_branches(g,restrict=None):
 prepared=[(weight,prepare(g,core,restrict))
           for weight,core in branches(g)]
 assert len(prepared)==45
 return prepared

def contract_prepared(prepared,divisor,emit_branch=None):
 """Contract the already prepared tables once, retaining exact branch weights."""
 assert len(prepared)==45
 total=Fraction();peak=0
 for branch,(weight,table) in enumerate(prepared):
  if table is None:raw,size=0,0
  else:
   factors,local_divisor,exclusive=table;assert local_divisor==divisor
   raw,size=k3.eliminate_components(factors,exclusive)
  value=Fraction(raw,divisor);total+=weight*value;peak=max(peak,size)
  if emit_branch is not None:
   emit_branch({'branch':branch,'weight':[weight.numerator,weight.denominator],
                'raw_numerator':raw,'divisor':divisor,
                'coefficient':[value.numerator,value.denominator],
                'algebraic_empty_preparation':table is None,'peak_rows':size})
 return total,peak

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
   prepared=prepare_branches(g,dict.fromkeys(g.frame,k3.witness.FIXED_GAMMAS))
   value,peak=contract_prepared(prepared,g.divisor)
   print(json.dumps({'kind':'fixed-label','word':word,'branches':45,
                     'scope':'Fixed-gamma control','coefficient':[value.numerator,value.denominator],
                     'peak_rows':peak,**binding},sort_keys=True),flush=True)
  return
 if args.word is None:
  print(json.dumps({'kind':'shared-square-protected-free-tori-census','origins':[0,1],
                    'valid_words':list(EXPECTED_WORDS),
                    'entries':[describe(row,g) for row,g in found.values()],
                    **binding},sort_keys=True),flush=True)
  return
 row,g=found[args.word];began=perf_counter();prepared=prepare_branches(g)
 prep_seconds=perf_counter()-began;warm_start=perf_counter()
 value,peak=contract_prepared(prepared,g.divisor)
 warm_seconds=perf_counter()-warm_start;raw=value*g.divisor;assert raw.denominator==1
 print(json.dumps({'kind':'exact-word','replay_geometry':'shared-square-protected-free-tori',
                   'scope':'Complete selected unrestricted word',**describe(row,g),
                   'coefficient':[value.numerator,value.denominator],
                   'raw_numerator':raw.numerator,'branches':45,'peak_rows':peak,
                   'preparation_seconds':prep_seconds,'whole45_warm_seconds':warm_seconds,
                   'seconds':round(perf_counter()-began,3),**binding},sort_keys=True),flush=True)

if __name__=='__main__':main()
