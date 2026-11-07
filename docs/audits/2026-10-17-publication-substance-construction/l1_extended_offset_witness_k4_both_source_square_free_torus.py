"""Exact paired k4 words with both sources on one square and one free torus.

Both directed sources are retained on a three-edge square gauge forest.
All fifteen paired action vertices remain; ten curvature pairs peel, while
one explicit square and an unfixed four-face torus are integrated exactly.
This selected two-word population does not establish a full response or B3.
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
Geometry=namedtuple('Geometry','frame edges sources squares lives fixed_square fixed_edges joined_source divisor fixed_sources free_tori')

def geometry(row):
 frame,sources,edges,faces,protected,removed=two.base(row)
 assert len(frame)==15 and len(row['changes'])==4 and len(removed)==10 and len(faces)==5
 squares=tuple(f for f,b in faces.items() if b<=protected);assert len(squares)==1
 square,=squares;live=square[0],square[1];lives=(live,)
 assert set(sources)<=faces[square]
 free={f:b for f,b in faces.items() if f!=square}
 assert len(free)==4 and all(f[1:]==(2,3) for f in free) and len({f[0]&3 for f in free})==1
 assert not set.union(*free.values())&protected
 fixed=dict.fromkeys(faces[square]-{live},IDENTITY);assert set(sources)<=set(fixed)
 parent={}
 def root(q):
  while q in parent:q=parent[q]
  return q
 for q,a in fixed:
  u,v=root(q),root(q^(1<<a));assert u!=v;parent[u]=v
 fixed_edges={}
 for q,a in fixed:
  y=q^(1<<a);fixed_edges[min(q,y),max(q,y),a]=int(q>y)
 q,a=live;y=q^(1<<a);assert len(edges[min(q,y),max(q,y),a])==1
 assert all((min(q,q^(1<<a)),max(q,q^(1<<a)),a) not in edges for q,a in sources)
 endpoints=Counter(v for q,a in sources for v in (q,q^(1<<a)))
 incoming=Counter(q^(1<<a) for q,axes in frame.items() for a in axes)
 assert all(4*(q in frame)+2*incoming[q]+2*endpoints[q]==8 for q in range(16))
 assert len(edges)==20
 divisor=k3.witness.SCALE**(2*len(edges)+2)*4**64*48**10*2**15
 return Geometry(frame,edges,sources,squares,lives,{square:fixed},fixed_edges,{},divisor,set(sources),[free])

def data():
 manifest,_=k4.data();found={}
 assert hashlib.sha256(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode()).hexdigest()=='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'
 for row in manifest['rows']:
  frame,sources,edges,faces,protected,removed=two.base(row)
  if len(faces)!=5:continue
  squares=[f for f,b in faces.items() if b<=protected]
  if len(squares)!=1:continue
  square,=squares
  if not set(sources)<=faces[square]:continue
  free={f:b for f,b in faces.items() if f!=square}
  if set.union(*free.values())&protected:continue
  found[row['index']]=(row,geometry(row))
 assert tuple(found)==(106,142)
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

def solve(g,restrict=None):
 total=Fraction();peak=0;n=0
 for weight,core in k2.free_branches(g.free_tori[0]):
  value,size=contraction(g,core,restrict);total+=weight*value;peak=max(peak,size);n+=1
 assert n==3
 return total,peak


EXPECTED_WORDS=(106,142)
EXPECTED_MANIFEST_SHA256='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'

def describe(row,g):
 return {'word':row,'squares':g.squares,'lives':g.lives,'fixed_sources':sorted(g.fixed_sources),'fixed_square':sorted(g.fixed_square[g.squares[0]]),'fixed_edges':sorted(g.fixed_edges),'free_torus':sorted(g.free_tori[0]),'joined_edges':sorted(g.joined_source),'action_edges':len(g.edges),'peeled':10,'divisor':g.divisor}

def source_hashes():
 import importlib
 names=('l1_extended_offset_witness_k2','l1_extended_offset_witness_k3','l1_extended_offset_witness_k4','l1_extended_offset_square','l1_extended_offset_witness','l1_extended_mixed_frame_moment','l1_extended_mixed_center_gamma','l1_extended_mixed_curvature_core','l1_extended_opposed_source','l1_extended_two_mixed_centers','l1_extended_four_face_gauge_join','l1_direct_b_haar','l1_extended_offset_witness_k4_two_square')
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
 binding={'manifest_sha256':EXPECTED_MANIFEST_SHA256,'source_sha256':source_hashes(),'row_cap':k2.ROW_CAP,'pair_cap':k2.PAIR_CAP}
 if args.controls_only:
  for word,(row,g) in found.items():
   k3.square_control(g.squares[0],g.lives[0],g.fixed_square[g.squares[0]])
   value,peak=solve(g,dict.fromkeys(g.frame,k3.witness.FIXED_GAMMAS))
   print(json.dumps({'kind':'fixed-label','word':word,'coefficient':[value.numerator,value.denominator],'peak_rows':peak,**binding},sort_keys=True),flush=True)
  return
 if args.word is None:
  print(json.dumps({'kind':'both-source-square-free-torus-census','origins':[0,1],'valid_words':list(EXPECTED_WORDS),'entries':[describe(row,g) for row,g in found.values()],**binding},sort_keys=True),flush=True)
  return
 row,g=found[args.word];began=perf_counter();value,peak=solve(g);raw=value*g.divisor;assert raw.denominator==1
 print(json.dumps({'kind':'exact-word','replay_geometry':'both-source-square-free-torus',**describe(row,g),'coefficient':[value.numerator,value.denominator],'raw_numerator':raw.numerator,'branches':3,'peak_rows':peak,'seconds':round(perf_counter()-began,3),**binding},sort_keys=True),flush=True)

if __name__=='__main__':main()
