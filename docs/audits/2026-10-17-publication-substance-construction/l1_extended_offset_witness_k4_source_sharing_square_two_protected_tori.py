"""Exact selected k4 source-sharing square with two protected tori.

Both sources, all fifteen paired action vertices and sixteen physical Grassmann
sites remain. Joint four-edge forest fixing separates conditional curvature
Haar tensors only; the complete action/source/gamma contraction stays global.
All225 source-ordered protected branch products are retained, including signs
and opposite chirality. This selected family is not the physical B3 response.
"""
import sys,json,hashlib,signal
from pathlib import Path
from collections import Counter,defaultdict,namedtuple
from fractions import Fraction
from itertools import product
from time import perf_counter
AUDIT=Path(__file__).resolve().parent
if not (AUDIT/'l1_extended_offset_witness_k3.py').is_file():
 AUDIT=Path('/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103/docs/audits/2026-10-17-publication-substance-construction')
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
Geometry=namedtuple('Geometry','frame edges sources squares lives fixed_square fixed_edges joined_source divisor fixed_sources tori shared_source forest')

def family_geometry(row):
 frame,sources,edges,faces,protected,removed=two.base(row)
 if len(frame)!=15 or len(row['changes'])!=4 or len(faces)!=9 or len(removed)!=6:return None
 squares=tuple(f for f,b in faces.items() if b<=protected)
 if len(squares)!=1:return None
 square,=squares;rest={f:b for f,b in faces.items() if f!=square}
 if any(f[1:]!=(2,3) for f in rest):return None
 groups=[{f:b for f,b in rest.items() if f[0]&3==c} for c in sorted({f[0]&3 for f in rest})]
 if len(groups)!=2 or any(len(t)!=4 for t in groups):return None
 incidence=[set.union(*t.values())&protected for t in groups]
 if any(len(s)!=1 or not s<=set(sources) for s in incidence):return None
 if set.union(*incidence)!=set(sources):return None
 shared=faces[square]&set.union(*(set.union(*t.values()) for t in groups))
 if len(shared)!=1 or not shared<=set(sources):return None
 shared_source,=shared
 assert not set.union(*groups[0].values())&set.union(*groups[1].values())
 assert not (faces[square]-shared)&set.union(*(set.union(*t.values()) for t in groups))
 live=square[0],square[1];fixed=dict.fromkeys(faces[square]-{live},IDENTITY)
 forest=set(fixed)|set(sources);assert len(fixed)==3 and len(forest)==4
 parent={}
 def root(q):
  while q in parent:q=parent[q]
  return q
 vertices=set()
 for q,a in sorted(forest):
  y=q^(1<<a);vertices.update((q,y));u,v=root(q),root(y);assert u!=v;parent[u]=v
 assert len(vertices)==6 and len({root(q) for q in vertices})==2
 fixed_edges={}
 for q,a in fixed:
  y=q^(1<<a);fixed_edges[min(q,y),max(q,y),a]=int(q>y)
 tori=[]
 for t,inc in zip(groups,incidence,strict=True):
  source,=inc;q,a=source;linked=q,q^(1<<a);other=tuple(f[0] for f in t if f[0] not in linked)
  assert len(other)==2 and set(linked)<=set(f[0] for f in t)
  assert sum(source in b for b in t.values())==2
  tori.append(Torus(t,source,linked,other))
 tori=tuple(sorted(tori,key=lambda t:t.fixed_source))
 assert len(edges)==20 and square[0] not in {f[0] for t in tori for f in t.faces}
 assert all((min(q,q^(1<<a)),max(q,q^(1<<a)),a) not in edges for q,a in sources)
 q,a=live;y=q^(1<<a);key=min(q,y),max(q,y),a
 assert len(edges[key])==1
 center,axis=edges[key][0]
 assert frame[center].index(axis)==1 and center==key[0] and q==key[1]
 actual_fixed=[]
 for edge,anchor in sorted(fixed_edges.items()):
  if edge not in edges:continue
  labels=edges[edge];assert len(labels)==1
  c,axis=labels[0];assert frame[c].index(axis)==1
  actual_fixed.append((int(c==edge[1]),anchor))
 assert sorted(actual_fixed)==[(0,1),(1,0)]
 endpoints=Counter(v for q,a in sources for v in (q,q^(1<<a)))
 incoming=Counter(q^(1<<a) for q,axes in frame.items() for a in axes)
 assert all(4*(q in frame)+2*incoming[q]+2*endpoints[q]==8 for q in range(16))
 divisor=k3.witness.SCALE**(2*len(edges)+2)*4**64*48**6*2**15
 return Geometry(frame,edges,sources,squares,(live,),{square:fixed},fixed_edges,{},divisor,set(sources),tori,shared_source,forest)

def geometry(row):
 result=family_geometry(row);assert result is not None
 return result

def data():
 manifest,_=k4.data();found={}
 assert hashlib.sha256(json.dumps(manifest,sort_keys=True,separators=(',',':')).encode()).hexdigest()==EXPECTED_MANIFEST_SHA256
 for row in manifest['rows']:
  g=family_geometry(row)
  if g is not None:found[row['index']]=(row,g)
 assert tuple(found)==EXPECTED_WORDS
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

EXPECTED_WORDS=(79,81)
EXPECTED_MANIFEST_SHA256='ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b'

def describe(row,g):
 square,=g.squares;live,=g.lives;q,a=live;y=q^(1<<a);key=min(q,y),max(q,y),a
 def routing(edge,labels,anchor):
  return {'edge':edge,'physical_anchor':anchor,'labels':[{'center':c,'axis':axis,'frame_gamma_slot':g.frame[c].index(axis),'center_flag':int(c==edge[1])} for c,axis in labels]}
 fixed=[routing(e,g.edges[e],anchor) for e,anchor in sorted(g.fixed_edges.items()) if e in g.edges]
 return {'word':row,'sources':g.sources,'fixed_sources':sorted(g.fixed_sources),
         'squares':g.squares,'lives':g.lives,'fixed_square_links':sorted(g.fixed_square[square]),
         'joint_forest':sorted(g.forest),'forest_components':2,'shared_source':g.shared_source,
         'tori':[{'faces':sorted(t.faces),'fixed_source':t.fixed_source,'linked':t.linked,'other':t.other} for t in g.tori],
         'live_action_routing':routing(key,g.edges[key],int(q==key[1])),
         'fixed_action_routing':fixed,'action_edges':len(g.edges),'joined_edges':sorted(g.joined_source),
         'paired_action_vertices':len(g.frame),'grassmann_sites':16,'peeled':6,'divisor':g.divisor,
         'branch_order':'source0_major_source1_minor','xor1_branch_map':'15*i+j -> 15*j+i'}


def source_hashes():
 import importlib
 names=('l1_direct_b_haar', 'l1_extended_four_face_gauge_join', 'l1_extended_mixed_center_gamma', 'l1_extended_mixed_curvature_core', 'l1_extended_mixed_frame_moment', 'l1_extended_offset_square', 'l1_extended_offset_witness', 'l1_extended_offset_witness_k2', 'l1_extended_offset_witness_k3', 'l1_extended_offset_witness_k4', 'l1_extended_offset_witness_k4_free_torus', 'l1_extended_offset_witness_k4_peeled', 'l1_extended_offset_witness_k4_single_square', 'l1_extended_offset_witness_k4_two_square', 'l1_extended_opposed_source', 'l1_extended_two_mixed_centers')
 modules=[importlib.import_module(n) for n in names]
 assert all(Path(m.__file__).parent==AUDIT for m in modules)
 result={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in modules}
 result['evaluator']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 return result

def prepare_branches(g,restrict=None):
 prepared=[(weight,prepare(g,core,restrict)) for weight,core in branches(g)]
 assert len(prepared)==225
 return prepared


def contract_prepared(prepared,divisor,emit_branch=None):
 """Contract the already prepared tables once, retaining exact branch weights."""
 assert len(prepared)==225
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


# Cold snapshots preserve factor, axis, row, mask and degree iteration order.
# Equal complete inputs share only terminal successful exact (raw, peak) values.
EXPECTED_SIBLING_SHA256={'l1_direct_b_haar.py': '535d4233a51b89e44f8b9d9b8d01ed624b659d68f1ee9e10ec14efea060900b1', 'l1_extended_four_face_gauge_join.py': '4ddfbc8731cc8c8f546b4347c28718fc3917e131d3a5f461fef19f67122ec91b', 'l1_extended_mixed_center_gamma.py': 'a3dcaffb79e59a174b3a2816d207d8ced22e2bd11a9e05b8c9ea07a20d9c158d', 'l1_extended_mixed_curvature_core.py': '24f640e140b8ab179779f8fc9f5029c2484d834a8f79d5f134991822d2010242', 'l1_extended_mixed_frame_moment.py': '3d1e8d1e1281e6a27223224cf0cbb7dc0545e9c7c035951a0adabd97d9cf3137', 'l1_extended_offset_square.py': '32373f84a267f266e29dea45fa4fe4dc49823be288f1e37dc168dabf06c1793d', 'l1_extended_offset_witness.py': 'e558b5a3211ee2ff62bd4f9d8b06c762ba26d3e041eb8a70280fee7464a4dd0f', 'l1_extended_offset_witness_k2.py': '1d10dc5705e89e8d16cc9e6991b7547b2d8b67bb52e257505aa04259c85455d7', 'l1_extended_offset_witness_k3.py': 'fa1ef180c87707c6e9a4a13410890b77b04c3620774587a81d00dd9b34e2c73d', 'l1_extended_offset_witness_k4.py': 'b2b6027c9a3f13dab49b9c72efd09ecc9dbf1e6bf3ab9903fdb008ac79fd12e0', 'l1_extended_offset_witness_k4_free_torus.py': 'ba82ce5abdcc35dc0e4d98fe52fef1f275837f7063074babfb2cd95c0ab24109', 'l1_extended_offset_witness_k4_peeled.py': '7eb0114dec24a2cc0674c2e3e3865ffc34d12924f131868d95ad121c62d31a4c', 'l1_extended_offset_witness_k4_single_square.py': '4fd18a9a852ce9c1d331f9462f4436d7d8d41f6cd10f408e0dfa2c3aca2729dd', 'l1_extended_offset_witness_k4_two_square.py': '1bd858308e4ba5be3d9d25ce1b0d0a8695600b7b030e45e765d923c60610e78b', 'l1_extended_opposed_source.py': '06e16f2f83062b1b123bf2a6ce7150522114a43c2af06fb117e73823a6bc42f5', 'l1_extended_two_mixed_centers.py': '6f950654cc6e2650246dcb55623040f22e5a3bda7a5ce74c4ab7f0eaf9f628b2'}

FrozenPrepared=namedtuple('FrozenPrepared','entries context unique_inputs branches')

def _reuse_context():
 assert k2.ROW_CAP==120000 and k2.PAIR_CAP==3000000
 fingerprint=source_hashes()
 assert set(fingerprint)==set(EXPECTED_SIBLING_SHA256)|{'evaluator'}
 assert all(fingerprint[name]==expected for name,expected in EXPECTED_SIBLING_SHA256.items())
 functions=(k3.eliminate_components,k2.eliminate,k2.choose,k2.indexed_join,k2.preceding_parity)
 return tuple((f,getattr(f,'__code__',None)) for f in functions)+(k2.ROW_CAP,k2.PAIR_CAP,tuple(sorted(fingerprint.items())))

def _freeze_label(value):
 if type(value) is tuple:return tuple(_freeze_label(v) for v in value)
 assert type(value) in (int,str)
 return value

def freeze_prepared(prepared,divisor):
 """Snapshot all effective inputs without contracting; charge this work to cold."""
 assert len(prepared)==225 and type(divisor) is int and divisor>0
 context=_reuse_context();entries=[];unique=set()
 for weight,table in prepared:
  weight=Fraction(weight)
  if table is None:descriptor=None
  else:
   factors,local_divisor,exclusive=table
   assert type(local_divisor) is int and local_divisor==divisor
   frozen_factors=[]
   for axes,rows,degrees in factors:
    frozen_rows=[]
    for key,poly in rows.items():
     frozen_poly=[]
     for mask,pair in poly.items():
      assert type(mask) is int and type(pair) is tuple and len(pair)==2
      assert all(type(v) is int for v in pair)
      frozen_poly.append((mask,pair))
     frozen_rows.append((_freeze_label(key),tuple(frozen_poly)))
    assert all(type(q) is int and type(d) is int for q,d in degrees.items())
    frozen_factors.append((_freeze_label(axes),tuple(frozen_rows),tuple(degrees.items())))
   descriptor=(local_divisor,tuple(frozen_factors),frozenset(_freeze_label(k) for k in exclusive))
   unique.add(descriptor)
  entries.append((weight,descriptor))
 assert _reuse_context()==context
 return FrozenPrepared(tuple(entries),context,len(unique),len(entries))

def contract_frozen(frozen,divisor,emit_branch=None):
 """One whole225 warm pass; materialize private inputs only for first exact keys."""
 assert frozen.branches==len(frozen.entries)==225
 assert _reuse_context()==frozen.context
 cache={};total=Fraction();peak=0
 for branch,(weight,descriptor) in enumerate(frozen.entries):
  assert _reuse_context()==frozen.context
  reused=False;representative=None
  if descriptor is None:raw,size=0,0
  else:
   local_divisor,factors,exclusive=descriptor
   # Keep the baseline local-divisor assertion ahead of every possible cache hit.
   assert local_divisor==divisor
   hit=cache.get(descriptor)
   if hit is not None:
    raw,size,representative=hit;reused=True
   else:
    private=[(axes,{key:dict(poly) for key,poly in rows},dict(degrees)) for axes,rows,degrees in factors]
    raw,size=k3.eliminate_components(private,set(exclusive))
    assert _reuse_context()==frozen.context
    representative=branch;cache[descriptor]=(raw,size,branch)
  value=Fraction(raw,divisor);total+=weight*value;peak=max(peak,size)
  if emit_branch is not None:
   emit_branch({'branch':branch,'weight':[weight.numerator,weight.denominator],
                'raw_numerator':raw,'divisor':divisor,
                'coefficient':[value.numerator,value.denominator],
                'algebraic_empty_preparation':descriptor is None,'peak_rows':size,
                'reused_contraction':reused,'representative_branch':representative})
  assert _reuse_context()==frozen.context
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
   frozen=freeze_prepared(prepared,g.divisor)
   value,peak=contract_frozen(frozen,g.divisor,lambda r:print(json.dumps({'kind':'exact-fixed-branch','word':word,**r},sort_keys=True),flush=True))
   print(json.dumps({'kind':'fixed-label','word':word,'branches':225,
                     'scope':'Fixed-gamma control','coefficient':[value.numerator,value.denominator],
                     'peak_rows':peak,'actual_unique_inputs':frozen.unique_inputs,**binding},sort_keys=True),flush=True)
  return
 if args.word is None:
  print(json.dumps({'kind':'source-sharing-square-two-protected-tori-census','origins':[0,1],
                    'valid_words':list(EXPECTED_WORDS),
                    'entries':[describe(row,g) for row,g in found.values()],
                    **binding},sort_keys=True),flush=True)
  return
 row,g=found[args.word];began=perf_counter();prepared=prepare_branches(g)
 frozen=freeze_prepared(prepared,g.divisor)
 prep_seconds=perf_counter()-began;warm_start=perf_counter()
 value,peak=contract_frozen(frozen,g.divisor,lambda r:print(json.dumps({'kind':'exact-branch','word':args.word,**r},sort_keys=True),flush=True))
 warm_seconds=perf_counter()-warm_start;raw=value*g.divisor;assert raw.denominator==1
 print(json.dumps({'kind':'exact-word','replay_geometry':'source-sharing-square-two-protected-tori',
                   'scope':'Complete selected unrestricted word',**describe(row,g),
                   'coefficient':[value.numerator,value.denominator],
                   'raw_numerator':raw.numerator,'branches':225,'peak_rows':peak,
                   'preparation_seconds':prep_seconds,'whole225_warm_seconds':warm_seconds,
                   'actual_unique_inputs':frozen.unique_inputs,
                   'seconds':round(perf_counter()-began,3),**binding},sort_keys=True),flush=True)

if __name__=='__main__':main()
