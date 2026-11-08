"""Bounded source-resolved pure-g2 covariance pilot; reuses archived exact engine."""
from pathlib import Path
from zipfile import ZipFile
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod,comb
import ast,hashlib,importlib.util,inspect,json,signal,subprocess,sys,tempfile,time,traceback

AUDITS=Path(__file__).resolve().parents[2]
ARCHIVE=AUDITS/'2026-11-05-l1-physical-bridges/leading_metric_order_source_r1.zip'
ROW_CAP=120000
PAIR_CAP=3000000
PILOT=((1,0,3,1,1),)*2+((2,0,2,2,2),)*2+((3,1,2,3,3),)*2

def emit(**record):print(json.dumps(record,sort_keys=True,default=str),flush=True)
def alarm(signum,frame):raise TimeoutError('Prospectively declared source-resolved phase deadline')
def bounded_wedge(L,A,B,stats):
    candidates=len(A)*len(B)
    if candidates>PAIR_CAP:raise RuntimeError('source wedge input-product upper bound exceeds original pair cap')
    stats['candidate_products']+=candidates;stats['calls']+=1
    stats['largest_wedge_product']=max(stats['largest_wedge_product'],candidates)
    if not A or not B:return {}
    degrees=[]
    for poly in (A,B):
        first=next(iter(poly));degree=tuple(((first>>(8*x))&255).bit_count() for x in range(4))
        assert all(tuple(((m>>(8*x))&255).bit_count() for x in range(4))==degree for m in poly)
        degrees.append(degree)
    summed=tuple(a+b for a,b in zip(*degrees))
    if any(d>8 for d in summed):return {}
    bound=min(candidates,prod(comb(8,d) for d in summed))
    if bound>ROW_CAP:raise RuntimeError('source wedge preallocation mask bound exceeds original row cap')
    out=L.wedge(A,B)
    assert len(out)<=bound<=ROW_CAP
    stats['peak_single_polynomial_rows']=max(stats['peak_single_polynomial_rows'],len(A),len(B),len(out))
    return out

def source_factor(C,components,anchors,tree,occurrence):
    assert len(components)==len(anchors)==2
    axes=tuple(axis for pair in components for axis in pair)
    origins=tuple(anchor for pair in anchors for anchor in pair)
    legs=[occurrence((anchor,axis)) for axis,anchor in zip(axes,origins)]
    free=[i for i,leg in enumerate(legs) if leg is not None]
    rows={};allocated=0
    stats={"calls":0,"candidate_products":0,"largest_wedge_product":0,"peak_single_polynomial_rows":0}
    degrees=Counter(x for axis in axes for x in (0,C.S.forward(0,axis)))
    for values in product(range(8),repeat=len(free)):
        coords=dict(zip(free,values));frames=[]
        for i,(axis,anchor) in enumerate(zip(axes,origins)):
            if i in coords:frames.append(C.L.fixed_frame(0,axis,anchor,coords[i]))
            else:frames.append(tuple(C.L.add(a,b) for a,b in zip(C.L.fixed_frame(0,axis,anchor,0),C.L.fixed_frame(0,axis,anchor,4))))
        metrics=[]
        for a,b in ((0,1),(2,3)):
            metrics.append(C.L.add(*(bounded_wedge(C.L,frames[a][i],frames[b][i],stats) for i in range(4))))
        poly=bounded_wedge(C.L,*metrics,stats)
        row=C.L.sparse_int(poly)
        if row:
            allocated+=len(row)
            if allocated>ROW_CAP:raise RuntimeError(f'{allocated} source boundary rows exceed original cap{ROW_CAP}')
            rows[values]=row
    emit(event="source-boundary",components=components,anchors=anchors,rows=allocated,degrees=dict(degrees),factory=stats)
    return C.bounded(tuple(legs[i] for i in free),rows,degrees)

def load_archive(directory):
    z=ZipFile(ARCHIVE);manifest=json.loads(z.read('manifest.json'))
    for name,entry in manifest['members'].items():
        assert hashlib.sha256(z.read(name)).hexdigest()==entry['sha256'],name
    for name in z.namelist():
        if name.startswith('source/') and not name.endswith('/'):
            relative=Path(name).relative_to('source');assert '..' not in relative.parts
            path=directory/relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(z.read(name))
    sys.path.insert(0,str(directory))
    spec=importlib.util.spec_from_file_location('leading',directory/'leading.py')
    C=importlib.util.module_from_spec(spec);sys.modules['leading']=C;spec.loader.exec_module(C);C.bind()
    assert C.ROW_CAP==ROW_CAP and C.PAIR_CAP==PAIR_CAP
    source=inspect.getsource(C.assemble)
    old="""    if component is not None:
        shared = internal()
        for axis, anchor in zip(component, anchors):
            frame(0, axis, anchor, shared)
"""
    new="""    if component is not None:
        factors.append(source_factor(C,component,anchors,tree,occurrence))
        frame_count += 4
"""
    assert source.count(old)==1
    replacement=source.replace(old,new).replace('def assemble(', 'def assemble_pair(',1)
    ns=dict(C.__dict__);ns.update(C=C,source_factor=source_factor)
    exec(compile(replacement,'<source-block-only-adapter>','exec'),ns)
    emit(event='source-binding',archive_sha256=hashlib.sha256(ARCHIVE.read_bytes()).hexdigest(),
         original_assemble_sha256=hashlib.sha256(source.encode()).hexdigest(),
         adapter_assemble_sha256=hashlib.sha256(replacement.encode()).hexdigest(),row_cap=ROW_CAP,pair_cap=PAIR_CAP)
    return C,ns['assemble_pair']

def direct_source_controls(C,old):
    L=C.L;checked=closed_checks=0
    for components in (((0,2),(0,2)),((2,3),(2,3)),((2,2),(2,2))):
        anchors=((0,0),(0,0));edge_legs=[]
        def occurrence(edge):
            if edge in C.TREE:return None
            leg=('source-control',len(edge_legs));edge_legs.append((leg,edge));return leg
        factor=source_factor(C,components,anchors,C.TREE,occurrence)
        free_edges=[edge for leg,edge in edge_legs]
        source_degrees=factor[2]
        for sl,sr in ((0,1),(1,2),(2,3),(3,0)):
            matrices,coords=old.fixtures(sl,sr,C.TREE)
            direct=[]
            for axes,aa in zip(components,anchors):
                frames=[]
                for axis,anchor in zip(axes,aa):
                    y=C.S.forward(0,axis);U=matrices[anchor,axis];Ud=U.H
                    if y==0:
                        delta=Ud-U;frame=tuple(L.bilinear(g*delta+delta*g,0,0) for g in L.gamma)
                    elif anchor==0:
                        frame=tuple(L.add(L.bilinear(g*Ud,0,y),L.scale(L.bilinear(U*g,y,0),-1)) for g in L.gamma)
                    else:
                        frame=tuple(L.add(L.bilinear(Ud*g,0,y),L.scale(L.bilinear(g*U,y,0),-1)) for g in L.gamma)
                    frames.append(frame)
                direct.append(L.add(*(L.wedge(a,b) for a,b in zip(*frames))))
            expected=L.sparse_int(L.wedge(*direct));actual={}
            for key,row in factor[1].items():
                weight=prod(coords[edge][q] for edge,q in zip(free_edges,key))
                if weight:actual=old.addpairs(actual,row,weight)
            assert actual==expected,(components,sl,sr)
            checked+=1
            if sl==0:
                for mask,value in list(expected.items())[:2]:
                    complement=((1<<32)-1)^mask
                    closure={x:8-source_degrees.get(x,0) for x in range(4) if source_degrees.get(x,0)<8}
                    factors=[factor,((),{():{complement:(1,0)}},closure)]
                    for leg,edge in edge_legs:
                        factors.append(((leg,),{(q,):{0:(v,0)} for q,v in enumerate(coords[edge]) if v},{}))
                    raw,peak,visits=C.contract(factors)
                    sign=1-2*((mask & L.preceding_parity(complement)).bit_count()&1)
                    assert raw==(sign*value[0],sign*value[1])
                    closed_checks+=1
    emit(event='source-direct-controls',fixed_matrix_comparisons=checked,complement_closures=closed_checks)

def controls(C,assemble,directory):
    import controls as old
    # Original exact primitive controls, with only new target/source-specific additions.
    r=subprocess.run([sys.executable,'-B',str(directory/'test_scientific_controls.py')],capture_output=True,text=True,timeout=120)
    emit(event='tiny-controls',exit=r.returncode,stdout=r.stdout,stderr=r.stderr);assert r.returncode==0
    for name in ('moments','frames','curvature'):
        result=getattr(old,name)();emit(event='archived-'+name,result=result)
    direct_source_controls(C,old)
    norm=tuple((x,0,1,x,x) for x in range(4) for _ in range(2))
    factors,divisor,meta=C.assemble(None,None,None,norm)
    raw,peak,visits=C.contract(factors);assert raw[1]==0 and F(raw[0],divisor)==104978
    emit(event='normalization-control',value=str(F(raw[0],divisor)),peak=peak,products=visits)
    local=tuple((x,0,1,x,x) for x in (1,2,3) for _ in range(2))
    for component,expected in [(((2,3),(2,3)),F(52488)),(((2,2),(2,2)),F(218700))]:
        factors,divisor,meta=assemble(component,((0,0),(0,0)),None,local)
        assert meta['frames']==16 and meta['curvature_quarters']==6
        raw,peak,visits=C.contract(factors);assert raw[1]==0 and F(raw[0],divisor)==expected
        emit(event='source-word-control',components=component,value=str(F(raw[0],divisor)),peak=peak,products=visits,metadata=meta)

def run():
    assert not sys.flags.optimize
    signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,600)
    started=time.monotonic();phase='controls'
    with tempfile.TemporaryDirectory(prefix='l1-cloud-source-') as tmp:
        directory=Path(tmp)
        try:
            C,assemble=load_archive(directory)
            controls(C,assemble,directory)
            emit(event='controls-complete',seconds=time.monotonic()-started)
            phase='pilot';signal.setitimer(signal.ITIMER_REAL,60)
            factors,divisor,meta=assemble(((0,2),(0,2)),((0,0),(0,0)),None,PILOT)
            assert meta['frames']==16 and meta['curvature_quarters']==6
            assert meta['haar_divisor']==4**8*48**5 and meta['multiplicity_factorial']==8
            assert divisor==4**30*48**5*8
            emit(event='pilot-built',word=PILOT,components=((0,2),(0,2)),anchors=((0,0),(0,0)),divisor=divisor,metadata=meta)
            raw,peak,visits=C.contract(factors)
            emit(event='pilot-result',raw=raw,value_real=str(F(raw[0],divisor)),value_imag=str(F(raw[1],divisor)),peak=peak,products=visits,scope='one anchor-resolved word only; not full covariance')
        except BaseException as exc:
            emit(event='terminal-failure',phase=phase,type=type(exc).__name__,reason=str(exc),seconds=time.monotonic()-started)
            traceback.print_exc();raise
        finally:signal.setitimer(signal.ITIMER_REAL,0)
if __name__=='__main__':run()
