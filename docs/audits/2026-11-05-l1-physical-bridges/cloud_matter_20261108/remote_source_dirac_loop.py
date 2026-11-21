"""Changed exact curvature factorization; old failed adapter remains untouched."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product
from pathlib import Path
import hashlib,inspect,signal,sys,tempfile,time,traceback
import remote_source_adapter as R
ROW_CAP=120000
PAIR_CAP=3000000

def gaussian(z):
    re,im=z.expand().as_real_imag();assert re.is_Integer and im.is_Integer
    return int(re),int(im)

@cache
def link_rows(C,fixed,dagger):
    rows={}
    for q in ([None] if fixed else range(8)):
        matrix=C.L.eye(4) if fixed else C.basis()[q]
        if dagger:matrix=matrix.H
        for i,j in product(range(4),repeat=2):
            if matrix[i,j]:rows[(i,j) if fixed else (q,i,j)]={0:gaussian(matrix[i,j])}
    assert len(rows)<=(4 if fixed else 16)
    return rows

@cache
def gamma_rows(C,sign):
    rows={};g5=C.L.diag(1,1,-1,-1)
    for a,b in product(range(4),repeat=2):
        if a==b:continue
        matrix=sign*C.L.gamma[a]*C.L.gamma[b]*g5
        for i,j in product(range(4),repeat=2):
            if matrix[i,j]:rows[a,b,i,j]={0:gaussian(matrix[i,j])}
    assert len(rows)==48
    return rows

def curvature_factors(C,legs,indices,sign,spins):
    assert sign in (-1,1) and len(set(spins))==5
    factors=[]
    for step,(position,dagger) in enumerate(((3,True),(2,True),(1,False),(0,False))):
        leg=legs[position];axes=(spins[step],spins[step+1])
        if leg is not None:axes=(leg,)+axes
        factors.append(C.bounded(axes,link_rows(C,leg is None,dagger),{}))
    factors.append(C.bounded(tuple(indices)+(spins[4],spins[0]),gamma_rows(C,sign),{}))
    return factors

@cache
def local_open(C,fixed,sign=1):
    legs=tuple(None if isfixed else ('openq',i) for i,isfixed in enumerate(fixed))
    spins=tuple(('openD',i) for i in range(5));indices=(('opena',0),('openb',0))
    factors=curvature_factors(C,legs,indices,sign,spins)
    current=factors[0];peak=sum(map(len,current[1].values()));visits=0
    for position,right in enumerate(factors[1:]):
        axes,rows,count=C.L.indexed_join(current,right,0,ROW_CAP,PAIR_CAP)
        visits+=count;current=(axes,rows,{})
        size=sum(map(len,rows.values()));peak=max(peak,size)
        assert size<=(6144 if position==3 else (64,256,1024)[position])
    canonical=tuple(leg for leg in legs if leg is not None)+indices
    order=tuple(current[0].index(leg) for leg in canonical)
    rows={tuple(key[i] for i in order):row for key,row in current[1].items()}
    assert len(rows)==len(current[1])
    return rows,peak,visits

def bind_assembly(C):
    source=inspect.getsource(C.assemble)
    old_source="""    if component is not None:
        shared = internal()
        for axis, anchor in zip(component, anchors):
            frame(0, axis, anchor, shared)
"""
    new_source="""    if component is not None:
        factors.append(R.source_factor(C,component,anchors,tree,occurrence))
        frame_count += 4
"""
    old_curvature="""        rows = curvature_table(fixed)
        if sign == -1:
            rows = {key: {0: (-value[0][0], -value[0][1])} for key, value in rows.items()}
        factors.append(bounded(tuple(leg for leg in legs if leg is not None) + (a, b), rows, {}))
"""
    new_curvature="""        spins=tuple(('D',internal()[1]) for _ in range(5))
        factors.extend(curvature_factors(C,legs,(a,b),sign,spins))
"""
    old_divisor='divisor = 4 ** (frame_count + curvature_count) * haar_divisor * multiplicity'
    new_divisor='divisor = 4 ** frame_count * haar_divisor * multiplicity'
    old_metadata="'curvature_quarters': curvature_count,"
    new_metadata="'curvature_quarters': 0, 'curvature_vertices': curvature_count,"
    for old in (old_source,old_curvature,old_divisor,old_metadata):assert source.count(old)==1,old
    adapted=source.replace(old_source,new_source).replace(old_curvature,new_curvature).replace(old_divisor,new_divisor).replace(old_metadata,new_metadata).replace('def assemble(', 'def assemble_loop(',1)
    ns=dict(C.__dict__);ns.update(C=C,R=R,curvature_factors=curvature_factors)
    exec(compile(adapted,'<reviewed-loop-source-transport>','exec'),ns)
    R.emit(event='loop-source-binding',original_assemble_sha256=hashlib.sha256(source.encode()).hexdigest(),loop_assemble_sha256=hashlib.sha256(adapted.encode()).hexdigest(),row_cap=ROW_CAP,pair_cap=PAIR_CAP)
    return ns['assemble_loop']

def loop_controls(C,assemble,directory):
    import controls as old
    for fixed in product((False,True),repeat=4):
        reference=C.curvature_table(fixed)
        for sign in (1,-1):
            rows,peak,visits=local_open(C,fixed,sign)
            assert set(rows)==set(reference)
            for key,row in rows.items():
                assert set(row)=={0}
                re,im=row[0];rr,ii=reference[key][0]
                assert (4*re,4*im)==(sign*rr,sign*ii),(fixed,sign,key)
                assert key[-2]!=key[-1]
            R.emit(event='loop-open-control',fixed=fixed,sign=sign,rows=len(rows),peak=peak,compatible_products=visits)
    # Transport only producer lookup and absorbed-quarter factor in the original
    # full-world control; its independent direct reference and poison are intact.
    source=inspect.getsource(old.curvature)
    lookup='C.curvature_table(fixed).items()'
    weight='F(C.epsilon((k, l, mu, nu)) * tv[mu][a] * tv[nu][b], 4)'
    assert source.count(lookup)==source.count(weight)==1
    changed=source.replace(lookup,'local_open(C,fixed)[0].items()').replace(weight,'F(C.epsilon((k, l, mu, nu)) * tv[mu][a] * tv[nu][b])').replace('def curvature():','def loop_world_control():',1)
    ns=dict(old.__dict__);ns.update(C=C,local_open=local_open)
    exec(compile(changed,'<loop-full-world-control>','exec'),ns)
    R.emit(event='loop-full-world-control',result=ns['loop_world_control']())
    norm=tuple((x,0,1,x,x) for x in range(4) for _ in range(2))
    cases=[(None,None,norm,F(104978))]
    local=tuple((x,0,1,x,x) for x in (1,2,3) for _ in range(2))
    cases.extend([(components,((0,0),(0,0)),local,value) for components,value in [(((2,3),(2,3)),F(52488)),(((2,2),(2,2)),F(218700))]])
    for components,anchors,word,expected in cases:
        factors,divisor,metadata=assemble(components,anchors,None,word)
        assert metadata['frames']==16 and metadata['curvature_quarters']==0
        raw,peak,visits=C.contract(factors)
        assert raw[1]==0 and F(raw[0],divisor)==expected
        R.emit(event='loop-word-control',components=components,value=str(F(raw[0],divisor)),peak=peak,products=visits,divisor=divisor,metadata=metadata)

def run():
    assert not sys.flags.optimize
    signal.signal(signal.SIGALRM,R.alarm);signal.setitimer(signal.ITIMER_REAL,600)
    started=time.monotonic();phase='controls'
    with tempfile.TemporaryDirectory(prefix='l1-cloud-loop-') as tmp:
        directory=Path(tmp)
        try:
            C,original_source_assemble=R.load_archive(directory)
            # Accepted old physical controls stay in place, but their failed
            # mixed target is never called.
            R.controls(C,original_source_assemble,directory)
            assemble=bind_assembly(C);loop_controls(C,assemble,directory)
            R.emit(event='loop-controls-complete',seconds=time.monotonic()-started)
            phase='pilot';signal.setitimer(signal.ITIMER_REAL,60)
            factors,divisor,metadata=assemble(((0,2),(0,2)),((0,0),(0,0)),None,R.PILOT)
            assert metadata['frames']==16 and metadata['curvature_vertices']==6 and metadata['curvature_quarters']==0
            assert metadata['haar_divisor']==4**8*48**5 and metadata['multiplicity_factorial']==8
            assert divisor==4**24*48**5*8
            R.emit(event='loop-pilot-built',word=R.PILOT,divisor=divisor,metadata=metadata)
            raw,peak,visits=C.contract(factors)
            R.emit(event='loop-pilot-result',raw=raw,value_real=str(F(raw[0],divisor)),value_imag=str(F(raw[1],divisor)),peak=peak,products=visits,scope='one anchor-resolved word only')
        except BaseException as exc:
            R.emit(event='loop-terminal-failure',phase=phase,type=type(exc).__name__,reason=str(exc),seconds=time.monotonic()-started)
            traceback.print_exc();raise
        finally:signal.setitimer(signal.ITIMER_REAL,0)
if __name__=='__main__':run()
