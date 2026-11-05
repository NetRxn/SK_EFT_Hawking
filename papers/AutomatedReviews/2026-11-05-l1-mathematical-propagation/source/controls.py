from pathlib import Path
from decimal import Decimal,localcontext
from fractions import Fraction
import hashlib,json,re
b=Path('/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103')
o=Path('/tmp/l1-source-math-author-20261105-r1')
s=(b/'papers/paper25_gravitational_waves/paper_draft.tex').read_text(); p=(o/'paper_draft.tex').read_text()
# Ad hoc intake assertions only; not a repository gate or a scientific build.
for name, bad in [
 ('susceptibility tolerance is not speed tolerance',r'\chivest = 1 \pm 3\times 10^{-15}'),
 ('finite tolerance does not require exact unity','sits exactly at unity'),
 ('width does not establish every prior mass','exponentially small measure in any'),
 ('quarter does not isolate P3 independence',"the fourth isolates P3'"),
 ('endpoints have different cap ratios',r'\sim 7\times 10^{14}$ at the'),
 ('endpoints do not exclude the whole range','the natural range fails by'),
 ('finite tolerance is not exact luminality',r'locating the $\cGW = c$ window'),
]:
 try: assert bad not in s,name
 except AssertionError: print('ORIGINAL RED:',name)
 else: raise AssertionError('Original control did not fail: '+name)
 assert bad not in p,name
 print('PROPOSED PASS:',name)
with localcontext() as ctx:
 ctx.prec=80
 t=Decimal('3e-15'); lo=(1-t)**2; hi=(1+t)**2
 assert hi-lo==4*t
 assert (lo+hi)/2==1+t*t
 assert (hi-lo)/2==2*t
 assert lo<1-t<1+t<hi # advertised 1 +/- tau is only a strict subset
 speed=1+Decimal('.75')*t; chi=speed*speed
 assert abs(speed-1)<=t and chi>1+t and chi!=1 # explicit compatible counterexample
 ratios=[abs(x.sqrt()-1)/t for x in [Decimal('.1'),Decimal('10')]]
 assert ratios[0]>Decimal('2.27e14') and ratios[0]<Decimal('2.29e14')
 assert ratios[1]>Decimal('7.20e14') and ratios[1]<Decimal('7.22e14')
 assert t<Decimal('.5') # P2 => P3'
 delta=Decimal('.25').sqrt()-1
 assert delta==Decimal('-.5') and abs(delta)>t and not abs(delta)<Decimal('.5')
 # Probability counterexamples: uniform vs point mass at allowed anchor.
 uniform=(hi-lo)/Decimal('9.9'); atomic=Decimal(1)
 assert uniform<Decimal('2e-15') and atomic>uniform
 vals={'tau':str(t),'lower':str(lo),'upper':str(hi),'center':str((lo+hi)/2),'half_width':str((hi-lo)/2),'width':str(hi-lo),'endpoint_ratios':[str(x) for x in ratios],'uniform_mass':str(uniform),'point_mass_at_anchor':str(atomic)}
(o/'math_controls.json').write_text(json.dumps(vals,indent=2)+'\n')
# Preserve every existing theorem identifier represented in supplied actual declaration evidence.
x=json.load(open(b/'papers/AutomatedReviews/2026-11-05-l1-current-claims/r1/lean_actual_declarations.json'))
used=[]
for d in x:
 if d['autogen']: continue
 name=d['name'].split('.')[-1]
 if d['module']=='SKEFTHawking.GravitationalWaves' and (name in s or name.replace('_',r'\_') in s):
  assert name in p or name.replace('_',r'\_') in p,name
  used.append({'name':d['name'],'type':d['type']})
(o/'statement_provenance.json').write_text(json.dumps(used,indent=2)+'\n')
assert re.findall(r'\\includegraphics.*',s)==re.findall(r'\\includegraphics.*',p)
assert [l for l in s.splitlines() if 'pytest' in l]==[l for l in p.splitlines() if 'pytest' in l]
assert s[s.index(r'\section{Dispersion correction'):s.index(r'\section{Result figure')]==p[p.index(r'\section{Dispersion correction'):p.index(r'\section{Result figure')]
assert s[s.index(r'\begin{equation*}',s.index(r'\subsection{The bundled hypothesis}')):s.index(r'\end{equation*}',s.index(r'\subsection{The bundled hypothesis}'))]==p[p.index(r'\begin{equation*}',p.index(r'\subsection{The bundled hypothesis}')):p.index(r'\end{equation*}',p.index(r'\subsection{The bundled hypothesis}'))]
assert hashlib.sha256((b/'papers/paper25_gravitational_waves/paper_draft.tex').read_bytes()).hexdigest()=='75a84e6136717a2db4158f9b35c51b9026563a1869b48c3243a01abcbbf27048'
print('PASS: exact Decimal/Fraction logic, prior counterexample, theorem identifiers, figure path, pytest line, dispersion section, Prop display and unchanged tracked source')
