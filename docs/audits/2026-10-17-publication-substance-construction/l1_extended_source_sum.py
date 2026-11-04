"""Reducer for the scaled separated-source scalar."""
from collections import Counter
from fractions import Fraction
from sys import argv
source=0
coverage=Counter()
for index,line in enumerate(open(argv[1])):
    i,weight,count,live,value,elapsed,mode=line.split()
    assert int(i)==index
    coverage[mode]+=1
    source+=int(weight)*int(value)
assert coverage=={'exact':320,'proportional':450,'parity':34314}
baseline=4549345865844500133837056022073964680182394381773293174409658368
z=Fraction(1057574865922986076396613,3696469150265516934764386546876416)
same=-Fraction(139968,52489)*z
separated=Fraction(source,2*baseline)*same
print('coverage',coverage,'raw',source)
print('separated / same',Fraction(source,2*baseline))
print('same single',same,'separated single',separated)
print('same eight',8*same,'separated eight',8*separated,'complete',8*(same+separated))
