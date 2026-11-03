from collections import Counter
from itertools import combinations_with_replacement, product

DIRECTIONS = (1, 2, 3)
BASIS = tuple(product(range(2), DIRECTIONS))
OPS = tuple(product("AB", range(2), DIRECTIONS))


def generators(op):
    kind, x, j = op
    local, remote = {"A": (4,0), "B": (3,1), "H": (3,1)}[kind]
    return (local,remote) if x==0 else (remote,local)


def center(op):
    kind, x, j = op
    if kind == "A":
        return (7 << (3*x)) ^ (1 << (3*(1-x)+j-1))
    return 1 << (3*x+j-1)


def survivor(ops):
    even=0
    for op in ops:
        even^=center(op)
    return not even and tuple(map(sum,zip(*(generators(op) for op in ops))))==(8,8)


patterns=Counter()
for x,j in BASIS:
    for y,k in BASIS:
        sources=(("H",x,j),("H",y,k))
        surviving=[pair for pair in combinations_with_replacement(OPS,2) if survivor(sources+pair)]
        if x==y and j==k:
            assert surviving==[(("B",1-x,a),)*2 for a in DIRECTIONS]
            patterns["same coordinate"]+=1
        elif x==y:
            assert surviving==[]
            patterns["same site distinct shear"]+=1
        else:
            assert surviving==[(("B",0,j if x==0 else k),("B",1,k if y==1 else j))]
            patterns["different sites, mean-zero curvature survives only parity"]+=1
for x,j in BASIS:
    survivors=[terms for terms in combinations_with_replacement(OPS,3)
               if survivor((("H",x,j),)+terms)]
    assert survivors==[tuple(sorted((("B",x,j),("B",1-x,a),("B",1-x,a)))) for a in DIRECTIONS]
print(dict(patterns))
print("All six linear sources: three parity survivors, all contain one independent mean-zero curvature")
