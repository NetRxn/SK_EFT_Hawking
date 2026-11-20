from l1_diagonal_classes import remain, zero, orbits, TERMS, labels
def isolates(terms,x):
    for j in (2,3):
        motif={(x,0,j,x,x),(x,1,j,x,x),(x,2,3,x,x)}
        indices=[i for i in terms if TERMS[i][2] in motif]
        if len(indices)!=3 or {TERMS[i][2] for i in indices}!=motif:continue
        if all(all(y!=x for y,d in labels(i)) for i in terms if i not in indices):
            return True
    return False
more=[ii for ii in remain if ii not in zero and any(isolates(ii,x) for x in (1,2))]
print('exact sparse center cancellation:',len(more),'multisets;',sum(ii in more for ii in orbits),'orbits')
print('remaining:',len(remain)-len(zero)-len(more),'multisets;',sum(ii not in more and ii not in zero for ii in orbits),'orbits')
