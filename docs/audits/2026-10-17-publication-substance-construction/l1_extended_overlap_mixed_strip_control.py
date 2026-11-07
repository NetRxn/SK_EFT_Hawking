"""Compare early and late frame attachment at fixed exterior masks."""
from collections import Counter
from l1_extended_overlap_mixed_frames import coefficients,PAIR
from functools import cache
from l1_extended_overlap_strip import HAAR,rows

def boundary(frame):
    keys=Counter(k[:3] for row in frame.values() for k in row)
    # Choose an open mixed-frame tensor output with multiple live channels.
    return max(sorted(keys),key=keys.get)

def sample(frame,key):
    return {i:(row.get((*key,0),0),row.get((*key,1),0))
            for i,p in enumerate(PAIR) if (row:=frame[p]) and any(row.get((*key,j),0) for j in range(2))}

def attach_moments(frame):
    """Apply the scaled Haar map to the actual frame slice on one link."""
    @cache
    def attached(pair):
        weights = HAAR[pair]
        return tuple(sum(weight * frame.get(i, (0, 0))[j]
                         for i, weight in weights) for j in range(2))
    return attached


def attach_staged(left, right):
    attach_left, attach_right = map(attach_moments, (left, right))
    for key, row in rows(raw=True):
        boundary = {}
        for (a, b), coefficient in row.items():
            r, i = attach_left(a)
            old_r, old_i = boundary.get(b, (0, 0))
            boundary[b] = old_r + coefficient * r, old_i + coefficient * i
        re = im = 0
        for b, (r, i) in boundary.items():
            u, v = attach_right(b)
            re += r*u - i*v
            im += r*v + i*u
        if re or im:
            yield key, (re, im)


if __name__=='__main__':
    F=coefficients()
    key=boundary(F)
    other=next(k[:3] for p,row in F.items() for k in row if k[:3]!=key)
    left,right=sample(F,key),sample(F,other)
    for chosen in (right,left):
        direct={}
        for k,row in rows():
            re=im=0
            for (i,j),z in row.items():
                if i in left and j in chosen:
                    r,s=left[i];u,v=chosen[j]
                    re+=z*(r*u-s*v);im+=z*(r*v+s*u)
            if re or im:direct[k]=(re,im)
        assert dict(attach_staged(left, chosen)) == direct
        found=Counter(direct.values())
        print('fixed frame boundaries',key,other if chosen is right else key,
              'channels',len(left),len(chosen),'nonzero curvature outputs',sum(found.values()),
              'Gaussian histogram',sorted(found.items()),flush=True)
