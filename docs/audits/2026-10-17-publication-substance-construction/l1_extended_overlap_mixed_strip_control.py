"""Attach complete frame pairs to the already projected strip, at fixed output masks."""
from collections import Counter
from l1_extended_overlap_mixed_frames import coefficients,PAIR
from l1_extended_overlap_strip import rows

def boundary(frame):
    keys=Counter(k[:3] for row in frame.values() for k in row)
    # Choose an open mixed-frame tensor output with multiple live channels.
    return max(sorted(keys),key=keys.get)

def sample(frame,key):
    return {i:(row.get((*key,0),0),row.get((*key,1),0))
            for i,p in enumerate(PAIR) if (row:=frame[p]) and any(row.get((*key,j),0) for j in range(2))}

if __name__=='__main__':
    F=coefficients()
    key=boundary(F)
    other=next(k[:3] for p,row in F.items() for k in row if k[:3]!=key)
    left,right=sample(F,key),sample(F,other)
    for chosen in (right,left):
        found=Counter()
        for k,row in rows():
            re=im=0
            for (i,j),z in row.items():
                if i in left and j in chosen:
                    r,s=left[i];u,v=chosen[j]
                    re+=z*(r*u-s*v);im+=z*(r*v+s*u)
            if re or im:found[re,im]+=1
        print('fixed frame boundaries',key,other if chosen is right else key,
              'channels',len(left),len(chosen),'nonzero curvature outputs',sum(found.values()),
              'Gaussian histogram',sorted(found.items()),flush=True)
