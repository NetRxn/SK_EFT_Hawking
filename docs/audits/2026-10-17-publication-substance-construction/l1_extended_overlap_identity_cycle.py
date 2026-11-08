from functools import cache
from fractions import Fraction
from sys import argv

def dot(a,b):return int(a==b)
def trace4_pauli(a,b,c,d):
    return 2*(dot(a,b)*dot(c,d)-dot(a,c)*dot(b,d)+dot(a,d)*dot(b,c))

@cache
def trace4_so3(indices):
    matrices=[]
    for a,b in indices:
        if a==b:
            matrices.append([[2*(i==a and j==a)-(i==j) for j in range(3)] for i in range(3)])
        else:
            matrices.append([[int((i,j) in ((a,b),(b,a))) for j in range(3)] for i in range(3)])
    from itertools import product
    return sum(matrices[0][i][j]*matrices[1][j][k]*matrices[2][k][l]*matrices[3][l][i]
               for i,j,k,l in product(range(3),repeat=4))

@cache
def moment(edges):
    # Common denominator lcm(4^4*3^3, 2^14).
    scaled=0
    if all(a==b for a,b in edges):scaled+=1728
    for ch in (0,1):
        if all(a//3==ch==b//3 for a,b in edges):
            scaled+=64*trace4_so3(tuple((a%3,b%3) for a,b in edges))
    if all(a<3<=b for a,b in edges):
        scaled+=27*trace4_pauli(*(a for a,b in edges))*trace4_pauli(*(b%3 for a,b in edges))
    return scaled

def main():
    total=0
    nnz=0
    by_pair={}
    for line in open(argv[1]):
        i,j,key,r,s=map(int,line.split())
        if (i,j) not in ((0,0),(0,4),(4,4)):continue
        assert s==0
        k=[0]*8
        for x in range(7,-1,-1):k[x],key=key%6,key//6
        edges=tuple(tuple(sorted((k[a],k[b]))) for a,b in ((4,6),(3,1),(7,5),(0,2)))
        v=moment(edges)
        if v:
            total+=r*v
            by_pair[i,j]=by_pair.get((i,j),0)+r*v
            nnz+=1
    assert moment(((0, 1),) * 4) == 128
    assert nnz == 23_616
    assert Fraction(total, 442368) == 46798847841893967231713280
    print(nnz,by_pair,total,Fraction(total,442368))
    print('both columns unnormalized except for time Haar:',Fraction(total,442368)**2)
if __name__=='__main__':main()
