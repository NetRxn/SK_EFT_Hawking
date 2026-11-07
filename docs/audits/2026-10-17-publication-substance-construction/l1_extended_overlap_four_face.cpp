// Exact tree-fixed projection of U(2,0) through four closed plaquettes.
// Faces in order (0,0,1),(2,0,1),(2,0,2),(6,0,2).
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <unordered_map>
#include <vector>
using namespace std;

// Signed quaternion units: +1, +i, +j, +k stored as 1..4.
int dagger(int q){return abs(q)==1?q:-q;}
int product(int x,int y){
    const int table[4][4]={{1,2,3,4},{2,-1,4,-3},{3,-4,-1,2},{4,3,-2,-1}};
    return (x<0?-1:1)*(y<0?-1:1)*table[abs(x)-1][abs(y)-1];
}
int haar48(array<int,4> i){
    array<int,8> n{};
    for(int x:i)n[x]++;
    if(any_of(n.begin(),n.end(),[](int x){return x%2;}))return 0;
    int left=n[0]+n[1]+n[2]+n[3];
    if(left==2)return 3;
    int v=2;
    for(int x:n)if(x==4)v*=3;
    return v;
}
using Key=uint32_t;
struct Moment{array<int,4> q; int w;};
struct Term{Key b,c;int w;};
int main(int argc,char**argv){
    bool dump=argc>1;
    map<Key,unordered_map<Key,int>> rows;
    array<int,16> nonzero_blocks{};
    size_t raw_terms=0;
    for(int ch=0;ch<16;ch++){
        array<int,4> c{};
        for(int j=0;j<4;j++)c[j]=(ch>>j)&1;
        vector<Moment> moments;
        for(int a=0;a<4;a++)for(int b=0;b<4;b++)for(int d=0;d<4;d++)for(int e=0;e<4;e++){
            int w=haar48({4*c[0]+a,4*c[1]+b,4*c[2]+d,4*c[3]+e});
            if(w)moments.push_back({{a+1,b+1,d+1,e+1},w});
        }
        if(moments.empty())continue;
        for(int r=1;r<=4;r++)for(int s=1;s<=4;s++)for(int v=1;v<=4;v++)
        for(int w=1;w<=4;w++)for(int x=1;x<=4;x++)for(int y=1;y<=4;y++){
            // Four linear port coordinates and one symmetrized quadratic port.
            int vl=4*c[2]+v-1,vr=4*c[3]+y-1;
            if(vl>vr)swap(vl,vr);
            Key boundary=0;
            for(int z:{4*c[1]+r-1,4*c[1]+s-1,4*c[3]+w-1,4*c[3]+x-1,vl,vr})
                boundary=8*boundary+z;
            for(auto m:moments){
                auto [a,b,d,e]=m.q;
                array<int,4> f={dagger(a),product(product(dagger(r),s),b),
                    product(dagger(v),d),product(product(dagger(w),dagger(e)),product(x,y))};
                if(any_of(f.begin(),f.end(),[](int z){return abs(z)==1;}))continue;
                Key curv=0;
                int weight=m.w;
                for(int j=0;j<4;j++){
                    curv=6*curv+3*c[j]+abs(f[j])-2;
                    if(f[j]<0)weight=-weight;
                }
                rows[boundary][curv]+=weight;
                raw_terms++;
            }
        }
    }
    size_t boundaries=0, entries=0,maxrow=0;
    map<int,size_t> histogram,slice;
    for(auto& [boundary,row]:rows){
        int k=boundary;
        array<int,6> b{};
        for(int j=5;j>=0;j--){b[j]=k&7;k>>=3;}
        const bool physical_slice=b[0]%4==0&&b[1]%4==0&&b[2]%4==0
                                  &&b[3]%4==0&&b[4]%4==b[5]%4;
        size_t live=0;
        for(auto [c,v]:row)if(v){
            live++;histogram[v]++;
            if(physical_slice)slice[v]++;
            if(dump)cout<<boundary<<" "<<c<<" "<<v<<"\n";
        }
        boundaries+=bool(live);entries+=live;maxrow=max(maxrow,live);
    }
    cerr<<"raw nonzero terms "<<raw_terms<<"; live boundaries "<<boundaries
        <<"; entries "<<entries<<"; peak row "<<maxrow<<"\n";
    cerr<<"coefficients";for(auto [v,n]:histogram)cerr<<" "<<v<<":"<<n;
    cerr<<"\nprior physical slice";for(auto [v,n]:slice)cerr<<" "<<v<<":"<<n;
    cerr<<"\n";
    if(slice!=map<int,size_t>{{-3,24},{-2,24},{2,78},{3,132},{6,18}})return 2;
}
