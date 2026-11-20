#include <memory>
#include <stdexcept>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using Wide=__int128;
Wide add(Wide a,Wide b){Wide c;if(__builtin_add_overflow(a,b,&c))throw overflow_error("sum");return c;}
Wide mul(Wide a,Wide b){Wide c;if(__builtin_mul_overflow(a,b,&c))throw overflow_error("product");return c;}
struct G{Wide r{},i{};};
G multiply(G a,G b){return {add(mul(a.r,b.r),-mul(a.i,b.i)),add(mul(a.r,b.i),mul(a.i,b.r))};}
void accumulate(G& a,G b){a.r=add(a.r,b.r);a.i=add(a.i,b.i);}
string decimal(Wide n){
    if(!n)return "0";bool neg=n<0;if(neg)n=-n;
    string s;for(;n;n/=10)s.insert(s.begin(),char('0'+n%10));
    return neg?"-"+s:s;
}
struct Half{int bit,triple;G z;};
using Block=array<vector<Half>,65536>;
void load(Block& out,const char* path,bool reverse){
    ifstream f(path); int incoming,remote,a,b,c,d,e;long long r,i;
    while(f>>incoming>>remote>>a>>b>>c>>d>>e>>r>>i){
        int p=__builtin_ctz(incoming),q=__builtin_ctz(remote);
        int channel=reverse?8*q+p:8*p+q;
        out[a|(b<<8)].push_back({channel,36*c+6*d+e,{r,i}});
    }
    if(!f.eof())throw runtime_error("malformed half tensor");
}
int main(int argc,char**argv){
    if(argc != 4) throw runtime_error("usage: lower_join half0.rows half1.rows mixed.rows");
    auto L=make_unique<Block>(),R=make_unique<Block>();
    load(*L,argv[1],false);
    load(*R,argv[2],true);
    ifstream f(argv[3]);
    if(!f) throw runtime_error("cannot open mixed frame rows");
    string line;
    int pi=-1,pj=-1;
    unordered_map<uint64_t,G> partial;
    unordered_map<uint32_t,G> out;
    uint64_t aops=0,bops=0,nnz=0,peak1=0,peak2=0;
    auto finish=[&]{
        uint64_t n=0,pop=0;
        for(auto [key,z]:partial)if(z.r||z.i){
            pop++;
            int block=key&65535,channel=(key>>16)&63,t=(key>>22)&255,ab=key>>30;
            for(auto e:(*R)[block])if(e.bit==channel){
                uint32_t dest=((ab*36+6*(t/36)+e.triple/36)*36+t%36)*36+e.triple%36;
                accumulate(out[dest],multiply(z,e.z));
                bops++;
            }
        }
        for(auto [key,z]:out)if(z.r||z.i){
            n++;
            cout<<pi<<" "<<pj<<" "<<key<<" "<<decimal(z.r)<<" "<<decimal(z.i)<<"\n";
        }
        if(pi>=0)cerr<<"pair "<<pi<<" "<<pj<<" partial "<<pop<<" result "<<n<<"\n";
        nnz+=n;peak1=max(peak1,pop);peak2=max(peak2,n);
        partial.clear();out.clear();
    };
    while(getline(f,line)){
        istringstream row(line);uint32_t m;int i,j,a,b;long long r,s;
        if(!(row>>i>>j>>a>>b>>m>>r>>s))throw runtime_error("malformed mixed row");
        if(i!=pi||j!=pj){finish();pi=i;pj=j;}
        auto low=(m&255)|(((m>>16)&255)<<8);
        auto high=((m>>8)&255)|((m>>24)<<8);
        for(auto h:(*L)[low]){
            uint64_t key=high|(uint64_t(h.bit)<<16)|(uint64_t(h.triple)<<22)|(uint64_t(6*a+b)<<30);
            accumulate(partial[key],multiply({r,s},h.z));
            aops++;
        }
    }
    finish();
    cerr<<"first products "<<aops<<" second products "<<bops<<" rows "<<nnz
        <<" peak partial "<<peak1<<" peak final "<<peak2<<"\n";
}
