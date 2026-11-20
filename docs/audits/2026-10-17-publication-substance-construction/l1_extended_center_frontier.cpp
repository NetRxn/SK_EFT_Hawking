#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>
using U=uint64_t;
using namespace std;
struct State {
    U deg=0,curv=0;
    uint32_t live=0,fp=0;
    bool operator==(const State& a) const {
        return deg==a.deg && curv==a.curv && live==a.live && fp==a.fp;
    }
};
U mix(U a) {
    a=(a^(a>>30))*0xbf58476d1ce4e5b9ULL;
    a=(a^(a>>27))*0x94d049bb133111ebULL;
    return a^(a>>31);
}
struct Hash {
    size_t operator()(const State& s) const {
        return mix(s.deg)^mix(s.curv+41)^mix((U(s.live)<<32|s.fp)+112);
    }
};
array<pair<int,int>,32> edges;
int eid[16][4];
array<vector<State>,16> options;
void local(int x,int k,int n,State s,const vector<State>& terms){
    options[x].push_back(s);
    if(n==4)return;
    for(int i=k;i<6;++i){
        const auto& t=terms[i];
        local(x,i,n+1,{s.deg+t.deg,s.curv^t.curv,s.live|t.live,s.fp^t.fp},terms);
    }
}
int main(int argc,char** argv){
    int ne=0;
    for(int x=0;x<16;++x)for(int a=0;a<4;++a){
        int y=x^(1<<a);
        if(x<y){eid[x][a]=eid[y][a]=ne;edges[ne++]={4*x+a,4*y+a};}
    }
    array<unsigned,16> dv{};
    array<unsigned,32> ev{};
    for(int x=0;x<16;++x){
        vector<State> terms;
        for(int a=0;a<4;++a)for(int b=a+1;b<4;++b){
            auto q=[](int x,int a){return U(1)<<(4*x+a);};
            State t;
            t.deg=U(2)<<(4*x);
            t.curv=q(x,a)^q(x^(1<<a),b)^q(x^(1<<b),a)^q(x,b);
            for(int i=0;i<4;++i)if(i!=a&&i!=b){
                t.deg+=U(1)<<(4*(x^(1<<i)));
                t.live|=uint32_t(1)<<eid[x][i];
            }
            t.fp=t.live;
            terms.push_back(t);
            for(int z=0;z<16;++z)if((t.deg>>(4*z))&15)dv[z]|=1u<<x;
            for(int e=0;e<32;++e){
                auto [j,k]=edges[e];
                if((t.live>>e&1)||(t.curv>>j&1)||(t.curv>>k&1))ev[e]|=1u<<x;
            }
        }
        local(x,0,0,{},terms);
    }
    unsigned chosen=0;
    unordered_set<State,Hash> pop{{}};
    size_t limit=argc>1?stoull(argv[1]):1000000;
    for(int step=0;step<16;++step){
        int winner=-1,best=999;
        for(int x=0;x<16;++x)if(!(chosen>>x&1)){
            unsigned cur=chosen|(1u<<x);int score=0;
            for(auto v:dv)if((cur&v)&&((~cur)&v))score+=3;
            for(auto v:ev)if((cur&v)&&((~cur)&v))score+=4;
            if(score<best){winner=x;best=score;}
        }
        int x=winner;
        unsigned after=chosen|(1u<<x);
        vector<int> closeD,closeE;
        for(int y=0;y<16;++y)if(!(dv[y]&~after)&&(dv[y]&~chosen))closeD.push_back(y);
        for(int e=0;e<32;++e)if(!(ev[e]&~after)&&(ev[e]&~chosen))closeE.push_back(e);
        unordered_set<State,Hash> next;
        size_t attempts=0;
        for(const auto& p:pop){
            for(const auto& q:options[x]){
                ++attempts;
                State s{p.deg+q.deg,p.curv^q.curv,p.live|q.live,p.fp^q.fp};
                // Pairwise addition may carry if any true nibble sum >=16.
                // The local maximum at each center is <=8, and existing <=8,
                // so detect 8+8 separately before using packed sum.
                if((p.deg&q.deg&0x8888888888888888ULL) ||
                   (s.deg&0x8888888888888888ULL)&&
                   ((s.deg&0x8888888888888888ULL)>>3 & (s.deg|s.deg>>1|s.deg>>2)))
                    continue;
                bool ok=true;
                for(int y:closeD){
                    if((s.deg>>(4*y)&15)!=8){ok=false;break;}
                    s.deg&=~(U(15)<<(4*y));
                }
                if(!ok)continue;
                for(int e:closeE){
                    auto [a,b]=edges[e];
                    int p0=s.curv>>a&1,p1=s.curv>>b&1;
                    if((p0^p1)!=(s.fp>>e&1)||(!(s.live>>e&1)&&p0)){
                        ok=false;break;
                    }
                    s.live&=~(uint32_t(1)<<e);s.fp&=~(uint32_t(1)<<e);
                    s.curv&=~((U(1)<<a)|(U(1)<<b));
                }
                if(!ok)continue;
                next.insert(s);
                if(next.size()>=limit){
                    cout<<"cutoff "<<step+1<<" center "<<x<<" attempts "<<attempts<<" states >= "<<next.size()<<" frontier score "<<best<<endl;
                    return 0;
                }
            }
        }
        cout<<"step "<<step+1<<" center "<<x<<" attempts "<<attempts<<" states "<<next.size()<<" closed "<<closeD.size()<<" sites "<<closeE.size()<<" edges frontier score "<<best<<endl;
        chosen=after;
        pop.swap(next);
    }
}
