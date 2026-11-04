#define main power_replay
#include "l1_wick_haar_cut.cpp"
#undef main
using Count=uint64_t;
using Local=array<array<Ext,3>,5>;
struct Paired {
    int x;
    array<unordered_map<Count,Poly>,3> cache;
    uint64_t examined=0;
    int fact[9]={1,1,2,6,24,120,720,5040,40320};
    Local out;
    Paired(int site):x(site){}
    const Poly& moment(Count word,int h){
        if(auto it=cache[h].find(word);it!=cache[h].end())return it->second;
        Poly result;
        if(!word){
            if(h==0)result[0]=1;
        }else{
            int i=countr_zero(word)/4;
            Count rem=word-(1ULL<<(4*i));
            for(int j=i;j<16;++j){
                int mult=(rem>>(4*j))&15;
                if(!mult)continue;
                auto rest=rem-(1ULL<<(4*j));
                if(!covariance[x][i][j].empty())
                    addprod(result,covariance[x][i][j],moment(rest,h),mult);
                if(h&&i==j&&i>=8)add(result,moment(rest,h-1),(i<12?2:-2)*mult);
            }
        }
        return cache[h].emplace(word,std::move(result)).first->second;
    }
    void enumerate(int start,int n,Count word,const Ext& E){
        ++examined;
        if(!(n%2)){
            int denom=1;
            for(int i=0;i<16;++i)denom=mod(1LL*denom*fact[(word>>(4*i))&15]);
            int inv=powm(denom,P-2);
            for(int h=0;h<=2&&2*h<=n;++h){
                const auto& m=moment(word,h);
                if(!m.empty())for(const auto& [k,p]:E)addprod(out[n/2-h][h][k],p,m,inv);
            }
        }
        if(n==8)return;
        for(int i=start;i<16;++i){
            auto next=wedge(E,coframe[x][i]);
            if(!next.empty())enumerate(i,n+1,word+(1ULL<<(4*i)),next);
        }
    }
    void run(){
        Ext one;one[0][0]=1;enumerate(0,0,0,one);
        for(auto& row:out)for(auto& e:row)
            for(auto i=e.begin();i!=e.end();)if(i->second.empty())i=e.erase(i);else++i;
    }
};
int main(int argc,char**argv){
    int active=argc>1?stoi(argv[1]):2,seed=argc>2?stoi(argv[2]):1;
    bool dense=argc>3?stoi(argv[3]):false;
    if(argc>4)P=stoi(argv[4]);
    if(argc>5)I=stoi(argv[5]);
    setup(argc>6 && stoi(argv[6]) ? -1 : 0,active,seed,dense);
    Paired left(0),right(1);
    array<Paired*,2> side{&left,&right};
    int fact[5]={1,1,2,6,24};
    for(int x=0;x<2;++x){
        auto [s,d]=center(x);
        auto& p=*side[x];
        p.run();
        cout<<"side "<<x<<" nonzero exterior prefixes "<<p.examined<<" Wick memo states ";
        for(auto& c:p.cache)cout<<c.size()<<' ';
        cout<<endl;
        Ext first;first[0][0]=1;
        for(int n=0;n<=4;++n){
            Ext power=first;
            for(int h=0;h<=2&&n+h<=4;++h){
                if(h)power=wedge(power,d);
                Ext scaled;
                add(scaled,p.out[n][h],fact[n]*fact[h]);
                for(auto i=power.begin();i!=power.end();)if(i->second.empty())i=power.erase(i);else++i;
                if(scaled!=power)throw runtime_error("local Wick versus power mismatch");
                cout<<"local "<<x<<' '<<n<<' '<<h<<" terms "<<count(scaled)<<endl;
            }
            first=wedge(first,s);
        }
    }
    for(int h=0;h<=2;++h){
        int val=0;uint64_t products=0;
        for(int i=0;i<=4-h;++i)for(int j=0;j<=h;++j)
            val=mod(val+haar_join(left.out[i][j],right.out[4-h-i][h-j],products));
        cout<<"coefficient "<<h<<' '<<val<<" products "<<products<<" moments "<<moment_cache.size()<<endl;
    }
}
