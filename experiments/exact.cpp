// Exact local synthesis by matching reachable states against suffix error sets.
#include <algorithm>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using Mask=std::bitset<2048>;
using States=std::unordered_map<Mask,uint64_t>;
struct Gate { int i,j,shift; Mask bad; };
std::vector<Gate> gates;
Mask advance(const Mask& states, int edge, bool forward) {
    if(!edge) return states;
    const auto& g=gates[edge];
    if(forward) return (states & ~g.bad) | ((states & g.bad)<<g.shift);
    return (states & ~g.bad) | ((states>>g.shift) & g.bad);
}
States expand(const States& input, int slot, bool forward) {
    States result;
    int first=slot<0?0:slot, last=slot<0?55:slot;
    for(auto& [states,path]: input) for(int e=first;e<=last;++e)
        result.try_emplace(advance(states,e,forward),slot<0?path*56+e:path);
    return result;
}
int main() {
    gates.push_back({-1,-1,0,{}});
    for(int i=0;i<11;++i) for(int j=i+1;j<11;++j) {
        Gate gate{i,j,(1<<j)-(1<<i),{}};
        for(int m=0;m<2048;++m) if ((m>>i&1) && !(m>>j&1)) gate.bad.set(m);
        gates.push_back(gate);
    }
    Mask initial,errors;
    for(int m=0;m<2048;++m) {
        int w=__builtin_popcount(m);
        if(w==5 || w==6) {
            initial.set(m);
            if((m>>5&1)!=(w==6)) errors.set(m);
        }
    }
    std::string label;
    int length;
    while(std::cin>>label>>length) {
        std::vector<int> slots(length);
        for(auto& slot:slots) std::cin>>slot;
        int free=std::count(slots.begin(),slots.end(),-1);
        if(free>10) return 2;
        int cut=0, used=0;
        while(cut<length && used<free/2) if(slots[cut++]==-1) ++used;
        States left{{initial,0}},right{{errors,0}};
        for(int k=0;k<cut;++k) left=expand(left,slots[k],true);
        for(int k=length-1;k>=cut;--k) right=expand(right,slots[k],false);
        bool found=false;
        for(auto& [outputs,lp]:left) {
            for(auto& [reject,rp]:right) if((outputs&reject).none()) {
                auto net=slots;
                uint64_t a=lp,b=rp;
                for(int k=cut-1;k>=0;--k) if(slots[k]<0) {net[k]=a%56;a/=56;}
                for(int k=cut;k<length;++k) if(slots[k]<0) {net[k]=b%56;b/=56;}
                std::cout<<label<<" SAT "<<left.size()<<" "<<right.size();
                for(int edge:net) if(edge) std::cout<<" "<<edge;
                std::cout<<std::endl;
                found=true;break;
            }
            if(found) break;
        }
        if(!found) std::cout<<label<<" UNSAT "<<left.size()<<" "<<right.size()<<std::endl;
    }
}
