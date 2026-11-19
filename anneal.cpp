// g++ -std=c++17 -O3 -march=native anneal.cpp -o anneal
// Read a flattened seed (one pair per line) on stdin.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>
using Edge = std::array<int,2>;
using Net = std::vector<Edge>;
using Bits = std::array<uint64_t,15>;
static std::array<Bits,11> inputs{};
static Bits target{};
int errors(const Net& net) {
    auto wires = inputs;
    for (auto [i,j] : net) {
        for (int k=0;k<15;++k) {
            auto a=wires[i][k], b=wires[j][k];
            wires[i][k]=a&b;
            wires[j][k]=a|b;
        }
    }
    int count=0;
    for (int k=0;k<15;++k) count+=__builtin_popcountll(wires[5][k]^target[k]);
    return count;
}
int main(int argc,char** argv) {
    if (argc!=3) return 2;
    std::mt19937 rng(std::stoul(argv[1]));
    const int restarts=std::stoi(argv[2]);
    int sample=0;
    for (int mask=0;mask<2048;++mask) {
        int weight=__builtin_popcount(mask);
        if (weight!=5 && weight!=6) continue;
        uint64_t bit=uint64_t{1}<<(sample%64);
        for(int i=0;i<11;++i) if(mask&(1<<i)) inputs[i][sample/64]|=bit;
        if(weight==6) target[sample/64]|=bit;
        ++sample;
    }
    Net seed;
    for (int i,j;std::cin>>i>>j;) seed.push_back({i,j});
    if(seed.size()<24 || errors(seed)!=0) return 3;
    std::vector<Edge> edges;
    for(int i=0;i<11;++i) for(int j=i+1;j<11;++j) edges.push_back({i,j});
    Net best=seed;
    int bestScore=925;
    for(int restart=0;restart<restarts;++restart) {
        Net net=(restart%3==0 || bestScore==925)?seed:best;
        while(net.size()>24) net.erase(net.begin()+rng()%net.size());
        int score=errors(net);
        for(int step=0;step<24000;++step) {
            Net next=net;
            int a=rng()%24,b=rng()%24;
            switch(rng()%5) {
            case 0: std::swap(next[a],next[b]); break;
            case 1: {
                Edge e=next[a]; next.erase(next.begin()+a); next.insert(next.begin()+b,e); break;
            }
            default: next[a]=edges[rng()%55];
            }
            int candidate=errors(next);
            double temperature=0.18+2.4*(1.0-step/24000.);
            if(candidate<=score || std::generate_canonical<double,32>(rng)<std::exp((score-candidate)/temperature)) {
                score=candidate; net=next;
            }
            if(score<bestScore) {
                best=net; bestScore=score;
                std::cout<<restart<<' '<<step<<' '<<score<<" [";
                for(size_t i=0;i<net.size();++i) std::cout<<(i?",":"")<<"["<<net[i][0]<<","<<net[i][1]<<"]";
                std::cout<<"]"<<std::endl;
                if(!score) return 0;
            }
        }
    }
}
