"""OPTIONAL floating-point candidate finder; NOT an existence/nonexistence proof.
Usage: python experiments/scan_small.py --max-n 6 --starts 4
Requires networkx, numpy, scipy. The exact code and prose theorem are separate.
"""
import argparse
from functools import lru_cache

def main():
    import networkx as nx
    import numpy as np
    from scipy.optimize import least_squares
    from exact import graph, maximal_independent_sets
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n",type=int,default=6)
    parser.add_argument("--starts",type=int,default=4)
    args=parser.parse_args()
    if not 1<=args.max_n<=7 or not 1<=args.starts<=100: parser.error("invalid bounds")
    def probs(adj,rates):
        n=len(adj)
        @lru_cache(None)
        def f(mask):
            if not mask: return {0:1.0}
            s=sum(rates[i] for i in range(n) if mask>>i&1)
            ans={}
            for v in range(n):
                if mask>>v&1:
                    for sub,p in f(mask & ~adj[v]).items():
                        key=sub|(1<<v)
                        ans[key]=ans.get(key,0.0)+p*rates[v]/s
            return ans
        return f((1<<n)-1)
    for n in range(1,args.max_n+1):
        graphs=[g for g in nx.graph_atlas_g() if len(g)==n and nx.is_connected(g)]
        unresolved=[]
        for ix,g in enumerate(graphs):
            adj=graph(n,g.edges())
            outcomes=maximal_independent_sets(adj)
            if len(outcomes)==1: continue
            def residual(logr):
                law=probs(adj,np.exp(np.r_[logr,0.0]))
                return np.array([law[m]-law[outcomes[-1]] for m in outcomes[:-1]])
            best=1.0
            for k in range(args.starts):
                rng=np.random.default_rng(n*100000+ix*100+k)
                x=np.zeros(n-1) if k==0 else rng.normal(0,1,n-1)
                fit=least_squares(residual,x,bounds=(-20,20),max_nfev=200)
                best=min(best,max(abs(residual(fit.x))))
                if best<1e-8: break
            if best>=1e-8: unresolved.append((ix,round(best,7),list(g.edges())))
        print(n,"connected",len(graphs),"numerically unresolved",len(unresolved),unresolved)
    print("HEURISTIC ONLY: no exact feasibility certificate generated.")

if __name__=="__main__": main()
