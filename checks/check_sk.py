from fractions import Fraction as F
from itertools import combinations, product
from collections import defaultdict
import random, json

def state(d):
    return d if d < 4 else 4 + d % 2

def evaluate(N,A,L,colors,w,capacity=None):
    # Compare both the paper's charge capacity L and the verified larger
    # intermediate capacity 2L against the same exhaustive original graphs.
    capacity=L if capacity is None else capacity
    A=tuple(sorted(A)); distinguished=(0,)+A
    outside=tuple(v for v in range(1,N+1) if v not in A)
    colorbit={v:1 << colors[v] for v in outside}
    used=0
    for v in outside: used |= colorbit[v]
    subsets=sorted((s for s in range(used+1) if s & ~used == 0),key=lambda x: bin(x).count("1"))
    pos={a:i for i,a in enumerate(distinguished)}
    zero=(0,)*len(distinguished)
    key0=(0,0,zero)
    def mul(p,q):
        out=defaultdict(F)
        for (e,c,d),v in p.items():
            for (e2,c2,d2),v2 in q.items():
                if e+e2<=capacity and not c & c2:
                    key=(e+e2,c|c2,tuple(state(x+y) for x,y in zip(d,d2)))
                    out[key]+=v*v2
        return {k:v for k,v in out.items() if v}
    def edge(i,j): return w[tuple(sorted((i,j)))] if i!=j else F(0)
    paths={}
    for a in distinguished:
        table=defaultdict(F)
        for j in outside: table[colorbit[j],j]=edge(a,j)
        for S in subsets:
            if bin(S).count("1")<2: continue
            for j in outside:
                if S & colorbit[j]:
                    prior=S^colorbit[j]
                    table[S,j]=sum((table[prior,i]*edge(i,j) for i in outside if colorbit[i]&prior),F(0))
        paths[a]=table
    roots={}
    for r in outside:
        table=defaultdict(F)
        table[colorbit[r],r]=F(1)
        for S in subsets:
            if bin(S).count("1")<2 or not S & colorbit[r]: continue
            for j in outside:
                if S&colorbit[j] and colorbit[j]!=colorbit[r]:
                    prior=S^colorbit[j]
                    table[S,j]=sum((table[prior,i]*edge(i,j) for i in outside if colorbit[i]&prior),F(0))
        roots[r]=table
    psi=defaultdict(F)
    def add(e,S,degrees,value):
        if e>capacity or not value:return
        d=list(zero)
        for a,degree in degrees.items():d[pos[a]]=degree
        psi[e,S,tuple(d)]+=value
    for S in subsets:
        n=bin(S).count("1")
        if n>=3:
            z=sum((roots[r][S,j]*edge(j,r) for r in outside if S&colorbit[r] for j in outside),F(0))/(2*n)
            add(n,S,{},z)
        if n>=1:
            for a,b in combinations(distinguished,2):
                p=sum((paths[a][S,j]*edge(j,b) for j in outside),F(0))
                add(n+(a!=0),S,{a:1,b:1},p)
        if n>=2:
            for a in distinguished:
                q=sum((paths[a][S,j]*edge(j,a) for j in outside),F(0))/2
                add(n-1 if a==0 else n+1,S,{a:2},q)
    E={key0:F(1)};Y=dict(E)
    for j in range(1,capacity+1):
        Y={k:v/j for k,v in mul(Y,psi).items()}
        for k,v in Y.items():E[k]=E.get(k,F(0))+v
    for a,b in combinations(distinguished,2):
        d=list(zero);d[pos[a]]=1;d[pos[b]]=1
        E=mul(E,{key0:F(1),(int(a!=0),0,tuple(d)):edge(a,b)})
    return {(e,S):v for (e,S,d),v in E.items() if e<=L and d[0] in (0,2,4) and all(x==4 for x in d[1:]) and v}

def enumeration(N,A,L,colors,w):
    edges=list(combinations(range(1,N+1),2));out=defaultdict(F)
    for bits in range(1<<len(edges)):
        if bin(bits).count("1")>L:continue
        d=[0]*(N+1);v=F(1)
        for i,(a,b) in enumerate(edges):
            if bits>>i&1:d[a]+=1;d[b]+=1;v*=w[a,b]
        if {a for a in range(1,N+1) if d[a]>=3}!=set(A):continue
        outside=[a for a in range(1,N+1) if d[a] and a not in A]
        if len({colors[a] for a in outside})!=len(outside):continue
        for a in range(1,N+1):
            if d[a]%2:v*=w[0,a]
        S=sum(1<<colors[a] for a in outside)
        out[bin(bits).count("1"),S]+=v
    return {k:v for k,v in out.items() if v}

def main():
    rng=random.Random(281454)
    count=0
    for N in range(2,6):
        vertices=range(1,N+1)
        for A_mask in range(1<<N):
            A={a for a in vertices if A_mask>>(a-1)&1}
            outside=[a for a in vertices if a not in A]
            for L in sorted(set((1,2,min(4,N*(N-1)//2),N*(N-1)//2))):
                # Injective, all-colliding, random coloring; signed or zero weights.
                for scheme in range(3):
                    colors={a:(i%(2*L) if scheme==0 else 0 if scheme==1 else rng.randrange(2*L)) for i,a in enumerate(outside)}
                    h=F(rng.choice((-3,-2,0,1,2)),3)
                    w={(a,b):(h if a==0 else F(rng.choice((-3,-2,-1,0,1,2,3)),5)) for a,b in combinations(range(N+1),2)}
                    expected=enumeration(N,A,L,colors,w)
                    actual=evaluate(N,A,L,colors,w)
                    assert actual==expected,(N,A,L,colors,w,actual,expected)
                    larger=evaluate(N,A,L,colors,w,capacity=2*L)
                    assert larger==expected,(N,A,L,colors,w,larger,expected)
                    count+=1
    print(json.dumps({'scenarios':count,'capacity_variants_per_scenario':2,'coefficient_comparisons':2*count,'N_min':2,'N_max':5,'result':'all exact rational coefficient comparisons passed'}))

if __name__=='__main__':main()
