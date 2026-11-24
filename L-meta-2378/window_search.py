"""Exact local rewrites for circuits computing the 21-by-21 Singer incidence edge function."""
import argparse
import json
import random
from pathlib import Path

N = 21
SHIFTS = (20, 0, 5, 7, 17)
EDGES = [(i, N+(i+k)%N) for i in range(N) for k in SHIFTS]


def exact_rows():
    columns = [sum(1 << i for i,j in EDGES if j == N+b) for b in range(N)]
    unions = {0}
    for column in columns:
        unions |= {u | column for u in unions}
    positives = [(1 << i) | (1 << j) for i,j in EDGES]
    negatives = [((1 << N)-1) ^ u | sum(1 << (N+j) for j,col in enumerate(columns)
                                        if (col & u) == col) for u in sorted(unions)]
    assert len(negatives) == 25237
    return positives, negatives


def transpose(rows):
    buffers = [bytearray((len(rows)+7)//8) for _ in range(2*N)]
    for i,mask in enumerate(rows):
        while mask:
            bit = mask & -mask
            buffers[bit.bit_length()-1][i//8] |= 1 << (i%8)
            mask ^= bit
    return [int.from_bytes(bits,'little') for bits in buffers]


def formula(seed, mode):
    rng = random.Random(seed)
    gates = []
    def gate(op,a,b):
        gates.append((op,a,b))
        return 2*N+len(gates)-1
    def disjoin(xs):
        xs = list(xs)
        if seed:
            rng.shuffle(xs)
        while len(xs)>1:
            xs = [gate('or',xs[k],xs[k+1]) if k+1 < len(xs) else xs[k]
                  for k in range(0,len(xs),2)]
        return xs[0]
    if mode=='edges':
        terms = [gate('and',i,j) for i,j in EDGES]
    else:
        stars = {}
        for i,j in EDGES:
            left = mode=='points' or (mode=='mixed' and rng.randrange(2)==0)
            center,leaf = (i,j) if left else (j,i)
            stars.setdefault(center,[]).append(leaf)
        terms = [gate('and',center,disjoin(leaves)) for center,leaves in stars.items()]
    output = disjoin(terms)
    assert output == len(gates)+2*N-1 and sum(op=='or' for op,_,_ in gates)==104
    return gates


def values(inputs,gates):
    vals=list(inputs)
    for op,a,b in gates:
        vals.append(vals[a] & vals[b] if op=='and' else vals[a] | vals[b])
    return vals


def rebuild(gates,root,factors):
    """Emit a legal topological circuit even when a replacement reuses a later independent wire."""
    fresh=[]
    translated={}
    def add(op,args):
        fresh.append({'op':op,'inputs':args})
        return 2*N+len(fresh)-1
    def reduce(op,items):
        if not items: return add(op,[])
        wire=items[0]
        for other in items[1:]:
            wire = add(op,[wire,other])
        return wire
    def visit(i):
        if i<2*N: return i
        if i not in translated:
            if i==root:
                factors_wires = []
                for arms in factors:
                    arm_wires = [reduce('and',[visit(j) for j in arm]) for arm in arms]
                    factors_wires.append(reduce('or',arm_wires))
                translated[i] = reduce('and',factors_wires)
            else:
                op,a,b=gates[i-2*N]
                translated[i]=add(op,[visit(a),visit(b)])
        return translated[i]
    out=visit(2*N+len(gates)-1)
    return {'gates':fresh,'output':out}


def search(gates,pin,nin,pm,nm):
    pv,nv=values(pin,gates),values(nin,gates)
    assert pv[-1]==pm and nv[-1]==0
    upper=len(pv)
    parent={}
    pd=[0]*upper
    nd=[0]*upper
    pd[-1],nd[-1]=pm,nm
    for i in reversed(range(2*N,upper)):
        op,a,b=gates[i-2*N]
        for v,w in [(a,b),(b,a)]:
            if v>=2*N:
                assert v not in parent
                parent[v]=i
                pd[v]=pd[i] & (pv[w] if op=='and' else ~pv[w])
                nd[v]=nd[i] & (nv[w] if op=='and' else ~nv[w])
    # Every positive footprint of a conjunction is an intersection of wire footprints.
    # Removing wires can only shrink the family. Intersecting with a local care set is exact.
    allsets={pm}
    for w in set(pv):
        allsets |= {u&w for u in allsets}
    def outward(i):
        while True:
            yield i
            if i not in parent: return
            i=parent[i]
    or_wires = [i for i in range(2*N,upper) if gates[i-2*N][0]=='or']
    children = {i:[] for i in or_wires}
    for i in or_wires:
        path = iter(outward(i))
        next(path)
        next_or = next((j for j in path if gates[j-2*N][0]=='or'),None)
        if next_or is not None:
            children[next_or].append(i)
    from itertools import combinations
    counts=[0,0,0]
    for root in or_wires:
        P,Q=pd[root],nd[root]
        windows=[(root,)]
        for child in children[root]:
            windows.append((root,child))
            windows.extend((root,child,grandchild) for grandchild in children[child])
        windows.extend((root,a,b) for a,b in combinations(children[root],2))
        for window in windows:
            k=len(window)
            counts[k-1]+=1
            removed={j for i in window for j in outward(i)}
            available=[w for w in range(upper) if w not in removed]
            by_foot={}
            for w in available:
                by_foot[pv[w]]=by_foot.get(pv[w],nm) & nv[w]
            groups=sorted(by_foot.items(),key=lambda pair:pair[1].bit_count())
            cache={}
            def bad(s):
                # Strongest conjunction containing s. Its remaining negative rows
                # are accepted by every conjunction that covers all positives in s.
                if s not in cache:
                    surviving=Q
                    for pos,neg in groups:
                        if s & ~pos == 0:
                            surviving &= neg
                            if surviving==0: break
                    cache[s]=surviving
                return cache[s]
            chosen=None
            if bad(P)==0:
                chosen=[[P]]
            elif k>=2:
                parts=sorted({v&P for v in allsets if v&P},key=lambda v:-v.bit_count())
                feasible=[]
                for a in parts:
                    if a==P or bad(a): continue
                    if not bad(P^a):
                        chosen=[[a,P^a]]
                        break
                    if all(a & ~b for b in feasible):
                        feasible.append(a)
                if chosen is None and k==3:
                    for a,b in combinations(feasible,2):
                        missing=P & ~(a|b)
                        if not bad(missing):
                            chosen=[[a,b,missing]]
                            break
                if chosen is None and k==3:
                    # A circuit with two ORs and free conjunctions is either a
                    # three-term DNF, or an AND of two two-term DNFs. After the
                    # second OR distributes, these are all possible uses of the first.
                    masks={}
                    for a in parts:
                        b=P^a
                        leak=bad(a)|bad(b)
                        if leak not in masks:
                            for other,split in masks.items():
                                if not (leak & other):
                                    chosen=[list(split),[a,b]]
                                    break
                            if chosen is not None: break
                            masks[leak]=(a,b)
            if chosen is not None:
                factors=[[[w for w in available if s & ~pv[w]==0] for s in arm] for arm in chosen]
                return counts,rebuild(gates,root,factors)
    return counts,None



def check_solution(c,pin,nin,pm,nm):
    def evaluate(inputs,mask):
        w=list(inputs)
        for g in c['gates']:
            v=mask if g['op']=='and' else 0
            for i in g['inputs']: v=v&w[i] if g['op']=='and' else v|w[i]
            w.append(v)
        return w[c['output']]
    return (evaluate(pin,pm)==pm and evaluate(nin,nm)==0 and
            sum(g['op']=='or' for g in c['gates'])<=103)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seeds',type=int,default=4)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    positives,negatives=exact_rows()
    pin,nin=transpose(positives),transpose(negatives)
    pm,nm=(1<<len(positives))-1,(1<<len(negatives))-1
    total=[0,0,0]
    for seed in range(args.seeds):
        for mode in ('points','lines','mixed','edges'):
            counts,solution=search(formula(seed,mode),pin,nin,pm,nm)
            total=[a+b for a,b in zip(total,counts)]
            if solution is not None:
                assert check_solution(solution,pin,nin,pm,nm)
                if args.output: args.output.write_text(json.dumps(solution,indent=2)+'\n')
                print('FOUND a correct circuit with at most 103 ORs',flush=True)
                raise SystemExit
        print('seeds completed',seed+1,'one-OR windows',total[0],'two-OR windows',total[1],'three-OR windows',total[2],flush=True)
    print('No one-OR saving in these windows.',flush=True)
