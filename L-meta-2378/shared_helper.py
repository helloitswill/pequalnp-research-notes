"""Test whether one new mixed OR wire can remove two ORs from a 104-OR formula."""
from itertools import combinations
import argparse
import json
from pathlib import Path

from window_search import N, EDGES, exact_rows, transpose, formula, values, check_solution


def helper_bank(pin, nin, pm, nm):
    terms = [(i,) for i in range(2*N)] + list(EDGES)
    def evaluate_term(term, signals, mask):
        for i in term:
            mask &= signals[i]
        return mask
    tpos = [evaluate_term(t,pin,pm) for t in terms]
    tneg = [evaluate_term(t,nin,nm) for t in terms]
    bank = []
    for i,j in combinations(range(len(terms)),2):
        p = tpos[i]|tpos[j]
        if p==tpos[i] or p==tpos[j]:
            continue
        bank.append((terms[i],terms[j],p,tneg[i]|tneg[j]))
    by_edge = []
    for p in range(len(EDGES)):
        by_edge.append(sum((1 << i) for i,h in enumerate(bank) if h[2]>>p&1))
    return bank,by_edge


def matches(gates, pin, nin, pm, nm, bank, by_edge):
    pv,nv=values(pin,gates),values(nin,gates)
    assert pv[-1]==pm and nv[-1]==0
    n=len(pv)
    parent={}
    pd=[0]*n
    nd=[0]*n
    pd[-1],nd[-1]=pm,nm
    for wire in range(n-1,2*N-1,-1):
        op,a,b=gates[wire-2*N]
        for v,w in ((a,b),(b,a)):
            if v>=2*N:
                assert v not in parent
                parent[v]=wire
                pd[v]=pd[wire] & (pv[w] if op=='and' else ~pv[w])
                nd[v]=nd[wire] & (nv[w] if op=='and' else ~nv[w])
    opportunities={}
    for wire,(op,_,_) in enumerate(gates,2*N):
        if op!='or':
            continue
        k=wire
        banned={k}
        while k in parent:
            k=parent[k]
            banned.add(k)
        needed=pd[wire]
        available=tuple(w for w in range(n) if w not in banned and not (needed & ~pv[w]))
        leak=nd[wire]
        for w in available:
            leak &= nv[w]
        assert leak!=0, 'A one-gate saving without a helper was found'
        helpers=(1<<len(bank))-1
        while needed and helpers:
            bit=needed & -needed
            helpers &= by_edge[bit.bit_length()-1]
            needed ^= bit
        while helpers:
            bit=helpers & -helpers
            i=bit.bit_length()-1
            helpers ^= bit
            if not (bank[i][3] & leak):
                opportunities.setdefault(i,[]).append((wire,banned,available))
    return opportunities


def candidate(gates, h, first, second):
    a,b,_,_=h
    new=[]
    memo={}
    def add(op,args):
        new.append({'op':op,'inputs':list(args)})
        return 2*N+len(new)-1
    def meet(wires):
        if not wires: return add('and',[])
        x=wires[0]
        for y in wires[1:]: x=add('and',(x,y))
        return x
    shared=add('or',(meet(a),meet(b)))
    banned=first[1]|second[1]
    replace={info[0]:[w for w in info[2] if w not in banned] for info in (first,second)}
    def visit(w):
        if w<2*N: return w
        if w not in memo:
            if w in replace:
                memo[w]=meet([shared]+[visit(i) for i in replace[w]])
            else:
                op,x,y=gates[w-2*N]
                memo[w]=add(op,(visit(x),visit(y)))
        return memo[w]
    out=visit(2*N+len(gates)-1)
    return {'gates':new,'output':out}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seeds',type=int,default=16)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    positives,negatives=exact_rows()
    pin,nin=transpose(positives),transpose(negatives)
    pm,nm=(1<<len(positives))-1,(1<<len(negatives))-1
    bank,by_edge=helper_bank(pin,nin,pm,nm)
    one=pair=0
    print('distinct candidate arm pairs',len(bank),flush=True)
    for seed in range(args.seeds):
        for mode in ('points','lines','mixed','edges'):
            base=formula(seed,mode)
            hits=matches(base,pin,nin,pm,nm,bank,by_edge)
            one+=sum(len(v) for v in hits.values())
            for h,options in hits.items():
                for first,second in combinations(options,2):
                    pair+=1
                    result=candidate(base,bank[h],first,second)
                    if check_solution(result,pin,nin,pm,nm):
                        if args.output: args.output.write_text(json.dumps(result,indent=2)+'\n')
                        print('FOUND a full solution',flush=True)
                        raise SystemExit
    print('formulas',4*args.seeds,'individual substitutions',one,'same-helper pairs',pair)
