#!/usr/bin/env python3
"""Finite regression for EPPA-III Section 8: E6 and binary orthogonal repair.
These checks do not replace the general English proofs or formalize geometry in Lean.
"""
from itertools import product

def cover(s,t,x,y):
    n=2*s*t
    def edge(a,b):
        if a==b:return False
        sa,ia,pa=a//(s*t),(a%(s*t))//t,a%t
        sb,ib,pb=b//(s*t),(b%(s*t))//t,b%t
        if sa==sb:return ia==ib
        if ia!=ib:return y==1
        return x=="1" or (x=="M" and pa==pb) or (x=="m" and pa!=pb)
    return tuple(frozenset(b for b in range(n) if edge(a,b)) for a in range(n))

def comp(A):
    n=len(A)
    return tuple(frozenset(range(n))-A[i]-{i} for i in range(n))

def is_connected(A):
    seen={0};todo=[0]
    while todo:
        for b in A[todo.pop()]:
            if b not in seen:seen.add(b);todo.append(b)
    return len(seen)==len(A)

def find_c5(A):
    for a in range(len(A)):
        for b in A[a]:
            for c in A[b]-A[a]-{a,b}:
                for d in A[c]-A[a]-A[b]-{a,b,c}:
                    for e in A[d]&A[a]:
                        if e in (a,b,c,d) or e in A[b] or e in A[c]:continue
                        v=[a,b,c,d,e]
                        if all((v[j] in A[v[i]])==((j-i) in (1,4))
                               for i in range(5) for j in range(i+1,5)):
                            return v
    return None

def q6(x,sign):
    if sign=="+":
        return (((x&7)&((x>>3)&7)).bit_count())%2
    a=x&3;b=(x>>2)&3;u=(x>>4)&1;v=(x>>5)&1
    return ((a&b).bit_count()+u+v+u*v)%2

def sp4(x,y):
    return (((x&3)&((y>>2)&3)).bit_count()
          +(((x>>2)&3)&(y&3)).bit_count())%2

def graph(name):
    if name=="Sp4":
        V=list(range(1,16))
        E=lambda a,b:sp4(a,b)==0
    else:
        sign=name[-1]
        Q=lambda z:q6(z,sign)
        V=([i for i in range(1,64) if Q(i)==0] if name.startswith("O6")
           else [i for i in range(1,64) if Q(i)==1] if name.startswith("NO")
           else list(range(64)))
        E=(lambda a,b:Q(a^b)==0) if name.startswith("VO") else (
            lambda a,b:(Q(a^b)^Q(a)^Q(b))==0)
    return V,lambda a,b:a!=b and E(a,b)

CERT={
 "Sp4":([1,2,4,12,11],(15,6,1,3)),
 "O6+":([1,2,8,24,55],(35,18,9,9)),
 "O6-":([1,2,4,12,27],(27,10,1,5)),
 "NO6+":([9,11,19,37,52],(28,15,6,10)),
 "NO6-":([5,7,11,17,24],(36,15,6,6)),
 "VO6+":([0,1,9,18,47],(64,35,18,20)),
 "VO6-":([0,1,5,10,23],(64,27,10,12)),
}

def main():
    checks=0
    for s,t,x,y in product(range(1,5),range(1,6),("0","1","M","m"),(0,1)):
        for A in (cover(s,t,x,y),comp(cover(s,t,x,y))):
            degs={len(v) for v in A}
            assert len(degs)==1
            if len(A)>=4 and is_connected(A):
                assert 4*next(iter(degs))>=len(A)
            assert find_c5(A) is None
            checks+=1
    for name,(v,expected) in CERT.items():
        vertices,E=graph(name)
        N,k,lam,mu=expected
        assert len(vertices)==N and len(set(v))==5
        assert set(v).issubset(vertices)
        assert all(E(v[i],v[j])==((j-i) in (1,4))
                   for i in range(5) for j in range(i+1,5))
        assert all(sum(E(a,b) for b in vertices)==k for a in vertices)
        cedge=set();cnon=set()
        for i,a in enumerate(vertices):
            for b in vertices[i+1:]:
                c=sum(E(a,z) and E(b,z) for z in vertices)
                (cedge if E(a,b) else cnon).add(c)
        assert cedge=={lam} and cnon=={mu},(name,cedge,cnon)
    for q in range(2,52):
        nb=(q+1)*(q*q+1)*(q**3+1)*(q**4+1)
        db=q*(q*q+1)*(q**5-1)//(q-1)
        k=q*(q**3+1)*(q**8-1)//(q-1)
        v=(q**12-1)*(q**9-1)//((q**4-1)*(q-1))
        n1=k;d1=q*db+q-1
        assert k==q*nb
        assert n1-4*d1==(q+1)*(q*q-q+1)*(q**3+q*q+q-1)*(q**5-2*q*q-q-4)>0
        n2=v-k-1
        assert n2==q**8*(q**4+1)*sum(q**i for i in range(5))
        assert (k*(k-d1-1))%n2==0
        mu=k*(k-d1-1)//n2
        assert mu==(q+1)**2*(q*q+1)*(q*q-q+1)
        assert n2>4*k>4*(k-mu)
    print("PASS: %s cover/complement checks, seven SRG C5 certificates, 50 E6 parameter tests"%checks)

if __name__=="__main__":main()
