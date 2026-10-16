#!/usr/bin/env python3
"""Exact finite SRG screen for generalised clique covers."""
def model(s,t,x,y):
    n=2*s*t
    def adj(a,b):
        if a==b:return False
        aa,ca,pa=a//(s*t),(a%(s*t))//t,a%t
        bb,cb,pb=b//(s*t),(b%(s*t))//t,b%t
        if aa==bb:return ca==cb
        if ca!=cb:return y==1
        return (x=="1" or (x=="M" and pa==pb) or
                (x=="m" and pa!=pb))
    return [[adj(i,j) for j in range(n)] for i in range(n)]
def is_srg(A):
    n=len(A)
    if len({sum(r) for r in A})!=1:return False
    count={True:set(),False:set()}
    for i in range(n):
        for j in range(i+1,n):
            count[A[i][j]].add(sum(A[i][k] and A[j][k] for k in range(n)))
    return all(len(v)<=1 for v in count.values())
def expected(s,t,x,y):
    if t==1:return y==0 or x in ("1","M") or s<=2
    if s==1:return x in ("0","1","m") or (x=="M" and t<=2)
    return (y==0 and x in ("0","1")) or (s==2 and y==1 and x=="0")
total=ok=0
for s in range(1,5):
    for t in range(1,7):
        for x in ("0","1","M","m"):
            for y in (0,1):
                b=is_srg(model(s,t,x,y))
                assert b==expected(s,t,x,y), (s,t,x,y,b)
                total+=1;ok+=int(b)
print("SRG cover audit PASS:",total,"models,",ok,"strongly regular")
