"""Exact triangle-count check for unequal-clique Taylor doubles.

Enumerates all ordered positive compositions with total n in 3..10.
For every base composition, verifies the closed triangle formula at
every vertex of both the Taylor double and the mate-matching variant.
No graph-library package is used.
"""
from itertools import combinations


def composition_from_cuts(n, cuts):
    result = []
    k = 1
    for i in range(n - 1):
        if cuts & (1 << i):
            result.append(k)
            k = 1
        else:
            k += 1
    result.append(k)
    return result


def double_adj(sizes, with_matching):
    indices = [i for i, k in enumerate(sizes) for _ in range(k)]
    n = len(indices)
    adjacency = [[False] * (2*n) for _ in range(2*n)]
    for u in range(2*n):
        for v in range(u+1, 2*n):
            x,y=u%n,v%n
            adj=(
                x!=y and (
                    (u//n==v//n and indices[x]==indices[y])
                    or (u//n!=v//n and indices[x]!=indices[y])
                )
            ) or (with_matching and x==y and u//n !=v//n)
            adjacency[u][v] = adjacency[v][u] = adj
    return adjacency, indices


def triangles_at(adj, x):
    return sum(adj[x][a] and adj[x][b] and adj[a][b]
               for a,b in combinations(range(len(adj)), 2))


def expected(sizes, index):
    n=sum(sizes)
    k=sizes[index]
    return sum(t*(t-1)//2 for t in sizes)+(k-1)*(n-k-1)


def main():
    checked=0
    for n in range(3,11):
        for cuts in range(1,1<<(n-1)):
            sizes=composition_from_cuts(n,cuts)
            for matching in (False,True):
                adj,index=double_adj(sizes,matching)
                for vertex in range(2*n):
                    actual=triangles_at(adj,vertex)
                    predicted=expected(sizes,index[vertex%n])
                    assert actual==predicted,(sizes,matching,vertex,actual,predicted)
                checked+=1
    print('Double graphs checked:',checked)
    print('K3+K2+K1 expected triangles:',
          [expected((3,2,1),i) for i in range(3)])
    assert checked==2024
    print('SECTION 3 TRIANGLE FORMULA PASS')


if __name__ == '__main__':
    main()
