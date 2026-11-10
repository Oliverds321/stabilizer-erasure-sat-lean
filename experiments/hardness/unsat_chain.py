import sys, itertools
sys.path.insert(0, sys.argv[1])
from reduction_check import *
for cl in ([[(0,0)],[(0,1)]], [[(0,1)],[(0,0)]]):
    N=1; rows, rhs, n, idx = gadget(N, cl); K=sum(map(len,cl)); t=N+K; m=r=t+2
    nq, X, Z = quantum_code(rows, rhs, n, explicit_kernel(N, cl, idx), m, r)
    Xd, Zd = basis_dict(X), basis_dict(Z); found=None
    for w in range(1, t+4):
        for supp in itertools.combinations(range(nq), w):
            v = sum(1<<q for q in supp)
            if all(popc(v&z)%2==0 for z in Z) and not in_span(v, Xd): found=("X",w); break
            if all(popc(v&x)%2==0 for x in X) and not in_span(v, Zd): found=("Z",w); break
        if found: break
    print(cl, "qubits", nq, "t+1 =", t+1, "lightest logical:", found, "sat:", sat(N,cl))
