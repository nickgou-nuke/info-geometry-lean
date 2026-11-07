from fractions import Fraction

def ldl(A):
    n = len(A)
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    D = [Fraction(0) for _ in range(n)]
    
    for i in range(n):
        L[i][i] = Fraction(1)
        sum_D = Fraction(0)
        for k in range(i):
            sum_D += L[i][k] * L[i][k] * D[k]
        D[i] = A[i][i] - sum_D
        
        for j in range(i + 1, n):
            sum_L = Fraction(0)
            for k in range(i):
                sum_L += L[j][k] * L[i][k] * D[k]
            if D[i] != 0:
                L[j][i] = (A[j][i] - sum_L) / D[i]
            else:
                L[j][i] = Fraction(0)
                
    return L, D

edges = [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]
A = [[Fraction(2) if i == j else Fraction(0) for j in range(10)] for i in range(10)]
for u, v in edges:
    A[u][v] = Fraction(-1)
    A[v][u] = Fraction(-1)

L, D = ldl(A)
print("D:", [str(d) for d in D])

# Compute P_inv = L^T
P_inv = [[L[j][i] for j in range(10)] for i in range(10)]

def invert_upper_triangular(U):
    n = len(U)
    V = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        V[i][i] = Fraction(1)
        for j in range(i+1, n):
            s = sum(U[i][k]*V[k][j] for k in range(i+1, j+1))
            V[i][j] = -s
    return V

P = invert_upper_triangular(P_inv)

print("P_inv:")
for row in P_inv:
    print([str(x) for x in row])

print("P:")
for row in P:
    print([str(x) for x in row])
