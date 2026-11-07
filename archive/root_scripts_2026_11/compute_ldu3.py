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

# Permute 8 and 9
P_perm = [0, 1, 2, 3, 4, 5, 6, 7, 9, 8]
A_perm = [[A[P_perm[i]][P_perm[j]] for j in range(10)] for i in range(10)]

L, D = ldl(A_perm)
print("D:", [str(d) for d in D])

pos = sum(1 for d in D if d > 0)
neg = sum(1 for d in D if d < 0)
zero = sum(1 for d in D if d == 0)
print(f"Signature: ({pos}, {neg}, {zero})")
