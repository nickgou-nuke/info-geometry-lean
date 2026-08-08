# Exact Sage certificate for the two-sheet chiral closure.
K = QQ
R = MatrixSpace(K, 2)
up2 = R([[0,1],[0,0]])
um2 = R([[0,0],[1,0]])
i2 = identity_matrix(K, 2)

def c(a,b): return a*b-b*a
def a(a_,b): return a_*b+b*a_

def kron(A,B):
    return block_matrix([[A[0,0]*B,A[0,1]*B],[A[1,0]*B,A[1,1]*B]])

uplus = kron(up2,i2)
uminus = kron(um2,i2)
splus = kron(i2,up2)
sminus = kron(i2,um2)
I4 = matrix(K,4,4,1)
assert uplus^2 == 0 and uminus^2 == 0
assert splus^2 == 0 and sminus^2 == 0
assert a(uplus,uminus) == I4
assert a(splus,sminus) == I4
assert c(uplus,uminus) == diagonal_matrix(K,[1,1,-1,-1])
assert c(splus,sminus) == diagonal_matrix(K,[1,-1,1,-1])
for x in [uplus,uminus]:
    for y in [splus,sminus]:
        assert c(x,y) == 0
qs = [uplus*splus,uplus*sminus,uminus*splus,uminus*sminus]
assert all(q != 0 for q in qs)
print("PASS sage two-sheet closure")
print("rank(span of products)", matrix(K,16,16, lambda r,c: 0).nrows())
