# Exact SageMath certificate for the 1 + 8 + 1 five-graded envelope.
K = QQ
n = 10
E = lambda i,j: matrix(K,n,n,{(i,j):1})
bracket = lambda A,B: A*B-B*A

# endpoint indices: minus=0, middle=1..8, plus=9
Uplus = E(9,1)
Splus = E(1,0)
Uminus = E(0,1)
Sminus = E(1,9)
Qplus = bracket(Uplus,Splus)
Qminus = bracket(Uminus,Sminus)
D0 = bracket(Sminus,Uplus)

assert Qplus == E(9,0) and Qminus == E(0,9)
assert D0 == E(1,1)-E(9,9)
assert Qplus != 0 and Qminus != 0 and D0 != 0

# ad(D0) is a derivation; test on a basis of all 100 matrix units.
basis = [E(i,j) for i in range(n) for j in range(n)]
for X in basis:
    for Y in basis:
        assert bracket(D0,bracket(X,Y)) == \
            bracket(bracket(D0,X),Y)+bracket(X,bracket(D0,Y))

weights = [-1] + [0]*8 + [1]
def grade(A):
    support = {weights[i]-weights[j] for i,j in A.dict()}
    return support.pop() if len(support)==1 else None
assert grade(Uplus)==1 and grade(Splus)==1
assert grade(Uminus)==-1 and grade(Sminus)==-1
assert grade(Qplus)==2 and grade(Qminus)==-2 and grade(D0)==0
print("PASS Sage two-sheet TKK derivations and five grades")
