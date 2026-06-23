-- Macaulay2 Clifford complex structure verification via matrix representation
e1 = matrix(QQ, {{1, 0}, {0, -1}})
e2 = matrix(QQ, {{0, 1}, {1, 0}})
I = id_(QQ^2)
S = e1 * e2
assert(S^2 == -I)
print "Macaulay2: Clifford complex equivalence verified successfully."
exit 0
