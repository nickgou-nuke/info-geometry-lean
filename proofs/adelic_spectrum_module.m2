-- Macaulay2 script
-- D = d + i*e, D_dag = d - i*e
-- D + D_dag = 1  => 2d = 1
-- D = l + i*m => d = l, e = m
-- Re(lambda) = l
-- Prove 2l = 1

R = QQ[d, e, l, m]
I = ideal(2*d - 1, d - l, e - m)
G = gens gb I
print G
