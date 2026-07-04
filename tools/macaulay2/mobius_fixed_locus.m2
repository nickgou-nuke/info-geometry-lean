R = QQ[x_0, x_1, y_0, y_1]

-- 1. Define the diagonal in P^1 x P^1
Delta = ideal(x_0*y_1 - x_1*y_0)

-- 2. Define a fractional linear transformation M
M = matrix{{1, 2}, {3, 4}}
a = M_(0,0); b = M_(0,1);
c = M_(1,0); d = M_(1,1);

-- 3. Define the graph of M
GraphM = ideal(y_0*(c*x_0 + d*x_1) - y_1*(a*x_0 + b*x_1))

-- 4. Compute the intersection
I_unsat = Delta + GraphM

-- 5. Saturate with respect to the irrelevant ideal of P^1 x P^1
B = ideal(x_0, x_1) * ideal(y_0, y_1)
I_sat = saturate(I_unsat, B)

-- 6. Show the scheme has degree 2
deg = degree I_sat
print("The degree of the saturated intersection is: " | toString deg)
assert(deg == 2)

-- 7. Project to the first P^1 to explicitly see the fixed points equation
FixedLocusP1 = eliminate(ideal(y_0, y_1), I_sat)
print("The fixed points are defined by: " | toString FixedLocusP1)
degP1 = degree FixedLocusP1
assert(degP1 == 2)
