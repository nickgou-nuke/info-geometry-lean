-- tools/macaulay2/circle_inversion.m2

-- Define the inversion mapping algebraically over real (x, y) coordinates.
-- We use a polynomial ring with coordinates (x,y) and target coordinates (X,Y)
R = QQ[x, y, X, Y]

-- The inversion mapping is (x, y) |-> (x/(x^2+y^2), y/(x^2+y^2))
-- Which means X = x/(x^2+y^2) and Y = y/(x^2+y^2)
-- Cross-multiplying gives the defining relations of the graph:
I = ideal(X*(x^2+y^2) - x, Y*(x^2+y^2) - y)

-- Saturate the ideal to remove the components where the denominator vanishes
-- This gives the true ideal of the graph of the rational map
J = saturate(I, ideal(x^2+y^2))

print "--- Ideal of the graph of the inversion map ---"
print J

-- Compute the syzygies showing that the mapping squared is the identity.
-- This is equivalent to showing that the reverse mapping holds:
-- x = X/(X^2+Y^2) and y = Y/(X^2+Y^2)
-- Or algebraically: x*(X^2+Y^2) - X \in J and y*(X^2+Y^2) - Y \in J

relX = x*(X^2+Y^2) - X
relY = y*(X^2+Y^2) - Y

print ""
print "--- Checking that mapping squared is the identity ---"
print("Is x*(X^2+Y^2) - X in J? ", relX % J == 0)
print("Is y*(X^2+Y^2) - Y in J? ", relY % J == 0)

-- Compute the fixed locus and show it equals the circle ideal exactly.
-- The fixed locus is where (X,Y) = (x,y), meaning X = x and Y = y.
fixedIdeal = J + ideal(X - x, Y - y)

-- We eliminate X and Y to find the equation in terms of x and y alone.
circleIdeal = eliminate({X, Y}, fixedIdeal)

print ""
print "--- Fixed locus ideal (eliminating X and Y) ---"
print circleIdeal

print ""
print "--- Checking equality with the circle ideal exactly ---"
print("Does it equal ideal(x^2 + y^2 - 1)? ", circleIdeal == ideal(x^2 + y^2 - 1))
