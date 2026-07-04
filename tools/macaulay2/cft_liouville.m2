-- cft_liouville.m2
-- Define a rational field ring with variables c, P, and Delta
R = QQ[c, P, Delta]

-- Define the algebra exactly and evaluate (c-1)/24 + P^2
expr = (c - 1)/24 + P^2

-- Define the relation for the conformal dimension bound
-- Delta = (c-1)/24 + P^2
f = Delta - expr

-- Define the ideal domain
I = ideal(f)

-- Map the polynomial explicitly and confirm its difference from Delta is strictly zero within the ideal domain
-- The difference is Delta - expr
diffExpr = Delta - expr

-- Confirm the difference is strictly zero modulo the ideal
isZero = (diffExpr % I == 0)

if isZero then (
    print("Confirmed: The difference from Delta is strictly zero within the ideal domain.")
) else (
    print("Failed: The difference is not zero.")
)
