# bergman.g
Print("Starting Bergman Metric Scale Matrix Limit Computation\n");

# Invariant parameters of the Poincaré boundary
# Across punctured domain representations (e.g. parabolic elements in SL2(Z))

# Define the generators of SL(2, Z)
S := [[0, -1], [1, 0]];
T := [[1, 1], [0, 1]];

# Punctured domain representation: parabolic element T
# We evaluate the invariant parameter (Trace)
inv_S := TraceMat(S);
inv_T := TraceMat(T);

Print("Invariant parameter of S: ", inv_S, "\n");
Print("Invariant parameter of T: ", inv_T, "\n");

# Construct the metric scale matrix limit
# A sequence of scaling limits: say, (S*T)^n
LimitScaleMatrix := function(n)
    local M, i;
    M := [[1,0],[0,1]];
    for i in [1..n] do
        M := M * S * T;
    od;
    return M;
end;

limit_10 := LimitScaleMatrix(10);
Print("Scale matrix after 10 iterations: ", limit_10, "\n");

# Computationally isolate the local limit natively
# For punctured domains, the local limit is often related to the boundary fixed points
# For T, the fixed point is infinity, represented by [1, 0]^T
vec := [1, 0];
local_limit := vec * T;
Print("Local limit native isolation: ", local_limit, "\n");

Print("Computation finished successfully.\n");
