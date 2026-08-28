# Exact finite GAP witness for the order-two collision moment.
# This is evidence for the finite probability-simplex statement only.
p := [ 1/2, 1/3, 1/6 ];;
if Sum(p) <> 1 then Error("RENyi_NORMALIZATION_FAIL"); fi;
c := Sum(p, x -> x^2);;
if c < 0 or c > 1 then Error("RENYI_COLLISION_BOUND_FAIL"); fi;
Print("GAP_RENYI_COLLISION_SUM=", c, "\n");
Print("GAP_RENYI_COLLISION_BOUND=PASS\n");
QUIT;
