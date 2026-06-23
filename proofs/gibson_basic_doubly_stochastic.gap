# Exact-rational GAP witnesses for Gibson basic doubly stochastic matrices.

Basic12 := function(x)
  return [[x, 1-x, 0], [1-x, x, 0], [0, 0, 1]];
end;;

RowSums := function(M) return List(M, Sum); end;;
ColSums := function(M)
  return List([1..Length(M[1])], j -> Sum(List(M, r -> r[j])));
end;;

A := Basic12(2/3);;
B := Basic12(3/5);;
P := A * B;;
if RowSums(A) <> [1,1,1] then Error("row sums failed"); fi;
if ColSums(A) <> [1,1,1] then Error("column sums failed"); fi;
if Determinant(A) <> 1/3 then Error("determinant failed"); fi;
if RowSums(P) <> [1,1,1] then Error("product row sums failed"); fi;
if ColSums(P) <> [1,1,1] then Error("product column sums failed"); fi;
if Determinant(P) <> Determinant(A) * Determinant(B) then Error("product determinant failed"); fi;
Print("gibson basic doubly stochastic GAP certificate: ok\n");
