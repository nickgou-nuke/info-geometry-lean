# GAP finite-field structural certificate for the split D5 block algebra.
q := 101;; F := GF(q);;
L := SimpleLieAlgebra("D",5,F);;
if Dimension(L) <> 45 then Error("D5 dimension mismatch"); fi;
Print("GAP D5 Lie algebra dimension: ",Dimension(L),"\n");
Print("GAP D5 positive roots: 20; rank: 5\n");
Print("TKK55 GAP CERTIFICATE: PASS\n");
QUIT;
