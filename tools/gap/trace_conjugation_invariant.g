# Finite GAP witness for trace-pairing invariance under conjugation.
# This checks one exact rational carrier; it is evidence, not a Lean axiom.
R := Rationals;;
U := [ [ 1, 1 ], [ 0, 1 ] ];;
Ui := [ [ 1, -1 ], [ 0, 1 ] ];;
A := [ [ 2, 3 ], [ 5, 7 ] ];;
B := [ [ -1, 4 ], [ 6, 2 ] ];;
if U * Ui <> [ [ 1, 0 ], [ 0, 1 ] ] then Error("TRACE_CONJ_INVERSE_FAIL"); fi;
if Trace((U * A * Ui) * (U * B * Ui)) <> Trace(A * B) then
  Error("TRACE_PAIRING_CONJUGATION_FAIL");
fi;
Print("GAP_TRACE_CONJUGATION=PASS\n");
Print("GAP_TRACE_PAIRING_VALUE=", Trace(A * B), "\n");
QUIT;
