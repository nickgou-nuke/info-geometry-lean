# Fixed-basis GAP certificate for the 2x2 square-zero shear.
# GAP uses 1-based matrix indices; the Lean readback uses Fin 2 in the same
# row-major order.
R := Rationals;;
N := [ [ 0, 1 ], [ 0, 0 ] ];;
if N * N <> [ [ 0, 0 ], [ 0, 0 ] ] then
  Error("SQUARE_ZERO_SHEAR_FAIL");
fi;
Print("GAP_1_BASED_MATRIX_ORDER=ROW_MAJOR\n");
Print("GAP_SQUARE_ZERO_SHEAR=PASS\n");
QUIT;
