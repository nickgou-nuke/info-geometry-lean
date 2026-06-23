# GAP verification of Zorn projectors & sandwich formulas
OP1 := [[1, 0], [0, 0]];;
OP2 := [[0, 0], [0, 1]];;
I := [[1, 0], [0, 1]];;

T := OP1 - OP2;;
if T^3 = T then
    Print("GAP: Tripotency T^3 = T verified.\n");
else
    Error("GAP: Tripotency check failed.\n");
fi;

# Reconstruct
P_plus := 1/2 * (T^2 + T);;
P_minus := 1/2 * (T^2 - T);;
P_zero := I - T^2;;

if P_plus = OP1 and P_minus = OP2 and P_zero = [[0, 0], [0, 0]] then
    Print("GAP: Projector reconstruction verified.\n");
else
    Error("GAP: Reconstruction check failed.\n");
fi;

# Sandwich
Mat := [[1, 2], [3, 4]];; # generic matrix
S12 := OP1 * Mat * OP2;;
S21 := OP2 * Mat * OP1;;

if S12 = [[0, 2], [0, 0]] and S21 = [[0, 0], [3, 0]] then
    Print("GAP: Zorn sandwich isolating checked successfully.\n");
else
    Error("GAP: Sandwich check failed.\n");
fi;
quit;
