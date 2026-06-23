# GAP algebraic verification of Clifford complex structure via matrix representation
e1 := [[1, 0], [0, -1]];;
e2 := [[0, 1], [1, 0]];;
I := [[1, 0], [0, 1]];;

# Bivector S = e1 * e2
S := e1 * e2;;

# S should square to -I
if S^2 = -I then
    Print("GAP: Clifford equivalence S^2 = -I verified successfully.\n");
else
    Error("GAP: Clifford equivalence verification failed.\n");
fi;
quit;
