# GAP verification of Hodge-Trifactor operator and partition factors
# 1. Operator algebra check using matrix representation
P_ex := [[1, 0, 0], [0, 0, 0], [0, 0, 0]];
P_co := [[0, 0, 0], [0, 1, 0], [0, 0, 0]];
P_har := [[0, 0, 0], [0, 0, 0], [0, 0, 1]];

# Projectiveness
if P_ex * P_ex <> P_ex or P_co * P_co <> P_co or P_har * P_har <> P_har then
    Error("GAP: Projector check failed.\n");
fi;

# Orthogonality
zero_mat := [[0,0,0],[0,0,0],[0,0,0]];
if P_ex * P_co <> zero_mat or P_ex * P_har <> zero_mat then
    Error("GAP: Orthogonality check failed.\n");
fi;

T := P_ex - P_co;
T3 := T * T * T;

if T3 <> T then
    Error("GAP: Tripotent operator check failed.\n");
fi;
Print("GAP: Hodge-Trifactor operator algebra verified.\n");
quit;
