F := Rationals;

# SU(2) generators in the 0-graded component:
Jz := [[0,0,0,0], [0,1,0,0], [0,0,-1,0], [0,0,0,0]];
Jp := [[0,0,0,0], [0,0,1,0], [0,0,0,0], [0,0,0,0]];
Jm := [[0,0,0,0], [0,0,0,0], [0,1,0,0], [0,0,0,0]];

# TKK 5-grading element
H_grad := [[1,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,-1]];

Bracket := function(A, B)
    return A*B - B*A;
end;

# 1. Check SU(2) algebra
su2_ok := Bracket(Jz, Jp) = 2*Jp and Bracket(Jz, Jm) = -2*Jm and Bracket(Jp, Jm) = Jz;

# 2. Check SU(2) is in 0-graded component
grade0_ok := Bracket(H_grad, Jz) = 0*Jz and Bracket(H_grad, Jp) = 0*Jp and Bracket(H_grad, Jm) = 0*Jm;

# 3. Check Cartan-Killing form on SU(2) block
KillingFormCheck := function(X, Y)
    return Sum([1..4], i -> (X*Y)[i][i]);
end;

kf_ok := KillingFormCheck(Jz, Jz) = 2 and KillingFormCheck(Jp, Jm) = 1 and KillingFormCheck(Jz, Jp) = 0;

# 4. Check adjoint action of SU(2) on graded components
E14 := [[0,0,0,1], [0,0,0,0], [0,0,0,0], [0,0,0,0]];

E12 := [[0,1,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0]];
E13 := [[0,0,1,0], [0,0,0,0], [0,0,0,0], [0,0,0,0]];
E24 := [[0,0,0,0], [0,0,0,1], [0,0,0,0], [0,0,0,0]];
E34 := [[0,0,0,0], [0,0,0,0], [0,0,0,1], [0,0,0,0]];

E41 := [[0,0,0,0], [0,0,0,0], [0,0,0,0], [1,0,0,0]];

E21 := [[0,0,0,0], [1,0,0,0], [0,0,0,0], [0,0,0,0]];
E31 := [[0,0,0,0], [0,0,0,0], [1,0,0,0], [0,0,0,0]];
E42 := [[0,0,0,0], [0,0,0,0], [0,0,0,0], [0,1,0,0]];
E43 := [[0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,1,0]];

NullMat4 := [[0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0]];

grad2_ok := Bracket(H_grad, E14) = 2*E14;
grad1_ok := Bracket(H_grad, E12) = 1*E12 and Bracket(H_grad, E13) = 1*E13 and Bracket(H_grad, E24) = 1*E24 and Bracket(H_grad, E34) = 1*E34;
grad_minus2_ok := Bracket(H_grad, E41) = -2*E41;
grad_minus1_ok := Bracket(H_grad, E21) = -1*E21 and Bracket(H_grad, E31) = -1*E31 and Bracket(H_grad, E42) = -1*E42 and Bracket(H_grad, E43) = -1*E43;

# Grade +1 components under SU(2)
action1_ok := Bracket(Jz, E12) = -E12 and Bracket(Jz, E13) = E13 and Bracket(Jz, E24) = E24 and Bracket(Jz, E34) = -E34;
action2_ok := Bracket(Jp, E12) = -E13 and Bracket(Jp, E34) = E24;
action3_ok := Bracket(Jm, E13) = -E12 and Bracket(Jm, E24) = E34;

# Grade +2 and -2 components under SU(2) (Singlets)
action4_ok := Bracket(Jz, E14) = NullMat4 and Bracket(Jp, E14) = NullMat4 and Bracket(Jm, E14) = NullMat4;
action5_ok := Bracket(Jz, E41) = NullMat4 and Bracket(Jp, E41) = NullMat4 and Bracket(Jm, E41) = NullMat4;

# Grade -1 components under SU(2)
action6_ok := Bracket(Jz, E21) = E21 and Bracket(Jz, E31) = -E31 and Bracket(Jz, E42) = -E42 and Bracket(Jz, E43) = E43;
action7_ok := Bracket(Jp, E31) = E21 and Bracket(Jp, E42) = -E43;
action8_ok := Bracket(Jm, E21) = E31 and Bracket(Jm, E43) = -E42;

all_ok := su2_ok and grade0_ok and kf_ok and grad2_ok and grad1_ok and grad_minus2_ok and grad_minus1_ok and action1_ok and action2_ok and action3_ok and action4_ok and action5_ok and action6_ok and action7_ok and action8_ok;

if all_ok then
    Print("true\n");
else
    Print("false\n");
fi;

QUIT;
