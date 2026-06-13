# tools/gap/susy_core_validation.g

AssertEq := function(label, lhs, rhs)
  if lhs <> rhs then
    Error(Concatenation("FAILED: ", label));
  fi;
end;

# Nilpotent blocks over QQ.
Q  := [[0, 1], [0, 0]];
Qd := [[0, 0], [1, 0]];
Z2 := [[0, 0], [0, 0]];

AssertEq("Q^2 = 0", Q * Q, Z2);
AssertEq("(Qd)^2 = 0", Qd * Qd, Z2);

Hp := Qd * Q;
Hm := Q * Qd;

Tr := function(M) return M[1][1] + M[2][2]; end;
AssertEq("Witten trace cancellation", Tr(Hp) - Tr(Hm), 0);

Print("SUSY_CORE_VALIDATION_OK\n");
Print("Q^2=0\n");
Print("WittenIndex=0\n");
QUIT;
