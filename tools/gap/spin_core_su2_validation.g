# tools/gap/spin_core_su2_validation.g

MyComm := function(A, B)
  return A * B - B * A;
end;

AssertEq := function(label, lhs, rhs)
  if lhs <> rhs then
    Error(Concatenation("FAILED: ", label));
  fi;
end;

# Spin-1/2 matrices over QQ.
Jp := [[0, 1], [0, 0]];
Jm := [[0, 0], [1, 0]];
J0 := [[1/2, 0], [0, -1/2]];
I2 := [[1, 0], [0, 1]];
Z2 := [[0, 0], [0, 0]];

AssertEq("[J0,Jp]=Jp", MyComm(J0, Jp), Jp);
AssertEq("[J0,Jm]=-Jm", MyComm(J0, Jm), -Jm);
AssertEq("[Jp,Jm]=2J0", MyComm(Jp, Jm), 2 * J0);

# Spin-half Casimir:
# J^2 = J0^2 + 1/2(J+J- + J-J+) = 3/4 I.
Casimir := J0 * J0 + (1/2) * (Jp * Jm + Jm * Jp);
AssertEq("spin-half Casimir = 3/4", Casimir, (3/4) * I2);

# SUSY nilpotent block sanity, if SusyCore uses these as Q/Q† atoms.
AssertEq("Jp^2=0", Jp * Jp, Z2);
AssertEq("Jm^2=0", Jm * Jm, Z2);

Print("SPIN_CORE_SU2_VALIDATION_OK\n");
Print("field=QQ\n");
Print("casimir=3/4\n");
QUIT;
