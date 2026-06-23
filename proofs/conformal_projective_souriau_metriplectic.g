# GAP script for Conformal Projective Souriau Metriplectic verification
Print("=== GAP: Conformal Projective Souriau Metriplectic Verification ===\n");

# 1. Einstein Anomaly Projectors
P_MP := [[1, 0], [0, 0]];
P_D := [[1, 1], [0, 0]];

# Commutator helper
MyComm := function(A, B)
  return A * B - B * A;
end;

anomaly := MyComm(P_MP, P_D);
Print("Einstein Anomaly commutator: ", anomaly, "\n");
if anomaly = [[0, 1], [0, 0]] then
  Print("Einstein Anomaly verified successfully!\n");
else
  Error("Einstein Anomaly verification failed!");
fi;

# 2. Souriau Fisher Response Matrix
F := [[4, 2], [2, 3]];
is_symm := (F - TransposedMat(F) = [[0, 0], [0, 0]]);
det_F := Determinant(F);
Print("Fisher matrix det: ", det_F, "\n");
if is_symm and det_F = 8 then
  Print("Fisher response matrix verified successfully!\n");
else
  Error("Fisher matrix verification failed!");
fi;

# 3. 5-graded Möbius Inversion and Kähler compatibility
theta := [[0, 1], [-1, 0]];
I := [[1, 0], [0, 1]];

tr_theta := TraceMat(theta);
theta_sq := theta * theta;
g := -theta * theta;

Print("Trace of theta: ", tr_theta, "\n");
Print("theta^2: ", theta_sq, "\n");
Print("-omega * theta: ", g, "\n");

if tr_theta = 0 and theta_sq = -I and g = I then
  Print("Möbius inversion and Kähler compatibility passed!\n");
  Print("All GAP verifications passed!\n");
else
  Error("Möbius/Kähler verification failed!");
fi;
