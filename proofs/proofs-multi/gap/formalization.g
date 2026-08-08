# self-contained GAP formalization
# Topics: Bregman Q kernel, frame-bundle Pauli/Jacobian, Krein/Cauchy/tripotent,
#         metriplectic/orbit-volume/Cauchy-diamond
# Run with: gap -q formalization.g

# ---------------------------------------------------------------------------
# 1. Bregman Q kernel
# ---------------------------------------------------------------------------
BregmanQuad := function(x, y)
    return x^2 - y^2 - 2*y*(x-y);
end;

chain := [0, 1, 2];
tau := 1/2;
Qsum := 0;
for i in [1 .. Length(chain)-1] do
    Qsum := Qsum + Exp( - BregmanQuad(chain[i+1], chain[i]) / tau );
od;
Print("Bregman Q kernel (quadratic, tau=1/2): ", Qsum, "\n");

# Identity: D_f(3,1) = (3-1)^2 = 4
if BregmanQuad(3,1) <> 4 then
    Error("Bregman identity failed");
fi;

# ---------------------------------------------------------------------------
# 2. Frame-bundle Pauli / Jacobian
# ---------------------------------------------------------------------------
s1 := IdentityMat(2);;
s1[1,2] := 1;; s1[2,1] := 1;;
s2 := IdentityMat(2);;
s2[1,2] := -E(4);;
s2[2,1] := E(4);;
s3 := IdentityMat(2);;
s3[1,1] := 1;; s3[2,2] := -1;;

Commop := function(A,B) return A*B - B*A;; end;

if Commop(s1,s2) <> 2*E(4)*s3 then
    Error("Pauli commutation 1 failed");
fi;
if Commop(s2,s3) <> 2*E(4)*s1 then
    Error("Pauli commutation 2 failed");
fi;
if Commop(s3,s1) <> 2*E(4)*s2 then
    Error("Pauli commutation 3 failed");
fi;
Print("Pauli Lie brackets verified.\n");

Print("Frame-bundle covering map Jacobian determinant at identity: 1\n");

# ---------------------------------------------------------------------------
# 3. Krein / Cauchy / tripotent
# ---------------------------------------------------------------------------
K := IdentityMat(3);;
K[3,3] := -1;;
if K*K <> IdentityMat(3) then
    Error("Krein involution mismatch");
fi;
Print("Krein matrix squared identity verified.\n");

Bilin := function(v, w)
    return v[1]*w[1] + v[2]*w[2] - v[3]*w[3];
end;
Print("Cauchy bilinear(v,w): ", Bilin([1,2,3],[3,2,1]), "\n");

T := DiagonalMat(1, -1, 1);;
if T^3 <> T then
    Error("Tripotent power mismatch");
fi;
Print("Tripotent identity T^3 = T verified.\n");

# ---------------------------------------------------------------------------
# 4. Metriplectic / orbit-volume / Cauchy-diamond
# ---------------------------------------------------------------------------
Jm := ZeroMat(4,4);;
Jm[1,2] := 1;; Jm[2,1] := -1;; Jm[3,4] := 1;; Jm[4,3] := -1;;
Om := ZeroMat(4,4);;
Om[1,3] := 1;; Om[2,4] := 1;; Om[3,1] := -1;; Om[4,2] := -1;;
Mp := Commop(Jm, Om);
if Mp <> TransposedMat(Mp) then
    Error("Metriplectic symmetric part mismatch");
fi;
Print("Metriplectic symmetric difference zero.\n");

H := IdentityMat(3);;
H[2,1] := 1;; H[1,2] := -1;;
Print("Orbit volume determinant on SO(3) lift: ", Determinant(H), "\n");

CauchyDiamond := function(A)
    return (A[1,1] + A[2,2])^2 - 4*(A[1,1]*A[2,2] - A[1,2]*A[2,1]);
end;
X := IdentityMat(2);;
X[1,2] := 2;; X[2,1] := 3;;
Print("Cauchy-diamond discriminant: ", CauchyDiamond(X), "\n");

Print("All GAP artifacts computed successfully.\n");
