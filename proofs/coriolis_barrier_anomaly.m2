-- Macaulay2 script for Coriolis barrier anomaly and D-module dilation verification
print "=== Macaulay2: D-Module Dilation Verification ==="

-- Define the Weyl algebra A_1 over QQ: QQ[x][d] where d stands for d/dx
W = QQ[x, d, WeylAlgebra => {x => d}]

-- Dilation operator D = x * d
D = x * d

-- Check the conformal scaling relation [d, D] = d
comm = d * D - D * d
print "Commutator [d, x*d] = ";
print comm;

-- Verify it equals d
if comm == d then (
  print "D-module conformal scaling relation [d, x*d] = d holds!\n";
) else (
  error "Verification failed!";
)

-- Matrix Projector Verification
PD = matrix{{1, 0, 0}, {0, 1, 0}, {0, 0, 0}};
PL = matrix{{1, 0, 0}, {0, 0, 0}, {0, 0, 1}};
PR = matrix{{0, 0, 0}, {0, 1, 0}, {0, 0, 1}};

-- Dilation matrix
DM = (PL - PR) * (1/2);

-- Commutator helper
commMat = (A, B) -> A * B - B * A;

commPDD = commMat(PD, DM);
chiL = commMat(PD, PL);
chiR = commMat(PD, PR);
decomp = (chiL - chiR) * (1/2);

diffMat = commPDD - decomp;
print "Difference [PD, DM] - 1/2 * (chiL - chiR) = ";
print diffMat;

if diffMat == 0 then (
  print "Projector and dilation commutator relation holds in M2!\n";
) else (
  error "Verification failed!";
)
