needsPackage "WeylAlgebras"

<< "================================================================" << endl
<< " Bergman Metric Transform using Weyl Algebra D-modules" << endl
<< "================================================================" << endl

-- 1. Setup Weyl Algebra
W = QQ[z, zb, Dz, Dzb, WeylAlgebra => {{z, Dz}, {zb, Dzb}}]
<< "Weyl Algebra W defined with variables: " << gens W << endl

-- 2. Define the differential operator for the Bergman metric
-- \omega = i \partial \bar{\partial} \log B(z,z)
-- We drop the 'i' for algebraic computation over QQ
bergmanOp = Dz * Dzb
<< "Bergman Operator (omega_op) = " << bergmanOp << endl

-- 3. Treat log B(z,z) as a symbolic generator L in a free D-module W^1
-- This represents the formal action before specifying B(z,z)
F = W^1
L = F_0
symbolicAction = bergmanOp * L
<< "Formal action on symbolic generator L = log B(z,z): " << symbolicAction << endl

-- 4. Algebraic evaluation of the second-order derivatives of log B(z,z)
-- We know that \partial_z \partial_{\bar{z}} \log B = (B * Dz Dzb B - Dz B * Dzb B) / B^2
R = QQ[B, Bz, Bzb, Bzzb]
logB_numerator = B * Bzzb - Bz * Bzb
<< "Numerator of \\partial_z \\partial_{\\bar{z}} \\log B in terms of B and its derivatives: " << logB_numerator << endl

-- 5. Specialization: The Bergman kernel for the unit disk B(z,z) = 1 - z*zb
P = QQ[z, zb]
BKernel = 1 - z*zb
BzKernel = diff(z, BKernel)
BzbKernel = diff(zb, BKernel)
BzzbKernel = diff(z, diff(zb, BKernel))

<< "--- Specialization to Unit Disk B(z,z) = 1 - z*zb ---" << endl
<< "B = " << BKernel << endl
<< "Dz B = " << BzKernel << endl
<< "Dzb B = " << BzbKernel << endl
<< "Dz Dzb B = " << BzzbKernel << endl

KernelNumerator = BKernel * BzzbKernel - BzKernel * BzbKernel
<< "Numerator ( B * Dz Dzb B - Dz B * Dzb B ) = " << KernelNumerator << endl
<< "Denominator ( B^2 ) = " << BKernel^2 << endl
<< "So \\partial \\bar{\\partial} \\log(1 - z*zb) = (" << KernelNumerator << ") / (" << BKernel^2 << ")" << endl

exit 0
