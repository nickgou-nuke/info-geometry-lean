-- Load D-modules package as requested
needsPackage "Dmodules"

-- The boson-fermion correspondence gives bosons alpha_n satisfying:
-- [alpha_n, alpha_m] = n * delta_{n, -m}
-- For n > 0, alpha_n acts as a derivative n * d/dx_n
-- For n < 0, alpha_n acts as multiplication by x_{-n}
-- We can truncate this to N variables to form a finite Weyl algebra.
N = 3
R = QQ[x_1..x_N]
D = makeWeylAlgebra R
use D
-- Now the variables in D are x_1..x_N and dx_1..dx_N.
-- In D, we have dx_1 * x_1 - x_1 * dx_1 = 1.

-- Define the bosons alpha_n for n > 0 and alpha_{-n}
-- In D-modules, [dx_n, x_n] = 1. We want [alpha_n, alpha_{-n}] = n.
-- Let alpha_{-n} = x_n
-- Let alpha_n = n * dx_n
alpha_minus = new HashTable from { 1 => x_1, 2 => x_2, 3 => x_3 }
alpha_plus  = new HashTable from { 1 => 1*dx_1, 2 => 2*dx_2, 3 => 3*dx_3 }

-- Check commutators
-- [alpha_n, alpha_{-m}] = alpha_n * alpha_{-m} - alpha_{-m} * alpha_n
checkCommutator = (n, m) -> (
    a_n = alpha_plus#n;
    a_m = alpha_minus#m;
    a_n * a_m - a_m * a_n
)

<< "Commutator [alpha_1, alpha_{-1}] = " << checkCommutator(1,1) << endl
<< "Commutator [alpha_2, alpha_{-2}] = " << checkCommutator(2,2) << endl

-- The energy operator (Hamiltonian) H = sum_{l=1}^N (l - 1/2) * ... wait.
-- H = sum_{k>0} alpha_{-k} alpha_k
H = sum(1..N, k -> alpha_minus#k * alpha_plus#k)
<< "Hamiltonian H = " << H << endl

exit 0
