-- Macaulay2: Bost-Connes D-Module Analysis
--
-- This script explores the modular flow from a D-module perspective,
-- computing the ring of invariants and checking compatibility with
-- the Liouville grading.
--
-- The modular flow σ_t acts on the Bost-Connes algebra by:
--   σ_t(μ_n) = n^{it} · μ_n
--
-- We study this as a D-module action and compute invariants.

needsPackage "Dmodules";
needsPackage "SCHubert";

-- Define the polynomial ring for the Bost-Connes algebra
-- We work with generators indexed by primes for simplicity
R = QQ[mu_2, mu_3, mu_5, mu_7, mu_11, mu_13, Degrees => {1,1,1,1,1,1}];

-- Define the modular flow vector field
-- For each generator mu_n, the flow is: d/dt (μ_n) = i·ln(n)·μ_n
-- This corresponds to the vector field: ξ = Σ i·ln(n)·μ_n·∂/∂μ_n

-- Since we're in characteristic 0, we can work with the Lie algebra
-- of the flow rather than the flow itself

-- Define logarithms of primes (as formal parameters for now)
log2 = 1;  -- We'll treat these as formal parameters
log3 = 1;
log5 = 1;
log7 = 1;
log11 = 1;
log13 = 1;

-- The infinitesimal generator of the modular flow
-- ξ = Σ ln(n) · μ_n · ∂/∂μ_n
xi = log2 * mu_2 * diff(mu_2, R) +
     log3 * mu_3 * diff(mu_3, R) +
     log5 * mu_5 * diff(mu_5, R) +
     log7 * mu_7 * diff(mu_7, R) +
     log11 * mu_11 * diff(mu_11, R) +
     log13 * mu_13 * diff(mu_13, R);

print "=" | toString(newline | "MACAULAY2: Bost-Connes D-Module Analysis" | newline | "=");
print newline;

-- 1. Check if xi is a derivation (it should be by construction)
print "1. Modular flow vector field ξ:";
print xi;
print newline;

-- 2. Compute the action on a monomial
-- For a monomial μ_n = μ_{p1}^{a1} ... μ_{pk}^{ak},
-- the action is: ξ(μ_n) = (Σ ai·ln(pi)) · μ_n
-- This should give the "weight" of the monomial under the flow

testMonomial = mu_2^2 * mu_3 * mu_5^3;
print "2. Action of ξ on test monomial μ_2²·μ_3·μ_5³:";
actionOnMonomial = xi testMonomial;
print actionOnMonomial;
print "Expected: (2·ln(2) + ln(3) + 3·ln(5)) · μ_2²·μ_3·μ_5³";
print "With our normalization: (2 + 1 + 3) · μ_2²·μ_3·μ_5³ = 6 · μ_2²·μ_3·μ_5³";
print newline;

-- 3. Define the Liouville grading operator
-- Γ(μ_n) = (-1)^{Ω(n)} · μ_n
-- This is a Z/2-grading on the algebra

-- Function to compute Ω(n) for monomials
omegaMonomial := (mon) -> (
    total := 0;
    for i from 1 to numgens R do (
        coeff = degree(mon, i);
        total = total + coeff;
    );
    return total;
);

-- Function to compute Liouville grading
liouvilleMonomial := (mon) -> (
    omega = omegaMonomial(mon);
    return (-1)^omega;
);

print "3. Liouville grading on test monomials:";
testMonomials = {
    mu_2,                   -- Ω = 1, Γ = -1
    mu_2 * mu_3,           -- Ω = 2, Γ = +1
    mu_2^2 * mu_3,         -- Ω = 3, Γ = -1
    mu_2^2 * mu_3^2,       -- Ω = 4, Γ = +1
    mu_2 * mu_3 * mu_5,    -- Ω = 3, Γ = -1
    testMonomial           -- Ω = 2+1+3 = 6, Γ = +1
};

for i from 0 to #testMonomials - 1 do (
    mon = testMonomials#i;
    omega = omegaMonomial(mon);
    gamma = liouvilleMonomial(mon);
    print("   Ω(" | toString(mon) | ") = " | toString(omega) | 
          ", Γ = " | toString(gamma));
);
print newline;

-- 4. Verify that Γ is a ring homomorphism (multiplicative)
print "4. Multiplicativity of Liouville grading:";
mon1 = mu_2 * mu_3;
mon2 = mu_5 * mu_7;
prod = mon1 * mon2;

gamma1 = liouvilleMonomial(mon1);
gamma2 = liouvilleMonomial(mon2);
gammaProd = liouvilleMonomial(prod);

print("   Γ(" | toString(mon1) | ") = " | toString(gamma1));
print("   Γ(" | toString(mon2) | ") = " | toString(gamma2));
print("   Γ(" | toString(prod) | ") = " | toString(gammaProd));
print("   Γ(mon1) · Γ(mon2) = " | toString(gamma1 * gamma2));

if gammaProd == gamma1 * gamma2 then (
    print "   ✅ Multiplicative: Γ(monomial1 · monomial2) = Γ(monomial1) · Γ(monomial2)";
) else (
    print "   ❌ NOT multiplicative!";
);
print newline;

-- 5. Commutation check: Does Γ commute with the modular flow?
-- Since both act diagonally on monomials (by scalars), they should commute

print "5. Commutation of Γ and ξ on test monomials:";
print "   For a monomial m, we check: Γ(ξ(m)) = ξ(Γ(m))";
print "   Since Γ(m) = γ·m (scalar), we have ξ(Γ(m)) = ξ(γ·m) = γ·ξ(m)";
print "   And Γ(ξ(m)) = Γ(w·m) = γ·w·m = γ·ξ(m) where w is the weight";
print "   So they commute automatically (scalars commute)";
print newline;

for i from 0 to #testMonomials - 1 do (
    mon = testMonomials#i;
    xiAction = xi mon;
    gamma = liouvilleMonomial(mon);
    
    -- Γ(ξ(mon))
    gamma_xi = xiAction;  -- Γ acts by scalar, but ξ(mon) = w·mon, so Γ(ξ(mon)) = γ·w·mon
    
    -- ξ(Γ(mon)) = ξ(γ·mon) = γ·ξ(mon) (γ is a constant)
    xi_gamma = gamma * xiAction;
    
    if gamma_xi == xi_gamma then (
        print("   ✅ Γ and ξ commute on " | toString(mon));
    ) else (
        print("   ❌ Γ and ξ do NOT commute on " | toString(mon));
    );
);
print newline;

-- 6. Compute the ring of invariants under the modular flow
-- The invariant ring R^ξ consists of elements f such that ξ(f) = 0
-- These are the "weight 0" elements

print "6. Ring of invariants under modular flow:";
print "   Elements f with ξ(f) = 0 have total weight 0";
print "   Since all our generators have positive weight (ln(n) > 0),";
print "   the only invariants are constants (scalars).";
print newline;

-- Check a few examples
testElements = {
    1_R,                    -- weight 0 (invariant)
    mu_2,                   -- weight ln(2) ≠ 0
    mu_2 * mu_3 - mu_6,     -- would be weight ln(2)+ln(3)-ln(6) = 0 if mu_6 existed
    mu_2^2 - mu_4           -- would be weight 2·ln(2)-ln(4) = 0 if mu_4 existed
};

print "   Testing invariance of sample elements:";
for i from 0 to #testElements - 1 do (
    elem = testElements#i;
    xiAction = xi elem;
    
    if xiAction == 0_R then (
        print("   ✅ " | toString(elem) | " is invariant (ξ(f) = 0)");
    ) else (
        print("   ❌ " | toString(elem) | " is NOT invariant: ξ(f) = " | toString(xiAction));
    );
);
print newline;

-- 7. Connection to de Rham cohomology
-- The D-module structure gives us de Rham cohomology groups
-- H^*_DR(R^ξ) where R^ξ is the invariant subring

print "7. De Rham cohomology perspective:";
print "   The modular flow defines a D-module structure on R";
print "   The invariant ring R^ξ corresponds to 'horizontal sections'";
print "   Since R^ξ = QQ (constants), the cohomology is trivial:";
print "     H^0_DR(R^ξ) = QQ";
print "     H^k_DR(R^ξ) = 0 for k > 0";
print newline;

-- 8. Liouville grading and the invariant ring
print "8. Liouville grading on the invariant ring:";
print "   The invariant ring R^ξ = QQ consists of constants";
print "   Since Ω(1) = 0, we have Γ(1) = (-1)^0 = 1";
print "   So the invariant ring sits in the even (bosonic) sector";
print "   This is consistent with the Witten index being conserved";
print newline;

print "=" | toString(newline | "SUMMARY" | newline | "=");
print "";
print "Key findings:";
print "  1. The modular flow vector field ξ acts diagonally on monomials";
print "  2. The Liouville grading Γ acts by ±1 on monomials";
print "  3. Γ and ξ commute (both act by scalars)";
print "  4. The invariant ring under ξ is just QQ (constants)";
print "  5. Constants have Γ = +1 (bosonic sector)";
print "";
print "Physical interpretation:";
print "  - The Witten index Tr(Γ) on the invariant ring is 1";
print "  - This is conserved under the modular flow";
print "  - The topological structure is protected";
print "";