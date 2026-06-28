-- wheeler_complexity.m2
-- Models the differential evolution of information/complexity using D-modules.
-- Inspired by Wheeler's "It from Bit" and the evolution of state complexity.

needsPackage "Dmodules"

<< "===========================================================" << endl
<< " Differential Evolution of Information/Complexity " << endl
<< "===========================================================" << endl

-- 1. Define the Weyl algebra over a polynomial ring (representing the state space)
-- x, y represent the spatial/state coordinates
-- dx, dy represent the momentum/differential operators
W = QQ[x, y, dx, dy, WeylAlgebra => {x => dx, y => dy}]

<< "State Space (Weyl Algebra W): " << W << endl
<< "-----------------------------------------------------------" << endl

-- 2. Define holonomic D-modules representing different stages of universe evolution

-- Stage A: The "Big Bang" / initial singularity
-- A state localized at the origin. Corresponds to the Dirac delta distribution.
-- Annihilated by position operators.
iBang = ideal(x, y)
<< "Stage A: Initial Singularity (Dirac Delta)" << endl
<< "  Generators: x, y" << endl

-- Stage B: Simple expanding universe
-- A uniform expansion state. Corresponds to the exponential function e^{x+y}.
-- Annihilated by (dx - 1) and (dy - 1).
iExp = ideal(dx - 1, dy - 1)
<< "Stage B: Simple Expansion (Exponential)" << endl
<< "  Generators: dx - 1, dy - 1" << endl

-- Stage C: Complex quantum evolution
-- A state undergoing acceleration/interference. Corresponds to Airy functions.
-- Annihilated by (dx^2 - x) and (dy^2 - y).
iAiry = ideal(dx^2 - x, dy^2 - y)
<< "Stage C: Complex Quantum Evolution (Airy)" << endl
<< "  Generators: dx^2 - x, dy^2 - y" << endl
<< "-----------------------------------------------------------" << endl

-- 3. Compute characteristic variety and holonomic rank to quantify complexity
-- The holonomic rank represents the dimension of the solution space at a generic point,
-- which can be interpreted as the local informational capacity or "degrees of freedom".

cBang = charIdeal iBang
rankBang = holonomicRank iBang

cExp = charIdeal iExp
rankExp = holonomicRank iExp

cAiry = charIdeal iAiry
rankAiry = holonomicRank iAiry

<< "--- Complexity Metrics ---" << endl << endl

<< "Stage A (Singularity):" << endl
<< "  Characteristic Ideal: " << cBang << endl
<< "  Holonomic Rank (Information Capacity): " << rankBang << endl << endl

<< "Stage B (Simple Expansion):" << endl
<< "  Characteristic Ideal: " << cExp << endl
<< "  Holonomic Rank (Information Capacity): " << rankExp << endl << endl

<< "Stage C (Complex Quantum Evolution):" << endl
<< "  Characteristic Ideal: " << cAiry << endl
<< "  Holonomic Rank (Information Capacity): " << rankAiry << endl << endl

<< "===========================================================" << endl
