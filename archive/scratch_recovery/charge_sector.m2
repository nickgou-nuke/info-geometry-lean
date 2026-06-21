loadPackage "Dmodules";

-- Instantiate our Weyl algebra sandbox
W = QQ[x_1..x_3, D_1..D_3, WeylAlgebra => {x_1 => D_1, x_2 => D_2, x_3 => D_3}];

-- Function to generate the module representation of a Charge Sector 'q'
getChargeSectorVacuum = (q) -> (
    -- Shift the annihilation criteria linearly based on the charge weight
    return ideal(D_1 - q, D_2 - q, D_3 - q);
);

-- Generate the vacuum for charge sector q = 1
charge1VacuumIdeal = getChargeSectorVacuum(1);
vacuumStateQ1 = W / charge1VacuumIdeal;

-- An active highest-weight state calculation can now check for holonomic constraints
-- We use print to output the holonomic rank
<< "Holonomic Rank of shifted sector: " << holonomicRank(vacuumStateQ1) << endl;

exit 0;
