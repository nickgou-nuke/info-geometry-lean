loadPackage "NCAlgebra";

-- 1. Ingest the generated energy weights (Logarithmic spectrum for 2^depth)
-- These can be piped dynamically from your Python tree script
energySpectrum = {0.6931, 1.3863, 2.0794, 2.7726, 3.4657, 4.1589};

-- 2. Boundary Sweep Predicate
-- Computes the state sum at a given inverse temperature beta
checkConvergenceAtBeta = (energies, beta) -> (
    stateSum := 0.0;
    scan(energies, E -> (
        stateSum = stateSum + exp(-beta * E);
    ));
    return stateSum;
);

-- 3. Automated Sweep Loop
-- Sweeping beta from low to high temperature to locate critical behavior
betaVals = {0.5, 0.8, 1.0, 1.2, 1.5};
print "--- Bost-Connes Partition Function Sweep ---";
scan(betaVals, b -> (
    zVal := checkConvergenceAtBeta(energySpectrum, b);
    print ("Beta: " | toString(b) | " -> Z(Beta) = " | toString(zVal));
));

-- 4. Schatten p-norm Divergence Boundary
checkSchattenDivergence = (energies, p_norm) -> (
    schattenSum := 0.0;
    scan(energies, E -> (
        schattenSum = schattenSum + (1.0 / (E^p_norm));
    ));
    return schattenSum;
);

print "--- Schatten p-norm Divergence ---";
print("p=1.0 bound: " | toString(checkSchattenDivergence(energySpectrum, 1.0)));

exit 0;
