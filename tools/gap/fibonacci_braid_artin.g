# Finite Artin presentation smoke test for the two-generator Fibonacci braid lane.
#
# This checks only the abstract B3 Artin relation and the Coxeter quotient
# obtained by imposing sigma_i^2 = 1.  It does not determine the Fibonacci
# braid image or identify a laboratory model.

Print("=== FINITE FIBONACCI B3 ARTIN QUOTIENT WITNESS ===\n");

RequireTrue := function(name, cond)
    if not cond then
        Error(Concatenation("validation failed: ", name));
    fi;
    Print("[OK] ", name, "\n");
end;

F := FreeGroup("sigma1", "sigma2");
sigma1 := F.1;
sigma2 := F.2;

B3 := F / [ sigma1 * sigma2 * sigma1 * (sigma2 * sigma1 * sigma2)^-1 ];
Print("[INFO] B3 presentation built from sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2\n");

Q := F / [
    sigma1 * sigma2 * sigma1 * (sigma2 * sigma1 * sigma2)^-1,
    sigma1^2,
    sigma2^2
];

Print("[INFO] B3 Coxeter quotient order: ", Size(Q), "\n");
RequireTrue("B3/<sigma_i^2> has order 6", Size(Q) = 6);
RequireTrue("B3 Coxeter quotient is symmetric group S3", IsomorphismGroups(Q, SymmetricGroup(3)) <> fail);

qgens := GeneratorsOfGroup(Q);
RequireTrue("quotient sigma1 involutive", qgens[1]^2 = One(Q));
RequireTrue("quotient sigma2 involutive", qgens[2]^2 = One(Q));
RequireTrue("quotient Artin relation", qgens[1] * qgens[2] * qgens[1] = qgens[2] * qgens[1] * qgens[2]);

Print("FIBONACCI_BRAID_B3_ARTIN_QUOTIENT_OK\n");
QUIT;
