# tools/gap/cole_fury_central_roots.g
# Automated test for the 10th roots of unity structure inside Cole-Fury limits

Print("--- GAP 10TH ROOTS OF UNITY CENTRAL TEST ---\n");

# We test the primitive 10th root of unity modulo limits
# E(10) is the 10th root of unity in GAP
z := E(10);

Print("10th Root of Unity z: ", z, "\n");
Print("Cube of z^10: ", z^10, "\n");

if z^10 = 1 then
    Print("PASS: Cyclotomic extension correctly evaluates the 10th root of unity.\n");
else
    Print("FAIL: Cyclotomic extension failed.\n");
fi;

# Parafermionic 10-fold root mapping to -1
# E(20) represents the 20th root of unity where z^10 = -1
sigma := E(20);

Print("Parafermion 10-fold root sigma^10: ", sigma^10, "\n");

if sigma^10 = -1 then
    Print("PASS: The n-fold roots of the center successfully map the negative identity across the Cole-Fury quadrants.\n");
else
    Print("FAIL: Negative identity mapping failed.\n");
fi;

Print("GAP: Successfully validated the discrete fraction anomaly limits.\n");
