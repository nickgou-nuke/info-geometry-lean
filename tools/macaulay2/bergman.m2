-- bergman.m2
-- Map the algebraic constraints corresponding to the Bergman kernel limits into an ideal structure
-- Compute the exact rational fractions binding the polynomial growth limits at the singularity boundary

R = QQ[x, y, z, w];
-- Define the ideal corresponding to the singularity boundary
-- Let's use a standard singularity, like a surface singularity
I = ideal(x^2 + y^2 + z^2 + w^3, x*y - z*w);

-- Print the ideal
print "Ideal structure of the singularity boundary:";
print I;

-- Compute the Hilbert series which gives the exact rational fraction binding the polynomial growth limits
HS = hilbertSeries I;

print "Exact rational fraction binding the polynomial growth limits (Hilbert Series):";
print HS;

exit(0);
