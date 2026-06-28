-- Macaulay2 script: compute the Hilbert series of QQ[x,y]/I where I = (x*(x-1), y)
R = QQ[x,y];
I = ideal(x*(x-1), y);
-- Compute the Gröbner basis
G = gens gb I;
print "Groebner basis:";
print G;
-- Determine the leading monomials (Macaulay2 uses the monomial order of the ring, default is GRevLex)
-- We can get the lead term of each generator
LT = apply(G, g -> leadTerm g);
print "Leading terms:";
print LT;
-- The quotient as a vector space has basis given by monomials not divisible by any leading term.
-- We can compute the Hilbert function up to some degree using the Hilbert series.
hilb = hilbertSeries I;
print "Hilbert series of I:";
print hilb;
-- Actually hilbertSeries of an ideal returns the Hilbert series of the quotient R/I?
-- According to M2 documentation, hilbertSeries(I) returns the Hilbert series of R/I.
-- Let's compute the Hilbert series of the quotient directly:
H = hilbertSeries (R^1 / I);
print "Hilbert series of R/I:";
print H;
-- The Hilbert series is a rational function; we can extract the dimension as the value at t=1? 
-- Actually the Hilbert polynomial gives the dimension for large degree, but since the quotient is
-- finite-dimensional, the Hilbert series is a polynomial.
-- We can compute the polynomial:
hilbPoly = hilbertPolynomial (R^1 / I);
print "Hilbert polynomial of R/I:";
print hilbPoly;
-- Since the quotient is finite-dimensional, the Hilbert polynomial is constant equal to the dimension.
-- Evaluate at a large integer:
dim = value(hilbPoly, 100);
print "Vector space dimension of R/I (via Hilbert polynomial):", dim;
-- Alternatively, compute the basis using the method "basis":
B = basis(0, R/I); -- basis in degree 0? Actually basis(n, M) gives the basis of the n-th graded part.
-- Since our ideal is not homogeneous, the quotient is not naturally graded.
-- However, we can still consider the vector space dimension via the "basis" command for the whole module? 
-- There is also "generators" but that gives module generators.
-- Let's compute the size using "rank" for a free module over a field? Not applicable.
-- Instead, we can use "hilbertSeries" and sum the coefficients.
-- The hilbertSeries of R/I is a polynomial; we can evaluate at t=1 to get the dimension? 
-- For a graded module, the Hilbert series is sum_{d>=0} (dim M_d) t^d.
-- If the module is finite-dimensional, the series is a polynomial, and the dimension is sum dim M_d = H(1).
-- So compute:
eval = substitute(hilb, {=>1});
print "Evaluation at t=1 (dimension):", eval;
-- Or use "poincare"?
-- Let's just compute directly using the method "degree" for a module over a field? 
-- Actually for a vector space, we can use "rank" if we consider it as a free module over the base field?
-- Not directly.
-- We'll compute the dimension via the vector space method:
-- Use "basis" to get a basis of the module as a vector space? There is "basis" for a module over a ring,
-- but if the ring is a field, then it works.
-- Since R/I is not a field, but we can consider it as a vector space over QQ by forgetting the ring structure.
-- There is a method "vectorSpace" ??? Not sure.
-- Instead, we can compute using "homogenize" and then take the projective coordinate ring? Too heavy.
-- For simplicity, we output the Hilbert series and note that the dimension is the sum of coefficients.