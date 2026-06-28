/* GAP script: compute the Hilbert series of the quotient QQ[x,y]/I where I = (x*(x-1), y). */

LoadPackage("gbnp");;

R := PolynomialRing(Rationals, ["x","y"]);
x := IndeterminatesOfPolynomialRing(R)[1];
y := IndeterminatesOfPolynomialRing(R)[2];

I := Ideal(R, [x*(x-1), y]);;
G := GroebnerBasis(I);;
Print("Groebner basis: ");
Print(G); Print("\n");

/* Determine the leading monomials with respect to the default ordering (lex?).
   We need to know the monomial order. Let's force a degree lexicographic order. */
R := PolynomialRing(Rationals, 2, ["x","y"]);
x := IndeterminatesOfPolynomialRing(R)[1];
y := IndeterminatesOfPolynomialRing(R)[2];
I := Ideal(R, [x*(x-1), y]);
G := GroebnerBasis(I);
Print("Groebner basis (default order): ");
Print(G); Print("\n");

/* Use weighted degree lexicographic with x,y weight 1 each. */
SetMonomialOrder(R, "deglex");
x := IndeterminatesOfPolynomialRing(R)[1];
y := IndeterminatesOfPolynomialRing(R)[2];
I := Ideal(R, [x*(x-1), y]);
G := GroebnerBasis(I);
Print("Groebner basis (deglex): ");
Print(G); Print("\n");

/* The leading monomials are x^2 and y (since x*(x-1) leads to x^2 under deglex?).
   Let's extract them. */
LM := List(G, LeadingMonomial);
Print("Leading monomials: ");
Print(LM); Print("\n");

/* The monomials not divisible by any leading monomial form a basis of the quotient
   as a vector space. We can compute them up to a certain degree. */
maxdeg := 3;
monoms := [];
for d in [0..maxdeg] do
  for monom in Monomials(TermOrder("deglex"), d) do
    if not Or(LM, l -> IsDivisibleMonomial(monom, l)) then
      Add(monoms, monom);
    fi;
  od;
od;
Print("Monomials up to degree ", maxdeg, " not in LT(I): ");
Print(monoms); Print("\n");
Print("Number of such monomials: ", Length(monoms), "\n");

/* The Hilbert function HF(d) = number of monomials of degree d not in LT(I). */
for d in [0..maxdeg] do
  count := Number(monoms, m -> TotalDegree(MonomialCoefficients(m)) = d);
  Print("HF(", d, ") = ", count, "\n");
od;

/* The dimension of the quotient is the total number of such monomials (finite). */
Print("Vector space dimension of QQ[x,y]/I: ", Length(monoms), "\n");