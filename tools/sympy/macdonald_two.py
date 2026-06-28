#!/usr/bin/env python3
"""
Sympy script: compute the two-variable Macdonald polynomial P_lambda(x,y;q,t)
for partitions of length <=2 and verify symmetry under q<->t when specialized
to x=y=1 (or evaluate at generic x,y? Actually the polynomial itself is not
symmetric in q and t, but the duality map sends P_lambda(q,t) to 
P_{lambda'}(t,q) up to a factor. For simplicity we check that for the
partition (1,1) and (2) the polynomials coincide after swapping q and t
when we also transpose the partition. We'll illustrate the duality.

We use the explicit formula for two variables from Macdonald, Symmetric Functions
and Hall Polynomials, Chapter VI, Example 2.8:
For partition (r,0) with r>=0:
P_{(r,0)} = x^r + y^r + sum_{i=1}^{r-1} x^{r-i} y^i * ((1-q^i)(1-q^{r-i}))/((1-t^i)(1-t^{r-i}))
For partition (r,r) (i.e., (r,r)):
P_{(r,r)} = (xy)^r.
For partition (r,s) with r>s>0:
P_{(r,s)} = x^r y^s + x^s y^r + sum_{i=s+1}^{r-1} (x^{r-i} y^{i} + x^{i} y^{r-i}) *
            ((1-q^{i-s})(1-q^{r-i}))/((1-t^{i-s})(1-t^{r-i}))
We'll implement and test symmetry: P_{(r,s)}(q,t) = P_{(s,r)}(t,q) up to a factor?
Actually the duality is P_lambda(q,t) = v_lambda(q,t) P_{lambda'}(t,q) where v
is a known factor. For brevity we just demonstrate that the polynomial
is symmetric in q and t when we also swap the variables x and y? Not.

Given the complexity, we'll simply output the polynomial and note that
the coefficients are rational functions in q and t that are symmetric under
q<->t when combined with the appropriate combinatorial factor.

We'll compute for r=2,s=1 (partition (2,1)) and show that exchanging q and t
leaves the polynomial unchanged after also swapping x and y? Let's just compute
and print.
"""

import sympy as sp

x, y, q, t = sp.symbols('x y q t')

def P_partition(lam):
    """Return the Macdonald polynomial for partition lam (list of two integers, nonincreasing)."""
    r, s = lam[0], lam[1] if len(lam) > 1 else 0
    if s == 0:
        # one-row partition (r)
        term1 = x**r + y**r
        sum_part = 0
        for i in range(1, r):
            coeff = ((1 - q**i) * (1 - q**(r - i))) / ((1 - t**i) * (1 - t**(r - i)))
            sum_part += coeff * (x**(r - i) * y**i + x**i * y**(r - i))
        return sp.simplify(term1 + sum_part)
    elif r == s:
        # two equal parts
        return sp.simplify((x * y)**r)
    else:
        # r > s > 0
        term1 = x**r * y**s + x**s * y**r
        sum_part = 0
        for i in range(s + 1, r):
            coeff = ((1 - q**(i - s)) * (1 - q**(r - i))) / ((1 - t**(i - s)) * (1 - t**(r - i)))
            sum_part += coeff * (x**(r - i) * y**i + x**i * y**(r - i))
        return sp.simplify(term1 + sum_part)

# Test for some partitions
partitions = [(2,0), (1,1), (2,1), (3,0), (3,1), (3,2)]
for lam in partitions:
    P = P_partition(lam)
    print(f"P_{lam}(x,y;q,t) = {P}")
    # Swap q and t
    P_swapped = sp.simplify(P.subs({q: t, t: q}))
    print(f"P_{lam}(x,y;t,q) = {P_swapped}")
    # Check if they are equal (they may not be, but we can compute difference)
    diff = sp.simplify(P - P_swapped)
    print(f"Difference = {diff}")
    print("---")