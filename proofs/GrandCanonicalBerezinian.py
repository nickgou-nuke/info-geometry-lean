import sympy as sp


beta, E, mu, Delta = sp.symbols("beta E mu Delta", real=True)

shifted = E - mu
gapped_energy = sp.sqrt(shifted**2 + Delta**2)
fugacity = sp.exp(-beta * gapped_energy)

fermion_odd_block = 1 + fugacity
boson_even_denominator = 1 - fugacity


def diagonal_berezinian(even, odd):
    return even / odd


super_berezinian = diagonal_berezinian(fermion_odd_block, boson_even_denominator)
gapped_fermion_factor = fermion_odd_block
gapped_boson_factor = 1 / boson_even_denominator

assert sp.simplify(gapped_energy.subs(E, mu) ** 2 - Delta**2) == 0
assert sp.simplify(fugacity.subs({E: mu, Delta: 0}) - 1) == 0

assert sp.simplify(
    super_berezinian - (1 + fugacity) / (1 - fugacity)
) == 0
assert sp.simplify(
    super_berezinian - gapped_fermion_factor * gapped_boson_factor
) == 0
assert sp.simplify(
    boson_even_denominator * super_berezinian - fermion_odd_block
) == 0

x = sp.symbols("x")
assert sp.simplify(
    diagonal_berezinian(1 + x, 1 - x) - (1 + x) / (1 - x)
) == 0

print("GrandCanonicalBerezinian.py: gapped super Berezinian identities verified")
