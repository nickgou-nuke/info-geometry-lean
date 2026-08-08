import sympy as sp


beta, E, E1, E2, mu, Delta = sp.symbols("beta E E1 E2 mu Delta", real=True)
x = sp.symbols("x")


def shifted_energy(energy, chemical_potential):
    return energy - chemical_potential


def fugacity(inv_temp, energy, chemical_potential):
    return sp.exp(-inv_temp * shifted_energy(energy, chemical_potential))


def fermion_local_partition(inv_temp, energy, chemical_potential):
    return 1 + fugacity(inv_temp, energy, chemical_potential)


def gapped_energy(energy, chemical_potential, gap):
    return sp.sqrt(shifted_energy(energy, chemical_potential) ** 2 + gap**2)


def gapped_fugacity(inv_temp, energy, chemical_potential, gap):
    return sp.exp(-inv_temp * gapped_energy(energy, chemical_potential, gap))


def gapped_fermion_partition(inv_temp, energy, chemical_potential, gap):
    return 1 + gapped_fugacity(inv_temp, energy, chemical_potential, gap)


assert sp.simplify(shifted_energy(mu, mu)) == 0
assert sp.simplify(fugacity(beta, mu, mu) - 1) == 0
assert sp.simplify(fermion_local_partition(beta, mu, mu) - 2) == 0

assert sp.simplify(gapped_energy(mu, mu, Delta) ** 2 - Delta**2) == 0
assert sp.simplify(gapped_energy(mu, mu, 0)) == 0
assert sp.simplify(gapped_fugacity(beta, mu, mu, 0) - 1) == 0
assert sp.simplify(gapped_fermion_partition(beta, mu, mu, 0) - 2) == 0
assert sp.simplify(
    gapped_energy(E, mu, Delta) ** 2 - shifted_energy(E, mu) ** 2 - Delta**2
) == 0

two_fermion = fermion_local_partition(beta, E1, mu) * fermion_local_partition(beta, E2, mu)
two_fermion_expanded = (
    1
    + fugacity(beta, E1, mu)
    + fugacity(beta, E2, mu)
    + fugacity(beta, E1, mu) * fugacity(beta, E2, mu)
)
assert sp.simplify(two_fermion - two_fermion_expanded) == 0

for cutoff in range(0, 8):
    boson_truncated = sum(x**k for k in range(cutoff + 1))
    if cutoff == 0:
        assert boson_truncated == 1
    if cutoff > 0:
        previous = sum(x**k for k in range(cutoff))
        assert sp.simplify(boson_truncated - previous - x**cutoff) == 0

    geometric = (1 - x ** (cutoff + 1)) / (1 - x)
    assert sp.factor((boson_truncated - geometric) * (1 - x)) == 0

boson_geometric = 1 / (1 - x)
assert sp.simplify((1 - x) * boson_geometric - 1) == 0

gapped_x = gapped_fugacity(beta, E, mu, Delta)
gapped_fermion = 1 + gapped_x
gapped_boson_geometric = 1 / (1 - gapped_x)
assert sp.simplify(gapped_fermion - gapped_fermion_partition(beta, E, mu, Delta)) == 0
assert sp.simplify((1 - gapped_x) * gapped_boson_geometric - 1) == 0

print("GrandCanonicalPrimon.py: bosonic and fermionic grand-canonical identities verified")
