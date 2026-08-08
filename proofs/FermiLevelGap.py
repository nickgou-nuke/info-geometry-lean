import sympy as sp


beta, E, mu, Delta = sp.symbols("beta E mu Delta", real=True)

shifted_fermi_level = E - mu
fermion_fugacity = sp.exp(-beta * shifted_fermi_level)
fermi_level_partition = 1 + fermion_fugacity

assert sp.simplify(shifted_fermi_level.subs(E, mu)) == 0
assert sp.simplify(fermion_fugacity.subs(E, mu) - 1) == 0
assert sp.simplify(fermi_level_partition.subs(E, mu) - 2) == 0

quasiparticle_energy_sq = shifted_fermi_level**2 + Delta**2
assert sp.simplify(quasiparticle_energy_sq.subs(E, mu) - Delta**2) == 0
assert sp.simplify(quasiparticle_energy_sq.subs({E: mu, Delta: 0})) == 0

x = sp.symbols("x")
fermion_factor = 1 + x
assert sp.simplify(fermion_factor.subs(x, fermion_fugacity) - fermi_level_partition) == 0

gapless_dispersion_sq = shifted_fermi_level**2
gapped_dispersion_sq = shifted_fermi_level**2 + Delta**2
assert sp.simplify(gapped_dispersion_sq - gapless_dispersion_sq - Delta**2) == 0

print("FermiLevelGap.py: Fermi level, chemical potential, and gap identities verified")
