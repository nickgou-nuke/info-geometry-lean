import sympy as sp

# Connes-Chern pairing is bilinear in classes; model as g ⟨*⟩-coefficient a.
a, b, g = sp.symbols("a b g", real=True)
zero_k0 = {g: 0}
pairing = a * g

print("General pairing ansatz: <[C], [e]> = a * g")
print("Proof-trivial K₀ hypothesis gives g = 0.")
print("Collapsed pairing value:", sp.simplify(pairing.subs(zero_k0)))

# Spectral-action toy profile S = S0 + c*|⟨[C],[e]⟩|^2
S0, c = sp.symbols("S0 c", real=True)
S = S0 + c * pairing**2
print("Spectral profile:", S)
print("Under the supplied zero K₀ hypothesis, S ->", sp.simplify(S.subs(zero_k0)))

# symbolic consistency checks for collapse
res = [sp.simplify(S.subs(zero_k0) - S0),
       sp.simplify(pairing.subs(zero_k0)),
       sp.solve([sp.Eq(g, 0)], [g], dict=True)]
print("Checks:", res)

# demonstrate positivity check
Sδ = S0 + c * (2 * g)**2
Sδ0 = S.subs({a: 2, g: 0})
print("Sample with a=2, collapsed:", sp.simplify(Sδ0))

print("Sanity: a supplied trivial K₀ carrier collapses Connes-Chern data; this is not a computation of K₀(O₂).")
