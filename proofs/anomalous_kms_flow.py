import sympy as sp

# -----------------------------------------------------------------------------
# Anomalous CPT flow witness equations
# -----------------------------------------------------------------------------

s = sp.symbols("s", real=True)
beta = s
A = sp.Function("A")
trK, tr_delta = sp.symbols("trK tr_delta", complex=True)

# 1) Modular anomaly deformation of the total partition:
#     Z_total(s) = exp(A(s))
Z_total = sp.exp(A(beta))
F = sp.simplify(-sp.log(Z_total) / beta)
U = sp.simplify(-(sp.diff(sp.log(Z_total), beta)))
S = sp.simplify(sp.log(Z_total) - beta * U)

print("=== Modular anomaly thermodynamics at finite beta ===")
print("Z_total =", Z_total)
print("F_total =", F)
print("U_total =", U)
print("S_total =", S)

# 2) Trace-identity level: J-symmetry gives
#    tr K = (1/2) tr(deltaK)
trace_eq = sp.Eq(trK, sp.Rational(1, 2) * tr_delta)
print("\nTrace relation from perturbed J-conjugation:")
print("  ", trace_eq)

# 3) Klein bottle V4 anomaly parity can enforce tr_delta = -tr_delta
#    => tr_delta = 0.
tr_delta_zero = sp.solve(sp.Eq(tr_delta, -tr_delta), tr_delta)
print("\nKlein-bottle Γ-even + Γ-odd anomaly gives:")
print("  tr(δK) ∈", tr_delta_zero)

# 4) If trace is faithful and tr(δK)=0 then δK = 0
print("\nIf Trace is faithful (injective), δK = 0 follows from tr(δK)=0.")

# 5) Linearized spectral leak model:
#    distance from critical line ~ |A(s)|.
leak = sp.Abs(A(beta))
print("\nSpectral-line leakage proxy:")
print("  ΔRe(s) ~", leak)

# 6) Critical line consistency check at A=0
F0 = sp.simplify(F.subs(A(beta), 0))
U0 = sp.simplify(U.subs(A(beta), 0))
S0 = sp.simplify(S.subs(A(beta), 0))
print("\nAt A=0 (anomaly-free):")
print("  F_total =", F0)
print("  U_total =", U0)
print("  S_total =", S0)
