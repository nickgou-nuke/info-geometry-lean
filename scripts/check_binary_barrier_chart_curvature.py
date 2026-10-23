"""Exact polynomial cross-check for the existing scalar binary chart.

Carrier: real interval coordinate p = trajectory 1 0 ξ in (0,1).
Inputs copied from BinaryBarrierCoordinateHessian's derivative theorems:
F'' = 8p(1-p), F''' = 16p(1-p)(1-2p). No basis change is performed.
This checks algebra only, not the analytic derivative or Lean theorem.
"""
import sympy as s

p = s.symbols("p", real=True)
second = 8 * p * (1 - p)
third = 16 * p * (1 - p) * (1 - 2 * p)
factor = 256 * p**2 * (1 - p)**2 * (12 * p * (1 - p) - 1)
assert s.expand(4 * second**3 - third**2 - factor) == 0
assert s.expand(third - 2 * second * (1 - 2 * p)) == 0
print("round_trip_verified: true; owner derivative readouts and factorization agree")
