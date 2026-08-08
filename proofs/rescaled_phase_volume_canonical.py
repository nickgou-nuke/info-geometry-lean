#!/usr/bin/env python3
"""Audit witnesses for RescaledPhaseVolumeCanonical.lean."""

import sympy as sp

sx, spm, raw, I_fisher, beta, dmu, Q, theta, E, mu = sp.symbols(
    "sx sp raw I_fisher beta dmu Q theta E mu", nonzero=True
)
i = sp.I

kappa = 1 / I_fisher
# Calibration: sx*sp*raw = i*kappa.
calibrated = i * kappa
assert sp.simplify(calibrated - i / I_fisher) == 0

# Grand-canonical/Bogoliubov log clock and chemical-potential shift.
rho = -beta * (E - mu * Q)
log_clock = theta + rho
rho_shift = -beta * (E - (mu + dmu) * Q)
log_clock_shift = theta + rho_shift
assert sp.expand(log_clock_shift - (log_clock + beta * dmu * Q)) == 0

# q-level phase-action gauge shift.
q = sp.exp(log_clock)
q_shift = sp.exp(log_clock_shift)
assert sp.simplify(q_shift - sp.exp(beta * dmu * Q) * q) == 0

# Finite Weyl cell still has [X,P]=2XP rather than scalar identity.
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
X = sigma3
P = sigma1
comm = X * P - P * X
assert comm == 2 * X * P
assert sp.trace(comm) == 0
assert sp.trace(i * sp.eye(2)) == 2 * i

print("rescaled_phase_volume_canonical.py: all witnesses passed")
