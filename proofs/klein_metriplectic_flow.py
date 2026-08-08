#!/usr/bin/env python3
"""Klein-bottle metriplectic flow and Painleve-like SBer stabilization witness.

No claim is made that this numerically solves Painleve III.  The script checks a
finite toy asymptotic: a collapsing bosonic determinant is regularized by a
fermionic/Super-Berezinian correction, and a glide-wrapped flow remains in the
Klein-bottle Brillouin-zone fundamental domain.
"""

import math
import numpy as np


def painleve_like_asymptotics(r, theta):
    lam_plus = math.exp(r) * math.cos(theta)
    lam_minus = math.exp(-r) * math.sin(theta)
    return lam_plus, lam_minus


def stabilized_sber(det_A, det_D, coupling, eps=1e-12):
    effective_boson = det_A + coupling / (det_D + eps)
    return effective_boson / (det_D + eps)


print("§1 Painleve-like Super-Berezinian stabilization")
thetas = np.linspace(0.0, 2.0 * math.pi, 500)
r_critical = 0.01
regulated = []
unregulated = []
for t in thetas:
    lp, lm = painleve_like_asymptotics(r_critical, float(t))
    det_A = lp * (math.sin(float(t)) ** 2)
    det_D = lm + 0.1
    sber = stabilized_sber(det_A, det_D, coupling=0.005)
    regulated.append(-math.log(abs(sber) + 1e-15))
    unregulated.append(-math.log(abs(det_A) + 1e-15))

max_reg = max(regulated)
max_unreg = max(unregulated)
print(f"max unregulated barrier: {max_unreg:.6f}")
print(f"max SBer-regulated barrier: {max_reg:.6f}")
assert math.isfinite(max_reg)
assert max_reg < max_unreg
print("SBer regularization remains finite and lowers the critical barrier ✓")


class KleinBottleMetriplecticFlow:
    def __init__(self, energy_scale=1.0, dissipation_scale=0.05):
        self.E0 = energy_scale
        self.gamma = dissipation_scale

    def wrap(self, kx, ky):
        while kx > 2 * math.pi:
            kx -= 2 * math.pi
            ky = -ky
        while kx < 0:
            kx += 2 * math.pi
            ky = -ky
        ky = (ky + math.pi) % (2 * math.pi) - math.pi
        return kx, ky

    def vector_field(self, kx, ky):
        sber_grad_x = -math.sin(kx) / (math.cos(kx) ** 2 + 0.1)
        sber_grad_y = -math.sin(ky) / (math.cos(ky) ** 2 + 0.1)
        dkx_dt = -math.sin(ky) - self.gamma * sber_grad_x
        dky_dt = math.sin(kx) - self.gamma * sber_grad_y
        return dkx_dt, dky_dt

    def simulate(self, kx0, ky0, steps=3000, dt=0.02):
        kx, ky = kx0, ky0
        flips = 0
        traj = []
        for _ in range(steps):
            dkx, dky = self.vector_field(kx, ky)
            old_kx = kx
            kx += dkx * dt
            ky += dky * dt
            if kx > 2 * math.pi or kx < 0:
                flips += 1
            kx, ky = self.wrap(kx, ky)
            traj.append((kx, ky))
            assert 0 <= kx <= 2 * math.pi + 1e-12
            assert -math.pi - 1e-12 <= ky <= math.pi + 1e-12
        return np.array(traj), flips


print("\n§2 Klein-bottle metriplectic flow")
flow = KleinBottleMetriplecticFlow()
traj, flips = flow.simulate(kx0=0.5, ky0=1.2)
print(f"final point: kx={traj[-1,0]:.6f}, ky={traj[-1,1]:.6f}")
print(f"glide boundary flips: {flips}")
assert traj.shape == (3000, 2)
print("trajectory stays inside the Klein fundamental domain with glide wrapping ✓")

print("\nklein_metriplectic_flow.py: All checks passed")
