#!/usr/bin/env python3
"""
SymPy witness for FibAnyonThm4: Braid relation R·B·R = B·R·B.
R = diag(e^{-4πi/5}, e^{3πi/5}), F = [[1/φ,1/√φ],[1/√φ,-1/φ]], B = F·R·F.
Reference: Turaev §XI.4, Kassel §VIII.1, Bakalov-Kirillov §3.2
"""
import numpy as np
φ = float((1 + np.sqrt(5))/2)
R1, Rτ = np.exp(-4j*np.pi/5), np.exp(3j*np.pi/5)
F = np.array([[1/φ, 1/np.sqrt(φ)], [1/np.sqrt(φ), -1/φ]], dtype=complex)
R = np.diag([R1, Rτ])
B = F @ R @ F
err = np.max(np.abs(R @ B @ R - B @ R @ B))
print(f"Braid relation R·B·R = B·R·B: {'✅' if err < 1e-10 else '❌'} (max error: {err:.2e})")
