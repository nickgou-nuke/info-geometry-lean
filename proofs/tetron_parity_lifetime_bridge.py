#!/usr/bin/env python3
"""Numerical bridge for InAs--Pb tetron parity lifetime vs photonic parity transfer.

This is a calibration/analogy script.  It does not claim that a room-temperature
photonic chip stores fermionic parity for 20 seconds.  It compares:

1. Arrhenius suppression of parity switching in a superconducting tetron:
      tau = tau0 * exp(Delta / kBT)
2. Propagation-time scale of an SOI photonic hyperbolic braid gate.
"""

from __future__ import annotations

import math

KB_UEV_PER_K = 86.17333262  # micro-eV / K
C = 299_792_458.0


def parity_lifetime(tau0: float, gap_uev: float, temp_k: float) -> float:
    theta = KB_UEV_PER_K * temp_k
    return tau0 * math.exp(gap_uev / theta)


def main() -> int:
    # Representative numbers from the discussion: Al-like gap ~30 μeV, Pb-like ~70 μeV.
    gap_al = 30.0
    gap_pb = 70.0
    temp_k = 0.020  # 20 mK dilution-fridge scale
    theta = KB_UEV_PER_K * temp_k
    measured_pb_tau = 20.0

    ratio = math.exp((gap_pb - gap_al) / theta)
    tau0 = measured_pb_tau / math.exp(gap_pb / theta)
    inferred_al_tau = parity_lifetime(tau0, gap_al, temp_k)

    print("Tetron parity lifetime bridge")
    print(f"T                     = {temp_k*1000:.1f} mK")
    print(f"kBT                   = {theta:.6f} μeV")
    print(f"Delta_Al              = {gap_al:.1f} μeV")
    print(f"Delta_Pb              = {gap_pb:.1f} μeV")
    print(f"Arrhenius ratio Pb/Al = {ratio:.3e}")
    print(f"calibrated tau0       = {tau0:.3e} s")
    print(f"if tau_Pb=20 s, inferred tau_Al ≈ {inferred_al_tau:.3e} s")

    # Photonic SOI parity-transfer time scale from the existing CMT/TMM spec.
    wavelength_nm = 1550.0
    length_um = 100.0
    n_group = 4.0
    v_group = C / n_group
    propagation_time = (length_um * 1e-6) / v_group
    alpha = 1.0
    kappa_im_cm_inv = alpha / (length_um * 1e-4)

    print("\nPhotonic SOI parity-transfer scale")
    print(f"lambda                = {wavelength_nm:.1f} nm")
    print(f"group index           = {n_group:.2f}")
    print(f"length                = {length_um:.1f} μm")
    print(f"propagation time      = {propagation_time:.3e} s")
    print(f"alpha                 = {alpha:.2f}")
    print(f"kappa_im              = {kappa_im_cm_inv:.3f} cm^-1")
    print("caveat                = photonic chip simulates parity transfer/contrast, not 20 s fermionic storage")

    if ratio <= 1 or propagation_time <= 0:
        raise SystemExit("FAIL lifetime bridge sanity check")
    print("\nOK tetron parity lifetime bridge witness completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
