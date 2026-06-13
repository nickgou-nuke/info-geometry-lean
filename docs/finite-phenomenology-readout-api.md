# Finite Phenomenology Readout API

Lean owner: `lean/InfoGeometry/Canonical/FinitePhenomenologyReadout.lean`

SymPy witness: `tools/sympy/finite_phenomenology_readout.py`

This module is a theorem-level dictionary from proposed physical labels to
finite algebraic readouts already proved elsewhere in the repository.

## Verified Readouts

| Label | Lean theorem | Finite content |
|---|---|---|
| Superlocalization | `superlocalization_null_projector_readout` | `T * P_zero T = 0` for `T ^ 3 = T` |
| Sector partition | `trifactor_sector_partition_readout` | `P_zero + P_plus + P_minus = 1` |
| Harmonic trap | `harmonic_trap_readout` | the finite triple `(-, 0, +)` is fixed by both adjacent updates |
| Goldstino label | `goldstino_odd_density_readout` | `c - a` is odd under an explicit Tomita ladder swap |
| Bose/Fermi pairing label | `bose_fermi_pairing_even_readout` | `c + a` is even under an explicit Tomita ladder swap |
| Vortex-pinning label | `parity_odd_supertrace_cancellation_readout` | parity-invariant states cancel parity-odd supertraces |
| Cuntz/CAR cancellation | `cuntz_car_supertrace_cancellation_readout` | the Cuntz-derived odd CAR generator has zero supertrace under an invariant state |
| Finite braid gate | `finite_braid_gate_readout` | the concrete `Z3` braid matrices satisfy the Artin/Yang-Baxter identity |

## Non-Claims

This API does not prove an optical-lattice experiment, wavefunction decay
estimate, Kibble-Zurek theorem, Josephson current spectrum, KMS phase
transition, C*-completion, zeta-zero theorem, or RH consequence.

Those remain separate theorem obligations requiring explicit analytic,
topological, or experimental premises.
