# Experimental Gate Specs: Non-Hermitian Waveguide Braid/Clifford Prototype

Status: engineering-level proposal / numerical specification, not a fabrication-certified recipe.

## 1. Minimal physical platform

Use three coupled non-Hermitian waveguides along propagation coordinate `z`.  The propagation coordinate plays the role of effective time.  A two-waveguide subsystem models one local Clifford braid gate.

Balanced two-mode Hamiltonian:

```text
H = [[β0 + i Δγ/2, κ],
     [κ,  β0 - i Δγ/2]]
```

where:

- `β0` is a common propagation offset,
- `κ` is evanescent coupling,
- `Δγ = γ1 - γ2` is gain/loss contrast.

The exceptional point condition is:

```text
κ² - (Δγ / 2)² = 0
```

In the physical quadrant `κ ≥ 0`, `Δγ ≥ 0` this is:

```text
κ = Δγ / 2
```

This condition is formalized in `WaveguideEPBraidSpec.lean`.

## 2. Suggested normalized parameter window

For a dimensionless or mm-scale photonic/acoustic simulator:

```text
β0      = 10.0 mm⁻¹    # arbitrary common phase offset
κ       = 0.20 mm⁻¹    # adjacent coupling
Δγ_EP   = 0.40 mm⁻¹    # gain/loss contrast at EP
loop r  = 0.05 mm⁻¹    # EP encircling radius
L_gate  = 10–50 mm     # adiabatic propagation length, platform-dependent
```

These values are intentionally normalized.  A fabrication team should rescale them to the actual platform dispersion, waveguide separation, and loss/gain mechanism.

## 3. EP encircling protocol

A loop around the EP can be parameterized by:

```text
δβ(φ) = r cos φ
γ(φ)  = κ + r sin φ
φ     = 2π z / L_gate
```

with discriminant:

```text
D(φ) = κ² + (δβ(φ) + i γ(φ))²
```

The loop has winding number `±1` around `D = 0`, detecting the EP braid/monodromy.

## 4. Three-waveguide Artin test

Use two experimental sequences:

```text
Left:  G12 → G23 → G12
Right: G23 → G12 → G23
```

Measure output complex amplitudes and intensities at the end of the array.  In the ideal topological regime, length-only Witten/gain budgets match because both words have length 3:

```text
W(left) = g³ = W(right)
```

This is the experimental analogue of `artin_protocol_gain_budget_equal` and `braid_clifford_integration_synthesis`.

## 5. Repository artifacts

Lean theorem specification:

- `WaveguideEPBraidSpec.lean`

Numerical witness:

- `waveguide_ep_braid_spec.py`

Existing braid/Clifford formal layer:

- `BraidCliffordIntegration.lean`
- `braid_clifford_integration_sympy.py`

## 6. Caveats

- Exact equality of output fields is an ideal topological statement. Real devices need tolerance bands and calibration.
- Non-Hermitian EP encircling can be dynamically chiral/non-adiabatic; the loop direction and speed matter experimentally.
- The current Lean formalization proves the invariant skeleton and EP condition, not a full Maxwell/FEM fabrication model.
