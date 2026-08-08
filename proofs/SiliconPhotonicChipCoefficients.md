# Silicon Photonic Chip Coefficients

Status: normalized coupled-mode specification, not a foundry PDK.

For the hyperbolic non-Hermitian braid-gate block:

```text
S(α) = [[cosh α, sinh α],
        [sinh α, cosh α]]
```

use:

```text
α = κ L
```

where `κ` is the effective coupling coefficient and `L` is the interaction length.

## Amplitude coefficients

```text
t(α) = cosh α
r(α) = sinh α
```

## Intensity coefficients

```text
T = |t|² = cosh² α
R = |r|² = sinh² α
```

The ordinary Euclidean intensity budget is not unitary:

```text
T + R - 1 = 2 sinh² α
```

but the Krein/SU(1,1) flux is exactly preserved:

```text
T - R = 1
```

## Balanced EP condition

For the two-waveguide non-Hermitian coupler:

```text
Δγ_EP = 2κ
```

so in the physical quadrant:

```text
κ = Δγ_EP / 2
```

## Example normalized parameter windows

```text
κ = 0.05 mm⁻¹, L = 2.0 mm  -> α = 0.10  weak gate
κ = 0.10 mm⁻¹, L = 3.0 mm  -> α = 0.30  moderate gate
κ = 0.20 mm⁻¹, L = 2.5 mm  -> α = 0.50  strong gate
```

Repository checks:

- `SiliconPhotonicChipCoefficients.lean`
- `silicon_photonic_chip_coefficients.py`
