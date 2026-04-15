# Bounded Commuting Log-Linearization Lane

## Purpose

This chapter closes Chunk B in a strict finite form:

- keep `Δ` as owner,
- expose `log(AB)=log A + log B` only under explicit bounded positivity assumptions,
- avoid any implicit promotion to unbounded/type-III claims.

## New Lean Owner Surface

- [RelativeModularBoundedCommutingInterface.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularBoundedCommutingInterface.lean)

Main theorems:

- `relativeModularOperator_diag_pos`
- `log_mul_diag_of_diag_positive`
- `log_mul_relativeModularOperator_diag`
- `log_mul_relativeModularOperator_diag_of_commute`
- `relativeModularOperator_commuting_witness`

## Canonical Reading

This lane is a bounded finite interface above:

- [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean)
- [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean)
- [RelativeModularCommutingLift.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularCommutingLift.lean)

It does not assert:

- unbounded `log Δ` domain calculus,
- crossed-product/Haagerup core construction,
- full Pedersen–Takesaki/Vaes owner theorem stack.

## Build Targets

```bash
lake build InfoGeometry.Canonical.RelativeModularBoundedCommutingInterface
lake build InfoGeometry.Canonical.All
```

## Method Rule

If commutation or positivity hypotheses are missing, do not apply additive `log` laws.
