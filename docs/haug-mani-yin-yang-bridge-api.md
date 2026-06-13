# Haug-Mani Yin-Yang Bridge API

Lean module:

- `lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean`

SymPy witness:

- `tools/sympy/haug_mani_yin_yang_bridge.py`

This module records the finite, theorem-backed real doubled representation
behind the Haug-Mani/Yin-Yang reading.  It uses the existing concrete
Tomita/Krein `2 x 2` matrix atom rather than adding a new number system.

## Theorem Surface

- `physicalSector_idempotent`
  proves the positive sector projector is idempotent.

- `ghostSector_idempotent`
  proves the negative sector projector is idempotent.

- `physical_ghost_orthogonal` and `ghost_physical_orthogonal`
  prove the two sectors are orthogonal.

- `physical_add_ghost`
  proves the two sectors sum to the identity.

- `mixedSector_conj_physical` and `mixedSector_conj_ghost`
  prove the sheet-mixing involution swaps the two projectors.

- `phaseAxis_eq_J_mul_eps`
  defines the real phase axis as `J * eps`.

- `phaseAxis_sq`
  proves the phase axis squares to `-1`.

- `mixedSector_conj_phaseAxis`
  proves sheet reflection flips the phase axis.

- `realDoubledScalar`
  embeds a pair of real coefficients as `a * I + b * K`.

- `realDoubledScalar_mul`
  proves the multiplication rule
  `(a + bK)(c + dK) = (ac - bd) + (ad + bc)K`.

- `mixedSector_conj_realDoubledScalar`
  proves sheet reflection is conjugation on the finite readback.

- `realDoubledScalar_injective`
  proves the two real coefficients are recovered injectively from the matrix.

- `haug_mani_real_doubled_capstone`
  bundles the finite sector split, phase-axis, and conjugation identities.

## Boundary

This is not a proof that imaginary numbers are unnecessary in physics, not a
new foundation for quantum mechanics, not a theorem about arithmetic
asymmetry, and not a Riemann Hypothesis consequence.  It proves only a finite
real `2 x 2` representation of complex scalar arithmetic inside the existing
Tomita/Krein matrix atom.
