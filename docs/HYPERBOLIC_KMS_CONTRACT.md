# Hyperbolic--Elliptic Chordal Duality, KMS Decoherence, and Bipartite Sandwich Contract

## Scope

This contract covers the kernel-checked declarations in:
- `lean/InfoGeometry/Core/HyperbolicPeirceRotor.lean`
- `lean/InfoGeometry/Canonical/HyperbolicEllipticKmsBridge.lean`
- `lean/InfoGeometry/Canonical/HyperbolicEllipticKmsBridgeAudit.lean`

## Verified Algebraic Claims

1. **Drazin vs. Reflexive Moore--Penrose Dichotomy (`nilpotent_commuting_inverse_forces_zero` & `carrierSupport_commuting_group_inverse`)**:
   - Any commuting generalized inverse (`d * x = x * d`, `d * x * d = d`) of a square-zero element (`d * d = 0`) forces `d = 0`.
   - Nonzero nilpotent seeds therefore require noncommuting reflexive partners (`d * b ≠ b * d`), while the active carrier `Delta = d * b + b * d` is strictly idempotent and is its own commuting group/Drazin inverse.
2. **Bipartite Directed Edge Transport (`bipartite_directed_edge_transport`)**:
   - `polePlus d b * d * poleMinus d b = d` and `poleMinus d b * b * polePlus d b = b`, with opposite-orientation products vanishing.
3. **Hyperbolic Squeeze Rotor (`hyperbolicRotor`, `hyperbolicRotorUnit`, `hyperbolic_projector_relations`)**:
   - On the scalar unit hyperbola `u * u - v * v = 1`, `hyperbolicRotor u v d b` has two-sided inverse `hyperbolicRotor u (-v) d b` and conjugates `polePlus d b` into the idempotent `hyperbolicPolePlus u v d b`.
4. **Opposite-Sign Chordal Squares & KMS Diagonal Decoherence (`elliptic_hyperbolic_kms_master_synthesis`)**:
   - Circular displacement square: `(movingPolePlus c s d b - polePlus d b)^2 = (s * s) • carrierSupport d b`.
   - Hyperbolic displacement square: `(hyperbolicPolePlus u v d b - polePlus d b)^2 = -((v * v) • carrierSupport d b)`.
   - Diagonal Peirce projection: `diagonalDecoherence d b (movingPolePlus c s d b) = kmsModularWeight s c d b`.
5. **Division-Free Two-State Transition Sandwich (`two_state_velocity_sandwich`)**:
   - `polePlus d b * transitionVelocity d b * movingPolePlus c s d b = (s * s) • d - (c * s) • polePlus d b`.
