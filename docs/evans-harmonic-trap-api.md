# Evans Harmonic Trap API

> Status: `live API overview`
> Audited: 2026-06-10
> Owner module: `lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean`
> Boundary: finite three-symbol local transition table only.

This module formalizes a finite Evans-style driven lattice rule table over
three labels:

- `LatticeCharge.exact`
- `LatticeCharge.coexact`
- `LatticeCharge.harmonic`

The labels are connected to the finite Hodge/trifactor dictionary through
`toHodgeSector`.

## Local Transition Rules

```lean
def local_transition :
    LatticeCharge × LatticeCharge → LatticeCharge × LatticeCharge

theorem exact_harmonic_moves_right :
    local_transition (LatticeCharge.exact, LatticeCharge.harmonic) =
      (LatticeCharge.harmonic, LatticeCharge.exact)

theorem harmonic_coexact_moves_left :
    local_transition (LatticeCharge.harmonic, LatticeCharge.coexact) =
      (LatticeCharge.coexact, LatticeCharge.harmonic)

theorem exact_coexact_swap :
    local_transition (LatticeCharge.exact, LatticeCharge.coexact) =
      (LatticeCharge.coexact, LatticeCharge.exact)
```

## Harmonic Trap

```lean
theorem harmonic_trap_invariant_left :
    local_transition (LatticeCharge.coexact, LatticeCharge.harmonic) =
      (LatticeCharge.coexact, LatticeCharge.harmonic)

theorem harmonic_trap_invariant_right :
    local_transition (LatticeCharge.harmonic, LatticeCharge.exact) =
      (LatticeCharge.harmonic, LatticeCharge.exact)

def harmonicTrap : LatticeTriple

theorem harmonic_trap_pairwise_invariant :
    updateLeft harmonicTrap = harmonicTrap ∧
      updateRight harmonicTrap = harmonicTrap
```

The finite window `(coexact, harmonic, exact)` is fixed under updates on either
adjacent pair.

## Companion Witness

```bash
python3 tools/sympy/evans_lattice_model.py
```

## Explicit Non-Claims

This API does not claim:

- a thermodynamic limit;
- a full Evans-Foster-Godreche-Mukamel statistical-mechanics theorem;
- KMS/BEC dynamics;
- a CFT or noncommutative-geometric identification;
- zeta-zero or Riemann-hypothesis consequences.
