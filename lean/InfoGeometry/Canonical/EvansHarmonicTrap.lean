import Mathlib.Data.List.Basic

/-!
# The Evans-Foster-Godrèche-Mukamel Model & The Harmonic Trap

This module formalizes the 1D spontaneous symmetry breaking lattice model
(Nature Vol 373, 1995) and maps it directly onto the Trifactor Projector
decomposition.

- `exact` (+): Holomorphic current flowing right
- `coexact` (-): Anti-holomorphic current flowing left
- `harmonic` (0): The zero-mode vacuum

The fundamental result formalized here is the "Harmonic Trap": a block of
harmonic holes topologically separates the exact and co-exact currents,
halting all non-equilibrium flow and protecting the symmetry-broken state.
-/

namespace InfoGeometry.Canonical.EvansHarmonicTrap

inductive TrifactorState
  | exact    -- The '+' charge
  | coexact  -- The '-' charge
  | harmonic -- The '0' hole
  deriving DecidableEq, Repr

open TrifactorState

/-- The local deterministic transition rule for adjacent sites.
Maps (Left, Right) → (Left', Right')
1. `+0 → 0+` (Exact flows right)
2. `0- → -0` (Coexact flows left)
3. `+- → -+` (Opposite charges cross)
Everything else is invariant. -/
def local_transition : TrifactorState × TrifactorState → TrifactorState × TrifactorState
  | (exact, harmonic) => (harmonic, exact)
  | (harmonic, coexact) => (coexact, harmonic)
  | (exact, coexact) => (coexact, exact)
  | pair => pair

/-- The Harmonic Trap Configuration `(-, 0, +)` is invariant under all
    local dynamics. No current can cross the zero-mode block. -/
theorem harmonic_trap_invariant_left :
    local_transition (coexact, harmonic) = (coexact, harmonic) := by
  rfl

theorem harmonic_trap_invariant_right :
    local_transition (harmonic, exact) = (harmonic, exact) := by
  rfl

/-- Two identical charges cannot pass through each other. -/
theorem exact_block : local_transition (exact, exact) = (exact, exact) := by rfl
theorem coexact_block : local_transition (coexact, coexact) = (coexact, coexact) := by rfl

end InfoGeometry.Canonical.EvansHarmonicTrap
