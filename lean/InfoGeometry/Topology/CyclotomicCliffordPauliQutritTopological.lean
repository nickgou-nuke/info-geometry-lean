import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicCliffordPauliQutrit

/-!
# Topological qutrit Weyl readout

The canonical qutrit clock and shift matrices form the finite order-three
Weyl system.  This owner views the Weyl words as a map from the discrete
integer lattice of exponents and records its period-three descent.  It keeps
the associative matrix lane separate from the nonassociative Zorn carrier.
-/

namespace InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological

open InfoGeometry.Canonical

noncomputable section

/-- The Weyl-word readout on the discrete exponent lattice. -/
def topologicalQutritWeyl (a b : ℕ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  qutritWeyl a b

@[simp] theorem topologicalQutritWeyl_eq (a b : ℕ) :
    topologicalQutritWeyl a b = qutritWeyl a b := by
  rfl

/-- The Weyl readout is continuous from the discrete exponent lattice. -/
theorem continuous_topologicalQutritWeyl :
    Continuous (fun p : ℕ × ℕ => topologicalQutritWeyl p.1 p.2) := by
  exact continuous_of_discreteTopology

/-- The Weyl readout is locally constant on the exponent lattice. -/
theorem isLocallyConstant_topologicalQutritWeyl :
    IsLocallyConstant (fun p : ℕ × ℕ => topologicalQutritWeyl p.1 p.2) := by
  exact IsLocallyConstant.of_discrete
    (f := fun p : ℕ × ℕ => topologicalQutritWeyl p.1 p.2)

/-- Adding three to the clock exponent does not change a Weyl word. -/
theorem topologicalQutritWeyl_clock_period (a b : ℕ) :
    topologicalQutritWeyl (a + 3) b =
      topologicalQutritWeyl a b := by
  simp [topologicalQutritWeyl, qutritWeyl, pow_add, qutritClock_cube]

/-- Adding three to the shift exponent does not change a Weyl word. -/
theorem topologicalQutritWeyl_shift_period (a b : ℕ) :
    topologicalQutritWeyl a (b + 3) =
      topologicalQutritWeyl a b := by
  simp [topologicalQutritWeyl, qutritWeyl, pow_add, qutritShift_cube]

end
end InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological
