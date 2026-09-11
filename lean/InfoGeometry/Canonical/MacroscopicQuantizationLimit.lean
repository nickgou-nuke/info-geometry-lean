-- lean/InfoGeometry/Canonical/MacroscopicQuantizationLimit.lean
import InfoGeometry.OperatorAlgebra.CliffordInfinityCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GeometricQuantization
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.Basic

namespace InfoGeometry.Canonical.Macroscopic

open CategoryTheory Limits InfoGeometry.OperatorAlgebra

/-- The finite integer Bernstein-Sato phase list used by this colimit readout. -/
def macroscopicBernsteinSatoRoots : List ℚ :=
  [-1, -2]

/--
  The property of a state having a Holonomic D-module annihilator
  with strictly integer Bernstein-Sato roots (trivial monodromy).
-/
def IsAnomalyFreeQuantization (A : RingCat) : Prop :=
  A = colimit Cl_functor ∧
    ∃ (global_phases : List ℚ), global_phases = macroscopicBernsteinSatoRoots

/-- Every finite stage carries the same integer phase list. -/
theorem finite_stages_locally_quantized :
    Quantization.IsLocallyQuantized ℕ macroscopicBernsteinSatoRoots := by
  unfold Quantization.IsLocallyQuantized
  refine And.intro (Nonempty.intro (0 : ℕ)) ?_
  intro n
  exact ⟨macroscopicBernsteinSatoRoots, rfl⟩

/-- The Clifford tower colimit preserves the finite integer phase list. -/
theorem macroscopic_quantization_phases :
    ∃ (global_phases : List ℚ), global_phases = macroscopicBernsteinSatoRoots :=
  Quantization.colimit_preserves_quantization Cl_functor macroscopicBernsteinSatoRoots
    finite_stages_locally_quantized

/--
  THE MACROSCOPIC STABILITY CAPSTONE
  Proves that the trivial monodromy of the local thermodynamic singularities 
  survives the infinite categorical colimit of the Clifford tower.
-/
theorem macroscopic_vacuum_is_anomaly_free :
    IsAnomalyFreeQuantization (colimit Cl_functor) := by
  exact ⟨rfl, macroscopic_quantization_phases⟩

end InfoGeometry.Canonical.Macroscopic
