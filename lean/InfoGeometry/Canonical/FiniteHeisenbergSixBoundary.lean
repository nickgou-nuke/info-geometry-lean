import InfoGeometry.Canonical.FiniteHeisenbergGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra

/-!
# The finite Heisenberg boundary of the six-state Weyl layer

This owner records the exact separation between the finite exponentiated Weyl
relations and the characteristic-zero additive CCR.  The latter cannot hold
in a finite matrix algebra by the trace obstruction.
-/

namespace InfoGeometry.Canonical.FiniteHeisenbergSixBoundary

open InfoGeometry.Canonical.FiniteHeisenbergCore
open InfoGeometry.Canonical.SixStateGeneralizedCliffordAlgebra

noncomputable section

def heisenbergSixX : FiniteHeisenberg 6 :=
  ⟨((1, 0), 0)⟩

def heisenbergSixZ : FiniteHeisenberg 6 :=
  ⟨((0, 1), 0)⟩

theorem heisenbergSixX_commutator_heisenbergSixZ :
    heisenbergSixX * heisenbergSixZ * heisenbergSixX⁻¹ * heisenbergSixZ⁻¹ =
      finiteHeisenbergCenterElement 1 := by
  rw [finiteHeisenberg_group_commutator]
  rfl

theorem heisenbergSix_center_card :
    Fintype.card (Heisenberg 6) = 216 :=
  card_heisenberg_six

/-! ## The additive CCR obstruction -/

def matrixCommutator (P Q : SixMatrix) : SixMatrix := P * Q - Q * P

theorem trace_matrixCommutator (P Q : SixMatrix) :
    Matrix.trace (matrixCommutator P Q) = 0 := by
  rw [matrixCommutator, Matrix.trace_sub, Matrix.trace_mul_comm P Q]
  ring

/-- No finite six-state matrix representation can satisfy the additive Weyl
CCR `[P,Q] = I`.  The finite Weyl layer is therefore necessarily the
exponentiated, cyclotomic relation instead. -/
theorem no_additive_CCR_in_six_state (P Q : SixMatrix) :
    matrixCommutator P Q ≠ (1 : SixMatrix) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [trace_matrixCommutator] at ht
  simp at ht

theorem finiteWeyl_is_not_additive_CCR :
    ¬ ∃ P Q : SixMatrix, P * Q - Q * P = (1 : SixMatrix) := by
  rintro ⟨P, Q, h⟩
  exact no_additive_CCR_in_six_state P Q h

end

end InfoGeometry.Canonical.FiniteHeisenbergSixBoundary
