import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGraphSection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Dual connections for the doubled chiral frame

For a fixed nondegenerate cross-sheet matrix `η`, the dual coefficient matrix is

`ω⁻ = -η⁻¹ (ω⁺)ᵀ η`.

The compatibility equation is proved here as a finite matrix identity.  No
curvature or affine-flatness theorem is inferred from this algebraic relation.
-/

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinDualConnection

abbrev Index := Fin 4
abbrev Connection := Matrix Index Index ℝ

def dualConnection (η ηInv ω : Connection) : Connection :=
  -(ηInv * ω.transpose * η)

theorem dualConnection_compatibility
    (η ηInv ω : Connection)
    (hη : η * ηInv = (1 : Connection)) :
    ω.transpose * η + η * dualConnection η ηInv ω = 0 := by
  calc
    ω.transpose * η + η * dualConnection η ηInv ω =
        ω.transpose * η - (η * ηInv) * ω.transpose * η := by
          simp [dualConnection, Matrix.mul_assoc, sub_eq_add_neg]
    _ = ω.transpose * η - (1 : Connection) * ω.transpose * η := by
          rw [hη]
    _ = 0 := by simp

theorem dualConnection_formula
    (η ηInv ω : Connection) :
    dualConnection η ηInv ω = -(ηInv * ω.transpose * η) := rfl

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinDualConnection
