import InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahlerBridge

/-!
# Pfaffian on Arbitrary Two-Dimensional Skew Matrices

This module formalizes the algebraic mechanics of the Pfaffian as the canonical
square root of the determinant for skew-symmetric matrices.

The repository already contains the standard parameterized 2-by-2 Pfaffian
identity and congruence formula. This module extends that finite result to an
arbitrary 2-by-2 matrix satisfying explicit skew-symmetry equations. It proves
only these matrix identities; no Spin or metaplectic group is constructed.
-/

namespace InfoGeometry.GrandUnification.PfaffianSquareRootCharacter

open Matrix

variable {R : Type*} [CommRing R]

/-- The signed Pfaffian in the standard orientation of the two coordinates. -/
def pfaffian2D (A : Matrix (Fin 2) (Fin 2) R) : R := A 0 1

/-- Exact skew-symmetry conditions for a two-dimensional matrix. -/
def IsSkew2D (A : Matrix (Fin 2) (Fin 2) R) : Prop :=
  A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 1 0 = -A 0 1

/-- For an arbitrary skew 2-by-2 matrix, the determinant is the square of
the `(0,1)` entry, the signed Pfaffian in this orientation. -/
theorem det_eq_pfaffian_sq_of_isSkew2D (A : Matrix (Fin 2) (Fin 2) R)
    (hA : IsSkew2D A) : Matrix.det A = (pfaffian2D A) ^ 2 := by
  rcases hA with ⟨h00, h11, h10⟩
  rw [Matrix.det_fin_two]
  simp [pfaffian2D, h00, h11, h10]
  ring

/-- The Pfaffian congruence law for every matrix satisfying the explicit
skew-symmetry conditions, not only the standard one-parameter representative. -/
theorem pfaffian2D_congruence_of_isSkew2D
    (M A : Matrix (Fin 2) (Fin 2) R) (hA : IsSkew2D A) :
    pfaffian2D (M * A * Mᵀ) = Matrix.det M * pfaffian2D A := by
  rcases hA with ⟨h00, h11, h10⟩
  have hA_eq : A =
      InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2 (A 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2,
        h00, h11, h10]
  have hcongA : M * A * Mᵀ = M *
      InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2 (A 0 1) * Mᵀ := by
    exact congrArg (fun B : Matrix (Fin 2) (Fin 2) R => M * B * Mᵀ) hA_eq
  calc
    pfaffian2D (M * A * Mᵀ) = pfaffian2D
        (M * InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2
          (A 0 1) * Mᵀ) := congrArg pfaffian2D hcongA
    _ = Matrix.det M * A 0 1 := by
      change (M * InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2
        (A 0 1) * Mᵀ) 0 1 = Matrix.det M * A 0 1
      rw [InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.pfaffian_congruence_2x2]
      rfl
    _ = Matrix.det M * pfaffian2D A := by rfl

end InfoGeometry.GrandUnification.PfaffianSquareRootCharacter
