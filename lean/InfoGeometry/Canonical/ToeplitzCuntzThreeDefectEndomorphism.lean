import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
import InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors

/-!
# The Toeplitz--Cuntz defect as an ambient multiplication endomorphism

`P₀` is a ring element in the native Toeplitz--Cuntz carrier.  This owner
records the canonical, type-correct passage from that element to left
multiplication on the algebra carrier.  It does not identify this map with a
Clifford-shadow readout; such an identification would require an additional
inclusion/readout theorem.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeDefectEndomorphism

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open InfoGeometry.Physics.Algebra
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Left multiplication by the native Toeplitz defect `P₀`. -/
def defectLeftMul : Module.End ℝ A := leftMulOp g.P0

@[simp] theorem defectLeftMul_apply (x : A) :
    defectLeftMul g x = g.P0 * x :=
  rfl

/-- The bilateral Peirce-sandwich action of the native defect `P₀`. -/
def defectSandwich : Module.End ℝ A :=
  (leftMulOp g.P0).comp (rightMulOp g.P0)

@[simp] theorem defectSandwich_apply (x : A) :
    defectSandwich g x = g.P0 * (x * g.P0) :=
  rfl

/-- The defect action is an idempotent ambient endomorphism. -/
theorem defectLeftMul_idempotent :
    defectLeftMul g * defectLeftMul g = defectLeftMul g := by
  ext x
  change g.P0 * (g.P0 * x) = g.P0 * x
  rw [← mul_assoc, defectProjection_sq g]

/-- The defect action kills the active Toeplitz Hamiltonian on the right. -/
theorem defectLeftMul_comp_hamiltonian :
    defectLeftMul g * leftMulOp g.susyHamiltonian = 0 := by
  ext x
  simp only [defectLeftMul, leftMulOp_apply]
  change g.P0 * (g.susyHamiltonian * x) = 0
  rw [← mul_assoc, susyHamiltonian_defect_annihilation_left g, zero_mul]

/-- If `P₀` is nonzero, its left-multiplication endomorphism is nonzero. -/
theorem defectLeftMul_ne_zero (hP0 : g.P0 ≠ 0) :
    defectLeftMul g ≠ 0 := by
  intro h
  have h1 : defectLeftMul g (1 : A) = (0 : A) := by
    rw [h]
    rfl
  simpa using hP0 (by simpa [defectLeftMul] using h1)

/-! The sandwich is a genuine idempotent endomorphism, but it is not yet
identified with a `ProjectedCliffordShadow` readout. -/

theorem defectSandwich_idempotent :
    defectSandwich g * defectSandwich g = defectSandwich g := by
  ext x
  change g.P0 * (g.P0 * (x * g.P0) * g.P0) = g.P0 * (x * g.P0)
  calc
    g.P0 * (g.P0 * (x * g.P0) * g.P0) =
        (g.P0 * g.P0) * (x * (g.P0 * g.P0)) := by noncomm_ring
    _ = g.P0 * (x * g.P0) := by rw [defectProjection_sq g]

theorem defectSandwich_ne_zero (hP0 : g.P0 ≠ 0) :
    defectSandwich g ≠ 0 := by
  intro h
  have h1 : defectSandwich g (1 : A) = (0 : A) := by
    rw [h]
    rfl
  have hp : g.P0 * g.P0 = 0 := by
    simpa [defectSandwich] using h1
  apply hP0
  rw [defectProjection_sq g] at hp
  exact hp

end InfoGeometry.Canonical.ToeplitzCuntzThreeDefectEndomorphism
