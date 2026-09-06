import InfoGeometry.Algebra.PauliQuaternionSplitComparison

/-!
# The two finite Weyl frames behind the Zorn--Weyl construction

The supplied Zorn--Weyl reference distinguishes the ordinary Pauli frame
`W₁(eᵢ) = σᵢ` from the quaternion-compatible frame
`W₂(eᵢ) = i⁻¹ σᵢ = -i σᵢ`.  This owner records that finite distinction and
connects the second frame to the already formalized quaternion matrices.

Only the finite matrix facts are asserted here.  The Zorn product remains in
its nonassociative owner; no associative representation of the full octonion
algebra is claimed.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornWeylBasisFrame

open Matrix
open scoped Matrix
open InfoGeometry.Algebra.PauliQuaternionSplitComparison

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The three ordinary Pauli matrices. -/
def pauli : Fin 3 → M2C
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The ordinary Pauli/Weyl basis `W₁(eᵢ) = σᵢ`. -/
def weylW1 (i : Fin 3) : M2C := pauli i

/-- The quaternion-compatible Weyl basis `W₂(eᵢ) = i⁻¹σᵢ = -iσᵢ`. -/
def weylW2 (i : Fin 3) : M2C := (-Complex.I) • pauli i

@[simp] theorem weylW1_zero : weylW1 0 = !![0, 1; 1, 0] := by
  rfl

@[simp] theorem weylW1_one : weylW1 1 = !![0, -Complex.I; Complex.I, 0] := by
  rfl

@[simp] theorem weylW1_two : weylW1 2 = !![1, 0; 0, -1] := by
  rfl

theorem weylW2_eq_inverse_i_mul_weylW1 (i : Fin 3) :
    weylW2 i = (Complex.I)⁻¹ • weylW1 i := by
  rw [weylW2, weylW1]
  norm_num [Complex.inv_I]

theorem weylW2_eq_quaternion_frame :
    weylW2 0 = quatI ∧
    weylW2 1 = quatJ ∧
    weylW2 2 = quatK := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [weylW2, pauli, quatI, quatJ, quatK, Matrix.smul_apply,
      Complex.I_mul_I]

theorem weylW2_square (i : Fin 3) :
    weylW2 i * weylW2 i = -(1 : M2C) := by
  rcases weylW2_eq_quaternion_frame with ⟨h₀, h₁, h₂⟩
  fin_cases i
  · change weylW2 0 * weylW2 0 = _
    rw [h₀]
    exact quatI_sq
  · change weylW2 1 * weylW2 1 = _
    rw [h₁]
    exact quatJ_sq
  · change weylW2 2 * weylW2 2 = _
    rw [h₂]
    exact quatK_sq

theorem weylW2_pair_packet :
    weylW2 0 * weylW2 1 = weylW2 2 ∧
    weylW2 1 * weylW2 0 = -weylW2 2 ∧
    weylW2 1 * weylW2 2 = weylW2 0 ∧
    weylW2 2 * weylW2 1 = -weylW2 0 ∧
    weylW2 2 * weylW2 0 = weylW2 1 ∧
    weylW2 0 * weylW2 2 = -weylW2 1 := by
  rcases weylW2_eq_quaternion_frame with ⟨h₀, h₁, h₂⟩
  rw [h₀, h₁, h₂]
  exact ⟨quatI_mul_quatJ, quatJ_mul_quatI, quatJ_mul_quatK,
    quatK_mul_quatJ, quatK_mul_quatI, quatI_mul_quatK⟩

theorem weylW2_commutator_packet :
    weylW2 0 * weylW2 1 - weylW2 1 * weylW2 0 = (2 : ℂ) • weylW2 2 ∧
    weylW2 1 * weylW2 2 - weylW2 2 * weylW2 1 = (2 : ℂ) • weylW2 0 ∧
    weylW2 2 * weylW2 0 - weylW2 0 * weylW2 2 = (2 : ℂ) • weylW2 1 := by
  rcases weylW2_eq_quaternion_frame with ⟨h₀, h₁, h₂⟩
  rw [h₀, h₁, h₂]
  exact quaternion_commutator_packet

end InfoGeometry.Algebra.ZornWeylBasisFrame

end
