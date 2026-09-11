import InfoGeometry.Canonical.HestenesKreinMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hestenes Hermitian adjoint and native Krein adjoint

The pure reverse-Krein operation is intentionally not identified with matrix
conjugate-transpose.  The Hermitian Clifford operation inserts γ₀ first:
`x†H = γ₀ reverse(x) γ₀`; the Krein operation then twists it by β.
-/

noncomputable section
namespace HestenesHermitianAdjoint

open HestenesCl14
open HestenesCliffordKrein
open HestenesKreinMatrixBridge

abbrev Algebra := Cl14
abbrev EvenAlgebra := ClPlus14

def hestenesAdjoint (x : EvenAlgebra) : EvenAlgebra :=
  ⟨gamma 0 * (reverseEven x : Algebra) * gamma 0, by
    have hodd : gamma 0 ∈ CliffordAlgebra.evenOdd Q14 1 := gamma_zero_mem_odd
    have heven : (reverseEven x : Algebra) ∈ CliffordAlgebra.evenOdd Q14 0 :=
      (CliffordAlgebra.reverse_mem_evenOdd_iff (Q := Q14)).2 x.2
    have hleft : gamma 0 * (reverseEven x : Algebra) ∈
        CliffordAlgebra.evenOdd Q14 (1 + 0) :=
      SetLike.mul_mem_graded hodd heven
    simpa using SetLike.mul_mem_graded hleft hodd⟩

def hestenesKreinAdjoint (x : EvenAlgebra) : EvenAlgebra :=
  sigmaEven 0 * hestenesAdjoint x * sigmaEven 0

@[simp] theorem hestenesAdjoint_val (x : EvenAlgebra) :
    (hestenesAdjoint x : Algebra) =
      gamma 0 * CliffordAlgebra.reverse (x : Algebra) * gamma 0 := rfl

@[simp] theorem hestenesAdjoint_add (x y : EvenAlgebra) :
    hestenesAdjoint (x + y) = hestenesAdjoint x + hestenesAdjoint y := by
  apply Subtype.ext
  simp [hestenesAdjoint, reverseEven, mul_add, add_mul]

@[simp] theorem hestenesAdjoint_smul (r : ℝ) (x : EvenAlgebra) :
    hestenesAdjoint (r • x) = r • hestenesAdjoint x := by
  apply Subtype.ext
  simp [hestenesAdjoint, reverseEven]

@[simp] theorem hestenesAdjoint_mul (x y : EvenAlgebra) :
    hestenesAdjoint (x * y) = hestenesAdjoint y * hestenesAdjoint x := by
  apply Subtype.ext
  change gamma 0 * CliffordAlgebra.reverse ((x : Algebra) * (y : Algebra)) *
      gamma 0 =
    (gamma 0 * CliffordAlgebra.reverse (y : Algebra) * gamma 0) *
      (gamma 0 * CliffordAlgebra.reverse (x : Algebra) * gamma 0)
  rw [CliffordAlgebra.reverse.map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (gamma 0) (gamma 0)]
  rw [gamma_zero_sq]
  simp

@[simp] theorem hestenesAdjoint_involutive (x : EvenAlgebra) :
    hestenesAdjoint (hestenesAdjoint x) = x := by
  apply Subtype.ext
  change gamma 0 * CliffordAlgebra.reverse
      (gamma 0 * CliffordAlgebra.reverse (x : Algebra) * gamma 0) * gamma 0 =
    (x : Algebra)
  rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul]
  have hr : CliffordAlgebra.reverse (gamma 0) = gamma 0 := by
    simp [gamma]
  rw [hr]
  simp only [CliffordAlgebra.reverse_reverse, mul_assoc]
  rw [← mul_assoc (gamma 0) (gamma 0), gamma_zero_sq]
  simp

end HestenesHermitianAdjoint
end noncomputable section
