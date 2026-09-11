import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

/-!
# KreinSemilinearMap (minimal scaffold)

A tiny epsilon-equivariant map interface for doubled-real/Krein lanes.
This avoids duplicating existing owner structures while giving a bridge type
for bilingual mapping notes.
-/

namespace InfoGeometry.OperatorAlgebra

structure KreinSemilinearMap
    (H₁ H₂ : Type*)
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁] [KreinSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂] [KreinSpace H₂]
    where
  toFun : H₁ → H₂
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (r : ℝ) x, toFun (r • x) = r • toFun x
  map_J' : ∀ x, toFun ((KreinSpace.J : H₁ ≃ₗᵢ[ℝ] H₁) x) =
    (KreinSpace.J : H₂ ≃ₗᵢ[ℝ] H₂) (toFun x)

namespace KreinSemilinearMap

variable {H₁ H₂ H₃ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁] [KreinSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂] [KreinSpace H₂]
variable [NormedAddCommGroup H₃] [InnerProductSpace ℝ H₃] [CompleteSpace H₃] [KreinSpace H₃]

instance : CoeFun (KreinSemilinearMap H₁ H₂) (fun _ => H₁ → H₂) := ⟨fun f => f.toFun⟩

def comp (g : KreinSemilinearMap H₂ H₃) (f : KreinSemilinearMap H₁ H₂) :
    KreinSemilinearMap H₁ H₃ where
  toFun := fun x => g (f x)
  map_add' := by intro x y; simp [f.map_add', g.map_add']
  map_smul' := by intro r x; simp [f.map_smul', g.map_smul']
  map_J' := by intro x; simpa [f.map_J', g.map_J']

end KreinSemilinearMap

end InfoGeometry.OperatorAlgebra
