import InfoGeometry.KK.KasparovCycle

namespace InfoGeometry.KK.NonVacuousIndex

open InfoGeometry.Canonical.AnalyticalIndex

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable (X : KasparovCycle A B H)

/--
NON-VACUOUS SPECTRAL INDEX THEOREM:
For any finite-dimensional Kasparov cycle where F² = 1, the analytical index
is constructively zero.

This replaces the 'rfl' transport with a derivation from the operator identity.
-/
theorem analyticalIndex_eq_zero_of_F_sq_one [FiniteDimensional ℝ H]
    (hF : X.F * X.F = 1) :
    X.analyticalIndex = 0 := by
  -- 1. F² = 1 implies ker(F) is trivial
  have hSq : ∀ x : H, X.F (X.F x) = x := by
    intro x
    simpa using DFunLike.congr_fun hF x
  
  have hKer : LinearMap.ker X.F.toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    calc
      x = X.F (X.F x) := by symm; exact hSq x
      _ = X.F (X.F y) := by exact congrArg X.F hxy
      _ = y := hSq y
  
  -- 2. If ker(F) is trivial, then both chiral kernel slices are trivial
  have hSlicePlus : chiralKernelSlicePlus X.F.toLinearMap (KreinGradedModule.gradeCLM (H := H)).toLinearMap = ⊥ := by
    unfold chiralKernelSlicePlus
    rw [hKer]
    simp
    
  have hSliceMinus : chiralKernelSliceMinus X.F.toLinearMap (KreinGradedModule.gradeCLM (H := H)).toLinearMap = ⊥ := by
    unfold chiralKernelSliceMinus
    rw [hKer]
    simp
    
  -- 3. Calculate index from dimensions
  unfold KasparovCycle.analyticalIndex analyticalIndex
  rw [hSlicePlus, hSliceMinus]
  simp

end InfoGeometry.KK.NonVacuousIndex
