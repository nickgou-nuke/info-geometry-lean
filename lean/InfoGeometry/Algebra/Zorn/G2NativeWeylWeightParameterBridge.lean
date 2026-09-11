import InfoGeometry.Algebra.Zorn.G2NativeWeylStructuralBridges
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylWeightParameterBridge

open InfoGeometry.Algebra.Zorn.G2NativeWeylStructuralBridges
open InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

def cycleInverseTracelessWeight :
    TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k :=
    ⟨![k.1 2, k.1 0, k.1 1], by
      change ∑ i, (![k.1 2, k.1 0, k.1 1] : Fin 3 → ℝ) i = 0
      rw [Fin.sum_univ_three]
      have hk := k.property
      change (∑ i, k.1 i) = 0 at hk
      rw [Fin.sum_univ_three] at hk
      simp at *
      linarith⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  map_smul' a k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

theorem cycleCartanParameterActionNative_cartanParameterOfWeight_inverse
    (k : TracelessWeight) :
    cycleCartanParameterActionNative (cartanParameterOfWeight k) =
      cartanParameterOfWeight (cycleInverseTracelessWeight k) := by
  have hk := k.property
  change (∑ i, k.1 i) = 0 at hk
  rw [Fin.sum_univ_three] at hk
  ext i
  fin_cases i <;>
    simp [cycleCartanParameterActionNative, cartanParameterOfWeight,
      cycleInverseTracelessWeight, parameterUnit] <;>
    linarith

theorem cycleInverseTracelessWeight_cycleTracelessWeight (k : TracelessWeight) :
    cycleInverseTracelessWeight (cycleTracelessWeight k) = k := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [cycleInverseTracelessWeight, cycleTracelessWeight]

def reflectionTracelessWeight :
    TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k :=
    ⟨![(k.1 0 - 4 * k.1 1) / 3,
      (-2 * k.1 0 - k.1 1) / 3,
      -((k.1 0 - 4 * k.1 1) / 3) -
        ((-2 * k.1 0 - k.1 1) / 3)], by
      change weightSum
        (![ (k.1 0 - 4 * k.1 1) / 3,
            (-2 * k.1 0 - k.1 1) / 3,
            -((k.1 0 - 4 * k.1 1) / 3) -
              ((-2 * k.1 0 - k.1 1) / 3)] : Fin 3 → ℝ) = 0
      simp [weightSum, Fin.sum_univ_three]
      ⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp <;> ring

theorem reflectionCartanParameterActionNative_cartanParameterOfWeight
    (k : TracelessWeight) :
    reflectionCartanParameterActionNative (cartanParameterOfWeight k) =
      cartanParameterOfWeight (reflectionTracelessWeight k) := by
  ext i
  fin_cases i <;>
    simp [reflectionCartanParameterActionNative, cartanParameterOfWeight,
      reflectionTracelessWeight, parameterUnit]

end InfoGeometry.Algebra.Zorn.G2NativeWeylWeightParameterBridge
