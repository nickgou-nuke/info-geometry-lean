import InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
import InfoGeometry.Algebra.Zorn.SplitOctonionExteriorFrameBridge
import InfoGeometry.Quantum.DualFlatKreinGraph

/-!
# Parameterized PAC/Krein null-coordinate bridge

The bridge is parameterized by a chosen primal/dual linear equivalence.  This
keeps the identification `Vector 4 ≃ Covector 4` explicit rather than
silently imposing a metric.
-/

namespace InfoGeometry.Quantum.PACKreinEquivalence

noncomputable section

open InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
open InfoGeometry.Algebra.Zorn.SplitOctonionExteriorFrameBridge
open ProjectiveAffineConformalClosure55
open InfoGeometry.Quantum.DualFlatKreinGraph

noncomputable def coordinateEquiv : Vector 4 ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toLinearEquiv

def xCoordinates (X : PACSplit44) : Fin 4 → ℝ :=
  ![X.x0, X.x1, X.x2, X.x3]

def yCoordinates (X : PACSplit44) : Fin 4 → ℝ :=
  ![X.y0, X.y1, X.y2, X.y3]

noncomputable def nullPrimal (X : PACSplit44) : Vector 4 :=
  coordinateEquiv.symm (xCoordinates X + yCoordinates X)

noncomputable def nullDual (X : PACSplit44) : Vector 4 :=
  coordinateEquiv.symm (xCoordinates X - yCoordinates X)

noncomputable def pacToKrein (E : Vector 4 ≃ₗ[ℝ] Covector 4) (X : PACSplit44) : Carrier 4 :=
  (nullPrimal X, E (nullDual X))

noncomputable def carrierToPAC (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (z : Carrier 4) : PACSplit44 :=
  let u := coordinateEquiv z.1
  let v := coordinateEquiv (E.symm z.2)
  coordinateToPAC
    (fun i => (u i + v i) / 2, fun i => (u i - v i) / 2)

theorem carrierToPAC_pacToKrein
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (X : PACSplit44) :
    carrierToPAC E (pacToKrein E X) = X := by
  cases X
  congr <;> simp [carrierToPAC, pacToKrein, nullPrimal, nullDual,
    xCoordinates, yCoordinates, coordinateToPAC] <;> ring

theorem pacToKrein_carrierToPAC
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (z : Carrier 4) :
    pacToKrein E (carrierToPAC E z) = z := by
  rcases z with ⟨v, α⟩
  apply Prod.ext
  · apply coordinateEquiv.injective
    funext i
    fin_cases i <;>
      simp [pacToKrein, carrierToPAC, nullPrimal, nullDual,
        xCoordinates, yCoordinates, coordinateToPAC,
        LinearEquiv.apply_symm_apply] <;> ring
  · apply E.symm.injective
    apply coordinateEquiv.injective
    funext i
    fin_cases i <;>
      simp [pacToKrein, carrierToPAC, nullPrimal, nullDual,
        xCoordinates, yCoordinates, coordinateToPAC,
        LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] <;> ring

noncomputable def pacKreinEquiv (E : Vector 4 ≃ₗ[ℝ] Covector 4) :
    PACSplit44 ≃ Carrier 4 where
  toFun := pacToKrein E
  invFun := carrierToPAC E
  left_inv := carrierToPAC_pacToKrein E
  right_inv := pacToKrein_carrierToPAC E

noncomputable def pacNeutralPolar (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (X Y : PACSplit44) : ℝ :=
  ((E (nullDual Y)) (nullPrimal X) +
    (E (nullDual X)) (nullPrimal Y)) / 2

def CoordinateCompatible (E : Vector 4 ≃ₗ[ℝ] Covector 4) : Prop :=
  ∀ a b, (E a) b = ∑ i : Fin 4, coordinateEquiv a i * coordinateEquiv b i

def pacQ44Polar (X Y : PACSplit44) : ℝ :=
  X.x0 * Y.x0 + X.x1 * Y.x1 + X.x2 * Y.x2 + X.x3 * Y.x3 -
    (X.y0 * Y.y0 + X.y1 * Y.y1 + X.y2 * Y.y2 + X.y3 * Y.y3)

theorem pacToKrein_neutralPair
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (X Y : PACSplit44) :
    neutralPair (pacToKrein E X) (pacToKrein E Y) = pacNeutralPolar E X Y := by
  simp [neutralPair, pacToKrein, pacNeutralPolar]
  ring

theorem pacNeutralPolar_eq_Q44Polar
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (hE : CoordinateCompatible E)
    (X Y : PACSplit44) :
    pacNeutralPolar E X Y = pacQ44Polar X Y := by
  rw [pacNeutralPolar, hE, hE]
  simp [nullPrimal, nullDual, coordinateEquiv, xCoordinates, yCoordinates,
    pacQ44Polar, Fin.sum_univ_succ]
  ring

theorem pacToKrein_neutralPair_eq_Q44Polar
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (hE : CoordinateCompatible E)
    (X Y : PACSplit44) :
    neutralPair (pacToKrein E X) (pacToKrein E Y) =
      pacQ44Polar X Y := by
  rw [pacToKrein_neutralPair, pacNeutralPolar_eq_Q44Polar E hE]

theorem pacToKrein_neutralPair_self_eq_Q44
    (E : Vector 4 ≃ₗ[ℝ] Covector 4) (hE : CoordinateCompatible E)
    (X : PACSplit44) :
    neutralPair (pacToKrein E X) (pacToKrein E X) = Q44 X := by
  rw [pacToKrein_neutralPair]
  unfold pacNeutralPolar
  rw [hE]
  simp [nullPrimal, nullDual, coordinateEquiv, xCoordinates, yCoordinates,
    Q44, Fin.sum_univ_succ]
  ring

theorem pacToKrein_primal_null (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (X : PACSplit44) :
    (pacToKrein E X).1 = nullPrimal X := by
  rfl

theorem pacToKrein_dual_null (E : Vector 4 ≃ₗ[ℝ] Covector 4)
    (X : PACSplit44) :
    E.symm (pacToKrein E X).2 = nullDual X := by
  simp [pacToKrein]

end

end InfoGeometry.Quantum.PACKreinEquivalence
