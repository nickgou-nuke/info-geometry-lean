import InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization

noncomputable section
set_option maxHeartbeats 800000

namespace InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
abbrev Derivation := SplitOctonionDerivationWittOrthogonalBridge.Derivation
abbrev Mat10 := InfoGeometry.Algebra.FiniteSpin.Mat10R
def derivationToSO55 (D : Derivation) : Mat10 := so44ToSO55 (canonicalDerivationFinMatrix D)
theorem so44ToSO55_injective : Function.Injective so44ToSO55 := by
  intro M N h; ext i j
  have h' := congrArg (fun K : Mat10 => K (fin10Equiv.symm (Sum.inl i)) (fin10Equiv.symm (Sum.inl j))) h
  simpa [so44ToSO55] using h'
theorem derivationToSO55_add (D E : Derivation) : derivationToSO55 (D + E) = derivationToSO55 D + derivationToSO55 E := by
  dsimp [derivationToSO55]
  have hmat : canonicalDerivationFinMatrix (D + E) = canonicalDerivationFinMatrix D + canonicalDerivationFinMatrix E := by
    change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) (transportedDerivation (D + E)) = _
    rw [show transportedDerivation (D + E) = transportedDerivation D + transportedDerivation E by exact transportedDerivationLinear.map_add D E]
    exact (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))).map_add _ _
  rw [hmat]; exact so44ToSO55_add _ _
theorem derivationToSO55_smul (r : ℝ) (D : Derivation) : derivationToSO55 (r • D) = r • derivationToSO55 D := by
  dsimp [derivationToSO55]
  have hmat : canonicalDerivationFinMatrix (r • D) = r • canonicalDerivationFinMatrix D := by
    change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) (transportedDerivation (r • D)) = _
    rw [show transportedDerivation (r • D) = r • transportedDerivation D by exact transportedDerivationLinear.map_smul r D]
    exact (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))).map_smul _ _
  rw [hmat]; exact so44ToSO55_smul r _
theorem derivationToSO55_map_lie (D E : Derivation) : derivationToSO55 ⁅D, E⁆ = derivationToSO55 D * derivationToSO55 E - derivationToSO55 E * derivationToSO55 D := by
  dsimp [derivationToSO55]; rw [canonicalDerivationFinMatrix_map_lie]; exact so44ToSO55_bracket _ _
theorem derivationToSO55_injective : Function.Injective derivationToSO55 := by
  intro D E h; apply canonicalDerivationFinMatrix_injective; exact so44ToSO55_injective h
noncomputable def derivationToSO55LieHom : Derivation →ₗ⁅ℝ⁆ Mat10 where
  toFun := derivationToSO55
  map_add' := derivationToSO55_add
  map_smul' := derivationToSO55_smul
  map_lie' := by intro D E; exact derivationToSO55_map_lie D E
theorem derivationToSO55LieHom_apply (D : Derivation) : derivationToSO55LieHom D = derivationToSO55 D := rfl
theorem derivationToSO55LieHom_injective : Function.Injective derivationToSO55LieHom := by
  intro D E h; apply derivationToSO55_injective; exact h
end InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
