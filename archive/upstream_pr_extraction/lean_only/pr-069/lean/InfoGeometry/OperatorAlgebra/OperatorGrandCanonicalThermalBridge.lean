import InfoGeometry.OperatorAlgebra.OperatorGrandCanonicalChiralGenerator
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR

/-!
# Grand-canonical operator/CAR bridge

This owner joins the two already-proved noncommutative layers.  The carrier is
an arbitrary associative operator ring.  The chemical potentials and
Bogoliubov coefficients are operator elements subject only to the explicit
centrality and normalization hypotheses used by the respective identities.
No scalar diagonalisation, state, completion, or analytic exponential is
introduced here.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A]

theorem operator_grandCanonical_CAR_and_grading
    {Γ_R Γ_χ Γ_N H Nplus Nminus μ μχ : A}
    {a c b d u v : A}
    (hH : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N H)
    (hPlus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nplus)
    (hMinus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nminus)
    (hμ : ∀ z : A, μ * z = z * μ)
    (hμχ : ∀ z : A, μχ * z = z * μχ)
    (hu : ∀ z : A, z * u = u * z)
    (hv : ∀ z : A, z * v = v * z)
    (huv : u * u + v * v = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
        (grandCanonicalGenerator H Nplus Nminus μ μχ) ∧
      thermalAnticommutator
        (operatorThermalAnnihilator a d u v)
        (operatorThermalCreator c b u v) = 1 := by
  refine ⟨?_, ?_⟩
  · exact grandCanonicalGenerator_isFullyEven
      hH hPlus hMinus hμ hμχ
  · exact operator_thermal_bogoliubov_car_preserved
      a c b d u v hu hv huv hac hbd hab hcd

theorem operator_modularGrandCanonical_CAR_and_grading
    {Γ_R Γ_χ Γ_N β H Nplus Nminus μ μχ : A}
    {a c b d u v : A}
    (hH : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N H)
    (hPlus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nplus)
    (hMinus : ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N Nminus)
    (hβ : ∀ z : A, β * z = z * β)
    (hμ : ∀ z : A, μ * z = z * μ)
    (hμχ : ∀ z : A, μχ * z = z * μχ)
    (hu : ∀ z : A, z * u = u * z)
    (hv : ∀ z : A, z * v = v * z)
    (huv : u * u + v * v = 1)
    (hac : thermalAnticommutator a c = 1)
    (hbd : thermalAnticommutator b d = 1)
    (hab : thermalAnticommutator a b = 0)
    (hcd : thermalAnticommutator c d = 0) :
    ModularZ2CubeGrading.isFullyEven Γ_R Γ_χ Γ_N
        (modularGrandCanonicalGenerator β H Nplus Nminus μ μχ) ∧
      thermalAnticommutator
        (operatorThermalAnnihilator a d u v)
        (operatorThermalCreator c b u v) = 1 := by
  refine ⟨?_, ?_⟩
  · have hTot := totalNumber_isFullyEven hPlus hMinus
    have hCharge := chiralCharge_isFullyEven hPlus hMinus
    exact _root_.ModularZ2CubeGrading.grand_canonical_generator_is_fully_even
      Γ_R Γ_χ Γ_N hH hTot hCharge hβ hμ hμχ
  · exact operator_thermal_bogoliubov_car_preserved
      a c b d u v hu hv huv hac hbd hab hcd

end InfoGeometry.OperatorAlgebra
