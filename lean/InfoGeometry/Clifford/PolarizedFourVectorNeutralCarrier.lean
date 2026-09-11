import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornPolarizationMetricBridge

/-!
# The attachment's ten coordinates belong to a neutral quadratic carrier

The coordinate layout is kept only for auditing the proposed quadratic form.
It is not given an octonionic multiplication. A linear coordinate equivalence
puts it into the split five-pair form, and its quadratic readout is compared
with the repository's native unscaled neutral quadratic form on `E × E*`.
-/

noncomputable section

namespace InfoGeometry.Clifford.PolarizedFourVectorNeutralCarrier

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev FourVectorLayout := (ℝ × (Fin 4 → ℝ)) × (ℝ × (Fin 4 → ℝ))
abbrev FiveCoordinates := InfoGeometry.Algebra.FiniteSpin.Vec5R

def sourceQuadratic (X : FourVectorLayout) : ℝ :=
  X.1.1 * X.2.1 - (X.1.2 0 * X.2.2 0 - X.1.2 1 * X.2.2 1 -
    X.1.2 2 * X.2.2 2 - X.1.2 3 * X.2.2 3)

/-- `(alpha,U)` and `(beta,-eta*V)` are five coordinates each. -/
def fivePairCoordinates : FourVectorLayout ≃ₗ[ℝ] (FiveCoordinates × FiveCoordinates) where
  toFun X :=
    (![X.1.1, X.1.2 0, X.1.2 1, X.1.2 2, X.1.2 3],
     ![X.2.1, -X.2.2 0, X.2.2 1, X.2.2 2, X.2.2 3])
  invFun X :=
    ((X.1 0, ![X.1 1, X.1 2, X.1 3, X.1 4]),
     (X.2 0, ![-X.2 1, X.2 2, X.2 3, X.2 4]))
  left_inv X := by
    rcases X with ⟨⟨a, U⟩, ⟨b, V⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp
    · apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp
  right_inv X := by
    rcases X with ⟨p, q⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  map_add' X Y := by
    apply Prod.ext
    · simp
    · ext i
      fin_cases i <;> simp <;> abel
  map_smul' c X := by
    apply Prod.ext
    · simp
    · ext i
      fin_cases i <;> simp

theorem quadratic_fivePair (X : FourVectorLayout) :
    sourceQuadratic X = ∑ i, (fivePairCoordinates X).1 i * (fivePairCoordinates X).2 i := by
  simp [sourceQuadratic, fivePairCoordinates, Fin.sum_univ_succ] <;> ring

/-- Native finite-coordinate covector. No Lorentz four-dimensional cross product is used. -/
def coordinateCovector (q : FiveCoordinates) : Module.Dual ℝ FiveCoordinates :=
  ∑ i : Fin 5, q i • LinearMap.proj i

@[simp] theorem coordinateCovector_apply (q p : FiveCoordinates) :
    coordinateCovector q p = ∑ i, q i * p i := by
  simp [coordinateCovector, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Read the ten-coordinate quadratic data in the existing neutral phase space. -/
def nativeNeutralReadout (X : FourVectorLayout) : PhaseSpaceCarrier FiveCoordinates :=
  ((fivePairCoordinates X).1, coordinateCovector (fivePairCoordinates X).2)

theorem quadratic_nativeNeutral (X : FourVectorLayout) :
    canonicalNeutralFormUnscaled (nativeNeutralReadout X) = sourceQuadratic X := by
  rw [canonicalNeutralFormUnscaled_apply, quadratic_fivePair]
  simp only [nativeNeutralReadout, coordinateCovector_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Diagonal hyperbolic normal form in freely varying five-pair coordinates. -/
theorem quadratic_split_normal_form (p q : FiveCoordinates) :
    sourceQuadratic (fivePairCoordinates.symm (p, q)) =
      ∑ i, (((p i + q i) / 2) ^ 2 - ((p i - q i) / 2) ^ 2) := by
  rw [quadratic_fivePair, fivePairCoordinates.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  dsimp
  ring

theorem ten_coordinate_dimension : Module.finrank ℝ FourVectorLayout = 10 := by
  simp [FourVectorLayout, Module.finrank_prod]

/-- A linear change of coordinates cannot turn the proposed ten coordinates
into the native eight-dimensional Zorn carrier. -/
theorem no_linear_equivalence_to_Zorn : ¬ Nonempty (FourVectorLayout ≃ₗ[ℝ] ZornCoord) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [ten_coordinate_dimension,
    InfoGeometry.Canonical.ZornPolarizationMetricBridge.native_dimensions.1] at h
  norm_num at h

/-- The quadratic nullness of either five-coordinate half is independent of
any multiplication. It is not a square-zero assertion. -/
theorem five_halves_null (p q : FiveCoordinates) :
    sourceQuadratic (fivePairCoordinates.symm (p, 0)) = 0 ∧
      sourceQuadratic (fivePairCoordinates.symm (0, q)) = 0 := by
  constructor <;> rw [quadratic_fivePair, fivePairCoordinates.apply_symm_apply] <;> simp

/-- The source's signed exchange on its own ten-coordinate layout. -/
def sourceSignedExchange (X : FourVectorLayout) : FourVectorLayout :=
  ((X.2.1, -X.2.2), (X.1.1, -X.1.2))

@[simp] theorem sourceSignedExchange_sq (X : FourVectorLayout) :
    sourceSignedExchange (sourceSignedExchange X) = X := by
  rcases X with ⟨⟨a, U⟩, ⟨b, V⟩⟩
  simp [sourceSignedExchange]

theorem sourceSignedExchange_preserves_quadratic (X : FourVectorLayout) :
    sourceQuadratic (sourceSignedExchange X) = sourceQuadratic X := by
  simp [sourceQuadratic, sourceSignedExchange] <;> ring

/-- Polarization, here used only to test the proposed fundamental symmetry. -/
def sourcePolar (X Y : FourVectorLayout) : ℝ :=
  (sourceQuadratic (X + Y) - sourceQuadratic X - sourceQuadratic Y) / 2

/-- In the ten-coordinate layout with a Minkowski vector contraction, the
same signed exchange fails the positive Hilbertization condition. -/
theorem sourceSignedExchange_not_positive :
    ¬ ∀ X : FourVectorLayout, 0 ≤ sourcePolar X (sourceSignedExchange X) := by
  intro h
  have hbad := h ((0, ![0, 1, 0, 0]), (0, 0))
  norm_num [sourcePolar, sourceQuadratic, sourceSignedExchange] at hbad
  have hneg : (0 : ℝ) ≤ -1 / 2 := by
    simpa using hbad
  linarith

end InfoGeometry.Clifford.PolarizedFourVectorNeutralCarrier
