import InfoGeometry.Twistor.PenroseZornWittBoundary
import InfoGeometry.Twistor.PenroseLiteralCrossObstruction
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Completing the existing Witt norm map to an actual composition product

The existing Penrose-to-Zorn Witt map is upgraded to a real-linear
equivalence by proving its explicit inverse. Transporting the ALREADY
CONSTRUCTED native Zorn multiplication then supplies a chosen unital,
alternative composition product on the same real twistor space.

This is additional multiplication data. It is not the product of (7.105)
with the literal CCR triple, and the inequality is proved below. The native
pointwise multiplication on `Fin 4 -> C` is left untouched: no incompatible
`Mul` instance is installed. No exceptional-group classification is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseWittCompositionCompletion

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Twistor.PenroseZornWittBoundary
open InfoGeometry.Twistor.PenroseSignedCCRGeometry
open InfoGeometry.Twistor.PenroseLiteralCrossObstruction
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

local notation "NormZ" => InfoGeometry.Algebra.Zorn.ZornMatrix.detZ

/-- Explicit inverse of the repository-owned Witt coordinate map. -/
def wittCoordinateEquiv : Twistor4 ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  { penroseWittCoordinates with
    invFun c :=
      (![⟨(c 0 + c 4)/2, (c 1 - c 5)/2⟩, ⟨(c 2 - c 6)/2, (c 3 - c 7)/2⟩],
       ![⟨(c 0 - c 4)/2, (c 1 + c 5)/2⟩, ⟨(c 2 + c 6)/2, (c 3 + c 7)/2⟩])
    left_inv Z := by
      apply Prod.ext <;> funext i <;> fin_cases i <;>
        apply Complex.ext <;> simp [penroseWittCoordinates] <;> ring
    right_inv c := by
      funext i
      fin_cases i <;> simp [penroseWittCoordinates] <;> ring }

/-- The full real-linear equivalence uses the existing chiral and Peirce maps. -/
def wittZornEquiv : TwistorCarrier ≃ₗ[ℝ] CanonicalZorn :=
  twistorChiralRealDecomposition.trans
    (wittCoordinateEquiv.trans real8CircularPeirceEquiv)

theorem wittZornEquiv_apply (z : TwistorCarrier) :
    wittZornEquiv z = penroseWittZornMap (twistorChiralRealDecomposition z) := rfl

/-- Reuses the established quadratic compatibility rather than reasserting it. -/
theorem wittZornEquiv_norm (z : TwistorCarrier) : NormZ (wittZornEquiv z) =
    twistorRealQuadraticForm z := by
  rw [wittZornEquiv_apply, ← penroseTwistor4Carrier_quadratic_eq_wittZorn_norm]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The selected positive unit is the actual identity of the native Zorn algebra. -/
theorem wittZornEquiv_unit : wittZornEquiv chosenUnit = 1 := by
  have h0 : real8CircularPeirceEquiv (Pi.single 0 1) =
      InfoGeometry.Canonical.ZornMatrix.zornPlus := by
    calc
      real8CircularPeirceEquiv (Pi.single 0 1) = circularPeirceBasis 0 := by
        change circularPeirceBasis.equivFun.symm (Pi.single 0 1) = _
        rw [circularPeirceBasis.equivFun_symm_apply]
        simp
      _ = InfoGeometry.Canonical.ZornMatrix.zornPlus := by
        rw [circularPeirceBasis_apply]
        exact cartesianZorn_scalarPlus
  have h4 : real8CircularPeirceEquiv (Pi.single 4 1) =
      InfoGeometry.Canonical.ZornMatrix.zornMinus := by
    calc
      real8CircularPeirceEquiv (Pi.single 4 1) = circularPeirceBasis 4 := by
        change circularPeirceBasis.equivFun.symm (Pi.single 4 1) = _
        rw [circularPeirceBasis.equivFun_symm_apply]
        simp
      _ = InfoGeometry.Canonical.ZornMatrix.zornMinus := by
        rw [circularPeirceBasis_apply]
        exact cartesianZorn_scalarMinus
  have hc : penroseWittCoordinates (twistorChiralRealDecomposition chosenUnit) =
      Pi.single 0 1 + Pi.single 4 1 := by
    funext i
    fin_cases i <;> norm_num [penroseWittCoordinates, twistorChiralRealDecomposition,
      chosenUnit, Pi.single_apply]
  change real8CircularPeirceEquiv
    (penroseWittCoordinates (twistorChiralRealDecomposition chosenUnit)) = 1
  rw [hc, map_add, h0, h4, InfoGeometry.Canonical.ZornMatrix.zornPlus_add_zornMinus]

/-- Chosen composition product; no equality with the literal triple product is assumed. -/
def selectedMul (x y : TwistorCarrier) : TwistorCarrier :=
  wittZornEquiv.symm (wittZornEquiv x * wittZornEquiv y)

@[simp] theorem wittZornEquiv_selectedMul (x y : TwistorCarrier) :
    wittZornEquiv (selectedMul x y) = wittZornEquiv x * wittZornEquiv y := by
  exact wittZornEquiv.apply_symm_apply _

/-- The full composition identity on the ORIGINAL twistor quadratic form. -/
theorem selectedMul_norm (x y : TwistorCarrier) :
    twistorRealQuadraticForm (selectedMul x y) =
      twistorRealQuadraticForm x * twistorRealQuadraticForm y := by
  rw [← wittZornEquiv_norm, wittZornEquiv_selectedMul,
    ← wittZornEquiv_norm x, ← wittZornEquiv_norm y]
  exact InfoGeometry.Algebra.Zorn.ZornMatrix.detZ_mul _ _

@[simp] theorem selectedMul_unit_left (x : TwistorCarrier) : selectedMul chosenUnit x = x := by
  apply wittZornEquiv.injective
  rw [wittZornEquiv_selectedMul, wittZornEquiv_unit,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul]

@[simp] theorem selectedMul_unit_right (x : TwistorCarrier) : selectedMul x chosenUnit = x := by
  apply wittZornEquiv.injective
  rw [wittZornEquiv_selectedMul, wittZornEquiv_unit,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one]

theorem selectedMul_add_left (x y z : TwistorCarrier) :
    selectedMul (x + y) z = selectedMul x z + selectedMul y z := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul, map_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul]

theorem selectedMul_smul_left (r : ℝ) (x y : TwistorCarrier) :
    selectedMul (r • x) y = r • selectedMul x y := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul, map_smul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul]

theorem selectedMul_add_right (x y z : TwistorCarrier) :
    selectedMul x (y + z) = selectedMul x y + selectedMul x z := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul, map_add,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add]

theorem selectedMul_smul_right (r : ℝ) (x y : TwistorCarrier) :
    selectedMul x (r • y) = r • selectedMul x y := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul, map_smul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul]

/-- Alternativity is transported from the existing native Zorn proof. -/
theorem selectedMul_left_alternative (x y : TwistorCarrier) :
    selectedMul (selectedMul x x) y = selectedMul x (selectedMul x y) := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul]
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul]
  exact InfoGeometry.Algebra.zorn_left_alternative _ _

theorem selectedMul_right_alternative (x y : TwistorCarrier) :
    selectedMul (selectedMul y x) x = selectedMul y (selectedMul x x) := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedMul]
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_mul]
  exact InfoGeometry.Algebra.zorn_right_alternative _ _

/-- The chosen native composition product differs from every normalization
of the literal CCR-derived candidate, already on one explicit pair. -/
theorem selectedMul_ne_literal_candidate (k : ℝ) :
    selectedMul testX testY ≠ candidateProduct k testX testY := by
  intro h
  have hq := congrArg twistorRealQuadraticForm h
  rw [selectedMul_norm, (candidate_test_products k).1] at hq
  norm_num [quadratic_signature, testX, testY] at hq

/-- Reuses the existing genuine multiplication-stabilizer, not a nominal G2 dimension. -/
def selectedAut (φ : realZornCompositionAut) : TwistorCarrier ≃ₗ[ℝ] TwistorCarrier :=
  wittZornEquiv.trans ((φ : CanonicalLinearAut).trans wittZornEquiv.symm)

@[simp] theorem wittZornEquiv_selectedAut (φ : realZornCompositionAut) (x : TwistorCarrier) :
    wittZornEquiv (selectedAut φ x) = (φ : CanonicalLinearAut) (wittZornEquiv x) := by
  simp [selectedAut]

theorem selectedAut_preserves_product (φ : realZornCompositionAut) (x y : TwistorCarrier) :
    selectedAut φ (selectedMul x y) = selectedMul (selectedAut φ x) (selectedAut φ y) := by
  apply wittZornEquiv.injective
  simp only [wittZornEquiv_selectedAut, wittZornEquiv_selectedMul]
  exact φ.property _ _

end InfoGeometry.Twistor.PenroseWittCompositionCompletion
