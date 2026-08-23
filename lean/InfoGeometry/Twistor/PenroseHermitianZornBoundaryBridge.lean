import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Twistor.PenroseZornWittBoundary
import Mathlib.Tactic.FinCases

/-!
# Penrose Hermitian boundary and the Witt-polarized Zorn norm

`PenroseIncidence` stores a twistor as `Spinor2 × Spinor2`, while
`PenroseTwistor` stores the same complex four-dimensional carrier as
`Fin 4 → ℂ`.  This owner supplies the explicit linear equivalence between
those two presentations and proves that the bundled Penrose real quadratic
form is exactly the split `(4,4)` sheet signature used by the Witt/Zorn
boundary owner.

Consequently the Penrose null boundary and the zero reduced-norm locus of the
Witt-polarized split-octonion carrier are the same finite quadratic condition.
No multiplication intertwining is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseHermitianZornBoundaryBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseZornWittBoundary

/-- Flatten the two Penrose spinor sheets into the established `Fin 4 → ℂ`
Penrose twistor carrier in the order `ω₀, ω₁, π₀, π₁`. -/
def twistor4ToPenroseCarrier : Twistor4 →ₗ[ℂ] TwistorCarrier where
  toFun Z := ![Z.1 0, Z.1 1, Z.2 0, Z.2 1]
  map_add' Z W := by
    funext i
    fin_cases i <;> simp
  map_smul' c Z := by
    funext i
    fin_cases i <;> simp

/-- Recover the two spinor sheets from the flattened Penrose carrier. -/
def penroseCarrierToTwistor4 : TwistorCarrier →ₗ[ℂ] Twistor4 where
  toFun z := (![z 0, z 1], ![z 2, z 3])
  map_add' z w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_smul' c z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

@[simp] theorem penroseCarrierToTwistor4_twistor4ToPenroseCarrier
    (Z : Twistor4) :
    penroseCarrierToTwistor4 (twistor4ToPenroseCarrier Z) = Z := by
  rcases Z with ⟨ω, π⟩
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

@[simp] theorem twistor4ToPenroseCarrier_penroseCarrierToTwistor4
    (z : TwistorCarrier) :
    twistor4ToPenroseCarrier (penroseCarrierToTwistor4 z) = z := by
  funext i
  fin_cases i <;> rfl

/-- The two concrete Penrose twistor presentations are complex-linearly
identical. -/
noncomputable def twistor4EquivPenroseCarrier :
    Twistor4 ≃ₗ[ℂ] TwistorCarrier where
  toLinearMap := twistor4ToPenroseCarrier
  invFun := penroseCarrierToTwistor4
  left_inv := penroseCarrierToTwistor4_twistor4ToPenroseCarrier
  right_inv := twistor4ToPenroseCarrier_penroseCarrierToTwistor4

/-- The Hermitian `(2,2)` self-pairing on the flattened carrier has real part
exactly equal to the direct real split-signature expression on the two spinor
sheets. -/
theorem helicity_flatten_eq_splitSignature (Z : Twistor4) :
    helicity (twistor4ToPenroseCarrier Z) = penroseRealSplitSignature Z := by
  simp [helicity, twistorHermitian_apply, twistor4ToPenroseCarrier,
    penroseRealSplitSignature, Fin.sum_univ_four, Complex.normSq]
  ring

/-- The bundled real Penrose quadratic form is exactly the split sheet
signature after the canonical flattening. -/
theorem penroseQuadraticForm_flatten_eq_splitSignature (Z : Twistor4) :
    twistorRealQuadraticForm (twistor4ToPenroseCarrier Z) =
      penroseRealSplitSignature Z := by
  rw [twistorRealQuadraticForm_apply, helicity_flatten_eq_splitSignature]

/-- Crown boundary identity at the finite quadratic level: the bundled Penrose
quadratic form equals the reduced norm of the explicit Witt-polarized Zorn
representative. -/
theorem penroseQuadraticForm_eq_wittZornNorm (Z : Twistor4) :
    twistorRealQuadraticForm (twistor4ToPenroseCarrier Z) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (penroseWittZornMap Z) := by
  rw [penroseQuadraticForm_flatten_eq_splitSignature,
    penroseWittZorn_norm_eq_splitSignature]

/-- Penrose nullness is therefore exactly Zorn reduced-norm zero after the
Witt polarization. -/
theorem penroseQuadraticNull_iff_wittZornNull (Z : Twistor4) :
    twistorRealQuadraticForm (twistor4ToPenroseCarrier Z) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (penroseWittZornMap Z) = 0 := by
  rw [penroseQuadraticForm_eq_wittZornNorm]

end InfoGeometry.Twistor.PenroseHermitianZornBoundaryBridge
