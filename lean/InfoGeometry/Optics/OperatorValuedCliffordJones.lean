import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution
import InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry
import InfoGeometry.Optics.SheetWittCircularBasis

/-!
# Operator-valued Clifford--Jones polarization calculus

This is the representation bridge from the generic operator-valued coordinate
owner in `Clifford.OperatorValuedJones` to the repository's constructive
chiral-projector and projective-Jones interfaces.  It also supplies the finite
algebraic joint projector calculus for commuting hyperbolic and elliptic axes.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorValuedCliffordJones

open Matrix
open InfoGeometry.Clifford

variable {B : Type*} [Ring B] [Algebra ℂ B]

abbrev SheetMatrix (B : Type*) := Matrix (Fin 2) (Fin 2) B

/-! ## The represented `Cl(1,1)` packet -/

abbrev sheetIdentity : SheetMatrix B := I_mat
abbrev sheetGamma : SheetMatrix B := Gamma_mat
abbrev sheetJ : SheetMatrix B := J_mat
abbrev sheetGammaJ : SheetMatrix B := K_mat

/-- The complex circular involution `-i ΓJ`. -/
def sheetCircular : SheetMatrix B :=
  !![0, -(algebraMap ℂ B Complex.I); algebraMap ℂ B Complex.I, 0]

@[simp] theorem sheetGamma_sq :
    sheetGamma (B := B) * sheetGamma = sheetIdentity :=
  Gamma_sq

@[simp] theorem sheetJ_sq :
    sheetJ (B := B) * sheetJ = sheetIdentity :=
  J_sq

@[simp] theorem sheetGammaJ_sq :
    sheetGammaJ (B := B) * sheetGammaJ = -sheetIdentity :=
  K_sq

theorem sheetJ_mul_sheetGamma :
    sheetJ (B := B) * sheetGamma = -(sheetGamma * sheetJ) :=
  J_Gamma

theorem sheetGammaJ_eq :
    sheetGammaJ (B := B) = sheetGamma * sheetJ :=
  K_eq_Gamma_J

@[simp] theorem sheetCircular_sq :
    sheetCircular (B := B) * sheetCircular = sheetIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetCircular, sheetIdentity, I_mat, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    rw [← map_mul, Complex.I_mul_I, map_neg] <;> simp

@[simp] theorem sheetIdentity_eq_one :
    sheetIdentity (B := B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sheetIdentity, I_mat]

/-! ## Coordinate-owner readback -/

abbrev OperatorCoordinates (B : Type*) := CausalOperatorCoordinates B

abbrev reconstructOperator : OperatorCoordinates B → SheetMatrix B :=
  reconstruct_causal

abbrev operatorCoordinates : SheetMatrix B → OperatorCoordinates B :=
  causalCoordinates

/-- The full operator-valued sheet space is exactly the four-coordinate packet. -/
noncomputable def operatorCoordinatesEquiv :
    OperatorCoordinates B ≃ SheetMatrix B :=
  causalOperatorCoordinatesEquiv

@[simp] theorem reconstruct_operatorCoordinates (A : SheetMatrix B) :
    reconstructOperator (operatorCoordinates A) = A :=
  reconstruct_causalCoordinates A

@[simp] theorem operatorCoordinates_reconstruct (c : OperatorCoordinates B) :
    operatorCoordinates (reconstructOperator c) = c :=
  causalCoordinates_reconstruct c

/-- Reconstruction in the ordered packet `(1, Γ, J, -iΓJ)`. -/
theorem reconstructOperator_eq_packet (c : OperatorCoordinates B) :
    reconstructOperator c =
      c.scalar • sheetIdentity + c.chiral • sheetGamma +
        c.exchange • sheetJ + c.circular • sheetCircular := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstructOperator, reconstruct_causal, sheetIdentity, I_mat,
      sheetGamma, Gamma_mat, sheetJ, J_mat, sheetCircular, sheetGammaJ, K_mat,
      Matrix.smul_apply, Algebra.smul_def, Algebra.commutes] <;>
    abel

/-! ## Chiral and projective-Jones interfaces -/

/-- The sheet grading as the repository's constructive chiral involution. -/
def sheetChiralInvolution :
    InfoGeometry.OperatorAlgebra.ChiralInvolution (SheetMatrix B) where
  chi := sheetGamma
  chi_sq := by
    rw [← sheetIdentity_eq_one (B := B)]
    exact sheetGamma_sq (B := B)

/-- The circular axis as a second constructive chiral involution. -/
def circularChiralInvolution :
    InfoGeometry.OperatorAlgebra.ChiralInvolution (SheetMatrix B) where
  chi := sheetCircular
  chi_sq := by
    rw [← sheetIdentity_eq_one (B := B)]
    exact sheetCircular_sq (B := B)

/-- The sheet involution exported as a projective Jones Cartan axis. -/
def sheetJonesAxis :
    InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry.JonesCartanAxis
      (SheetMatrix B) where
  chi := sheetGamma
  chi_sq := (sheetChiralInvolution (B := B)).chi_sq
  P_left := (sheetChiralInvolution (B := B)).Pleft
  P_right := (sheetChiralInvolution (B := B)).Pright
  P_left_idem := (sheetChiralInvolution (B := B)).Pleft_idem
  P_right_idem := (sheetChiralInvolution (B := B)).Pright_idem
  complementary := (sheetChiralInvolution (B := B)).Pleft_add_Pright
  left_right_zero := (sheetChiralInvolution (B := B)).Pleft_mul_Pright
  right_left_zero := (sheetChiralInvolution (B := B)).Pright_mul_Pleft

/-! ## Projective two-sheet readout -/

abbrev ComplexSheetMatrix := Matrix (Fin 2) (Fin 2) ℂ

def sheetRatio (ψ : Fin 2 → ℂ) : ℂ := ψ 1 / ψ 0

def mobiusReadout (G : ComplexSheetMatrix) (z : ℂ) : ℂ :=
  (G 1 0 + G 1 1 * z) / (G 0 0 + G 0 1 * z)

theorem sheetRatio_mulVec_eq_mobiusReadout
    (G : ComplexSheetMatrix) (ψ : Fin 2 → ℂ)
    (hψ : ψ 0 ≠ 0) :
    sheetRatio (G.mulVec ψ) = mobiusReadout G (sheetRatio ψ) := by
  simp [sheetRatio, mobiusReadout, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  field_simp [hψ]

/-! ## Commuting hyperbolic/elliptic axes -/

/-- Algebraic data for a hyperbolic axis and a commuting elliptic axis. -/
structure LoxodromicAxes (B : Type*) [Ring B] [Algebra ℂ B] where
  hyperbolic : B
  elliptic : B
  hyperbolic_sq : hyperbolic * hyperbolic = 1
  elliptic_sq : elliptic * elliptic = -1
  commute : hyperbolic * elliptic = elliptic * hyperbolic

namespace LoxodromicAxes

variable (L : LoxodromicAxes B)

/-- `iC` is the involution associated with the elliptic axis `C²=-1`. -/
def ellipticInvolution : B := Complex.I • L.elliptic

@[simp] theorem ellipticInvolution_sq :
    L.ellipticInvolution * L.ellipticInvolution = 1 := by
  calc
    L.ellipticInvolution * L.ellipticInvolution
        = (Complex.I * Complex.I) • (L.elliptic * L.elliptic) := by
            rw [ellipticInvolution, smul_mul_smul]
    _ = (-1 : ℂ) • (-1 : B) := by
          rw [Complex.I_mul_I, L.elliptic_sq]
    _ = 1 := by simp

theorem hyperbolic_commutes_ellipticInvolution :
    L.hyperbolic * L.ellipticInvolution =
      L.ellipticInvolution * L.hyperbolic := by
  calc
    L.hyperbolic * L.ellipticInvolution
        = Complex.I • (L.hyperbolic * L.elliptic) := by
            rw [ellipticInvolution, mul_smul_comm]
    _ = Complex.I • (L.elliptic * L.hyperbolic) := by rw [L.commute]
    _ = L.ellipticInvolution * L.hyperbolic := by
          rw [ellipticInvolution, smul_mul_assoc]

def hyperbolicChiral : InfoGeometry.OperatorAlgebra.ChiralInvolution B where
  chi := L.hyperbolic
  chi_sq := L.hyperbolic_sq

def ellipticChiral : InfoGeometry.OperatorAlgebra.ChiralInvolution B where
  chi := L.ellipticInvolution
  chi_sq := L.ellipticInvolution_sq

abbrev hyperbolicPlus : B := L.hyperbolicChiral.Pleft
abbrev hyperbolicMinus : B := L.hyperbolicChiral.Pright
abbrev circularPlus : B := L.ellipticChiral.Pleft
abbrev circularMinus : B := L.ellipticChiral.Pright

/-- Every hyperbolic spectral projector commutes with every circular projector. -/
theorem spectralProjectors_commute (hSign cSign : Bool) :
    (if hSign then L.hyperbolicPlus else L.hyperbolicMinus) *
        (if cSign then L.circularPlus else L.circularMinus) =
      (if cSign then L.circularPlus else L.circularMinus) *
        (if hSign then L.hyperbolicPlus else L.hyperbolicMinus) := by
  have hcomm := L.hyperbolic_commutes_ellipticInvolution
  cases hSign <;> cases cSign <;>
    dsimp [hyperbolicPlus, hyperbolicMinus, circularPlus, circularMinus,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright,
      hyperbolicChiral, ellipticChiral] <;>
    rw [smul_mul_smul, smul_mul_smul] <;>
    apply congrArg (fun z : B => ((1 / 2 : ℝ) * (1 / 2 : ℝ)) • z) <;>
    noncomm_ring [hcomm]

/-- Joint hyperbolic/circular spectral projector. -/
def commutingInvolutions :
    InfoGeometry.Optics.SheetWittCircularBasis.CommutingInvolutions B where
  hyperbolic := L.hyperbolic
  circular := L.ellipticInvolution
  hyperbolic_sq := L.hyperbolic_sq
  circular_sq := L.ellipticInvolution_sq
  commute := L.hyperbolic_commutes_ellipticInvolution
  projector_commute := by
    intro hSign cSign
    cases hSign <;> cases cSign
    · exact L.spectralProjectors_commute false false
    · exact L.spectralProjectors_commute false true
    · exact L.spectralProjectors_commute true false
    · exact L.spectralProjectors_commute true true

/-- Joint hyperbolic/circular spectral projector, delegated to the Witt/circular owner. -/
abbrev jointProjector (hSign cSign : Bool) : B :=
  L.commutingInvolutions.jointProjector hSign cSign

@[simp] theorem jointProjector_idempotent (hSign cSign : Bool) :
    L.jointProjector hSign cSign * L.jointProjector hSign cSign =
      L.jointProjector hSign cSign := by
  exact L.commutingInvolutions.jointProjector_idem hSign cSign

/-- The four joint modes resolve the identity. -/
theorem jointProjectors_sum :
    L.jointProjector true true + L.jointProjector true false +
        L.jointProjector false true + L.jointProjector false false = 1 := by
  exact L.commutingInvolutions.jointProjector_sum

end LoxodromicAxes

end InfoGeometry.Optics.OperatorValuedCliffordJones
