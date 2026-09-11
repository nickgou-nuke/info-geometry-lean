import InfoGeometry.Canonical.SuperchargeCentralChargeClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation

noncomputable section

/-!
# Dirac/Fredholm central-charge morphism

This file only packages morphisms already owned by the repository.  The
operatorial charge is the analytical index of a real split-Krein Dirac
Fredholm module; its operator-valued readout is the integer cast times the
identity.  The CPT supercharge square then reads as a kinetic term plus this
central operator.  No identification with a Virasoro scalar central charge
is asserted here.
-/

namespace InfoGeometry.Canonical.CentralChargeDiracMorphismBridge

open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein
open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The scalar-to-operator central-charge morphism. -/
noncomputable def integerCentralChargeMorphism : ℤ →+ EndH where
  toFun z := (z : ℝ) • (1 : EndH)
  map_zero' := by
    norm_num
    exact zero_smul ℝ (1 : EndH)
  map_add' z w := by
    simpa only [Int.cast_add] using
      (add_smul (z : ℝ) (w : ℝ) (1 : EndH))

@[simp] theorem integerCentralChargeMorphism_apply (z : ℤ) :
    integerCentralChargeMorphism (E := E) z = (z : ℝ) • (1 : EndH) := by
  rfl

/-- The operatorial charge is exactly the Fredholm/Dirac analytical index. -/
@[simp] theorem operatorialCentralCharge_eq_diracAnalyticalIndex
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    operatorialCentralCharge (A := A) (B := B) (E := E) X hX = X.analyticalIndex hX := by
  rfl

/-- The operator-valued charge factors through the integer central-charge map. -/
@[simp] theorem operatorialCentralChargeOperator_eq_integerMorphism
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX =
      integerCentralChargeMorphism (E := E)
        (operatorialCentralCharge (A := A) (B := B) (E := E) X hX) := by
  rfl

/-- The Fredholm/Dirac central operator is central on the whole carrier. -/
theorem operatorialCentralChargeOperator_central
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) (Y : EndH) :
    Commute
      (integerCentralChargeMorphism (E := E)
        (operatorialCentralCharge (A := A) (B := B) (E := E) X hX)) Y := by
  change Commute
    (operatorialCentralChargeOperator (A := A) (B := B) (E := E) X hX) Y
  exact operatorialCentralChargeOperator_commute (A := A) (B := B) (E := E) X hX Y

/-- The existing CPT square, expressed through the Dirac/Fredholm charge map. -/
theorem cptSupercharge_sq_eq_kinetic_plus_diracCentralOperator
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX +
        integerCentralChargeMorphism (E := E)
          (operatorialCentralCharge (A := A) (B := B) (E := E) X hX) := by
  simpa [operatorialCentralChargeOperator_eq_integerMorphism (A := A) (B := B) (E := E) X hX] using
    cptSupercharge_sq_eq_kinetic_plus_centralChargeOperator
      (A := A) (B := B) (E := E) X hX

/-! ## Cuntz chiral supercharge morphism -/

/-- A Cuntz `Q₊+Q₋` Dirac operator transports its square law through a ring map. -/
theorem ringHom_cuntz_chiralDirac_square_eq_image_one
    {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S)
    (g : CuntzO2Generators R)
    (hS1star_S1 : g.S1star * g.S1 = 1)
    (hS2star_S2 : g.S2star * g.S2 = 1)
    (hS1star_S2 : g.S1star * g.S2 = 0)
    (hS2star_S1 : g.S2star * g.S1 = 0)
    (hcompleteness : g.S1 * g.S1star + g.S2 * g.S2star = 1) :
    (φ (QPlus g) + φ (QMinus g)) * (φ (QPlus g) + φ (QMinus g)) = φ 1 := by
  have hQ : QPlus g * QPlus g = 0 :=
    qplus_nilpotent g hS2star_S1
  have hR : QMinus g * QMinus g = 0 :=
    qminus_nilpotent g hS1star_S2
  have hZ : QPlus g * QMinus g + QMinus g * QPlus g = 1 :=
    susy_hamiltonian_completeness g hS2star_S2 hS1star_S1 hcompleteness
  simpa using
    ringHom_preserves_recursive_nilpotent_centralCharge_square φ hQ hR hZ

/-- Central-extension form of the transported Cuntz Dirac square. -/
theorem ringHom_cuntz_chiralDirac_square_eq_image_even_plus_central
    {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S)
    (g : CuntzO2Generators R) (H Z : R)
    (hS1star_S1 : g.S1star * g.S1 = 1)
    (hS2star_S2 : g.S2star * g.S2 = 1)
    (hS1star_S2 : g.S1star * g.S2 = 0)
    (hS2star_S1 : g.S2star * g.S1 = 0)
    (hCentralSplit : QPlus g * QMinus g + QMinus g * QPlus g = H + Z) :
    (φ (QPlus g) + φ (QMinus g)) * (φ (QPlus g) + φ (QMinus g)) =
      φ H + φ Z := by
  have hQ : QPlus g * QPlus g = 0 :=
    qplus_nilpotent g hS2star_S1
  have hR : QMinus g * QMinus g = 0 :=
    qminus_nilpotent g hS1star_S2
  have hSq :=
    ringHom_preserves_recursive_nilpotent_centralCharge_square
      φ hQ hR hCentralSplit
  simpa [map_add] using hSq

/-- The Cuntz parity grading remains an involution after representation. -/
theorem ringHom_cuntz_parity_square_eq_image_one
    {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S)
    (g : CuntzO2Generators R)
    (hS1star_S1 : g.S1star * g.S1 = 1)
    (hS2star_S2 : g.S2star * g.S2 = 1)
    (hS1star_S2 : g.S1star * g.S2 = 0)
    (hS2star_S1 : g.S2star * g.S1 = 0)
    (hcompleteness : g.S1 * g.S1star + g.S2 * g.S2star = 1) :
    φ (ParityGrading g) * φ (ParityGrading g) = φ 1 := by
  have hΓ := parity_grading_square g hS1star_S1 hS2star_S2
    hS1star_S2 hS2star_S1 hcompleteness
  simpa using congrArg φ hΓ

/- The chiral components remain nilpotent after the same morphism. -/
theorem ringHom_cuntz_chiral_supercharges_nilpotent
    {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S)
    (g : CuntzO2Generators R)
    (hS1star_S2 : g.S1star * g.S2 = 0)
    (hS2star_S1 : g.S2star * g.S1 = 0) :
    (φ (QPlus g) * φ (QPlus g) = 0) ∧
      (φ (QMinus g) * φ (QMinus g) = 0) := by
  constructor
  · rw [← map_mul, qplus_nilpotent g hS2star_S1, map_zero]
  · rw [← map_mul, qminus_nilpotent g hS1star_S2, map_zero]

end InfoGeometry.Canonical.CentralChargeDiracMorphismBridge
