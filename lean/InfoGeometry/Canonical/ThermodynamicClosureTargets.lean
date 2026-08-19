import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ThermodynamicClosureTargets

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Cartan-even operator predicate relative to a grading `Γ`.
-/
@[rep_depth krein]
def isEven (Γ X : EndH) : Prop :=
  X * Γ = Γ * X

/--
Cartan-odd operator predicate relative to a grading `Γ`.
-/
@[rep_depth krein]
def isOdd (Γ X : EndH) : Prop :=
  X * Γ = -(Γ * X)

/--
Submodule carrier of Cartan-even operators for a fixed grading `Γ`.
-/
@[rep_depth krein]
def EvenSector (Γ : EndH) : Submodule ℝ EndH where
  carrier := {X | isEven (E := E) Γ X}
  zero_mem' := by
    simp [isEven]
  add_mem' := by
    intro X Y hX hY
    unfold isEven at hX hY ⊢
    calc
      (X + Y) * Γ = X * Γ + Y * Γ := by simp [add_mul]
      _ = Γ * X + Γ * Y := by rw [hX, hY]
      _ = Γ * (X + Y) := by simp [mul_add]
  smul_mem' := by
    intro a X hX
    unfold isEven at hX ⊢
    calc
      (a • X) * Γ = a • (X * Γ) := by simp
      _ = a • (Γ * X) := by rw [hX]
      _ = Γ * (a • X) := by simp

/--
Submodule carrier of Cartan-odd operators for a fixed grading `Γ`.
-/
@[rep_depth krein]
def OddSector (Γ : EndH) : Submodule ℝ EndH where
  carrier := {X | isOdd (E := E) Γ X}
  zero_mem' := by
    simp [isOdd]
  add_mem' := by
    intro X Y hX hY
    unfold isOdd at hX hY ⊢
    calc
      (X + Y) * Γ = X * Γ + Y * Γ := by simp [add_mul]
      _ = -(Γ * X) + -(Γ * Y) := by rw [hX, hY]
      _ = -((Γ * X) + (Γ * Y)) := by
            rw [← neg_add]
      _ = -(Γ * (X + Y)) := by simp [mul_add]
  smul_mem' := by
    intro a X hX
    unfold isOdd at hX ⊢
    calc
      (a • X) * Γ = a • (X * Γ) := by simp
      _ = a • (-(Γ * X)) := by rw [hX]
      _ = -(Γ * (a • X)) := by simp

/--
Norm of the canonical Drazin-lane defect-central channel.

This is the scalar defect-energy readout used by closure targets.
-/
@[rep_depth krein]
noncomputable def defectCentralNorm
    (CIK : CertifiedInverseKernel H₂) : ℝ :=
  ‖DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral (CIK := CIK)‖

/--
Projector-mismatch anomaly on the Drazin/MP lane:
`χ := [P_D, P_MP]`.
-/
@[rep_depth krein]
noncomputable def projectorMismatchAnomaly
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  DrazinSupercharge.commutator CIK.spectralProjector CIK.mpRangeProjector

/--
Defect-augmented free-energy functional:
`β * KL + λ * ‖Z_D‖`.
-/
@[rep_depth transport]
noncomputable def defectAugmentedFreeEnergy
    (KLterm : CertifiedInverseKernel H₂ → ℝ)
    (β lam : ℝ)
    (CIK : CertifiedInverseKernel H₂) : ℝ :=
  β * KLterm CIK + lam * defectCentralNorm (E := E) CIK

/--
Constructive monotonicity criterion for the defect-augmented objective:
if one Sinkhorn-like step is nonincreasing on both the KL term and the defect
central norm, then the combined objective is nonincreasing.
-/
@[rep_depth transport]
theorem sinkhornStep_nonincreasing_defectAugmentedFreeEnergy_of_component_bounds
    (step : CertifiedInverseKernel H₂ → CertifiedInverseKernel H₂)
    (KLterm : CertifiedInverseKernel H₂ → ℝ)
    (β lam : ℝ)
    (hBeta : 0 ≤ β)
    (hLam : 0 ≤ lam)
    (hKL :
      ∀ CIK : CertifiedInverseKernel H₂,
        KLterm (step CIK) ≤ KLterm CIK)
    (hDefect :
      ∀ CIK : CertifiedInverseKernel H₂,
        defectCentralNorm (E := E) (step CIK) ≤ defectCentralNorm (E := E) CIK) :
    (∀ CIK : CertifiedInverseKernel H₂,
      defectAugmentedFreeEnergy (E := E) KLterm β lam (step CIK)
        ≤ defectAugmentedFreeEnergy (E := E) KLterm β lam CIK) := by
  intro CIK
  unfold defectAugmentedFreeEnergy
  have hKLscaled : β * KLterm (step CIK) ≤ β * KLterm CIK :=
    mul_le_mul_of_nonneg_left (hKL CIK) hBeta
  have hDefectScaled :
      lam * defectCentralNorm (E := E) (step CIK)
        ≤ lam * defectCentralNorm (E := E) CIK :=
    mul_le_mul_of_nonneg_left (hDefect CIK) hLam
  exact add_le_add hKLscaled hDefectScaled

/-- Vanishing closure: zero router residual satisfies the defect-central bound. -/
@[rep_depth transport, capstone]
theorem norm_zero_routerResidual_bounded_by_defectCentral
    (routerResidual : CertifiedInverseKernel H₂ → EndH)
    (hZero : ∀ CIK : CertifiedInverseKernel H₂, routerResidual CIK = 0) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ CIK : CertifiedInverseKernel H₂,
        ‖routerResidual CIK‖ ≤ c * defectCentralNorm (E := E) CIK := by
  refine ⟨1, zero_le_one, ?_⟩
  intro CIK
  rw [hZero CIK, norm_zero, one_mul]
  exact norm_nonneg _

/--
Target surface: in the operatorial scale/shape split, a scalar Weyl-scale
coefficient exists that dominates the defect-central norm.
-/
theorem commutator_even_even_isEven
    (Γ X Y : EndH)
    (hX : isEven (E := E) Γ X)
    (hY : isEven (E := E) Γ Y) :
    isEven (E := E) Γ (DrazinSupercharge.commutator X Y) := by
  unfold isEven at hX hY ⊢
  dsimp [DrazinSupercharge.commutator]
  calc
    (X * Y - Y * X) * Γ = X * (Y * Γ) - Y * (X * Γ) := by
      rw [sub_mul, mul_assoc, mul_assoc]
    _ = X * (Γ * Y) - Y * (Γ * X) := by rw [hY, hX]
    _ = Γ * (X * Y - Y * X) := by
      have hXY : X * (Γ * Y) = Γ * (X * Y) := by
        rw [← mul_assoc, hX, mul_assoc]
      have hYX : Y * (Γ * X) = Γ * (Y * X) := by
        rw [← mul_assoc, hY, mul_assoc]
      rw [hXY, hYX, mul_sub]

theorem commutator_even_odd_isOdd
    (Γ X Y : EndH)
    (hX : isEven (E := E) Γ X)
    (hY : isOdd (E := E) Γ Y) :
    isOdd (E := E) Γ (DrazinSupercharge.commutator X Y) := by
  unfold isEven at hX
  unfold isOdd at hY ⊢
  dsimp [DrazinSupercharge.commutator]
  calc
    (X * Y - Y * X) * Γ = X * (Y * Γ) - Y * (X * Γ) := by
      rw [sub_mul, mul_assoc, mul_assoc]
    _ = X * (-(Γ * Y)) - Y * (Γ * X) := by rw [hY, hX]
    _ = -(Γ * (X * Y - Y * X)) := by
      have hXY : X * (-(Γ * Y)) = -(Γ * (X * Y)) := by
        rw [mul_neg, ← mul_assoc, hX, mul_assoc]
      have hYX : Y * (Γ * X) = -(Γ * (Y * X)) := by
        rw [← mul_assoc, hY, neg_mul, mul_assoc]
      rw [hXY, hYX]
      rw [mul_sub]
      abel

theorem commutator_odd_odd_isEven
    (Γ X Y : EndH)
    (hX : isOdd (E := E) Γ X)
    (hY : isOdd (E := E) Γ Y) :
    isEven (E := E) Γ (DrazinSupercharge.commutator X Y) := by
  unfold isOdd at hX
  unfold isOdd at hY
  unfold isEven at ⊢
  dsimp [DrazinSupercharge.commutator]
  calc
    (X * Y - Y * X) * Γ = X * (Y * Γ) - Y * (X * Γ) := by
      rw [sub_mul, mul_assoc, mul_assoc]
    _ = X * (-(Γ * Y)) - Y * (-(Γ * X)) := by rw [hY, hX]
    _ = Γ * (X * Y - Y * X) := by
      have hXY : X * (-(Γ * Y)) = Γ * (X * Y) := by
        rw [mul_neg, ← mul_assoc, hX, neg_mul, neg_neg, mul_assoc]
      have hYX : Y * (-(Γ * X)) = Γ * (Y * X) := by
        rw [mul_neg, ← mul_assoc, hY, neg_mul, neg_neg, mul_assoc]
      rw [hXY, hYX]
      rw [mul_sub]

end Core

end InfoGeometry.Canonical.ThermodynamicClosureTargets
