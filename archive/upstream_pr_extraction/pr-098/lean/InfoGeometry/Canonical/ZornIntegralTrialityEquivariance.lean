import InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

/-!
# Integral Zorn axis triality and Clifford equivariance

This file maps the external integral axis triality onto the canonical
polymorphic types. The cyclic permutation of axes is realized natively as an
`R`-linear equivalence on `ZornMatrix R`, which restricts perfectly to the
integers and commutes with the Clifford structure natively via functoriality.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornIntegralTrialityEquivariance

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Canonical.ZornIntegralSpinSubgroup
open InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

variable {R : Type*} [CommRing R]

attribute [local simp] ZornMatrix.smul_a ZornMatrix.smul_b ZornMatrix.smul_x ZornMatrix.smul_y Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

/-- Cyclic coordinate triality as an `R`-linear equivalence. -/
def zornTrialityEquiv : ZornMatrix R ≃ₗ[R] ZornMatrix R where
  toFun := zornTriality
  invFun Z := zornTriality (zornTriality Z)
  left_inv Z := zornTriality_order_three Z
  right_inv Z := by simp [zornTriality_order_three]
  map_add' X Y := by
    apply ZornMatrix.ext
    · simp [zornTriality]
    · simp [zornTriality]
    · ext i; fin_cases i <;> simp [zornTriality]
    · ext i; fin_cases i <;> simp [zornTriality]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [zornTriality]
    · simp [zornTriality]
    · ext i; fin_cases i <;> simp [zornTriality]
    · ext i; fin_cases i <;> simp [zornTriality]

def zornTrialityUnit : LinearMap.GeneralLinearGroup R (ZornMatrix R) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv zornTrialityEquiv

theorem zornTrialityUnit_pow_three : zornTrialityUnit (R := R) ^ 3 = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro X
  exact zornTriality_order_three X

theorem zornTriality_conj (Z : ZornMatrix R) :
    zornTriality (zornConj Z) = zornConj (zornTriality Z) := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

/-- Extending triality to the canonical 16-dimensional Dirac spinor carrier. -/
def diracAxisCycle (Ψ : DiracSpinor16 (R := R)) : DiracSpinor16 (R := R) :=
  (zornTriality Ψ.1, zornTriality Ψ.2)

theorem diracGamma_axis_covariant (V : ZornMatrix R) (Ψ : DiracSpinor16 (R := R)) :
    diracAxisCycle (diracGamma V Ψ) = diracGamma (zornTriality V) (diracAxisCycle Ψ) := by
  apply Prod.ext
  · exact zornTriality_mul V Ψ.2
  · change zornTriality (zornConj V * Ψ.1) = zornConj (zornTriality V) * zornTriality Ψ.1
    rw [zornTriality_mul, zornTriality_conj]

/-- The integral axis cycle is exactly the generic triality restricted to ℤ.
It faithfully intertwines with real scalar extension and the real Clifford representation. -/
theorem integral_axis_triality_clifford_closure (X : ZornMatrix ℤ) (Ψ : DiracSpinor16 (R := ℝ)) :
    zornTrialityUnit (R := ℤ) ^ 3 = 1 ∧
    zornNorm (R := ℤ) (zornTriality X) = zornNorm (R := ℤ) X ∧
    zornBaseChange (zornTriality X) = zornTriality (zornBaseChange X) ∧
    diracAxisCycle (diracGamma (zornBaseChange X) Ψ) =
      diracGamma (zornBaseChange (zornTriality X)) (diracAxisCycle Ψ) := by
  refine ⟨zornTrialityUnit_pow_three, zornTriality_norm X, zornBaseChange_triality X, ?_⟩
  rw [zornBaseChange_triality]
  exact diracGamma_axis_covariant _ _

end InfoGeometry.Canonical.ZornIntegralTrialityEquivariance

end noncomputable section
