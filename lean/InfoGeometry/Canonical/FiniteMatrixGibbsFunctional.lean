import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite matrix Gibbs functionals

This file gives the native finite-stage construction for an arbitrary
self-adjoint complex matrix Hamiltonian.  The weight is defined by the
continuous functional calculus; no diagonalisation, witness structure, or
analytic completion is introduced here.
-/

noncomputable section

open scoped MatrixOrder ComplexOrder
open Matrix

namespace InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

def expWeight (β : ℝ) : ℝ → ℝ := fun r => Real.exp (-β * r)

def gibbsDensity {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : Matrix n n ℂ :=
  hH.cfc (expWeight β)

theorem gibbsDensity_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    0 ≤ gibbsDensity H hH β := by
  rw [gibbsDensity, ← hH.cfc_eq]
  apply cfc_nonneg
  intro r hr
  exact (Real.exp_pos _).le

theorem gibbsDensity_strictlyPositive {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    IsStrictlyPositive (gibbsDensity H hH β) := by
  rw [gibbsDensity, ← hH.cfc_eq]
  have hcont : Continuous (expWeight β) := by
    unfold expWeight
    fun_prop
  apply (cfc_isStrictlyPositive_iff (expWeight β) H hcont.continuousOn).2
  intro r hr
  exact Real.exp_pos _

theorem gibbsDensity_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsDensity H hH β).IsHermitian := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    (gibbsDensity_nonneg H hH β)).isHermitian

theorem gibbsDensity_isUnit {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    IsUnit (gibbsDensity H hH β) :=
  (gibbsDensity_strictlyPositive H hH β).isUnit

theorem gibbsPartition_ne_zero {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace (gibbsDensity H hH β) ≠ 0 := by
  intro hz
  have hp : (gibbsDensity H hH β).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (gibbsDensity_nonneg H hH β)
  have hzero : gibbsDensity H hH β = 0 := hp.trace_eq_zero_iff.mp hz
  exact (gibbsDensity_isUnit H hH β).ne_zero hzero

def weightedTrace {n : Type*} [Fintype n]
    (D : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun X := Matrix.trace (D * X)
  map_add' X Y := by
    change Matrix.trace (D * (X + Y)) = _
    rw [mul_add, Matrix.trace_add]
  map_smul' c X := by
    change Matrix.trace (D * (c • X)) = _
    rw [Matrix.mul_smul, Matrix.trace_smul]
    rfl

@[simp] theorem weightedTrace_apply {n : Type*} [Fintype n]
    (D X : Matrix n n ℂ) :
    weightedTrace D X = Matrix.trace (D * X) := rfl

theorem weightedTrace_nonneg_complex {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.PosSemidef)
    (X : Matrix n n ℂ) :
    0 ≤ weightedTrace D (star X * X) := by
  obtain ⟨S, hS⟩ :=
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg)
  have htrace : Matrix.trace (D * (star X * X)) =
      Matrix.trace (star (X * star S) * (X * star S)) := by
    rw [hS]
    calc
      Matrix.trace (star S * S * (star X * X)) =
          Matrix.trace (S * (star X * X) * star S) := by
            symm
            exact Matrix.trace_mul_cycle S (star X * X) (star S)
      _ = Matrix.trace (star (X * star S) * (X * star S)) := by
            simp [Matrix.star_mul, Matrix.mul_assoc]
  rw [weightedTrace_apply, htrace]
  have hp : 0 ≤ star (X * star S) * (X * star S) :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨X * star S, rfl⟩
  have hps : (star (X * star S) * (X * star S)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hp
  exact hps.trace_nonneg

theorem weightedTrace_nonneg {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (D : Matrix n n ℂ) (hD : D.PosSemidef)
    (X : Matrix n n ℂ) :
    0 ≤ (weightedTrace D (star X * X)).re := by
  exact (RCLike.nonneg_iff.mp (weightedTrace_nonneg_complex D hD X)).1

def gibbsFunctional {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix n n ℂ →ₗ[ℂ] ℂ :=
  (Matrix.trace (gibbsDensity H hH β))⁻¹ • weightedTrace (gibbsDensity H hH β)

@[simp] theorem gibbsFunctional_apply {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (β : ℝ) (X : Matrix n n ℂ) :
    gibbsFunctional H hH β X =
      (Matrix.trace (gibbsDensity H hH β))⁻¹ *
        Matrix.trace (gibbsDensity H hH β * X) := by
  simp [gibbsFunctional, weightedTrace_apply]

theorem gibbsFunctional_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsFunctional H hH β 1 = 1 := by
  rw [gibbsFunctional_apply, mul_one, inv_mul_cancel₀ (gibbsPartition_ne_zero H hH β)]

theorem gibbsFunctional_star {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X : Matrix n n ℂ) :
    gibbsFunctional H hH β (star X) =
      star (gibbsFunctional H hH β X) := by
  rw [gibbsFunctional_apply, gibbsFunctional_apply]
  let D := gibbsDensity H hH β
  have hD : star D = D := (gibbsDensity_isHermitian H hH β)
  have htrace : Matrix.trace (D * star X) =
      star (Matrix.trace (D * X)) := by
    calc
      Matrix.trace (D * star X) = Matrix.trace (star X * D) :=
        Matrix.trace_mul_comm D (star X)
      _ = Matrix.trace (star (D * X)) := by
        simp [Matrix.star_mul, hD]
      _ = star (Matrix.trace (D * X)) := by
        rw [← Matrix.trace_conjTranspose]
        rfl
  have hden : star (Matrix.trace D) = Matrix.trace D := by
    calc
      star (Matrix.trace D) = Matrix.trace (star D) := by
        rw [← Matrix.trace_conjTranspose]
        rfl
      _ = Matrix.trace D := congrArg Matrix.trace hD
  simp [D, htrace, hden]

theorem gibbsFunctional_positive {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X : Matrix n n ℂ) :
    0 ≤ (gibbsFunctional H hH β (star X * X)).re := by
  rw [gibbsFunctional_apply]
  have hD : (gibbsDensity H hH β).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (gibbsDensity_nonneg H hH β)
  have hden : 0 ≤ Matrix.trace (gibbsDensity H hH β) := hD.trace_nonneg
  have hinv : 0 ≤ (Matrix.trace (gibbsDensity H hH β))⁻¹ := inv_nonneg.mpr hden
  have hnumC : 0 ≤ weightedTrace (gibbsDensity H hH β) (star X * X) :=
    weightedTrace_nonneg_complex (gibbsDensity H hH β) hD X
  have hprod : 0 ≤ (Matrix.trace (gibbsDensity H hH β))⁻¹ *
      weightedTrace (gibbsDensity H hH β) (star X * X) :=
    mul_nonneg hinv hnumC
  exact (RCLike.nonneg_iff.mp hprod).1

/-! Finite Gibbs stationarity is the algebraic commutator consequence of
cyclicity of the matrix trace and the fact that the functional-calculus
density commutes with its self-adjoint Hamiltonian.  This is a stationarity
identity, not the analytic strip formulation of the full KMS condition. -/

theorem gibbsFunctional_commutator_zero {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X : Matrix n n ℂ) :
    gibbsFunctional H hH β (H * X - X * H) = 0 := by
  rw [gibbsFunctional_apply]
  let D := gibbsDensity H hH β
  have hcomm : Commute D H := by
    change Commute (hH.cfc (expWeight β)) H
    rw [← hH.cfc_eq]
    have hsa : IsSelfAdjoint H := hH
    exact hsa.commute_cfc (Commute.refl H) (expWeight β)
  have h₁ : Matrix.trace (D * H * X) = Matrix.trace (X * D * H) := by
    exact Matrix.trace_mul_cycle D H X
  have h₂ : Matrix.trace (D * X * H) = Matrix.trace (X * H * D) := by
    exact Matrix.trace_mul_cycle D X H |>.trans (Matrix.trace_mul_cycle H D X)
  have htrace : Matrix.trace (D * (H * X - X * H)) = 0 := by
    have htrace' : Matrix.trace (D * H * X) - Matrix.trace (D * X * H) = 0 := by
      rw [h₁, h₂]
      rw [mul_assoc X D H, hcomm.eq]
      simp only [mul_assoc, sub_self]
    rw [mul_sub, Matrix.trace_sub]
    simpa only [mul_assoc] using htrace'
  rw [htrace]
  simp

/-! ### Delta-first finite KMS boundary identity

For a finite matrix algebra with faithful density `D`, the modular boundary
map is inner conjugation `X ↦ D * X * D⁻¹`.  The KMS identity is a direct
consequence of cyclicity of the matrix trace.  This is the finite-dimensional
algebraic boundary identity; no logarithm or analytic strip extension is used.
-/

/-- Mathlib's native conjugation action specialized to an invertible matrix. -/
def unitImaginaryTimeAlgEquiv {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
  MulSemiringAction.toAlgEquiv ℂ (Matrix n n ℂ) (ConjAct.toConjAct u)

@[simp]
theorem unitImaginaryTimeAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (X : Matrix n n ℂ) :
    unitImaginaryTimeAlgEquiv u X =
      (u : Matrix n n ℂ) * X * ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) :=
  rfl

/-- Cyclicity and the native unit inverse law prove the density-weighted KMS
boundary identity. -/
theorem weightedTrace_kms_of_unit {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (X Y : Matrix n n ℂ) :
    weightedTrace (u : Matrix n n ℂ) (X * Y) =
      weightedTrace (u : Matrix n n ℂ)
        (Y * unitImaginaryTimeAlgEquiv u X) := by
  rw [weightedTrace_apply, weightedTrace_apply, unitImaginaryTimeAlgEquiv_apply]
  calc
    Matrix.trace ((u : Matrix n n ℂ) * (X * Y)) =
        Matrix.trace (((u : Matrix n n ℂ) * X) * Y) := by rw [mul_assoc]
    _ = Matrix.trace (Y * ((u : Matrix n n ℂ) * X)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((u : Matrix n n ℂ) *
          (Y * ((u : Matrix n n ℂ) * X *
            ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)))) := by
      symm
      calc
        Matrix.trace
            ((u : Matrix n n ℂ) *
              (Y * ((u : Matrix n n ℂ) * X *
                ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)))) =
            Matrix.trace
              (((u : Matrix n n ℂ) * Y) *
                ((u : Matrix n n ℂ) * X) *
                ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)) := by
          simp only [mul_assoc]
        _ = Matrix.trace
              (((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) *
                ((u : Matrix n n ℂ) * Y) *
                ((u : Matrix n n ℂ) * X)) :=
          Matrix.trace_mul_cycle _ _ _
        _ = Matrix.trace (Y * ((u : Matrix n n ℂ) * X)) := by
          simp only [← mul_assoc, Units.inv_mul, one_mul]

/-- The strictly positive Gibbs density represented as a native unit. -/
def gibbsDensityUnit {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : (Matrix n n ℂ)ˣ :=
  (gibbsDensity_isUnit H hH β).unit

@[simp]
theorem gibbsDensityUnit_coe {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsDensityUnit H hH β : Matrix n n ℂ) = gibbsDensity H hH β := by
  simp [gibbsDensityUnit]

/-- The Gibbs imaginary-time boundary automorphism is constructed from the
primary density, without introducing `log D`. -/
def gibbsImaginaryTimeAlgEquiv {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
  unitImaginaryTimeAlgEquiv (gibbsDensityUnit H hH β)

@[simp]
theorem gibbsImaginaryTimeAlgEquiv_apply {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (X : Matrix n n ℂ) :
    gibbsImaginaryTimeAlgEquiv H hH β X =
      gibbsDensity H hH β * X *
        (((gibbsDensityUnit H hH β)⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) := by
  rw [gibbsImaginaryTimeAlgEquiv, unitImaginaryTimeAlgEquiv_apply,
    gibbsDensityUnit_coe]

/-- The normalized finite Gibbs functional satisfies the genuine algebraic
KMS boundary identity. -/
theorem gibbsFunctional_kms {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X Y : Matrix n n ℂ) :
    gibbsFunctional H hH β (X * Y) =
      gibbsFunctional H hH β
        (Y * gibbsImaginaryTimeAlgEquiv H hH β X) := by
  have hKMS := weightedTrace_kms_of_unit
    (gibbsDensityUnit H hH β) X Y
  rw [gibbsDensityUnit_coe] at hKMS
  simpa [gibbsFunctional, gibbsImaginaryTimeAlgEquiv] using
    congrArg
      (fun z : ℂ => (Matrix.trace (gibbsDensity H hH β))⁻¹ * z)
      hKMS

/-! A single finite-stage packet for downstream transport.  Every component is
proved on the same matrix carrier, so the packet does not introduce a second
state or operator representation. -/

theorem finite_gibbs_functional_capstone
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X Y : Matrix n n ℂ) :
    gibbsFunctional H hH β 1 = 1 ∧
      0 ≤ (gibbsFunctional H hH β (star X * X)).re ∧
      gibbsFunctional H hH β (star X) =
        star (gibbsFunctional H hH β X) ∧
      gibbsFunctional H hH β (H * X - X * H) = 0 ∧
      gibbsFunctional H hH β (X * Y) =
        gibbsFunctional H hH β
          (Y * gibbsImaginaryTimeAlgEquiv H hH β X) :=
  ⟨gibbsFunctional_one H hH β,
    gibbsFunctional_positive H hH β X,
    gibbsFunctional_star H hH β X,
    gibbsFunctional_commutator_zero H hH β X,
    gibbsFunctional_kms H hH β X Y⟩

end InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
