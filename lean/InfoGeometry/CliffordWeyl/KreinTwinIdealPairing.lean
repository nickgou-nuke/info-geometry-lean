/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.DiracPeircePairing
import InfoGeometry.Algebra.IdempotentCornerCommutant
import InfoGeometry.Krein.ExchangedProjectionPairing

/-!
# Twin ideals for an exchanged Dirac adjoint

The existing algebraic Dirac adjoint gives the real bilinear form
`B X Y = τ (X * K.diracAdjoint Y)` for any real linear functional `τ`.
If `τ` is cyclic and `K.diracAdjoint P = 1 - P`, left multiplication by
`P` has complementary bilinear adjoint. Its two actual range submodules,
the right ideals `P A` and `(1-P) A`, are therefore totally isotropic.

For the full algebra of real finite matrices, trace separation proves ambient
nondegeneracy. The generic exchanged-projection theorem then constructs a
perfect pairing between the two ideals. Neither nondegeneracy nor a dimension
condition is hidden in a new structure field.

The adjoint reverses product order. Under the exchanged-projection hypothesis,
it preserves each off-diagonal Peirce sector and exchanges the diagonal
sectors. This differs from the existing self-adjoint-projector case.
Preservation of the pairing by Dirac-unitary left multiplication is algebraic;
no bound in a positive norm or identification with modular time is asserted.
-/

noncomputable section

namespace InfoGeometry.CliffordWeyl.KreinTwinIdealPairing

open InfoGeometry.Physics
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Algebra.IdempotentCornerCommutant

section Adjoint

variable {A : Type*} [Ring A] [StarRing A]
variable (K : KasparovKreinData A)

@[simp] theorem diracAdjoint_zero : K.diracAdjoint 0 = 0 := by
  simp [KasparovKreinData.diracAdjoint]

@[simp] theorem diracAdjoint_add (X Y : A) :
    K.diracAdjoint (X + Y) = K.diracAdjoint X + K.diracAdjoint Y := by
  simp only [KasparovKreinData.diracAdjoint, star_add, mul_add, add_mul]

theorem adjoint_complement_of_exchanged (P : A)
    (hAdj : K.diracAdjoint P = 1 - P) : K.diracAdjoint (1 - P) = P := by
  rw [← hAdj, K.diracAdjoint_involution]

/-- Reversal turns `P A` into the complementary left ideal `A (1-P)`. -/
theorem adjoint_mem_left_complement_iff (P X : A)
    (hAdj : K.diracAdjoint P = 1 - P) :
    K.diracAdjoint X ∈ principalLeftIdeal (1 - P) ↔ X ∈ principalRightIdeal P := by
  change K.diracAdjoint X * (1 - P) = K.diracAdjoint X ↔ P * X = X
  constructor
  · intro h
    have h' := congrArg K.diracAdjoint h
    simpa only [K.diracAdjoint_mul, adjoint_complement_of_exchanged K P hAdj,
      K.diracAdjoint_involution] using h'
  · intro h
    rw [← hAdj, ← K.diracAdjoint_mul, h]

/-- Diagonal corners are exchanged when the two idempotents are exchanged. -/
theorem adjoint_component11_of_exchanged (P X : A)
    (hAdj : K.diracAdjoint P = 1 - P) :
    K.diracAdjoint (component11 P X) = component00 P (K.diracAdjoint X) := by
  unfold component11 component00 complementIdempotent
  rw [K.diracAdjoint_diagonal_sandwich, hAdj]

/-- Reversal of product order cancels exchange of the two end projectors. -/
theorem adjoint_component10_of_exchanged (P X : A)
    (hAdj : K.diracAdjoint P = 1 - P) :
    K.diracAdjoint (component10 P X) = component10 P (K.diracAdjoint X) := by
  rw [K.diracAdjoint_component10, hAdj]
  simp [component01, component10, complementIdempotent]

/-- The other off-diagonal sector is preserved as well. -/
theorem adjoint_component01_of_exchanged (P X : A)
    (hAdj : K.diracAdjoint P = 1 - P) :
    K.diracAdjoint (component01 P X) = component01 P (K.diracAdjoint X) := by
  rw [K.diracAdjoint_component01, hAdj]
  simp [component01, component10, complementIdempotent]

/-- A nonzero off-diagonal element cannot be sent to the opposite sector. -/
theorem offDiagonal_eq_zero_of_adjoint_opposite (P X : A)
    (hP : P * P = P) (hAdj : K.diracAdjoint P = 1 - P)
    (hX : component10 P X = X)
    (hOpposite : component01 P (K.diracAdjoint X) = K.diracAdjoint X) : X = 0 := by
  have hFixed : component10 P (K.diracAdjoint X) = K.diracAdjoint X := by
    rw [← adjoint_component10_of_exchanged K P X hAdj, hX]
  have hPQ : P * (1 - P) = 0 := by
    simpa only [complementIdempotent] using idempotent_mul_complement P hP
  have hZero : K.diracAdjoint X = 0 := by
    calc
      K.diracAdjoint X = P * K.diracAdjoint X * (1 - P) := hFixed.symm
      _ = P * ((1 - P) * K.diracAdjoint X * P) * (1 - P) := by
        rw [show (1 - P) * K.diracAdjoint X * P = K.diracAdjoint X from hOpposite]
      _ = (P * (1 - P)) * K.diracAdjoint X * (P * (1 - P)) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hPQ]; simp
  have h := congrArg K.diracAdjoint hZero
  simpa only [K.diracAdjoint_involution, diracAdjoint_zero] using h

end Adjoint

section RealAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]
variable (K : KasparovKreinData A) (τ : A →ₗ[ℝ] ℝ)

@[simp] theorem diracAdjoint_smul (r : ℝ) (X : A) :
    K.diracAdjoint (r • X) = r • K.diracAdjoint X := by
  simp [KasparovKreinData.diracAdjoint, star_smul]

/-- The actual real bilinear Dirac pairing on the complete algebra carrier. -/
def pairing : LinearMap.BilinForm ℝ A where
  toFun X :=
    { toFun := fun Y => τ (X * K.diracAdjoint Y)
      map_add' := by
        intro Y Z
        simp only [diracAdjoint_add, mul_add, map_add]
      map_smul' := by
        intro r Y
        change τ (X * K.diracAdjoint (r • Y)) = r • τ (X * K.diracAdjoint Y)
        simp only [diracAdjoint_smul, mul_smul_comm, map_smul] }
  map_add' := by
    intro X Y
    ext Z
    change τ ((X + Y) * K.diracAdjoint Z) =
      τ (X * K.diracAdjoint Z) + τ (Y * K.diracAdjoint Z)
    simp only [add_mul, map_add]
  map_smul' := by
    intro r X
    ext Y
    change τ ((r • X) * K.diracAdjoint Y) = r • τ (X * K.diracAdjoint Y)
    simp only [smul_mul_assoc, map_smul]

@[simp] theorem pairing_apply (X Y : A) :
    pairing K τ X Y = τ (X * K.diracAdjoint Y) := rfl

/-- Cyclicity moves the left projector to the adjointed argument. -/
theorem pairing_mul_left
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : A) (hAdj : K.diracAdjoint P = 1 - P) (X Y : A) :
    pairing K τ (P * X) Y = pairing K τ X ((1 - P) * Y) := by
  change τ (P * X * K.diracAdjoint Y) = τ (X * K.diracAdjoint ((1 - P) * Y))
  rw [K.diracAdjoint_mul, adjoint_complement_of_exchanged K P hAdj]
  calc
    τ (P * X * K.diracAdjoint Y) = τ (P * (X * K.diracAdjoint Y)) := by
      rw [mul_assoc]
    _ = τ ((X * K.diracAdjoint Y) * P) := hτ _ _
    _ = τ (X * (K.diracAdjoint Y * P)) := by rw [mul_assoc]

omit [StarRing A] [StarModule ℝ A] in
/-- The algebra idempotent gives a genuine idempotent endomorphism. -/
theorem mulLeft_isIdempotent (P : A) (hP : P * P = P) :
    IsIdempotentElem (LinearMap.mulLeft ℝ P) := by
  ext X
  change P * (P * X) = P * X
  rw [← mul_assoc, hP]

omit [StarRing A] [StarModule ℝ A] in
/-- The range used by the generic theorem is the actual principal right ideal. -/
theorem range_mulLeft_eq_principalRightIdeal (P : A) (hP : P * P = P) :
    (LinearMap.range (LinearMap.mulLeft ℝ P) : Set A) = principalRightIdeal P := by
  ext X
  change (∃ Y, P * Y = X) ↔ P * X = X
  constructor
  · rintro ⟨Y, rfl⟩
    rw [← mul_assoc, hP]
  · intro hX
    exact ⟨X, hX⟩

/-- The exact hypothesis required by the generic exchanged-projection theorem. -/
theorem mulLeft_pairing_adjoint
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : A) (hAdj : K.diracAdjoint P = 1 - P) (X Y : A) :
    pairing K τ ((LinearMap.mulLeft ℝ P) X) Y =
      pairing K τ X ((1 - LinearMap.mulLeft ℝ P) Y) := by
  change pairing K τ (P * X) Y = pairing K τ X (Y - P * Y)
  simpa only [sub_mul, one_mul] using pairing_mul_left K τ hτ P hAdj X Y

/-- Every two vectors in `P A` have zero pairing, not merely zero self-pairing. -/
theorem principalRightIdeal_pairing_eq_zero
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : A) (hP : P * P = P) (hAdj : K.diracAdjoint P = 1 - P)
    (X Y : A) (hX : X ∈ principalRightIdeal P) (hY : Y ∈ principalRightIdeal P) :
    pairing K τ X Y = 0 := by
  exact InfoGeometry.Krein.ExchangedProjectionPairing.range_pairing_eq_zero
    (pairing K τ) (LinearMap.mulLeft ℝ P) (mulLeft_isIdempotent P hP)
    (mulLeft_pairing_adjoint K τ hτ P hAdj)
    ⟨X, ⟨X, hX⟩⟩ ⟨Y, ⟨Y, hY⟩⟩

/-- The complementary principal right ideal is totally isotropic as well. -/
theorem complementRightIdeal_pairing_eq_zero
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (P : A) (hP : P * P = P) (hAdj : K.diracAdjoint P = 1 - P)
    (X Y : A)
    (hX : X ∈ principalRightIdeal (1 - P))
    (hY : Y ∈ principalRightIdeal (1 - P)) : pairing K τ X Y = 0 := by
  apply principalRightIdeal_pairing_eq_zero K τ hτ (1 - P)
    (by simpa only [complementIdempotent] using complementIdempotent_sq P hP)
    (by simpa using adjoint_complement_of_exchanged K P hAdj) X Y hX hY

/-- A left Dirac-unitary identity suffices to preserve the cyclic pairing. -/
theorem pairing_left_unitary
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (U : A) (hU : K.diracAdjoint U * U = 1) (X Y : A) :
    pairing K τ (U * X) (U * Y) = pairing K τ X Y := by
  change τ ((U * X) * K.diracAdjoint (U * Y)) = τ (X * K.diracAdjoint Y)
  rw [K.diracAdjoint_mul]
  calc
    τ ((U * X) * (K.diracAdjoint Y * K.diracAdjoint U)) =
        τ (U * (X * K.diracAdjoint Y * K.diracAdjoint U)) := by
          simp only [mul_assoc]
    _ = τ ((X * K.diracAdjoint Y * K.diracAdjoint U) * U) := hτ _ _
    _ = τ (X * K.diracAdjoint Y) := by simp only [mul_assoc, hU, mul_one]

/-- The two unitary identities construct an actual linear equivalence. -/
def unitaryLeftEquiv (U : A)
    (hLeft : K.diracAdjoint U * U = 1) (hRight : U * K.diracAdjoint U = 1) :
    A ≃ₗ[ℝ] A where
  toFun X := U * X
  invFun X := K.diracAdjoint U * X
  left_inv X := by simp only [← mul_assoc, hLeft, one_mul]
  right_inv X := by simp only [← mul_assoc, hRight, one_mul]
  map_add' := mul_add U
  map_smul' r X := mul_smul_comm r U X

omit [StarModule ℝ A] in
@[simp] theorem unitaryLeftEquiv_apply (U : A)
    (hLeft : K.diracAdjoint U * U = 1) (hRight : U * K.diracAdjoint U = 1) (X : A) :
    unitaryLeftEquiv K U hLeft hRight X = U * X := rfl

omit [StarModule ℝ A] in
@[simp] theorem unitaryLeftEquiv_symm_apply (U : A)
    (hLeft : K.diracAdjoint U * U = 1) (hRight : U * K.diracAdjoint U = 1) (X : A) :
    (unitaryLeftEquiv K U hLeft hRight).symm X = K.diracAdjoint U * X := rfl

end RealAlgebra

section RealMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (K : KasparovKreinData (Matrix n n ℝ))

/-- On the full real matrix algebra, trace and the involutive adjoint separate both arguments. -/
theorem matrix_pairing_nondegenerate :
    (pairing K (Matrix.traceLinearMap n ℝ ℝ)).Nondegenerate := by
  constructor
  · intro X hX
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    have h := hX (K.diracAdjoint Y)
    simpa only [pairing_apply, Matrix.traceLinearMap_apply,
      K.diracAdjoint_involution, zero_mul, Matrix.trace_zero] using h
  · intro Y hY
    have hZero : K.diracAdjoint Y = 0 := by
      apply Matrix.ext_iff_trace_mul_left.mpr
      intro X
      have h := hY X
      simpa only [pairing_apply, Matrix.traceLinearMap_apply,
        mul_zero, Matrix.trace_zero] using h
    have h := congrArg K.diracAdjoint hZero
    simpa only [K.diracAdjoint_involution, diracAdjoint_zero] using h

/-- The actual two right ideals of the full matrix algebra have a perfect cross pairing. -/
theorem matrix_crossPairing_isPerfPair
    (P : Matrix n n ℝ) (hP : P * P = P) (hAdj : K.diracAdjoint P = 1 - P) :
    (InfoGeometry.Krein.ExchangedProjectionPairing.crossPairing
      (pairing K (Matrix.traceLinearMap n ℝ ℝ)) (LinearMap.mulLeft ℝ P)).IsPerfPair := by
  apply InfoGeometry.Krein.ExchangedProjectionPairing.crossPairing_isPerfPair
    (pairing K (Matrix.traceLinearMap n ℝ ℝ)) (LinearMap.mulLeft ℝ P)
    (mulLeft_isIdempotent P hP)
    (mulLeft_pairing_adjoint K (Matrix.traceLinearMap n ℝ ℝ)
      Matrix.trace_mul_comm P hAdj)
    (matrix_pairing_nondegenerate K)

end RealMatrix

/-- The real matrix carrier used below contains genuinely noncommuting elements. -/
theorem exists_real_noncommuting_pair :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℝ, X * Y ≠ Y * X := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 1, 0], ?_⟩
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- A concrete full `2 × 2` real matrix model discharges the exchanged-idempotent
hypotheses, and its two nonzero ideal vectors have nonzero cross pairing. -/
theorem exchanged_matrix_example :
    ∃ (K : KasparovKreinData (Matrix (Fin 2) (Fin 2) ℝ))
      (P : Matrix (Fin 2) (Fin 2) ℝ),
      P * P = P ∧ K.diracAdjoint P = 1 - P ∧ P ≠ 0 ∧ 1 - P ≠ 0 ∧
      pairing K (Matrix.traceLinearMap (Fin 2) ℝ ℝ) P (1 - P) = 1 := by
  let η : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  have hηsq : η * η = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [η, Matrix.mul_apply, Fin.sum_univ_two]
  have hηstar : star η = η := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [η, Matrix.star_apply]
  let K : KasparovKreinData (Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨⟨η, 1⟩, by
      refine ⟨hηsq, hηstar, ?_, ?_⟩ <;> simp⟩
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  have hPsq : P * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hPstar : star P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.star_apply]
  have hPAdj : K.diracAdjoint P = 1 - P := by
    change η * star P * η = 1 - P
    rw [hPstar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, η, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨K, P, hPsq, hPAdj, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [P] at h'
  · intro h
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
    norm_num [P] at h'
  · change Matrix.trace (P * K.diracAdjoint (1 - P)) = 1
    rw [adjoint_complement_of_exchanged K P hPAdj, hPsq]
    norm_num [P, Matrix.trace, Fin.sum_univ_two]

end InfoGeometry.CliffordWeyl.KreinTwinIdealPairing
