import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.DoubledSpace
import Mathlib.LinearAlgebra.Trace

noncomputable section

namespace InfoGeometry.Krein.KreinAdjointCommutantBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

section FiniteDeterminant

variable [FiniteDimensional ℝ H]

/-- Finite-dimensional determinant readout of a continuous Krein operator. -/
noncomputable def finiteDet (A : H →L[ℝ] H) : ℝ :=
  LinearMap.det A.toLinearMap

omit [CompleteSpace H] [KreinSpace H] [FiniteDimensional ℝ H] in
theorem finiteDet_mul (A B : H →L[ℝ] H) :
    finiteDet (A.comp B) = finiteDet A * finiteDet B := by
  unfold finiteDet
  exact map_mul (LinearMap.det : (H →ₗ[ℝ] H) →* ℝ) A.toLinearMap B.toLinearMap

end FiniteDeterminant

/-- The canonical finite doubled carrier used for Krein matrix readouts. -/
abbrev FiniteDoubledCarrier (n : ℕ) :=
  DoubledSpace (EuclideanSpace ℝ (Fin n))

/-- The native Dirac/Krein fundamental symmetry on the finite doubled carrier. -/
noncomputable def finiteDoubledFundamentalSymmetry (n : ℕ) :
    FiniteDoubledCarrier n →L[ℝ] FiniteDoubledCarrier n :=
  spectral_epsilon (E := EuclideanSpace ℝ (Fin n))

@[simp] theorem finiteDoubledFundamentalSymmetry_involution (n : ℕ) :
    (finiteDoubledFundamentalSymmetry n).comp
        (finiteDoubledFundamentalSymmetry n) =
      ContinuousLinearMap.id ℝ (FiniteDoubledCarrier n) := by
  exact spectral_epsilon_involution (EuclideanSpace ℝ (Fin n))

/-! The involutive continuous map is also a genuine linear equivalence. -/
noncomputable def finiteDoubledFundamentalSymmetryEquiv (n : ℕ) :
    FiniteDoubledCarrier n ≃ₗ[ℝ] FiniteDoubledCarrier n := by
  apply LinearEquiv.ofInvolutive
    (finiteDoubledFundamentalSymmetry n).toLinearMap
  intro x
  have h := congrArg
    (fun T : FiniteDoubledCarrier n →L[ℝ] FiniteDoubledCarrier n => T x)
    (finiteDoubledFundamentalSymmetry_involution n)
  change finiteDoubledFundamentalSymmetry n
      (finiteDoubledFundamentalSymmetry n x) = x at h
  exact h

@[simp] theorem finiteDoubledFundamentalSymmetryEquiv_apply (n : ℕ)
    (x : FiniteDoubledCarrier n) :
    finiteDoubledFundamentalSymmetryEquiv n x =
      finiteDoubledFundamentalSymmetry n x := by
  rfl

theorem finiteDoubled_trace_conjugation_invariant (n : ℕ)
    (A : FiniteDoubledCarrier n →L[ℝ] FiniteDoubledCarrier n) :
    LinearMap.trace ℝ (FiniteDoubledCarrier n)
        ((finiteDoubledFundamentalSymmetryEquiv n).conj A.toLinearMap) =
      LinearMap.trace ℝ (FiniteDoubledCarrier n) A.toLinearMap := by
  exact LinearMap.trace_conj' A.toLinearMap
    (finiteDoubledFundamentalSymmetryEquiv n)

/-- Determinant readout on the canonical finite doubled carrier. -/
noncomputable def finiteDoubledDet (n : ℕ)
    (A : FiniteDoubledCarrier n →L[ℝ] FiniteDoubledCarrier n) : ℝ :=
  finiteDet A

theorem finiteDoubledDet_mul (n : ℕ)
    (A B : FiniteDoubledCarrier n →L[ℝ] FiniteDoubledCarrier n) :
    finiteDoubledDet n (A.comp B) =
      finiteDoubledDet n A * finiteDoubledDet n B := by
  exact finiteDet_mul A B

/-- The determinant of the finite fundamental symmetry is a square root of one.

This is the determinant-level consequence of the native Krein involution.  The
statement intentionally leaves the sign unresolved: choosing a basis and an
orientation is a separate readout choice, not part of the abstract Krein
carrier.
-/
theorem finiteDoubledDet_fundamentalSymmetry_sq (n : ℕ) :
    finiteDoubledDet n (finiteDoubledFundamentalSymmetry n) ^ 2 = 1 := by
  rw [pow_two, ← finiteDoubledDet_mul]
  rw [finiteDoubledFundamentalSymmetry_involution]
  simp [finiteDoubledDet, finiteDet]

/-- The finite fundamental symmetry is invertible at the determinant level. -/
theorem finiteDoubledDet_fundamentalSymmetry_ne_zero (n : ℕ) :
    finiteDoubledDet n (finiteDoubledFundamentalSymmetry n) ≠ 0 := by
  intro h
  have hsq := finiteDoubledDet_fundamentalSymmetry_sq n
  rw [h] at hsq
  norm_num at hsq

/-- The commutant of the fundamental Krein symmetry on continuous operators. -/
def CommutesWithFundamentalSymmetry (A : H →L[ℝ] H) : Prop :=
  A.comp (jCLM (H := H)) = (jCLM (H := H)).comp A

@[simp] theorem finiteKreinCommutant_zero :
    CommutesWithFundamentalSymmetry (0 : H →L[ℝ] H) := by
  simp [CommutesWithFundamentalSymmetry]

@[simp] theorem finiteKreinCommutant_one :
    CommutesWithFundamentalSymmetry (ContinuousLinearMap.id ℝ H) := by
  simp [CommutesWithFundamentalSymmetry]

/-- The fundamental-symmetry commutant is closed under addition. -/
theorem finiteKreinCommutant_add
    (A B : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A)
    (hB : CommutesWithFundamentalSymmetry B) :
    CommutesWithFundamentalSymmetry (A + B) := by
  change (A + B).comp (jCLM (H := H)) =
      (jCLM (H := H)).comp (A + B)
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hA, hB]

/-- The fundamental-symmetry commutant is closed under real scalar multiples. -/
theorem finiteKreinCommutant_smul
    (c : ℝ) (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    CommutesWithFundamentalSymmetry (c • A) := by
  change (c • A).comp (jCLM (H := H)) =
      (jCLM (H := H)).comp (c • A)
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hA]

/-- Hilbert adjunction preserves commutation with the self-adjoint fundamental
symmetry. -/
theorem adjoint_commutes_of_commutes
    (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    CommutesWithFundamentalSymmetry (ContinuousLinearMap.adjoint A) := by
  change (ContinuousLinearMap.adjoint A).comp (jCLM (H := H)) =
      (jCLM (H := H)).comp (ContinuousLinearMap.adjoint A)
  have h := congrArg ContinuousLinearMap.adjoint hA
  simpa [ContinuousLinearMap.adjoint_comp] using h.symm

/-- On the fundamental-symmetry commutant, the Krein adjoint reduces to the
Hilbert adjoint once the Hilbert adjoint itself commutes with the symmetry.

The hypothesis is explicit because commutation is not automatically preserved
by adjunction in an arbitrary noncommutative operator algebra. -/
theorem kreinAdjoint_eq_adjoint_of_adjoint_commutes
    (A : H →L[ℝ] H)
    (hAadj : CommutesWithFundamentalSymmetry (ContinuousLinearMap.adjoint A)) :
    kreinAdjoint A = ContinuousLinearMap.adjoint A := by
  change (jCLM (H := H)).comp
      ((ContinuousLinearMap.adjoint A).comp (jCLM (H := H))) =
      ContinuousLinearMap.adjoint A
  change (ContinuousLinearMap.adjoint A).comp (jCLM (H := H)) =
      (jCLM (H := H)).comp (ContinuousLinearMap.adjoint A) at hAadj
  rw [← ContinuousLinearMap.comp_assoc, ← hAadj]
  simp

/-- The commutant of the fundamental symmetry is closed under the Krein
adjoint. -/
theorem finiteKreinCommutant_kreinAdjoint
    (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    CommutesWithFundamentalSymmetry (kreinAdjoint A) := by
  have hAadj := adjoint_commutes_of_commutes A hA
  rw [kreinAdjoint_eq_adjoint_of_adjoint_commutes A hAadj]
  exact hAadj

/-- On the fundamental-symmetry commutant, Krein self-adjointness is exactly
Hilbert self-adjointness. -/
theorem finiteKreinCommutant_selfAdjoint_iff
    (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    IsKreinSelfAdjoint A ↔
      ContinuousLinearMap.adjoint A = A := by
  rw [IsKreinSelfAdjoint,
    kreinAdjoint_eq_adjoint_of_adjoint_commutes A
      (adjoint_commutes_of_commutes A hA)]

/-- The fundamental-symmetry commutant is closed under composition. -/
theorem finiteKreinCommutant_mul
    (A B : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A)
    (hB : CommutesWithFundamentalSymmetry B) :
    CommutesWithFundamentalSymmetry (A.comp B) := by
  change (A.comp B).comp (jCLM (H := H)) =
      (jCLM (H := H)).comp (A.comp B)
  rw [ContinuousLinearMap.comp_assoc, hB]
  rw [← ContinuousLinearMap.comp_assoc, hA]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The fundamental-symmetry commutant is closed under the operator commutator. -/
theorem finiteKreinCommutant_commutator
    (A B : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A)
    (hB : CommutesWithFundamentalSymmetry B) :
    CommutesWithFundamentalSymmetry (A * B - B * A) := by
  simpa [sub_eq_add_neg, one_smul] using
    (finiteKreinCommutant_add (A.comp B) ((-1 : ℝ) • (B.comp A))
      (finiteKreinCommutant_mul A B hA hB)
      (finiteKreinCommutant_smul (-1) (B.comp A)
      (finiteKreinCommutant_mul B A hB hA)))

/-- The symmetric Jordan product of two commutant operators remains in the
fundamental-symmetry commutant. -/
theorem finiteKreinCommutant_jordan
    (A B : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A)
    (hB : CommutesWithFundamentalSymmetry B) :
    CommutesWithFundamentalSymmetry
      ((1 / 2 : ℝ) • (A * B + B * A)) := by
  exact finiteKreinCommutant_smul (1 / 2 : ℝ) (A.comp B + B.comp A)
    (finiteKreinCommutant_add (A.comp B) (B.comp A)
      (finiteKreinCommutant_mul A B hA hB)
      (finiteKreinCommutant_mul B A hB hA))

/-- The Krein adjoint preserves the symmetric Jordan product. -/
theorem kreinAdjoint_jordan
    (A B : H →L[ℝ] H) :
    kreinAdjoint ((1 / 2 : ℝ) • (A * B + B * A)) =
      (1 / 2 : ℝ) •
        (kreinAdjoint A * kreinAdjoint B +
          kreinAdjoint B * kreinAdjoint A) := by
  simp [add_comm]

/-- The Jordan product of two commutant Krein-self-adjoint operators is again
Krein-self-adjoint. -/
theorem finiteKreinCommutant_jordan_selfAdjoint
    (A B : H →L[ℝ] H)
    (hA : IsKreinSelfAdjoint A)
    (hB : IsKreinSelfAdjoint B) :
    IsKreinSelfAdjoint ((1 / 2 : ℝ) • (A * B + B * A)) := by
  rw [IsKreinSelfAdjoint]
  rw [kreinAdjoint_jordan, hA, hB]

/-- The commutator of two Krein-self-adjoint operators is
Krein-skew-adjoint. -/
theorem finiteKreinCommutant_commutator_skewAdjoint
    (A B : H →L[ℝ] H)
    (hA : IsKreinSelfAdjoint A)
    (hB : IsKreinSelfAdjoint B) :
    IsKreinSkewAdjoint (A * B - B * A) := by
  rw [isKreinSkewAdjoint_iff_eq_neg, kreinAdjoint_sub,
    kreinAdjoint_mul, kreinAdjoint_mul, hA, hB]
  simp [sub_eq_add_neg]

end InfoGeometry.Krein.KreinAdjointCommutantBridge

end
