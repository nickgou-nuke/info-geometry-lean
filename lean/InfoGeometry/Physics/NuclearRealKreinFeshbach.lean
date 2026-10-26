/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachSymmetry
import InfoGeometry.Krein.KreinSpace

/-!
# Exact Feshbach reduction with the native real Krein adjoint

The bounded operators below forget exactly to the existing algebraic Feshbach
operators. Their adjoint is the owned `KreinSpace.kreinAdjoint`, not a new star
instance on the real bounded-operator algebra. A self-adjoint denominator and
a supported right inverse suffice to derive the inverse's Krein adjoint and
the matching left inverse. These statements assert neither positivity nor a
real spectral theorem for arbitrary Krein-self-adjoint operators.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRealKreinFeshbach

open InfoGeometry.Krein
open KreinSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [CompleteSpace V] [KreinSpace V]

/-- Unit notation in the bounded-operator algebra has the owned Krein adjoint. -/
@[simp] theorem kreinAdjoint_one : kreinAdjoint (1 : V →L[ℝ] V) = 1 := by
  change kreinAdjoint (ContinuousLinearMap.id ℝ V) = ContinuousLinearMap.id ℝ V
  exact kreinAdjoint_id

/-- The bounded native-real version of the existing complementary denominator. -/
def denominator (P H : V →L[ℝ] V) (E : ℝ) : V →L[ℝ] V :=
  E • (1 - P) - (1 - P) * H * (1 - P)

/-- The bounded native-real version of the existing effective Hamiltonian. -/
def effectiveHamiltonian (P H R : V →L[ℝ] V) : V →L[ℝ] V :=
  P * H * P + P * H * R * H * P

/-- The bounded native-real version of the existing reconstruction map. -/
def waveOperator (P H R : V →L[ℝ] V) : V →L[ℝ] V := P + R * H * P

@[simp] theorem denominator_toLinearMap (P H : V →L[ℝ] V) (E : ℝ) :
    (denominator P H E).toLinearMap =
      NuclearFeshbachReduction.denominator P.toLinearMap H.toLinearMap E := rfl

@[simp] theorem effectiveHamiltonian_toLinearMap (P H R : V →L[ℝ] V) :
    (effectiveHamiltonian P H R).toLinearMap =
      NuclearFeshbachReduction.effectiveHamiltonian
        P.toLinearMap H.toLinearMap R.toLinearMap := rfl

@[simp] theorem waveOperator_toLinearMap (P H R : V →L[ℝ] V) :
    (waveOperator P H R).toLinearMap =
      NuclearFeshbachReduction.waveOperator
        P.toLinearMap H.toLinearMap R.toLinearMap := rfl

/-- The owned corner-inverse uniqueness theorem applies to the actual Krein
adjoint, without replacing the bounded operator algebra's existing star. -/
theorem cornerInverse_kreinAdjoint (Q D R : V →L[ℝ] V)
    (hQ : kreinAdjoint Q = Q) (hD : kreinAdjoint D = D)
    (hQR : Q * R = R) (hDR : D * R = Q) : kreinAdjoint R = R := by
  apply NuclearFeshbachSymmetry.cornerInverse_unique Q D (kreinAdjoint R) R
  · simpa only [kreinAdjoint_mul, hQ] using congrArg kreinAdjoint hQR
  · exact hQR
  · simpa only [kreinAdjoint_mul, hD, hQ] using congrArg kreinAdjoint hDR
  · exact hDR

theorem denominator_kreinAdjoint (P H : V →L[ℝ] V) (E : ℝ)
    (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H) :
    kreinAdjoint (denominator P H E) = denominator P H E := by
  simp only [denominator, kreinAdjoint_sub, kreinAdjoint_smul,
    kreinAdjoint_mul, kreinAdjoint_one, hP, hH]
  noncomm_ring

/-- A supported inverse at a real energy is Krein-self-adjoint when the
Hamiltonian and model projection are Krein-self-adjoint. -/
theorem resolvent_kreinAdjoint (P H R : V →L[ℝ] V) (E : ℝ)
    (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    kreinAdjoint R = R :=
  cornerInverse_kreinAdjoint (1 - P) (denominator P H E) R
    (by simp only [kreinAdjoint_sub, kreinAdjoint_one, hP])
    (denominator_kreinAdjoint P H E hP hH) hQR hDR

/-- Adjoint coherence also derives the missing right support equation. -/
theorem resolvent_mul_complement (P H R : V →L[ℝ] V) (E : ℝ)
    (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    R * (1 - P) = R := by
  have hR := resolvent_kreinAdjoint P H R E hP hH hQR hDR
  simpa only [kreinAdjoint_mul, kreinAdjoint_sub, kreinAdjoint_one, hP, hR]
    using congrArg kreinAdjoint hQR

/-- Adjoint coherence derives the left inverse needed for reconstruction of
all full eigenvectors, not only the right-inverse reduction direction. -/
theorem resolvent_mul_denominator (P H R : V →L[ℝ] V) (E : ℝ)
    (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    R * denominator P H E = 1 - P := by
  have hR := resolvent_kreinAdjoint P H R E hP hH hQR hDR
  have hD := denominator_kreinAdjoint P H E hP hH
  simpa only [kreinAdjoint_mul, kreinAdjoint_sub, kreinAdjoint_one, hP, hR, hD]
    using congrArg kreinAdjoint hDR

/-- The exact energy-dependent correction preserves the native Krein adjoint. -/
theorem effectiveHamiltonian_kreinSelfAdjoint
    (P H R : V →L[ℝ] V) (E : ℝ)
    (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    IsKreinSelfAdjoint (effectiveHamiltonian P H R) := by
  have hR := resolvent_kreinAdjoint P H R E hP hH hQR hDR
  change kreinAdjoint (effectiveHamiltonian P H R) = effectiveHamiltonian P H R
  simp only [effectiveHamiltonian, kreinAdjoint_add, kreinAdjoint_mul, hP, hH, hR]
  noncomm_ring

/-- The bounded formulation has exactly the already-proved algebraic spectral
equation; no new spectral hypothesis is hidden in the carrier conversion. -/
theorem eigen_equation_iff (P H R : V →L[ℝ] V) (E : ℝ)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P)
    (v : V) (hv : P v = v) :
    H (waveOperator P H R v) = E • waveOperator P H R v ↔
      effectiveHamiltonian P H R v = E • v := by
  exact NuclearFeshbachReduction.eigen_equation_iff
    P.toLinearMap H.toLinearMap R.toLinearMap E
    (congrArg ContinuousLinearMap.toLinearMap hQR)
    (congrArg ContinuousLinearMap.toLinearMap hDR) v hv

/-- The native Krein hypotheses make the right-inverse data sufficient for
full reconstruction, by deriving the left inverse rather than assuming it. -/
theorem reconstruct_eigenvector (P H R : V →L[ℝ] V) (E : ℝ)
    (hPP : P * P = P) (hP : kreinAdjoint P = P) (hH : kreinAdjoint H = H)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P)
    (ψ : V) (hψ : H ψ = E • ψ) : waveOperator P H R (P ψ) = ψ := by
  exact NuclearFeshbachReduction.reconstruct_eigenvector
    P.toLinearMap H.toLinearMap R.toLinearMap E
    (congrArg ContinuousLinearMap.toLinearMap hPP)
    (congrArg ContinuousLinearMap.toLinearMap
      (resolvent_mul_complement P H R E hP hH hQR hDR))
    (congrArg ContinuousLinearMap.toLinearMap
      (resolvent_mul_denominator P H R E hP hH hQR hDR)) ψ hψ

end InfoGeometry.Physics.NuclearRealKreinFeshbach
