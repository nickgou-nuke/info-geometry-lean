/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachSymmetry
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.PontryaginSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

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

omit [CompleteSpace V] [KreinSpace V] in
@[simp] theorem denominator_toLinearMap (P H : V →L[ℝ] V) (E : ℝ) :
    (denominator P H E).toLinearMap =
      NuclearFeshbachReduction.denominator P.toLinearMap H.toLinearMap E := rfl

omit [CompleteSpace V] [KreinSpace V] in
@[simp] theorem effectiveHamiltonian_toLinearMap (P H R : V →L[ℝ] V) :
    (effectiveHamiltonian P H R).toLinearMap =
      NuclearFeshbachReduction.effectiveHamiltonian
        P.toLinearMap H.toLinearMap R.toLinearMap := rfl

omit [CompleteSpace V] [KreinSpace V] in
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

omit [CompleteSpace V] [KreinSpace V] in
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

/-! ## Nested-Projection Krein–Feshbach Schur Transitivity (`P₀ ≤ P₁ ≤ 1`) -/

section NestedKreinFeshbach

section RingAlgebraic

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [KreinSpace V] in
/-- Purely algebraic ring-level nested Schur transitivity over any associative `[Ring A]`,
requiring neither inner-product nor Krein structure. -/
theorem effectiveOperator_schur_transitive_ring {A : Type*} [Ring A]
    (P₀ P₁ H R₁ R₀₁ : A)
    (hP1 : P₁ * P₁ = P₁)
    (h_nestL : P₀ * P₁ = P₀) (h_nestR : P₁ * P₀ = P₀)
    (hSR01 : (P₁ - P₀) * R₀₁ = R₀₁) (hR01S : R₀₁ * (P₁ - P₀) = R₀₁) :
    let eff : A → A → A → A := fun P K R => P * K * P + P * K * R * K * P
    let H₁ := eff P₁ H R₁
    let R₀ := R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁)
    eff P₀ H R₀ = eff P₀ H₁ R₀₁ := by
  intro eff H₁ R₀
  have hP1S : P₁ * (P₁ - P₀) = P₁ - P₀ := by
    calc P₁ * (P₁ - P₀) = P₁ * P₁ - P₁ * P₀ := by noncomm_ring
      _ = P₁ - P₀ := by rw [hP1, h_nestR]
  have hSP1 : (P₁ - P₀) * P₁ = P₁ - P₀ := by
    calc (P₁ - P₀) * P₁ = P₁ * P₁ - P₀ * P₁ := by noncomm_ring
      _ = P₁ - P₀ := by rw [hP1, h_nestL]
  have hP1R01 : P₁ * R₀₁ = R₀₁ := by
    calc P₁ * R₀₁ = P₁ * ((P₁ - P₀) * R₀₁) := by rw [hSR01]
      _ = (P₁ * (P₁ - P₀)) * R₀₁ := (mul_assoc _ _ _).symm
      _ = (P₁ - P₀) * R₀₁ := by rw [hP1S]
      _ = R₀₁ := hSR01
  have hR01P1 : R₀₁ * P₁ = R₀₁ := by
    calc R₀₁ * P₁ = (R₀₁ * (P₁ - P₀)) * P₁ := by rw [hR01S]
      _ = R₀₁ * ((P₁ - P₀) * P₁) := mul_assoc _ _ _
      _ = R₀₁ * (P₁ - P₀) := by rw [hSP1]
      _ = R₀₁ := hR01S
  have h0H10 : P₀ * H₁ * P₀ = P₀ * H * P₀ + P₀ * H * R₁ * H * P₀ := by
    dsimp [H₁, eff]
    calc P₀ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) * P₀
        = (P₀ * P₁) * H * (P₁ * P₀) + (P₀ * P₁) * H * R₁ * H * (P₁ * P₀) := by noncomm_ring
      _ = P₀ * H * P₀ + P₀ * H * R₁ * H * P₀ := by rw [h_nestL, h_nestR]
  have h0H1R : P₀ * H₁ * R₀₁ = P₀ * H * (1 + R₁ * H) * R₀₁ := by
    dsimp [H₁, eff]
    calc P₀ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) * R₀₁
        = (P₀ * P₁) * H * (P₁ * R₀₁) + (P₀ * P₁) * H * R₁ * H * (P₁ * R₀₁) := by noncomm_ring
      _ = P₀ * H * R₀₁ + P₀ * H * R₁ * H * R₀₁ := by rw [h_nestL, hP1R01]
      _ = P₀ * H * (1 + R₁ * H) * R₀₁ := by noncomm_ring
  have hRH10 : R₀₁ * H₁ * P₀ = R₀₁ * (1 + H * R₁) * H * P₀ := by
    dsimp [H₁, eff]
    calc R₀₁ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) * P₀
        = (R₀₁ * P₁) * H * (P₁ * P₀) + (R₀₁ * P₁) * H * R₁ * H * (P₁ * P₀) := by noncomm_ring
      _ = R₀₁ * H * P₀ + R₀₁ * H * R₁ * H * P₀ := by rw [hR01P1, h_nestR]
      _ = R₀₁ * (1 + H * R₁) * H * P₀ := by noncomm_ring
  dsimp [eff, R₀]
  calc P₀ * H * P₀ + P₀ * H * (R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁)) * H * P₀
      = (P₀ * H * P₀ + P₀ * H * R₁ * H * P₀) +
          (P₀ * H * (1 + R₁ * H) * R₀₁) * ((1 + H * R₁) * H * P₀) := by noncomm_ring
    _ = P₀ * H₁ * P₀ + (P₀ * H₁ * R₀₁) * ((1 + H * R₁) * H * P₀) := by rw [h0H10, h0H1R]
    _ = P₀ * H₁ * P₀ + P₀ * H₁ * (R₀₁ * (1 + H * R₁) * H * P₀) := by noncomm_ring
    _ = P₀ * H₁ * P₀ + P₀ * H₁ * (R₀₁ * H₁ * P₀) := by rw [hRH10]
    _ = P₀ * H₁ * P₀ + P₀ * H₁ * R₀₁ * H₁ * P₀ := by noncomm_ring

end RingAlgebraic

/-- Intermediate shell projector `P₁ - P₀` between the IR model `P₀` and intermediate scale `P₁`. -/
def intermediateShell (P₀ P₁ : V →L[ℝ] V) : V →L[ℝ] V :=
  P₁ - P₀

/-- Schur-compressed denominator on the intermediate shell `P₁ - P₀`. -/
def intermediateDenominator (P₀ P₁ H₁ : V →L[ℝ] V) (E : ℝ) : V →L[ℝ] V :=
  E • intermediateShell P₀ P₁ - intermediateShell P₀ P₁ * H₁ * intermediateShell P₀ P₁

/-- Exact Banachiewicz / Frobenius–Schur 2×2 nested resolvent on `1 - P₀ = (P₁ - P₀) ⊕ (1 - P₁)`. -/
def nestedResolvent (H R₁ R₀₁ : V →L[ℝ] V) : V →L[ℝ] V :=
  R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁)

/-- For Krein-self-adjoint projections, `P₀ * P₁ = P₀` implies `P₁ * P₀ = P₀`. -/
theorem nested_mul_right (P₀ P₁ : V →L[ℝ] V)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁)
    (h_nest : P₀ * P₁ = P₀) : P₁ * P₀ = P₀ := by
  have h := congrArg kreinAdjoint h_nest
  simpa only [kreinAdjoint_mul, hP0_sa, hP1_sa] using h

section ShellIdentities

omit [CompleteSpace V] [KreinSpace V] in
theorem intermediateShell_idempotent (P₀ P₁ : V →L[ℝ] V)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hL : P₀ * P₁ = P₀) (hR : P₁ * P₀ = P₀) :
    intermediateShell P₀ P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ := by
  dsimp [intermediateShell]
  calc (P₁ - P₀) * (P₁ - P₀) = P₁ * P₁ - P₁ * P₀ - P₀ * P₁ + P₀ * P₀ := by noncomm_ring
    _ = P₁ - P₀ := by rw [hP1, hR, hL, hP0]; abel

theorem intermediateShell_kreinAdjoint (P₀ P₁ : V →L[ℝ] V)
    (hP0 : kreinAdjoint P₀ = P₀) (hP1 : kreinAdjoint P₁ = P₁) :
    kreinAdjoint (intermediateShell P₀ P₁) = intermediateShell P₀ P₁ := by
  simp only [intermediateShell, kreinAdjoint_sub, hP0, hP1]

omit [CompleteSpace V] [KreinSpace V] in
theorem intermediateShell_mul_outer (P₀ P₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁) (hL : P₀ * P₁ = P₀) :
    intermediateShell P₀ P₁ * (1 - P₁) = 0 := by
  dsimp [intermediateShell]
  calc (P₁ - P₀) * (1 - P₁) = P₁ - P₁ * P₁ - P₀ + P₀ * P₁ := by noncomm_ring
    _ = 0 := by rw [hP1, hL]; abel

omit [CompleteSpace V] [KreinSpace V] in
theorem outer_mul_intermediateShell (P₀ P₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁) (hR : P₁ * P₀ = P₀) :
    (1 - P₁) * intermediateShell P₀ P₁ = 0 := by
  dsimp [intermediateShell]
  calc (1 - P₁) * (P₁ - P₀) = P₁ - P₁ * P₁ - P₀ + P₁ * P₀ := by noncomm_ring
    _ = 0 := by rw [hP1, hR]; abel

omit [CompleteSpace V] [KreinSpace V] in
theorem intermediateShell_add_outer (P₀ P₁ : V →L[ℝ] V) :
    intermediateShell P₀ P₁ + (1 - P₁) = 1 - P₀ := by
  dsimp [intermediateShell]; abel

omit [CompleteSpace V] [KreinSpace V] in
theorem intermediateShell_mul_P1 (P₀ P₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁) (hL : P₀ * P₁ = P₀) :
    intermediateShell P₀ P₁ * P₁ = intermediateShell P₀ P₁ := by
  dsimp [intermediateShell]
  calc (P₁ - P₀) * P₁ = P₁ * P₁ - P₀ * P₁ := by noncomm_ring
    _ = P₁ - P₀ := by rw [hP1, hL]

omit [CompleteSpace V] [KreinSpace V] in
theorem P1_mul_intermediateShell (P₀ P₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁) (hR : P₁ * P₀ = P₀) :
    P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ := by
  dsimp [intermediateShell]
  calc P₁ * (P₁ - P₀) = P₁ * P₁ - P₁ * P₀ := by noncomm_ring
    _ = P₁ - P₀ := by rw [hP1, hR]

omit [CompleteSpace V] [KreinSpace V] in
theorem P0_mul_intermediateShell (P₀ P₁ : V →L[ℝ] V)
    (hP0 : P₀ * P₀ = P₀) (hL : P₀ * P₁ = P₀) :
    P₀ * intermediateShell P₀ P₁ = 0 := by
  dsimp [intermediateShell]
  calc P₀ * (P₁ - P₀) = P₀ * P₁ - P₀ * P₀ := by noncomm_ring
    _ = 0 := by rw [hL, hP0, sub_self]

omit [CompleteSpace V] [KreinSpace V] in
theorem intermediateShell_mul_P0 (P₀ P₁ : V →L[ℝ] V)
    (hP0 : P₀ * P₀ = P₀) (hR : P₁ * P₀ = P₀) :
    intermediateShell P₀ P₁ * P₀ = 0 := by
  dsimp [intermediateShell]
  calc (P₁ - P₀) * P₀ = P₁ * P₀ - P₀ * P₀ := by noncomm_ring
    _ = 0 := by rw [hR, hP0, sub_self]

end ShellIdentities

theorem intermediateDenominator_kreinAdjoint (P₀ P₁ H₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : kreinAdjoint P₀ = P₀) (hP1 : kreinAdjoint P₁ = P₁)
    (hH1 : kreinAdjoint H₁ = H₁) :
    kreinAdjoint (intermediateDenominator P₀ P₁ H₁ E) = intermediateDenominator P₀ P₁ H₁ E := by
  have hS := intermediateShell_kreinAdjoint P₀ P₁ hP0 hP1
  simp only [intermediateDenominator, kreinAdjoint_sub, kreinAdjoint_smul,
    kreinAdjoint_mul, hS, hH1]
  noncomm_ring

theorem intermediateResolvent_kreinAdjoint (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : kreinAdjoint P₀ = P₀) (hP1 : kreinAdjoint P₁ = P₁) (hH : kreinAdjoint H = H)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    kreinAdjoint R₀₁ = R₀₁ := by
  have hH1 := effectiveHamiltonian_kreinSelfAdjoint P₁ H R₁ E hP1 hH hQR1 hDR1
  exact cornerInverse_kreinAdjoint
    (intermediateShell P₀ P₁)
    (intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E)
    R₀₁
    (intermediateShell_kreinAdjoint P₀ P₁ hP0 hP1)
    (intermediateDenominator_kreinAdjoint P₀ P₁ (effectiveHamiltonian P₁ H R₁) E hP0 hP1 hH1)
    hSR01 hDR01

theorem intermediateResolvent_mul_shell (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : kreinAdjoint P₀ = P₀) (hP1 : kreinAdjoint P₁ = P₁) (hH : kreinAdjoint H = H)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    R₀₁ * intermediateShell P₀ P₁ = R₀₁ := by
  have hR01 := intermediateResolvent_kreinAdjoint P₀ P₁ H R₁ R₀₁ E hP0 hP1 hH hQR1 hDR1 hSR01 hDR01
  have hS := intermediateShell_kreinAdjoint P₀ P₁ hP0 hP1
  simpa only [kreinAdjoint_mul, hS, hR01] using congrArg kreinAdjoint hSR01

theorem intermediateResolvent_mul_denominator (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : kreinAdjoint P₀ = P₀) (hP1 : kreinAdjoint P₁ = P₁) (hH : kreinAdjoint H = H)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    R₀₁ * intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E =
      intermediateShell P₀ P₁ := by
  have hR01 := intermediateResolvent_kreinAdjoint P₀ P₁ H R₁ R₀₁ E hP0 hP1 hH hQR1 hDR1 hSR01 hDR01
  have hH1 := effectiveHamiltonian_kreinSelfAdjoint P₁ H R₁ E hP1 hH hQR1 hDR1
  have hD := intermediateDenominator_kreinAdjoint P₀ P₁ (effectiveHamiltonian P₁ H R₁) E hP0 hP1 hH1
  have hS := intermediateShell_kreinAdjoint P₀ P₁ hP0 hP1
  simpa only [kreinAdjoint_mul, hD, hR01, hS] using congrArg kreinAdjoint hDR01

omit [CompleteSpace V] [KreinSpace V] in
theorem nestedResolvent_support (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V)
    (hP0 : P₀ * P₀ = P₀)
    (h_nestL : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁) :
    (1 - P₀) * nestedResolvent H R₁ R₀₁ = nestedResolvent H R₁ R₀₁ := by
  have hQ0Q1 : (1 - P₀) * (1 - P₁) = 1 - P₁ := by
    calc (1 - P₀) * (1 - P₁) = 1 - P₁ - P₀ + P₀ * P₁ := by noncomm_ring
      _ = 1 - P₁ := by rw [h_nestL]; abel
  have hQ0R1 : (1 - P₀) * R₁ = R₁ := by
    calc (1 - P₀) * R₁ = (1 - P₀) * ((1 - P₁) * R₁) := by rw [hQR1]
      _ = ((1 - P₀) * (1 - P₁)) * R₁ := (mul_assoc _ _ _).symm
      _ = (1 - P₁) * R₁ := by rw [hQ0Q1]
      _ = R₁ := hQR1
  have hQ0S : (1 - P₀) * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ := by
    have hP0S := P0_mul_intermediateShell P₀ P₁ hP0 h_nestL
    calc (1 - P₀) * intermediateShell P₀ P₁
        = intermediateShell P₀ P₁ - P₀ * intermediateShell P₀ P₁ := by noncomm_ring
      _ = intermediateShell P₀ P₁ := by rw [hP0S, sub_zero]
  have hQ0R01 : (1 - P₀) * R₀₁ = R₀₁ := by
    calc (1 - P₀) * R₀₁ = (1 - P₀) * (intermediateShell P₀ P₁ * R₀₁) := by rw [hSR01]
      _ = ((1 - P₀) * intermediateShell P₀ P₁) * R₀₁ := (mul_assoc _ _ _).symm
      _ = intermediateShell P₀ P₁ * R₀₁ := by rw [hQ0S]
      _ = R₀₁ := hSR01
  dsimp [nestedResolvent]
  calc (1 - P₀) * (R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁))
      = (1 - P₀) * R₁ + ((1 - P₀) * R₀₁ + ((1 - P₀) * R₁) * H * R₀₁) * (1 + H * R₁) := by
          noncomm_ring
    _ = R₁ + (R₀₁ + R₁ * H * R₀₁) * (1 + H * R₁) := by rw [hQ0R1, hQ0R01]
    _ = R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁) := by noncomm_ring

omit [CompleteSpace V] [KreinSpace V] in
/-- Key Schur inverse identity: `nestedResolvent` is a supported right inverse of `denominator P₀ H E`. -/
theorem denominator_mul_nestedResolvent (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (h_nestL : P₀ * P₁ = P₀) (h_nestR : P₁ * P₀ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    denominator P₀ H E * nestedResolvent H R₁ R₀₁ = 1 - P₀ := by
  set S := intermediateShell P₀ P₁
  set Q₁ := (1 - P₁)
  set Q₀ := (1 - P₀)
  set H₁ := effectiveHamiltonian P₁ H R₁
  have hQ0_split : Q₀ = S + Q₁ := (intermediateShell_add_outer P₀ P₁).symm
  have hS_idem : S * S = S := intermediateShell_idempotent P₀ P₁ hP0 hP1 h_nestL h_nestR
  have hSQ1 : S * Q₁ = 0 := intermediateShell_mul_outer P₀ P₁ hP1 h_nestL
  have hQ1S : Q₁ * S = 0 := outer_mul_intermediateShell P₀ P₁ hP1 h_nestR
  have hSP1 : S * P₁ = S := intermediateShell_mul_P1 P₀ P₁ hP1 h_nestL
  have hP1S : P₁ * S = S := P1_mul_intermediateShell P₀ P₁ hP1 h_nestR
  have hSR1 : S * R₁ = 0 := by
    calc S * R₁ = S * (Q₁ * R₁) := by rw [hQR1]
      _ = (S * Q₁) * R₁ := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hSQ1, zero_mul]
  have hD0_R1 : denominator P₀ H E * R₁ = -S * H * R₁ + Q₁ := by
    have hD1_R1 : (E • Q₁ - Q₁ * H * Q₁) * R₁ = Q₁ := by
      simpa [denominator, Q₁] using hDR1
    calc denominator P₀ H E * R₁
        = (E • Q₀ - Q₀ * H * Q₀) * R₁ := rfl
      _ = (E • (S + Q₁) - (S + Q₁) * H * (S + Q₁)) * R₁ := by rw [hQ0_split]
      _ = E • (S * R₁) + E • (Q₁ * R₁) - S * H * (S * R₁) - S * H * (Q₁ * R₁) -
            Q₁ * H * (S * R₁) - Q₁ * H * (Q₁ * R₁) := by
            simp only [add_mul, mul_add, sub_mul, smul_add, smul_mul_assoc, mul_assoc]; abel
      _ = (E • (Q₁ * R₁) - Q₁ * H * (Q₁ * R₁)) - S * H * R₁ := by
            rw [hSR1, hQR1]
            simp only [smul_zero, mul_zero, zero_add, sub_zero]
            noncomm_ring
      _ = (E • Q₁ - Q₁ * H * Q₁) * R₁ - S * H * R₁ := by
            simp only [sub_mul, smul_mul_assoc, mul_assoc, hQR1]
      _ = Q₁ - S * H * R₁ := by rw [hD1_R1]
      _ = -S * H * R₁ + Q₁ := by noncomm_ring
  have hD0_block : denominator P₀ H E * (1 + R₁ * H) * S = intermediateDenominator P₀ P₁ H₁ E := by
    have hSH1S : S * H₁ * S = S * H * S + S * H * R₁ * H * S := by
      dsimp [H₁, effectiveHamiltonian]
      calc S * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) * S
          = (S * P₁) * H * (P₁ * S) + (S * P₁) * H * R₁ * H * (P₁ * S) := by noncomm_ring
        _ = S * H * S + S * H * R₁ * H * S := by rw [hSP1, hP1S]
    have hD0_S : denominator P₀ H E * S = E • S - S * H * S - Q₁ * H * S := by
      calc denominator P₀ H E * S
          = (E • Q₀ - Q₀ * H * Q₀) * S := rfl
        _ = (E • (S + Q₁) - (S + Q₁) * H * (S + Q₁)) * S := by rw [hQ0_split]
        _ = E • (S * S) + E • (Q₁ * S) - S * H * (S * S) - S * H * (Q₁ * S) -
              Q₁ * H * (S * S) - Q₁ * H * (Q₁ * S) := by
            simp only [add_mul, mul_add, sub_mul, smul_add, smul_mul_assoc, mul_assoc]; abel
        _ = E • S - S * H * S - Q₁ * H * S := by
            rw [hS_idem, hQ1S]
            simp only [smul_zero, add_zero, mul_zero, sub_zero]
    have hD0_R1_HS : denominator P₀ H E * (R₁ * H * S) = (-S * H * R₁ + Q₁) * H * S := by
      rw [← mul_assoc, ← mul_assoc, hD0_R1]
    calc denominator P₀ H E * (1 + R₁ * H) * S
        = denominator P₀ H E * S + denominator P₀ H E * (R₁ * H * S) := by noncomm_ring
      _ = (E • S - S * H * S - Q₁ * H * S) + (-S * H * R₁ + Q₁) * H * S := by
          rw [hD0_S, hD0_R1_HS]
      _ = E • S - (S * H * S + S * H * R₁ * H * S) := by noncomm_ring
      _ = E • S - S * H₁ * S := by rw [hSH1S]
      _ = intermediateDenominator P₀ P₁ H₁ E := by rfl
  have hD0_second : denominator P₀ H E * ((1 + R₁ * H) * R₀₁ * (1 + H * R₁)) = S + S * H * R₁ := by
    calc denominator P₀ H E * ((1 + R₁ * H) * R₀₁ * (1 + H * R₁))
        = (denominator P₀ H E * (1 + R₁ * H)) * (S * R₀₁) * (1 + H * R₁) := by
            rw [hSR01]; noncomm_ring
      _ = (denominator P₀ H E * (1 + R₁ * H) * S) * R₀₁ * (1 + H * R₁) := by noncomm_ring
      _ = (intermediateDenominator P₀ P₁ H₁ E * R₀₁) * (1 + H * R₁) := by
            rw [hD0_block]
      _ = S * (1 + H * R₁) := by rw [hDR01]
      _ = S + S * H * R₁ := by noncomm_ring
  dsimp [nestedResolvent]
  rw [mul_add, hD0_R1, hD0_second]
  calc (-S * H * R₁ + Q₁) + (S + S * H * R₁) = S + Q₁ := by noncomm_ring
    _ = 1 - P₀ := intermediateShell_add_outer P₀ P₁

theorem nestedResolvent_kreinAdjoint (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁) (hH_sa : kreinAdjoint H = H)
    (h_nest : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    kreinAdjoint (nestedResolvent H R₁ R₀₁) = nestedResolvent H R₁ R₀₁ := by
  have hR := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  exact resolvent_kreinAdjoint P₀ H (nestedResolvent H R₁ R₀₁) E hP0_sa hH_sa
    (nestedResolvent_support P₀ P₁ H R₁ R₀₁ hP0 h_nest hQR1 hSR01)
    (denominator_mul_nestedResolvent P₀ P₁ H R₁ R₀₁ E hP0 hP1 h_nest hR hQR1 hDR1 hSR01 hDR01)

theorem nestedResolvent_mul_denominator (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁) (hH_sa : kreinAdjoint H = H)
    (h_nest : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    nestedResolvent H R₁ R₀₁ * denominator P₀ H E = 1 - P₀ := by
  have hR := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  exact resolvent_mul_denominator P₀ H (nestedResolvent H R₁ R₀₁) E hP0_sa hH_sa
    (nestedResolvent_support P₀ P₁ H R₁ R₀₁ hP0 h_nest hQR1 hSR01)
    (denominator_mul_nestedResolvent P₀ P₁ H R₁ R₀₁ E hP0 hP1 h_nest hR hQR1 hDR1 hSR01 hDR01)

omit [CompleteSpace V] [KreinSpace V] in
/-- Purely algebraic support form of nested Schur transitivity on `V →L[ℝ] V`, requiring no
Krein self-adjointness or denominator hypotheses. -/
theorem effectiveHamiltonian_schur_transitive_algebraic
    (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁)
    (h_nestL : P₀ * P₁ = P₀) (h_nestR : P₁ * P₀ = P₀)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hR01S : R₀₁ * intermediateShell P₀ P₁ = R₀₁) :
    effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁) =
      effectiveHamiltonian P₀ (effectiveHamiltonian P₁ H R₁) R₀₁ := by
  dsimp only [effectiveHamiltonian, intermediateShell, nestedResolvent]
  exact effectiveOperator_schur_transitive_ring P₀ P₁ H R₁ R₀₁ hP1 h_nestL h_nestR hSR01 hR01S

/-- **Main Theorem 1 — Nested Krein–Feshbach Schur Transitivity** (Exact Discrete RG Decimation Step):
eliminating `(1 - P₁)` then `(P₁ - P₀)` equals single-step elimination of `(1 - P₀)` with the
nested resolvent, derived from minimal right-inverse hypotheses via Krein self-adjointness. -/
theorem effectiveHamiltonian_schur_transitive
    (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁) (hH_sa : kreinAdjoint H = H)
    (h_nest : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁) :
    effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁) =
      effectiveHamiltonian P₀ (effectiveHamiltonian P₁ H R₁) R₀₁ := by
  have hR := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  have hR01S := intermediateResolvent_mul_shell P₀ P₁ H R₁ R₀₁ E
    hP0_sa hP1_sa hH_sa hQR1 hDR1 hSR01 hDR01
  exact effectiveHamiltonian_schur_transitive_algebraic
    P₀ P₁ H R₁ R₀₁ hP1 h_nest hR hSR01 hR01S

omit [CompleteSpace V] [KreinSpace V] in
/-- **Main Theorem 2 — RG Wave-Operator Cocycle Composition**:
reconstructing from `P₀` to `P₁` and then from `P₁` to `V` equals direct reconstruction via `nestedResolvent`. -/
theorem waveOperator_schur_comp (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V)
    (hP1 : P₁ * P₁ = P₁)
    (h_nestL : P₀ * P₁ = P₀) (h_nestR : P₁ * P₀ = P₀)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hR01S : R₀₁ * intermediateShell P₀ P₁ = R₀₁) :
    waveOperator P₁ H R₁ * waveOperator P₀ (effectiveHamiltonian P₁ H R₁) R₀₁ =
      waveOperator P₀ H (nestedResolvent H R₁ R₀₁) := by
  set H₁ := effectiveHamiltonian P₁ H R₁
  have hP1S : P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ :=
    P1_mul_intermediateShell P₀ P₁ hP1 h_nestR
  have hSP1 : intermediateShell P₀ P₁ * P₁ = intermediateShell P₀ P₁ :=
    intermediateShell_mul_P1 P₀ P₁ hP1 h_nestL
  have hP1R01 : P₁ * R₀₁ = R₀₁ := by
    calc P₁ * R₀₁ = P₁ * (intermediateShell P₀ P₁ * R₀₁) := by rw [hSR01]
      _ = (P₁ * intermediateShell P₀ P₁) * R₀₁ := (mul_assoc _ _ _).symm
      _ = intermediateShell P₀ P₁ * R₀₁ := by rw [hP1S]
      _ = R₀₁ := hSR01
  have hR01P1 : R₀₁ * P₁ = R₀₁ := by
    calc R₀₁ * P₁ = (R₀₁ * intermediateShell P₀ P₁) * P₁ := by rw [hR01S]
      _ = R₀₁ * (intermediateShell P₀ P₁ * P₁) := mul_assoc _ _ _
      _ = R₀₁ * intermediateShell P₀ P₁ := by rw [hSP1]
      _ = R₀₁ := hR01S
  have hR01H1P0 : R₀₁ * H₁ * P₀ = R₀₁ * (1 + H * R₁) * H * P₀ := by
    dsimp [H₁, effectiveHamiltonian]
    calc R₀₁ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) * P₀
        = (R₀₁ * P₁) * H * (P₁ * P₀) + (R₀₁ * P₁) * H * R₁ * H * (P₁ * P₀) := by noncomm_ring
      _ = R₀₁ * H * P₀ + R₀₁ * H * R₁ * H * P₀ := by rw [hR01P1, h_nestR]
      _ = R₀₁ * (1 + H * R₁) * H * P₀ := by noncomm_ring
  dsimp [waveOperator, nestedResolvent]
  calc (P₁ + R₁ * H * P₁) * (P₀ + R₀₁ * H₁ * P₀)
      = P₁ * P₀ + (P₁ * R₀₁) * H₁ * P₀ + R₁ * H * (P₁ * P₀) +
          R₁ * H * (P₁ * R₀₁) * H₁ * P₀ := by noncomm_ring
    _ = P₀ + R₀₁ * H₁ * P₀ + R₁ * H * P₀ + R₁ * H * (R₀₁ * H₁ * P₀) := by
          rw [h_nestR, hP1R01]; noncomm_ring
    _ = P₀ + R₀₁ * (1 + H * R₁) * H * P₀ + R₁ * H * P₀ +
          R₁ * H * (R₀₁ * (1 + H * R₁) * H * P₀) := by rw [hR01H1P0]
    _ = P₀ + (R₁ + (1 + R₁ * H) * R₀₁ * (1 + H * R₁)) * H * P₀ := by noncomm_ring

/-- **Main Theorem 3a — Nested Spectral Equation Equivalence**:
on any model state `v` with `P₀ v = v`, the full eigenvalue equation for the two-step
reconstructed vector equals the intermediate-scale eigenvalue equation and the IR effective
eigenvalue equation. -/
theorem nested_eigen_equation_iff (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁) (hH_sa : kreinAdjoint H = H)
    (h_nest : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁)
    (v : V) (hv : P₀ v = v) :
    let H₁ := effectiveHamiltonian P₁ H R₁
    let W₀ := waveOperator P₀ H (nestedResolvent H R₁ R₀₁)
    let W₀₁ := waveOperator P₀ H₁ R₀₁
    (H (W₀ v) = E • W₀ v ↔ H₁ (W₀₁ v) = E • W₀₁ v) ∧
      (H (W₀ v) = E • W₀ v ↔ effectiveHamiltonian P₀ H₁ R₀₁ v = E • v) := by
  intro H₁ W₀ W₀₁
  have hR := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  have hR01S := intermediateResolvent_mul_shell P₀ P₁ H R₁ R₀₁ E
    hP0_sa hP1_sa hH_sa hQR1 hDR1 hSR01 hDR01
  have hSupp0 := nestedResolvent_support P₀ P₁ H R₁ R₀₁ hP0 h_nest hQR1 hSR01
  have hD0 := denominator_mul_nestedResolvent P₀ P₁ H R₁ R₀₁ E
    hP0 hP1 h_nest hR hQR1 hDR1 hSR01 hDR01
  have heff := effectiveHamiltonian_schur_transitive P₀ P₁ H R₁ R₀₁ E
    hP1 hP0_sa hP1_sa hH_sa h_nest hQR1 hDR1 hSR01 hDR01
  have h_full : H (W₀ v) = E • W₀ v ↔ effectiveHamiltonian P₀ H₁ R₀₁ v = E • v := by
    rw [← heff]
    exact eigen_equation_iff P₀ H (nestedResolvent H R₁ R₀₁) E hSupp0 hD0 v hv
  have hW01_P1 : P₁ (W₀₁ v) = W₀₁ v := by
    have h1 : P₁ * W₀₁ = W₀₁ := by
      have hP1S' := P1_mul_intermediateShell P₀ P₁ hP1 hR
      have hP1R01 : P₁ * R₀₁ = R₀₁ := by
        calc P₁ * R₀₁ = P₁ * (intermediateShell P₀ P₁ * R₀₁) := by rw [hSR01]
          _ = (P₁ * intermediateShell P₀ P₁) * R₀₁ := (mul_assoc _ _ _).symm
          _ = intermediateShell P₀ P₁ * R₀₁ := by rw [hP1S']
          _ = R₀₁ := hSR01
      dsimp [W₀₁, waveOperator]
      calc P₁ * (P₀ + R₀₁ * H₁ * P₀) = P₁ * P₀ + (P₁ * R₀₁) * H₁ * P₀ := by noncomm_ring
        _ = P₀ + R₀₁ * H₁ * P₀ := by rw [hR, hP1R01]
    exact congrArg (fun T : V →L[ℝ] V => T v) h1
  have hW0_eq : W₀ v = waveOperator P₁ H R₁ (W₀₁ v) := by
    have hc := waveOperator_schur_comp P₀ P₁ H R₁ R₀₁ hP1 h_nest hR hSR01 hR01S
    exact (congrArg (fun T : V →L[ℝ] V => T v) hc).symm
  have h_mid : H (W₀ v) = E • W₀ v ↔ H₁ (W₀₁ v) = E • W₀₁ v := by
    rw [hW0_eq]
    exact eigen_equation_iff P₁ H R₁ E hQR1 hDR1 (W₀₁ v) hW01_P1
  exact ⟨h_mid, h_full⟩

/-- **Main Theorem 3b — Nested Eigenvector Reconstruction**:
any full eigenvector `H ψ = E • ψ` reconstructs successively via `W₀₁ (P₀ (P₁ ψ)) = P₁ ψ`
and `W₁ (W₀₁ (P₀ ψ)) = ψ`, matching direct reconstruction `W₀ (P₀ ψ) = ψ`. -/
theorem nested_reconstruct_eigenvector (P₀ P₁ H R₁ R₀₁ : V →L[ℝ] V) (E : ℝ)
    (hP0 : P₀ * P₀ = P₀) (hP1 : P₁ * P₁ = P₁)
    (hP0_sa : kreinAdjoint P₀ = P₀) (hP1_sa : kreinAdjoint P₁ = P₁) (hH_sa : kreinAdjoint H = H)
    (h_nest : P₀ * P₁ = P₀)
    (hQR1 : (1 - P₁) * R₁ = R₁) (hDR1 : denominator P₁ H E * R₁ = 1 - P₁)
    (hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁)
    (hDR01 : intermediateDenominator P₀ P₁ (effectiveHamiltonian P₁ H R₁) E * R₀₁ =
      intermediateShell P₀ P₁)
    (ψ : V) (hψ : H ψ = E • ψ) :
    let H₁ := effectiveHamiltonian P₁ H R₁
    let W₁ := waveOperator P₁ H R₁
    let W₀ := waveOperator P₀ H (nestedResolvent H R₁ R₀₁)
    let W₀₁ := waveOperator P₀ H₁ R₀₁
    W₀ (P₀ ψ) = ψ ∧ W₁ (W₀₁ (P₀ ψ)) = ψ := by
  intro H₁ W₁ W₀ W₀₁
  have hR := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  have hR01S := intermediateResolvent_mul_shell P₀ P₁ H R₁ R₀₁ E
    hP0_sa hP1_sa hH_sa hQR1 hDR1 hSR01 hDR01
  have hSupp0 := nestedResolvent_support P₀ P₁ H R₁ R₀₁ hP0 h_nest hQR1 hSR01
  have hD0 := denominator_mul_nestedResolvent P₀ P₁ H R₁ R₀₁ E
    hP0 hP1 h_nest hR hQR1 hDR1 hSR01 hDR01
  have hW0 : W₀ (P₀ ψ) = ψ :=
    reconstruct_eigenvector P₀ H (nestedResolvent H R₁ R₀₁) E
      hP0 hP0_sa hH_sa hSupp0 hD0 ψ hψ
  have hc := waveOperator_schur_comp P₀ P₁ H R₁ R₀₁ hP1 h_nest hR hSR01 hR01S
  have hW1_W01 : W₁ (W₀₁ (P₀ ψ)) = W₀ (P₀ ψ) :=
    congrArg (fun T : V →L[ℝ] V => T (P₀ ψ)) hc
  refine ⟨hW0, hW1_W01.trans hW0⟩

omit [CompleteSpace V] [KreinSpace V] in
/-- For any `P, H`, the commutator `[P, H]` decomposes exactly into the difference
of the two off-diagonal corner couplings `P * H * (1 - P) - (1 - P) * H * P`. -/
theorem comm_proj_hamiltonian_eq_offDiagonal_corners (P H : V →L[ℝ] V) :
    P * H - H * P = P * H * (1 - P) - (1 - P) * H * P := by
  calc P * H - H * P
      = P * H - P * H * P + (P * H * P - H * P) := by noncomm_ring
    _ = P * H * (1 - P) - (1 - P) * H * P := by noncomm_ring

omit [CompleteSpace V] [KreinSpace V] in
/-- An idempotent `P` commutes with `H` (`[P, H] = 0`) if and only if both off-diagonal corner
couplings `P * H * (1 - P)` and `(1 - P) * H * P` vanish. -/
theorem comm_proj_hamiltonian_zero_iff_corners_zero (P H : V →L[ℝ] V)
    (hP : P * P = P) :
    P * H = H * P ↔ P * H * (1 - P) = 0 ∧ (1 - P) * H * P = 0 := by
  constructor
  · intro hComm
    constructor
    · calc P * H * (1 - P) = (H * P) * (1 - P) := by rw [hComm]
        _ = H * (P - P * P) := by noncomm_ring
        _ = 0 := by rw [hP, sub_self, mul_zero]
    · calc (1 - P) * H * P = (1 - P) * (H * P) := mul_assoc _ _ _
        _ = (1 - P) * (P * H) := by rw [hComm]
        _ = (P - P * P) * H := by noncomm_ring
        _ = 0 := by rw [hP, sub_self, zero_mul]
  · rintro ⟨h1, h2⟩
    have hdiff := comm_proj_hamiltonian_eq_offDiagonal_corners P H
    rw [h1, h2, sub_zero] at hdiff
    exact sub_eq_zero.mp hdiff

omit [CompleteSpace V] [KreinSpace V] in
/-- When `[P, H] = 0`, the Feshbach–Schur effective Hamiltonian collapses to the direct projection
`P * H * P`; equivalently, `[P, H] ≠ 0` is a necessary obstruction for nontrivial Schur flow. -/
theorem effectiveHamiltonian_sub_direct_eq_zero_of_commute (P H R : V →L[ℝ] V)
    (hP : P * P = P) (hComm : P * H = H * P) (hQR : (1 - P) * R = R) :
    effectiveHamiltonian P H R = P * H * P := by
  have h1 : P * H * (1 - P) = 0 :=
    ((comm_proj_hamiltonian_zero_iff_corners_zero P H hP).mp hComm).1
  have hcorr : P * H * R * H * P = 0 := by
    calc P * H * R * H * P
        = (P * H * ((1 - P) * R)) * H * P := by rw [hQR]
      _ = (P * H * (1 - P)) * R * H * P := by noncomm_ring
      _ = 0 := by rw [h1, zero_mul, zero_mul, zero_mul]
  dsimp [effectiveHamiltonian]
  rw [hcorr, add_zero]

end NestedKreinFeshbach

/-! ## Concrete `Fin 3` Inhabitant Witness for Nested Krein–Feshbach (T17 Non-Vacuity) -/

section Fin3Witness

abbrev E3 := EuclideanSpace ℝ (Fin 3)

private def mat3Lin (M : Matrix (Fin 3) (Fin 3) ℝ) : E3 →ₗ[ℝ] E3 where
  toFun v := WithLp.toLp 2 (Matrix.mulVec M (WithLp.ofLp v))
  map_add' u v := by
    ext i
    change M.mulVec (u.ofLp + v.ofLp) i = M.mulVec u.ofLp i + M.mulVec v.ofLp i
    rw [Matrix.mulVec_add, Pi.add_apply]
  map_smul' c v := by
    ext i
    change M.mulVec (c • v.ofLp) i = c * M.mulVec v.ofLp i
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

private noncomputable def mat3CLM (M : Matrix (Fin 3) (Fin 3) ℝ) : E3 →L[ℝ] E3 :=
  (mat3Lin M).toContinuousLinearMap

private lemma mat3CLM_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    mat3CLM M * mat3CLM N = mat3CLM (M * N) := by
  ext v i
  change (mat3CLM M (mat3CLM N v)).ofLp i = (mat3CLM (M * N) v).ofLp i
  simp [mat3CLM, mat3Lin, Matrix.mulVec_mulVec]

private lemma mat3CLM_one : mat3CLM (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext v i
  simp [mat3CLM, mat3Lin]

private lemma mat3CLM_sub (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    mat3CLM M - mat3CLM N = mat3CLM (M - N) := by
  ext v i
  change (mat3CLM M v).ofLp i - (mat3CLM N v).ofLp i = (mat3CLM (M - N) v).ofLp i
  simp [mat3CLM, mat3Lin, Matrix.sub_mulVec]

private lemma mat3CLM_smul (c : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    c • mat3CLM M = mat3CLM (c • M) := by
  ext v i
  change c * (mat3CLM M v).ofLp i = (mat3CLM (c • M) v).ofLp i
  simp [mat3CLM, mat3Lin, Matrix.smul_mulVec]

private lemma mat3CLM_kreinAdjoint {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.transpose = M) :
    kreinAdjoint (mat3CLM M) = mat3CLM M := by
  change ContinuousLinearMap.adjoint (mat3CLM M) = mat3CLM M
  refine ContinuousLinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mat3CLM,
    LinearMap.coe_toContinuousLinearMap', mat3Lin, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h01 : M 0 1 = M 1 0 := congrFun (congrFun hM 1) 0
  have h02 : M 0 2 = M 2 0 := congrFun (congrFun hM 2) 0
  have h12 : M 1 2 = M 2 1 := congrFun (congrFun hM 2) 1
  rw [h01, h02, h12]
  ring

private lemma clm_mul_smul (A B : E3 →L[ℝ] E3) (c : ℝ) : A * (c • B) = c • (A * B) := by
  ext v i; simp [ContinuousLinearMap.mul_def]

private lemma clm_smul_mul (c : ℝ) (A B : E3 →L[ℝ] E3) : (c • A) * B = c • (A * B) := by
  ext v i; simp [ContinuousLinearMap.mul_def]

/-- Concrete finite-dimensional `Fin 3` witness proving that all nested Krein–Feshbach
hypotheses (`P₀ ≤ P₁ ≤ 1`, right inverses `R₁` on `1 - P₁` and `R₀₁` on `P₁ - P₀`, and
`effectiveHamiltonian_schur_transitive`) are non-vacuously inhabited. -/
theorem fin3_nested_witness (a b c v g E : ℝ)
    (hE1 : E ≠ c) (hE01 : E ≠ b + g ^ 2 / (E - c)) :
    let P₀ := mat3CLM !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    let P₁ := mat3CLM !![1, 0, 0; 0, 1, 0; 0, 0, 0]
    let H := mat3CLM !![a, v, g; v, b, g; g, g, c]
    let R₁ := (E - c)⁻¹ • (1 - P₁)
    let H₁ := effectiveHamiltonian P₁ H R₁
    let R₀₁ := (E - (b + g ^ 2 / (E - c)))⁻¹ • intermediateShell P₀ P₁
    P₀ * P₀ = P₀ ∧ P₁ * P₁ = P₁ ∧ P₀ * P₁ = P₀ ∧
      kreinAdjoint P₀ = P₀ ∧ kreinAdjoint P₁ = P₁ ∧ kreinAdjoint H = H ∧
      (1 - P₁) * R₁ = R₁ ∧ denominator P₁ H E * R₁ = 1 - P₁ ∧
      intermediateShell P₀ P₁ * R₀₁ = R₀₁ ∧
      intermediateDenominator P₀ P₁ H₁ E * R₀₁ = intermediateShell P₀ P₁ ∧
      effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁) =
        effectiveHamiltonian P₀ H₁ R₀₁ := by
  intro P₀ P₁ H R₁ H₁ R₀₁
  have hP0_idem : P₀ * P₀ = P₀ := by
    dsimp [P₀]; rw [mat3CLM_mul]; congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hP1_idem : P₁ * P₁ = P₁ := by
    dsimp [P₁]; rw [mat3CLM_mul]; congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h_nest : P₀ * P₁ = P₀ := by
    dsimp [P₀, P₁]; rw [mat3CLM_mul]; congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hP0_sa : kreinAdjoint P₀ = P₀ := mat3CLM_kreinAdjoint (by
    ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hP1_sa : kreinAdjoint P₁ = P₁ := mat3CLM_kreinAdjoint (by
    ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hH_sa : kreinAdjoint H = H := mat3CLM_kreinAdjoint (by
    ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hQ1_idem : (1 - P₁) * (1 - P₁) = 1 - P₁ := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP1_idem]; abel
  have hQR1 : (1 - P₁) * R₁ = R₁ := by
    dsimp [R₁]; rw [clm_mul_smul, hQ1_idem]
  have hQ1_mat : (1 - P₁) = mat3CLM !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    dsimp [P₁]; rw [← mat3CLM_one, mat3CLM_sub]; congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hDR1 : denominator P₁ H E * R₁ = 1 - P₁ := by
    have hD1 : denominator P₁ H E = (E - c) • (1 - P₁) := by
      dsimp [denominator]
      have hQ1HQ1 : (1 - P₁) * H * (1 - P₁) = c • (1 - P₁) := by
        rw [hQ1_mat, mat3CLM_smul]
        dsimp [H]; rw [mat3CLM_mul, mat3CLM_mul]; congr 1
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      rw [hQ1HQ1, sub_smul]
    rw [hD1]
    dsimp [R₁]
    rw [clm_smul_mul, clm_mul_smul, smul_smul, hQ1_idem,
      mul_inv_cancel₀ (sub_ne_zero.mpr hE1), one_smul]
  have hR_nest := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  have hS_idem : intermediateShell P₀ P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ :=
    intermediateShell_idempotent P₀ P₁ hP0_idem hP1_idem h_nest hR_nest
  have hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁ := by
    dsimp [R₀₁]; rw [clm_mul_smul, hS_idem]
  have hS_mat : intermediateShell P₀ P₁ = mat3CLM !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
    dsimp [intermediateShell, P₁, P₀]; rw [mat3CLM_sub]; congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hDR01 : intermediateDenominator P₀ P₁ H₁ E * R₀₁ = intermediateShell P₀ P₁ := by
    have hSH1S : intermediateShell P₀ P₁ * H₁ * intermediateShell P₀ P₁ =
        (b + g ^ 2 / (E - c)) • intermediateShell P₀ P₁ := by
      have hS_H_S : intermediateShell P₀ P₁ * H * intermediateShell P₀ P₁ =
          b • intermediateShell P₀ P₁ := by
        rw [hS_mat, mat3CLM_smul]
        dsimp [H]; rw [mat3CLM_mul, mat3CLM_mul]; congr 1
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      have hS_HR1H_S : intermediateShell P₀ P₁ * H * R₁ * H * intermediateShell P₀ P₁ =
          (g ^ 2 / (E - c)) • intermediateShell P₀ P₁ := by
        rw [hS_mat, mat3CLM_smul]
        have hR1_mat : R₁ = mat3CLM ((E - c)⁻¹ • !![0, 0, 0; 0, 0, 0; 0, 0, 1]) := by
          dsimp [R₁]; rw [hQ1_mat, mat3CLM_smul]; rfl
        rw [hR1_mat]
        dsimp [H]; simp only [mat3CLM_mul]
        congr 1
        ext i j; fin_cases i <;> fin_cases j <;>
          (simp [Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]; try ring)
      have hSP1 : intermediateShell P₀ P₁ * P₁ = intermediateShell P₀ P₁ :=
        intermediateShell_mul_P1 P₀ P₁ hP1_idem h_nest
      have hP1S : P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ :=
        P1_mul_intermediateShell P₀ P₁ hP1_idem hR_nest
      dsimp [H₁, effectiveHamiltonian]
      calc intermediateShell P₀ P₁ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) *
              intermediateShell P₀ P₁
          = (intermediateShell P₀ P₁ * P₁) * H * (P₁ * intermediateShell P₀ P₁) +
              (intermediateShell P₀ P₁ * P₁) * H * R₁ * H *
                (P₁ * intermediateShell P₀ P₁) := by noncomm_ring
        _ = intermediateShell P₀ P₁ * H * intermediateShell P₀ P₁ +
              intermediateShell P₀ P₁ * H * R₁ * H * intermediateShell P₀ P₁ := by
            rw [hSP1, hP1S]
        _ = (b + g ^ 2 / (E - c)) • intermediateShell P₀ P₁ := by
            rw [hS_H_S, hS_HR1H_S, ← add_smul]
    have hD01 : intermediateDenominator P₀ P₁ H₁ E =
        (E - (b + g ^ 2 / (E - c))) • intermediateShell P₀ P₁ := by
      dsimp [intermediateDenominator]
      rw [hSH1S, sub_smul]
    rw [hD01]
    dsimp [R₀₁]
    rw [clm_smul_mul, clm_mul_smul, smul_smul, hS_idem,
      mul_inv_cancel₀ (sub_ne_zero.mpr hE01), one_smul]
  refine ⟨hP0_idem, hP1_idem, h_nest, hP0_sa, hP1_sa, hH_sa, hQR1, hDR1, hSR01, hDR01, ?_⟩
  exact effectiveHamiltonian_schur_transitive P₀ P₁ H R₁ R₀₁ E
    hP1_idem hP0_sa hP1_sa hH_sa h_nest hQR1 hDR1 hSR01 hDR01

/-- Explicit `Matrix (Fin 3) (Fin 3) ℝ` noncommutativity witness for the `mat3CLM` carrier. -/
theorem fin3_matrix_noncomm_witness :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 1; 1, 1, 0], ?_⟩
  intro hmat
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) hmat
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02

/-- Explicit `Fin 3` CLM noncommutativity witness confirming `[P, H] ≠ 0` when `g ≠ 0`
(`P * H ≠ H * P`) and nontrivial Schur RG correction `effectiveHamiltonian P H R ≠ P * H * P`. -/
theorem fin3_noncomm_witness :
    let P_mat : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
    let H_mat : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 1; 1, 1, 0]
    let P := mat3CLM P_mat
    let H := mat3CLM H_mat
    let R := (1 : ℝ)⁻¹ • (1 - P)
    P * H ≠ H * P ∧ effectiveHamiltonian P H R ≠ P * H * P := by
  intro P_mat H_mat P H R
  constructor
  · intro hcomm
    have hmul :
        (P * H) (WithLp.toLp 2 ![0, 0, (1 : ℝ)]) =
          (H * P) (WithLp.toLp 2 ![0, 0, (1 : ℝ)]) :=
      congrArg (fun T : E3 →L[ℝ] E3 => T (WithLp.toLp 2 ![0, 0, (1 : ℝ)])) hcomm
    have h0 := congrArg (fun x : E3 => x.ofLp 0) hmul
    dsimp [P, H] at h0
    rw [mat3CLM_mul, mat3CLM_mul] at h0
    simp [mat3CLM, mat3Lin, P_mat, H_mat] at h0
  · intro heff
    have hdiff :
        (effectiveHamiltonian P H R) (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) =
          (P * H * P) (WithLp.toLp 2 ![(1 : ℝ), 0, 0]) :=
      congrArg (fun T : E3 →L[ℝ] E3 => T (WithLp.toLp 2 ![(1 : ℝ), 0, 0])) heff
    have h0 := congrArg (fun x : E3 => x.ofLp 0) hdiff
    have hQ_mat :
        (1 : Matrix (Fin 3) (Fin 3) ℝ) - P_mat = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [P_mat]
    have hR : R = mat3CLM !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
      dsimp [R, P]
      rw [inv_one, one_smul, ← mat3CLM_one, mat3CLM_sub, hQ_mat]
    have hmat_prod :
        P_mat * H_mat * !![0, 0, 0; 0, 0, 0; 0, 0, 1] * H_mat * P_mat =
          !![1, 1, 0; 1, 1, 0; 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [P_mat, H_mat, Matrix.mul_apply, Fin.sum_univ_three]
    have hprod :
        P * H * R * H * P = mat3CLM !![1, 1, 0; 1, 1, 0; 0, 0, 0] := by
      rw [hR]
      dsimp [P, H]
      simp only [mat3CLM_mul]
      rw [hmat_prod]
    dsimp [effectiveHamiltonian] at h0
    rw [hprod] at h0
    dsimp [P, H] at h0
    simp only [mat3CLM_mul, add_apply, PiLp.add_apply] at h0
    simp [mat3CLM, mat3Lin, P_mat, H_mat] at h0

end Fin3Witness

/-! ## Indefinite `(2, 1)` Pontryagin–Krein Witness (`J = diag(1, 1, -1)`) -/

section IndefiniteKreinWitness

/-- Indefinite `(2, 1)` Pontryagin–Krein carrier `PontryaginSum ℝ² ℝ¹` with
`kreinInner (x, y) (x', y') = ⟪x, x'⟫ - ⟪y, y'⟫` (`J = diag(1, 1, -1)`). -/
abbrev E21 := InfoGeometry.Krein.PontryaginSum (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))

private noncomputable def e21ToE3 : E21 ≃ₗᵢ[ℝ] E3 where
  toFun u := WithLp.toLp 2
    ![WithLp.fst u.toLp 0, WithLp.fst u.toLp 1, WithLp.snd u.toLp 0]
  invFun v := ⟨WithLp.toLp 2 (WithLp.toLp 2 ![v.ofLp 0, v.ofLp 1], WithLp.toLp 2 ![v.ofLp 2])⟩
  left_inv u := by
    apply InfoGeometry.Krein.PontryaginSum.ext
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    apply Prod.ext
    · apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      funext i; fin_cases i <;> rfl
    · apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
      funext i; fin_cases i; rfl
  right_inv v := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    funext i
    fin_cases i <;> rfl
  map_add' u₁ u₂ := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    funext i
    fin_cases i <;> rfl
  map_smul' r u := by
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    funext i
    fin_cases i <;> rfl
  norm_map' u := by
    let w : E3 := WithLp.toLp 2 ![WithLp.fst u.toLp 0, WithLp.fst u.toLp 1, WithLp.snd u.toLp 0]
    have hinner : inner ℝ w w = inner ℝ u u := by
      change inner ℝ w w = inner ℝ u.toLp u.toLp
      rw [PiLp.inner_apply, WithLp.prod_inner_apply, PiLp.inner_apply, PiLp.inner_apply,
        Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_one]
      simp only [w, RCLike.inner_apply, conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      rfl
    have hsq : ‖w‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]
    exact (sq_eq_sq₀ (norm_nonneg w) (norm_nonneg u)).mp hsq

private noncomputable def mat21CLM (M : Matrix (Fin 3) (Fin 3) ℝ) : E21 →L[ℝ] E21 :=
  (e21ToE3.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((mat3CLM M).comp e21ToE3.toContinuousLinearEquiv.toContinuousLinearMap)

private lemma mat21CLM_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    mat21CLM M * mat21CLM N = mat21CLM (M * N) := by
  refine ContinuousLinearMap.ext fun u => ?_
  change e21ToE3.symm (mat3CLM M (e21ToE3 (e21ToE3.symm (mat3CLM N (e21ToE3 u))))) =
    e21ToE3.symm (mat3CLM (M * N) (e21ToE3 u))
  rw [e21ToE3.apply_symm_apply]
  change e21ToE3.symm ((mat3CLM M * mat3CLM N) (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (M * N) (e21ToE3 u))
  rw [mat3CLM_mul]

private lemma mat21CLM_one : mat21CLM (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  refine ContinuousLinearMap.ext fun u => ?_
  change e21ToE3.symm (mat3CLM 1 (e21ToE3 u)) = u
  rw [mat3CLM_one]
  change e21ToE3.symm (e21ToE3 u) = u
  exact e21ToE3.symm_apply_apply u

private lemma mat21CLM_sub (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    mat21CLM M - mat21CLM N = mat21CLM (M - N) := by
  refine ContinuousLinearMap.ext fun u => ?_
  change e21ToE3.symm (mat3CLM M (e21ToE3 u)) - e21ToE3.symm (mat3CLM N (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (M - N) (e21ToE3 u))
  rw [← map_sub]
  change e21ToE3.symm ((mat3CLM M - mat3CLM N) (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (M - N) (e21ToE3 u))
  rw [mat3CLM_sub]

private lemma mat21CLM_smul (c : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    c • mat21CLM M = mat21CLM (c • M) := by
  refine ContinuousLinearMap.ext fun u => ?_
  change c • e21ToE3.symm (mat3CLM M (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (c • M) (e21ToE3 u))
  rw [← map_smul]
  change e21ToE3.symm ((c • mat3CLM M) (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (c • M) (e21ToE3 u))
  rw [mat3CLM_smul]

private lemma mat21CLM_add (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    mat21CLM M + mat21CLM N = mat21CLM (M + N) := by
  refine ContinuousLinearMap.ext fun u => ?_
  change e21ToE3.symm (mat3CLM M (e21ToE3 u)) + e21ToE3.symm (mat3CLM N (e21ToE3 u)) =
    e21ToE3.symm (mat3CLM (M + N) (e21ToE3 u))
  rw [← map_add]
  apply congrArg e21ToE3.symm
  ext i
  change (mat3CLM M (e21ToE3 u)).ofLp i + (mat3CLM N (e21ToE3 u)).ofLp i =
    (mat3CLM (M + N) (e21ToE3 u)).ofLp i
  simp [mat3CLM, mat3Lin, Matrix.add_mulVec]

private lemma e21_clm_mul_smul (A B : E21 →L[ℝ] E21) (c : ℝ) : A * (c • B) = c • (A * B) := by
  ext u; simp [ContinuousLinearMap.mul_def]

private lemma e21_clm_smul_mul (c : ℝ) (A B : E21 →L[ℝ] E21) : (c • A) * B = c • (A * B) := by
  ext u; simp [ContinuousLinearMap.mul_def]

private lemma e21_inner_eq (u v : E21) :
    inner ℝ u v =
      WithLp.fst u.toLp 0 * WithLp.fst v.toLp 0 +
      WithLp.fst u.toLp 1 * WithLp.fst v.toLp 1 +
      WithLp.snd u.toLp 0 * WithLp.snd v.toLp 0 := by
  change inner ℝ u.toLp v.toLp = _
  rw [WithLp.prod_inner_apply, PiLp.inner_apply, PiLp.inner_apply,
    Fin.sum_univ_two, Fin.sum_univ_one]
  simp only [RCLike.inner_apply, conj_trivial]
  change v.toLp.ofLp.1.ofLp 0 * u.toLp.ofLp.1.ofLp 0 +
      v.toLp.ofLp.1.ofLp 1 * u.toLp.ofLp.1.ofLp 1 +
      v.toLp.ofLp.2.ofLp 0 * u.toLp.ofLp.2.ofLp 0 =
    u.toLp.ofLp.1.ofLp 0 * v.toLp.ofLp.1.ofLp 0 +
      u.toLp.ofLp.1.ofLp 1 * v.toLp.ofLp.1.ofLp 1 +
      u.toLp.ofLp.2.ofLp 0 * v.toLp.ofLp.2.ofLp 0
  ring

private lemma e21_kreinInner_eq (u v : E21) :
    kreinInner u v =
      WithLp.fst u.toLp 0 * WithLp.fst v.toLp 0 +
      WithLp.fst u.toLp 1 * WithLp.fst v.toLp 1 -
      WithLp.snd u.toLp 0 * WithLp.snd v.toLp 0 := by
  rw [PontryaginSum.kreinInner_eq, PiLp.inner_apply, PiLp.inner_apply,
    Fin.sum_univ_two, Fin.sum_univ_one]
  simp only [RCLike.inner_apply, conj_trivial]
  change v.toLp.ofLp.1.ofLp 0 * u.toLp.ofLp.1.ofLp 0 +
      v.toLp.ofLp.1.ofLp 1 * u.toLp.ofLp.1.ofLp 1 -
      v.toLp.ofLp.2.ofLp 0 * u.toLp.ofLp.2.ofLp 0 =
    u.toLp.ofLp.1.ofLp 0 * v.toLp.ofLp.1.ofLp 0 +
      u.toLp.ofLp.1.ofLp 1 * v.toLp.ofLp.1.ofLp 1 -
      u.toLp.ofLp.2.ofLp 0 * v.toLp.ofLp.2.ofLp 0
  ring

private lemma mat21CLM_coords (M : Matrix (Fin 3) (Fin 3) ℝ) (u : E21) :
    WithLp.fst (mat21CLM M u).toLp 0 =
      M 0 0 * WithLp.fst u.toLp 0 + M 0 1 * WithLp.fst u.toLp 1 + M 0 2 * WithLp.snd u.toLp 0 ∧
    WithLp.fst (mat21CLM M u).toLp 1 =
      M 1 0 * WithLp.fst u.toLp 0 + M 1 1 * WithLp.fst u.toLp 1 + M 1 2 * WithLp.snd u.toLp 0 ∧
    WithLp.snd (mat21CLM M u).toLp 0 =
      M 2 0 * WithLp.fst u.toLp 0 + M 2 1 * WithLp.fst u.toLp 1 + M 2 2 * WithLp.snd u.toLp 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change M.mulVec ![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] 0 = _
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 0 =
        WithLp.fst u.toLp 0 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 1 =
        WithLp.fst u.toLp 1 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 2 =
        WithLp.snd u.toLp 0 from rfl]
  · change M.mulVec ![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] 1 = _
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 0 =
        WithLp.fst u.toLp 0 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 1 =
        WithLp.fst u.toLp 1 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 2 =
        WithLp.snd u.toLp 0 from rfl]
  · change M.mulVec ![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] 2 = _
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 0 =
        WithLp.fst u.toLp 0 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 1 =
        WithLp.fst u.toLp 1 from rfl,
      show (![u.toLp.ofLp.1.ofLp 0, u.toLp.ofLp.1.ofLp 1, u.toLp.ofLp.2.ofLp 0] : Fin 3 → ℝ) 2 =
        WithLp.snd u.toLp 0 from rfl]

private lemma mat21_eff01_matrix_eq (a b c v g₁ g₂ E : ℝ) :
    let P0m : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    let P1m : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 1]
    let Hm : Matrix (Fin 3) (Fin 3) ℝ := !![a, v, g₁; v, b, g₂; -g₁, -g₂, c]
    let R1m : Matrix (Fin 3) (Fin 3) ℝ := (E - b)⁻¹ • !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    let R01m : Matrix (Fin 3) (Fin 3) ℝ :=
      (E - (c - g₂ ^ 2 / (E - b)))⁻¹ • !![0, 0, 0; 0, 0, 0; 0, 0, 1]
    let H1m : Matrix (Fin 3) (Fin 3) ℝ := P1m * Hm * P1m + P1m * Hm * R1m * Hm * P1m
    P0m * H1m * P0m + P0m * H1m * R01m * H1m * P0m =
      (a + v ^ 2 / (E - b) -
        (g₁ + v * g₂ / (E - b)) ^ 2 / (E - (c - g₂ ^ 2 / (E - b)))) • P0m := by
  intro P0m P1m Hm R1m R01m H1m
  have hHR1m : Hm * R1m * Hm =
      !![v ^ 2 / (E - b), v * b / (E - b), v * g₂ / (E - b);
         b * v / (E - b), b ^ 2 / (E - b), b * g₂ / (E - b);
         -(g₂ * v / (E - b)), -(g₂ * b / (E - b)), -(g₂ ^ 2 / (E - b))] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [Hm, R1m, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]; try ring)
  have hH1m_val : H1m =
      !![a + v ^ 2 / (E - b), 0, g₁ + v * g₂ / (E - b);
         0, 0, 0;
         -(g₁ + g₂ * v / (E - b)), 0, c - g₂ ^ 2 / (E - b)] := by
    dsimp [H1m]
    rw [mul_assoc P1m Hm R1m, mul_assoc P1m (Hm * R1m) Hm]
    change P1m * Hm * P1m + P1m * (Hm * R1m * Hm) * P1m = _
    rw [hHR1m]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [P1m, Hm]; try ring)
  have h0H1m : P0m * H1m =
      !![a + v ^ 2 / (E - b), 0, g₁ + v * g₂ / (E - b); 0, 0, 0; 0, 0, 0] := by
    rw [hH1m_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0m, Matrix.mul_apply, Fin.sum_univ_three]
  have hH1m0 : H1m * P0m =
      !![a + v ^ 2 / (E - b), 0, 0; 0, 0, 0; -(g₁ + g₂ * v / (E - b)), 0, 0] := by
    rw [hH1m_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0m, Matrix.mul_apply, Fin.sum_univ_three]
  have h0H10m : P0m * H1m * P0m = (a + v ^ 2 / (E - b)) • P0m := by
    rw [h0H1m]
    ext i j; fin_cases i <;> fin_cases j <;> simp [P0m, Matrix.mul_apply, Fin.sum_univ_three]
  have h0H1R01m : P0m * H1m * R01m =
      !![0, 0, (g₁ + v * g₂ / (E - b)) / (E - (c - g₂ ^ 2 / (E - b))); 0, 0, 0; 0, 0, 0] := by
    rw [h0H1m]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [R01m, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]
  have h0H1R01H10m : P0m * H1m * R01m * H1m * P0m =
      (-((g₁ + v * g₂ / (E - b)) ^ 2 / (E - (c - g₂ ^ 2 / (E - b))))) • P0m := by
    rw [mul_assoc (P0m * H1m * R01m) H1m P0m, h0H1R01m, hH1m0]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [P0m, Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]; try ring)
  rw [h0H10m, h0H1R01H10m, ← add_smul, ← sub_eq_add_neg]

private lemma e21_krein_symm_scalar (u0 u1 u2 v0 v1 v2
    m00 m01 m02 m10 m11 m12 m20 m21 m22 : ℝ)
    (h01 : m01 = m10) (h02 : m02 = -m20) (h12 : m12 = -m21) :
    (m00 * u0 + m01 * u1 + m02 * u2) * v0 +
      (m10 * u0 + m11 * u1 + m12 * u2) * v1 -
      (m20 * u0 + m21 * u1 + m22 * u2) * v2 =
    u0 * (m00 * v0 + m01 * v1 + m02 * v2) +
      u1 * (m10 * v0 + m11 * v1 + m12 * v2) -
      u2 * (m20 * v0 + m21 * v1 + m22 * v2) := by
  subst h01; subst h02; subst h12
  ring

private lemma mat21CLM_kreinAdjoint {M : Matrix (Fin 3) (Fin 3) ℝ}
    (h01 : M 0 1 = M 1 0) (h02 : M 0 2 = -M 2 0) (h12 : M 1 2 = -M 2 1) :
    kreinAdjoint (mat21CLM M) = mat21CLM M := by
  refine (isKreinSelfAdjoint_iff (mat21CLM M)).mpr fun u v => ?_
  rw [e21_kreinInner_eq, e21_kreinInner_eq]
  rcases mat21CLM_coords M u with ⟨hu0, hu1, hu2⟩
  rcases mat21CLM_coords M v with ⟨hv0, hv1, hv2⟩
  rw [hu0, hu1, hu2, hv0, hv1, hv2]
  exact e21_krein_symm_scalar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h01 h02 h12

/-- Concrete indefinite `(2, 1)` Pontryagin–Krein nested-projection witness:
- `P₀` projects onto positive-sheet coordinate `0` (`kreinInner e₀ e₀ = +1`);
- `P₁` projects onto coordinates `(0, 2)`, so the intermediate shell `P₁ - P₀` is strictly
  negative-definite (`kreinInner e₂ e₂ = -1`);
- `H` is genuinely Krein-self-adjoint (`kreinAdjoint H = H`, skew between `+` and `-` sheets)
  and **not** Hilbert-self-adjoint when `g₁ ≠ 0 ∨ g₂ ≠ 0`;
- nested Schur transitivity and `IsKreinSelfAdjoint` hold with the indefinite-metric sign flip
  `c - g₂ ^ 2 / (E - b)` on the intermediate negative-metric shell. -/
theorem indefinite_krein21_nested_witness (a b c v g₁ g₂ E : ℝ)
    (hE1 : E ≠ b) (hE01 : E ≠ c - g₂ ^ 2 / (E - b)) :
    let P₀ := mat21CLM !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    let P₁ := mat21CLM !![1, 0, 0; 0, 0, 0; 0, 0, 1]
    let H := mat21CLM !![a, v, g₁; v, b, g₂; -g₁, -g₂, c]
    let R₁ := (E - b)⁻¹ • (1 - P₁)
    let H₁ := effectiveHamiltonian P₁ H R₁
    let R₀₁ := (E - (c - g₂ ^ 2 / (E - b)))⁻¹ • intermediateShell P₀ P₁
    let e₀ : E21 := e21ToE3.symm (WithLp.toLp 2 ![1, 0, 0])
    let e₂ : E21 := e21ToE3.symm (WithLp.toLp 2 ![0, 0, 1])
    (kreinInner e₀ e₀ = 1 ∧ kreinInner e₂ e₂ = -1 ∧
      P₀ e₀ = e₀ ∧ intermediateShell P₀ P₁ e₂ = e₂) ∧
    ((g₁ ≠ 0 ∨ g₂ ≠ 0) → ContinuousLinearMap.adjoint H ≠ H) ∧
    (P₀ * P₀ = P₀ ∧ P₁ * P₁ = P₁ ∧ P₀ * P₁ = P₀ ∧
      kreinAdjoint P₀ = P₀ ∧ kreinAdjoint P₁ = P₁ ∧ kreinAdjoint H = H) ∧
    ((1 - P₁) * R₁ = R₁ ∧ denominator P₁ H E * R₁ = 1 - P₁ ∧
      intermediateShell P₀ P₁ * R₀₁ = R₀₁ ∧
      intermediateDenominator P₀ P₁ H₁ E * R₀₁ = intermediateShell P₀ P₁) ∧
    (effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁) =
        effectiveHamiltonian P₀ H₁ R₀₁ ∧
      IsKreinSelfAdjoint H₁ ∧
      IsKreinSelfAdjoint (effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁)) ∧
      IsKreinSelfAdjoint (effectiveHamiltonian P₀ H₁ R₀₁)) ∧
    (intermediateShell P₀ P₁ * H₁ * intermediateShell P₀ P₁ =
        (c - g₂ ^ 2 / (E - b)) • intermediateShell P₀ P₁ ∧
      effectiveHamiltonian P₀ H₁ R₀₁ =
        (a + v ^ 2 / (E - b) -
          (g₁ + v * g₂ / (E - b)) ^ 2 / (E - (c - g₂ ^ 2 / (E - b)))) • P₀) := by
  intro P₀ P₁ H R₁ H₁ R₀₁ e₀ e₂
  have he0_inner : kreinInner e₀ e₀ = 1 := by
    rw [e21_kreinInner_eq]
    have h0 : WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![1, 0, 0])).toLp 0 = 1 := rfl
    have h1 : WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![1, 0, 0])).toLp 1 = 0 := rfl
    have h2 : WithLp.snd (e21ToE3.symm (WithLp.toLp 2 ![1, 0, 0])).toLp 0 = 0 := rfl
    change WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![1, 0, 0])).toLp 0 * _ + _ - _ = 1
    rw [h0, h1, h2]; norm_num
  have he2_inner : kreinInner e₂ e₂ = -1 := by
    rw [e21_kreinInner_eq]
    have h0 : WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![0, 0, 1])).toLp 0 = 0 := rfl
    have h1 : WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![0, 0, 1])).toLp 1 = 0 := rfl
    have h2 : WithLp.snd (e21ToE3.symm (WithLp.toLp 2 ![0, 0, 1])).toLp 0 = 1 := rfl
    change WithLp.fst (e21ToE3.symm (WithLp.toLp 2 ![0, 0, 1])).toLp 0 * _ + _ - _ = -1
    rw [h0, h1, h2]; norm_num
  have hS_mat : intermediateShell P₀ P₁ = mat21CLM !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    dsimp [intermediateShell, P₁, P₀]
    rw [mat21CLM_sub]
    apply congrArg mat21CLM
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hP0_e0 : P₀ e₀ = e₀ := by
    apply e21ToE3.injective
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    fin_cases i <;>
      simp [P₀, e₀, mat21CLM, e21ToE3, mat3CLM, mat3Lin, dotProduct, Fin.sum_univ_three]
  have hS_e2 : intermediateShell P₀ P₁ e₂ = e₂ := by
    rw [hS_mat]
    apply e21ToE3.injective
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext i
    fin_cases i <;>
      simp [e₂, mat21CLM, e21ToE3, mat3CLM, mat3Lin, dotProduct, Fin.sum_univ_three]
  have hNotHilb : (g₁ ≠ 0 ∨ g₂ ≠ 0) → ContinuousLinearMap.adjoint H ≠ H := by
    intro hg hadj
    have he0_0 : WithLp.fst e₀.toLp 0 = 1 := rfl
    have he0_1 : WithLp.fst e₀.toLp 1 = 0 := rfl
    have he0_2 : WithLp.snd e₀.toLp 0 = 0 := rfl
    have he2_0 : WithLp.fst e₂.toLp 0 = 0 := rfl
    have he2_1 : WithLp.fst e₂.toLp 1 = 0 := rfl
    have he2_2 : WithLp.snd e₂.toLp 0 = 1 := rfl
    rcases hg with hg1 | hg2
    · have h_eq := congrArg (fun T : E21 →L[ℝ] E21 => inner ℝ (T e₀) e₂) hadj
      rw [ContinuousLinearMap.adjoint_inner_left] at h_eq
      rcases mat21CLM_coords !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] e₂ with ⟨h20, h21, h22⟩
      rcases mat21CLM_coords !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] e₀ with ⟨h00, h01, h02⟩
      have hL : inner ℝ e₀ (H e₂) = g₁ := by
        rw [e21_inner_eq]; dsimp [H]; rw [h20, h21, h22, he0_0, he0_1, he0_2, he2_0, he2_1, he2_2]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      have hR : inner ℝ (H e₀) e₂ = -g₁ := by
        rw [e21_inner_eq]; dsimp [H]; rw [h00, h01, h02, he0_0, he0_1, he0_2, he2_0, he2_1, he2_2]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rw [hL, hR] at h_eq
      exact hg1 (by linarith)
    · let e₁ : E21 := e21ToE3.symm (WithLp.toLp 2 ![0, 1, 0])
      have he1_0 : WithLp.fst e₁.toLp 0 = 0 := rfl
      have he1_1 : WithLp.fst e₁.toLp 1 = 1 := rfl
      have he1_2 : WithLp.snd e₁.toLp 0 = 0 := rfl
      have h_eq := congrArg (fun T : E21 →L[ℝ] E21 => inner ℝ (T e₁) e₂) hadj
      rw [ContinuousLinearMap.adjoint_inner_left] at h_eq
      rcases mat21CLM_coords !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] e₂ with ⟨h20, h21, h22⟩
      rcases mat21CLM_coords !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] e₁ with ⟨h10, h11, h12⟩
      have hL : inner ℝ e₁ (H e₂) = g₂ := by
        rw [e21_inner_eq]; dsimp [H]; rw [h20, h21, h22, he1_0, he1_1, he1_2, he2_0, he2_1, he2_2]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      have hR : inner ℝ (H e₁) e₂ = -g₂ := by
        rw [e21_inner_eq]; dsimp [H]; rw [h10, h11, h12, he1_0, he1_1, he1_2, he2_0, he2_1, he2_2]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      rw [hL, hR] at h_eq
      exact hg2 (by linarith)
  have hP0_idem : P₀ * P₀ = P₀ := by
    dsimp [P₀]; rw [mat21CLM_mul]; apply congrArg mat21CLM
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hP1_idem : P₁ * P₁ = P₁ := by
    dsimp [P₁]; rw [mat21CLM_mul]; apply congrArg mat21CLM
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h_nest : P₀ * P₁ = P₀ := by
    dsimp [P₀, P₁]; rw [mat21CLM_mul]; apply congrArg mat21CLM
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hP0_sa : kreinAdjoint P₀ = P₀ := mat21CLM_kreinAdjoint (by norm_num) (by norm_num) (by norm_num)
  have hP1_sa : kreinAdjoint P₁ = P₁ := mat21CLM_kreinAdjoint (by norm_num) (by norm_num) (by norm_num)
  have hH_sa : kreinAdjoint H = H := mat21CLM_kreinAdjoint rfl (by simp) (by simp)
  have hQ1_idem : (1 - P₁) * (1 - P₁) = 1 - P₁ := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP1_idem]; abel
  have hQR1 : (1 - P₁) * R₁ = R₁ := by
    dsimp [R₁]; rw [e21_clm_mul_smul, hQ1_idem]
  have hQ1_mat : (1 - P₁) = mat21CLM !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
    dsimp [P₁]; rw [← mat21CLM_one, mat21CLM_sub]; apply congrArg mat21CLM
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hDR1 : denominator P₁ H E * R₁ = 1 - P₁ := by
    have hD1 : denominator P₁ H E = (E - b) • (1 - P₁) := by
      dsimp [denominator]
      have hQ1HQ1 : (1 - P₁) * H * (1 - P₁) = b • (1 - P₁) := by
        rw [hQ1_mat, mat21CLM_smul]
        dsimp [H]; rw [mat21CLM_mul, mat21CLM_mul]; apply congrArg mat21CLM
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      rw [hQ1HQ1]
      module
    rw [hD1]
    dsimp [R₁]
    rw [e21_clm_smul_mul, e21_clm_mul_smul, hQ1_idem]
    refine ContinuousLinearMap.ext fun u => ?_
    change (E - b) • ((E - b)⁻¹ • (1 - P₁) u) = (1 - P₁) u
    rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hE1), one_smul]
  have hR_nest := nested_mul_right P₀ P₁ hP0_sa hP1_sa h_nest
  have hS_idem : intermediateShell P₀ P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ :=
    intermediateShell_idempotent P₀ P₁ hP0_idem hP1_idem h_nest hR_nest
  have hSR01 : intermediateShell P₀ P₁ * R₀₁ = R₀₁ := by
    dsimp [R₀₁]; rw [e21_clm_mul_smul, hS_idem]
  have hR1_mat : R₁ = mat21CLM ((E - b)⁻¹ • !![0, 0, 0; 0, 1, 0; 0, 0, 0]) := by
    dsimp [R₁]; rw [hQ1_mat, mat21CLM_smul]; rfl
  have hSH1S : intermediateShell P₀ P₁ * H₁ * intermediateShell P₀ P₁ =
      (c - g₂ ^ 2 / (E - b)) • intermediateShell P₀ P₁ := by
    have hS_H_S : intermediateShell P₀ P₁ * H * intermediateShell P₀ P₁ =
        c • intermediateShell P₀ P₁ := by
      rw [hS_mat, mat21CLM_smul]
      dsimp [H]; rw [mat21CLM_mul, mat21CLM_mul]; apply congrArg mat21CLM
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hS_HR1H_S : intermediateShell P₀ P₁ * H * R₁ * H * intermediateShell P₀ P₁ =
        (-(g₂ ^ 2 / (E - b))) • intermediateShell P₀ P₁ := by
      rw [hS_mat, mat21CLM_smul, hR1_mat]
      dsimp [H]
      have hSH : !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1] * !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] =
          !![0, 0, 0; 0, 0, 0; -g₁, -g₂, c] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      have hHS : !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] * !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1] =
          !![0, 0, g₁; 0, 0, g₂; 0, 0, c] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
      simp only [mat21CLM_mul]
      rw [hSH, mul_assoc _ _ !![(0 : ℝ), 0, 0; 0, 0, 0; 0, 0, 1], hHS]
      apply congrArg mat21CLM
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp [Matrix.mul_apply, Fin.sum_univ_three, div_eq_mul_inv]; try ring)
    have hSP1 : intermediateShell P₀ P₁ * P₁ = intermediateShell P₀ P₁ :=
      intermediateShell_mul_P1 P₀ P₁ hP1_idem h_nest
    have hP1S : P₁ * intermediateShell P₀ P₁ = intermediateShell P₀ P₁ :=
      P1_mul_intermediateShell P₀ P₁ hP1_idem hR_nest
    dsimp [H₁, effectiveHamiltonian]
    calc intermediateShell P₀ P₁ * (P₁ * H * P₁ + P₁ * H * R₁ * H * P₁) *
            intermediateShell P₀ P₁
        = (intermediateShell P₀ P₁ * P₁) * H * (P₁ * intermediateShell P₀ P₁) +
            (intermediateShell P₀ P₁ * P₁) * H * R₁ * H * (P₁ * intermediateShell P₀ P₁) := by
              noncomm_ring
      _ = intermediateShell P₀ P₁ * H * intermediateShell P₀ P₁ +
            intermediateShell P₀ P₁ * H * R₁ * H * intermediateShell P₀ P₁ := by
              rw [hSP1, hP1S]
      _ = (c - g₂ ^ 2 / (E - b)) • intermediateShell P₀ P₁ := by
            rw [hS_H_S, hS_HR1H_S]
            module
  have hDR01 : intermediateDenominator P₀ P₁ H₁ E * R₀₁ = intermediateShell P₀ P₁ := by
    have hD01 : intermediateDenominator P₀ P₁ H₁ E =
        (E - (c - g₂ ^ 2 / (E - b))) • intermediateShell P₀ P₁ := by
      dsimp [intermediateDenominator]
      rw [hSH1S]
      module
    rw [hD01]
    dsimp [R₀₁]
    rw [e21_clm_smul_mul, e21_clm_mul_smul, hS_idem]
    refine ContinuousLinearMap.ext fun u => ?_
    change (E - (c - g₂ ^ 2 / (E - b))) • ((E - (c - g₂ ^ 2 / (E - b)))⁻¹ •
      intermediateShell P₀ P₁ u) = intermediateShell P₀ P₁ u
    rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hE01), one_smul]
  have hTrans :
      effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁) = effectiveHamiltonian P₀ H₁ R₀₁ :=
    effectiveHamiltonian_schur_transitive P₀ P₁ H R₁ R₀₁ E
      hP1_idem hP0_sa hP1_sa hH_sa h_nest hQR1 hDR1 hSR01 hDR01
  have hSA_H1 : IsKreinSelfAdjoint H₁ :=
    effectiveHamiltonian_kreinSelfAdjoint P₁ H R₁ E hP1_sa hH_sa hQR1 hDR1
  have hSupp0 : (1 - P₀) * nestedResolvent H R₁ R₀₁ = nestedResolvent H R₁ R₀₁ :=
    nestedResolvent_support P₀ P₁ H R₁ R₀₁ hP0_idem h_nest hQR1 hSR01
  have hD0 : denominator P₀ H E * nestedResolvent H R₁ R₀₁ = 1 - P₀ :=
    denominator_mul_nestedResolvent P₀ P₁ H R₁ R₀₁ E
      hP0_idem hP1_idem h_nest hR_nest hQR1 hDR1 hSR01 hDR01
  have hSA_0 : IsKreinSelfAdjoint (effectiveHamiltonian P₀ H (nestedResolvent H R₁ R₀₁)) :=
    effectiveHamiltonian_kreinSelfAdjoint P₀ H (nestedResolvent H R₁ R₀₁) E hP0_sa hH_sa hSupp0 hD0
  have hSA_01 : IsKreinSelfAdjoint (effectiveHamiltonian P₀ H₁ R₀₁) := by
    rw [← hTrans]; exact hSA_0
  have hEff01 :
      effectiveHamiltonian P₀ H₁ R₀₁ =
        (a + v ^ 2 / (E - b) -
          (g₁ + v * g₂ / (E - b)) ^ 2 / (E - (c - g₂ ^ 2 / (E - b)))) • P₀ := by
    have hH1_eq : H₁ = mat21CLM
        (!![1, 0, 0; 0, 0, 0; 0, 0, 1] * !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] *
          !![1, 0, 0; 0, 0, 0; 0, 0, 1] +
         !![1, 0, 0; 0, 0, 0; 0, 0, 1] * !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] *
          ((E - b)⁻¹ • !![0, 0, 0; 0, 1, 0; 0, 0, 0]) *
          !![a, v, g₁; v, b, g₂; -g₁, -g₂, c] * !![1, 0, 0; 0, 0, 0; 0, 0, 1]) := by
      dsimp [H₁, effectiveHamiltonian, P₁, H]
      rw [hR1_mat]
      simp only [mat21CLM_mul, mat21CLM_add]
      rfl
    have hR01_eq : R₀₁ = mat21CLM
        ((E - (c - g₂ ^ 2 / (E - b)))⁻¹ • !![0, 0, 0; 0, 0, 0; 0, 0, 1]) := by
      dsimp [R₀₁]; rw [hS_mat, mat21CLM_smul]; rfl
    rw [hH1_eq, hR01_eq]
    dsimp [effectiveHamiltonian, P₀]
    simp only [mat21CLM_mul, mat21CLM_add]
    rw [mat21CLM_smul]
    exact congrArg mat21CLM (mat21_eff01_matrix_eq a b c v g₁ g₂ E)
  exact ⟨⟨he0_inner, he2_inner, hP0_e0, hS_e2⟩, hNotHilb,
    ⟨hP0_idem, hP1_idem, h_nest, hP0_sa, hP1_sa, hH_sa⟩,
    ⟨hQR1, hDR1, hSR01, hDR01⟩,
    ⟨hTrans, hSA_H1, hSA_0, hSA_01⟩,
    ⟨hSH1S, hEff01⟩⟩

end IndefiniteKreinWitness

end InfoGeometry.Physics.NuclearRealKreinFeshbach
