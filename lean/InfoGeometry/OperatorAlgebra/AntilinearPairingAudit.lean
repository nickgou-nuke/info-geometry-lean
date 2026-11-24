/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Module
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Antilinear twists of sesquilinear pairings

The pairing convention is conjugate-linear in the first argument and linear in
the second. Composing the second argument with a conjugate-linear map therefore
makes both arguments conjugate-linear. On an eigenvector, the two sides of
twisted adjointness have the same conjugated eigenvalue.

This pointwise calculation does not imply that global twisted adjointness is
spectrally vacuous: if the twist is surjective and commutes with the operator,
global twisted adjointness is equivalent to ordinary symmetry for the original
pairing. In particular, positivity of that original pairing remains relevant.
The finite counterexample below uses a nondegenerate indefinite pairing.

The related Hilbert-space metric results are
`InfoGeometry.Krein.eta_biorthogonal_pairing`,
`InfoGeometry.Krein.eta_nonreal_eigenvector_null`. The existing owner of the
unbroken, nonzero symmetry eigenline theorem is
`InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance.wigner_antilinear_time_reversal`.
The linear-twist cancellation below is purely algebraic and does not require
a Hilbert space or a continuous metric operator. The concrete complex vector
space below is a finite countermodel at the analytic scalar boundary, not a
proposed replacement of a real operator carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AntilinearPairingAudit

section StarRing

variable {R V : Type*} [CommRing R] [StarRing R]
variable [AddCommGroup V] [Module R V]

/-- An antilinear twist in the second slot of a sesquilinear pairing conjugates
the scalar in each slot. No positivity, involutivity, or spectral assumption is
used. -/
theorem twisted_pairing_smul_smul
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (K : V →ₛₗ[starRingEnd R] V) (a b : R) (u v : V) :
    B (a • u) (K (b • v)) = (star a * star b) * B u (K v) := by
  rw [LinearMap.map_smulₛₗ₂, K.map_smulₛₗ, (B u).map_smul]
  exact (mul_assoc _ _ _).symm

/-- Both sides of twisted adjointness on a single eigenvector have coefficient
`star E`. This does not assume either global adjointness or commutation. -/
theorem twisted_eigenvector_pairings
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (K : V →ₛₗ[starRingEnd R] V) (H : V →ₗ[R] V)
    (v : V) (E : R) (hEigen : H v = E • v) :
    B (H v) (K v) = star E * B v (K v) ∧
      B v (K (H v)) = star E * B v (K v) := by
  constructor
  · simpa only [hEigen, starRingEnd_apply, smul_eq_mul] using
      (LinearMap.map_smulₛₗ₂ B E v (K v))
  · rw [hEigen, K.map_smulₛₗ, (B v).map_smul, starRingEnd_apply, smul_eq_mul]

/-- The diagonal twisted-adjointness equation holds on every eigenvector,
including eigenvectors with non-real eigenvalues. -/
theorem twisted_adjointness_on_eigenvector
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (K : V →ₛₗ[starRingEnd R] V) (H : V →ₗ[R] V)
    (v : V) (E : R) (hEigen : H v = E • v) :
    B (H v) (K v) = B v (K (H v)) := by
  obtain ⟨hLeft, hRight⟩ := twisted_eigenvector_pairings B K H v E hEigen
  exact hLeft.trans hRight.symm

/-- Commuting an antilinear symmetry past the operator leaves the same
conjugated eigenvalue in the second slot. -/
theorem commuting_twisted_eigenvector_pairing
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (K : V →ₛₗ[starRingEnd R] V) (H : V →ₗ[R] V)
    (hComm : ∀ w, H (K w) = K (H w))
    (v : V) (E : R) (hEigen : H v = E • v) :
    B v (H (K v)) = star E * B v (K v) := by
  rw [hComm v]
  exact (twisted_eigenvector_pairings B K H v E hEigen).2

/-- A linear twist has coefficient `E` in the second slot. Twisted adjointness
and a nonzero diagonal pairing therefore force `star E = E`. Only the scalar
ring has a no-zero-divisors hypothesis; the form need not be positive,
nondegenerate, Hermitian, or induced by a Hilbert inner product. -/
theorem eigenvalue_star_eq_of_linear_twist [NoZeroDivisors R]
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (η H : V →ₗ[R] V) (v : V) (E : R)
    (hEigen : H v = E • v)
    (hAdj : B (H v) (η v) = B v (η (H v)))
    (hNonzero : B v (η v) ≠ 0) : star E = E := by
  have hScalar : star E * B v (η v) = E * B v (η v) := by
    calc
      star E * B v (η v) = B (H v) (η v) := by
        rw [hEigen, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
      _ = B v (η (H v)) := hAdj
      _ = E * B v (η v) := by
        rw [hEigen, η.map_smul, (B v).map_smul, smul_eq_mul]
  have hProduct : (star E - E) * B v (η v) = 0 := by
    rw [sub_mul, hScalar, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hNonzero)

/-- For a surjective commuting twist, global twisted adjointness is exactly
ordinary symmetry for `B`. Thus the pointwise eigenvector tautology does not
remove the consequences of a positive definite original pairing. -/
theorem twisted_symmetry_iff_symmetry_of_surjective
    (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R)
    (K : V →ₛₗ[starRingEnd R] V) (H : V →ₗ[R] V)
    (hComm : ∀ v, H (K v) = K (H v))
    (hSurj : Function.Surjective K) :
    (∀ u v, B (H u) (K v) = B u (K (H v))) ↔
      (∀ u v, B (H u) v = B u (H v)) := by
  constructor
  · intro h u w
    obtain ⟨v, rfl⟩ := hSurj w
    rw [h u v, hComm v]
  · intro h u v
    rw [h u (K v), hComm v]

end StarRing

namespace ConjugateSwapCounterexample

/-- The linear operator with matrix `diag(I, -I)` on the native `Fin 2 → ℂ`
module. -/
def hamiltonian : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![Complex.I * v 0, -Complex.I * v 1]
  map_add' u v := by
    funext j
    fin_cases j <;> simp [mul_add]
  map_smul' c v := by
    funext j
    fin_cases j <;> simp [mul_left_comm]

/-- The conjugate-linear swap `(z₀,z₁) ↦ (star z₁,star z₀)`. -/
def conjugateSwap : (Fin 2 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 2 → ℂ) where
  toFun v := ![star (v 1), star (v 0)]
  map_add' u v := by
    funext j
    fin_cases j <;> simp
  map_smul' c v := by
    rw [starRingEnd_apply]
    funext j
    fin_cases j <;> simp

/-- The nondegenerate indefinite Hermitian cross-form with metric matrix
`[[0,1],[1,0]]`. -/
def crossForm : (Fin 2 → ℂ) →ₛₗ[starRingEnd ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun (u v : Fin 2 → ℂ) => star (u 0) * v 1 + star (u 1) * v 0)
    (by
      intro u u' v
      simp only [Pi.add_apply, star_add]
      ring)
    (by
      intro c u v
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, starRingEnd_apply]
      ring)
    (by
      intro u v v'
      simp only [Pi.add_apply]
      ring)
    (by
      intro c u v
      simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring)

/-- The eigenvector `(1,0)` of the imaginary eigenvalue `I`. -/
def eigenvector : Fin 2 → ℂ := ![1, 0]

theorem conjugateSwap_involutive : Function.Involutive conjugateSwap := by
  intro v
  funext j
  fin_cases j <;> simp [conjugateSwap]

theorem hamiltonian_commutes_conjugateSwap (v : Fin 2 → ℂ) :
    hamiltonian (conjugateSwap v) = conjugateSwap (hamiltonian v) := by
  funext j
  fin_cases j <;> simp [hamiltonian, conjugateSwap, Complex.star_def]

theorem crossForm_hermitian (u v : Fin 2 → ℂ) :
    star (crossForm u v) = crossForm v u := by
  change star (star (u 0) * v 1 + star (u 1) * v 0) =
    star (v 0) * u 1 + star (v 1) * u 0
  simp only [star_add, star_mul, star_star]
  ring

theorem crossForm_nondegenerate (u : Fin 2 → ℂ)
    (hu : ∀ v, crossForm u v = 0) : u = 0 := by
  have h0 : u 0 = 0 := by
    simpa [crossForm] using hu ![0, 1]
  have h1 : u 1 = 0 := by
    simpa [crossForm] using hu ![1, 0]
  funext j
  fin_cases j <;> simp [h0, h1]

/-- The original form takes both positive and negative real diagonal values.
It is therefore not a positive definite Hilbert inner product. -/
theorem crossForm_positive_and_negative :
    crossForm ![1, 1] ![1, 1] = 2 ∧
      crossForm ![1, -1] ![1, -1] = -2 := by
  constructor <;> norm_num [crossForm]

theorem hamiltonian_crossForm_symmetric (u v : Fin 2 → ℂ) :
    crossForm (hamiltonian u) v = crossForm u (hamiltonian v) := by
  simp [crossForm, hamiltonian, Complex.star_def]; ring

/-- Full global twisted adjointness holds in this countermodel, as does
ordinary symmetry for the indefinite cross-form. -/
theorem hamiltonian_twisted_crossForm_symmetric (u v : Fin 2 → ℂ) :
    crossForm (hamiltonian u) (conjugateSwap v) =
      crossForm u (conjugateSwap (hamiltonian v)) :=
  (twisted_symmetry_iff_symmetry_of_surjective crossForm conjugateSwap hamiltonian
    hamiltonian_commutes_conjugateSwap conjugateSwap_involutive.surjective).2
      hamiltonian_crossForm_symmetric u v

theorem eigenvector_ne_zero : eigenvector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp [eigenvector] at h0

theorem hamiltonian_eigenvector :
    hamiltonian eigenvector = Complex.I • eigenvector := by
  funext j
  fin_cases j <;> simp [hamiltonian, eigenvector]

theorem eigenvalue_nonreal : Complex.I.im ≠ 0 := by
  simp

theorem crossForm_eigenvector_self : crossForm eigenvector eigenvector = 0 := by
  simp [crossForm, eigenvector]

theorem crossForm_eigenvector_twist :
    crossForm eigenvector (conjugateSwap eigenvector) = 1 := by
  simp [crossForm, eigenvector, conjugateSwap]

/-- This eigenline is not an unbroken symmetry eigenline; hence the existing
Wigner reality theorem does not apply to it. -/
theorem conjugateSwap_eigenvector_not_smul (c : ℂ) :
    conjugateSwap eigenvector ≠ c • eigenvector := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  simp [eigenvector, conjugateSwap] at h1

end ConjugateSwapCounterexample

end InfoGeometry.OperatorAlgebra.AntilinearPairingAudit

end
