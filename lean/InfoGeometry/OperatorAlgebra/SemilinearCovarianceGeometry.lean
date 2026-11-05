/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
import InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry
import InfoGeometry.OperatorAlgebra.CovarianceStationary
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Semilinear symmetry of evolution, stationary covariance, and amplitudes

The concrete sheet exchange transports the native matrix exponential and the
existing covariance update. A strict contraction with invariant transition and
noise has a unique positive stationary covariance, whose exchange symmetry is
proved from uniqueness. Odd Hermitian observables therefore have zero pairing
with that constructed stationary covariance.

The final bridge transports the ordered amplitude quotient through the same
automorphism. None of these finite operator statements identifies the symmetry
with a spacetime CPT action or assumes a negative-energy sector.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry

open Matrix Filter
open scoped Topology ComplexOrder Matrix.Norms.L2Operator
open InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
open InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.OperatorAlgebra.CovarianceContraction
open InfoGeometry.OperatorAlgebra.CovarianceStationary

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => SheetMatrix n

local instance : NormedAlgebra ℚ Mat := NormedAlgebra.restrictScalars ℚ ℂ Mat

/-- Finite dimensionality turns the native real linear equivalence into a continuous map. -/
theorem continuous_sheetConj : Continuous (sheetConj : Mat → Mat) :=
  (sheetConj : Mat ≃ₐ[ℝ] Mat).toLinearMap.continuous_of_finiteDimensional

/-- This transports the actual norm-convergent native matrix exponential. -/
theorem sheetConj_exp (X : Mat) :
    sheetConj (NormedSpace.exp X) = NormedSpace.exp (sheetConj X) :=
  NormedSpace.map_exp (sheetConj : Mat ≃ₐ[ℝ] Mat).toRingHom continuous_sheetConj X

/-- Finite matrix evolution with the conventional imaginary coefficient. -/
def matrixEvolution (H : Mat) (t : ℝ) : Mat :=
  NormedSpace.exp (t • (-Complex.I • H))

theorem matrixEvolution_zero (H : Mat) : matrixEvolution H 0 = 1 := by
  simp [matrixEvolution]

/-- The one-parameter composition law follows from commuting scalar multiples of one generator. -/
theorem matrixEvolution_add (H : Mat) (s t : ℝ) :
    matrixEvolution H (s + t) = matrixEvolution H s * matrixEvolution H t := by
  unfold matrixEvolution
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl (-Complex.I • H)).smul_left s).smul_right t)

/-- Hermitian generators give genuine unitary evolution in the full matrix algebra. -/
theorem matrixEvolution_mem_unitary {H : Mat} (hH : H.IsHermitian) (t : ℝ) :
    matrixEvolution H t ∈ unitary Mat := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (t • (-Complex.I • H)) = -(t • (-Complex.I • H))
  simp [star_smul, hH.isSelfAdjoint.star_eq]

/-- Conjugate linearity reverses time while preserving the transformed Hamiltonian. -/
theorem sheetConj_matrixEvolution (H : Mat) (t : ℝ) :
    sheetConj (matrixEvolution H t) = matrixEvolution (sheetConj H) (-t) := by
  rw [matrixEvolution, sheetConj_exp, map_smul, sheetConj_smul]
  simp [matrixEvolution]

theorem sheetConj_matrixEvolution_of_even {H : Mat}
    (hH : sheetConj H = H) (t : ℝ) :
    sheetConj (matrixEvolution H t) = matrixEvolution H (-t) := by
  rw [sheetConj_matrixEvolution, hH]

/-- The full affine covariance update is equivariant under the concrete semilinear symmetry. -/
theorem sheetConj_covarianceStep (T Q C : Mat) :
    sheetConj (covarianceStep T Q C) =
      covarianceStep (sheetConj T) (sheetConj Q) (sheetConj C) := by
  simp only [covarianceStep, map_add, map_mul, sheetConj_star]

theorem sheetConj_covariance_iterate (T Q C : Mat) (k : ℕ) :
    sheetConj ((covarianceStep T Q)^[k] C) =
      (covarianceStep (sheetConj T) (sheetConj Q))^[k] (sheetConj C) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        sheetConj_covarianceStep, ih]

/-- Symmetry of a stationary covariance is derived from contraction uniqueness. -/
theorem stationary_covariance_invariant {T Q S : Mat} (hT : ‖T‖ < 1)
    (hTeven : sheetConj T = T) (hQeven : sheetConj Q = Q)
    (hS : covarianceStep T Q S = S) : sheetConj S = S := by
  apply stationary_unique_of_norm_lt_one T Q hT _ hS
  calc
    covarianceStep T Q (sheetConj S) = sheetConj (covarianceStep T Q S) := by
      rw [sheetConj_covarianceStep, hTeven, hQeven]
    _ = sheetConj S := congrArg sheetConj hS

/-- The invariant positive covariance is constructed, not supplied as a structure field. -/
theorem existsUnique_invariant_posSemidef_stationary (T Q : Mat)
    (hT : ‖T‖ < 1) (hQ : Q.PosSemidef)
    (hTeven : sheetConj T = T) (hQeven : sheetConj Q = Q) :
    ∃! S : Mat, S.PosSemidef ∧ covarianceStep T Q S = S ∧ sheetConj S = S := by
  obtain ⟨S, hS, huniq⟩ := existsUnique_posSemidef_stationary T Q hT hQ
  refine ⟨S, ⟨hS.1, hS.2,
    stationary_covariance_invariant hT hTeven hQeven hS.2⟩, ?_⟩
  intro C hC
  exact huniq C ⟨hC.1, hC.2.1⟩

/-- Odd Hermitian moments vanish at every positive stationary point of this contraction. -/
theorem stationary_odd_trace_zero {T Q S A : Mat} (hT : ‖T‖ < 1)
    (hTeven : sheetConj T = T) (hQeven : sheetConj Q = Q)
    (hSpos : S.PosSemidef) (hS : covarianceStep T Q S = S)
    (hA : A.IsHermitian) (hAodd : sheetConj A = -A) :
    trace (S * A) = 0 :=
  trace_mul_eq_zero_of_even_odd hSpos.isHermitian hA
    (stationary_covariance_invariant hT hTeven hQeven hS) hAodd

/-- All initial matrices converge to the invariant positive point, with all odd moments zero. -/
theorem exists_invariant_stationary_limit (T Q : Mat)
    (hT : ‖T‖ < 1) (hQ : Q.PosSemidef)
    (hTeven : sheetConj T = T) (hQeven : sheetConj Q = Q) :
    ∃ S : Mat, S.PosSemidef ∧ covarianceStep T Q S = S ∧ sheetConj S = S ∧
      (∀ C : Mat, Tendsto (fun k : ℕ => (covarianceStep T Q)^[k] C) atTop (𝓝 S)) ∧
      (∀ A : Mat, A.IsHermitian → sheetConj A = -A → trace (S * A) = 0) := by
  obtain ⟨S, hS, _⟩ := existsUnique_invariant_posSemidef_stationary T Q hT hQ hTeven hQeven
  refine ⟨S, hS.1, hS.2.1, hS.2.2,
    fun C => tendsto_covariance_iterates T Q hT hS.2.1 C, ?_⟩
  intro A hA hAodd
  exact trace_mul_eq_zero_of_even_odd hS.1.isHermitian hA hS.2.2 hAodd

/-- Transport of the amplitude quotient uses the induced native map on units. -/
theorem sheetConj_matrixAmplitudeQuotient (H : Mat) (g : Matˣ) :
    sheetConj (matrixAmplitudeQuotient H g) =
      matrixAmplitudeQuotient (sheetConj H)
        (Units.map (sheetConj : Mat ≃ₐ[ℝ] Mat).toMonoidHom g) := by
  simp only [matrixAmplitudeQuotient_eq, sheetConj_lie, map_mul,
    Units.coe_map, Units.coe_map_inv]
  rfl

end InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry
