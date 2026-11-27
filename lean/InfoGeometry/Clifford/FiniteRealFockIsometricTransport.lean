/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockExteriorDerivation

/-!
# Isometric transport of the full quadratic real Fock representation

The existing exterior coordinates already preserve the actual positive Fock
norm. Bundling that exact map as a linear isometry equivalence supplies the
native star-algebra conjugation equivalence. Consequently adjoints, Lie brackets
and noncommutation survive transport to the actual finite Euclidean coordinates.
This does not identify any separate Zorn or phase carrier with these coordinates.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford InfoGeometry.CliffordExteriorLift

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

local instance fockTransportFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SpinorSpace (Vector n)) :=
  ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra).finiteDimensional_of_finite

local instance fockTransportCompleteSpace (n : ℕ) :
    CompleteSpace (SpinorSpace (Vector n)) :=
  FiniteDimensional.complete ℝ (SpinorSpace (Vector n))

/-- The existing exact exterior coordinates, with their already proved norm. -/
def fockCoordinatesLinearIsometryEquiv (n : ℕ) :
    SpinorSpace (Vector n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Finset (Fin n)) where
  toLinearEquiv := fockCoordinates n
  norm_map' x := (fock_norm_eq_coordinates n x).symm

@[simp] theorem fockCoordinatesLinearIsometryEquiv_apply (n : ℕ)
    (x : SpinorSpace (Vector n)) :
    fockCoordinatesLinearIsometryEquiv n x = fockCoordinates n x := rfl

/-- Isometric conjugation is a genuine native equivalence of star algebras. -/
def fockCoordinateConjugation (n : ℕ) :
    (SpinorSpace (Vector n) →L[ℝ] SpinorSpace (Vector n)) ≃⋆ₐ[ℝ]
      (EuclideanSpace ℝ (Finset (Fin n)) →L[ℝ] EuclideanSpace ℝ (Finset (Fin n))) :=
  (fockCoordinatesLinearIsometryEquiv n).conjStarAlgEquiv

theorem fockCoordinateConjugation_adjoint (n : ℕ)
    (A : SpinorSpace (Vector n) →L[ℝ] SpinorSpace (Vector n)) :
    (fockCoordinateConjugation n A).adjoint = fockCoordinateConjugation n A.adjoint := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (fockCoordinateConjugation n) A).symm

/-- The entire quadratic operator transported by the actual coordinate isometry. -/
def fockCoordinateQuadratic (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Finset (Fin n)) →L[ℝ] EuclideanSpace ℝ (Finset (Fin n)) :=
  fockCoordinateConjugation n (fockQuadraticCLM n M)

@[simp] theorem fockCoordinateQuadratic_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Finset (Fin n))) :
    fockCoordinateQuadratic n M y =
      fockCoordinates n (fockQuadraticCLM n M ((fockCoordinates n).symm y)) := rfl

theorem fockCoordinateQuadratic_intertwines (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x : SpinorSpace (Vector n)) :
    fockCoordinateQuadratic n M (fockCoordinates n x) =
      fockCoordinates n (fockQuadraticCLM n M x) := by
  simp only [fockCoordinateQuadratic_apply, LinearEquiv.symm_apply_apply]

/-- The coordinate operator intertwines the proved exterior derivation on every degree. -/
theorem fockCoordinateQuadratic_exteriorLift (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x : SpinorSpace (Vector n)) :
    fockCoordinateQuadratic n M (fockCoordinates n x) =
      fockCoordinates n (exteriorLift (Matrix.toLin' M) x) := by
  rw [fockCoordinateQuadratic_intertwines, fockQuadraticCLM_eq_exteriorLift_apply]

@[simp] theorem fockCoordinateQuadratic_adjoint (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (fockCoordinateQuadratic n M).adjoint = fockCoordinateQuadratic n M.transpose := by
  simp only [fockCoordinateQuadratic, fockCoordinateConjugation_adjoint,
    fockQuadraticCLM_adjoint]

theorem fockCoordinateQuadratic_isSelfAdjoint (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    IsSelfAdjoint (fockCoordinateQuadratic n M) :=
  IsSelfAdjoint.map (fockCoordinateConjugation n) (fockQuadraticCLM_isSelfAdjoint n M hM)

/-- The full Lie identity is preserved by this actual isometric transport. -/
theorem fockCoordinateQuadratic_commutator (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    (fockCoordinateQuadratic n M).comp (fockCoordinateQuadratic n N) -
        (fockCoordinateQuadratic n N).comp (fockCoordinateQuadratic n M) =
      fockCoordinateQuadratic n (M * N - N * M) := by
  have h := congrArg (fockCoordinateConjugation n) (fockQuadraticCLM_commutator n M N)
  change fockCoordinateConjugation n
    (fockQuadraticCLM n M * fockQuadraticCLM n N -
      fockQuadraticCLM n N * fockQuadraticCLM n M) = _ at h
  simp only [map_sub, map_mul] at h
  simpa only [fockCoordinateQuadratic, ContinuousLinearMap.mul_def] using h

/-- Isometric conjugation preserves and reflects noncommutation. -/
theorem fockCoordinateQuadratic_comp_commute_iff (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    (fockCoordinateQuadratic n M).comp (fockCoordinateQuadratic n N) =
        (fockCoordinateQuadratic n N).comp (fockCoordinateQuadratic n M) ↔ M * N = N * M := by
  rw [← fockQuadraticCLM_comp_commute_iff n M N]
  change fockCoordinateConjugation n (fockQuadraticCLM n M) *
      fockCoordinateConjugation n (fockQuadraticCLM n N) =
    fockCoordinateConjugation n (fockQuadraticCLM n N) *
      fockCoordinateConjugation n (fockQuadraticCLM n M) ↔
    fockQuadraticCLM n M * fockQuadraticCLM n N =
      fockQuadraticCLM n N * fockQuadraticCLM n M
  rw [← map_mul, ← map_mul]
  exact (fockCoordinateConjugation n).injective.eq_iff

/-- The explicit symmetric noncommuting pair remains self-adjoint and
noncommuting on the transported positive Hilbert carrier. -/
theorem exists_selfAdjoint_noncommuting_fockCoordinateQuadratic :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ,
      IsSelfAdjoint (fockCoordinateQuadratic 2 M) ∧
      IsSelfAdjoint (fockCoordinateQuadratic 2 N) ∧
      (fockCoordinateQuadratic 2 M).comp (fockCoordinateQuadratic 2 N) ≠
        (fockCoordinateQuadratic 2 N).comp (fockCoordinateQuadratic 2 M) := by
  obtain ⟨M, N, hM, hN, _hMN, hne⟩ := exists_symmetric_noncommuting_fockQuadraticCLM
  refine ⟨M, N, fockCoordinateQuadratic_isSelfAdjoint 2 M hM,
    fockCoordinateQuadratic_isSelfAdjoint 2 N hN, ?_⟩
  intro h
  exact hne ((fockQuadraticCLM_comp_commute_iff 2 M N).mpr
    ((fockCoordinateQuadratic_comp_commute_iff 2 M N).mp h))

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
