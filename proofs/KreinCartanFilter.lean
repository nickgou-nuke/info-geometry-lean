import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Cartan-Krein Filtering for 2x2 Image Patches
-/

namespace KreinCartan

variable (R : Type*) [CommRing R]

/-- Define a 2x2 matrix representing a local image patch -/
abbrev ImagePatch := Matrix (Fin 2) (Fin 2) R

variable [Invertible (2 : R)]

/-- Cartan Decomposition: Symmetric Part -/
def symmPart (M : ImagePatch R) : ImagePatch R :=
  (invOf (2 : R)) • (M + Mᵀ)

/-- Cartan Decomposition: Antisymmetric Part -/
def antiSymmPart (M : ImagePatch R) : ImagePatch R :=
  (invOf (2 : R)) • (M - Mᵀ)

/-- Every matrix decomposes into a symmetric and antisymmetric part -/
lemma cartan_decomp (M : ImagePatch R) :
  M = symmPart R M + antiSymmPart R M := by
  dsimp [symmPart, antiSymmPart]
  rw [← smul_add]
  have h : M + Mᵀ + (M - Mᵀ) = M + M := by abel
  rw [h, ← two_smul R M, smul_smul, invOf_mul_self, one_smul]

/-- The Krein metric is the determinant of the patch -/
def kreinMetric (M : ImagePatch R) : R :=
  Matrix.det M

end KreinCartan

namespace KreinCartan.Real

open KreinCartan

variable {R : Type*} [LinearOrderedRing R] [CommRing R]

/-- V+ : Elliptic region (Background / Noise dominant) -/
def IsPositiveKrein (M : ImagePatch R) : Prop :=
  kreinMetric R M > 0

/-- V- : Hyperbolic region (Gradient / Texture dominant) -/
def IsNegativeKrein (M : ImagePatch R) : Prop :=
  kreinMetric R M < 0

/-- Null Space : Parabolic region (Exact contour boundary) -/
def IsNullKrein (M : ImagePatch R) : Prop :=
  kreinMetric R M = 0

end KreinCartan.Real
