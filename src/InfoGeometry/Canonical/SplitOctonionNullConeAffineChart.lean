import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionNullConeProjectiveTopology

/-!
# The affine `a ≠ 0` chart of the projective split-octonion null cone

On the open part where the upper-left scalar is nonzero, every projective
null ray has the unique normalization `a = 1`.  This file records the
normalization and an explicit null representative; it makes no claim about a
global projective atlas or compactification.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.OperatorAlgebra.KreinIsotropicCone
open InfoGeometry.Physics.ZornMatrixSU3

abbrev SplitZornAffineNullChart :=
  {X : SplitZornNonzeroNull // (X.1 : SplitZornMatrix).a ≠ 0}

def splitZornNullNormalize
  (X : SplitZornAffineNullChart) : SplitZornNonzeroNull :=
  ⟨(((X.1 : SplitZornMatrix).a)⁻¹) • (X.1 : SplitZornMatrix),
    splitZornNullCone_smul ((X.1 : SplitZornMatrix).a)⁻¹
      (X.1 : SplitZornMatrix) X.1.2.1,
    smul_ne_zero (inv_ne_zero X.2) X.1.2.2⟩

@[simp] theorem splitZornNullNormalize_a
    (X : SplitZornAffineNullChart) :
    (splitZornNullNormalize X).1.a = 1 := by
  simp [splitZornNullNormalize, X.2]

theorem splitZornNullNormalize_sameRay
    (X : SplitZornAffineNullChart) :
  SameProjectiveRay X.1.1 (splitZornNullNormalize X).1 := by
  exact ⟨((X.1 : SplitZornMatrix).a)⁻¹, inv_ne_zero X.2, rfl⟩

theorem splitZornNullNormalize_projection_eq
    (X : SplitZornAffineNullChart) :
    splitZornNullRayProjection X.1 =
      splitZornNullRayProjection (splitZornNullNormalize X) := by
  apply Quotient.sound
  exact splitZornNullNormalize_sameRay X

def splitZornAffineNullRepresentative
    (u v : Fin 3 → ℝ) : SplitZornMatrix where
  a := 1
  b := InfoGeometry.Physics.ZornMatrixSU3.dotProduct u v
  x := u
  y := v

theorem splitZornAffineNullRepresentative_mem
    (u v : Fin 3 → ℝ) :
    splitZornAffineNullRepresentative u v ∈ splitZornNullCone := by
  rw [mem_splitZornNullCone_iff]
  simp [splitZornAffineNullRepresentative]

theorem splitZornAffineNullRepresentative_ne_zero
    (u v : Fin 3 → ℝ) :
    splitZornAffineNullRepresentative u v ≠ 0 := by
  intro h
  have ha := congrArg (fun X : SplitZornMatrix => X.a) h
  simpa [splitZornAffineNullRepresentative] using ha

def splitZornAffineNullPoint
    (u v : Fin 3 → ℝ) : SplitZornNonzeroNull :=
  ⟨splitZornAffineNullRepresentative u v,
    splitZornAffineNullRepresentative_mem u v,
    splitZornAffineNullRepresentative_ne_zero u v⟩

@[simp] theorem splitZornAffineNullPoint_a
    (u v : Fin 3 → ℝ) :
    (splitZornAffineNullPoint u v).1.a = 1 := by
  rfl

end

end InfoGeometry.Canonical
