import InfoGeometry.Canonical.RealDoubledKreinMirror
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def realComplexScalarAction (I : V →ₗ[ℝ] V) (a b : ℝ) (v : V) : V :=
  a • v + b • I v

def IsRealComplexStructure (I : V →ₗ[ℝ] V) : Prop :=
  I.comp I = -LinearMap.id

def IsComplexAntilinearMirror
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V) : Prop :=
  ∀ (a b : ℝ) (v : V),
    J (realComplexScalarAction I a b v) =
      realComplexScalarAction I a (-b) (J v)

theorem mirror_is_complex_antilinear
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap) :
    IsComplexAntilinearMirror I J := by
  intro a b v
  unfold realComplexScalarAction
  simp only [map_add, map_smul]
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hJI
  change J (I v) = -(I (J v)) at h
  rw [h]
  simp [smul_neg]

theorem realComplexStructure_apply_sq
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I) (v : V) :
    I (I v) = -v := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hI
  simpa [LinearMap.comp_apply] using h

end

end InfoGeometry.Canonical
