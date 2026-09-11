import InfoGeometry.Canonical.RealMirrorComplexStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def doubledSheetExchange : (V × V) →ₗ[ℝ] (V × V) where
  toFun p := (p.2, p.1)
  map_add' p q := by
    ext <;> rfl
  map_smul' a p := by
    ext <;> rfl

def doubledOppositeComplexStructure
    (I : V →ₗ[ℝ] V) : (V × V) →ₗ[ℝ] (V × V) where
  toFun p := (I p.1, -(I p.2))
  map_add' p q := by
    ext <;> simp [map_add, add_comm]
  map_smul' a p := by
    ext <;> simp

theorem doubledSheetExchange_sq :
    (doubledSheetExchange (V := V)).comp doubledSheetExchange =
      LinearMap.id := by
  ext p <;> rfl

theorem doubledOppositeComplexStructure_sq
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I) :
    (doubledOppositeComplexStructure I).comp
        (doubledOppositeComplexStructure I) =
      -LinearMap.id := by
  apply LinearMap.ext
  intro p
  change (I (I p.1), -(I (-(I p.2)))) = (-p.1, -p.2)
  rw [realComplexStructure_apply_sq I hI, map_neg,
    realComplexStructure_apply_sq I hI]
  simp

theorem doubledSheetExchange_anticommutes
    (I : V →ₗ[ℝ] V) :
    (doubledSheetExchange (V := V)).comp
        (doubledOppositeComplexStructure I) =
      -(doubledOppositeComplexStructure I).comp
        doubledSheetExchange := by
  ext p <;> simp [doubledSheetExchange, doubledOppositeComplexStructure,
    LinearMap.comp_apply, add_comm, sub_eq_add_neg]

/-!
The real doubled formulation keeps three properties separate:

* `mirror` is a real-linear involution;
* anticommutation with a real complex structure gives complex antilinearity;
* skew-adjointness is an additional property relative to a chosen bilinear
  form.

In particular, anticommutation does not imply skew-adjointness.
-/

def IsRealMirror (J : V ≃ₗ[ℝ] V) : Prop :=
  J.toLinearMap.comp J.toLinearMap = LinearMap.id

def IsBilinearSkew
    (B : V → V → ℝ) (J : V →ₗ[ℝ] V) : Prop :=
  ∀ v w, B (J v) w = -B v (J w)

theorem realMirror_is_involutive
    (J : V ≃ₗ[ℝ] V) (hJ : IsRealMirror J) (v : V) :
    J (J v) = v := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hJ
  simpa [IsRealMirror, LinearMap.comp_apply] using h

theorem realMirror_is_complex_antilinear_of_anticommute
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap) :
    IsComplexAntilinearMirror I J :=
  mirror_is_complex_antilinear I J hJI

theorem realMirror_reverses_complex_structure
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap) (v : V) :
    J (I v) = -(I (J v)) := by
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hJI
  simpa [LinearMap.comp_apply] using h

theorem realMirror_skew_is_independent
    (B : V → V → ℝ) (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap)
    (hskew : IsBilinearSkew B J.toLinearMap) :
    IsComplexAntilinearMirror I J := by
  exact realMirror_is_complex_antilinear_of_anticommute I J hJI

end

end InfoGeometry.Canonical
