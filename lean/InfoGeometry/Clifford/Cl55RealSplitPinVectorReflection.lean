import Mathlib.LinearAlgebra.Reflection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinKernelBridge
import InfoGeometry.Clifford.Cl55WittQuadraticReflection

namespace InfoGeometry.Clifford.Clifford55

/-!
# Normalized anisotropic-vector inversion

This is the native Clifford calculation needed before a general
Cartan--Dieudonné argument can be connected to the corrected split subgroup.
-/

theorem normalizedVectorUnit_inv_coe
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    (↑((normalizedVectorUnit v hunit)⁻¹) : Cl55) =
      (Q55 v) • ι55 v := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [normalizedVectorUnit_coe]
  rcases hv with hv | hv
  · simp [hv, CliffordAlgebra.ι_sq_scalar]
  · simp [hv, CliffordAlgebra.ι_sq_scalar]

theorem normalizedVector_twistedAdj
    (v x : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v))
    (hu : normalizedVectorUnit v hunit ∈ realSplitPin55) :
    realSplitPinTwistedAdj ⟨normalizedVectorUnit v hunit, hu⟩ x =
      -((Q55 v) •
        ι55 (QuadraticMap.polar Q55 v x • v - (Q55 v) • x)) := by
  rw [realSplitPinTwistedAdj, normalizedVectorUnit_coe,
    CliffordAlgebra.involute_ι,
    normalizedVectorUnit_inv_coe v hv hunit]
  have hfactor :
      -ι55 v * ι55 x * ((Q55 v) • ι55 v) =
        -((Q55 v) • (ι55 v * ι55 x * ι55 v)) := by
    rw [mul_smul_comm]
    simp [mul_assoc]
  rw [hfactor, CliffordAlgebra.ι_mul_ι_mul_ι]

noncomputable def normalizedVectorReflection
    (v : V55) (hunit : IsUnit (Q55 v)) : V55 →ₗ[ℝ] V55 :=
  Module.preReflection v ((Q55 v) • QuadraticMap.polarBilin Q55 v)

theorem normalizedVectorReflection_apply
    (v x : V55) (hunit : IsUnit (Q55 v)) :
    normalizedVectorReflection v hunit x =
      x - (Q55 v) • (QuadraticMap.polar Q55 v x • v) := by
  simp [normalizedVectorReflection, Module.preReflection_apply, mul_smul]

theorem normalizedVectorReflection_involutive
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    Function.Involutive (normalizedVectorReflection v hunit) := by
  apply Module.involutive_preReflection
  change Q55 v * QuadraticMap.polar Q55 v v = 2
  rw [QuadraticMap.polar_self]
  rcases hv with hv | hv <;> simp [hv]

theorem normalizedVectorUnit_mem_realSplitPin
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    normalizedVectorUnit v hunit ∈ realSplitPin55 := by
  apply Subgroup.subset_closure
  exact ⟨v, hv, (normalizedVectorUnit_coe v hunit).symm⟩

theorem normalizedVector_action_apply_ι
    (v x : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v))
    (hu : normalizedVectorUnit v hunit ∈ realSplitPin55) :
    ι55 (realSplitPinTwistedAction
      ⟨normalizedVectorUnit v hunit, hu⟩ x) =
      ι55 (normalizedVectorReflection v hunit x) := by
  rw [realSplitPinTwistedAction_apply_ι]
  rw [normalizedVector_twistedAdj v x hv hunit hu]
  rw [normalizedVectorReflection_apply]
  rcases hv with hv | hv <;> simp [hv, smul_sub, smul_smul]

theorem normalizedVectorReflection_eq_quadraticReflection
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    normalizedVectorReflection v hunit =
    quadraticReflection v (by
        rcases hv with hv | hv <;> simp [hv]) := by
  have hne : Q55 v ≠ 0 := by
    rcases hv with hv | hv <;> simp [hv]
  apply LinearMap.ext
  intro x
  change normalizedVectorReflection v hunit x = quadraticReflection v hne x
  rw [normalizedVectorReflection_apply, quadraticReflection_apply,
    QuadraticMap.polar_comm]
  rcases hv with hv | hv
  · simp [hv]
  · simp [hv, div_eq_mul_inv]

theorem normalizedVectorReflection_preserves_Q55
    (v x : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    Q55 (normalizedVectorReflection v hunit x) = Q55 x := by
  let g : realSplitPin55 :=
    ⟨normalizedVectorUnit v hunit,
      normalizedVectorUnit_mem_realSplitPin v hv hunit⟩
  have hvec : realSplitPinTwistedAction g x =
      normalizedVectorReflection v hunit x := by
    apply ι55_injective
    exact normalizedVector_action_apply_ι v x hv hunit g.property
  rw [← hvec]
  exact realSplitPinTwistedAction_preserves_Q55 g x

noncomputable def normalizedVectorReflectionIsometry
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) : Q55.IsometryEquiv Q55 := by
  let r : V55 ≃ₗ[ℝ] V55 :=
    LinearEquiv.ofLinear
      (normalizedVectorReflection v hunit)
      (normalizedVectorReflection v hunit)
      (by
        apply LinearMap.ext
        intro x
        exact normalizedVectorReflection_involutive v hv hunit x)
      (by
        apply LinearMap.ext
        intro x
        exact normalizedVectorReflection_involutive v hv hunit x)
  exact
    { __ := r
      map_app' := fun x =>
        normalizedVectorReflection_preserves_Q55 v x hv hunit }

@[simp] theorem normalizedVectorReflectionIsometry_apply
    (v x : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    normalizedVectorReflectionIsometry v hv hunit x =
      normalizedVectorReflection v hunit x :=
  rfl

/- The normalized Clifford generator has the corresponding native
quadratic-reflection action. -/
theorem normalizedVector_orthogonalAction_eq_quadraticReflection
    (v : V55) (hv : Q55 v = 1 ∨ Q55 v = -1)
    (hunit : IsUnit (Q55 v)) :
    realSplitPinOrthogonalAction
        ⟨normalizedVectorUnit v hunit,
          normalizedVectorUnit_mem_realSplitPin v hv hunit⟩ =
      orthogonalGroup55FromIsometry
        (quadraticReflectionIsometry v (by
          rcases hv with hv | hv <;> simp [hv])) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change realSplitPinTwistedAction
      ⟨normalizedVectorUnit v hunit,
        normalizedVectorUnit_mem_realSplitPin v hv hunit⟩ x =
    quadraticReflection v (by
      rcases hv with hv | hv <;> simp [hv]) x
  apply ι55_injective
  calc
    ι55 (realSplitPinTwistedAction
        ⟨normalizedVectorUnit v hunit,
          normalizedVectorUnit_mem_realSplitPin v hv hunit⟩ x) =
        ι55 (normalizedVectorReflection v hunit x) :=
      normalizedVector_action_apply_ι v x hv hunit _
    _ = ι55 (quadraticReflection v (by
      rcases hv with hv | hv <;> simp [hv]) x) := by
      simpa using congrArg (fun f => ι55 (f x))
        (normalizedVectorReflection_eq_quadraticReflection v hv hunit)

end InfoGeometry.Clifford.Clifford55
