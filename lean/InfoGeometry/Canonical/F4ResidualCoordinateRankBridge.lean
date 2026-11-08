import Mathlib
import InfoGeometry.Canonical.F4ResidualUpperBoundTransfer
import InfoGeometry.Canonical.F4LeibnizResidualBridge
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornJordanInstance

/-!
Finite coordinate realization of the native split-Albert Leibniz residual.

The raw residual is function-valued, so finite samples cannot identify it on
the whole function space. The residual is bilinear in its two Jordan inputs;
this module packages it in the finite-dimensional curried bilinear-map carrier
and proves that its basis-coordinate tensor has the same range finrank.
-/

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfoGeometry.Canonical.F4ResidualCoordinateRankBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.F4LeibnizResidualBridge
open InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge
open InfoGeometry.Canonical.F4ResidualUpperBoundTransfer

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3
abbrev Residual := H3 → H3 → H3
abbrev BilinearResidual := H3 →ₗ[ℝ] H3 →ₗ[ℝ] H3
abbrev TensorCoordinates := Fin 27 → Fin 27 → Fin 27 → ℝ

local instance : FiniteDimensional ℝ H3 :=
  h3ZornCoordinateBasis.finiteDimensional_of_finite

/-- The native Leibniz defect, bundled as a bilinear map using the additive
and homogeneous laws of the installed Jordan product. -/
def residualBilinear (D : EndH3) : BilinearResidual :=
  LinearMap.mk₂ ℝ (InfoGeometry.Canonical.F4LeibnizResidualBridge.residual D)
    (by
      intro X₁ X₂ Y
      simp [InfoGeometry.Canonical.F4LeibnizResidualBridge.residual,
        ← candidateJordanMul_eq_mul, map_add, candidateJordanMul_add_left]
      abel)
    (by
      intro r X Y
      simp [InfoGeometry.Canonical.F4LeibnizResidualBridge.residual,
        ← candidateJordanMul_eq_mul, map_smul, candidateJordanMul_smul_left]
      module)
    (by
      intro X Y₁ Y₂
      simp [InfoGeometry.Canonical.F4LeibnizResidualBridge.residual,
        ← candidateJordanMul_eq_mul, candidateJordanMul_add_right]
      abel)
    (by
      intro r X Y
      simp [InfoGeometry.Canonical.F4LeibnizResidualBridge.residual,
        ← candidateJordanMul_eq_mul, candidateJordanMul_smul_right]
      module)

@[simp] theorem residualBilinear_apply (D : EndH3) (X Y : H3) :
    residualBilinear D X Y =
      InfoGeometry.Canonical.F4LeibnizResidualBridge.residual D X Y := rfl

/-- The native pointwise residual, repackaged into the curried bilinear-map
carrier. -/
def residualBilinearLinear : EndH3 →ₗ[ℝ] BilinearResidual where
  toFun := residualBilinear
  map_add' D E := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    have h := congrFun (congrFun (LinearMap.map_add residualLinear D E) X) Y
    exact h
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    have h := congrFun (congrFun (LinearMap.map_smul residualLinear r D) X) Y
    exact h

/-- Coordinate flattening on the finite-dimensional bilinear-map carrier. -/
def bilinearCoordinateReadout (B : BilinearResidual) : TensorCoordinates :=
  fun i j k =>
    (h3ZornCoordinateBasis.repr
      (B (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j))) k

def bilinearCoordinateReadoutLinear :
    BilinearResidual →ₗ[ℝ] TensorCoordinates where
  toFun := bilinearCoordinateReadout
  map_add' B C := by
    funext i j k
    simp [bilinearCoordinateReadout]
  map_smul' r B := by
    funext i j k
    simp [bilinearCoordinateReadout]

/-- Linear map given by the repository's finite residual coordinate readout. -/
def residualReadoutLinear : EndH3 →ₗ[ℝ] TensorCoordinates :=
  bilinearCoordinateReadoutLinear.comp residualBilinearLinear

/-- The basis-coordinate readout is injective on bilinear maps. The finite
27³ readout is only claimed on this carrier, not on arbitrary functions. -/
theorem bilinearCoordinateReadoutLinear_injective :
    Function.Injective bilinearCoordinateReadoutLinear := by
  intro B C h
  apply LinearMap.ext
  intro X
  apply LinearMap.ext
  intro Y
  have hBasis : ∀ i j : Fin 27,
      B (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j) =
        C (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j) := by
    intro i j
    apply h3ZornCoordinateBasis.repr.injective
    ext k
    have hk := congrFun (congrFun (congrFun h i) j) k
    exact hk
  have hAt (x : H3) (j : Fin 27) :
      B x (h3ZornCoordinateBasis j) = C x (h3ZornCoordinateBasis j) := by
    rw [← h3ZornCoordinateBasis.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hBasis i j]
  rw [← h3ZornCoordinateBasis.sum_repr Y]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hAt X j]

/-- Repackaging the residual does not change its kernel. -/
theorem residualBilinearLinear_ker_eq_residualLinear_ker :
    LinearMap.ker residualBilinearLinear = LinearMap.ker residualLinear := by
  ext D
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    change residualBilinear D = 0 at h
    funext X Y
    have h' : residualBilinear D X Y = 0 := by
      simpa using congrArg (fun F : BilinearResidual => F X Y) h
    change residualLinear D X Y = 0 at h'
    exact h'
  · intro h
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    have h' : residualLinear D X Y = 0 := by
      simpa using congrArg (fun F : Residual => F X Y) h
    change residualLinear D X Y = 0
    exact h'

/-- Equal kernels over a finite-dimensional common domain give equal range
finranks. -/
theorem finrank_range_eq_of_equal_kernels
    {U V W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ U]
    (L : U →ₗ[ℝ] V) (M : U →ₗ[ℝ] W)
    (hker : LinearMap.ker L = LinearMap.ker M) :
    Module.finrank ℝ (LinearMap.range L) =
      Module.finrank ℝ (LinearMap.range M) := by
  have hL := LinearMap.finrank_range_add_finrank_ker L
  have hM := LinearMap.finrank_range_add_finrank_ker M
  rw [hker] at hL
  omega

/-- An injective finite coordinate readout preserves the range finrank of any
linear map into its domain. -/
theorem finrank_range_eq_of_injective_readout
    {U V W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ U]
    (L : U →ₗ[ℝ] V) (R : V →ₗ[ℝ] W)
    (hR : Function.Injective R) :
    Module.finrank ℝ (LinearMap.range L) =
      Module.finrank ℝ (LinearMap.range (R.comp L)) := by
  have hker : LinearMap.ker L = LinearMap.ker (R.comp L) := by
    ext x
    change (L x = 0) ↔ R (L x) = 0
    constructor
    · intro hx
      simp [hx]
    · intro hx
      apply hR
      simpa using hx
  exact finrank_range_eq_of_equal_kernels L (R.comp L) hker

/-- The kernel of the finite residual tensor readout is the native derivation
subspace. This connects the existing basis-sampled residual coordinates to the
pointwise Leibniz definition. The second component identifies this linear map
with the repository's established `residualReadout`. -/
theorem residualReadoutLinear_ker_eq_derivations :
    LinearMap.ker residualReadoutLinear = H3ZornF4Derivations.toSubmodule ∧
      ∀ D : EndH3,
        residualReadoutLinear D =
          F4LeibnizConstraintSpaceBridge.residualReadout D := by
  constructor
  · have hkerReadout :
        LinearMap.ker residualReadoutLinear =
          LinearMap.ker residualBilinearLinear := by
      have h := bilinearCoordinateReadoutLinear_injective
      change LinearMap.ker (bilinearCoordinateReadoutLinear.comp
        residualBilinearLinear) = LinearMap.ker residualBilinearLinear
      ext D
      change (bilinearCoordinateReadoutLinear (residualBilinearLinear D) = 0) ↔
        residualBilinearLinear D = 0
      constructor
      · intro hz
        apply h
        simpa using hz
      · intro hz
        simp [hz]
    calc
      LinearMap.ker residualReadoutLinear =
          LinearMap.ker residualBilinearLinear := hkerReadout
      _ = LinearMap.ker residualLinear :=
        residualBilinearLinear_ker_eq_residualLinear_ker
      _ = H3ZornF4Derivations.toSubmodule :=
        residualLinear_ker_eq_derivations
  · intro D
    rfl

/-- The native pointwise residual and its finite tensor readout have equal
range finrank. This provides an exact finite target for the outstanding rank
lower-bound certificate. -/
theorem residual_rank_eq_tensor_readout_rank :
    Module.finrank ℝ (LinearMap.range residualLinear) =
      Module.finrank ℝ (LinearMap.range residualReadoutLinear) := by
  calc
    Module.finrank ℝ (LinearMap.range residualLinear) =
        Module.finrank ℝ (LinearMap.range residualBilinearLinear) :=
      finrank_range_eq_of_equal_kernels residualLinear residualBilinearLinear
        residualBilinearLinear_ker_eq_residualLinear_ker.symm
    _ = Module.finrank ℝ
        (LinearMap.range
          residualReadoutLinear) :=
      finrank_range_eq_of_injective_readout residualBilinearLinear
        bilinearCoordinateReadoutLinear bilinearCoordinateReadoutLinear_injective

end InfoGeometry.Canonical.F4ResidualCoordinateRankBridge
