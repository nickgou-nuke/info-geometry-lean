/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension

/-!
# Symplectic Lagrangian sheets for finite-dimensional para-Kähler spaces

The companion dimension module establishes half-dimension and total isotropy for
the neutral metric `g`. This module supplies the corresponding isotropy for the
symplectic form `omega` and proves its nondegeneracy from that of `g`. Thus the
projector ranges are genuinely half-dimensional isotropic subspaces for the
symplectic form, rather than being called Lagrangian based on metric isotropy.
-/

namespace InfoGeometry.Canonical.ParaKahlerSymplecticLagrangian

open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Canonical.ParaKahlerLagrangianDimension

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {K : V →ₗ[ℝ] V}

/-- Nondegeneracy of `g` and para-Kähler compatibility imply nondegeneracy of
the fundamental symplectic form `omega`. -/
theorem omega_nondegenerate (hPK : ParaKahlerStructure g omega K)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    ∀ v, (∀ w, omega v w = 0) → v = 0 := by
  intro v hv
  apply hnd v
  intro w
  have h := hPK.compatibility v w
  rw [hv (K w)] at h
  exact h

/-- The positive projector range is isotropic for the symplectic form. -/
theorem range_plus_omega_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) :
    ∀ v ∈ LinearMap.range (paraProjectorPlus K),
      ∀ w ∈ LinearMap.range (paraProjectorPlus K), omega v w = 0 := by
  intro v hv w hw
  have hv' := inTPlus_of_mem_range hK hv
  have hw' := inTPlus_of_mem_range hK hw
  have hg := tplus_isotropic hK hPK hv' hw'
  have hcompat := hPK.compatibility v w
  rw [hw'] at hcompat
  rw [← hcompat]
  exact hg

/-- The negative projector range is isotropic for the symplectic form. -/
theorem range_minus_omega_isotropic (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K) :
    ∀ v ∈ LinearMap.range (paraProjectorMinus K),
      ∀ w ∈ LinearMap.range (paraProjectorMinus K), omega v w = 0 := by
  intro v hv w hw
  have hv' := inTMinus_of_mem_range hK hv
  have hw' := inTMinus_of_mem_range hK hw
  have hg := tminus_isotropic hK hPK hv' hw'
  have hcompat := hPK.compatibility v w
  rw [hw', map_neg] at hcompat
  rw [hcompat] at hg
  exact neg_eq_zero.mp hg

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- The positive sheet is symplectically isotropic and has half the ambient
dimension. Together with `omega_nondegenerate`, this is the Lagrangian
criterion in finite dimension. -/
theorem range_plus_lagrangian_data (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    (∀ v ∈ LinearMap.range (paraProjectorPlus K),
      ∀ w ∈ LinearMap.range (paraProjectorPlus K), omega v w = 0) ∧
      2 * Module.finrank ℝ (LinearMap.range (paraProjectorPlus K)) =
        Module.finrank ℝ V := by
  exact ⟨range_plus_omega_isotropic hK hPK,
    two_mul_finrank_range_plus hK hPK hnd⟩

/-- The negative sheet is symplectically isotropic and has half the ambient
dimension. Together with `omega_nondegenerate`, this is the Lagrangian
criterion in finite dimension. -/
theorem range_minus_lagrangian_data (hK : ParaComplexStructure K)
    (hPK : ParaKahlerStructure g omega K)
    (hnd : ∀ v, (∀ w, g v w = 0) → v = 0) :
    (∀ v ∈ LinearMap.range (paraProjectorMinus K),
      ∀ w ∈ LinearMap.range (paraProjectorMinus K), omega v w = 0) ∧
      2 * Module.finrank ℝ (LinearMap.range (paraProjectorMinus K)) =
        Module.finrank ℝ V := by
  refine ⟨range_minus_omega_isotropic hK hPK, ?_⟩
  rw [← finrank_range_plus_eq_minus hK hPK hnd]
  exact two_mul_finrank_range_plus hK hPK hnd

end FiniteDimensional

end InfoGeometry.Canonical.ParaKahlerSymplecticLagrangian
