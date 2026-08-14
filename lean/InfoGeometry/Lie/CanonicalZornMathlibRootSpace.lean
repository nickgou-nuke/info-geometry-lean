import InfoGeometry.Lie.CanonicalZornMathlibBridge

/-!
# One-dimensional Mathlib root spaces for the canonical Zorn Cartan

The simultaneous coordinate calculation is used here only to identify the
generalized Mathlib root space with the corresponding native one-dimensional
space.  No Killing-form or root-system hypothesis is used.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornMathlibRootSpace

open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Der := CanonicalZornCartanRootSystem.Der

theorem mathlib_rootSpace_eq_span_rootDerivation (i : nonzeroIndex) :
    LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i) =
      ℝ ∙ rootDerivation i.1 := by
  apply le_antisymm
  · intro D hD
    change D ∈ LieModule.genWeightSpace Der (nativeRootWeight i) at hD
    rw [LieModule.mem_genWeightSpace] at hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hzero (j : Fin 14) (hij : j ≠ i.1) : p j = 0 := by
      obtain ⟨k, hk⟩ := adCartanWeight_separates_nonzero_indices
        j i.1 hij i.2.1 i.2.2
      have hk' : rootWeight j k ≠ rootWeight i.1 k := by
        rw [rootWeight_eq_adCartanDiagonalCoefficient]
        exact hk
      obtain ⟨n, hn⟩ := hD (axialCartanLieEquiv k)
      let A : Module.End ℝ Der :=
        (LieModule.toEnd ℝ axialCartanLieSubalgebra Der)
          (axialCartanLieEquiv k) -
          nativeRootWeight i (axialCartanLieEquiv k) • 1
      let T : Module.End ℝ Params :=
        adCartanCoordinates k -
          rootWeight i.1 k • 1
      have hT (q : Params) :
          T q j =
            (rootWeight j k - rootWeight i.1 k) * q j := by
        change adCartanCoordinates k q j - rootWeight i.1 k * q j = _
        rw [adCartanCoordinates_apply_diagonal]
        rw [← rootWeight_eq_adCartanDiagonalCoefficient]
        ring
      have hpow (m : ℕ) (q : Params) :
          (T ^ m) q j =
            (rootWeight j k - rootWeight i.1 k)^m * q j := by
        induction m generalizing q with
        | zero => simp
        | succ m ih =>
            rw [pow_succ, Module.End.mul_apply]
            calc
              (T ^ m) (T q) j =
                  (rootWeight j k - rootWeight i.1 k)^m * (T q) j :=
                ih (T q)
              _ = (rootWeight j k - rootWeight i.1 k)^m *
                  ((rootWeight j k - rootWeight i.1 k) * q j) := by
                rw [hT]
              _ = (rootWeight j k - rootWeight i.1 k)^(m + 1) * q j := by
                ring
      have htransport (X : Der) :
          canonicalParameterLinearEquiv.symm (A X) =
            T (canonicalParameterLinearEquiv.symm X) := by
        change canonicalParameterLinearEquiv.symm
            ((((LieModule.toEnd ℝ axialCartanLieSubalgebra Der)
              (axialCartanLieEquiv k)) X) -
              nativeRootWeight i (axialCartanLieEquiv k) • X) = _
        rw [map_sub, map_smul]
        rw [show ((LieModule.toEnd ℝ axialCartanLieSubalgebra Der)
            (axialCartanLieEquiv k)) X = ⁅(axialCartanLieEquiv k : Der), X⁆
            by rfl]
        rw [show canonicalParameterLinearEquiv.symm
            (⁅(axialCartanLieEquiv k : Der), X⁆) =
            adCartanCoordinates k (canonicalParameterLinearEquiv.symm X) by
              simp [adCartanCoordinates_apply, adCartan_apply]]
        simp [T, nativeRootWeight]
      have htransport_pow (m : ℕ) (X : Der) :
          canonicalParameterLinearEquiv.symm ((A ^ m) X) =
            (T ^ m) (canonicalParameterLinearEquiv.symm X) := by
        induction m generalizing X with
        | zero => simp
        | succ m ih =>
            rw [pow_succ, Module.End.mul_apply]
            calc
              canonicalParameterLinearEquiv.symm ((A ^ m) (A X)) =
                  (T ^ m) (canonicalParameterLinearEquiv.symm (A X)) :=
                ih (A X)
              _ = (T ^ m) (T (canonicalParameterLinearEquiv.symm X)) := by
                rw [htransport]
              _ = (T ^ (m + 1)) (canonicalParameterLinearEquiv.symm X) := by
                rw [pow_succ, Module.End.mul_apply]
      change (A ^ n) D = 0 at hn
      have hzero0 := (congrArg
        (fun q : Params => q j) (htransport_pow n D)).symm
      rw [hn, map_zero] at hzero0
      rw [hpow] at hzero0
      exact (mul_eq_zero.mp hzero0).resolve_left
        (pow_ne_zero n (sub_ne_zero.mpr hk'))
    have hpform : p = p i.1 • parameterUnit i.1 := by
      funext j
      by_cases hji : j = i.1
      · subst j
        simp [parameterUnit]
      · simp [hzero j hji, parameterUnit, hji]
    have hDform : D = ((p i.1 : ℝ) • rootDerivation i.1 : Der) := by
      apply (canonicalParameterLinearEquiv.symm).injective
      change p = canonicalParameterLinearEquiv.symm
        ((p i.1 : ℝ) • rootDerivation i.1 : Der)
      rw [map_smul]
      simpa only [rootDerivation, LinearEquiv.symm_apply_apply] using hpform
    rw [hDform]
    exact Submodule.mem_span_singleton.mpr ⟨p i.1, rfl⟩
  · intro D hD
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hD
    exact Submodule.smul_mem _ c
      (rootDerivation_mem_mathlib_rootSpace i)

end InfoGeometry.Lie.CanonicalZornMathlibRootSpace
