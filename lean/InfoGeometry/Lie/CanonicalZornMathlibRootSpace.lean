import InfoGeometry.Lie.CanonicalZornMathlibBridge
import InfoGeometry.Lie.LieEquivEigenvectorTransport

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

@[reducible] def Der := CanonicalZornCartanRootSystem.Der

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

theorem mem_mathlib_rootSpace_iff_exists_scalar
    (i : nonzeroIndex) (D : Der) :
    D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i) ↔
      ∃ c : ℝ, D = c • rootDerivation i.1 := by
  have hspan := mathlib_rootSpace_eq_span_rootDerivation i
  constructor
  · intro hD
    have hD' : D ∈ ℝ ∙ rootDerivation i.1 := hspan ▸ hD
    rcases Submodule.mem_span_singleton.mp hD' with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    have hD' : c • rootDerivation i.1 ∈ ℝ ∙ rootDerivation i.1 :=
      Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    have hm := congrArg
      (fun S : Submodule ℝ Der => c • rootDerivation i.1 ∈ S) hspan.symm
    exact Eq.mp hm hD'

theorem mem_mathlib_rootSpace_iff_existsUnique_scalar
    (i : nonzeroIndex) (D : Der) :
    D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i) ↔
      ∃! c : ℝ, D = c • rootDerivation i.1 := by
  constructor
  · intro hD
    obtain ⟨c, hc⟩ :=
      (mem_mathlib_rootSpace_iff_exists_scalar i D).mp hD
    refine ⟨c, hc, ?_⟩
    intro d hd
    have hzero : (c - d) • rootDerivation i.1 = 0 := by
      calc
        (c - d) • rootDerivation i.1 =
            c • rootDerivation i.1 - d • rootDerivation i.1 := sub_smul _ _ _
        _ = D - D := by rw [← hc, ← hd]
        _ = 0 := sub_self D
    rcases smul_eq_zero.mp hzero with hcd | hroot
    · exact (sub_eq_zero.mp hcd).symm
    · exact False.elim (rootDerivation_ne_zero i.1 hroot)
  · rintro ⟨c, hc, -⟩
    exact (mem_mathlib_rootSpace_iff_exists_scalar i D).mpr ⟨c, hc⟩

/-- The coefficient of a derivation in the canonical generator of a
one-dimensional nonzero root space.  The parameter equivalence makes this
readback independent of a choice of witness scalar. -/
noncomputable def rootCoefficient (i : nonzeroIndex) (D : Der) : ℝ :=
  canonicalParameterLinearEquiv.symm D i.1

@[simp]
theorem rootCoefficient_rootDerivation (i : nonzeroIndex) :
    rootCoefficient i (rootDerivation i.1) = 1 := by
  change (canonicalParameterLinearEquiv.symm
    (canonicalParameterLinearEquiv (parameterUnit i.1))) i.1 = 1
  rw [LinearEquiv.symm_apply_apply]
  simp [parameterUnit]

/-- A derivation in a nonzero root space is reconstructed from its canonical
parameter coefficient. -/
theorem eq_rootCoefficient_smul_of_mem_rootSpace
    (i : nonzeroIndex) (D : Der)
    (hD : D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i)) :
    D = rootCoefficient i D • rootDerivation i.1 := by
  obtain ⟨c, hc, huniq⟩ :=
    (mem_mathlib_rootSpace_iff_existsUnique_scalar i D).mp hD
  have hcoeff : rootCoefficient i D = c := by
    rw [hc]
    simp [rootCoefficient, rootDerivation, parameterUnit]
  rw [hcoeff]
  exact hc

theorem rootCoefficient_ne_zero_of_ne_zero_of_mem_rootSpace
    (i : nonzeroIndex) (D : Der)
    (hD : D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i))
    (hD0 : D ≠ 0) :
    rootCoefficient i D ≠ 0 := by
  intro hc
  have hform := eq_rootCoefficient_smul_of_mem_rootSpace i D hD
  rw [hc, zero_smul] at hform
  exact hD0 hform

theorem rootCoefficient_eq_iff_of_mem_rootSpace
    (i : nonzeroIndex) (D : Der)
    (hD : D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i)) (c : ℝ) :
    D = c • rootDerivation i.1 ↔ rootCoefficient i D = c := by
  constructor
  · intro h
    rw [h]
    simp [rootCoefficient, rootDerivation, parameterUnit]
  · intro h
    rw [eq_rootCoefficient_smul_of_mem_rootSpace i D hD, h]

theorem mem_mathlib_rootSpace_of_bracket_eq_smul
    (i : nonzeroIndex) (D : Der)
    (hD : ∀ H : axialCartanLieSubalgebra,
      ⁅(H : Der), D⁆ = nativeRootWeight i H • D) :
    D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  simp only [pow_one]
  change ⁅(H : Der), D⁆ - nativeRootWeight i H • D = 0
  rw [hD H]
  exact sub_self _

theorem LinearEquiv.map_rootSpace_mem_of_cartan_normalizer
    (i j : nonzeroIndex) (e : Der ≃ₗ[ℝ] Der)
    (c : axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra)
    (hbracket : ∀ X Y, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (hcartan : ∀ H : axialCartanLieSubalgebra,
      e (H : Der) = ((c H : axialCartanLieSubalgebra) : Der))
    (hweight : ∀ H : axialCartanLieSubalgebra,
      nativeRootWeight i (c.symm H) = nativeRootWeight j H)
    (D : Der)
    (hD : ∀ H : axialCartanLieSubalgebra,
      ⁅(H : Der), D⁆ = nativeRootWeight i H • D) :
    e D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight j) := by
  apply mem_mathlib_rootSpace_of_bracket_eq_smul j (e D)
  intro H
  let K : axialCartanLieSubalgebra := c.symm H
  have hHK : e (K : Der) = (H : Der) := by
    rw [hcartan]
    exact congrArg (fun T : axialCartanLieSubalgebra => (T : Der))
      (c.apply_symm_apply H)
  have heigen := e.map_bracket_eigenvector hbracket D
    (H : Der) (K : Der) (nativeRootWeight i K) hHK (hD K)
  rw [heigen, ← hweight H]

theorem LinearEquiv.map_rootSpace_mem_existsUnique_scalar
    (i : nonzeroIndex) (e : Der ≃ₗ[ℝ] Der) (D : Der)
    (hD : e D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i)) :
    ∃! c : ℝ, e D = c • rootDerivation i.1 := by
  exact (mem_mathlib_rootSpace_iff_existsUnique_scalar i (e D)).mp hD

theorem LinearEquiv.map_rootSpace_mem_rootCoefficient_ne_zero
    (i : nonzeroIndex) (e : Der ≃ₗ[ℝ] Der) (D : Der)
    (hD0 : D ≠ 0)
    (hD : e D ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra
      (nativeRootWeight i)) :
    rootCoefficient i (e D) ≠ 0 := by
  apply rootCoefficient_ne_zero_of_ne_zero_of_mem_rootSpace i (e D) hD
  intro heD
  apply hD0
  apply e.injective
  simpa using heD

end InfoGeometry.Lie.CanonicalZornMathlibRootSpace
