import Mathlib.Algebra.Lie.CartanSubalgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.RootSystem
import InfoGeometry.Lie.CanonicalZornCartanRootSystem
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Weights.Basic

/-!
# Honest Mathlib bridge for the canonical Zorn Cartan

Only kernel-checked native identifications are exposed here.  The Killing
form and the resulting `RootPairing` remain separate proof obligations.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornMathlibBridge

open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Der := CanonicalZornCartanRootSystem.Der
abbrev Cartan := axialCartanLieSubalgebra

theorem axialCartan_isCartanSubalgebra :
    LieSubalgebra.IsCartanSubalgebra
      (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) := by
  infer_instance

theorem rootDerivation_mem_mathlib_rootSpace (i : nonzeroIndex) :
    rootDerivation i.1 ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra (nativeRootWeight i) := by
  exact CanonicalZornCartanRootSystem.rootDerivation_mem_rootSpace i

theorem cartan_bracket_rootDerivation
    (H : axialCartanLieSubalgebra) (i : nonzeroIndex) :
    ⁅(H : Der), rootDerivation i.1⁆ =
      (nativeRootWeight i H) • rootDerivation i.1 := by
  change ⁅(H : Der), rootDerivation i.1⁆ =
    (rootWeight i.1 (axialCartanLieEquiv.symm H)) • rootDerivation i.1
  rw [← adCartan_rootDerivation (axialCartanLieEquiv.symm H) i.1]
  rw [adCartan_apply, axialCartanLieEquiv.apply_symm_apply]
  rfl

theorem nativeCartan_le_mathlib_rootSpace_zero :
    axialCartanLieSubalgebra.toLieSubmodule ≤
      LieAlgebra.rootSpace axialCartanLieSubalgebra 0 := by
  exact CanonicalZornCartanRootSystem.nativeCartan_le_mathlib_rootSpace_zero

theorem mathlib_rootSpace_zero_eq_nativeCartan :
    LieAlgebra.rootSpace axialCartanLieSubalgebra 0 =
      axialCartanLieSubalgebra.toLieSubmodule := by
  exact CanonicalZornCartanRootSystem.mathlib_rootSpace_zero_eq_nativeCartan

theorem mathlib_zeroRootSubalgebra_eq_nativeCartan :
    LieAlgebra.zeroRootSubalgebra ℝ Der axialCartanLieSubalgebra =
      axialCartanLieSubalgebra := by
  exact (LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan
    ℝ Der axialCartanLieSubalgebra).mpr axialCartan_isCartanSubalgebra

theorem cartanIsTriangularizable :
    LieModule.IsTriangularizable ℝ axialCartanLieSubalgebra Der := by
  exact CanonicalZornCartanRootSystem.axialCartan_isTriangularizable

theorem mathlib_rootSpace_iSup_eq_top :
    (⨆ χ : axialCartanLieSubalgebra → ℝ,
      LieAlgebra.rootSpace axialCartanLieSubalgebra χ) = ⊤ := by
  simpa only [LieAlgebra.rootSpace] using
    (LieModule.iSup_genWeightSpace_eq_top
      ℝ axialCartanLieSubalgebra Der)

theorem mathlib_rootSpace_iSupIndep :
    iSupIndep (fun χ : axialCartanLieSubalgebra → ℝ =>
      LieAlgebra.rootSpace axialCartanLieSubalgebra χ) := by
  simpa only [LieAlgebra.rootSpace] using
    (LieModule.iSupIndep_genWeightSpace
      ℝ axialCartanLieSubalgebra Der)

/-- A generalized Mathlib root space whose character is absent from the
concrete simultaneous spectrum is trivial.  This is the coordinate-free
exhaustion direction needed before classifying arbitrary Mathlib weights by
the native `rootWeight` family. -/
theorem mathlib_rootSpace_eq_bot_of_not_native_rootWeight
    (χ : axialCartanLieSubalgebra → ℝ)
    (hχ : ∀ j : Fin 14,
      (fun x : axialCartanLieSubalgebra =>
        rootWeight j (axialCartanLieEquiv.symm x)) ≠ χ) :
    LieAlgebra.rootSpace axialCartanLieSubalgebra χ = ⊥ := by
  apply le_antisymm
  · intro D hD
    rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace] at hD
    let p : Params := canonicalParameterLinearEquiv.symm D
    have hpzero : p = 0 := by
      funext j
      have hnot : ¬ ∀ k : axialCartanLieSubalgebra,
          rootWeight j (axialCartanLieEquiv.symm k) = χ k := by
        intro hall
        apply hχ j
        funext k
        exact hall k
      obtain ⟨k, hk⟩ : ∃ k : axialCartanLieSubalgebra,
          rootWeight j (axialCartanLieEquiv.symm k) ≠ χ k :=
        not_forall.mp hnot
      obtain ⟨n, hn⟩ := hD (k : axialCartanLieSubalgebra)
      let A : Module.End ℝ Der :=
        (LieModule.toEnd ℝ axialCartanLieSubalgebra Der) k - χ k • 1
      let T : Module.End ℝ Params :=
        adCartanCoordinates (axialCartanLieEquiv.symm k) - χ k • 1
      have hT (q : Params) :
          T q j =
            (rootWeight j (axialCartanLieEquiv.symm k) - χ k) * q j := by
        change adCartanCoordinates (axialCartanLieEquiv.symm k) q j -
          χ k * q j = _
        rw [adCartanCoordinates_apply_diagonal]
        rw [← rootWeight_eq_adCartanDiagonalCoefficient]
        ring
      have hpow (m : ℕ) (q : Params) :
          (T ^ m) q j =
            (rootWeight j (axialCartanLieEquiv.symm k) - χ k)^m * q j := by
        induction m generalizing q with
        | zero => simp
        | succ m ih =>
          rw [pow_succ, Module.End.mul_apply]
          calc
            (T ^ m) (T q) j =
                (rootWeight j (axialCartanLieEquiv.symm k) - χ k)^m * (T q) j :=
              ih (T q)
            _ = (rootWeight j (axialCartanLieEquiv.symm k) - χ k)^m *
                ((rootWeight j (axialCartanLieEquiv.symm k) - χ k) * q j) := by
              rw [hT]
            _ = (rootWeight j (axialCartanLieEquiv.symm k) - χ k)^(m + 1) * q j := by
              ring
      have htransport (X : Der) :
          canonicalParameterLinearEquiv.symm (A X) =
            T (canonicalParameterLinearEquiv.symm X) := by
        change canonicalParameterLinearEquiv.symm
            ((((LieModule.toEnd ℝ axialCartanLieSubalgebra Der) k) X) -
              χ k • (1 : Module.End ℝ Der) X) =
          T (canonicalParameterLinearEquiv.symm X)
        simp only [Module.End.one_apply]
        rw [show ((LieModule.toEnd ℝ axialCartanLieSubalgebra Der) k) X =
            ⁅(k : Der), X⁆ by rfl]
        rw [map_sub, map_smul]
        rw [show canonicalParameterLinearEquiv.symm (⁅(k : Der), X⁆) =
            adCartanCoordinates (axialCartanLieEquiv.symm k)
              (canonicalParameterLinearEquiv.symm X) by
              simp [adCartanCoordinates_apply, adCartan_apply]]
        rfl
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
        (pow_ne_zero n (sub_ne_zero.mpr hk))
    have hDzero : D = 0 := by
      apply canonicalParameterLinearEquiv.symm.injective
      change p = canonicalParameterLinearEquiv.symm 0
      rw [hpzero, map_zero]
    rw [hDzero]
    exact Submodule.zero_mem _
  · exact bot_le

theorem mathlib_rootSpace_nontrivial_implies_native_rootWeight
    (χ : axialCartanLieSubalgebra → ℝ)
    (hχ : LieAlgebra.rootSpace axialCartanLieSubalgebra χ ≠ ⊥) :
    ∃ j : Fin 14,
      (fun x : axialCartanLieSubalgebra =>
        rootWeight j (axialCartanLieEquiv.symm x)) = χ := by
  by_contra h
  push_neg at h
  apply hχ
  exact mathlib_rootSpace_eq_bot_of_not_native_rootWeight χ h

theorem mathlib_nonzero_weight_eq_nativeRootWeight
    (α : LieModule.Weight ℝ axialCartanLieSubalgebra Der)
    (hα : α.IsNonZero) :
    ∃ i : nonzeroIndex,
      (nativeRootWeight i : axialCartanLieSubalgebra → ℝ) = α := by
  have hα' : (α : axialCartanLieSubalgebra → ℝ) ≠ 0 := hα
  obtain ⟨j, hj⟩ :=
    mathlib_rootSpace_nontrivial_implies_native_rootWeight
      (α : axialCartanLieSubalgebra → ℝ) α.genWeightSpace_ne_bot
  have hj6 : j ≠ 6 := by
    intro h6
    subst j
    apply hα'
    funext H
    have h := congrFun hj H
    simpa [rootWeight] using h.symm
  have hj13 : j ≠ 13 := by
    intro h13
    subst j
    apply hα'
    funext H
    have h := congrFun hj H
    simpa [rootWeight] using h.symm
  refine ⟨⟨j, hj6, hj13⟩, ?_⟩
  simpa [nativeRootWeight] using hj

/-! The native label supplied by root exhaustion is unique.  This is the
comparison theorem needed when an abstract Mathlib root is transported back
to the explicit Zorn index set. -/
theorem mathlib_nonzero_weight_nativeRootWeight_unique
    {α : LieModule.Weight ℝ axialCartanLieSubalgebra Der}
    {i j : nonzeroIndex}
    (hi : (nativeRootWeight i : axialCartanLieSubalgebra → ℝ) = α)
    (hj : (nativeRootWeight j : axialCartanLieSubalgebra → ℝ) = α) :
    i = j := by
  by_contra hne
  apply rootWeight_injective_on_nonzero i j hne
  apply LinearMap.ext
  intro k
  have h := congrFun (hi.trans hj.symm)
    (axialCartanLieEquiv k)
  simpa [nativeRootWeight] using h

theorem lie_bracket_mem_mathlib_rootSpace_add
    {χ ψ : axialCartanLieSubalgebra → ℝ} {X Y : Der}
    (hX : X ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra χ)
    (hY : Y ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra ψ) :
    ⁅X, Y⁆ ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra (χ + ψ) := by
  exact LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hX hY

theorem rootDerivation_bracket_mem_mathlib_rootSpace_add
    (i j : nonzeroIndex) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra
        (nativeRootWeight i + nativeRootWeight j) := by
  exact lie_bracket_mem_mathlib_rootSpace_add
    (rootDerivation_mem_mathlib_rootSpace i)
    (rootDerivation_mem_mathlib_rootSpace j)

theorem lie_bracket_eq_zero_of_sum_not_nativeRootWeight
    {χ ψ : axialCartanLieSubalgebra → ℝ} {X Y : Der}
    (hX : X ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra χ)
    (hY : Y ∈ LieAlgebra.rootSpace axialCartanLieSubalgebra ψ)
    (hχψ : ∀ k : Fin 14,
      (fun x : axialCartanLieSubalgebra =>
        rootWeight k (axialCartanLieEquiv.symm x)) ≠ χ + ψ) :
    ⁅X, Y⁆ = 0 := by
  have hbot :
      LieAlgebra.rootSpace axialCartanLieSubalgebra (χ + ψ) = ⊥ :=
    mathlib_rootSpace_eq_bot_of_not_native_rootWeight (χ + ψ) hχψ
  have hmem := lie_bracket_mem_mathlib_rootSpace_add hX hY
  rw [hbot] at hmem
  simpa using hmem

theorem rootDerivation_bracket_eq_zero_of_sum_not_nativeRootWeight
    (i j : nonzeroIndex)
    (hχ : ∀ k : Fin 14,
      (fun x : axialCartanLieSubalgebra =>
        rootWeight k (axialCartanLieEquiv.symm x)) ≠
          (nativeRootWeight i + nativeRootWeight j)) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ = 0 := by
  exact lie_bracket_eq_zero_of_sum_not_nativeRootWeight
    (rootDerivation_mem_mathlib_rootSpace i)
    (rootDerivation_mem_mathlib_rootSpace j) hχ

theorem rootDerivation_bracket_mem_nativeCartan_of_opposite
    (i j : nonzeroIndex)
    (hij : nativeRootWeight i + nativeRootWeight j = 0) :
    ⁅rootDerivation i.1, rootDerivation j.1⁆ ∈
      axialCartanLieSubalgebra.toLieSubmodule := by
  rw [← mathlib_rootSpace_zero_eq_nativeCartan]
  rw [← hij]
  exact rootDerivation_bracket_mem_mathlib_rootSpace_add i j

end InfoGeometry.Lie.CanonicalZornMathlibBridge
