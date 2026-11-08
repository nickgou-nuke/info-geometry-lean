import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# The two native descriptions of the Cartan parameter plane

The Cartan plane is generated either by the two coordinate directions or by
the two pair readback directions used by the real Weyl generators.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2CartanParameterSpan

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation

abbrev Params := InfoGeometry.Lie.CanonicalZornDerivationDimension.Params

def cartanParameterPlane : Submodule ℝ Params :=
  Submodule.span ℝ ({parameterUnit 6, parameterUnit 13} : Set Params)

def cartanPairParameterSpan : Submodule ℝ Params :=
  Submodule.span ℝ ({parameterUnit 6 + parameterUnit 13,
    (-2 : ℝ) • parameterUnit 6 + parameterUnit 13} : Set Params)

theorem cartanPairParameterSpan_le_cartanParameterPlane :
    cartanPairParameterSpan ≤ cartanParameterPlane := by
  apply Submodule.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.subset_span (by simp))

theorem cartanParameterPlane_le_cartanPairParameterSpan :
    cartanParameterPlane ≤ cartanPairParameterSpan := by
  apply Submodule.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · let p₀ := parameterUnit 6 + parameterUnit 13
    let p₁ := (-2 : ℝ) • parameterUnit 6 + parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan :=
      Submodule.subset_span (by simp [p₀])
    have hp₁ : p₁ ∈ cartanPairParameterSpan :=
      Submodule.subset_span (by simp [p₁])
    have h : parameterUnit 6 = (1 / 3 : ℝ) • (p₀ - p₁) := by
      funext i
      fin_cases i <;> simp [p₀, p₁, parameterUnit] <;> norm_num
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hp₀ hp₁)
  · let p₀ := parameterUnit 6 + parameterUnit 13
    let p₁ := (-2 : ℝ) • parameterUnit 6 + parameterUnit 13
    have hp₀ : p₀ ∈ cartanPairParameterSpan :=
      Submodule.subset_span (by simp [p₀])
    have hp₁ : p₁ ∈ cartanPairParameterSpan :=
      Submodule.subset_span (by simp [p₁])
    have h : parameterUnit 13 = (1 / 3 : ℝ) • ((2 : ℝ) • p₀ + p₁) := by
      funext i
      fin_cases i <;> simp [p₀, p₁, parameterUnit] <;> norm_num
    rw [h]
    exact Submodule.smul_mem _ (1 / 3 : ℝ)
      (Submodule.add_mem _ (Submodule.smul_mem _ (2 : ℝ) hp₀) hp₁)

theorem cartanPairParameterSpan_eq_cartanParameterPlane :
    cartanPairParameterSpan = cartanParameterPlane := by
  exact le_antisymm cartanPairParameterSpan_le_cartanParameterPlane
    cartanParameterPlane_le_cartanPairParameterSpan

theorem map_cartanParameterPlane_le_of_pair_generators
    (L : Params →ₗ[ℝ] Params)
    (h₀ : L (parameterUnit 6 + parameterUnit 13) ∈ cartanParameterPlane)
    (h₁ : L ((-2 : ℝ) • parameterUnit 6 + parameterUnit 13) ∈
      cartanParameterPlane) :
    cartanParameterPlane.map L ≤ cartanParameterPlane := by
  rintro _ ⟨p, hp, rfl⟩
  rw [← cartanPairParameterSpan_eq_cartanParameterPlane] at hp
  refine Submodule.span_induction (p := fun q _ => L q ∈ cartanParameterPlane)
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact h₀
    · exact h₁
  · simpa using cartanParameterPlane.zero_mem
  · intro p q _ _ hp hq
    simpa using cartanParameterPlane.add_mem hp hq
  · intro a p _ hp
    simpa using cartanParameterPlane.smul_mem a hp

theorem map_eq_self_of_linearEquiv_map_le
    (T : Params ≃ₗ[ℝ] Params)
    (hT : cartanParameterPlane.map T.toLinearMap ≤ cartanParameterPlane) :
    cartanParameterPlane.map T.toLinearMap = cartanParameterPlane := by
  apply Submodule.eq_of_le_of_finrank_eq hT
  exact T.finrank_map_eq cartanParameterPlane

theorem conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_pair_generators
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut)
    (h₀ : conjugatedParameterLieEquiv φ
      (parameterUnit 6 + parameterUnit 13) ∈ cartanParameterPlane)
    (h₁ : conjugatedParameterLieEquiv φ
      ((-2 : ℝ) • parameterUnit 6 + parameterUnit 13) ∈
      cartanParameterPlane) :
    cartanParameterPlane.map (conjugatedParameterLieEquiv φ).toLinearMap =
      cartanParameterPlane := by
  apply map_eq_self_of_linearEquiv_map_le
  exact map_cartanParameterPlane_le_of_pair_generators
    (conjugatedParameterLieEquiv φ).toLinearMap h₀ h₁

theorem symm_mem_cartanParameterPlane_of_map_eq
    (T : Params ≃ₗ[ℝ] Params)
    (hT : cartanParameterPlane.map T.toLinearMap = cartanParameterPlane)
    {p : Params} (hp : p ∈ cartanParameterPlane) :
    T.symm p ∈ cartanParameterPlane := by
  have hp' : p ∈ cartanParameterPlane.map T.toLinearMap := by
    rw [hT]
    exact hp
  rcases hp' with ⟨q, hq, hqp⟩
  have hqeq : T q = p := hqp
  rw [← hqeq]
  simpa using hq

end InfoGeometry.Algebra.Zorn.G2CartanParameterSpan
