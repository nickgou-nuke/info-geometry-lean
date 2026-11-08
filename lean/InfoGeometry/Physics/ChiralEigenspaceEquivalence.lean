import InfoGeometry.Physics.FiniteChiralSpectralSymmetry
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace InfoGeometry.Physics.ChiralEigenspaceEquivalence

open FiniteChiralSpectralSymmetry

variable {Scalar Space : Type*} [Field Scalar] [AddCommGroup Space] [Module Scalar Space]

theorem map_eigenspace (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    {eigenvalue : Scalar} {vector : Space}
    (hvector : vector ∈ operator.eigenspace eigenvalue) :
    grading vector ∈ operator.eigenspace (-eigenvalue) := by
  rw [Module.End.mem_eigenspace_iff] at hvector ⊢
  exact anticommuting_maps_eigenmode_neg operator grading hanti hvector

theorem map_hasEigenvector (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id)
    {eigenvalue : Scalar} {vector : Space}
    (hvector : operator.HasEigenvector eigenvalue vector) :
    operator.HasEigenvector (-eigenvalue) (grading vector) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hvector ⊢
  exact anticommuting_involution_preserves_nonzero operator grading hanti
    hinvolution hvector.1 hvector.2

theorem shifted_grading_apply (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (eigenvalue : Scalar) (vector : Space) :
    (operator - (-eigenvalue) • 1) (grading vector) =
      -grading ((operator - eigenvalue • 1) vector) := by
  have hpoint := congrArg (fun current : Module.End Scalar Space => current vector) hanti
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hpoint
  simp [hpoint, map_smul, neg_smul, sub_eq_add_neg, add_comm]

theorem shifted_pow_grading_apply (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (eigenvalue : Scalar) (depth : ℕ) (vector : Space) :
    ((operator - (-eigenvalue) • 1) ^ depth) (grading vector) =
      (-1 : Scalar) ^ depth • grading (((operator - eigenvalue • 1) ^ depth) vector) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, map_smul]
    rw [shifted_grading_apply operator grading hanti]
    simp only [mul_smul, neg_one_smul, smul_neg]

/-- Anticommutation transports every generalized eigenspace, including depth `⊤`. -/
theorem map_genEigenspace (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    {eigenvalue : Scalar} {depth : ℕ∞} {vector : Space}
    (hvector : vector ∈ operator.genEigenspace eigenvalue depth) :
    grading vector ∈ operator.genEigenspace (-eigenvalue) depth := by
  rw [Module.End.mem_genEigenspace] at hvector ⊢
  obtain ⟨exponent, hbound, hzero⟩ := hvector
  refine ⟨exponent, hbound, ?_⟩
  rw [LinearMap.mem_ker] at hzero ⊢
  rw [shifted_pow_grading_apply operator grading hanti, hzero, map_zero, smul_zero]

/-- Involutive grading pairs generalized eigenspaces without diagonalizability assumptions. -/
def genEigenspaceEquiv (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id)
    (eigenvalue : Scalar) (depth : ℕ∞) :
    operator.genEigenspace eigenvalue depth ≃ₗ[Scalar]
      operator.genEigenspace (-eigenvalue) depth where
  toFun vector := ⟨grading vector, map_genEigenspace operator grading hanti vector.property⟩
  invFun vector := ⟨grading vector, by
    simpa using map_genEigenspace operator grading hanti vector.property⟩
  left_inv vector := by
    apply Subtype.ext
    exact congrArg (fun linear : Module.End Scalar Space => linear vector) hinvolution
  right_inv vector := by
    apply Subtype.ext
    exact congrArg (fun linear : Module.End Scalar Space => linear vector) hinvolution
  map_add' first second := by
    apply Subtype.ext
    exact grading.map_add first second
  map_smul' scalar vector := by
    apply Subtype.ext
    exact grading.map_smul scalar vector

def eigenspaceEquiv (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id) (eigenvalue : Scalar) :
    operator.eigenspace eigenvalue ≃ₗ[Scalar] operator.eigenspace (-eigenvalue) :=
  genEigenspaceEquiv operator grading hanti hinvolution eigenvalue 1

theorem genEigenspace_finrank_eq (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id)
    (eigenvalue : Scalar) (depth : ℕ∞) :
    Module.finrank Scalar (operator.genEigenspace eigenvalue depth) =
      Module.finrank Scalar (operator.genEigenspace (-eigenvalue) depth) :=
  (genEigenspaceEquiv operator grading hanti hinvolution eigenvalue depth).finrank_eq

/-- Symmetry of the point spectrum, not a claim about arbitrary analytic spectra. -/
theorem hasEigenvalue_iff_neg (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id) (eigenvalue : Scalar) :
    operator.HasEigenvalue eigenvalue ↔ operator.HasEigenvalue (-eigenvalue) := by
  have forward (value : Scalar) (heigen : operator.HasEigenvalue value) :
      operator.HasEigenvalue (-value) := by
    obtain ⟨vector, hvector⟩ := heigen.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (map_hasEigenvector operator grading hanti hinvolution hvector)
  constructor
  · exact forward eigenvalue
  · intro heigen
    simpa only [neg_neg] using forward (-eigenvalue) heigen

theorem eigenspace_finrank_eq (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    (hinvolution : grading.comp grading = LinearMap.id) (eigenvalue : Scalar) :
    Module.finrank Scalar (operator.eigenspace eigenvalue) =
      Module.finrank Scalar (operator.eigenspace (-eigenvalue)) :=
  (eigenspaceEquiv operator grading hanti hinvolution eigenvalue).finrank_eq

theorem zero_mode (operator grading : Module.End Scalar Space)
    (hanti : operator.comp grading = -(grading.comp operator))
    {vector : Space} (hzero : operator vector = 0) :
    operator (grading vector) = 0 := by
  have heigen : IsEigenmode operator 0 vector := by
    simpa [IsEigenmode] using hzero
  simpa [IsEigenmode] using anticommuting_maps_eigenmode_neg operator grading hanti heigen

end InfoGeometry.Physics.ChiralEigenspaceEquivalence
