import Mathlib
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin

/-!
# Signature correlations, observable quotients, and finite compatibility

A signature is a specified linear observation map. Its Gram operator is a
correlation operator, not the physical transition matrix. Finite dimensionality
supplies closed range, so the existing Hilbert-space Moore-Penrose construction
is instantiated, rather than assuming an inverse exists. No covariance model,
chemical separation, or infinite-dimensional Fredholm theorem is asserted.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.SignatureGeometry
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin

section Algebra
variable {A : Type*} [Ring A] [StarRing A]

/-- Self-adjoint MP data supplies a Drazin witness at exponent one. -/
theorem selfAdjoint_mp_drazin {a b : A} (ha : star a = a)
    (h : IsMoorePenroseInverse a b) : IsDrazinInverse a b 1 := by
  have hs : IsMoorePenroseInverse a (star b) := by
    refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
    · simpa [star_mul, ha, mul_assoc] using congrArg star h.aba_eq_a
    · simpa [star_mul, ha, mul_assoc] using congrArg star h.bab_eq_b
    · have hh := h.ba_adj_eq
      simpa [star_mul, ha] using hh.symm
    · have hh := h.ab_adj_eq
      simpa [star_mul, ha] using hh.symm
  have hb : star b = b := (MoorePenrose_unique h hs).symm
  have hab : a*b=b*a := by simpa [star_mul, ha, hb] using h.ab_adj_eq.symm
  refine IsDrazinInverse.mk h.bab_eq_b hab ?_
  simp only [pow_one, pow_two]
  calc
    a = a*b*a := h.aba_eq_a.symm
    _ = a*(b*a) := mul_assoc _ _ _
    _ = a*(a*b) := by rw [← hab]
    _ = a*a*b := (mul_assoc _ _ _).symm

end Algebra

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]

/-- State-side correlation of the specified observation map. -/
def gram (O : E →L[ℝ] F) : E →L[ℝ] E := O.adjoint.comp O

def crossGram (O V : E →L[ℝ] F) : E →L[ℝ] E := O.adjoint.comp V

theorem gram_energy (O : E →L[ℝ] F) (x : E) :
    inner ℝ x (gram O x) = inner ℝ (O x) (O x) :=
  ContinuousLinearMap.adjoint_inner_right O x (O x)

theorem gram_nonnegative (O : E →L[ℝ] F) (x : E) : 0 ≤ inner ℝ x (gram O x) := by
  rw [gram_energy, real_inner_self_eq_norm_sq]
  positivity

theorem gram_selfAdjoint (O : E →L[ℝ] F) : star (gram O) = gram O := by
  change (O.adjoint.comp O).adjoint = O.adjoint.comp O
  simp

theorem crossGram_pairing (O V : E →L[ℝ] F) (x y : E) :
    inner ℝ x (crossGram O V y) = inner ℝ (O x) (V y) :=
  ContinuousLinearMap.adjoint_inner_right O x (V y)

theorem crossGram_adjoint (O V : E →L[ℝ] F) :
    star (crossGram O V) = crossGram V O := by
  change (O.adjoint.comp V).adjoint = V.adjoint.comp O
  simp

theorem gram_kernel (O : E →L[ℝ] F) : (gram O).ker = O.ker :=
  O.ker_adjoint_comp_self

theorem gram_zero_iff (O : E →L[ℝ] F) (x : E) : gram O x = 0 ↔ O x = 0 := by
  change x ∈ (gram O).ker ↔ x ∈ O.ker
  rw [gram_kernel]

theorem same_signature_iff_gram_difference (O : E →L[ℝ] F) (x y : E) :
    O x = O y ↔ gram O (x-y) = 0 := by
  rw [gram_zero_iff, map_sub, sub_eq_zero]

/-- Native quotient by the unobservable submodule, with its actual range. -/
def observableQuotientEquiv (O : E →L[ℝ] F) :
    (E ⧸ O.ker) ≃ₗ[ℝ] O.range := O.toLinearMap.quotKerEquivRange

/-- The finite compatibility alternative, stated using Mathlib's adjoint. -/
theorem finite_fredholm_alternative (O : E →L[ℝ] F) (y : F) :
    (∃ x, O x = y) ↔ y ∈ O.toLinearMap.adjoint.kerᗮ := by
  rw [LinearMap.orthogonal_ker, LinearMap.adjoint_adjoint]
  rfl

/-- Finite index balance; for equal dimensions the two defects have equal dimension. -/
theorem finite_index_balance (O : E →L[ℝ] F) :
    Module.finrank ℝ O.ker + Module.finrank ℝ F =
      Module.finrank ℝ O.toLinearMap.adjoint.ker + Module.finrank ℝ E := by
  have h := O.toLinearMap.finrank_range_add_finrank_ker
  have ha := O.toLinearMap.adjoint.finrank_range_add_finrank_ker
  have hr := O.toLinearMap.finrank_range_adjoint
  omega

/-- Instantiate the pre-existing closed-range MP construction. -/
def inverse (O : E →L[ℝ] F) : F →L[ℝ] E :=
  moorePenroseInverse O O.range.closed_of_finiteDimensional

theorem inverse_laws (O : E →L[ℝ] F) : IsMoorePenroseInverseCLM O (inverse O) :=
  isMoorePenroseInverse_moorePenroseInverse O O.range.closed_of_finiteDimensional

def visible (O : E →L[ℝ] F) : E →L[ℝ] E := (inverse O).comp O

def invisible (O : E →L[ℝ] F) : E →L[ℝ] E := 1-visible O

theorem visible_idempotent (O : E →L[ℝ] F) : visible O * visible O = visible O := by
  ext x
  exact congrArg (fun B : F →L[ℝ] E => B (O x)) (inverse_laws O).2.1

theorem visible_selfAdjoint (O : E →L[ℝ] F) : star (visible O) = visible O :=
  (inverse_laws O).2.2.2

theorem visible_preserves_signature (O : E →L[ℝ] F) (x : E) : O (visible O x) = O x :=
  congrArg (fun A : E →L[ℝ] F => A x) (inverse_laws O).1

theorem visible_zero_iff (O : E →L[ℝ] F) (x : E) : visible O x = 0 ↔ O x = 0 := by
  constructor
  · intro h
    rw [← visible_preserves_signature O x, h, map_zero]
  · intro h
    change inverse O (O x) = 0
    rw [h, map_zero]

theorem invisible_signature_zero (O : E →L[ℝ] F) (x : E) : O (invisible O x) = 0 := by
  change O (x-visible O x)=0
  rw [map_sub, visible_preserves_signature, sub_self]

theorem visible_gram_kernel (O : E →L[ℝ] F) (x : E) :
    visible O x = 0 ↔ gram O x = 0 :=
  (visible_zero_iff O x).trans (gram_zero_iff O x).symm

theorem same_signature_iff_visible (O : E →L[ℝ] F) (x y : E) :
    O x = O y ↔ visible O x = visible O y := by
  constructor
  · intro h
    exact congrArg (inverse O) h
  · intro h
    simpa only [visible_preserves_signature] using congrArg O h

/-- Drazin/MP coincidence is justified for the self-adjoint Gram, not for K. -/
theorem gram_inverse_drazin (O : E →L[ℝ] F) :
    IsDrazinInverse (gram O) (inverse (gram O)) 1 := by
  have h := inverse_laws (gram O)
  apply selfAdjoint_mp_drazin (gram_selfAdjoint O)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end InfoGeometry.MassSpectrometry.SignatureGeometry
