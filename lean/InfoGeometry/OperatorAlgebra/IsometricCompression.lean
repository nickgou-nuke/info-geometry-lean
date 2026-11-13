/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Compression through a Hilbert-space isometry

An isometric embedding `V : E →ₗᵢ[𝕜] F` identifies bounded operators on `E`
with the operators supported on its range in `F`. The supported extension
preserves operator norm, even when `V` is not surjective. Compression of an
ambient projection is a projection exactly when its complementary leakage
vanishes, equivalently when the ambient projection preserves the range of `V`.

The ambient Gram factorization is the existing Peirce compression theorem.
This file supplies its transport between distinct Hilbert spaces and native
operator positivity. It does not construct an STFT or a Bargmann transform.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.IsometricCompression

open InfoGeometry.Core.PeirceCompressionDefect

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The bounded range projection of the isometric embedding. -/
def rangeProjection (V : E →ₗᵢ[𝕜] F) : F →L[𝕜] F :=
  V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint

/-- Pull an ambient bounded operator back through an isometric embedding. -/
def compress (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) : E →L[𝕜] E :=
  V.toContinuousLinearMap.adjoint.comp (S.comp V.toContinuousLinearMap)

/-- Extend an operator on the source by zero on the orthogonal complement
of the isometry's range. -/
def supportedExtension (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) : F →L[𝕜] F :=
  V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)

/-- The range expression is an actual self-adjoint idempotent. -/
theorem rangeProjection_isStarProjection (V : E →ₗᵢ[𝕜] F) :
    IsStarProjection (rangeProjection V) := by
  constructor
  · change
      (V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint).comp
          (V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint) =
        V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint
    calc
      _ = V.toContinuousLinearMap.comp
          ((V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap).comp
            V.toContinuousLinearMap.adjoint) := by
              simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by
        rw [V.adjoint_comp_self]
        simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  · change
      (V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint).adjoint =
        V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- Its native linear range is precisely the image of the original isometry. -/
theorem range_rangeProjection (V : E →ₗᵢ[𝕜] F) :
    (rangeProjection V).range = V.toContinuousLinearMap.range := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨V.toContinuousLinearMap.adjoint z, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨V.toContinuousLinearMap x, ?_⟩
    exact congrArg (fun T : E →L[𝕜] E => V.toContinuousLinearMap (T x))
      V.adjoint_comp_self

@[simp] theorem compress_supportedExtension (V : E →ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) : compress V (supportedExtension V T) = T := by
  unfold compress supportedExtension
  calc
    _ = (V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap).comp
        (T.comp (V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap)) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = T := by
      rw [V.adjoint_comp_self]
      simp only [ContinuousLinearMap.one_def,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

/-- Re-extending a compressed operator is the ambient corner sandwich. -/
theorem supportedExtension_compress (V : E →ₗᵢ[𝕜] F)
    (S : F →L[𝕜] F) :
    supportedExtension V (compress V S) = rangeProjection V * S * rangeProjection V := by
  simp only [supportedExtension, compress, rangeProjection,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

/-- No source operator is lost by its supported extension. -/
theorem supportedExtension_injective (V : E →ₗᵢ[𝕜] F) :
    Function.Injective (supportedExtension V) := by
  intro S T h
  have h' := congrArg (compress V) h
  simpa only [compress_supportedExtension] using h'

@[simp] theorem supportedExtension_sub (V : E →ₗᵢ[𝕜] F)
    (S T : E →L[𝕜] E) :
    supportedExtension V (S - T) = supportedExtension V S - supportedExtension V T := by
  simp only [supportedExtension, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub]

/-- Supported extension preserves the ordered operator product. -/
theorem supportedExtension_mul (V : E →ₗᵢ[𝕜] F) (S T : E →L[𝕜] E) :
    supportedExtension V (S * T) = supportedExtension V S * supportedExtension V T := by
  unfold supportedExtension
  symm
  change
    (V.toContinuousLinearMap.comp (S.comp V.toContinuousLinearMap.adjoint)).comp
        (V.toContinuousLinearMap.comp (T.comp V.toContinuousLinearMap.adjoint)) =
      V.toContinuousLinearMap.comp ((S.comp T).comp V.toContinuousLinearMap.adjoint)
  calc
    _ = V.toContinuousLinearMap.comp
        (S.comp ((V.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap).comp
          (T.comp V.toContinuousLinearMap.adjoint))) := by
            simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by
      rw [V.adjoint_comp_self]
      simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_assoc]

@[simp] theorem supportedExtension_star (V : E →ₗᵢ[𝕜] F)
    (T : E →L[𝕜] E) :
    supportedExtension V (star T) = star (supportedExtension V T) := by
  simp only [supportedExtension, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

@[simp] theorem compress_star (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    compress V (star S) = star (compress V S) := by
  simp only [compress, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

@[simp] theorem compress_one (V : E →ₗᵢ[𝕜] F) : compress V 1 = 1 := by
  simpa only [compress, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    V.adjoint_comp_self

/-- Complementary ambient symbols retain the full identity on the source. -/
theorem compress_complement (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    compress V (1 - S) = 1 - compress V S := by
  have hsub : compress V (1 - S) = compress V 1 - compress V S := by
    simp only [compress, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [hsub, compress_one]

/-- Supported extension preserves operator norm without assuming surjectivity
or a nonzero source space. -/
theorem norm_supportedExtension (V : E →ₗᵢ[𝕜] F) (T : E →L[𝕜] E) :
    ‖supportedExtension V T‖ = ‖T‖ := by
  unfold supportedExtension
  rw [V.norm_toContinuousLinearMap_comp]
  calc
    ‖T.comp V.toContinuousLinearMap.adjoint‖ =
        ‖(T.comp V.toContinuousLinearMap.adjoint).adjoint‖ := by
          rw [LinearIsometryEquiv.norm_map]
    _ = ‖V.toContinuousLinearMap.comp T.adjoint‖ := by
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    _ = ‖T.adjoint‖ := V.norm_toContinuousLinearMap_comp
    _ = ‖T‖ := LinearIsometryEquiv.norm_map _ _

/-- Pullback and the supported ambient corner have exactly the same norm. -/
theorem norm_compress_eq_corner (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    ‖compress V S‖ = ‖rangeProjection V * S * rangeProjection V‖ := by
  rw [← supportedExtension_compress, norm_supportedExtension]

/-- Native positivity is preserved by isometric compression. -/
theorem compress_isPositive (V : E →ₗᵢ[𝕜] F) {S : F →L[𝕜] F}
    (hS : S.IsPositive) : (compress V S).IsPositive := by
  simpa only [compress, ContinuousLinearMap.comp_assoc] using
    hS.adjoint_conj V.toContinuousLinearMap

/-- A projection compression is the Gram operator of the localized isometry. -/
theorem compress_projection_eq_gram (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    compress V Q = (Q.comp V.toContinuousLinearMap).adjoint.comp
      (Q.comp V.toContinuousLinearMap) := by
  have hstar : Q.adjoint = Q := hQ.isSelfAdjoint
  have hsq : Q.comp Q = Q := hQ.isIdempotentElem.eq
  symm
  calc
    _ = V.toContinuousLinearMap.adjoint.comp
        ((Q.adjoint.comp Q).comp V.toContinuousLinearMap) := by
          simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    _ = compress V Q := by rw [hstar, hsq]; rfl

/-- Localization in a projection and its complement has exactly the full
source Gram operator. This uses an isometry, with no surjectivity assumption. -/
theorem localization_gram_partition (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    (Q.comp V.toContinuousLinearMap).adjoint.comp (Q.comp V.toContinuousLinearMap) +
      ((1 - Q).comp V.toContinuousLinearMap).adjoint.comp
        ((1 - Q).comp V.toContinuousLinearMap) = 1 := by
  rw [← compress_projection_eq_gram V Q hQ,
    ← compress_projection_eq_gram V (1 - Q) hQ.one_sub, compress_complement]
  exact add_sub_cancel _ _

/-- The norm of the positive compression is the squared localization norm. -/
theorem norm_compress_projection (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    ‖compress V Q‖ = ‖Q.comp V.toContinuousLinearMap‖ ^ 2 := by
  rw [compress_projection_eq_gram V Q hQ,
    ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- Projection compression is contractive in the native operator norm. -/
theorem norm_compress_projection_le_one (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : ‖compress V Q‖ ≤ 1 := by
  have hbound : ‖Q.comp V.toContinuousLinearMap‖ ≤ 1 := by
    calc
      _ ≤ ‖Q‖ * ‖V.toContinuousLinearMap‖ := Q.opNorm_comp_le _
      _ ≤ 1 * 1 := mul_le_mul hQ.norm_le V.norm_toContinuousLinearMap_le
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [norm_compress_projection V Q hQ]
  exact pow_le_one₀ (norm_nonneg _) hbound

/-- The part of an ambient image which leaves the embedded source space. -/
def leakage (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) : E →L[𝕜] F :=
  (1 - rangeProjection V).comp (S.comp V.toContinuousLinearMap)

/-- A projection symbol has an exact, positive Gram defect after compression.
The factorization is transported from the existing ambient Peirce owner. -/
theorem projection_defect_eq_gram (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    compress V Q - (compress V Q) ^ 2 = (leakage V Q).adjoint.comp (leakage V Q) := by
  have hp := rangeProjection_isStarProjection V
  have hambient :
      rangeProjection V * Q * rangeProjection V -
          (rangeProjection V * Q * rangeProjection V) ^ 2 =
        star ((1 - rangeProjection V) * Q * rangeProjection V) *
          ((1 - rangeProjection V) * Q * rangeProjection V) := by
    simpa only [hQ.isSelfAdjoint.star_eq, hQ.isIdempotentElem.eq, pow_two] using
      compression_adjoint_mul_defect (rangeProjection V) Q Q
        hp.isIdempotentElem.eq hp.isSelfAdjoint.star_eq
  have htransfer :
      (leakage V Q).comp V.toContinuousLinearMap.adjoint =
        (1 - rangeProjection V) * Q * rangeProjection V := by
    simp only [leakage, rangeProjection, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  have hgram :
      supportedExtension V ((leakage V Q).adjoint.comp (leakage V Q)) =
        star ((leakage V Q).comp V.toContinuousLinearMap.adjoint) *
          ((leakage V Q).comp V.toContinuousLinearMap.adjoint) := by
    simp only [supportedExtension, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  apply supportedExtension_injective V
  simpa only [pow_two, supportedExtension_sub, supportedExtension_mul,
    supportedExtension_compress, hgram, htransfer] using hambient

/-- The operator-norm defect measures the squared norm of the actual leakage. -/
theorem norm_projection_defect (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    ‖compress V Q - (compress V Q) ^ 2‖ = ‖leakage V Q‖ ^ 2 := by
  rw [projection_defect_eq_gram V Q hQ,
    ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- An ambient projection compresses to a native positive operator. -/
theorem compress_projection_isPositive (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : (compress V Q).IsPositive :=
  compress_isPositive V (ContinuousLinearMap.IsPositive.of_isStarProjection hQ)

/-- Its idempotency defect is native positive on the source Hilbert space. -/
theorem projection_defect_isPositive (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) : (compress V Q - (compress V Q) ^ 2).IsPositive := by
  rw [projection_defect_eq_gram V Q hQ]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- Compression preserves idempotency precisely when the projection does not
transfer the embedded source into its orthogonal complement. -/
theorem compress_projection_idempotent_iff (V : E →ₗᵢ[𝕜] F) (Q : F →L[𝕜] F)
    (hQ : IsStarProjection Q) :
    IsIdempotentElem (compress V Q) ↔ leakage V Q = 0 := by
  change compress V Q * compress V Q = compress V Q ↔ leakage V Q = 0
  rw [← pow_two, eq_comm, ← sub_eq_zero, projection_defect_eq_gram V Q hQ]
  exact ContinuousLinearMap.adjoint_comp_self_eq_zero_iff

/-- The leakage criterion is equivalent to the native invariant-submodule
condition, for arbitrary bounded ambient operators. -/
theorem leakage_eq_zero_iff_invariant (V : E →ₗᵢ[𝕜] F) (S : F →L[𝕜] F) :
    leakage V S = 0 ↔
      V.toContinuousLinearMap.range ∈ Module.End.invtSubmodule S.toLinearMap := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  constructor
  · intro h y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨V.toContinuousLinearMap.adjoint (S (V.toContinuousLinearMap x)), ?_⟩
    have hx := congrArg (fun A : E →L[𝕜] F => A x) h
    change S (V.toContinuousLinearMap x) -
      V.toContinuousLinearMap
        (V.toContinuousLinearMap.adjoint (S (V.toContinuousLinearMap x))) = 0 at hx
    exact (sub_eq_zero.mp hx).symm
  · intro h
    ext x
    obtain ⟨z, hz⟩ := h (V.toContinuousLinearMap x) ⟨x, rfl⟩
    change V.toContinuousLinearMap z = S (V.toContinuousLinearMap x) at hz
    change S (V.toContinuousLinearMap x) -
      V.toContinuousLinearMap
        (V.toContinuousLinearMap.adjoint (S (V.toContinuousLinearMap x))) = 0
    rw [← hz]
    apply sub_eq_zero.mpr
    exact (congrArg (fun T : E →L[𝕜] E => V.toContinuousLinearMap (T z))
      V.adjoint_comp_self).symm

/-- A compressed projection remains an orthogonal projection exactly when
the ambient projection preserves the native range of the isometry. -/
theorem compress_isStarProjection_iff_invariant (V : E →ₗᵢ[𝕜] F)
    (Q : F →L[𝕜] F) (hQ : IsStarProjection Q) :
    IsStarProjection (compress V Q) ↔
      V.toContinuousLinearMap.range ∈ Module.End.invtSubmodule Q.toLinearMap := by
  rw [← leakage_eq_zero_iff_invariant V Q]
  constructor
  · intro h
    exact (compress_projection_idempotent_iff V Q hQ).mp h.isIdempotentElem
  · intro h
    exact ⟨(compress_projection_idempotent_iff V Q hQ).mpr h,
      (compress_projection_isPositive V Q hQ).isSelfAdjoint⟩

end InfoGeometry.OperatorAlgebra.IsometricCompression
