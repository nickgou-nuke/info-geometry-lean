import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Moore-Penrose Inverse

This module provides the L0 foundation for generalized inverses in StarRings and Hilbert spaces.
It follows the Pauli Protocol: zero sorry, bottom-up derivation, and direct conductivity 
to Mathlib roots.

The construction is generalized to bounded operators between different Hilbert spaces.
-/

namespace InfoGeometry.Singular.MoorePenrose

-- Geometric adjoint postfix.
postfix:max "†" => star

section MP
variable {R : Type*} [Ring R] [StarRing R]

/-- The Four Penrose equations as a direct predicate. -/
def IsMoorePenroseInverse (A B : R) : Prop :=
  A * B * A = A ∧
  B * A * B = B ∧
  (A * B)† = A * B ∧
  (B * A)† = B * A

namespace IsMoorePenroseInverse

variable {A B : R}

theorem mk
    (h1 : A * B * A = A)
    (h2 : B * A * B = B)
    (h3 : (A * B)† = A * B)
    (h4 : (B * A)† = B * A) :
    IsMoorePenroseInverse A B :=
  ⟨h1, h2, h3, h4⟩

theorem aba_eq_a (h : IsMoorePenroseInverse A B) : A * B * A = A := h.1
theorem bab_eq_b (h : IsMoorePenroseInverse A B) : B * A * B = B := h.2.1
theorem ab_adj_eq (h : IsMoorePenroseInverse A B) : (A * B)† = A * B := h.2.2.1
theorem ba_adj_eq (h : IsMoorePenroseInverse A B) : (B * A)† = B * A := h.2.2.2

-- Backward-compatible aliases.
theorem eq1 (h : IsMoorePenroseInverse A B) : A * B * A = A := h.aba_eq_a
theorem eq2 (h : IsMoorePenroseInverse A B) : B * A * B = B := h.bab_eq_b
theorem eq3 (h : IsMoorePenroseInverse A B) : (A * B)† = A * B := h.ab_adj_eq
theorem eq4 (h : IsMoorePenroseInverse A B) : (B * A)† = B * A := h.ba_adj_eq

end IsMoorePenroseInverse

/-- Star distributes over a triple product. -/
lemma adjoint_mul_triple (X Y Z : R) : (X * Y * Z)† = Z† * Y† * X† := by
  simp only [star_mul, mul_assoc]

/-- The range projector A * B from a Moore-Penrose pair. -/
def MP_Projector (A B : R) (_h : IsMoorePenroseInverse A B) : R := A * B

lemma MP_Projector_idempotent {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h) * (MP_Projector A B h) = MP_Projector A B h := by
  unfold MP_Projector
  calc
    (A * B) * (A * B) = (A * B * A) * B := by simp only [mul_assoc]
    _ = A * B := by rw [h.aba_eq_a]

lemma MP_Projector_self_adjoint {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h)† = MP_Projector A B h := h.ab_adj_eq

/-- The Uniqueness Theorem for Moore-Penrose inverses. -/
theorem MoorePenrose_unique {A B C : R} 
    (hB : IsMoorePenroseInverse A B) 
    (hC : IsMoorePenroseInverse A C) : B = C := by
  have h1 : A * B = A * C := by
    calc
      A * B = (A * B)† := hB.ab_adj_eq.symm
      _ = B† * A† := star_mul _ _
      _ = B† * (A * C * A)† := by rw [hC.aba_eq_a]
      _ = B† * (A† * C† * A†) := by simp only [star_mul, mul_assoc]
      _ = (B† * A†) * C† * A† := by simp only [mul_assoc]
      _ = (A * B)† * C† * A† := by rw [star_mul]
      _ = (A * B) * C† * A† := by rw [hB.ab_adj_eq]
      _ = A * B * (C† * A†) := by rw [mul_assoc]
      _ = A * B * (A * C)† := by rw [star_mul]
      _ = A * B * (A * C) := by rw [hC.ab_adj_eq]
      _ = (A * B * A) * C := by simp only [mul_assoc]
      _ = A * C := by rw [hB.aba_eq_a]
  have h2 : B * A = C * A := by
    calc
      B * A = (B * A)† := hB.ba_adj_eq.symm
      _ = A† * B† := star_mul _ _
      _ = (A * C * A)† * B† := by rw [hC.aba_eq_a]
      _ = (A† * C† * A†) * B† := by simp only [star_mul, mul_assoc]
      _ = A† * C† * (A† * B†) := by simp only [mul_assoc]
      _ = A† * C† * (B * A)† := by rw [star_mul]
      _ = A† * C† * (B * A) := by rw [hB.ba_adj_eq]
      _ = (C * A)† * (B * A) := by rw [star_mul]
      _ = (C * A) * (B * A) := by rw [hC.ba_adj_eq]
      _ = C * (A * B * A) := by simp only [mul_assoc]
      _ = C * A := by rw [hB.aba_eq_a]
  calc
    B = B * A * B := hB.bab_eq_b.symm
    _ = (B * A) * B := by rw [mul_assoc]
    _ = (C * A) * B := by rw [h2]
    _ = C * (A * B) := by rw [← mul_assoc]
    _ = C * (A * C) := by rw [h1]
    _ = C * A * C := by rw [mul_assoc]
    _ = C := hC.bab_eq_b

end MP

section Hilbert

open InnerProductSpace ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {𝕜 E : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem exists_moorePenroseInverse_of_closedRange
    (A : E →L[𝕜] E)
    (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (B : E →L[𝕜] E), IsMoorePenroseInverse A B := by
  classical

  let K : Submodule 𝕜 E := A.ker
  let R : Submodule 𝕜 E := A.range
  let Kp : Submodule 𝕜 E := Kᗮ

  -- L0: closed/completed subspaces and their orthogonal projections.
  have hK_closed : IsClosed (K : Set E) := A.isClosed_ker
  haveI : CompleteSpace K := hK_closed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance

  haveI : CompleteSpace Kp := inferInstance
  haveI : Kp.HasOrthogonalProjection := inferInstance

  haveI : CompleteSpace R := hClosedRange.completeSpace_coe
  haveI : R.HasOrthogonalProjection := inferInstance

  -- The kernel component is killed by A, hence A only sees the Kᗮ component.
  have hA_on_Kp : ∀ x : E, A (Kp.starProjection x) = A x := by
    intro x
    have hsplit : K.starProjection x + Kp.starProjection x = x :=
      Submodule.starProjection_add_starProjection_orthogonal (K := K) x
    have hKzero : A (K.starProjection x) = 0 := by
      exact Submodule.starProjection_apply_mem K x
    calc
      A (Kp.starProjection x)
          = 0 + A (Kp.starProjection x) := by rw [zero_add]
      _ = A (K.starProjection x) + A (Kp.starProjection x) := by rw [hKzero]
      _ = A (K.starProjection x + Kp.starProjection x) := by rw [map_add]
      _ = A x := by rw [hsplit]

  -- L1: restrict A to Kᗮ and codrestrict it to range(A).
  let Ares : Kp →L[𝕜] R :=
    (A.comp Kp.subtypeL).codRestrict R (fun x =>
      LinearMap.mem_range.mpr ⟨x.1, rfl⟩)

  -- Injectivity: if x,y ∈ Kᗮ and A x = A y, then x-y ∈ K ∩ Kᗮ = {0}.
  have hAres_inj : (Ares : Kp →ₗ[𝕜] R).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply Subtype.ext
    have hval : A x.1 = A y.1 := congrArg Subtype.val hxy
    have hker : x.1 - y.1 ∈ K := by
      change A (x.1 - y.1) = 0
      rw [map_sub, hval, sub_self]
    have horth : x.1 - y.1 ∈ Kᗮ := Submodule.sub_mem Kp x.2 y.2
    have hzero : x.1 - y.1 = 0 := by
      have hmem : x.1 - y.1 ∈ K ⊓ Kᗮ := ⟨hker, horth⟩
      simpa [Submodule.inf_orthogonal_eq_bot K] using hmem
    exact sub_eq_zero.mp hzero

  -- Surjectivity: every y = A x in range(A) is A applied to the Kᗮ projection of x.
  have hAres_surj : (Ares : Kp →ₗ[𝕜] R).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    refine ⟨Kp.orthogonalProjection x, ?_⟩
    apply Subtype.ext
    change A ((Kp.orthogonalProjection x : Kp) : E) = A x
    exact hA_on_Kp x

  -- L2: invert the restricted/codrestricted map.
  let e : Kp ≃L[𝕜] R :=
    ContinuousLinearEquiv.ofBijective Ares hAres_inj hAres_surj

  -- B = inclusion_Kᗮ ∘ e⁻¹ ∘ P_range.
  let B : E →L[𝕜] E :=
    Kp.subtypeL.comp (e.symm.toContinuousLinearMap.comp R.orthogonalProjection)

  -- Direct verification of A ∘ B = P_range.
  have hAB_apply : ∀ x : E, A (B x) = R.starProjection x := by
    intro x
    have h := ContinuousLinearEquiv.ofBijective_apply_symm_apply Ares hAres_inj hAres_surj (R.orthogonalProjection x)
    have hval : A (B x) = (R.orthogonalProjection x : E) := by
      simp only [B, comp_apply, Submodule.subtypeL_apply]
      change (Ares (e.symm (R.orthogonalProjection x)) : E) = _
      rw [h]
    exact hval

  -- Direct verification of B ∘ A = P_Kᗮ.
  have hBA_apply : ∀ x : E, B (A x) = Kp.starProjection x := by
    intro x
    have hproj : R.orthogonalProjection (A x) = (⟨A x, ⟨x, rfl⟩⟩ : R) := by
      apply Subtype.ext
      exact Submodule.starProjection_mem_subspace_eq_self (K := R) (⟨A x, ⟨x, rfl⟩⟩ : R)
    have hTz : Ares (Kp.orthogonalProjection x) = (⟨A x, ⟨x, rfl⟩⟩ : R) := by
      apply Subtype.ext
      exact hA_on_Kp x
    have hsymm : e.symm (⟨A x, ⟨x, rfl⟩⟩ : R) = Kp.orthogonalProjection x := by
      rw [← hTz]
      exact (e.symm_apply_apply (Kp.orthogonalProjection x))
    calc
      B (A x) = ((e.symm (R.orthogonalProjection (A x)) : Kp) : E) := rfl
      _ = ((e.symm (⟨A x, ⟨x, rfl⟩⟩ : R) : Kp) : E) := by rw [hproj]
      _ = ((Kp.orthogonalProjection x : Kp) : E) := by rw [hsymm]
      _ = Kp.starProjection x := rfl

  have hAB : A * B = R.starProjection := by
    ext x
    exact hAB_apply x

  have hBA : B * A = Kp.starProjection := by
    ext x
    exact hBA_apply x

  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · -- A * B * A = A.
    ext x
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hAB_apply]
    exact Submodule.starProjection_mem_subspace_eq_self (K := R) (⟨A x, ⟨x, rfl⟩⟩ : R)
  · -- B * A * B = B.
    ext x
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hBA_apply]
    have hBmem : B x ∈ Kᗮ :=
      (e.symm (R.orthogonalProjection x)).property
    exact Submodule.starProjection_mem_subspace_eq_self (K := Kᗮ) ⟨B x, hBmem⟩
  · -- star (A * B) = A * B.
    rw [hAB]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection R)
  · -- star (B * A) = B * A.
    rw [hBA]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection Kp)

end Hilbert

end InfoGeometry.Singular.MoorePenrose
