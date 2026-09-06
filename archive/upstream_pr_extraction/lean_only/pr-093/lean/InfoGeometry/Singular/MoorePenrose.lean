import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Moore-Penrose Inverse

This module provides the L0 foundation for generalized inverses in StarRings and Hilbert spaces.
It follows the Pauli Protocol: zero by rfl, bottom-up derivation, and direct conductivity
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

end IsMoorePenroseInverse

/-- Star distributes over a triple product. -/
lemma adjoint_mul_triple (X Y Z : R) : (X * Y * Z)† = Z† * Y† * X† := by
  calc
    (X * Y * Z)† = (X * (Y * Z))† := by rw [mul_assoc]
    _ = (Y * Z)† * X† := by rw [star_mul]
    _ = Z† * Y† * X† := by rw [star_mul]

/-- The range projector A * B from a Moore-Penrose pair. -/
def MP_Projector (A B : R) (_h : IsMoorePenroseInverse A B) : R := A * B

lemma MP_Projector_idempotent {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h) * (MP_Projector A B h) = MP_Projector A B h := by
  unfold MP_Projector
  calc
    (A * B) * (A * B) = A * (B * (A * B)) := by rw [mul_assoc]
    _ = A * (B * A * B) := by rw [← mul_assoc B A B]
    _ = A * B := by rw [h.bab_eq_b]

lemma MP_Projector_self_adjoint {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h)† = MP_Projector A B h := by
  unfold MP_Projector
  exact h.ab_adj_eq

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

/-- 
  Moore--Penrose inverse property for continuous linear maps between distinct
  Hilbert spaces (rectangular case).
  -/
def IsMoorePenroseInverseCLM
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) (B : F →L[𝕜] E) : Prop :=
  (A.comp B).comp A = A ∧
  (B.comp A).comp B = B ∧
  star (A.comp B) = A.comp B ∧
  star (B.comp A) = B.comp A

end MP

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Restriction of `A` to the orthogonal complement of its kernel. -/
noncomputable def mpRestricted (A : E →L[𝕜] F) : (A.ker)ᗮ →L[𝕜] A.range :=
  (A.comp (A.ker)ᗮ.subtypeL).codRestrict A.range (fun x => LinearMap.mem_range.mpr ⟨x.1, rfl⟩)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The restricted operator is injective. -/
theorem mpRestricted_injective (A : E →L[𝕜] F) : Function.Injective (mpRestricted A) := by
  intro x y h
  ext
  have h_val := Subtype.ext_iff.mp h
  have hAxy : A (x : E) = A (y : E) := by
    simpa [mpRestricted] using h_val
  have h_mem : (x - y : E) ∈ A.ker := by
    change A ((x : E) - (y : E)) = 0
    rw [map_sub, hAxy, sub_self]
  have h_mem_Kp : (x - y : E) ∈ (A.ker)ᗮ := Submodule.sub_mem _ x.2 y.2
  have h_zero : (x - y : E) = 0 := by
    exact inner_self_eq_zero.mp
      (Submodule.inner_left_of_mem_orthogonal h_mem h_mem_Kp)
  exact sub_eq_zero.mp h_zero

omit [CompleteSpace F] in
/-- The restricted operator is surjective. -/
theorem mpRestricted_surjective (A : E →L[𝕜] F) : Function.Surjective (mpRestricted A) := by
  intro y
  obtain ⟨x, hx⟩ := y.2
  refine ⟨⟨(Submodule.starProjection (A.ker)ᗮ) x,
    Submodule.starProjection_apply_mem ((A.ker)ᗮ) x⟩, ?_⟩
  apply Subtype.ext
  simp only [mpRestricted]
  have h_split : x = (Submodule.starProjection (A.ker)) x + (Submodule.starProjection (A.ker)ᗮ) x := by
    exact (Submodule.starProjection_add_starProjection_orthogonal (K := A.ker) x).symm
  have h_ker : A ((Submodule.starProjection (A.ker)) x) = 0 := by
    exact Submodule.starProjection_apply_mem (A.ker) x
  have hA_on_Kp : A x = A ((Submodule.starProjection (A.ker)ᗮ) x) := by
    calc
      A x = A ((Submodule.starProjection (A.ker)) x +
          (Submodule.starProjection (A.ker)ᗮ) x) := by
            exact congrArg A h_split
      _ = A ((Submodule.starProjection (A.ker)) x) +
          A ((Submodule.starProjection (A.ker)ᗮ) x) := by rw [map_add]
      _ = A ((Submodule.starProjection (A.ker)ᗮ) x) := by rw [h_ker, zero_add]
  calc
    A ((Submodule.starProjection (A.ker)ᗮ) x)
        = A x := hA_on_Kp.symm
    _ = y := hx

/-- The continuous linear equivalence between `(ker A)ᗮ` and `range A`. -/
noncomputable def mpEquiv (A : E →L[𝕜] F) (hClosedRange : IsClosed (A.range : Set F)) :
    (A.ker)ᗮ ≃L[𝕜] A.range :=
  haveI : CompleteSpace A.range := hClosedRange.completeSpace_coe
  ContinuousLinearEquiv.ofBijective (mpRestricted A)
    (LinearMap.ker_eq_bot.mpr (mpRestricted_injective A))
    (LinearMap.range_eq_top.mpr (mpRestricted_surjective A))

/--
  Constructive Moore--Penrose inverse for a continuous linear map between Hilbert spaces
  with closed range.
  -/
noncomputable def moorePenroseInverse
    (A : E →L[𝕜] F)
    (hClosedRange : IsClosed (A.range : Set F)) : F →L[𝕜] E :=
  let Kp : Submodule 𝕜 E := (A.ker)ᗮ
  let R : Submodule 𝕜 F := A.range
  haveI : CompleteSpace R := hClosedRange.completeSpace_coe
  Kp.subtypeL.comp ((mpEquiv A hClosedRange).symm.toContinuousLinearMap.comp (Submodule.orthogonalProjection R))

/-- Proof that the construction satisfies the Moore--Penrose identities. -/
theorem isMoorePenroseInverse_moorePenroseInverse
    (A : E →L[𝕜] F)
    (hClosedRange : IsClosed (A.range : Set F)) :
    IsMoorePenroseInverseCLM A (moorePenroseInverse A hClosedRange) := by
  let B := moorePenroseInverse A hClosedRange
  let Kp : Submodule 𝕜 E := (A.ker)ᗮ
  let R : Submodule 𝕜 F := A.range
  let e := mpEquiv A hClosedRange
  haveI : CompleteSpace R := hClosedRange.completeSpace_coe
  have hAB : A.comp B = R.starProjection := by
    ext y
    let y_proj : R := Submodule.orthogonalProjection R y
    let x_perp : Kp := e.symm y_proj
    have he_x : e x_perp = y_proj := e.apply_symm_apply y_proj
    have h_Axp : A (x_perp : E) = (y_proj : F) := by
      have hval := congrArg Subtype.val he_x
      simpa [e, mpEquiv, mpRestricted] using hval
    change A ((e.symm (Submodule.orthogonalProjection R y) : Kp) : E) =
      R.starProjection y
    exact h_Axp
  have hBA : B.comp A = Kp.starProjection := by
    ext x
    let x_perp : Kp := Submodule.orthogonalProjection Kp x
    have hAx : A x ∈ R := LinearMap.mem_range.mpr ⟨x, rfl⟩
    have h_split :
        x = (Submodule.starProjection (A.ker)) x + (Submodule.starProjection Kp) x := by
      exact (Submodule.starProjection_add_starProjection_orthogonal (K := A.ker) x).symm
    have hA_on_Kp : A x = A (x_perp : E) := by
      change A x = A ((Submodule.starProjection Kp) x)
      have h_ker : A ((Submodule.starProjection (A.ker)) x) = 0 := by
        exact Submodule.starProjection_apply_mem (A.ker) x
      calc
        A x = A ((Submodule.starProjection (A.ker)) x +
            (Submodule.starProjection Kp) x) := by
              exact congrArg A h_split
        _ = A ((Submodule.starProjection (A.ker)) x) +
            A ((Submodule.starProjection Kp) x) := by rw [map_add]
        _ = A ((Submodule.starProjection Kp) x) := by rw [h_ker, zero_add]
    have hproj :
        Submodule.orthogonalProjection R (A x) = ⟨A x, hAx⟩ := by
      exact Submodule.orthogonalProjection_mem_subspace_eq_self ⟨A x, hAx⟩
    have he : e x_perp = Submodule.orthogonalProjection R (A x) := by
      apply Subtype.ext
      change A (x_perp : E) = (Submodule.orthogonalProjection R (A x) : F)
      rw [← hA_on_Kp]
      exact (congrArg Subtype.val hproj).symm
    have hsymm : e.symm (Submodule.orthogonalProjection R (A x)) = x_perp := by
      rw [← he]
      exact e.symm_apply_apply x_perp
    change ((e.symm (Submodule.orthogonalProjection R (A x)) : Kp) : E) =
      Kp.starProjection x
    rw [hsymm]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ABA = A
    ext x
    have hAx : A x ∈ R := LinearMap.mem_range.mpr ⟨x, rfl⟩
    calc
      ((A.comp B).comp A) x = (A.comp B) (A x) := rfl
      _ = R.starProjection (A x) := by rw [hAB]
      _ = A x := Submodule.starProjection_mem_subspace_eq_self ⟨A x, hAx⟩
  · -- BAB = B
    ext y
    have hBy : B y ∈ Kp := by
      simp [B, moorePenroseInverse, Kp]
    calc
      ((B.comp A).comp B) y = (B.comp A) (B y) := rfl
      _ = Kp.starProjection (B y) := by rw [hBA]
      _ = B y := Submodule.starProjection_mem_subspace_eq_self ⟨B y, hBy⟩
  · -- star (AB) = AB
    rw [hAB]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection R)
  · -- star (BA) = BA
    rw [hBA]
    exact IsSelfAdjoint.star_eq (isSelfAdjoint_starProjection Kp)

/-- Legacy existence wrapper for endomorphisms. -/
theorem exists_moorePenroseInverse_of_closedRange
    (A : E →L[𝕜] E)
    (hClosedRange : IsClosed (A.range : Set E)) :
    ∃ (B : E →L[𝕜] E), IsMoorePenroseInverse A B := by
  let B := moorePenroseInverse A hClosedRange
  use B
  have h := isMoorePenroseInverse_moorePenroseInverse A hClosedRange
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end Hilbert

end InfoGeometry.Singular.MoorePenrose
