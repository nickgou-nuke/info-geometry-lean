/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Bounded intertwiners in a directed operator corner

An arbitrary bounded map `T : E →L[𝕜] F` embeds faithfully into the lower-left
corner of the continuous endomorphisms of `E × F`. The product has its native
maximum norm; no Hilbert inner product or adjoint on this product is asserted.

Intertwining becomes commutation with the *diagonal pair* of source and target
actions. Commutation with the target corner alone instead forces `T = 0`.
Products of two creation maps with the same orientation vanish, so this
construction does not identify their multiplication with Connes fusion.
-/

namespace InfoGeometry.OperatorAlgebra.BoundedIntertwinerLinking

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded arrow, embedded as a lower-left endomorphism of the product. -/
def creation (T : E →L[𝕜] F) : E × F →L[𝕜] E × F :=
  (ContinuousLinearMap.inr 𝕜 E F).comp
    (T.comp (ContinuousLinearMap.fst 𝕜 E F))

@[simp] theorem creation_apply (T : E →L[𝕜] F) (z : E × F) :
    creation T z = (0, T z.1) := rfl

/-- The original bounded map can be recovered on the source summand. -/
theorem creation_injective :
    Function.Injective (creation (𝕜 := 𝕜) (E := E) (F := F)) := by
  intro S T h
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg Prod.snd (DFunLike.congr_fun h (x, 0))

@[simp] theorem creation_eq_zero_iff (T : E →L[𝕜] F) :
    creation T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun h (x, 0))
  · rintro rfl
    ext z <;> simp

/-- Two arrows with the same lower-left orientation have zero product.
In particular every `creation T` is square-zero. -/
@[simp] theorem creation_mul_creation (S T : E →L[𝕜] F) :
    creation S * creation T = 0 := by
  ext z <;> simp

/-- The embedding retains the operator norm for the native maximum-norm product. -/
@[simp] theorem norm_creation (T : E →L[𝕜] F) : ‖creation T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    rintro ⟨x, y⟩
    calc
      ‖creation T (x, y)‖ = ‖T x‖ := by simp [Prod.norm_def]
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ ‖T‖ * ‖(x, y)‖ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
        rw [Prod.norm_def]
        exact le_max_left _ _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (creation T))
    intro x
    simpa [Prod.norm_def] using (creation T).le_opNorm (x, 0)

/-- The target projection acts as the identity on the output of a creation map. -/
@[simp] theorem targetProjection_mul_creation (T : E →L[𝕜] F) :
    (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) * creation T = creation T := by
  ext z <;> simp [ContinuousLinearMap.prodMap]

/-- A creation map vanishes on the target summand. The multiplication order matters. -/
@[simp] theorem creation_mul_targetProjection (T : E →L[𝕜] F) :
    creation T * (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) = 0 := by
  ext z <;> simp [ContinuousLinearMap.prodMap]

/-- With `P` the source projection and `Q` the target projection, creation lies
in the directed corner `Q * End(E × F) * P`. -/
theorem creation_eq_corner (T : E →L[𝕜] F) :
    (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) * creation T *
      (1 : E →L[𝕜] E).prodMap (0 : F →L[𝕜] F) = creation T := by
  ext z <;> simp [ContinuousLinearMap.prodMap]

/-- The native source injection and target projection recover the full
lower-left corner of an arbitrary bounded endomorphism. -/
theorem creation_extract_eq_corner (Z : E × F →L[𝕜] E × F) :
    creation ((ContinuousLinearMap.snd 𝕜 E F).comp
      (Z.comp (ContinuousLinearMap.inl 𝕜 E F))) =
      (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) * Z *
        (1 : E →L[𝕜] E).prodMap (0 : F →L[𝕜] F) := by
  ext z <;> simp [ContinuousLinearMap.prodMap]

/-- Every bounded endomorphism supported in this corner comes from a bounded
map between the two summands. -/
theorem exists_creation_iff (Z : E × F →L[𝕜] E × F) :
    (∃ T : E →L[𝕜] F, creation T = Z) ↔
      (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) * Z *
        (1 : E →L[𝕜] E).prodMap (0 : F →L[𝕜] F) = Z := by
  constructor
  · rintro ⟨T, rfl⟩
    exact creation_eq_corner T
  · intro h
    refine ⟨(ContinuousLinearMap.snd 𝕜 E F).comp
      (Z.comp (ContinuousLinearMap.inl 𝕜 E F)), ?_⟩
    exact (creation_extract_eq_corner Z).trans h

/-- The exact commutator is the lower-left embedding of the intertwining defect. -/
theorem diagonal_commutator_creation
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (T : E →L[𝕜] F) :
    A.prodMap B * creation T - creation T * A.prodMap B =
      creation (B.comp T - T.comp A) := by
  ext z <;> simp [ContinuousLinearMap.prodMap]

/-- Commutation with the diagonal pair is exactly the correctly typed
intertwining relation `B ∘ T = T ∘ A`. -/
theorem diagonal_commute_creation_iff
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (T : E →L[𝕜] F) :
    Commute (A.prodMap B) (creation T) ↔ B.comp T = T.comp A := by
  change A.prodMap B * creation T = creation T * A.prodMap B ↔ _
  calc
    _ ↔ A.prodMap B * creation T - creation T * A.prodMap B = 0 :=
      sub_eq_zero.symm
    _ ↔ creation (B.comp T - T.comp A) = 0 := by
      rw [diagonal_commutator_creation]
    _ ↔ B.comp T - T.comp A = 0 := creation_eq_zero_iff _
    _ ↔ B.comp T = T.comp A := sub_eq_zero

/-- A nonzero creation map cannot commute with the target projection alone. -/
theorem targetProjection_commute_creation_iff (T : E →L[𝕜] F) :
    Commute ((0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F)) (creation T) ↔ T = 0 := by
  change (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) * creation T =
    creation T * (0 : E →L[𝕜] E).prodMap (1 : F →L[𝕜] F) ↔ _
  rw [targetProjection_mul_creation, creation_mul_targetProjection, creation_eq_zero_iff]

section Transport

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Independent continuous coordinate changes on the summands transport the
embedded arrow by `T ↦ v ∘ T ∘ u⁻¹`, in that order. -/
theorem creation_conjugate
    (u : E ≃L[𝕜] E') (v : F ≃L[𝕜] F') (T : E →L[𝕜] F) :
    (u.prodCongr v).toContinuousLinearMap.comp
      ((creation T).comp (u.prodCongr v).symm.toContinuousLinearMap) =
      creation (v.toContinuousLinearMap.comp (T.comp u.symm.toContinuousLinearMap)) := by
  ext z <;> simp [ContinuousLinearEquiv.prodCongr_symm]

end Transport

end InfoGeometry.OperatorAlgebra.BoundedIntertwinerLinking
