import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# Adjoint Hodge consequences

This is the positive-Hilbert-space layer.  It is intentionally separate from
the split Krein carrier: orthogonality and positivity require an explicit
adjoint witness.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure ChiralHodgeAdjointData where
  d : E →L[ℝ] E
  delta : E →L[ℝ] E
  d_sq : d.comp d = 0
  delta_sq : delta.comp delta = 0
  adjoint_eq : ContinuousLinearMap.adjoint d = delta

def ChiralHodgeAdjointData.dirac (H : ChiralHodgeAdjointData (E := E)) : E →L[ℝ] E :=
  H.d + H.delta

def ChiralHodgeAdjointData.laplacian
    (H : ChiralHodgeAdjointData (E := E)) : E →L[ℝ] E :=
  H.d.comp H.delta + H.delta.comp H.d

theorem chiral_hodge_adjoint_dirac_sq
    (H : ChiralHodgeAdjointData (E := E)) :
    H.dirac.comp H.dirac = H.laplacian := by
  unfold ChiralHodgeAdjointData.dirac ChiralHodgeAdjointData.laplacian
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add, H.d_sq, H.delta_sq]
  simp

theorem chiral_hodge_adjoint_inner_d
    (H : ChiralHodgeAdjointData (E := E)) (x y : E) :
    @inner ℝ E _ (H.d x) y = @inner ℝ E _ x (H.delta y) := by
  have h := (ContinuousLinearMap.adjoint_inner_left H.d x y).symm
  simpa [H.adjoint_eq, real_inner_comm] using h

theorem chiral_hodge_adjoint_inner_delta
    (H : ChiralHodgeAdjointData (E := E)) (x y : E) :
    @inner ℝ E _ (H.delta x) y = @inner ℝ E _ x (H.d y) := by
  have hadj : ContinuousLinearMap.adjoint H.delta = H.d := by
    rw [← H.adjoint_eq, ContinuousLinearMap.adjoint_adjoint]
  have h := (ContinuousLinearMap.adjoint_inner_left H.delta x y).symm
  simpa [hadj, real_inner_comm] using h

theorem chiral_hodge_adjoint_inner_laplacian
    (H : ChiralHodgeAdjointData (E := E)) (x : E) :
    @inner ℝ E _ x (H.laplacian x) =
      @inner ℝ E _ (H.delta x) (H.delta x) +
        @inner ℝ E _ (H.d x) (H.d x) := by
  unfold ChiralHodgeAdjointData.laplacian
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  change @inner ℝ E _ x (H.d (H.delta x)) +
      @inner ℝ E _ x (H.delta (H.d x)) = _
  rw [show @inner ℝ E _ x (H.d (H.delta x)) =
      @inner ℝ E _ (H.delta x) (H.delta x) by
        simpa [real_inner_comm] using chiral_hodge_adjoint_inner_d H (H.delta x) x,
    show @inner ℝ E _ x (H.delta (H.d x)) =
      @inner ℝ E _ (H.d x) (H.d x) by
        simpa [real_inner_comm] using chiral_hodge_adjoint_inner_delta H (H.d x) x]

theorem chiral_hodge_adjoint_mem_ker_laplacian_iff
    (H : ChiralHodgeAdjointData (E := E)) (x : E) :
    H.laplacian x = 0 ↔ H.d x = 0 ∧ H.delta x = 0 := by
  constructor
  · intro hx
    have hq : @inner ℝ E _ x (H.laplacian x) = 0 := by
      rw [hx, inner_zero_right]
    rw [chiral_hodge_adjoint_inner_laplacian H x] at hq
    have hd : @inner ℝ E _ (H.d x) (H.d x) = 0 := by
      have h₁ : 0 ≤ @inner ℝ E _ (H.delta x) (H.delta x) := real_inner_self_nonneg
      have h₂ : 0 ≤ @inner ℝ E _ (H.d x) (H.d x) := real_inner_self_nonneg
      linarith
    have hdelta : @inner ℝ E _ (H.delta x) (H.delta x) = 0 := by
      have h₁ : 0 ≤ @inner ℝ E _ (H.delta x) (H.delta x) := real_inner_self_nonneg
      have h₂ : 0 ≤ @inner ℝ E _ (H.d x) (H.d x) := real_inner_self_nonneg
      linarith
    exact ⟨inner_self_eq_zero.mp hd, inner_self_eq_zero.mp hdelta⟩
  · rintro ⟨hd, hdelta⟩
    unfold ChiralHodgeAdjointData.laplacian
    rw [ContinuousLinearMap.add_apply]
    change H.d (H.delta x) + H.delta (H.d x) = 0
    rw [hdelta, hd, map_zero, map_zero, add_zero]

theorem chiral_hodge_adjoint_image_orthogonal
    (H : ChiralHodgeAdjointData (E := E)) (x y : E) :
    @inner ℝ E _ (H.d x) (H.delta y) = 0 := by
  rw [chiral_hodge_adjoint_inner_d H x (H.delta y)]
  rw [show H.delta (H.delta y) = (H.delta.comp H.delta) y by rfl,
    H.delta_sq, ContinuousLinearMap.zero_apply, inner_zero_right]

end
end InfoGeometry.Dynamics
