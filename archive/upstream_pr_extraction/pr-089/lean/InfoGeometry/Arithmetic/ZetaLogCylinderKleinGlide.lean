import Mathlib.Tactic

import InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

/-!
# Logarithmic cylinder and affine Klein glide

This is the affine/topological shadow after the completed-Xi homogeneous
coordinate.  It keeps the two translations separate:

* `transverseTranslation a` is inverted by the glide;
* `cylinderTranslation L` is the square of the glide.

No claim is made that a completed-Xi zero orbit is this quotient.
-/

namespace InfoGeometry.Arithmetic.ZetaLogCylinderKleinGlide

abbrev CylinderPoint : Type := ℝ × ℝ

def transverseTranslation (a : ℝ) : CylinderPoint → CylinderPoint :=
  fun X => (X.1 + a, X.2)

def cylinderTranslation (L : ℝ) : CylinderPoint → CylinderPoint :=
  fun X => (X.1, X.2 + L)

noncomputable def glide (L : ℝ) : CylinderPoint → CylinderPoint :=
  fun X => (-X.1, X.2 + L / 2)

noncomputable def glideInv (L : ℝ) : CylinderPoint → CylinderPoint :=
  fun X => (-X.1, X.2 - L / 2)

@[simp] theorem transverseTranslation_apply (a x t : ℝ) :
    transverseTranslation a (x, t) = (x + a, t) := rfl

@[simp] theorem cylinderTranslation_apply (L x t : ℝ) :
    cylinderTranslation L (x, t) = (x, t + L) := rfl

@[simp] theorem glide_apply (L x t : ℝ) :
    glide L (x, t) = (-x, t + L / 2) := rfl

@[simp] theorem glideInv_apply (L x t : ℝ) :
    glideInv L (x, t) = (-x, t - L / 2) := rfl

theorem glide_comp_glide (L : ℝ) (X : CylinderPoint) :
    glide L (glide L X) = cylinderTranslation L X := by
  rcases X with ⟨x, t⟩
  simp [glide, cylinderTranslation]
  ring

theorem glideInv_comp_glide (L : ℝ) (X : CylinderPoint) :
    glideInv L (glide L X) = X := by
  rcases X with ⟨x, t⟩
  simp [glide, glideInv]

theorem glide_comp_glideInv (L : ℝ) (X : CylinderPoint) :
    glide L (glideInv L X) = X := by
  rcases X with ⟨x, t⟩
  simp [glide, glideInv]

theorem transverseTranslation_add (a b : ℝ) (X : CylinderPoint) :
    transverseTranslation b (transverseTranslation a X) =
      transverseTranslation (a + b) X := by
  rcases X with ⟨x, t⟩
  simp [transverseTranslation, add_assoc]

theorem transverseTranslation_neg_left (a : ℝ) (X : CylinderPoint) :
    transverseTranslation (-a) (transverseTranslation a X) = X := by
  rcases X with ⟨x, t⟩
  simp [transverseTranslation]

theorem transverseTranslation_neg_right (a : ℝ) (X : CylinderPoint) :
    transverseTranslation a (transverseTranslation (-a) X) = X := by
  rcases X with ⟨x, t⟩
  simp [transverseTranslation]

theorem cylinderTranslation_add (L M : ℝ) (X : CylinderPoint) :
    cylinderTranslation M (cylinderTranslation L X) =
      cylinderTranslation (L + M) X := by
  rcases X with ⟨x, t⟩
  simp [cylinderTranslation, add_assoc]

theorem cylinderTranslation_neg_left (L : ℝ) (X : CylinderPoint) :
    cylinderTranslation (-L) (cylinderTranslation L X) = X := by
  rcases X with ⟨x, t⟩
  simp [cylinderTranslation]

theorem cylinderTranslation_neg_right (L : ℝ) (X : CylinderPoint) :
    cylinderTranslation L (cylinderTranslation (-L) X) = X := by
  rcases X with ⟨x, t⟩
  simp [cylinderTranslation]

noncomputable def transverseTranslationEquiv (a : ℝ) :
    CylinderPoint ≃ CylinderPoint where
  toFun := transverseTranslation a
  invFun := transverseTranslation (-a)
  left_inv := transverseTranslation_neg_left a
  right_inv := transverseTranslation_neg_right a

noncomputable def cylinderTranslationEquiv (L : ℝ) :
    CylinderPoint ≃ CylinderPoint where
  toFun := cylinderTranslation L
  invFun := cylinderTranslation (-L)
  left_inv := cylinderTranslation_neg_left L
  right_inv := cylinderTranslation_neg_right L

noncomputable def glideEquiv (L : ℝ) : CylinderPoint ≃ CylinderPoint where
  toFun := glide L
  invFun := glideInv L
  left_inv := glideInv_comp_glide L
  right_inv := glide_comp_glideInv L

@[simp] theorem transverseTranslationEquiv_apply (a : ℝ) (X : CylinderPoint) :
    transverseTranslationEquiv a X = transverseTranslation a X := rfl

@[simp] theorem cylinderTranslationEquiv_apply (L : ℝ) (X : CylinderPoint) :
    cylinderTranslationEquiv L X = cylinderTranslation L X := rfl

@[simp] theorem glideEquiv_apply (L : ℝ) (X : CylinderPoint) :
    glideEquiv L X = glide L X := rfl

@[simp] theorem glideEquiv_symm_apply (L : ℝ) (X : CylinderPoint) :
    (glideEquiv L).symm X = glideInv L X := rfl

/-! ## Group-level packaging of the two independent translations -/

noncomputable def transverseTranslationHom :
    Multiplicative ℝ →* Equiv.Perm CylinderPoint where
  toFun a := transverseTranslationEquiv a.toAdd
  map_one' := by
    rw [Equiv.Perm.one_def]
    apply Equiv.ext
    intro X
    simp [transverseTranslationEquiv, transverseTranslation]
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro X
    change transverseTranslationEquiv (a.toAdd + b.toAdd) X =
      (transverseTranslationEquiv a.toAdd *
        transverseTranslationEquiv b.toAdd) X
    rw [Equiv.Perm.mul_apply]
    change transverseTranslation (a.toAdd + b.toAdd) X =
      transverseTranslation a.toAdd (transverseTranslation b.toAdd X)
    simpa [add_comm] using
      (transverseTranslation_add b.toAdd a.toAdd X).symm

noncomputable def cylinderTranslationHom :
    Multiplicative ℝ →* Equiv.Perm CylinderPoint where
  toFun L := cylinderTranslationEquiv L.toAdd
  map_one' := by
    rw [Equiv.Perm.one_def]
    apply Equiv.ext
    intro X
    simp [cylinderTranslationEquiv, cylinderTranslation]
  map_mul' := by
    intro L M
    apply Equiv.ext
    intro X
    change cylinderTranslationEquiv (L.toAdd + M.toAdd) X =
      (cylinderTranslationEquiv L.toAdd *
        cylinderTranslationEquiv M.toAdd) X
    rw [Equiv.Perm.mul_apply]
    change cylinderTranslation (L.toAdd + M.toAdd) X =
      cylinderTranslation L.toAdd (cylinderTranslation M.toAdd X)
    simpa [add_comm] using
      (cylinderTranslation_add M.toAdd L.toAdd X).symm

theorem glideEquiv_square (L : ℝ) :
    glideEquiv L * glideEquiv L = cylinderTranslationEquiv L := by
  apply Equiv.ext
  intro X
  change glide L (glide L X) = cylinderTranslation L X
  exact glide_comp_glide L X

/-- The glide reverses the transverse translation direction. -/
theorem glide_conjugates_transverseTranslation
    (L a : ℝ) (X : CylinderPoint) :
    glide L (transverseTranslation a (glideInv L X)) =
      transverseTranslation (-a) X := by
  rcases X with ⟨x, t⟩
  simp [glide, glideInv, transverseTranslation]
  ring

theorem glideEquiv_conjugates_transverseTranslationEquiv
    (L a : ℝ) :
    glideEquiv L * transverseTranslationEquiv a * (glideEquiv L).symm =
      transverseTranslationEquiv (-a) := by
  apply Equiv.ext
  intro X
  change glide L (transverseTranslation a (glideInv L X)) =
    transverseTranslation (-a) X
  exact glide_conjugates_transverseTranslation L a X

/-! ## A direct one-step Klein sewing relation -/

theorem kleinSewing_step (L : ℝ) (x t : ℝ) :
    glide L (x, t) = (-x, t + L / 2) := rfl

theorem kleinSewing_period_step (L : ℝ) (x t : ℝ) :
    glide L (glide L (x, t)) = (x, t + L) := by
  simpa [cylinderTranslation] using glide_comp_glide L (x, t)

end InfoGeometry.Arithmetic.ZetaLogCylinderKleinGlide
