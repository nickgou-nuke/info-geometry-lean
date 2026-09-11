import InfoGeometry.AsanoRuelle.MobiusPoleBlowup
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bundled multiplicative pole-scale action

The pointwise pole dilation from `MobiusPoleBlowup` is bundled here as a
genuine action of the group of nonzero real scalars on the complex plane.
This is only an affine scale action.  It does not assert a Weyl gauge action,
compactification, or a categorical colimit.
-/

noncomputable section

namespace InfoGeometry.AsanoRuelle

open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-- The affine dilation about `p` associated to a nonzero real scalar. -/
def poleScaleEquiv (p : ℂ) (lam : ℝˣ) : Equiv.Perm ℂ where
  toFun := poleScale p (lam : ℝ)
  invFun := poleScale p ((lam : ℝ)⁻¹)
  left_inv := by
    intro z
    rw [poleScale_inv]
    exact Units.ne_zero lam
  right_inv := by
    intro z
    have h := poleScale_inv p z (lam := (lam : ℝ)⁻¹)
      (inv_ne_zero (Units.ne_zero lam))
    simpa using h

@[simp] theorem poleScaleEquiv_apply (p : ℂ) (lam : ℝˣ) (z : ℂ) :
    poleScaleEquiv p lam z = poleScale p (lam : ℝ) z := rfl

theorem poleScaleEquiv_mul (p : ℂ) (lam mu : ℝˣ) :
    poleScaleEquiv p (lam * mu) =
      poleScaleEquiv p lam * poleScaleEquiv p mu := by
  ext z
  change poleScale p ((lam * mu : ℝˣ) : ℝ) z =
    poleScale p (lam : ℝ) (poleScale p (mu : ℝ) z)
  rw [poleScale_mul]
  rfl

/-- The multiplicative pole-scale action as a monoid homomorphism. -/
def poleScaleAction (p : ℂ) : ℝˣ →* Equiv.Perm ℂ where
  toFun := poleScaleEquiv p
  map_one' := by
    ext z
    simp [poleScaleEquiv, poleScale]
  map_mul' lam mu := by
    exact poleScaleEquiv_mul p lam mu

@[simp] theorem poleScaleAction_apply (p : ℂ) (lam : ℝˣ) (z : ℂ) :
    poleScaleAction p lam z = poleScale p (lam : ℝ) z := rfl

theorem poleScaleAction_mul_apply (p : ℂ) (lam mu : ℝˣ) (z : ℂ) :
    poleScaleAction p (lam * mu) z =
      poleScaleAction p lam (poleScaleAction p mu z) := by
  change poleScaleEquiv p (lam * mu) z =
    poleScaleEquiv p lam (poleScaleEquiv p mu z)
  rw [poleScaleEquiv_mul]
  rfl

@[simp] theorem poleScaleAction_one_apply (p : ℂ) (z : ℂ) :
    poleScaleAction p 1 z = z := by
  simp [poleScaleAction, poleScaleEquiv, poleScale]

theorem poleScaleAction_inv_apply (p : ℂ) (lam : ℝˣ) (z : ℂ) :
    poleScaleAction p lam⁻¹ (poleScaleAction p lam z) = z := by
  change poleScaleEquiv p lam⁻¹ (poleScaleEquiv p lam z) = z
  have hinv : poleScaleEquiv p lam⁻¹ = (poleScaleEquiv p lam).symm := by
    ext w
    simp [poleScaleEquiv, poleScale]
  rw [hinv]
  exact (poleScaleEquiv p lam).left_inv z

/- The bundled action agrees with the pole-centered direction coordinates. -/
theorem poleScaleAction_polePoint (C D : ℂ) (lam : ℝˣ) (v : ℂ) :
    poleScaleAction (-(C / D)) lam (-(C / D) + v) =
      poleScalePoint C D (lam : ℝ) v := by
  simp [poleScaleAction, poleScaleEquiv, poleScale, poleScalePoint]

/- The bundled action exposes the inverse-scale Möbius readout. -/
theorem mobiusPolePath_scaleAction_inverse_scale
    (A B C D : ℂ) (lam : ℝˣ) (v : ℂ)
    (hD : D ≠ 0) (hv : v ≠ 0) :
    mobiusPolePath A B C D ((lam : ℂ) * v) =
      (lam : ℂ)⁻¹ *
          (-(A * D - B * C) / (D ^ 2 * v)) - B / D := by
  have hlam : ((lam : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero lam
  exact mobiusPolePath_scale_transport A B C D
    (lam : ℝ) v hD hlam hv

end InfoGeometry.AsanoRuelle
