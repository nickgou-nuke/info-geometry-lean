/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionRegularEllipticOperators
import InfoGeometry.Canonical.SplitOctonionRegularProjectors

/-!
# Elliptic and hyperbolic operators on the full split-octonion carrier

The existing quaternion-pair multiplication gives anticommutation of its actual
left regular operators. Their composition is an involution when the two axes
are normalized, and the elliptic operator interchanges the hyperbolic
projectors. These are identities in `Module.End ℝ SplitOctonion`.

Composition is kept distinct from multiplication of split-octonion elements:
the difference is the negative of the existing associator. A concrete `i, ell, j`
witness computes the sign and proves that the two operators differ.
-/

noncomputable section

namespace SplitOctonion

/-- Actual regular operators anticommute when the quaternion elliptic axis is
purely imaginary. Neither axis needs normalization for this identity. -/
theorem elliptic_hyperbolic_anticommute (g h : H) (hg : star g = -g) :
    (ellipticAxisOperator g).comp (hyperbolicAxisOperator h) =
      -(hyperbolicAxisOperator h).comp (ellipticAxisOperator g) := by
  apply LinearMap.ext
  intro z
  change I_gen g * (J_g h * z) = -(J_g h * (I_gen g * z))
  apply SplitOctonion.ext
  · simp only [mul_a, mul_b, I_gen, J_g, neg_a, zero_mul, mul_zero,
      zero_add, add_zero]
    rw [star_mul, hg, neg_mul, neg_mul, neg_neg, mul_assoc]
  · simp only [mul_a, mul_b, I_gen, J_g, neg_b, zero_mul, mul_zero,
      zero_add, add_zero]
    rw [star_mul, hg, mul_neg, mul_neg, neg_neg, mul_assoc]

/-- The opposite composition order has the opposite sign. -/
theorem hyperbolic_elliptic_anticommute (g h : H) (hg : star g = -g) :
    (hyperbolicAxisOperator h).comp (ellipticAxisOperator g) =
      -(ellipticAxisOperator g).comp (hyperbolicAxisOperator h) := by
  simpa only [neg_neg] using
    (congrArg (fun A : Module.End ℝ SplitOctonion => -A)
      (elliptic_hyperbolic_anticommute g h hg)).symm

/-- The ordered composite `S = I ∘ K` squares to the identity on all eight
real dimensions. The separate square laws are reused from their owners. -/
theorem elliptic_hyperbolic_comp_self (g h : H) (hg : star g = -g)
    (hgn : Quaternion.normSq g = 1) (hhn : Quaternion.normSq h = 1) :
    ((ellipticAxisOperator g).comp (hyperbolicAxisOperator h)).comp
        ((ellipticAxisOperator g).comp (hyperbolicAxisOperator h)) =
      (LinearMap.id : Module.End ℝ SplitOctonion) := by
  apply LinearMap.ext
  intro z
  have hKI (x : SplitOctonion) :
      hyperbolicAxisOperator h (ellipticAxisOperator g x) =
        -(ellipticAxisOperator g (hyperbolicAxisOperator h x)) :=
    LinearMap.congr_fun (hyperbolic_elliptic_anticommute g h hg) x
  have hI (x : SplitOctonion) :
      ellipticAxisOperator g (ellipticAxisOperator g x) = -x :=
    LinearMap.congr_fun (ellipticAxisOperator_comp_self g hg hgn) x
  have hK (x : SplitOctonion) :
      hyperbolicAxisOperator h (hyperbolicAxisOperator h x) = x :=
    LinearMap.congr_fun (hyperbolicAxisOperator_sq h hhn) x
  change ellipticAxisOperator g (hyperbolicAxisOperator h
    (ellipticAxisOperator g (hyperbolicAxisOperator h z))) = z
  rw [hKI, map_neg, hI, hK, neg_neg]

/-- The elliptic operator carries the existing positive hyperbolic projector
to the negative one. -/
theorem elliptic_comp_projectorPlus (g h : H) (hg : star g = -g) :
    (ellipticAxisOperator g).comp (hyperbolicProjectorPlus h) =
      (hyperbolicProjectorMinus h).comp (ellipticAxisOperator g) := by
  apply LinearMap.ext
  intro z
  have hKI : hyperbolicAxisOperator h (ellipticAxisOperator g z) =
      -(ellipticAxisOperator g (hyperbolicAxisOperator h z)) :=
    LinearMap.congr_fun (hyperbolic_elliptic_anticommute g h hg) z
  change ellipticAxisOperator g
      ((1 / 2 : ℝ) • (z + hyperbolicAxisOperator h z)) =
    (1 / 2 : ℝ) • (ellipticAxisOperator g z -
      hyperbolicAxisOperator h (ellipticAxisOperator g z))
  rw [map_smul, map_add, hKI, sub_neg_eq_add]

/-- The opposite hyperbolic projector is interchanged as well. -/
theorem elliptic_comp_projectorMinus (g h : H) (hg : star g = -g) :
    (ellipticAxisOperator g).comp (hyperbolicProjectorMinus h) =
      (hyperbolicProjectorPlus h).comp (ellipticAxisOperator g) := by
  apply LinearMap.ext
  intro z
  have hKI : hyperbolicAxisOperator h (ellipticAxisOperator g z) =
      -(ellipticAxisOperator g (hyperbolicAxisOperator h z)) :=
    LinearMap.congr_fun (hyperbolic_elliptic_anticommute g h hg) z
  change ellipticAxisOperator g
      ((1 / 2 : ℝ) • (z - hyperbolicAxisOperator h z)) =
    (1 / 2 : ℝ) • (ellipticAxisOperator g z +
      hyperbolicAxisOperator h (ellipticAxisOperator g z))
  rw [map_smul, map_sub, hKI, sub_eq_add_neg]

/-- The elliptic operator maps the `+1` eigenspace into the `-1` eigenspace. -/
theorem elliptic_maps_hyperbolic_plus_to_minus (g h : H)
    (hg : star g = -g) (z : SplitOctonion)
    (hz : hyperbolicAxisOperator h z = z) :
    hyperbolicAxisOperator h (ellipticAxisOperator g z) =
      -(ellipticAxisOperator g z) := by
  calc
    hyperbolicAxisOperator h (ellipticAxisOperator g z) =
        -(ellipticAxisOperator g (hyperbolicAxisOperator h z)) :=
      LinearMap.congr_fun (hyperbolic_elliptic_anticommute g h hg) z
    _ = -(ellipticAxisOperator g z) := by rw [hz]

/-- The elliptic operator maps the `-1` eigenspace into the `+1` eigenspace. -/
theorem elliptic_maps_hyperbolic_minus_to_plus (g h : H)
    (hg : star g = -g) (z : SplitOctonion)
    (hz : hyperbolicAxisOperator h z = -z) :
    hyperbolicAxisOperator h (ellipticAxisOperator g z) =
      ellipticAxisOperator g z := by
  calc
    hyperbolicAxisOperator h (ellipticAxisOperator g z) =
        -(ellipticAxisOperator g (hyperbolicAxisOperator h z)) :=
      LinearMap.congr_fun (hyperbolic_elliptic_anticommute g h hg) z
    _ = ellipticAxisOperator g z := by rw [hz, map_neg, neg_neg]

/-- Composition minus multiplication by the product has the negative
associator sign in the existing convention. -/
theorem elliptic_hyperbolic_defect_apply (g h : H) (z : SplitOctonion) :
    ellipticAxisOperator g (hyperbolicAxisOperator h z) -
        leftRegular (I_gen g * J_g h) z =
      -associator (I_gen g) (J_g h) z := by
  change I_gen g * (J_g h * z) - (I_gen g * J_g h) * z =
    -((I_gen g * J_g h) * z - I_gen g * (J_g h * z))
  exact (neg_sub _ _).symm

/-- A parenthesized calculation in the full quaternion-pair carrier:
`[i, ell, j] = -2 k ell`. -/
theorem associator_i_ell_j :
    associator (I_gen (⟨0, 1, 0, 0⟩ : H)) (J_g 1)
        (I_gen (⟨0, 0, 1, 0⟩ : H)) =
      J_g (⟨0, 0, 0, -2⟩ : H) := by
  apply SplitOctonion.ext <;> ext <;>
    norm_num [associator, I_gen, J_g, mul_a, mul_b, sub_a, sub_b]

/-- The corresponding operator defect is `+2 k ell`, with the opposite sign
to the associator. -/
theorem elliptic_hyperbolic_defect_i_ell_j :
    ellipticAxisOperator (⟨0, 1, 0, 0⟩ : H)
        (hyperbolicAxisOperator 1 (I_gen (⟨0, 0, 1, 0⟩ : H))) -
        leftRegular (I_gen (⟨0, 1, 0, 0⟩ : H) * J_g 1)
          (I_gen (⟨0, 0, 1, 0⟩ : H)) =
      J_g (⟨0, 0, 0, 2⟩ : H) := by
  rw [elliptic_hyperbolic_defect_apply, associator_i_ell_j]
  apply SplitOctonion.ext <;> ext <;> norm_num [J_g]

/-- The real composite operator is not left multiplication by the raw
split-octonion product, witnessed by `j`. -/
theorem elliptic_hyperbolic_composite_ne_leftRegular_product :
    (ellipticAxisOperator (⟨0, 1, 0, 0⟩ : H)).comp
        (hyperbolicAxisOperator 1) ≠
      leftRegular (I_gen (⟨0, 1, 0, 0⟩ : H) * J_g 1) := by
  intro heq
  have hz : associator (I_gen (⟨0, 1, 0, 0⟩ : H)) (J_g 1)
      (I_gen (⟨0, 0, 1, 0⟩ : H)) = 0 :=
    (leftRegular_comp_eq_iff_associator_zero
      (I_gen (⟨0, 1, 0, 0⟩ : H)) (J_g 1)).mp heq.symm _
  rw [associator_i_ell_j] at hz
  have hcomponent := congrArg (fun z : SplitOctonion => z.b.imK) hz
  norm_num [J_g] at hcomponent

end SplitOctonion
