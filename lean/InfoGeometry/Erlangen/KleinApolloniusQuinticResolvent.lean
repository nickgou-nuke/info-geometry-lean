/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
import InfoGeometry.Canonical.ApolloniusHomogeneousCoordinatesBridge

/-!
# Apollonius Chart Specialization of the Klein Quintic Quotient Resolvent

The Apollonius owner uses homogeneous coordinates `[t : 1]`, whereas the
quintic interpolation theorem uses the affine chart `(1, t)`. This file makes
that coordinate swap explicit and specializes the existing quotient/orbit
resolvent theorem. It does not identify this finite five-coordinate object
with the Cantor double-cylinder operator colimit.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinApolloniusQuinticResolvent

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

/-- Convert the Apollonius homogeneous point `[t : 1]` to the swapped
binary-form chart `(1, t)` used by the quintic orbit evaluation. -/
def apolloniusBinaryQuinticPoint (ξ θ : ℝ) : ℂ × ℂ :=
  (1, projectiveRatio (apolloniusHomogeneousCoord ξ θ))

@[simp] theorem apolloniusBinaryQuinticPoint_apply (ξ θ : ℝ) :
    apolloniusBinaryQuinticPoint ξ θ =
      (1, Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) := by
  rw [apolloniusBinaryQuinticPoint, projectiveRatio_apolloniusHomogeneousCoord]

/-- The Apollonius coordinate supplies the nonzero affine parameter required
by the five-node interpolation and quotient-equivalence theorem. -/
theorem apollonius_parameter_ne_zero (ξ θ : ℝ) :
    projectiveRatio (apolloniusHomogeneousCoord ξ θ) ≠ 0 := by
  rw [projectiveRatio_apolloniusHomogeneousCoord]
  exact Complex.exp_ne_zero _

/-- The coefficient-quotient class at an Apollonius point is read out by the
five signed Klein orbit evaluations, with no choice of representative. -/
theorem apollonius_quotient_equiv_apply_mk
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    (binaryQuinticAffineOrbitQuotientEquiv
      (apollonius_parameter_ne_zero ξ θ) (Submodule.Quotient.mk v) :
        BrioschiRootCoordinateSpace) =
      binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ) v := by
  exact binaryQuinticAffineOrbitQuotientEquiv_apply_mk
    (apollonius_parameter_ne_zero ξ θ) v

/-- At an Apollonius projective point, the coefficient-quotient action is
identified with the signed five-coordinate action by the actual orbit
evaluation equivalence. This is the representation-level statement behind
the squared evaluation-resolvent identity below. -/
theorem apollonius_quotient_equiv_intertwines
    (ξ θ : ℝ)
    (q : BinaryQuinticCoefficientSpace ⧸
      LinearMap.ker
        (binaryQuinticOrbitEvaluation (apolloniusBinaryQuinticPoint ξ θ))) :
    binaryQuinticAffineOrbitQuotientEquiv
        (apollonius_parameter_ne_zero ξ θ)
        (binaryQuinticOrbitQuotientGenerator
          (apolloniusBinaryQuinticPoint ξ θ) q) =
      binaryQuinticSignedCycle
        (binaryQuinticAffineOrbitQuotientEquiv
          (apollonius_parameter_ne_zero ξ θ) q) := by
  exact binaryQuinticAffineOrbitQuotientEquiv_intertwines
    (apollonius_parameter_ne_zero ξ θ) q

/-- **Apollonius-specialized representation-to-resolvent identification.**
The degree-five polynomial formed from squared orbit coordinates is exactly
the orbit polynomial of the quotient class of the source-ordered quintic at
the Apollonius projective point. The square removes the signed central
spinor character, as in the underlying Klein resolvent owner. -/
theorem apollonius_evaluation_resolvent_eq_quotient_orbit_polynomial
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticEvaluationResolvent v (apolloniusBinaryQuinticPoint ξ θ) =
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C
        (((binaryQuinticAffineOrbitQuotientEquiv
          (apollonius_parameter_ne_zero ξ θ) (Submodule.Quotient.mk v) :
            BrioschiRootCoordinateSpace) k) ^ 2)) := by
  simpa [apolloniusBinaryQuinticPoint] using
    (binaryQuinticEvaluationResolvent_eq_affine_quotient_orbit_polynomial
      (apollonius_parameter_ne_zero ξ θ) v)

/-- The Apollonius-specialized evaluation resolvent is invariant under the
binary quintic order-ten generator; its central sign disappears in the
degree-five orbit polynomial. -/
theorem apollonius_evaluation_resolvent_generator_invariant
    (ξ θ : ℝ) (v : BinaryQuinticCoefficientSpace) :
    binaryQuinticEvaluationResolvent (binaryQuinticGenerator v)
        (apolloniusBinaryQuinticPoint ξ θ) =
      binaryQuinticEvaluationResolvent v (apolloniusBinaryQuinticPoint ξ θ) := by
  exact binaryQuinticEvaluationResolvent_invariant v
    (apolloniusBinaryQuinticPoint ξ θ)

/-- At an Apollonius point where the Klein edge invariant is nonzero and the
five classical orbit roots are distinct, some source-ordered binary quintic
has evaluation resolvent equal to the displayed Brioschi quintic. The
existence remains noncanonical, as in the underlying interpolation theorem. -/
theorem exists_apollonius_binary_quintic_with_brioschi_resolvent
    (ξ θ : ℝ)
    (hT : kleinIcosahedralEdgeT
      (apolloniusBinaryQuinticPoint ξ θ).1
      (apolloniusBinaryQuinticPoint ξ θ).2 ≠ 0)
    (hinj : Function.Injective
      (kleinBrioschiRootTuple (apolloniusBinaryQuinticPoint ξ θ))) :
    ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticEvaluationResolvent v (apolloniusBinaryQuinticPoint ξ θ) =
        brioschiResolvent
          (brioschiParameter
            (apolloniusBinaryQuinticPoint ξ θ).1
            (apolloniusBinaryQuinticPoint ξ θ).2) := by
  have hpoint := apolloniusBinaryQuinticPoint_apply ξ θ
  rw [hpoint] at hT hinj ⊢
  exact exists_binaryQuinticEvaluationResolvent_eq_brioschiResolvent
    (1, Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)))
    (kleinOrderFiveAffineOrbit_first_ne_zero _)
    (kleinOrderFiveAffineOrbit_nodes_injective (Complex.exp_ne_zero _))
    hT hinj

/-- Every nonzero affine parameter in the Brioschi chart is represented by
the Apollonius coordinates `exp (ξ + I θ)`. This is the exact chart coverage
needed to transport existence results to the Apollonius parameterization. -/
theorem exists_apollonius_coordinates_for_nonzero_parameter
    (t : ℂ) (ht : t ≠ 0) :
    ∃ ξ θ : ℝ, apolloniusBinaryQuinticPoint ξ θ = (1, t) := by
  let w := Complex.log t
  refine ⟨w.re, w.im, ?_⟩
  rw [apolloniusBinaryQuinticPoint_apply]
  have hdecomp : (w.re : ℂ) + Complex.I * (w.im : ℂ) = w := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hdecomp, Complex.exp_log ht]

/-- A source-ordered binary quintic exists whose five squared Klein orbit
coordinates give the Brioschi resolvent at some Apollonius point. The witness
is noncanonical, inherited from interpolation on the affine slice. -/
theorem exists_apollonius_binary_quintic_with_brioschi_evaluation_resolvent :
    ∃ ξ θ : ℝ, ∃ v : BinaryQuinticCoefficientSpace,
      binaryQuinticEvaluationResolvent v (apolloniusBinaryQuinticPoint ξ θ) =
        brioschiResolvent (brioschiParameter
          (apolloniusBinaryQuinticPoint ξ θ).1
          (apolloniusBinaryQuinticPoint ξ θ).2) := by
  obtain ⟨t, v, hT, hinj, hres⟩ :=
    exists_brioschi_evaluation_resolvent_specialization
  have ht : t ≠ 0 := by
    intro hzero
    subst t
    exact kleinBrioschiRootTuple_not_injective_degenerate hinj
  obtain ⟨ξ, θ, hpoint⟩ :=
    exists_apollonius_coordinates_for_nonzero_parameter t ht
  refine ⟨ξ, θ, v, ?_⟩
  rw [hpoint]
  exact hres

end InfoGeometry.Erlangen.KleinApolloniusQuinticResolvent
