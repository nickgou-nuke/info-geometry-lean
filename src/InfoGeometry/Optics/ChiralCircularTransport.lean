import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry
import InfoGeometry.Optics.OperatorValuedCliffordJones

/-!
# Chiral/circular transport

This module records the algebraic transport law needed by the polarization
calculus.  It is deliberately stated for the existing `OperatorialJonesTransform`
owner: conjugation preserves multiplication, so preservation of two axes implies
preservation of their joint projector.
-/

noncomputable section

namespace InfoGeometry.Optics.ChiralCircularTransport

open InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry

variable {Op : Type*} [Ring Op]

@[simp] theorem act_mul (T : OperatorialJonesTransform Op) (a b : Op) :
    T.act (a * b) = T.act a * T.act b := by
  simp [OperatorialJonesTransform.act, mul_assoc]

theorem act_joint_projector
    (T : OperatorialJonesTransform Op) (p q : Op)
    (hp : T.act p = p) (hq : T.act q = q) :
    T.act (p * q) = p * q := by
  rw [act_mul, hp, hq]

theorem act_joint_projector_of_axes
    (T : OperatorialJonesTransform Op) (p q : Op)
    (hp : T.act p = p) (hq : T.act q = q) :
    T.act p * T.act q = p * q := by
  rw [hp, hq]

@[simp] theorem act_add (T : OperatorialJonesTransform Op) (a b : Op) :
    T.act (a + b) = T.act a + T.act b := by
  simp [OperatorialJonesTransform.act, mul_add, add_mul]

@[simp] theorem act_neg (T : OperatorialJonesTransform Op) (a : Op) :
    T.act (-a) = -T.act a := by
  simp [OperatorialJonesTransform.act]

@[simp] theorem act_sub (T : OperatorialJonesTransform Op) (a b : Op) :
    T.act (a - b) = T.act a - T.act b := by
  simp [sub_eq_add_neg]

section ComplexAlgebra

variable [Algebra ℂ Op]

@[simp] theorem act_smul (T : OperatorialJonesTransform Op) (z : ℂ) (a : Op) :
    T.act (z • a) = z • T.act a := by
  simp only [OperatorialJonesTransform.act, Algebra.smul_def]
  calc
    T.U.val * ((algebraMap ℂ Op) z * a) * T.U.inv =
        ((T.U.val * (algebraMap ℂ Op) z) * a) * T.U.inv := by
          simp only [mul_assoc]
    _ = (((algebraMap ℂ Op) z * T.U.val) * a) * T.U.inv := by
          rw [Algebra.commutes]
    _ = (algebraMap ℂ Op) z * (T.U.val * a * T.U.inv) := by
          simp only [mul_assoc]

@[simp] theorem act_real_smul (T : OperatorialJonesTransform Op) (r : ℝ) (a : Op) :
    T.act (r • a) = r • T.act a := by
  change T.act ((r : ℂ) • a) = (r : ℂ) • T.act a
  exact act_smul T (r : ℂ) a

/-- Conjugation fixes the circular involution `iC` whenever it fixes `C`. -/
theorem act_ellipticInvolution_of_elliptic
    (T : OperatorialJonesTransform Op)
    (L : OperatorValuedCliffordJones.LoxodromicAxes Op)
    (hC : T.act L.elliptic = L.elliptic) :
    T.act L.ellipticInvolution = L.ellipticInvolution := by
  simp [OperatorValuedCliffordJones.LoxodromicAxes.ellipticInvolution, hC]

/--
Preservation of the hyperbolic and elliptic axes forces preservation of every
derived sheet/circular joint spectral projector.
-/
theorem act_loxodromic_jointProjector_of_axes
    (T : OperatorialJonesTransform Op)
    (L : OperatorValuedCliffordJones.LoxodromicAxes Op)
    (hH : T.act L.hyperbolic = L.hyperbolic)
    (hC : T.act L.elliptic = L.elliptic)
    (hSign cSign : Bool) :
    T.act (L.jointProjector hSign cSign) =
      L.jointProjector hSign cSign := by
  have hI : T.act L.ellipticInvolution = L.ellipticInvolution :=
    act_ellipticInvolution_of_elliptic T L hC
  unfold OperatorValuedCliffordJones.LoxodromicAxes.jointProjector
  unfold SheetWittCircularBasis.CommutingInvolutions.jointProjector
  rw [act_mul]
  cases hSign <;> cases cSign <;>
    simp [SheetWittCircularBasis.choose,
      SheetWittCircularBasis.CommutingInvolutions.hyperbolicInvolution,
      SheetWittCircularBasis.CommutingInvolutions.circularInvolution,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright,
      OperatorValuedCliffordJones.LoxodromicAxes.commutingInvolutions,
      hH, hI]

end ComplexAlgebra

end InfoGeometry.Optics.ChiralCircularTransport
