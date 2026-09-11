import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorValuedCliffordJones

/-!
# Finite loxodromic mode readout

This is the algebraic replacement for an exponential mode formula.  The two
axes are operators in a possibly noncommutative algebra.  Their commuting
joint projectors therefore give a finite spectral readout for every polynomial
of degree at most one in each axis.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorLoxodromicFiniteReadout

open InfoGeometry.Optics.OperatorValuedCliffordJones

variable {B : Type*} [Ring B] [Algebra ℂ B]

private def sign (b : Bool) : ℂ := if b then 1 else -1

private theorem involution_mul_Pleft
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : InfoGeometry.OperatorAlgebra.ChiralInvolution Op) :
    C.chi * C.Pleft = C.Pleft := by
  dsimp [InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft]
  rw [mul_smul_comm]
  congr 1
  noncomm_ring [C.chi_sq]

private theorem involution_mul_Pright
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (C : InfoGeometry.OperatorAlgebra.ChiralInvolution Op) :
    C.chi * C.Pright = -C.Pright := by
  dsimp [InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright]
  rw [mul_smul_comm]
  calc
    (1 / 2 : ℝ) • (C.chi * ((1 : Op) - C.chi)) =
        (1 / 2 : ℝ) • (-(1 - C.chi)) := by
      congr 1
      noncomm_ring [C.chi_sq]
    _ = -((1 / 2 : ℝ) • ((1 : Op) - C.chi)) := by
      exact smul_neg (1 / 2 : ℝ) ((1 : Op) - C.chi)

private theorem hyperbolic_mul_Pleft (L : LoxodromicAxes B) :
    L.hyperbolic * L.hyperbolicChiral.Pleft = L.hyperbolicChiral.Pleft := by
  change L.hyperbolicChiral.chi * L.hyperbolicChiral.Pleft = _
  exact involution_mul_Pleft L.hyperbolicChiral

private theorem hyperbolic_mul_Pright (L : LoxodromicAxes B) :
    L.hyperbolic * L.hyperbolicChiral.Pright = -L.hyperbolicChiral.Pright := by
  change L.hyperbolicChiral.chi * L.hyperbolicChiral.Pright = _
  exact involution_mul_Pright L.hyperbolicChiral

private theorem elliptic_mul_Pleft (L : LoxodromicAxes B) :
    L.ellipticInvolution * L.ellipticChiral.Pleft = L.ellipticChiral.Pleft := by
  change L.ellipticChiral.chi * L.ellipticChiral.Pleft = _
  exact involution_mul_Pleft L.ellipticChiral

private theorem elliptic_mul_Pright (L : LoxodromicAxes B) :
    L.ellipticInvolution * L.ellipticChiral.Pright = -L.ellipticChiral.Pright := by
  change L.ellipticChiral.chi * L.ellipticChiral.Pright = _
  exact involution_mul_Pright L.ellipticChiral

private theorem elliptic_mul_hyperbolic (L : LoxodromicAxes B) :
    L.ellipticInvolution * L.hyperbolic =
      L.hyperbolic * L.ellipticInvolution := by
  exact L.hyperbolic_commutes_ellipticInvolution.symm

private theorem elliptic_mul_hyperbolicPleft (L : LoxodromicAxes B) :
    L.ellipticInvolution * L.hyperbolicChiral.Pleft =
      L.hyperbolicChiral.Pleft * L.ellipticInvolution := by
  dsimp [InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h : L.ellipticInvolution * L.hyperbolicChiral.chi =
      L.hyperbolicChiral.chi * L.ellipticInvolution := by
    change L.ellipticInvolution * L.hyperbolic =
      L.hyperbolic * L.ellipticInvolution
    exact L.hyperbolic_commutes_ellipticInvolution.symm
  noncomm_ring [h]

private theorem elliptic_mul_hyperbolicPright (L : LoxodromicAxes B) :
    L.ellipticInvolution * L.hyperbolicChiral.Pright =
      L.hyperbolicChiral.Pright * L.ellipticInvolution := by
  dsimp [InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h : L.ellipticInvolution * L.hyperbolicChiral.chi =
      L.hyperbolicChiral.chi * L.ellipticInvolution := by
    change L.ellipticInvolution * L.hyperbolic =
      L.hyperbolic * L.ellipticInvolution
    exact L.hyperbolic_commutes_ellipticInvolution.symm
  noncomm_ring [h]

/-- The degree-one-in-each-axis loxodromic operator polynomial. -/
def modePolynomial (L : LoxodromicAxes B) (α β γ δ : ℂ) : B :=
  α • (1 : B) + β • L.hyperbolic +
    γ • L.ellipticInvolution + δ • (L.hyperbolic * L.ellipticInvolution)

private theorem hyperbolic_mul_projector
    (L : LoxodromicAxes B) (hSign cSign : Bool) :
    L.hyperbolic * L.jointProjector hSign cSign =
      sign hSign • L.jointProjector hSign cSign := by
  unfold LoxodromicAxes.jointProjector
  unfold SheetWittCircularBasis.CommutingInvolutions.jointProjector
  cases hSign <;> cases cSign <;>
    dsimp [SheetWittCircularBasis.choose,
      LoxodromicAxes.commutingInvolutions,
      SheetWittCircularBasis.CommutingInvolutions.hyperbolicInvolution,
      SheetWittCircularBasis.CommutingInvolutions.circularInvolution,
      sign]
  · change L.hyperbolic * (L.hyperbolicChiral.Pright *
      L.ellipticChiral.Pright) =
      (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pright)
    calc
      _ = (L.hyperbolic * L.hyperbolicChiral.Pright) *
          L.ellipticChiral.Pright := by rw [← mul_assoc]
      _ = (-L.hyperbolicChiral.Pright) * L.ellipticChiral.Pright := by
        rw [hyperbolic_mul_Pright L]
      _ = -(L.hyperbolicChiral.Pright * L.ellipticChiral.Pright) := by rw [neg_mul]
      _ = (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pright) := by simp
  · change L.hyperbolic * (L.hyperbolicChiral.Pright *
      L.ellipticChiral.Pleft) =
      (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft)
    calc
      _ = (L.hyperbolic * L.hyperbolicChiral.Pright) *
          L.ellipticChiral.Pleft := by rw [← mul_assoc]
      _ = (-L.hyperbolicChiral.Pright) * L.ellipticChiral.Pleft := by
        rw [hyperbolic_mul_Pright L]
      _ = -(L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft) := by rw [neg_mul]
      _ = (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft) := by simp
  · change L.hyperbolic * (L.hyperbolicChiral.Pleft *
      L.ellipticChiral.Pright) =
      (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright)
    calc
      _ = (L.hyperbolic * L.hyperbolicChiral.Pleft) *
          L.ellipticChiral.Pright := by rw [← mul_assoc]
      _ = L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright := by
        rw [hyperbolic_mul_Pleft L]
      _ = (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright) := by simp
  · change L.hyperbolic * (L.hyperbolicChiral.Pleft *
      L.ellipticChiral.Pleft) =
      (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft)
    calc
      _ = (L.hyperbolic * L.hyperbolicChiral.Pleft) *
          L.ellipticChiral.Pleft := by rw [← mul_assoc]
      _ = L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft := by
        rw [hyperbolic_mul_Pleft L]
      _ = (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft) := by simp

private theorem elliptic_mul_projector
    (L : LoxodromicAxes B) (hSign cSign : Bool) :
    L.ellipticInvolution * L.jointProjector hSign cSign =
      sign cSign • L.jointProjector hSign cSign := by
  unfold LoxodromicAxes.jointProjector
  unfold SheetWittCircularBasis.CommutingInvolutions.jointProjector
  cases hSign <;> cases cSign <;>
    dsimp [SheetWittCircularBasis.choose,
      LoxodromicAxes.commutingInvolutions,
      SheetWittCircularBasis.CommutingInvolutions.hyperbolicInvolution,
      SheetWittCircularBasis.CommutingInvolutions.circularInvolution,
      sign]
  · change L.ellipticInvolution * (L.hyperbolicChiral.Pright *
      L.ellipticChiral.Pright) =
      (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pright)
    calc
      _ = (L.ellipticInvolution * L.hyperbolicChiral.Pright) *
          L.ellipticChiral.Pright := by rw [← mul_assoc]
      _ = (L.hyperbolicChiral.Pright * L.ellipticInvolution) *
          L.ellipticChiral.Pright := by
        rw [elliptic_mul_hyperbolicPright L]
      _ = L.hyperbolicChiral.Pright *
          (L.ellipticInvolution * L.ellipticChiral.Pright) := by rw [mul_assoc]
      _ = L.hyperbolicChiral.Pright * (-L.ellipticChiral.Pright) := by
        rw [elliptic_mul_Pright L]
      _ = -(L.hyperbolicChiral.Pright * L.ellipticChiral.Pright) := by rw [mul_neg]
      _ = (-1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pright) := by simp
  · change L.ellipticInvolution * (L.hyperbolicChiral.Pright *
      L.ellipticChiral.Pleft) =
      (1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft)
    calc
      _ = (L.ellipticInvolution * L.hyperbolicChiral.Pright) *
          L.ellipticChiral.Pleft := by rw [← mul_assoc]
      _ = (L.hyperbolicChiral.Pright * L.ellipticInvolution) *
          L.ellipticChiral.Pleft := by rw [elliptic_mul_hyperbolicPright L]
      _ = L.hyperbolicChiral.Pright *
          (L.ellipticInvolution * L.ellipticChiral.Pleft) := by rw [mul_assoc]
      _ = L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft := by
        rw [elliptic_mul_Pleft L]
      _ = (1 : ℂ) • (L.hyperbolicChiral.Pright * L.ellipticChiral.Pleft) := by simp
  · change L.ellipticInvolution * (L.hyperbolicChiral.Pleft *
      L.ellipticChiral.Pright) =
      (-1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright)
    calc
      _ = (L.ellipticInvolution * L.hyperbolicChiral.Pleft) *
          L.ellipticChiral.Pright := by rw [← mul_assoc]
      _ = (L.hyperbolicChiral.Pleft * L.ellipticInvolution) *
          L.ellipticChiral.Pright := by rw [elliptic_mul_hyperbolicPleft L]
      _ = L.hyperbolicChiral.Pleft *
          (L.ellipticInvolution * L.ellipticChiral.Pright) := by rw [mul_assoc]
      _ = L.hyperbolicChiral.Pleft * (-L.ellipticChiral.Pright) := by
        rw [elliptic_mul_Pright L]
      _ = -(L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright) := by rw [mul_neg]
      _ = (-1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pright) := by simp
  · change L.ellipticInvolution * (L.hyperbolicChiral.Pleft *
      L.ellipticChiral.Pleft) =
      (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft)
    calc
      _ = (L.ellipticInvolution * L.hyperbolicChiral.Pleft) *
          L.ellipticChiral.Pleft := by rw [← mul_assoc]
      _ = (L.hyperbolicChiral.Pleft * L.ellipticInvolution) *
          L.ellipticChiral.Pleft := by rw [elliptic_mul_hyperbolicPleft L]
      _ = L.hyperbolicChiral.Pleft *
          (L.ellipticInvolution * L.ellipticChiral.Pleft) := by rw [mul_assoc]
      _ = L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft := by
        rw [elliptic_mul_Pleft L]
      _ = (1 : ℂ) • (L.hyperbolicChiral.Pleft * L.ellipticChiral.Pleft) := by simp

theorem modePolynomial_mul_jointProjector
    (L : LoxodromicAxes B) (α β γ δ : ℂ) (hSign cSign : Bool) :
    modePolynomial L α β γ δ * L.jointProjector hSign cSign =
      (α + sign hSign * β + sign cSign * γ +
        (sign hSign * sign cSign) * δ) •
        L.jointProjector hSign cSign := by
  have hH := hyperbolic_mul_projector L hSign cSign
  have hC := elliptic_mul_projector L hSign cSign
  have hHC : L.hyperbolic * L.ellipticInvolution *
      L.jointProjector hSign cSign =
      (sign hSign * sign cSign) • L.jointProjector hSign cSign := by
    calc
      L.hyperbolic * L.ellipticInvolution * L.jointProjector hSign cSign =
          L.hyperbolic * (L.ellipticInvolution *
            L.jointProjector hSign cSign) := by rw [mul_assoc]
      _ = L.hyperbolic * (sign cSign • L.jointProjector hSign cSign) := by rw [hC]
      _ = sign cSign • (L.hyperbolic * L.jointProjector hSign cSign) := by
        rw [mul_smul_comm]
      _ = sign cSign • (sign hSign • L.jointProjector hSign cSign) := by rw [hH]
      _ = (sign hSign * sign cSign) • L.jointProjector hSign cSign := by
        rw [smul_smul]
        congr 1
        ring
  unfold modePolynomial
  calc
    (α • (1 : B) + β • L.hyperbolic + γ • L.ellipticInvolution +
        δ • (L.hyperbolic * L.ellipticInvolution)) *
        L.jointProjector hSign cSign =
      (α • (1 : B)) * L.jointProjector hSign cSign +
        (β • L.hyperbolic) * L.jointProjector hSign cSign +
        (γ • L.ellipticInvolution) * L.jointProjector hSign cSign +
        (δ • (L.hyperbolic * L.ellipticInvolution)) *
          L.jointProjector hSign cSign := by noncomm_ring
    _ = α • L.jointProjector hSign cSign +
        β • (L.hyperbolic * L.jointProjector hSign cSign) +
        γ • (L.ellipticInvolution * L.jointProjector hSign cSign) +
        δ • ((L.hyperbolic * L.ellipticInvolution) *
          L.jointProjector hSign cSign) := by
      simp only [smul_mul_assoc, one_mul]
    _ = (α + sign hSign * β + sign cSign * γ +
        (sign hSign * sign cSign) * δ) •
        L.jointProjector hSign cSign := by
      rw [hH, hC, hHC]
      module

theorem modePolynomial_mul_jointProjectors_sum
    (L : LoxodromicAxes B) (α β γ δ : ℂ) :
    modePolynomial L α β γ δ *
        (L.jointProjector true true + L.jointProjector true false +
          L.jointProjector false true + L.jointProjector false false) =
      modePolynomial L α β γ δ := by
  rw [L.jointProjectors_sum, mul_one]

end InfoGeometry.Optics.OperatorLoxodromicFiniteReadout
