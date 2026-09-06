import Mathlib
import InfoGeometry.Canonical.TwelveFoldArithmeticNative
import InfoGeometry.Physics.NuclearOperatorSchurComplement
import InfoGeometry.Physics.QCDExceptionalArtinBridge
import InfoGeometry.Physics.QCDTrialityStructuralBridge
import InfoGeometry.Physics.QCDColorCARAnyonBridge

/-!
# Twelvefold / Schur / triality structural bridge

This module connects theorem owners that already exist on distinct carriers:

* a generic commuting order-two/order-three product closes after six steps;
* the repository-owned `masterTwelve` operator has exact order twelve, with
  explicit order-two and order-three projections;
* the `G₂/I₂(6)` Artin spin lift has sixth power `-1` and twelfth power `1`;
* the noncommutative Schur operator at zero light block is exactly
  `-(V * Binv * W)` and is invariant under simultaneous sign reflection;
* the finite Furey occupation readout has denominator three;
* the finite triality carrier closes after three steps.

These are algebraic statements.  No theorem here identifies one abstract step
with a physical `2π` rotation, proves a minimal `12π` period, constructs PMNS
mixing, identifies a neutrino carrier, or proves a physical seesaw model.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDTwelveFoldSchurTrialityBridge

open InfoGeometry.Canonical.TwelveFoldExplicitOperators
open InfoGeometry.Canonical.TwelveFoldArithmeticNative
open InfoGeometry.Physics.NuclearOperatorSchurComplement
open InfoGeometry.Physics.QCDExceptionalArtinBridge
open InfoGeometry.Physics.QCDTrialityStructuralBridge
open InfoGeometry.Physics.QCDColorCARAnyonBridge
open InfoGeometry.Exceptional.ArtinOperators

/-- Pure group-theoretic `lcm(2,3)` closure: commuting order-two/order-three
components have product sixth power equal to the identity.

This theorem asserts closure at six; it does not assert that six is the exact
order without additional nondegeneracy hypotheses. -/
theorem commuting_z2_z3_product_pow_six
    {M : Type*} [Monoid M] (p q : M)
    (hpq : Commute p q)
    (hp2 : p ^ 2 = 1)
    (hq3 : q ^ 3 = 1) :
    (p * q) ^ 6 = 1 := by
  have hp6 : p ^ 6 = 1 := by
    calc
      p ^ 6 = (p ^ 2) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [hp2]; simp
  have hq6 : q ^ 6 = 1 := by
    calc
      q ^ 6 = (q ^ 3) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hq3]; simp
  rw [hpq.mul_pow, hp6, hq6, one_mul]

/-- The elementary arithmetic shadow of the product closure. -/
theorem z2_z3_lcm_eq_six : Nat.lcm 2 3 = 6 := by
  norm_num

/-- Parallel exact twelvefold closure: the concrete repository operator has
order twelve, while the independent `G₂/I₂(6)` spin lift closes projectively at
six and linearly at twelve.  The carriers are not identified. -/
theorem artin_native_twelvefold_packet (rho : G2SpinOperatorLift) :
    orderOf masterTwelve = 12 ∧
      (rho.Bs * rho.Bl) ^ 6 = -1 ∧
      (rho.Bs * rho.Bl) ^ 12 = 1 :=
  ⟨masterTwelve_order_exact,
    rho.coxeter_pow_six_eq_neg_one,
    rho.spin_coxeter_pow_twelve⟩

/-- Zero-light-block Schur elimination has the exact seesaw-shaped algebraic
form `-V * Binv * W` (with the stated parenthesization) and is even under the
simultaneous sign reflection of the two transition channels. -/
theorem zero_block_schur_packet
    {A : Type*} [Ring A] (V W Binv : A) :
    effectiveOperator 0 V W Binv = -(V * Binv * W) ∧
      effectiveOperator 0 (-V) (-W) Binv =
        effectiveOperator 0 V W Binv := by
  constructor
  · simp [effectiveOperator]
  · exact effectiveOperator_reflection 0 V W Binv

/-- Capstone structural packet combining the neutral Schur elimination with the
independent exact twelvefold/Artin closure. -/
theorem schur_artin_twelvefold_packet
    {A : Type*} [Ring A]
    (V W Binv : A) (rho : G2SpinOperatorLift) :
    effectiveOperator 0 V W Binv = -(V * Binv * W) ∧
      effectiveOperator 0 (-V) (-W) Binv =
        effectiveOperator 0 V W Binv ∧
      (rho.Bs * rho.Bl) ^ 6 = -1 ∧
      (rho.Bs * rho.Bl) ^ 12 = 1 ∧
      orderOf masterTwelve = 12 := by
  rcases zero_block_schur_packet V W Binv with ⟨hschur, hreflect⟩
  exact ⟨hschur, hreflect,
    rho.coxeter_pow_six_eq_neg_one,
    rho.spin_coxeter_pow_twelve,
    masterTwelve_order_exact⟩

end InfoGeometry.Physics.QCDTwelveFoldSchurTrialityBridge

end noncomputable section
