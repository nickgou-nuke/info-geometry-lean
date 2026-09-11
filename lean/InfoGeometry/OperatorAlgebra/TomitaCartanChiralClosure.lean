/-
InfoGeometry/OperatorAlgebra/TomitaCartanChiralClosure.lean

Cartan dynamics with modular chiral mirroring.

This module composes two previously separated mechanisms:

* noncompact Cartan dynamics reaches the Tomita algebra/commutant overlap and
  therefore maps to an isotropic doubled-Krein carrier vector;
* a modular mirror with `J chi = - chi J` swaps the left and right chiral
  projectors.

The resulting theorem is the intended CPT/noncompact branch:

  noncompact Cartan flow + Tomita mirror + chiral sign
    => isotropic boundary data with left/right chirality exchanged.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.TomitaCartanDynamics
import InfoGeometry.OperatorAlgebra.ModularChiralMirror

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TomitaCartanSplit

open InfoGeometry.OperatorAlgebra.ModularChiralMirror

universe uGen uOp uH

/--
A bundled noncompact Cartan/CPT branch.

The field `boundary_eq_J_conj` is the model-specific statement that the
Cartan-flow boundary representative is the Tomita/CPT mirror `J x J`.
The general Tomita-Cartan dynamics file proves isotropy after the boundary is
reached; the chiral mirror file proves that `J` swaps `P_left` and `P_right`.
-/
structure TomitaCartanChiralKreinDynamics
    (Gen : Type uGen)
    (Op : Type uOp) [Ring Op] [Algebra ℝ Op]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Noncompact Cartan flow reaches overlap and maps to a Krein-isotropic carrier. -/
  cartanKrein : TomitaCartanKreinDynamics Gen Op H

  /-- Modular/CPT mirror that flips the chiral grading. -/
  chiralMirror : ModularChiralMirror.ModularChiralMirrorDatum Op

  /-- The noncompact boundary hit is the Tomita/CPT conjugate `J x J`. -/
  boundary_eq_J_conj :
    ∀ {X : Gen} {x : Op},
      cartanKrein.dynamics.parity X = CartanParity.noncompact →
        cartanKrein.hit X x =
          chiralMirror.J * x * chiralMirror.J

namespace TomitaCartanChiralKreinDynamics

variable
    {Gen : Type uGen}
    {Op : Type uOp} [Ring Op] [Algebra ℝ Op]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (W : TomitaCartanChiralKreinDynamics Gen Op H)

/-- The Cartan-flow boundary representative. -/
def hit
    (X : Gen) (x : Op) : Op :=
  W.cartanKrein.hit X x

/-- Left support with respect to the chiral projector. -/
def IsLeftSupported
    (x : Op) : Prop :=
  W.chiralMirror.P_left * x = x

/-- Right support with respect to the chiral projector. -/
def IsRightSupported
    (x : Op) : Prop :=
  W.chiralMirror.P_right * x = x

/--
The noncompact Cartan/CPT boundary hit is isotropic in the doubled Krein
carrier.
-/
theorem noncompact_hit_isotropic
    {X : Gen} {x : Op}
    (hX : W.cartanKrein.dynamics.parity X = CartanParity.noncompact) :
    doubledKreinForm
        (W.cartanKrein.bridge.carrierReadout (W.hit X x))
        (W.cartanKrein.bridge.carrierReadout (W.hit X x)) = 0 := by
  exact W.cartanKrein.noncompact_generates_isotropic hX

/--
If the incoming operator is left-supported, the noncompact Tomita/CPT boundary
hit is right-supported.
-/
theorem noncompact_left_supported_hit_is_right_supported
    {X : Gen} {x : Op}
    (hX : W.cartanKrein.dynamics.parity X = CartanParity.noncompact)
    (hx : W.IsLeftSupported x) :
    W.IsRightSupported (W.hit X x) := by
  dsimp [IsRightSupported, hit]
  rw [W.boundary_eq_J_conj hX]
  calc
    W.chiralMirror.P_right *
        (W.chiralMirror.J * x * W.chiralMirror.J)
        = (W.chiralMirror.P_right * W.chiralMirror.J) * x * W.chiralMirror.J := by
            simp [mul_assoc]
    _ = (W.chiralMirror.J * W.chiralMirror.P_left) * x * W.chiralMirror.J := by
            rw [← W.chiralMirror.J_mul_P_left_eq_P_right_mul_J]
    _ = W.chiralMirror.J * (W.chiralMirror.P_left * x) * W.chiralMirror.J := by
            simp [mul_assoc]
    _ = W.chiralMirror.J * x * W.chiralMirror.J := by
            rw [hx]

/--
If the incoming operator is right-supported, the noncompact Tomita/CPT boundary
hit is left-supported.
-/
theorem noncompact_right_supported_hit_is_left_supported
    {X : Gen} {x : Op}
    (hX : W.cartanKrein.dynamics.parity X = CartanParity.noncompact)
    (hx : W.IsRightSupported x) :
    W.IsLeftSupported (W.hit X x) := by
  dsimp [IsLeftSupported, hit]
  rw [W.boundary_eq_J_conj hX]
  calc
    W.chiralMirror.P_left *
        (W.chiralMirror.J * x * W.chiralMirror.J)
        = (W.chiralMirror.P_left * W.chiralMirror.J) * x * W.chiralMirror.J := by
            simp [mul_assoc]
    _ = (W.chiralMirror.J * W.chiralMirror.P_right) * x * W.chiralMirror.J := by
            rw [← W.chiralMirror.J_mul_P_right_eq_P_left_mul_J]
    _ = W.chiralMirror.J * (W.chiralMirror.P_right * x) * W.chiralMirror.J := by
            simp [mul_assoc]
    _ = W.chiralMirror.J * x * W.chiralMirror.J := by
            rw [hx]

end TomitaCartanChiralKreinDynamics

end InfoGeometry.OperatorAlgebra.TomitaCartanSplit
