import Mathlib.Tactic
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Exceptional.Freudenthal

/-!
# Concrete Freudenthal quartic invariant for `H3Zorn ℝ`

This module specializes the abstract Freudenthal charge space to the native
split-Albert carrier `H3Zorn ℝ` using the already verified cubic Jordan datum
`h3zornCubicJordanDatum`.

The construction keeps the cubic Jordan norm and the Freudenthal quartic
strictly distinct.  In particular, on the canonical electric embedding
`X ↦ (1,0,X,0)`, the quartic restricts to `-4 * normCubic X`.
-/

noncomputable section

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

/-- The Freudenthal charge carrier associated to the real split-Albert algebra. -/
abbrev Charge := FreudenthalCharge (H3Zorn ℝ)

/-- The concrete Freudenthal quartic obtained from the verified H3Zorn cubic datum. -/
def quarticInvariant (Q : Charge) : ℝ :=
  FreudenthalCharge.quarticInvariant h3zornCubicJordanDatum Q

/-- The concrete Freudenthal alternating pairing on split-Albert charges. -/
def symplecticForm (Q₁ Q₂ : Charge) : ℝ :=
  FreudenthalCharge.symplecticForm h3zornCubicJordanDatum Q₁ Q₂

/-- Expanded native formula for the split-Albert Freudenthal quartic. -/
theorem quarticInvariant_expanded (Q : Charge) :
    quarticInvariant Q =
      (Q.alpha * Q.beta - H3Zorn.traceBilin Q.x Q.y) ^ 2 -
        4 *
          (Q.alpha * H3Zorn.normCubic Q.x
            + Q.beta * H3Zorn.normCubic Q.y
            - H3Zorn.traceBilin
                (H3Zorn.adjointQuad Q.x)
                (H3Zorn.adjointQuad Q.y)) := by
  rfl

/-- Expanded native formula for the split-Albert Freudenthal symplectic form. -/
theorem symplecticForm_expanded (Q₁ Q₂ : Charge) :
    symplecticForm Q₁ Q₂ =
      Q₁.alpha * Q₂.beta - Q₁.beta * Q₂.alpha
        + H3Zorn.traceBilin Q₁.x Q₂.y
        - H3Zorn.traceBilin Q₁.y Q₂.x := by
  rfl

/-- The quadratic adjoint sends the additive zero to zero. -/
@[simp]
theorem adjointQuad_zero :
    H3Zorn.adjointQuad (0 : H3Zorn ℝ) = 0 := by
  simpa using
    (H3Zorn.adjointQuad_smul (R := ℝ) (0 : ℝ) (1 : H3Zorn ℝ))

/-- The split-Albert Freudenthal pairing is alternating. -/
@[simp]
theorem symplecticForm_self (Q : Charge) :
    symplecticForm Q Q = 0 := by
  exact FreudenthalCharge.symplectic_form_alternating h3zornCubicJordanDatum Q

/-- The split-Albert Freudenthal pairing is skew-symmetric. -/
theorem symplecticForm_skew (Q₁ Q₂ : Charge) :
    symplecticForm Q₂ Q₁ = -symplecticForm Q₁ Q₂ := by
  exact FreudenthalCharge.symplectic_form_skew h3zornCubicJordanDatum Q₁ Q₂

/-- Pure scalar Freudenthal charge. -/
def scalarCharge (α β : ℝ) : Charge where
  alpha := α
  beta := β
  x := 0
  y := 0

/-- Electric embedding of the cubic Jordan carrier into the Freudenthal space. -/
def electricCharge (α : ℝ) (X : H3Zorn ℝ) : Charge where
  alpha := α
  beta := 0
  x := X
  y := 0

/-- Magnetic embedding of the cubic Jordan carrier into the Freudenthal space. -/
def magneticCharge (β : ℝ) (Y : H3Zorn ℝ) : Charge where
  alpha := 0
  beta := β
  x := 0
  y := Y

/-- On the two scalar slots, the quartic reduces to `(αβ)^2`. -/
theorem quarticInvariant_scalarCharge (α β : ℝ) :
    quarticInvariant (scalarCharge α β) = (α * β) ^ 2 := by
  rw [quarticInvariant_expanded]
  simp [scalarCharge]

/-- On a pure electric charge, the quartic is `-4 α N(X)`. -/
theorem quarticInvariant_electricCharge (α : ℝ) (X : H3Zorn ℝ) :
    quarticInvariant (electricCharge α X) =
      -4 * (α * H3Zorn.normCubic X) := by
  rw [quarticInvariant_expanded]
  simp [electricCharge]
  ring

/-- On a pure magnetic charge, the quartic is `-4 β N(Y)`. -/
theorem quarticInvariant_magneticCharge (β : ℝ) (Y : H3Zorn ℝ) :
    quarticInvariant (magneticCharge β Y) =
      -4 * (β * H3Zorn.normCubic Y) := by
  rw [quarticInvariant_expanded]
  simp [magneticCharge]
  ring

/-- The cubic Jordan norm is recovered exactly from the unit electric slice. -/
theorem cubicNorm_from_quartic (X : H3Zorn ℝ) :
    H3Zorn.normCubic X =
      (-1 / 4 : ℝ) * quarticInvariant (electricCharge 1 X) := by
  rw [quarticInvariant_electricCharge]
  ring

/-- The cubic norm and the Freudenthal quartic are distinct invariants:
for the diagonal unit, the unit-electric quartic equals `-4` while the cubic
norm equals `1`. -/
theorem unit_electric_quartic :
    quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) = -4 := by
  rw [quarticInvariant_electricCharge]
  simp

/-- The existing global H3Zorn adjoint identity is the cubic input underlying
this concrete quartic construction. -/
theorem cubic_adjoint_identity (X : H3Zorn ℝ) :
    H3Zorn.adjointQuad (H3Zorn.adjointQuad X) =
      H3Zorn.normCubic X • X :=
  H3Zorn.adjointQuad_adjointQuad X

end InfoGeometry.Algebra.H3ZornFreudenthal
