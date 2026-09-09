import Mathlib.Tactic
import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Exceptional.FreudenthalAction

/-!
# Concrete Freudenthal quartic invariant for `H3Zorn ℝ`

This module specializes the abstract Freudenthal charge space to the native
split-Albert carrier `H3Zorn ℝ` using the already verified cubic Jordan datum
`h3zornCubicJordanDatum`.

The construction keeps the cubic Jordan norm and the Freudenthal quartic
strictly distinct. In particular, on the canonical electric embedding
`X ↦ (1,0,X,0)`, the quartic restricts to `-4 * normCubic X`.

The final section specializes the repository's theorem-safe invariant-action
interface. It does not assert an identification with `E₇(7)`; any concrete
group realization must provide preservation of both the Freudenthal
symplectic form and quartic invariant.
-/

set_option autoImplicit false

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

/-- A split-Albert Freudenthal charge is regular when its quartic is nonzero. -/
def Regular (Q : Charge) : Prop :=
  FreudenthalRegular h3zornCubicJordanDatum Q

/-- A split-Albert Freudenthal boundary charge has vanishing quartic and is nonzero. -/
def Boundary (Q : Charge) : Prop :=
  FreudenthalBoundary h3zornCubicJordanDatum Q

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
  change (α * β - H3Zorn.traceBilin (0 : H3Zorn ℝ) 0) ^ 2 -
      4 * (α * H3Zorn.normCubic 0 + β * H3Zorn.normCubic 0 -
        H3Zorn.traceBilin (H3Zorn.adjointQuad 0) (H3Zorn.adjointQuad 0)) =
    (α * β) ^ 2
  have hmain : (α * β - H3Zorn.traceBilin (0 : H3Zorn ℝ) 0) ^ 2 -
      4 * (α * H3Zorn.normCubic 0 + β * H3Zorn.normCubic 0 -
        H3Zorn.traceBilin (H3Zorn.adjointQuad 0) (H3Zorn.adjointQuad 0)) =
      (α * β) ^ 2 := by
    rw [H3Zorn.traceBilin_zero_left, H3Zorn.normCubic_zero,
      adjointQuad_zero, H3Zorn.traceBilin_zero_left]
    ring
  exact hmain

/-- On a pure electric charge, the quartic is `-4 α N(X)`. -/
theorem quarticInvariant_electricCharge (α : ℝ) (X : H3Zorn ℝ) :
    quarticInvariant (electricCharge α X) =
      -4 * (α * H3Zorn.normCubic X) := by
  rw [quarticInvariant_expanded]
  change (α * 0 - H3Zorn.traceBilin X 0) ^ 2 -
      4 * (α * H3Zorn.normCubic X + 0 * H3Zorn.normCubic 0 -
        H3Zorn.traceBilin (H3Zorn.adjointQuad X) (H3Zorn.adjointQuad 0)) =
    -4 * (α * H3Zorn.normCubic X)
  have hq : H3Zorn.adjointQuad (0 : H3Zorn ℝ) = 0 := adjointQuad_zero
  have hz0 : H3Zorn.traceBilin X (0 : H3Zorn ℝ) = 0 :=
    H3Zorn.traceBilin_zero_right _
  have hz : H3Zorn.traceBilin (H3Zorn.adjointQuad X) (0 : H3Zorn ℝ) = 0 :=
    H3Zorn.traceBilin_zero_right _
  rw [hz0, hq, hz]
  simp [H3Zorn.normCubic_zero]

/-- On a pure magnetic charge, the quartic is `-4 β N(Y)`. -/
theorem quarticInvariant_magneticCharge (β : ℝ) (Y : H3Zorn ℝ) :
    quarticInvariant (magneticCharge β Y) =
      -4 * (β * H3Zorn.normCubic Y) := by
  rw [quarticInvariant_expanded]
  change (0 * β - H3Zorn.traceBilin 0 Y) ^ 2 -
      4 * (0 * H3Zorn.normCubic 0 + β * H3Zorn.normCubic Y -
        H3Zorn.traceBilin (H3Zorn.adjointQuad 0) (H3Zorn.adjointQuad Y)) =
    -4 * (β * H3Zorn.normCubic Y)
  have hq : H3Zorn.adjointQuad (0 : H3Zorn ℝ) = 0 := adjointQuad_zero
  have hz0 : H3Zorn.traceBilin (0 : H3Zorn ℝ) Y = 0 :=
    H3Zorn.traceBilin_zero_left _
  have hz : H3Zorn.traceBilin (0 : H3Zorn ℝ) (H3Zorn.adjointQuad Y) = 0 :=
    H3Zorn.traceBilin_zero_left _
  rw [hz0, hq]
  rw [hz]
  simp [H3Zorn.normCubic_zero]

/-- The cubic Jordan norm is recovered exactly from the unit electric slice. -/
theorem cubicNorm_from_quartic (X : H3Zorn ℝ) :
    H3Zorn.normCubic X =
      (-1 / 4 : ℝ) * quarticInvariant (electricCharge 1 X) := by
  rw [quarticInvariant_electricCharge]
  ring

/-- The unit electric slice has quartic invariant `-4`. -/
theorem unit_electric_quartic :
    quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) = -4 := by
  rw [quarticInvariant_electricCharge]
  simp

/-- The cubic norm and quartic invariant are numerically distinct on the
canonical unit electric slice. -/
theorem unit_cubic_ne_unit_electric_quartic :
    H3Zorn.normCubic (1 : H3Zorn ℝ) ≠
      quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) := by
  rw [H3Zorn.normCubic_one, unit_electric_quartic]
  norm_num

/-- The existing global H3Zorn adjoint identity is the cubic input underlying
this concrete quartic construction. -/
theorem cubic_adjoint_identity (X : H3Zorn ℝ) :
    H3Zorn.adjointQuad (H3Zorn.adjointQuad X) =
      H3Zorn.normCubic X • X :=
  H3Zorn.adjointQuad_adjointQuad X

/-! ## Invariant group actions -/

/-- A theorem-safe group action on the concrete split-Albert Freudenthal space.
A future `E₇(7)` realization must construct an inhabitant of this type rather
than identifying the group by name alone. -/
abbrev InvariantAction (G : Type*) [Group G] :=
  FreudenthalInvariantAction G (H3Zorn ℝ) h3zornCubicJordanDatum

namespace InvariantAction

variable {G : Type*} [Group G]
variable (A : InvariantAction G)

/-- Every admitted invariant action preserves the concrete quartic. -/
@[simp]
theorem quarticInvariant_act (g : G) (Q : Charge) :
    quarticInvariant (A.act g Q) = quarticInvariant Q := by
  exact A.preserves_quarticInvariant g Q

/-- Every admitted invariant action preserves the concrete symplectic form. -/
@[simp]
theorem symplecticForm_act (g : G) (Q₁ Q₂ : Charge) :
    symplecticForm (A.act g Q₁) (A.act g Q₂) = symplecticForm Q₁ Q₂ := by
  exact A.preserves_symplecticForm g Q₁ Q₂

/-- Freudenthal regularity is invariant under every admitted action. -/
theorem regular_iff (g : G) (Q : Charge) :
    Regular (A.act g Q) ↔ Regular Q := by
  exact FreudenthalInvariantAction.regular_iff A g Q

/-- The quartic boundary is invariant under every admitted action. -/
theorem boundary_iff (g : G) (Q : Charge) :
    Boundary (A.act g Q) ↔ Boundary Q := by
  exact FreudenthalInvariantAction.boundary_iff A g Q

end InvariantAction

end InfoGeometry.Algebra.H3ZornFreudenthal
