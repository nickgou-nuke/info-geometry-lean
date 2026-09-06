import Mathlib

/-!
# Algebraic dual-flat difference operators

This owner records only identities that are independent of a manifold
connection implementation.  Curvature is supplied as an endomorphism-valued
field by a later geometric owner; the final theorem below consumes the
dual-flat commutator identity rather than postulating a connection model.
-/

namespace InfoGeometry.Geometry.Statistical

noncomputable section

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

def midpointOperator (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    Module.End ℝ T :=
  (1 / 2 : ℝ) • (nabla X + nablaStar X)

def differenceOperator (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    Module.End ℝ T :=
  nablaStar X - nabla X

def cubicCorrection (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    Module.End ℝ T :=
  (-1 / 2 : ℝ) • differenceOperator nabla nablaStar X

def operatorCommutator (A B : Module.End ℝ T) : Module.End ℝ T :=
  A.comp B - B.comp A

/-- The scalar identity direction is central for the endomorphism commutator.
This is the algebraic scale/Weyl cancellation behind the shape-only curvature
channel. -/
theorem operatorCommutator_add_smul_id
    (c d : ℝ) (A B : Module.End ℝ T) :
    operatorCommutator
        (c • LinearMap.id + A)
        (d • LinearMap.id + B) =
      operatorCommutator A B := by
  ext z
  simp [operatorCommutator]
  module

structure DualFlatCurvatureDatum where
  R0 : T → T → Module.End ℝ T
  nabla : T → Module.End ℝ T
  nablaStar : T → Module.End ℝ T
  curvature_sum : ∀ X Y,
    R0 X Y +
        operatorCommutator (cubicCorrection nabla nablaStar X)
          (cubicCorrection nabla nablaStar Y) =
      (1 / 2 : ℝ) •
        (operatorCommutator (nabla X) (nabla Y) +
          operatorCommutator (nablaStar X) (nablaStar Y))
  flat : ∀ X Y, operatorCommutator (nabla X) (nabla Y) = 0
  flatStar : ∀ X Y, operatorCommutator (nablaStar X) (nablaStar Y) = 0

theorem midpointOperator_curvature_expansion
    (nabla nablaStar : T → Module.End ℝ T) (X Y : T) :
    (1 / 2 : ℝ) •
        (operatorCommutator (nabla X) (nabla Y) +
          operatorCommutator (nablaStar X) (nablaStar Y)) =
      operatorCommutator (midpointOperator nabla nablaStar X)
          (midpointOperator nabla nablaStar Y) +
        operatorCommutator (cubicCorrection nabla nablaStar X)
          (cubicCorrection nabla nablaStar Y) := by
  ext z
  simp [operatorCommutator, midpointOperator, cubicCorrection,
    differenceOperator]
  module

theorem midpointOperator_add_cubicCorrection
    (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    midpointOperator nabla nablaStar X + cubicCorrection nabla nablaStar X =
      nabla X := by
  ext z
  simp [midpointOperator, cubicCorrection, differenceOperator]
  module

theorem midpointOperator_sub_cubicCorrection
    (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    midpointOperator nabla nablaStar X - cubicCorrection nabla nablaStar X =
      nablaStar X := by
  ext z
  simp [midpointOperator, cubicCorrection, differenceOperator]
  module

theorem differenceOperator_eq_neg_two_cubicCorrection
    (nabla nablaStar : T → Module.End ℝ T) (X : T) :
    differenceOperator nabla nablaStar X =
      (-2 : ℝ) • cubicCorrection nabla nablaStar X := by
  ext z
  simp [cubicCorrection, differenceOperator]
  module

theorem dualFlat_curvature_eq_neg_quarter_difference
    (R0 : T → T → Module.End ℝ T)
    (nabla nablaStar : T → Module.End ℝ T)
    (X Y : T)
    (hsum : R0 X Y +
        operatorCommutator (cubicCorrection nabla nablaStar X)
          (cubicCorrection nabla nablaStar Y) =
      (1 / 2 : ℝ) •
        (operatorCommutator (nabla X) (nabla Y) +
          operatorCommutator (nablaStar X) (nablaStar Y)))
    (hflat : operatorCommutator (nabla X) (nabla Y) = 0)
    (hflatStar : operatorCommutator (nablaStar X) (nablaStar Y) = 0) :
    R0 X Y = (-1 / 4 : ℝ) •
      operatorCommutator (differenceOperator nabla nablaStar X)
        (differenceOperator nabla nablaStar Y) := by
  calc
    R0 X Y =
        ((1 / 2 : ℝ) •
          (operatorCommutator (nabla X) (nabla Y) +
            operatorCommutator (nablaStar X) (nablaStar Y))) -
          operatorCommutator (cubicCorrection nabla nablaStar X)
            (cubicCorrection nabla nablaStar Y) :=
      (eq_sub_iff_add_eq).2 hsum
    _ = (-1 / 4 : ℝ) •
        operatorCommutator (differenceOperator nabla nablaStar X)
          (differenceOperator nabla nablaStar Y) := by
      rw [hflat, hflatStar]
      ext z
      simp [operatorCommutator, cubicCorrection, differenceOperator]
      module

theorem DualFlatCurvatureDatum.curvature_eq_neg_quarter_difference
    (C : DualFlatCurvatureDatum (T := T)) (X Y : T) :
    C.R0 X Y = (-1 / 4 : ℝ) •
      operatorCommutator (differenceOperator C.nabla C.nablaStar X)
        (differenceOperator C.nabla C.nablaStar Y) := by
  exact dualFlat_curvature_eq_neg_quarter_difference
    C.R0 C.nabla C.nablaStar X Y
    (C.curvature_sum X Y) (C.flat X Y) (C.flatStar X Y)

theorem DualFlatCurvatureDatum.curvature_eq_neg_quarter_shape_difference
    (C : DualFlatCurvatureDatum (T := T))
    (κ : T → ℝ) (K0 : T → Module.End ℝ T)
    (hshape : ∀ X,
      differenceOperator C.nabla C.nablaStar X =
        κ X • LinearMap.id + K0 X)
    (X Y : T) :
    C.R0 X Y = (-1 / 4 : ℝ) • operatorCommutator (K0 X) (K0 Y) := by
  rw [C.curvature_eq_neg_quarter_difference X Y,
    hshape X, hshape Y,
    operatorCommutator_add_smul_id]

theorem DualFlatCurvatureDatum.curvature_eq_neg_correction_shape_commutator
    (C : DualFlatCurvatureDatum (T := T))
    (κ : T → ℝ) (K0 : T → Module.End ℝ T)
    (hshape : ∀ X,
      cubicCorrection C.nabla C.nablaStar X =
        κ X • LinearMap.id + K0 X)
    (X Y : T) :
    C.R0 X Y = -operatorCommutator (K0 X) (K0 Y) := by
  rw [C.curvature_eq_neg_quarter_difference X Y]
  simp_rw [differenceOperator_eq_neg_two_cubicCorrection, hshape]
  ext z
  simp [operatorCommutator]
  module

/-! ## Represented derivation-valued difference fields

This interface records the additional data needed to compare the algebraic
dual-flat curvature identity with a Lie-algebra-valued operator field.  The
representation is explicit; no restriction to a proposed carrier is inferred
from the source Lie algebra. -/

/-! The generic representation statement is intentionally parameterized by the
actual correction field.  It is the theorem used by concrete split-octonion
derivation bridges after supplying their representation map. -/
theorem represented_curvature_eq_neg_representation_bracket
    {D : Type*} [AddCommGroup D] [Module ℝ D] [LieRing D]
    (C : DualFlatCurvatureDatum (T := T))
    (parameter : T → D)
    (representation : D →ₗ[ℝ] Module.End ℝ T)
    (correction_eq : ∀ X,
      cubicCorrection C.nabla C.nablaStar X = representation (parameter X))
    (representation_map_lie : ∀ d e : D,
      representation ⁅d, e⁆ =
        operatorCommutator (representation d) (representation e))
    (X Y : T) :
    C.R0 X Y =
      -representation ⁅parameter X, parameter Y⁆ := by
  rw [C.curvature_eq_neg_quarter_difference]
  simp_rw [differenceOperator_eq_neg_two_cubicCorrection]
  rw [correction_eq X, correction_eq Y]
  rw [representation_map_lie]
  ext z
  simp [operatorCommutator]
  module

end
end InfoGeometry.Geometry.Statistical
