/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AtiyahBottShapiroSymbolContinuity
import InfoGeometry.Canonical.NegativeLineModuleClassification
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic.NoncommRing

/-!
# The ABS symbol extends through an additional odd Clifford generator

An actual extra generator `J`, odd for the given grading, with square `-1` and
anticommuting with all represented vectors constructs a representation of
`Q(v)-t²` through the native Clifford universal property. Its ABS symbol is
`-c(v)-tJ`. On the quadratic hemisphere it is invertible, agrees with the
original symbol at the boundary, and is continuous in finite dimensions.
No stable topological quotient or Bott comparison theorem is asserted here.
-/

noncomputable section
namespace InfoGeometry.Canonical.AtiyahBottShapiroHemisphere
open CliffordAlgebra PinOperatorFamilyBridge AtiyahBottShapiroSymbol
open AtiyahBottShapiroSymbolContinuity

section Algebraic
variable {M W : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup W] [Module ℝ W]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))

/-- Add one negative real Clifford direction. -/
def extendedQuadratic (Q : QuadraticForm ℝ M) : QuadraticForm ℝ (M × ℝ) :=
  Q.prod (-(QuadraticMap.sq : QuadraticForm ℝ ℝ))

@[simp] theorem extendedQuadratic_apply (p : M × ℝ) :
    extendedQuadratic Q p = Q p.1 - p.2 * p.2 := rfl

/-- The actual vector operator in the extended representation. -/
def extendedVector (J : Module.End ℝ W) : (M × ℝ) →ₗ[ℝ] Module.End ℝ W :=
  (ρ.representation.toLinearMap.comp (ι Q)).comp (LinearMap.fst ℝ M ℝ) +
    (LinearMap.snd ℝ M ℝ).smulRight J

@[simp] theorem extendedVector_apply (J : Module.End ℝ W) (p : M × ℝ) :
    extendedVector ρ J p = ρ.representation (ι Q p.1) + p.2 • J := rfl

theorem extendedVector_sq (J : Module.End ℝ W) (hJ : J * J = -1)
    (hanti : ∀ v, ρ.representation (ι Q v) * J + J * ρ.representation (ι Q v) = 0)
    (p : M × ℝ) :
    extendedVector ρ J p * extendedVector ρ J p =
      algebraMap ℝ (Module.End ℝ W) (extendedQuadratic Q p) := by
  rw [extendedVector_apply]
  calc
    (ρ.representation (ι Q p.1) + p.2 • J) *
        (ρ.representation (ι Q p.1) + p.2 • J) =
      ρ.representation (ι Q p.1) * ρ.representation (ι Q p.1) +
        p.2 • (ρ.representation (ι Q p.1) * J + J * ρ.representation (ι Q p.1)) +
        (p.2 * p.2) • (J * J) := by
          simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_smul, smul_add]
          abel
    _ = algebraMap ℝ (Module.End ℝ W) (extendedQuadratic Q p) := by
      rw [CliffordAlgebra.comp_ι_sq_scalar, hanti, hJ]
      simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_smul]

/-- A genuine representation of the enlarged Clifford algebra, with the same grading. -/
def extendedRepresentation (J : Module.End ℝ W) (hJ : J * J = -1)
    (hodd : ρ.grading * J + J * ρ.grading = 0)
    (hanti : ∀ v, ρ.representation (ι Q v) * J + J * ρ.representation (ι Q v) = 0) :
    GradedCliffordOperatorRepresentation (R := ℝ) (M := M × ℝ) (W := W)
      (Q := extendedQuadratic Q) where
  representation := CliffordAlgebra.lift (extendedQuadratic Q)
    ⟨extendedVector ρ J, extendedVector_sq ρ J hJ hanti⟩
  grading := ρ.grading
  grading_sq := ρ.grading_sq
  generator_odd p := by
    simp only [CliffordAlgebra.lift_ι_apply, extendedVector_apply]
    calc
      ρ.grading * (ρ.representation (ι Q p.1) + p.2 • J) +
          (ρ.representation (ι Q p.1) + p.2 • J) * ρ.grading =
        (ρ.grading * ρ.representation (ι Q p.1) +
          ρ.representation (ι Q p.1) * ρ.grading) +
          p.2 • (ρ.grading * J + J * ρ.grading) := by
            simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add]
            abel
      _ = 0 := by rw [ρ.generator_odd, hodd]; simp

variable (J : Module.End ℝ W) (hJ : J * J = -1)
variable (hodd : ρ.grading * J + J * ρ.grading = 0)
variable (hanti : ∀ v, ρ.representation (ι Q v) * J + J * ρ.representation (ι Q v) = 0)

/-- The enlarged native action agrees with its defining vector operator. -/
@[simp] theorem extendedRepresentation_generator (p : M × ℝ) :
    (extendedRepresentation ρ J hJ hodd hanti).representation
      (ι (extendedQuadratic Q) p) = extendedVector ρ J p := by
  change CliffordAlgebra.lift (extendedQuadratic Q)
    ⟨extendedVector ρ J, extendedVector_sq ρ J hJ hanti⟩
      (ι (extendedQuadratic Q) p) = _
  exact CliffordAlgebra.lift_ι_apply _ _ p

/-- Restricting the enlarged action along the native Clifford inclusion
recovers the entire original action, not only its vector generators. -/
theorem extendedRepresentation_restrict :
    (extendedRepresentation ρ J hJ hodd hanti).representation.comp
        (CliffordAlgebra.map
          (QuadraticMap.Isometry.inl Q (-(QuadraticMap.sq : QuadraticForm ℝ ℝ)))) =
      ρ.representation := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change (extendedRepresentation ρ J hJ hodd hanti).representation
    (CliffordAlgebra.map
      (QuadraticMap.Isometry.inl Q (-(QuadraticMap.sq : QuadraticForm ℝ ℝ)))
      (ι Q v)) = ρ.representation (ι Q v)
  rw [CliffordAlgebra.map_apply_ι]
  change (extendedRepresentation ρ J hJ hodd hanti).representation
    (ι (extendedQuadratic Q) (v, 0)) = _
  rw [extendedRepresentation_generator, extendedVector_apply, zero_smul, add_zero]

/-- The symbol is exactly the sign-sensitive hemisphere formula. -/
theorem extended_symbol_apply (p : M × ℝ) (w : oddSpace ρ) :
    (symbol (extendedRepresentation ρ J hJ hodd hanti) p w : W) =
      -(ρ.representation (ι Q p.1) w) - p.2 • J w := by
  change -((extendedRepresentation ρ J hJ hodd hanti).representation
    (ι (extendedQuadratic Q) p) (w : W)) = _
  rw [extendedRepresentation_generator, extendedVector_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  abel

/-- At `t=0`, the extension restricts to the original actual symbol. -/
theorem extended_symbol_boundary (v : M) :
    symbol (extendedRepresentation ρ J hJ hodd hanti) (v, 0) = symbol ρ v := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change -((extendedRepresentation ρ J hJ hodd hanti).representation
    (ι (extendedQuadratic Q) (v, 0)) (w : W)) =
      -(ρ.representation (ι Q v) (w : W))
  rw [extendedRepresentation_generator, extendedVector_apply, zero_smul, add_zero]

/-- The upper negative-unit level set, with no unproved compactness assertion. -/
abbrev QuadraticHemisphere (Q : QuadraticForm ℝ M) :=
  {p : M × ℝ // extendedQuadratic Q p = -1 ∧ 0 ≤ p.2}

/-- Every point of the hemisphere carries an explicitly constructed invertible symbol. -/
def hemisphereSymbolEquiv (p : QuadraticHemisphere Q) : oddSpace ρ ≃ₗ[ℝ] evenSpace ρ :=
  symbolEquiv (extendedRepresentation ρ J hJ hodd hanti) p.val
    (by rw [p.property.1]; norm_num)

/-- The inverse is `c(v)+tJ`, with no denominator on the negative unit level set. -/
theorem hemisphereSymbolEquiv_inverse_apply (p : QuadraticHemisphere Q) (w : evenSpace ρ) :
    ((hemisphereSymbolEquiv ρ J hJ hodd hanti p).symm w : W) =
      ρ.representation (ι Q p.val.1) w + p.val.2 • J w := by
  change -(extendedQuadratic Q p.val)⁻¹ •
    (extendedRepresentation ρ J hJ hodd hanti).representation
      (ι (extendedQuadratic Q) p.val) (w : W) = _
  rw [p.property.1, extendedRepresentation_generator, extendedVector_apply]
  simp only [inv_neg, inv_one, neg_neg, one_smul, LinearMap.add_apply,
    LinearMap.smul_apply]

end Algebraic

section Topology
variable {M W : Type*}
variable [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))
variable (J : Module.End ℝ W) (hJ : J * J = -1)
variable (hodd : ρ.grading * J + J * ρ.grading = 0)
variable (hanti : ∀ v, ρ.representation (ι Q v) * J + J * ρ.representation (ι Q v) = 0)

/-- The forward hemisphere extension is a continuous family of actual operators. -/
theorem continuous_hemisphereSymbol :
    Continuous (fun p : QuadraticHemisphere Q =>
      continuousSymbol (extendedRepresentation ρ J hJ hodd hanti) p.val) :=
  (continuous_continuousSymbol _).comp continuous_subtype_val

/-- The explicit inverse hemisphere operators are continuous as well. -/
theorem continuous_hemisphereInverseSymbol :
    Continuous (fun p : QuadraticHemisphere Q =>
      continuousInverseUnitSymbol (extendedRepresentation ρ J hJ hodd hanti) p.val) :=
  (continuous_continuousInverseUnitSymbol _).comp continuous_subtype_val

end Topology

section ConcreteExtension

open NegativeLineModuleClassification

/-- The actual four-dimensional real carrier of a graded two-generator example. -/
abbrev FourSpace := (ℝ × ℝ) × (ℝ × ℝ)

/-- The first negative Clifford generator is the standard doubled phase. -/
def fourPhase : Module.End ℝ FourSpace := standardPhase (ℝ × ℝ)

/-- A second odd negative generator, using the real phase within each pair. -/
def fourExtra : Module.End ℝ FourSpace :=
  ((standardPhase ℝ).comp (LinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))).prod
    ((standardPhase ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)))

@[simp] theorem fourExtra_apply (p : FourSpace) :
    fourExtra p = ((-p.2.2, p.2.1), (-p.1.2, p.1.1)) := rfl

@[simp] theorem fourExtra_sq : fourExtra * fourExtra = -1 := by
  ext <;> simp [Module.End.mul_apply]

theorem fourExtra_odd :
    standardGrading (ℝ × ℝ) * fourExtra +
      fourExtra * standardGrading (ℝ × ℝ) = 0 := by
  ext <;> simp [Module.End.mul_apply]

theorem fourPhase_extra_anticommute :
    fourPhase * fourExtra + fourExtra * fourPhase = 0 := by
  ext <;> simp [fourPhase, Module.End.mul_apply]

/-- These actual endomorphisms do not commute; evaluation distinguishes their
products before any scalar coordinate is read. -/
theorem fourPhase_extra_noncommute : fourPhase * fourExtra ≠ fourExtra * fourPhase := by
  intro h
  have hcoord := congrArg
    (fun A : Module.End ℝ FourSpace => (A ((1, 0), (0, 0))).1.2) h
  norm_num [fourPhase, Module.End.mul_apply] at hcoord

theorem fourExtra_generator_anticommute (r : ℝ) :
    (standardRepresentation (ℝ × ℝ)).representation (ι negativeQuadratic r) * fourExtra +
      fourExtra * (standardRepresentation (ℝ × ℝ)).representation (ι negativeQuadratic r) = 0 := by
  simp only [standardRepresentation_generator]
  change (r • fourPhase) * fourExtra + fourExtra * (r • fourPhase) = 0
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, fourPhase_extra_anticommute, smul_zero]

/-- The closed example instantiates the full hemisphere construction: all
extra-generator relations are proved for the displayed real operators. -/
def fourExtendedRepresentation :
    GradedCliffordOperatorRepresentation (R := ℝ) (M := ℝ × ℝ) (W := FourSpace)
      (Q := extendedQuadratic negativeQuadratic) :=
  extendedRepresentation (standardRepresentation (ℝ × ℝ)) fourExtra
    fourExtra_sq fourExtra_odd fourExtra_generator_anticommute

/-- The represented coordinate generators are exactly the noncommuting
operators displayed above. -/
theorem fourExtendedRepresentation_generators :
    fourExtendedRepresentation.representation
        (ι (extendedQuadratic negativeQuadratic) (1, 0)) = fourPhase ∧
      fourExtendedRepresentation.representation
        (ι (extendedQuadratic negativeQuadratic) (0, 1)) = fourExtra := by
  have hgen (p : ℝ × ℝ) :
      fourExtendedRepresentation.representation
          (ι (extendedQuadratic negativeQuadratic) p) =
        p.1 • fourPhase + p.2 • fourExtra := by
    change CliffordAlgebra.lift (extendedQuadratic negativeQuadratic)
      ⟨extendedVector (standardRepresentation (ℝ × ℝ)) fourExtra,
        extendedVector_sq (standardRepresentation (ℝ × ℝ)) fourExtra
          fourExtra_sq fourExtra_generator_anticommute⟩
        (ι (extendedQuadratic negativeQuadratic) p) =
      p.1 • standardPhase (ℝ × ℝ) + p.2 • fourExtra
    rw [CliffordAlgebra.lift_ι_apply, extendedVector_apply,
      standardRepresentation_generator]
  constructor
  · simpa only [one_smul, zero_smul, add_zero] using hgen (1, 0)
  · simpa only [zero_smul, one_smul, zero_add] using hgen (0, 1)

end ConcreteExtension

end InfoGeometry.Canonical.AtiyahBottShapiroHemisphere
