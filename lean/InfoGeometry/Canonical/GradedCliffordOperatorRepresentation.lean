/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Graded Clifford representations on operator domains

A representation of the native Clifford algebra acts on an actual module by
linear endomorphisms. An involutive grading that anticommutes with the vector
generators intertwines the complete Clifford action with the native grade
involution. Consequently, even elements commute with the grading and odd
elements anticommute with it.

The resulting action defines an object of `GradedMatrixMorita.GradedModuleCat`
through `Module.compHom`. This is the algebraic grading compatibility used for
Clifford modules in Part I of Atiyah--Bott--Shapiro. The regular representation
provides a faithful instance on the Clifford algebra itself.

The namespace retains the public names originally declared in
`Canonical.PinOperatorFamilyBridge`.
-/

noncomputable section

namespace InfoGeometry.Canonical.PinOperatorFamilyBridge

open CliffordAlgebra

universe u

section Representation

variable {R M W : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup W] [Module R W]
variable {Q : QuadraticForm R M}

/-- A represented Clifford module with a specified involutive grading
operator. The generator anticommutation equation is the grading contract. -/
structure GradedCliffordOperatorRepresentation where
  representation : CliffordAlgebra Q →ₐ[R] Module.End R W
  grading : Module.End R W
  grading_sq : grading * grading = 1
  generator_odd : ∀ v : M,
    grading * representation (ι Q v) + representation (ι Q v) * grading = 0

namespace GradedCliffordOperatorRepresentation

variable (ρ : GradedCliffordOperatorRepresentation (R := R) (M := M) (W := W) (Q := Q))

/-- Conjugation by the grading sends every represented Clifford vector to its
negative. -/
theorem grading_conjugates_generator (v : M) :
    ρ.grading * ρ.representation (ι Q v) * ρ.grading =
      -(ρ.representation (ι Q v)) := by
  have hanti := ρ.generator_odd v
  have hleft : ρ.grading * ρ.representation (ι Q v) =
      -(ρ.representation (ι Q v) * ρ.grading) := by
    calc
      ρ.grading * ρ.representation (ι Q v) =
          (ρ.grading * ρ.representation (ι Q v) +
            ρ.representation (ι Q v) * ρ.grading) -
            ρ.representation (ι Q v) * ρ.grading := by abel
      _ = -(ρ.representation (ι Q v) * ρ.grading) := by rw [hanti]; simp
  calc
    ρ.grading * ρ.representation (ι Q v) * ρ.grading =
        -(ρ.representation (ι Q v) * ρ.grading) * ρ.grading := by rw [hleft]
    _ = -(ρ.representation (ι Q v) * (ρ.grading * ρ.grading)) := by noncomm_ring
    _ = -(ρ.representation (ι Q v)) := by rw [ρ.grading_sq]; simp

/-- Conjugation by the grading fixes a product of two represented Clifford
vectors; this gives the explicit even two-generator calculation. -/
theorem grading_fixes_two_generators (v w : M) :
    ρ.grading * (ρ.representation (ι Q v) * ρ.representation (ι Q w)) * ρ.grading =
      ρ.representation (ι Q v) * ρ.representation (ι Q w) := by
  calc
    ρ.grading * (ρ.representation (ι Q v) * ρ.representation (ι Q w)) * ρ.grading =
        (ρ.grading * ρ.representation (ι Q v) * ρ.grading) *
          (ρ.grading * ρ.representation (ι Q w) * ρ.grading) := by
            calc
              ρ.grading * (ρ.representation (ι Q v) * ρ.representation (ι Q w)) * ρ.grading =
                  (ρ.grading * ρ.representation (ι Q v)) *
                    (ρ.representation (ι Q w) * ρ.grading) := by noncomm_ring
              _ = (ρ.grading * ρ.representation (ι Q v) * ρ.grading) *
                    (ρ.grading * ρ.representation (ι Q w) * ρ.grading) := by
                  calc
                    _ = (ρ.grading * ρ.representation (ι Q v)) * 1 *
                        (ρ.representation (ι Q w) * ρ.grading) := by simp
                    _ = (ρ.grading * ρ.representation (ι Q v)) *
                        (ρ.grading * ρ.grading) *
                        (ρ.representation (ι Q w) * ρ.grading) := by rw [ρ.grading_sq]
                    _ = _ := by noncomm_ring
    _ = _ := by rw [ρ.grading_conjugates_generator, ρ.grading_conjugates_generator]; noncomm_ring

/-- Generator anticommutation extends to every element of the native Clifford
algebra as equivariance for its grade involution. -/
theorem grading_intertwines (a : CliffordAlgebra Q) :
    ρ.grading * ρ.representation a =
      ρ.representation (CliffordAlgebra.involute a) * ρ.grading := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      simp only [AlgHom.commutes]
      exact (Algebra.commutes r ρ.grading).symm
  | ι v =>
      simpa only [CliffordAlgebra.involute_ι, map_neg, neg_mul] using
        (eq_neg_of_add_eq_zero_left (ρ.generator_odd v))
  | mul a b ha hb =>
      simp only [map_mul]
      calc
        ρ.grading * (ρ.representation a * ρ.representation b) =
            (ρ.grading * ρ.representation a) * ρ.representation b :=
          (mul_assoc _ _ _).symm
        _ = (ρ.representation (CliffordAlgebra.involute a) * ρ.grading) *
            ρ.representation b := by rw [ha]
        _ = ρ.representation (CliffordAlgebra.involute a) *
            (ρ.grading * ρ.representation b) := mul_assoc _ _ _
        _ = ρ.representation (CliffordAlgebra.involute a) *
            (ρ.representation (CliffordAlgebra.involute b) * ρ.grading) := by rw [hb]
        _ = (ρ.representation (CliffordAlgebra.involute a) *
            ρ.representation (CliffordAlgebra.involute b)) * ρ.grading :=
          (mul_assoc _ _ _).symm
  | add a b ha hb =>
      simp only [map_add, mul_add, add_mul, ha, hb]

/-- Conjugation by the grading represents the grade involution on every
Clifford element. -/
theorem grading_conjugates (a : CliffordAlgebra Q) :
    ρ.grading * ρ.representation a * ρ.grading =
      ρ.representation (CliffordAlgebra.involute a) := by
  rw [ρ.grading_intertwines a, mul_assoc, ρ.grading_sq, mul_one]

/-- Pointwise form of the full grading compatibility. -/
theorem grading_representation_apply (a : CliffordAlgebra Q) (w : W) :
    ρ.grading (ρ.representation a w) =
      ρ.representation (CliffordAlgebra.involute a) (ρ.grading w) :=
  congrArg (fun T : Module.End R W => T w) (ρ.grading_intertwines a)

/-- The grading is an involution on the represented module. -/
@[simp] theorem grading_grading_apply (w : W) :
    ρ.grading (ρ.grading w) = w :=
  congrArg (fun T : Module.End R W => T w) ρ.grading_sq

/-- Every element of the native even Clifford submodule commutes with the
represented module grading. -/
theorem grading_commutes_of_mem_even (a : CliffordAlgebra Q)
    (ha : a ∈ CliffordAlgebra.evenOdd Q 0) :
    ρ.grading * ρ.representation a = ρ.representation a * ρ.grading := by
  rw [ρ.grading_intertwines a, CliffordAlgebra.involute_eq_of_mem_even ha]

/-- Every element of the native odd Clifford submodule anticommutes with the
represented module grading. -/
theorem grading_anticommutes_of_mem_odd (a : CliffordAlgebra Q)
    (ha : a ∈ CliffordAlgebra.evenOdd Q 1) :
    ρ.grading * ρ.representation a = -(ρ.representation a * ρ.grading) := by
  rw [ρ.grading_intertwines a, CliffordAlgebra.involute_eq_of_mem_odd ha, map_neg, neg_mul]

end GradedCliffordOperatorRepresentation

end Representation

namespace GradedCliffordOperatorRepresentation

section ModuleCategory

variable {R M W : Type u}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup W] [Module R W]
variable {Q : QuadraticForm R M}

/-- The represented action and its proved grading compatibility define an
actual graded module over the Clifford algebra. The common universe matches
the existing `GradedModuleCat` interface. -/
def toGradedModule
    (ρ : GradedCliffordOperatorRepresentation (R := R) (M := M) (W := W) (Q := Q)) :
    InfoGeometry.OperatorAlgebra.GradedMatrixMorita.GradedModuleCat
      (CliffordAlgebra.involuteEquiv (Q := Q)).toRingEquiv := by
  letI : Module (CliffordAlgebra Q) W :=
    Module.compHom W ρ.representation.toRingHom
  exact
    { V := ModuleCat.of (CliffordAlgebra Q) W
      grade := ρ.grading.toAddMonoidHom
      grade_smul := by
        intro a w
        change ρ.grading (ρ.representation a w) =
          ρ.representation (CliffordAlgebra.involute a) (ρ.grading w)
        exact ρ.grading_representation_apply a w
      grade_sq := ρ.grading_grading_apply }

end ModuleCategory

section RegularRepresentation

variable {R M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Left multiplication and the native grade involution give the regular
graded Clifford representation. -/
def regular (Q : QuadraticForm R M) :
    GradedCliffordOperatorRepresentation
      (R := R) (M := M) (W := CliffordAlgebra Q) (Q := Q) where
  representation := Algebra.lmul R (CliffordAlgebra Q)
  grading := CliffordAlgebra.involute.toLinearMap
  grading_sq := by
    ext a
    exact CliffordAlgebra.involute_involute a
  generator_odd v := by
    ext a
    change CliffordAlgebra.involute (ι Q v * a) +
      ι Q v * CliffordAlgebra.involute a = 0
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, neg_add_cancel]

@[simp] theorem regular_representation_apply (Q : QuadraticForm R M)
    (a b : CliffordAlgebra Q) :
    (regular Q).representation a b = a * b := rfl

@[simp] theorem regular_grading_apply (Q : QuadraticForm R M) (a : CliffordAlgebra Q) :
    (regular Q).grading a = CliffordAlgebra.involute a := rfl

/-- The regular module retains the entire Clifford algebra faithfully. -/
theorem regular_representation_injective (Q : QuadraticForm R M) :
    Function.Injective (regular Q).representation := by
  change Function.Injective (Algebra.lmul R (CliffordAlgebra Q))
  exact Algebra.lmul_injective

end RegularRepresentation

local instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

section RegularReal

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The grading and a nonzero vector's left multiplication fail to commute
in the actual endomorphism algebra of the regular real Clifford module. -/
theorem regular_grading_noncommutes_generator
    (Q : QuadraticForm ℝ M) (v : M) (hv : v ≠ 0) :
    (regular Q).grading * (regular Q).representation (ι Q v) ≠
      (regular Q).representation (ι Q v) * (regular Q).grading := by
  intro hcomm
  have hunit := congrArg
    (fun T : Module.End ℝ (CliffordAlgebra Q) => T 1) hcomm
  change CliffordAlgebra.involute (ι Q v * 1) =
    ι Q v * CliffordAlgebra.involute 1 at hunit
  simp only [mul_one, map_one, CliffordAlgebra.involute_ι] at hunit
  have htwo : (2 : ℝ) • (ι Q v) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hunit.symm
  have hzero : ι Q v = 0 := by
    calc
      ι Q v = (2 : ℝ)⁻¹ • ((2 : ℝ) • (ι Q v)) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul]
      _ = 0 := by rw [htwo, smul_zero]
  apply hv
  apply (ExteriorAlgebra.ι_eq_zero_iff (R := ℝ) v).mp
  have hext := congrArg (CliffordAlgebra.equivExterior Q) hzero
  simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_ι, map_zero] using hext

end RegularReal

/-- A closed real graded Clifford representation: the regular action for
the negative quadratic form on the real line. -/
def negativeLine :
    GradedCliffordOperatorRepresentation
      (R := ℝ) (M := ℝ)
      (W := CliffordAlgebra (-(QuadraticMap.sq : QuadraticForm ℝ ℝ)))
      (Q := -(QuadraticMap.sq : QuadraticForm ℝ ℝ)) :=
  regular (-(QuadraticMap.sq : QuadraticForm ℝ ℝ))

/-- The closed negative-line module has an explicit pair of noncommuting
operators: its grading and left multiplication by the vector `1`. -/
theorem negativeLine_grading_noncommutes_generator :
    ¬ Commute negativeLine.grading
      (negativeLine.representation (ι (-(QuadraticMap.sq : QuadraticForm ℝ ℝ)) 1)) := by
  intro hcomm
  exact regular_grading_noncommutes_generator
    (-(QuadraticMap.sq : QuadraticForm ℝ ℝ)) (1 : ℝ) one_ne_zero hcomm.eq


end GradedCliffordOperatorRepresentation

end InfoGeometry.Canonical.PinOperatorFamilyBridge
