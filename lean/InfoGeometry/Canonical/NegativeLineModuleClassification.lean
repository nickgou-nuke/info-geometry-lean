/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AtiyahBottShapiroSymbol
import Mathlib.LinearAlgebra.Prod

/-!
# Actual graded real Cl(0,1) modules have the standard doubled form

The carrier is the represented module itself. The equivalence uses its actual
grading eigenspaces and the ABS symbol at the real vector `1`. It conjugates
the Clifford generator to `(x,y) ↦ (-y,x)` and the grading to `(x,y) ↦ (x,-y)`.
The compatibility extends to every element of the native Clifford algebra.
No finite dimension is needed for the equivalence; finite dimensions are a
consequence, not a substitute for a module isomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.NegativeLineModuleClassification

open CliffordAlgebra
open PinOperatorFamilyBridge AtiyahBottShapiroSymbol

abbrev negativeQuadratic : QuadraticForm ℝ ℝ := -(QuadraticMap.sq : QuadraticForm ℝ ℝ)

@[simp] theorem negativeQuadratic_apply (r : ℝ) : negativeQuadratic r = -(r * r) := rfl

section Standard
variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- The real square-minus-one generator on the standard doubled module. -/
def standardPhase : Module.End ℝ (V × V) :=
  (-LinearMap.snd ℝ V V).prod (LinearMap.fst ℝ V V)

@[simp] theorem standardPhase_apply (p : V × V) : standardPhase V p = (-p.2, p.1) := rfl

/-- The standard even/odd grading. -/
def standardGrading : Module.End ℝ (V × V) :=
  (LinearMap.fst ℝ V V).prod (-LinearMap.snd ℝ V V)

@[simp] theorem standardGrading_apply (p : V × V) : standardGrading V p = (p.1, -p.2) := rfl

@[simp] theorem standardPhase_sq : standardPhase V * standardPhase V = -1 := by
  ext p <;> simp [Module.End.mul_apply]

@[simp] theorem standardGrading_sq : standardGrading V * standardGrading V = 1 := by
  ext p <;> simp [Module.End.mul_apply]

theorem standardGrading_phase_anticommute :
    standardGrading V * standardPhase V + standardPhase V * standardGrading V = 0 := by
  ext p <;> simp [Module.End.mul_apply]

/-- The real line acts by scalar multiples of the standard Clifford generator. -/
def standardVector : ℝ →ₗ[ℝ] Module.End ℝ (V × V) where
  toFun r := r • standardPhase V
  map_add' r s := add_smul r s _
  map_smul' r s := by simp [mul_smul]

@[simp] theorem standardVector_apply (r : ℝ) :
    standardVector V r = r • standardPhase V := rfl

theorem standardVector_sq (r : ℝ) :
    standardVector V r * standardVector V r =
      algebraMap ℝ (Module.End ℝ (V × V)) (negativeQuadratic r) := by
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, Algebra.algebraMap_eq_smul_one]

/-- The native Clifford universal property constructs the full standard action. -/
def standardRepresentation :
    GradedCliffordOperatorRepresentation (R := ℝ) (M := ℝ) (W := V × V)
      (Q := negativeQuadratic) where
  representation := CliffordAlgebra.lift negativeQuadratic
    ⟨standardVector V, standardVector_sq V⟩
  grading := standardGrading V
  grading_sq := standardGrading_sq V
  generator_odd r := by
    simp only [CliffordAlgebra.lift_ι_apply, standardVector_apply]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, standardGrading_phase_anticommute,
      smul_zero]

@[simp] theorem standardRepresentation_generator (r : ℝ) :
    (standardRepresentation V).representation (ι negativeQuadratic r) =
      r • standardPhase V := by
  change CliffordAlgebra.lift negativeQuadratic
    ⟨standardVector V, standardVector_sq V⟩ (ι negativeQuadratic r) = _
  rw [CliffordAlgebra.lift_ι_apply, standardVector_apply]

end Standard

section Classification
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := ℝ) (W := W) (Q := negativeQuadratic))

/-- The actual carrier equivalence with two copies of the even subspace. -/
def toStandard : W ≃ₗ[ℝ] evenSpace ρ × evenSpace ρ :=
  (gradingDecomposition ρ).trans
    ((LinearEquiv.refl ℝ (evenSpace ρ)).prodCongr
      (symbolEquiv ρ (1 : ℝ) (by norm_num)))

/-- The inverse is the explicit standard-model reconstruction. -/
@[simp] theorem toStandard_symm_apply (p : evenSpace ρ × evenSpace ρ) :
    (toStandard ρ).symm p =
      (p.1 : W) + ρ.representation (ι negativeQuadratic 1) p.2 := by
  change (gradingDecomposition ρ).symm
      (p.1, (symbolEquiv ρ (1 : ℝ) (by norm_num)).symm p.2) = _
  rw [gradingDecomposition_symm_apply,
    symbolEquiv_symm_apply_of_neg_one ρ (1 : ℝ) _ (by norm_num)]

theorem toStandard_symm_grading (p : evenSpace ρ × evenSpace ρ) :
    ρ.grading ((toStandard ρ).symm p) =
      (toStandard ρ).symm (standardGrading (evenSpace ρ) p) := by
  rw [toStandard_symm_apply, map_add, grading_generator_apply]
  rw [(mem_evenSpace_iff ρ _).mp p.1.property,
    (mem_evenSpace_iff ρ _).mp p.2.property]
  simp [toStandard_symm_apply]

theorem toStandard_symm_phase (p : evenSpace ρ × evenSpace ρ) :
    ρ.representation (ι negativeQuadratic 1) ((toStandard ρ).symm p) =
      (toStandard ρ).symm (standardPhase (evenSpace ρ) p) := by
  rw [toStandard_symm_apply, map_add, generator_sq_apply]
  simp [toStandard_symm_apply, add_comm]

/-- The actual grading is conjugate to the standard signed grading. -/
theorem toStandard_grading (w : W) :
    toStandard ρ (ρ.grading w) = standardGrading (evenSpace ρ) (toStandard ρ w) := by
  apply (toStandard ρ).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← toStandard_symm_grading,
    LinearEquiv.symm_apply_apply]

/-- The represented generator becomes the standard real phase operator. -/
theorem toStandard_phase (w : W) :
    toStandard ρ (ρ.representation (ι negativeQuadratic 1) w) =
      standardPhase (evenSpace ρ) (toStandard ρ w) := by
  apply (toStandard ρ).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← toStandard_symm_phase,
    LinearEquiv.symm_apply_apply]

theorem toStandard_generator (r : ℝ) (w : W) :
    toStandard ρ (ρ.representation (ι negativeQuadratic r) w) =
      (standardRepresentation (evenSpace ρ)).representation
        (ι negativeQuadratic r) (toStandard ρ w) := by
  have hr : (ι negativeQuadratic r) = r • ι negativeQuadratic (1 : ℝ) := by
    simpa using (ι negativeQuadratic).map_smul r (1 : ℝ)
  rw [hr, map_smul]
  simp [toStandard_phase]

/-- Compatibility holds for the full native Clifford action, not only its generator. -/
theorem toStandard_action (a : CliffordAlgebra negativeQuadratic) (w : W) :
    toStandard ρ (ρ.representation a w) =
      (standardRepresentation (evenSpace ρ)).representation a (toStandard ρ w) := by
  induction a using CliffordAlgebra.induction generalizing w with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι r => exact toStandard_generator ρ r w
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- This is a native equivalence of modules over the whole Clifford algebra. -/
def toStandardModuleEquiv :
    letI : Module (CliffordAlgebra negativeQuadratic) W :=
      Module.compHom W ρ.representation.toRingHom
    letI : Module (CliffordAlgebra negativeQuadratic) (evenSpace ρ × evenSpace ρ) :=
      Module.compHom _ (standardRepresentation (evenSpace ρ)).representation.toRingHom
    W ≃ₗ[CliffordAlgebra negativeQuadratic] (evenSpace ρ × evenSpace ρ) := by
  letI : Module (CliffordAlgebra negativeQuadratic) W :=
    Module.compHom W ρ.representation.toRingHom
  letI : Module (CliffordAlgebra negativeQuadratic) (evenSpace ρ × evenSpace ρ) :=
    Module.compHom _ (standardRepresentation (evenSpace ρ)).representation.toRingHom
  exact
    { toAddEquiv := (toStandard ρ).toAddEquiv
      map_smul' := toStandard_action ρ }

/-- Finite graded Cl(0,1) modules have twice the dimension of their even subspace. -/
theorem finrank_eq_twice_even [FiniteDimensional ℝ W] :
    Module.finrank ℝ W = 2 * Module.finrank ℝ (evenSpace ρ) := by
  rw [(toStandard ρ).finrank_eq, Module.finrank_prod, two_mul]

end Classification

section ModuleCategory

open CategoryTheory

variable {W : Type} [AddCommGroup W] [Module ℝ W]
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := ℝ) (W := W) (Q := negativeQuadratic))

/-- The standardization is an isomorphism in the existing category of graded
modules over the native Clifford algebra, with grading compatibility proved. -/
def toStandardGradedIso :
    ρ.toGradedModule ≅ (standardRepresentation (evenSpace ρ)).toGradedModule :=
  InfoGeometry.OperatorAlgebra.GradedMatrixMorita.GradedModuleCat.isoOfUnderlying
    (toStandardModuleEquiv ρ).toModuleIso (toStandard_grading ρ)

end ModuleCategory

end InfoGeometry.Canonical.NegativeLineModuleClassification
