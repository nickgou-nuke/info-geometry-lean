/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornFiniteVectorCalculus
import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-!
# Differential forms, Hodge operator, and Clifford morphism

This is a generic finite bridge.  Forms are represented by an exterior
algebra, the Hodge operator and differential are linear maps on that carrier,
and a Clifford representation is produced by Mathlib's universal `lift` from
an explicit generator square law.  No identification of the Zorn product
with an associative Clifford target is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge

private noncomputable def witnessQ : QuadraticForm ℝ (Fin 2 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ ![1, 1]

private noncomputable def cliffordE0 : CliffordAlgebra witnessQ :=
  CliffordAlgebra.ι witnessQ ![1, 0]

private noncomputable def cliffordE1 : CliffordAlgebra witnessQ :=
  CliffordAlgebra.ι witnessQ ![0, 1]

/-- Explicit non-commutativity witness for `CliffordAlgebra`. -/
theorem clifford_noncomm_witness :
    cliffordE0 * cliffordE1 ≠ cliffordE1 * cliffordE0 := by
  intro h
  let f : (Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    { toFun := fun v => v 0 • !![1, 0; 0, -1] + v 1 • !![0, 1; 1, 0]
      map_add' := fun u v => by simp [add_smul]
      map_smul' := fun r v => by ext i j; fin_cases i <;> fin_cases j <;> simp }
  have hf : ∀ v, f v * f v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (witnessQ v) := by
    intro v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, witnessQ, QuadraticMap.weightedSumSquares_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring
  have hmap := congrArg (CliffordAlgebra.lift witnessQ ⟨f, hf⟩) h
  simp only [cliffordE0, cliffordE1, map_mul, CliffordAlgebra.lift_ι_apply] at hmap
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hmap
  norm_num [f, Matrix.mul_apply, Fin.sum_univ_two] at h01

variable {R V C : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [Semiring C] [Algebra R C]

structure FormHodgeCliffordData (R V C : Type*)
    [CommRing R] [AddCommGroup V] [Module R V]
    [Semiring C] [Algebra R C] where
  Q : QuadraticForm R V
  differential : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V
  differential_sq : differential.comp differential = 0
  hodgeStar : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V
  hodgeSquareSign : R
  hodgeStar_sq : hodgeStar.comp hodgeStar = hodgeSquareSign • LinearMap.id
  generator : V →ₗ[R] C
  generator_sq : ∀ v, generator v * generator v = algebraMap R C (Q v)

def hodgeDirac (D : FormHodgeCliffordData R V C) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  D.differential +
    LinearMap.comp D.hodgeStar (LinearMap.comp D.differential D.hodgeStar)

@[simp] theorem hodgeDirac_apply
    (D : FormHodgeCliffordData R V C)
    (ω : ExteriorAlgebra R V) :
    hodgeDirac D ω =
      D.differential ω + D.hodgeStar (D.differential (D.hodgeStar ω)) := by
  rfl

theorem differential_square_apply
    (D : FormHodgeCliffordData R V C)
    (ω : ExteriorAlgebra R V) :
    D.differential (D.differential ω) = 0 := by
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω)
    D.differential_sq
  simpa [LinearMap.comp_apply] using h

theorem hodgeStar_square_apply
    (D : FormHodgeCliffordData R V C)
    (ω : ExteriorAlgebra R V) :
    D.hodgeStar (D.hodgeStar ω) = D.hodgeSquareSign • ω := by
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω)
    D.hodgeStar_sq
  simpa [LinearMap.comp_apply] using h

theorem hodgeStar_involutive
    (D : FormHodgeCliffordData R V C)
    (hSign : D.hodgeSquareSign = 1) :
    D.hodgeStar.comp D.hodgeStar = LinearMap.id := by
  simpa [hSign] using D.hodgeStar_sq

def cliffordMorphism
    (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₐ[R] C :=
  CliffordAlgebra.lift D.Q ⟨D.generator, D.generator_sq⟩

@[simp] theorem cliffordMorphism_generator
    (D : FormHodgeCliffordData R V C) (v : V) :
    cliffordMorphism D (CliffordAlgebra.ι D.Q v) = D.generator v := by
  rw [cliffordMorphism, CliffordAlgebra.lift_ι_apply]

theorem cliffordMorphism_mul
    (D : FormHodgeCliffordData R V C)
    (x y : CliffordAlgebra D.Q) :
    cliffordMorphism D (x * y) = cliffordMorphism D x * cliffordMorphism D y := by
  exact (cliffordMorphism D).map_mul x y

theorem cliffordMorphism_one
    (D : FormHodgeCliffordData R V C) :
    cliffordMorphism D 1 = 1 := by
  exact (cliffordMorphism D).map_one

theorem cliffordMorphism_generator_square
    (D : FormHodgeCliffordData R V C) (v : V) :
    cliffordMorphism D (CliffordAlgebra.ι D.Q v) *
        cliffordMorphism D (CliffordAlgebra.ι D.Q v) =
      algebraMap R C (D.Q v) := by
  rw [cliffordMorphism_generator]
  exact D.generator_sq v

theorem hodgeDirac_sq_expansion
    (D : FormHodgeCliffordData R V C) :
    hodgeDirac D = D.differential +
      LinearMap.comp D.hodgeStar (LinearMap.comp D.differential D.hodgeStar) := by
  rfl

end InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
