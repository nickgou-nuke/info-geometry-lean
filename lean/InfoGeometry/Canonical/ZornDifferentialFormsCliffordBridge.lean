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
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.Tactic
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.CoordinateLessCliffordInvariance
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus

/-!
# Differential forms, Hodge operator, and Clifford morphism

This is a generic finite bridge.  Forms are represented by an exterior
algebra, the Hodge operator and differential are linear maps on that carrier,
and a Clifford representation is produced by Mathlib's universal `lift` from
an explicit generator square law.  No identification of the Zorn product
with an associative Clifford target is made.

In addition to the core `FormHodgeCliffordData` bridge, this module couples:
- the Hodge-Dirac calculus `(d, ★, δ = ★ d ★, d + δ)` to `CliffordAlgebra.equivExterior`,
  `cliffordGradeProj`, `hTrace_cl`, and a faithful noncommutative `chevalleyAction`;
- M2.1 coordinate-less `Q.IsometryEquiv Q` (`cliffordSymmetryAction`) equivariance;
- R1 `DerivationExteriorCalculus` (`ActionOperatorForm` / `DerivationOperatorForm`) via
  `ExteriorAlgebra.liftAlternating`, `cliffordGradeProj`, and `cliffordMorphism`.
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

/-! ## Section A: Hodge Codifferential and Nilpotent Hodge–Dirac Square -/

section HodgeCodifferential

/-- Codifferential `δ := ★ ∘ d ∘ ★` on `ExteriorAlgebra R V`. -/
def hodgeCodifferential (D : FormHodgeCliffordData R V C) :
    ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V :=
  D.hodgeStar.comp (D.differential.comp D.hodgeStar)

@[simp] theorem hodgeCodifferential_apply (D : FormHodgeCliffordData R V C)
    (ω : ExteriorAlgebra R V) :
    hodgeCodifferential D ω = D.hodgeStar (D.differential (D.hodgeStar ω)) :=
  rfl

theorem hodgeDirac_eq_add_codifferential (D : FormHodgeCliffordData R V C) :
    hodgeDirac D = D.differential + hodgeCodifferential D :=
  rfl

/-- Nilpotency of the codifferential: `δ ∘ δ = 0`, using `★² = σ · id` and `d² = 0`. -/
theorem hodgeCodifferential_sq (D : FormHodgeCliffordData R V C) :
    (hodgeCodifferential D).comp (hodgeCodifferential D) = 0 := by
  refine LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, hodgeCodifferential_apply, hodgeCodifferential_apply,
    hodgeStar_square_apply, map_smul, differential_square_apply, smul_zero, map_zero,
    LinearMap.zero_apply]

/-- Hodge–Dirac Laplacian expansion: `(d + δ)² = d ∘ δ + δ ∘ d`. -/
theorem hodgeDirac_comp_hodgeDirac (D : FormHodgeCliffordData R V C) :
    (hodgeDirac D).comp (hodgeDirac D) =
      D.differential.comp (hodgeCodifferential D) +
        (hodgeCodifferential D).comp D.differential := by
  rw [hodgeDirac_eq_add_codifferential, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.comp_add, D.differential_sq, hodgeCodifferential_sq, zero_add, add_zero]

/-- Explicit noncommutative constructive inhabitant of `FormHodgeCliffordData` over `M₂(ℝ)`
with nonzero nilpotent exterior multiplication differential (`d² = 0`). -/
def witnessFormHodgeCliffordData :
    FormHodgeCliffordData ℝ (Fin 2 → ℝ) (Matrix (Fin 2) (Fin 2) ℝ) where
  Q := witnessQ
  differential := LinearMap.mul ℝ (ExteriorAlgebra ℝ (Fin 2 → ℝ)) (ExteriorAlgebra.ι ℝ ![1, 0])
  differential_sq := by
    refine LinearMap.ext fun ω => ?_
    change ExteriorAlgebra.ι ℝ ![1, 0] * (ExteriorAlgebra.ι ℝ ![1, 0] * ω) = 0
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  hodgeStar := LinearMap.id
  hodgeSquareSign := 1
  hodgeStar_sq := by
    refine LinearMap.ext fun ω => ?_
    simp
  generator :=
    { toFun := fun v => v 0 • !![1, 0; 0, -1] + v 1 • !![0, 1; 1, 0]
      map_add' := fun u v => by simp [add_smul]
      map_smul' := fun r v => by ext i j; fin_cases i <;> fin_cases j <;> simp }
  generator_sq := fun v => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [witnessQ, QuadraticMap.weightedSumSquares_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring

end HodgeCodifferential

/-! ## Section B: `equivExterior`, `cliffordGradeProj`, `hTrace_cl`, and Chevalley Action -/

section CliffordExteriorCoupling

open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Riemannian

variable [Invertible (2 : R)]

/-- Differential `d` transported onto `CliffordAlgebra D.Q` across `equivExterior D.Q`. -/
def cliffordDifferential (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₗ[R] CliffordAlgebra D.Q :=
  (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap.comp
    (D.differential.comp (CliffordAlgebra.equivExterior D.Q).toLinearMap)

/-- Hodge star `★` transported onto `CliffordAlgebra D.Q` across `equivExterior D.Q`. -/
def cliffordHodgeStar (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₗ[R] CliffordAlgebra D.Q :=
  (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap.comp
    (D.hodgeStar.comp (CliffordAlgebra.equivExterior D.Q).toLinearMap)

/-- Codifferential `δ = ★ ∘ d ∘ ★` transported onto `CliffordAlgebra D.Q`. -/
def cliffordCodifferential (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₗ[R] CliffordAlgebra D.Q :=
  (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap.comp
    ((hodgeCodifferential D).comp (CliffordAlgebra.equivExterior D.Q).toLinearMap)

/-- Hodge–Dirac operator `d + δ` transported onto `CliffordAlgebra D.Q`. -/
def cliffordHodgeDirac (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₗ[R] CliffordAlgebra D.Q :=
  (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap.comp
    ((hodgeDirac D).comp (CliffordAlgebra.equivExterior D.Q).toLinearMap)

@[simp] theorem equivExterior_cliffordDifferential (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivExterior D.Q (cliffordDifferential D x) =
      D.differential (CliffordAlgebra.equivExterior D.Q x) := by
  exact (CliffordAlgebra.equivExterior D.Q).apply_symm_apply _

@[simp] theorem equivExterior_cliffordHodgeStar (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivExterior D.Q (cliffordHodgeStar D x) =
      D.hodgeStar (CliffordAlgebra.equivExterior D.Q x) := by
  exact (CliffordAlgebra.equivExterior D.Q).apply_symm_apply _

@[simp] theorem equivExterior_cliffordCodifferential (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivExterior D.Q (cliffordCodifferential D x) =
      hodgeCodifferential D (CliffordAlgebra.equivExterior D.Q x) := by
  exact (CliffordAlgebra.equivExterior D.Q).apply_symm_apply _

@[simp] theorem equivExterior_cliffordHodgeDirac (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivExterior D.Q (cliffordHodgeDirac D x) =
      hodgeDirac D (CliffordAlgebra.equivExterior D.Q x) := by
  exact (CliffordAlgebra.equivExterior D.Q).apply_symm_apply _

theorem cliffordDifferential_sq (D : FormHodgeCliffordData R V C) :
    (cliffordDifferential D).comp (cliffordDifferential D) = 0 := by
  ext x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [LinearMap.comp_apply, equivExterior_cliffordDifferential, equivExterior_cliffordDifferential,
    differential_square_apply, LinearMap.zero_apply, map_zero]

theorem cliffordHodgeStar_sq (D : FormHodgeCliffordData R V C) :
    (cliffordHodgeStar D).comp (cliffordHodgeStar D) = D.hodgeSquareSign • LinearMap.id := by
  ext x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [LinearMap.comp_apply, equivExterior_cliffordHodgeStar, equivExterior_cliffordHodgeStar,
    hodgeStar_square_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

theorem cliffordCodifferential_sq (D : FormHodgeCliffordData R V C) :
    (cliffordCodifferential D).comp (cliffordCodifferential D) = 0 := by
  ext x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V =>
      f (CliffordAlgebra.equivExterior D.Q x)) (hodgeCodifferential_sq D)
  rw [LinearMap.comp_apply, equivExterior_cliffordCodifferential,
    equivExterior_cliffordCodifferential, LinearMap.zero_apply, map_zero]
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

theorem cliffordHodgeDirac_eq_add (D : FormHodgeCliffordData R V C) :
    cliffordHodgeDirac D = cliffordDifferential D + cliffordCodifferential D := by
  ext x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [LinearMap.add_apply, map_add, equivExterior_cliffordHodgeDirac,
    equivExterior_cliffordDifferential, equivExterior_cliffordCodifferential,
    hodgeDirac_apply, hodgeCodifferential_apply]

theorem cliffordHodgeDirac_comp_cliffordHodgeDirac (D : FormHodgeCliffordData R V C) :
    (cliffordHodgeDirac D).comp (cliffordHodgeDirac D) =
      (cliffordDifferential D).comp (cliffordCodifferential D) +
        (cliffordCodifferential D).comp (cliffordDifferential D) := by
  ext x
  apply (CliffordAlgebra.equivExterior D.Q).injective
  have h := congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V =>
      f (CliffordAlgebra.equivExterior D.Q x)) (hodgeDirac_comp_hodgeDirac D)
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    map_add, equivExterior_cliffordHodgeDirac, equivExterior_cliffordHodgeDirac,
    equivExterior_cliffordDifferential, equivExterior_cliffordCodifferential,
    equivExterior_cliffordCodifferential, equivExterior_cliffordDifferential]
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using h

/-- Faithful noncommutative Chevalley representation of `CliffordAlgebra D.Q`
acting on `ExteriorAlgebra R V` by conjugating left multiplication across
`CliffordAlgebra.equivExterior D.Q`. -/
def chevalleyAction (D : FormHodgeCliffordData R V C) :
    CliffordAlgebra D.Q →ₐ[R] Module.End R (ExteriorAlgebra R V) where
  toFun a :=
    (CliffordAlgebra.equivExterior D.Q).toLinearMap.comp
      ((LinearMap.mul R (CliffordAlgebra D.Q) a).comp
        (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap)
  map_one' := by
    refine LinearMap.ext fun ω => ?_
    change (CliffordAlgebra.equivExterior D.Q)
        (1 * (CliffordAlgebra.equivExterior D.Q).symm ω) = ω
    rw [one_mul, LinearEquiv.apply_symm_apply]
  map_mul' a b := by
    refine LinearMap.ext fun ω => ?_
    change (CliffordAlgebra.equivExterior D.Q)
        ((a * b) * (CliffordAlgebra.equivExterior D.Q).symm ω) =
      (CliffordAlgebra.equivExterior D.Q)
        (a * (CliffordAlgebra.equivExterior D.Q).symm
          ((CliffordAlgebra.equivExterior D.Q)
            (b * (CliffordAlgebra.equivExterior D.Q).symm ω)))
    rw [LinearEquiv.symm_apply_apply, mul_assoc]
  map_zero' := by
    refine LinearMap.ext fun ω => ?_
    simp
  map_add' a b := by
    refine LinearMap.ext fun ω => ?_
    change (CliffordAlgebra.equivExterior D.Q)
        ((a + b) * (CliffordAlgebra.equivExterior D.Q).symm ω) =
      (CliffordAlgebra.equivExterior D.Q) (a * (CliffordAlgebra.equivExterior D.Q).symm ω) +
        (CliffordAlgebra.equivExterior D.Q) (b * (CliffordAlgebra.equivExterior D.Q).symm ω)
    rw [add_mul, map_add]
  commutes' r := by
    refine LinearMap.ext fun ω => ?_
    change (CliffordAlgebra.equivExterior D.Q)
        (algebraMap R (CliffordAlgebra D.Q) r * (CliffordAlgebra.equivExterior D.Q).symm ω) =
      r • ω
    rw [← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply]

@[simp] theorem chevalleyAction_apply (D : FormHodgeCliffordData R V C)
    (a : CliffordAlgebra D.Q) (ω : ExteriorAlgebra R V) :
    chevalleyAction D a ω =
      CliffordAlgebra.equivExterior D.Q
        (a * (CliffordAlgebra.equivExterior D.Q).symm ω) :=
  rfl

@[simp] theorem chevalleyAction_one_apply (D : FormHodgeCliffordData R V C)
    (a : CliffordAlgebra D.Q) :
    chevalleyAction D a 1 = CliffordAlgebra.equivExterior D.Q a := by
  rw [chevalleyAction_apply]
  have h1 : (CliffordAlgebra.equivExterior D.Q).symm (1 : ExteriorAlgebra R V) = 1 := by
    apply (CliffordAlgebra.equivExterior D.Q).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (equivExterior_algebraMap D.Q (1 : R)).symm
  rw [h1, mul_one]

theorem chevalleyAction_injective (D : FormHodgeCliffordData R V C) :
    Function.Injective (chevalleyAction D) := by
  intro a b hab
  have h := congrArg (fun f : Module.End R (ExteriorAlgebra R V) => f 1) hab
  rw [chevalleyAction_one_apply, chevalleyAction_one_apply] at h
  exact (CliffordAlgebra.equivExterior D.Q).injective h

/-- The Chevalley action preserves noncommutativity on the concrete witness `witnessQ`. -/
theorem chevalleyAction_noncomm_witness
    (D : FormHodgeCliffordData ℝ (Fin 2 → ℝ) (Matrix (Fin 2) (Fin 2) ℝ))
    (hQ : D.Q = witnessQ) :
    chevalleyAction D (hQ ▸ cliffordE0) * chevalleyAction D (hQ ▸ cliffordE1) ≠
      chevalleyAction D (hQ ▸ cliffordE1) * chevalleyAction D (hQ ▸ cliffordE0) := by
  rcases D with ⟨Q, diff, hdiff, star, sign, hstar, gen, hgen⟩
  dsimp at hQ
  subst hQ
  intro h
  dsimp only at h
  exact clifford_noncomm_witness
    (chevalleyAction_injective ⟨witnessQ, diff, hdiff, star, sign, hstar, gen, hgen⟩
      (by rw [map_mul, map_mul]; exact h))

theorem chevalleyAction_ι_sq (D : FormHodgeCliffordData R V C) (v : V) :
    chevalleyAction D (CliffordAlgebra.ι D.Q v) *
        chevalleyAction D (CliffordAlgebra.ι D.Q v) =
      D.Q v • 1 := by
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one]

theorem chevalleyAction_cliffordGradeProj_one (D : FormHodgeCliffordData R V C)
    (k : ℕ) (a : CliffordAlgebra D.Q) :
    chevalleyAction D (cliffordGradeProj D.Q k a) 1 =
      exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q a) := by
  rw [chevalleyAction_one_apply]
  change CliffordAlgebra.equivExterior D.Q
      ((CliffordAlgebra.equivExterior D.Q).symm
        (exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q a))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Grade-`k` component of `cliffordMorphism D` via `cliffordGradeProj D.Q k`. -/
def cliffordMorphismGrade (D : FormHodgeCliffordData R V C) (k : ℕ) :
    CliffordAlgebra D.Q →ₗ[R] C :=
  (cliffordMorphism D).toLinearMap.comp (cliffordGradeProj D.Q k)

/-- Exterior symbol of `cliffordMorphism D` transported across `(equivExterior D.Q).symm`. -/
def exteriorToTarget (D : FormHodgeCliffordData R V C) :
    ExteriorAlgebra R V →ₗ[R] C :=
  (cliffordMorphism D).toLinearMap.comp (CliffordAlgebra.equivExterior D.Q).symm.toLinearMap

@[simp] theorem cliffordMorphismGrade_apply (D : FormHodgeCliffordData R V C)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    cliffordMorphismGrade D k x = cliffordMorphism D (cliffordGradeProj D.Q k x) :=
  rfl

@[simp] theorem exteriorToTarget_apply (D : FormHodgeCliffordData R V C)
    (ω : ExteriorAlgebra R V) :
    exteriorToTarget D ω = cliffordMorphism D ((CliffordAlgebra.equivExterior D.Q).symm ω) :=
  rfl

@[simp] theorem exteriorToTarget_equivExterior (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    exteriorToTarget D (CliffordAlgebra.equivExterior D.Q x) = cliffordMorphism D x := by
  change cliffordMorphism D ((CliffordAlgebra.equivExterior D.Q).symm
      (CliffordAlgebra.equivExterior D.Q x)) = cliffordMorphism D x
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem exteriorToTarget_ι (D : FormHodgeCliffordData R V C) (v : V) :
    exteriorToTarget D (ExteriorAlgebra.ι R v) = D.generator v := by
  rw [exteriorToTarget_apply, ← equivExterior_ι D.Q v, LinearEquiv.symm_apply_apply,
    cliffordMorphism_generator]

theorem exteriorToTarget_ι_sq (D : FormHodgeCliffordData R V C) (v : V) :
    exteriorToTarget D (ExteriorAlgebra.ι R v) *
        exteriorToTarget D (ExteriorAlgebra.ι R v) =
      algebraMap R C (D.Q v) := by
  rw [exteriorToTarget_ι]
  exact D.generator_sq v

/-- Grade-0 component of `cliffordMorphism D` equals the scalar trace `hTrace_cl D.Q`. -/
theorem cliffordMorphismGrade_zero (D : FormHodgeCliffordData R V C)
    (x : CliffordAlgebra D.Q) :
    cliffordMorphismGrade D 0 x = algebraMap R C (hTrace_cl D.Q x) := by
  rw [cliffordMorphismGrade_apply, cliffordGradeProj_zero_eq_algebraMap_hTrace,
    (cliffordMorphism D).commutes]

/-- Grade-1 component of `cliffordMorphism D` evaluates identically to `D.generator` on `ι`. -/
theorem cliffordMorphismGrade_one_ι (D : FormHodgeCliffordData R V C) (v : V) :
    cliffordMorphismGrade D 1 (CliffordAlgebra.ι D.Q v) = D.generator v := by
  rw [cliffordMorphismGrade_apply, cliffordGradeProj_one_ι, cliffordMorphism_generator]

theorem cliffordGradeProj_cliffordDifferential (D : FormHodgeCliffordData R V C)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    cliffordGradeProj D.Q k (cliffordDifferential D x) =
      (CliffordAlgebra.equivExterior D.Q).symm
        (exteriorGradeProj R V k (D.differential (CliffordAlgebra.equivExterior D.Q x))) := by
  change (CliffordAlgebra.equivExterior D.Q).symm
      (exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q (cliffordDifferential D x))) = _
  rw [equivExterior_cliffordDifferential]

theorem cliffordGradeProj_cliffordHodgeStar (D : FormHodgeCliffordData R V C)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    cliffordGradeProj D.Q k (cliffordHodgeStar D x) =
      (CliffordAlgebra.equivExterior D.Q).symm
        (exteriorGradeProj R V k (D.hodgeStar (CliffordAlgebra.equivExterior D.Q x))) := by
  change (CliffordAlgebra.equivExterior D.Q).symm
      (exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q (cliffordHodgeStar D x))) = _
  rw [equivExterior_cliffordHodgeStar]

theorem cliffordGradeProj_cliffordHodgeDirac (D : FormHodgeCliffordData R V C)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    cliffordGradeProj D.Q k (cliffordHodgeDirac D x) =
      (CliffordAlgebra.equivExterior D.Q).symm
        (exteriorGradeProj R V k (hodgeDirac D (CliffordAlgebra.equivExterior D.Q x))) := by
  change (CliffordAlgebra.equivExterior D.Q).symm
      (exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q (cliffordHodgeDirac D x))) = _
  rw [equivExterior_cliffordHodgeDirac]

/-- Grade-raising compatibility: if `D.differential` maps `⋀^k V` into `⋀^(k + 1) V`,
then `cliffordDifferential D` maps the grade-`k` Clifford projection into grade `k + 1`
with vanishing scalar trace `hTrace_cl`. -/
theorem cliffordDifferential_grade_raising (D : FormHodgeCliffordData R V C)
    (hd : ∀ (k : ℕ) (ω : ExteriorAlgebra R V),
      ω ∈ ⋀[R]^k V → D.differential ω ∈ ⋀[R]^(k + 1) V)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    cliffordGradeProj D.Q (k + 1) (cliffordDifferential D (cliffordGradeProj D.Q k x)) =
      cliffordDifferential D (cliffordGradeProj D.Q k x) := by
  have hmem :
      CliffordAlgebra.equivExterior D.Q (cliffordGradeProj D.Q k x) ∈ ⋀[R]^k V := by
    change CliffordAlgebra.equivExterior D.Q
        ((CliffordAlgebra.equivExterior D.Q).symm
          (exteriorGradeProj R V k (CliffordAlgebra.equivExterior D.Q x))) ∈ ⋀[R]^k V
    rw [LinearEquiv.apply_symm_apply]
    exact exteriorGradeProj_mem R V k _
  have hdmem := hd k _ hmem
  rw [cliffordGradeProj_cliffordDifferential, exteriorGradeProj_of_mem hdmem,
    ← equivExterior_cliffordDifferential, LinearEquiv.symm_apply_apply]

theorem hTrace_cl_cliffordDifferential_grade_eq_zero (D : FormHodgeCliffordData R V C)
    (hd : ∀ (k : ℕ) (ω : ExteriorAlgebra R V),
      ω ∈ ⋀[R]^k V → D.differential ω ∈ ⋀[R]^(k + 1) V)
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    hTrace_cl D.Q (cliffordDifferential D (cliffordGradeProj D.Q k x)) = 0 := by
  rw [← cliffordDifferential_grade_raising D hd k x]
  exact hTrace_cliffordGradeProj_succ D.Q k _

section RealFiniteGradeDecomposition

variable {V_real C_real : Type*}
variable [AddCommGroup V_real] [Module ℝ V_real] [Module.Finite ℝ V_real]
variable [Semiring C_real] [Algebra ℝ C_real]

/-- Over a finite-dimensional real space, `cliffordMorphism D` resolves as the finite sum
of its grade projections `cliffordMorphismGrade D k` for `k ≤ Module.finrank ℝ V_real`. -/
theorem cliffordMorphism_eq_sum_cliffordMorphismGrade
    (D : FormHodgeCliffordData ℝ V_real C_real) (x : CliffordAlgebra D.Q) :
    cliffordMorphism D x =
      ∑ k ∈ Finset.range (Module.finrank ℝ V_real + 1), cliffordMorphismGrade D k x := by
  calc
    cliffordMorphism D x
        = cliffordMorphism D
            (∑ k ∈ Finset.range (Module.finrank ℝ V_real + 1), cliffordGradeProj D.Q k x) := by
          rw [cliffordGradeProj_sum_range_apply D.Q x]
    _ = ∑ k ∈ Finset.range (Module.finrank ℝ V_real + 1), cliffordMorphismGrade D k x := by
          rw [map_sum]
          rfl

end RealFiniteGradeDecomposition

end CliffordExteriorCoupling

/-! ## Section C: M2.1 Coordinate-Less `O(Q)` Isometry Equivariance -/

section IsometryEquivariance

open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.OperatorAlgebra

variable [Invertible (2 : R)]

/-- The Chevalley Clifford action is equivariant under every `g : D.Q.IsometryEquiv D.Q`. -/
theorem chevalleyAction_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (a : CliffordAlgebra D.Q) (ω : ExteriorAlgebra R V) :
    ExteriorAlgebra.map (g : V →ₗ[R] V) (chevalleyAction D a ω) =
      chevalleyAction D ((cliffordSymmetryAction D.Q).act g a)
        (ExteriorAlgebra.map (g : V →ₗ[R] V) ω) := by
  rw [chevalleyAction_apply, chevalleyAction_apply, cliffordSymmetryAction_act_apply,
    ← equivExterior_equivOfIsometry g, map_mul (CliffordAlgebra.equivOfIsometry g),
    equivExterior_symm_equivOfIsometry g ω]

/-- Equivariance of `cliffordDifferential D` when `D.differential` commutes with `ExteriorAlgebra.map g`. -/
theorem cliffordDifferential_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q)
    (hd : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.differential =
      D.differential.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap)
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivOfIsometry g (cliffordDifferential D x) =
      cliffordDifferential D (CliffordAlgebra.equivOfIsometry g x) := by
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [equivExterior_equivOfIsometry, equivExterior_cliffordDifferential,
    equivExterior_cliffordDifferential, equivExterior_equivOfIsometry]
  exact congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V =>
    f (CliffordAlgebra.equivExterior D.Q x)) hd

/-- Equivariance of `cliffordHodgeStar D` with parity sign `ε : R` (e.g. `ε = det g`). -/
theorem cliffordHodgeStar_equivOfIsometry_of_sign (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (ε : R)
    (hs : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.hodgeStar =
      ε • (D.hodgeStar.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap))
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivOfIsometry g (cliffordHodgeStar D x) =
      ε • cliffordHodgeStar D (CliffordAlgebra.equivOfIsometry g x) := by
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [equivExterior_equivOfIsometry, equivExterior_cliffordHodgeStar, map_smul,
    equivExterior_cliffordHodgeStar, equivExterior_equivOfIsometry]
  exact congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V =>
    f (CliffordAlgebra.equivExterior D.Q x)) hs

/-- When `d` is `g`-equivariant and `★` transforms by `ε` with `ε * ε = 1`,
`cliffordHodgeDirac D` is strictly `g`-equivariant. -/
theorem cliffordHodgeDirac_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (ε : R) (hε : ε * ε = 1)
    (hd : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.differential =
      D.differential.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap)
    (hs : (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.comp D.hodgeStar =
      ε • (D.hodgeStar.comp (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap))
    (x : CliffordAlgebra D.Q) :
    CliffordAlgebra.equivOfIsometry g (cliffordHodgeDirac D x) =
      cliffordHodgeDirac D (CliffordAlgebra.equivOfIsometry g x) := by
  have hd_apply : ∀ ω, ExteriorAlgebra.map (g : V →ₗ[R] V) (D.differential ω) =
      D.differential (ExteriorAlgebra.map (g : V →ₗ[R] V) ω) := fun ω =>
    congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω) hd
  have hs_apply : ∀ ω, ExteriorAlgebra.map (g : V →ₗ[R] V) (D.hodgeStar ω) =
      ε • D.hodgeStar (ExteriorAlgebra.map (g : V →ₗ[R] V) ω) := fun ω =>
    congrArg (fun f : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V => f ω) hs
  apply (CliffordAlgebra.equivExterior D.Q).injective
  rw [equivExterior_equivOfIsometry, equivExterior_cliffordHodgeDirac,
    equivExterior_cliffordHodgeDirac, equivExterior_equivOfIsometry,
    hodgeDirac_apply, hodgeDirac_apply, map_add, hd_apply,
    hs_apply, hd_apply, hs_apply, D.differential.map_smul, D.hodgeStar.map_smul,
    smul_smul, hε, one_smul]

omit [Invertible (2 : R)] in
/-- Equivariance of `cliffordMorphism D` against an algebra automorphism `φ : C ≃ₐ[R] C`
implementing `g` on the generators. -/
theorem cliffordMorphism_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (φ : C ≃ₐ[R] C)
    (hgen : ∀ v : V, φ (D.generator v) = D.generator (g v)) :
    φ.toAlgHom.comp (cliffordMorphism D) =
      (cliffordMorphism D).comp (CliffordAlgebra.equivOfIsometry g).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  ext v
  change φ (cliffordMorphism D (CliffordAlgebra.ι D.Q v)) =
    cliffordMorphism D (CliffordAlgebra.equivOfIsometry g (CliffordAlgebra.ι D.Q v))
  rw [cliffordMorphism_generator, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι, cliffordMorphism_generator]
  exact hgen v

theorem cliffordMorphismGrade_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (φ : C ≃ₐ[R] C)
    (hgen : ∀ v : V, φ (D.generator v) = D.generator (g v))
    (k : ℕ) (x : CliffordAlgebra D.Q) :
    φ (cliffordMorphismGrade D k x) =
      cliffordMorphismGrade D k ((cliffordSymmetryAction D.Q).act g x) := by
  have hm := AlgHom.congr_fun (cliffordMorphism_equivOfIsometry D g φ hgen)
    (cliffordGradeProj D.Q k x)
  change φ (cliffordMorphism D (cliffordGradeProj D.Q k x)) =
    cliffordMorphism D (CliffordAlgebra.equivOfIsometry g (cliffordGradeProj D.Q k x)) at hm
  rw [cliffordMorphismGrade_apply, hm, cliffordGradeProj_equivOfIsometry,
    cliffordSymmetryAction_act_apply, cliffordMorphismGrade_apply]

theorem cliffordMorphismGrade_zero_equivOfIsometry (D : FormHodgeCliffordData R V C)
    (g : D.Q.IsometryEquiv D.Q) (x : CliffordAlgebra D.Q) :
    cliffordMorphismGrade D 0 ((cliffordSymmetryAction D.Q).act g x) =
      cliffordMorphismGrade D 0 x := by
  rw [cliffordMorphismGrade_zero, cliffordMorphismGrade_zero,
    cliffordSymmetryAction_act_apply, hTrace_cl_equivOfIsometry]

end IsometryEquivariance

/-! ## Section D: R1 ↔ R3 Coupling (`DerivationExteriorCalculus` ↔ `FormHodgeCliffordData`) -/

section R1R3Coupling

open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.CoordinateLessCliffordInvariance
open InfoGeometry.Riemannian
open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

section ExteriorAlternatingLifting

variable [Invertible (2 : R)]

/-- Evaluate a family of R1 alternating forms `ω : ∀ i, V [⋀^Fin i]→ₗ[R] A`
on `CliffordAlgebra D.Q` via `ExteriorAlgebra.liftAlternating` and `equivExterior D.Q`. -/
def cliffordAlternatingEval (D : FormHodgeCliffordData R V C)
    {A : Type*} [AddCommGroup A] [Module R A]
    (ω : ∀ i : ℕ, V [⋀^Fin i]→ₗ[R] A) :
    CliffordAlgebra D.Q →ₗ[R] A :=
  (ExteriorAlgebra.liftAlternating ω).comp (CliffordAlgebra.equivExterior D.Q).toLinearMap

@[simp] theorem cliffordAlternatingEval_one (D : FormHodgeCliffordData R V C)
    {A : Type*} [AddCommGroup A] [Module R A]
    (ω : ∀ i : ℕ, V [⋀^Fin i]→ₗ[R] A) :
    cliffordAlternatingEval D ω 1 = ω 0 0 := by
  change ExteriorAlgebra.liftAlternating ω (CliffordAlgebra.equivExterior D.Q (1 : CliffordAlgebra D.Q)) = ω 0 0
  have h1 : CliffordAlgebra.equivExterior D.Q (1 : CliffordAlgebra D.Q) = 1 := by
    simpa only [map_one] using equivExterior_algebraMap D.Q (1 : R)
  rw [h1, ExteriorAlgebra.liftAlternating_one]

@[simp] theorem cliffordAlternatingEval_ι (D : FormHodgeCliffordData R V C)
    {A : Type*} [AddCommGroup A] [Module R A]
    (ω : ∀ i : ℕ, V [⋀^Fin i]→ₗ[R] A) (v : V) :
    cliffordAlternatingEval D ω (CliffordAlgebra.ι D.Q v) = ω 1 ![v] := by
  change ExteriorAlgebra.liftAlternating ω (CliffordAlgebra.equivExterior D.Q (CliffordAlgebra.ι D.Q v)) = _
  rw [equivExterior_ι, ExteriorAlgebra.liftAlternating_ι]

theorem cliffordAlternatingEval_equivOfIsometry (D : FormHodgeCliffordData R V C)
    {A : Type*} [AddCommGroup A] [Module R A]
    (ω : ∀ i : ℕ, V [⋀^Fin i]→ₗ[R] A) (g : D.Q.IsometryEquiv D.Q)
    (x : CliffordAlgebra D.Q) :
    cliffordAlternatingEval D ω ((cliffordSymmetryAction D.Q).act g x) =
      cliffordAlternatingEval D
        (fun i => (ExteriorAlgebra.liftAlternating ω).compAlternatingMap
          ((ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.compAlternatingMap
            (ExteriorAlgebra.ιMulti R i))) x := by
  change ExteriorAlgebra.liftAlternating ω
      (CliffordAlgebra.equivExterior D.Q ((cliffordSymmetryAction D.Q).act g x)) =
    ExteriorAlgebra.liftAlternating _ (CliffordAlgebra.equivExterior D.Q x)
  rw [cliffordSymmetryAction_act_apply, equivExterior_equivOfIsometry]
  have hl : (ExteriorAlgebra.liftAlternating ω).comp
        (ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap =
      ExteriorAlgebra.liftAlternating
        (fun i => (ExteriorAlgebra.liftAlternating ω).compAlternatingMap
          ((ExteriorAlgebra.map (g : V →ₗ[R] V)).toLinearMap.compAlternatingMap
            (ExteriorAlgebra.ιMulti R i))) := by
    apply ExteriorAlgebra.lhom_ext
    intro i
    rw [ExteriorAlgebra.liftAlternating_comp_ιMulti]
    rfl
  exact congrArg (fun f : ExteriorAlgebra R V →ₗ[R] A =>
    f (CliffordAlgebra.equivExterior D.Q x)) hl

/-- Pullback of an R1 alternating form family along an exterior endomorphism `T`. -/
def pullbackFormFamily {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (T : ExteriorAlgebra R K.L →ₗ[R] ExteriorAlgebra R K.L)
    (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    ∀ i : ℕ, ActionOperatorForm K i :=
  fun i => ((ExteriorAlgebra.liftAlternating ω).comp T).compAlternatingMap
    (ExteriorAlgebra.ιMulti R i)

omit [Invertible (2 : R)] in
theorem liftAlternating_pullbackFormFamily {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (T : ExteriorAlgebra R K.L →ₗ[R] ExteriorAlgebra R K.L)
    (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    ExteriorAlgebra.liftAlternating (pullbackFormFamily T ω) =
      (ExteriorAlgebra.liftAlternating ω).comp T := by
  apply ExteriorAlgebra.lhom_ext
  intro i
  rw [ExteriorAlgebra.liftAlternating_comp_ιMulti]
  rfl

omit [Invertible (2 : R)] in
theorem pullbackFormFamily_comp {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (T₁ T₂ : ExteriorAlgebra R K.L →ₗ[R] ExteriorAlgebra R K.L)
    (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    pullbackFormFamily (T₁.comp T₂) ω =
      pullbackFormFamily T₂ (pullbackFormFamily T₁ ω) := by
  funext i
  dsimp [pullbackFormFamily]
  rw [liftAlternating_pullbackFormFamily]
  rfl

omit [Invertible (2 : R)] in
theorem pullbackFormFamily_differential_sq {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (D : FormHodgeCliffordData R K.L C)
    (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    pullbackFormFamily D.differential (pullbackFormFamily D.differential ω) = 0 := by
  rw [← pullbackFormFamily_comp, D.differential_sq]
  funext i
  ext v
  simp [pullbackFormFamily]

omit [Invertible (2 : R)] in
theorem pullbackFormFamily_exteriorGradeProj_eq {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (k : ℕ) (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    pullbackFormFamily (exteriorGradeProj R K.L k) ω k = ω k := by
  ext v
  dsimp [pullbackFormFamily]
  have hmem : ExteriorAlgebra.ιMulti R k v ∈ ⋀[R]^k K.L :=
    ExteriorAlgebra.ιMulti_range R k ⟨v, rfl⟩
  rw [exteriorGradeProj_of_mem hmem, ExteriorAlgebra.liftAlternating_apply_ιMulti]

omit [Invertible (2 : R)] in
theorem pullbackFormFamily_exteriorGradeProj_ne {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    {j k : ℕ} (hjk : j ≠ k) (ω : ∀ i : ℕ, ActionOperatorForm K i) :
    pullbackFormFamily (exteriorGradeProj R K.L k) ω j = 0 := by
  ext v
  dsimp [pullbackFormFamily]
  have hmem : ExteriorAlgebra.ιMulti R j v ∈ ⋀[R]^j K.L :=
    ExteriorAlgebra.ιMulti_range R j ⟨v, rfl⟩
  rw [exteriorGradeProj_of_mem_ne hjk hmem, map_zero]

theorem cliffordAlternatingEval_cliffordGradeProj {A : Type*} [AddCommGroup A] [Module R A]
    {K : LieActionLane R A}
    (D : FormHodgeCliffordData R K.L C) (k : ℕ)
    (ω : ∀ i : ℕ, ActionOperatorForm K i) (x : CliffordAlgebra D.Q) :
    cliffordAlternatingEval D ω (cliffordGradeProj D.Q k x) =
      cliffordAlternatingEval D (pullbackFormFamily (exteriorGradeProj R K.L k) ω) x := by
  change ExteriorAlgebra.liftAlternating ω
      (CliffordAlgebra.equivExterior D.Q
        ((CliffordAlgebra.equivExterior D.Q).symm
          (exteriorGradeProj R K.L k (CliffordAlgebra.equivExterior D.Q x)))) =
    ExteriorAlgebra.liftAlternating (pullbackFormFamily (exteriorGradeProj R K.L k) ω)
      (CliffordAlgebra.equivExterior D.Q x)
  rw [LinearEquiv.apply_symm_apply, liftAlternating_pullbackFormFamily]
  rfl

end ExteriorAlternatingLifting

section CliffordValuedR1Forms

variable [Invertible (2 : R)]

/-- Grade-`m` projection of a `CliffordAlgebra D.Q`-valued R1 alternating `n`-form. -/
def cliffordGradeProjForm (D : FormHodgeCliffordData R V C)
    (K : LieActionLane R (CliffordAlgebra D.Q)) (m n : ℕ) :
    ActionOperatorForm K n →ₗ[R] ActionOperatorForm K n where
  toFun ω := (cliffordGradeProj D.Q m).compAlternatingMap ω
  map_add' ω₁ ω₂ := by ext v; simp
  map_smul' c ω := by ext v; simp

@[simp] theorem cliffordGradeProjForm_apply (D : FormHodgeCliffordData R V C)
    (K : LieActionLane R (CliffordAlgebra D.Q)) (m n : ℕ)
    (ω : ActionOperatorForm K n) (v : Fin n → K.L) :
    cliffordGradeProjForm D K m n ω v = cliffordGradeProj D.Q m (ω v) :=
  rfl

/-- Scalar `hTrace_cl` readout of a `CliffordAlgebra D.Q`-valued R1 alternating `n`-form. -/
def cliffordHTraceForm (D : FormHodgeCliffordData R V C)
    (K : LieActionLane R (CliffordAlgebra D.Q)) (n : ℕ) :
    ActionOperatorForm K n →ₗ[R] (K.L [⋀^Fin n]→ₗ[R] R) where
  toFun ω := (hTrace_cl D.Q).compAlternatingMap ω
  map_add' ω₁ ω₂ := by ext v; simp
  map_smul' c ω := by ext v; simp

@[simp] theorem cliffordHTraceForm_apply (D : FormHodgeCliffordData R V C)
    (K : LieActionLane R (CliffordAlgebra D.Q)) (n : ℕ)
    (ω : ActionOperatorForm K n) (v : Fin n → K.L) :
    cliffordHTraceForm D K n ω v = hTrace_cl D.Q (ω v) :=
  rfl

theorem cliffordGradeProjForm_zero_eq_hTrace (D : FormHodgeCliffordData R V C)
    (K : LieActionLane R (CliffordAlgebra D.Q)) (n : ℕ)
    (ω : ActionOperatorForm K n) (v : Fin n → K.L) :
    cliffordGradeProjForm D K 0 n ω v =
      algebraMap R (CliffordAlgebra D.Q) (cliffordHTraceForm D K n ω v) := by
  exact cliffordGradeProj_zero_eq_algebraMap_hTrace D.Q (ω v)

private theorem alternatingMap_finset_sum_apply {ι R' M' N' : Type*}
    [CommRing R'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    {n : ℕ} (s : Finset ι) (f : ι → M' [⋀^Fin n]→ₗ[R'] N') (v : Fin n → M') :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem cliffordGradeProjForm_sum_eq {V_real C_real : Type*}
    [AddCommGroup V_real] [Module ℝ V_real] [Module.Finite ℝ V_real]
    [Semiring C_real] [Algebra ℝ C_real]
    (D : FormHodgeCliffordData ℝ V_real C_real)
    (K : LieActionLane ℝ (CliffordAlgebra D.Q)) (n : ℕ)
    (ω : ActionOperatorForm K n) :
    (∑ m ∈ Finset.range (Module.finrank ℝ V_real + 1), cliffordGradeProjForm D K m n ω) = ω := by
  ext v
  rw [alternatingMap_finset_sum_apply]
  simp only [cliffordGradeProjForm_apply]
  exact cliffordGradeProj_sum_range_apply D.Q (ω v)

end CliffordValuedR1Forms

section CliffordMorphismR1Forms

variable {C_ring : Type*} [Ring C_ring] [Algebra R C_ring]

/-- Pushforward-pullback of a `CliffordAlgebra D.Q`-valued R1 form along `cliffordMorphism D`
and a linear map `φ : K_C.L →ₗ[R] K.L`. -/
def cliffordMorphismPullbackForm (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) (n : ℕ) :
    ActionOperatorForm K n →ₗ[R] ActionOperatorForm K_C n where
  toFun ω :=
    ((cliffordMorphism D).toLinearMap.compAlternatingMap ω).compLinearMap φ
  map_add' ω₁ ω₂ := by ext v; simp
  map_smul' c ω := by ext v; simp

@[simp] theorem cliffordMorphismPullbackForm_apply (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) (n : ℕ) (ω : ActionOperatorForm K n) (v : Fin n → K_C.L) :
    cliffordMorphismPullbackForm D φ n ω v =
      cliffordMorphism D (ω (fun i => φ (v i))) :=
  rfl

@[simp] theorem cliffordMorphismPullbackForm_curryLeft (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) {n : ℕ} (ω : ActionOperatorForm K (n + 1)) (x : K_C.L) :
    (cliffordMorphismPullbackForm D φ (n + 1) ω).curryLeft x =
      cliffordMorphismPullbackForm D φ n (ω.curryLeft (φ x)) := by
  ext w
  simp only [AlternatingMap.curryLeft_apply_apply, cliffordMorphismPullbackForm_apply]
  congr 2
  ext i
  induction i using Fin.cases <;> rfl

@[simp] theorem cliffordMorphismPullbackForm_reindexForm (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) {m n : ℕ} (h : m = n) (ω : ActionOperatorForm K m) :
    cliffordMorphismPullbackForm D φ n (reindexForm h ω) =
      reindexForm h (cliffordMorphismPullbackForm D φ m ω) := by
  subst h
  rfl

private theorem cliffordMorphismPullbackForm_lieDeriv (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (x : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ x) u) =
        K_C.operatorAction x (cliffordMorphism D u))
    (x : K_C.L) {n : ℕ} (ω : ActionOperatorForm K n) :
    lieDeriv K_C x (cliffordMorphismPullbackForm D (φ : K_C.L →ₗ[R] K.L) n ω) =
      cliffordMorphismPullbackForm D (φ : K_C.L →ₗ[R] K.L) n (lieDeriv K (φ x) ω) := by
  ext v
  simp only [lieDeriv_apply, cliffordMorphismPullbackForm_apply]
  rw [← hact x (ω (fun i => (φ : K_C.L →ₗ[R] K.L) (v i))), map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    exact φ.map_lie x (v j)
  · simp [Function.update_of_ne hji]

/-- `cliffordMorphismPullbackForm` commutes with `actionExteriorDerivative` at every degree `n`. -/
theorem cliffordMorphismPullbackForm_actionExteriorDerivative
    (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (x : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ x) u) =
        K_C.operatorAction x (cliffordMorphism D u)) :
    ∀ (n : ℕ) (ω : ActionOperatorForm K n),
      actionExteriorDerivative K_C n
          (cliffordMorphismPullbackForm D (φ : K_C.L →ₗ[R] K.L) n ω) =
        cliffordMorphismPullbackForm D (φ : K_C.L →ₗ[R] K.L) (n + 1)
          (actionExteriorDerivative K n ω)
  | 0, ω => by
    apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    rw [hv, actionExteriorDerivative_zero_apply, cliffordMorphismPullbackForm_apply,
      cliffordMorphismPullbackForm_apply, actionExteriorDerivative_zero_apply]
    have hact' := hact (![v 0] 0) (ω (fun i => (φ : K_C.L →ₗ[R] K.L) i.elim0))
    dsimp [LieActionLane.operatorAction] at hact' ⊢
    rw [← hact']
    exact congrArg (fun u => cliffordMorphism D (K.act (φ (![v 0] 0)) (ω u)))
      (Subsingleton.elim _ Fin.elim0)
  | m + 1, ω => by
    apply alternating_ext_curryLeft
    intro x
    erw [actionExteriorDerivative_succ_curryLeft, cliffordMorphismPullbackForm_curryLeft,
      cliffordMorphismPullbackForm_curryLeft, actionExteriorDerivative_succ_curryLeft,
      cliffordMorphismPullbackForm_lieDeriv D φ hact,
      cliffordMorphismPullbackForm_actionExteriorDerivative D φ hact m (ω.curryLeft (φ x)),
      ← map_sub]
    rfl

/-- `cliffordMorphismPullbackForm` preserves the noncommutative graded wedge `actionWedge`. -/
theorem cliffordMorphismPullbackForm_actionWedge
    (D : FormHodgeCliffordData R V C_ring)
    {K : LieActionLane R (CliffordAlgebra D.Q)} {K_C : LieActionLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) :
    ∀ {p q : ℕ} (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
      cliffordMorphismPullbackForm D φ (p + q) (actionWedge K ω η) =
        actionWedge K_C (cliffordMorphismPullbackForm D φ p ω)
          (cliffordMorphismPullbackForm D φ q η)
  | 0, q, ω, η => by
    ext v
    simp only [cliffordMorphismPullbackForm_apply, actionWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', cliffordMorphism_mul]
    congr 1
    · exact congrArg (fun u => cliffordMorphism D (ω u)) (Subsingleton.elim Fin.elim0 _)
  | p' + 1, 0, ω, η => by
    ext v
    simp only [cliffordMorphismPullbackForm_apply, actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply',
      cliffordMorphism_mul]
    congr 1
    exact congrArg (fun u => cliffordMorphism D (η u)) (Subsingleton.elim Fin.elim0 _)
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    erw [cliffordMorphismPullbackForm_curryLeft]
    rw [actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft, map_add, map_smul,
      cliffordMorphismPullbackForm_reindexForm,
      cliffordMorphismPullbackForm_actionWedge D φ (ω.curryLeft (φ x)) η]
    erw [cliffordMorphismPullbackForm_actionWedge D φ ω (η.curryLeft (φ x))]
    rw [cliffordMorphismPullbackForm_curryLeft, cliffordMorphismPullbackForm_curryLeft]

/-- `DerivationLieLane` specialization: `cliffordMorphismPullbackForm` intertwines
`ceExteriorDerivative`, `ceWedge`, and `ceCurvature` (preserving Maurer–Cartan flatness). -/
theorem cliffordMorphismPullbackForm_ceExteriorDerivative
    (D : FormHodgeCliffordData R V C_ring)
    {K : DerivationLieLane R (CliffordAlgebra D.Q)} {K_C : DerivationLieLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (x : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ x) u) =
        K_C.operatorAction x (cliffordMorphism D u))
    (n : ℕ) (ω : DerivationOperatorForm K n) :
    ceExteriorDerivative K_C n
        (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          (φ : K_C.L →ₗ[R] K.L) n ω) =
      cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
        (φ : K_C.L →ₗ[R] K.L) (n + 1) (ceExteriorDerivative K n ω) :=
  cliffordMorphismPullbackForm_actionExteriorDerivative D
    (K := K.toLieActionLane) (K_C := K_C.toLieActionLane) φ hact n ω

theorem cliffordMorphismPullbackForm_ceWedge
    (D : FormHodgeCliffordData R V C_ring)
    {K : DerivationLieLane R (CliffordAlgebra D.Q)} {K_C : DerivationLieLane R C_ring}
    (φ : K_C.L →ₗ[R] K.L) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
        φ (p + q) (ceWedge K ω η) =
      ceWedge K_C
        (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          φ p ω)
        (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          φ q η) :=
  cliffordMorphismPullbackForm_actionWedge D
    (K := K.toLieActionLane) (K_C := K_C.toLieActionLane) φ ω η

theorem cliffordMorphismPullbackForm_ceCurvature
    (D : FormHodgeCliffordData R V C_ring)
    {K : DerivationLieLane R (CliffordAlgebra D.Q)} {K_C : DerivationLieLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (x : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ x) u) =
        K_C.operatorAction x (cliffordMorphism D u))
    (Γ : DerivationOperatorForm K 1) :
    ceCurvature K_C
        (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          (φ : K_C.L →ₗ[R] K.L) 1 Γ) =
      cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
        (φ : K_C.L →ₗ[R] K.L) 2 (ceCurvature K Γ) := by
  have h1 := cliffordMorphismPullbackForm_ceExteriorDerivative D φ hact 1 Γ
  have h2 := cliffordMorphismPullbackForm_ceWedge D (φ : K_C.L →ₗ[R] K.L) Γ Γ
  ext v
  have hv1 := AlternatingMap.congr_fun h1 v
  have hv2 := AlternatingMap.congr_fun h2 v
  exact (congrArg₂ (· + ·) hv1 hv2.symm).trans (map_add (cliffordMorphism D) _ _).symm

theorem cliffordMorphismPullbackForm_ceCurvature_eq_zero
    (D : FormHodgeCliffordData R V C_ring)
    {K : DerivationLieLane R (CliffordAlgebra D.Q)} {K_C : DerivationLieLane R C_ring}
    (φ : K_C.L →ₗ⁅R⁆ K.L)
    (hact : ∀ (x : K_C.L) (u : CliffordAlgebra D.Q),
      cliffordMorphism D (K.operatorAction (φ x) u) =
        K_C.operatorAction x (cliffordMorphism D u))
    (Γ : DerivationOperatorForm K 1) (hflat : ceCurvature K Γ = 0) :
    ceCurvature K_C
        (cliffordMorphismPullbackForm D (K := K.toLieActionLane) (K_C := K_C.toLieActionLane)
          (φ : K_C.L →ₗ[R] K.L) 1 Γ) = 0 := by
  ext v
  have hv := AlternatingMap.congr_fun (cliffordMorphismPullbackForm_ceCurvature D φ hact Γ) v
  rw [hflat] at hv
  exact hv.trans (map_zero (cliffordMorphism D))

end CliffordMorphismR1Forms

end R1R3Coupling

end InfoGeometry.Canonical.ZornDifferentialFormsCliffordBridge
