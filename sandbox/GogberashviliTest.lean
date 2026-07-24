import Mathlib
import Mathlib.Data.Fin.Basic
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.ConcreteComposition

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open Fin
open Matrix

namespace InfoGeometry.Clifford.GogberashviliSplitOctonionBasis

/--
Levi-Civita symbol εₙₘₖ on `Fin 3`.
-/
noncomputable def eps3 (i j k : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1
  else if i = 1 ∧ j = 2 ∧ k = 0 then 1
  else if i = 2 ∧ j = 0 ∧ k = 1 then 1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else 0

/-- Negation of a Zorn cell. -/
def negZ (X : ZornCell ℝ) : ZornCell ℝ :=
  ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

/-- Add instance for ZornCell ℝ. -/
instance : Add (ZornCell ℝ) where
  add := addZ

/-- SMul function for ZornCell ℝ. -/
def smulZ (r : ℝ) (X : ZornCell ℝ) : ZornCell ℝ :=
  ⟨r * X.r, r * X.s, r * X.x1, r * X.x2, r * X.x3, r * X.y1, r * X.y2, r * X.y3⟩

/-- SMul instance for ZornCell ℝ. -/
instance : SMul ℝ (ZornCell ℝ) where
  smul := smulZ

/-- Neg instance for ZornCell ℝ. -/
instance : Neg (ZornCell ℝ) where
  neg := negZ

/-- Zero instance for ZornCell ℝ. -/
instance : Zero (ZornCell ℝ) where
  zero := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Canonical Zorn scalar unit `1 = (1, 1, 0, 0, 0, 0, 0, 0)`. -/
def oneZ : ZornCell ℝ :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Pseudoscalar `I = (1, -1, 0, 0, 0, 0, 0, 0)`. -/
def I_pseudoscalar : ZornCell ℝ :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Vector-like unit `Jₙ = (0, 0, eₙ, eₙ)` for `n : Fin 3`. -/
def J (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨0, 0, 1, 0, 0, 1, 0, 0⟩  -- J₀ = (0, 0, 1, 0, 0, 1, 0, 0)
  | ⟨1, _⟩ => ⟨0, 0, 0, 1, 0, 0, 1, 0⟩  -- J₁ = (0, 0, 0, 1, 0, 0, 1, 0)
  | ⟨2, _⟩ => ⟨0, 0, 0, 0, 1, 0, 0, 1⟩  -- J₂ = (0, 0, 0, 0, 1, 0, 0, 1)

/-- Pseudovector-like unit `jₙ = (0, 0, -eₙ, eₙ)` for `n : Fin 3`. -/
def j (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨0, 0, -1, 0, 0, 1, 0, 0⟩  -- j₀ = (0, 0, -1, 0, 0, 1, 0, 0)
  | ⟨1, _⟩ => ⟨0, 0, 0, -1, 0, 0, 1, 0⟩  -- j₁ = (0, 0, 0, -1, 0, 0, 1, 0)
  | ⟨2, _⟩ => ⟨0, 0, 0, 0, -1, 0, 0, 1⟩  -- j₂ = (0, 0, 0, 0, -1, 0, 0, 1)

/-- Helper: sum over Fin 3. -/
def sumFin3 (f : Fin 3 → ZornCell ℝ) : ZornCell ℝ :=
  f 0 + f 1 + f 2

/-- Check equality of two Zorn cells by components. -/
lemma zorn_ext {X Y : ZornCell ℝ}
    (hr : X.r = Y.r) (hs : X.s = Y.s)
    (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2) (hx3 : X.x3 = Y.x3)
    (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) (hy3 : X.y3 = Y.y3) : X = Y := by
  cases X <;> cases Y <;> simp_all [ZornCell.mk.injEq]

theorem J_sq (n : Fin 3) : J n * J n = oneZ := by
  fin_cases n <;>
  change mulZ (J _) (J _) = oneZ <;>
  apply zorn_ext <;>
  (dsimp [J, oneZ, mulZ] <;> norm_num)

theorem j_sq (n : Fin 3) : j n * j n = -oneZ := by
  fin_cases n <;>
  change mulZ (j _) (j _) = negZ oneZ <;>
  apply zorn_ext <;>
  (dsimp [j, oneZ, mulZ, negZ] <;> norm_num)

theorem I_sq : I_pseudoscalar * I_pseudoscalar = oneZ := by
  change mulZ I_pseudoscalar I_pseudoscalar = oneZ <;>
  apply zorn_ext <;>
  (dsimp [I_pseudoscalar, oneZ, mulZ] <;> norm_num)

theorem J_anticomm (n m : Fin 3) (h : n ≠ m) : J n * J m = -(J m * J n) := by
  fin_cases n <;> fin_cases m <;> try (cases h rfl) <;>
  change mulZ (J _) (J _) = negZ (mulZ (J _) (J _)) <;>
  apply zorn_ext <;>
  (dsimp [J, mulZ, negZ] <;> norm_num)

theorem j_anticomm (n m : Fin 3) (h : n ≠ m) : j n * j m = -(j m * j n) := by
  fin_cases n <;> fin_cases m <;> try (cases h rfl) <;>
  change mulZ (j _) (j _) = negZ (mulZ (j _) (j _)) <;>
  apply zorn_ext <;>
  (dsimp [j, mulZ, negZ] <;> norm_num)

theorem J_mul_J (n m : Fin 3) (h : n ≠ m) : J n * J m = sumFin3 (fun k => (eps3 n m k : ℝ) • j k) := by
  fin_cases n <;> fin_cases m <;> try (cases h rfl) <;>
  change mulZ (J _) (J _) = addZ (addZ (smulZ (eps3 _ _ 0) (j 0)) (smulZ (eps3 _ _ 1) (j 1))) (smulZ (eps3 _ _ 2) (j 2)) <;>
  apply zorn_ext <;>
  (dsimp [J, j, eps3, mulZ, smulZ, addZ] <;> norm_num)

theorem j_mul_j (n m : Fin 3) (h : n ≠ m) : j n * j m = sumFin3 (fun k => (eps3 n m k : ℝ) • j k) := by
  fin_cases n <;> fin_cases m <;> try (cases h rfl) <;>
  change mulZ (j _) (j _) = addZ (addZ (smulZ (eps3 _ _ 0) (j 0)) (smulZ (eps3 _ _ 1) (j 1))) (smulZ (eps3 _ _ 2) (j 2)) <;>
  apply zorn_ext <;>
  (dsimp [J, j, eps3, mulZ, smulZ, addZ] <;> norm_num)

theorem j_mul_J (n m : Fin 3) (h : n ≠ m) : j m * J n = sumFin3 (fun k => (eps3 n m k : ℝ) • J k) := by
  fin_cases n <;> fin_cases m <;> try (cases h rfl) <;>
  change mulZ (j _) (J _) = addZ (addZ (smulZ (eps3 _ _ 0) (J 0)) (smulZ (eps3 _ _ 1) (J 1))) (smulZ (eps3 _ _ 2) (J 2)) <;>
  apply zorn_ext <;>
  (dsimp [J, j, eps3, mulZ, smulZ, addZ] <;> norm_num)

theorem J_mul_I (n : Fin 3) : J n * I_pseudoscalar = j n := by
  fin_cases n <;>
  change mulZ (J _) I_pseudoscalar = j _ <;>
  apply zorn_ext <;>
  (dsimp [J, I_pseudoscalar, j, mulZ] <;> norm_num)

theorem I_mul_J (n : Fin 3) : I_pseudoscalar * J n = -(j n) := by
  fin_cases n <;>
  change mulZ I_pseudoscalar (J _) = negZ (j _) <;>
  apply zorn_ext <;>
  (dsimp [I_pseudoscalar, J, j, mulZ, negZ] <;> norm_num)

theorem j_mul_I (n : Fin 3) : j n * I_pseudoscalar = J n := by
  fin_cases n <;>
  change mulZ (j _) I_pseudoscalar = J _ <;>
  apply zorn_ext <;>
  (dsimp [j, I_pseudoscalar, J, mulZ] <;> norm_num)

theorem I_mul_j (n : Fin 3) : I_pseudoscalar * j n = -(J n) := by
  fin_cases n <;>
  change mulZ I_pseudoscalar (j _) = negZ (J _) <;>
  apply zorn_ext <;>
  (dsimp [I_pseudoscalar, j, J, mulZ, negZ] <;> norm_num)

noncomputable def D_plus (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨1/2, 1/2, 1/2, 0, 0, 1/2, 0, 0⟩
  | ⟨1, _⟩ => ⟨1/2, 1/2, 0, 1/2, 0, 0, 1/2, 0⟩
  | ⟨2, _⟩ => ⟨1/2, 1/2, 0, 0, 1/2, 0, 0, 1/2⟩

noncomputable def D_minus (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨1/2, 1/2, -1/2, 0, 0, -1/2, 0, 0⟩
  | ⟨1, _⟩ => ⟨1/2, 1/2, 0, -1/2, 0, 0, -1/2, 0⟩
  | ⟨2, _⟩ => ⟨1/2, 1/2, 0, 0, -1/2, 0, 0, -1/2⟩

noncomputable def G_plus (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨1/2, -1/2, -1/2, 0, 0, 1/2, 0, 0⟩
  | ⟨1, _⟩ => ⟨1/2, -1/2, 0, -1/2, 0, 0, 1/2, 0⟩
  | ⟨2, _⟩ => ⟨1/2, -1/2, 0, 0, -1/2, 0, 0, 1/2⟩

noncomputable def G_minus (n : Fin 3) : ZornCell ℝ :=
  match n with
  | ⟨0, _⟩ => ⟨1/2, -1/2, 1/2, 0, 0, -1/2, 0, 0⟩
  | ⟨1, _⟩ => ⟨1/2, -1/2, 0, 1/2, 0, 0, -1/2, 0⟩
  | ⟨2, _⟩ => ⟨1/2, -1/2, 0, 0, 1/2, 0, 0, -1/2⟩

theorem D_plus_idempotent (n : Fin 3) : D_plus n * D_plus n = D_plus n := by
  fin_cases n <;>
  change mulZ (D_plus _) (D_plus _) = D_plus _ <;>
  apply zorn_ext <;>
  (dsimp [D_plus, mulZ] <;> norm_num)

theorem D_minus_idempotent (n : Fin 3) : D_minus n * D_minus n = D_minus n := by
  fin_cases n <;>
  change mulZ (D_minus _) (D_minus _) = D_minus _ <;>
  apply zorn_ext <;>
  (dsimp [D_minus, mulZ] <;> norm_num)

theorem D_plus_mul_D_minus (n : Fin 3) : D_plus n * D_minus n = 0 := by
  fin_cases n <;>
  change mulZ (D_plus _) (D_minus _) = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ <;>
  apply zorn_ext <;>
  (dsimp [D_plus, D_minus, mulZ] <;> norm_num)

theorem G_plus_nilpotent (n : Fin 3) : G_plus n * G_plus n = 0 := by
  fin_cases n <;>
  change mulZ (G_plus _) (G_plus _) = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ <;>
  apply zorn_ext <;>
  (dsimp [G_plus, mulZ] <;> norm_num)

theorem G_minus_nilpotent (n : Fin 3) : G_minus n * G_minus n = 0 := by
  fin_cases n <;>
  change mulZ (G_minus _) (G_minus _) = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ <;>
  apply zorn_ext <;>
  (dsimp [G_minus, mulZ] <;> norm_num)

theorem G_plus_mul_G_minus (n : Fin 3) : G_plus n * G_minus n = D_plus n := by
  fin_cases n <;>
  change mulZ (G_plus _) (G_minus _) = D_plus _ <;>
  apply zorn_ext <;>
  (dsimp [G_plus, G_minus, D_plus, mulZ] <;> norm_num)

theorem gogberashvili_basis_synthesis :
    (∀ n : Fin 3, J n * J n = oneZ) ∧
    (∀ n : Fin 3, j n * j n = -oneZ) ∧
    I_pseudoscalar * I_pseudoscalar = oneZ ∧
    (∀ n m : Fin 3, n ≠ m → J n * J m = -(J m * J n)) ∧
    (∀ n m : Fin 3, n ≠ m → J n * J m = sumFin3 (fun k => (eps3 n m k : ℝ) • j k)) ∧
    (∀ n m : Fin 3, n ≠ m → j n * j m = sumFin3 (fun k => (eps3 n m k : ℝ) • j k)) ∧
    (∀ n m : Fin 3, n ≠ m → j m * J n = sumFin3 (fun k => (eps3 n m k : ℝ) • J k)) ∧
    (∀ n : Fin 3, J n * I_pseudoscalar = j n) ∧
    (∀ n : Fin 3, I_pseudoscalar * J n = -(j n)) ∧
    (∀ n : Fin 3, j n * I_pseudoscalar = J n) ∧
    (∀ n : Fin 3, I_pseudoscalar * j n = -(J n)) ∧
    (∀ n : Fin 3, D_plus n * D_plus n = D_plus n) ∧
    (∀ n : Fin 3, D_minus n * D_minus n = D_minus n) ∧
    (∀ n : Fin 3, D_plus n * D_minus n = 0) ∧
    (∀ n : Fin 3, G_plus n * G_plus n = 0) ∧
    (∀ n : Fin 3, G_minus n * G_minus n = 0) ∧
    (∀ n : Fin 3, G_plus n * G_minus n = D_plus n) := by
  refine' ⟨J_sq, j_sq, I_sq, ?_, J_mul_J, j_mul_j, j_mul_J, J_mul_I, I_mul_J, j_mul_I, I_mul_j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- J anticommutation
    intro n m h
    exact J_anticomm n m h
  · -- D_plus idempotent
    intro n
    exact D_plus_idempotent n
  · -- D_minus idempotent
    intro n
    exact D_minus_idempotent n
  · -- D_plus * D_minus = 0
    intro n
    exact D_plus_mul_D_minus n
  · -- G_plus nilpotent
    intro n
    exact G_plus_nilpotent n
  · -- G_minus nilpotent
    intro n
    exact G_minus_nilpotent n
  · -- G_plus * G_minus = D_plus
    intro n
    exact G_plus_mul_G_minus n

end InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
