import Mathlib.LinearAlgebra.Matrix.Permutation
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# S₃ Weyl symmetry of SU(3) color — Lie automorphism transport

The general algebraic fact: conjugation by an invertible matrix is a Lie
algebra automorphism.  If `Q·P = 1` then `(P·A·Q)(P·B·Q) - (P·B·Q)(P·A·Q) = P·[A,B]·Q`.

For SU(3), this file realizes the two generating transpositions by
Mathlib permutation matrices and proves that conjugation by each involution
transports any supplied commutator identity.  It does not assert the still
unformalized root-pair transitivity or that all sixteen concrete Gell-Mann
commutators have been generated from a seed identity.

Zero sorries.
-/

noncomputable section

namespace WeylSU3ColorSymmetry

open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Physics.BogoliubovSU3ParafermionProofChain
open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-! ## General lemma: conjugation is a Lie automorphism -/

/-- If `Q·P = 1`, conjugation `A ↦ P·A·Q` preserves commutators. -/
theorem conjAct_commutator (P Q : M3C) (hQP : Q * P = 1) (A B : M3C) :
    (P * A * Q) * (P * B * Q) - (P * B * Q) * (P * A * Q) =
    P * (A * B - B * A) * Q := by
  calc
    (P * A * Q) * (P * B * Q) - (P * B * Q) * (P * A * Q)
        = (P * A * (Q * P) * B * Q) - (P * B * (Q * P) * A * Q) := by
          simp [Matrix.mul_assoc]
    _ = (P * A * 1 * B * Q) - (P * B * 1 * A * Q) := by rw [hQP]
    _ = P * (A * B - B * A) * Q := by
      simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]

/-! ## S₃ generators as Fin 3 permutations -/

def swap12 := Equiv.swap (0 : Fin 3) 1
def swap23 := Equiv.swap (1 : Fin 3) 2

theorem swap12_swap23_braid :
    swap12 ∘ swap23 ∘ swap12 = swap23 ∘ swap12 ∘ swap23 := by
  ext i; fin_cases i <;> rfl

/-! ## Permutation matrices and their basic properties -/

/-- Mathlib's native permutation-matrix representation. -/
abbrev permMatrix (σ : Equiv.Perm (Fin 3)) : M3C :=
  σ.permMatrix ℂ

/-- Entry lemmas: `permMatrix swap12` evaluated at all 9 positions. -/
@[simp] lemma perm12_00 : permMatrix swap12 0 0 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_01 : permMatrix swap12 0 1 = (1 : ℂ) := by
  rfl
@[simp] lemma perm12_02 : permMatrix swap12 0 2 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_10 : permMatrix swap12 1 0 = (1 : ℂ) := by
  rfl
@[simp] lemma perm12_11 : permMatrix swap12 1 1 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_12 : permMatrix swap12 1 2 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_20 : permMatrix swap12 2 0 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_21 : permMatrix swap12 2 1 = (0 : ℂ) := by
  rfl
@[simp] lemma perm12_22 : permMatrix swap12 2 2 = (1 : ℂ) := by
  rfl
/-- Permutation matrix squared = identity (since a transposition is its own inverse). -/
theorem permMatrix_swap12_sq : permMatrix swap12 * permMatrix swap12 = (1 : M3C) := by
  rw [← Matrix.permMatrix_mul]
  simp [swap12]

/-- Entry lemmas for swap23 permutation matrix. -/
@[simp] lemma perm23_00 : permMatrix swap23 0 0 = (1 : ℂ) := by
  rfl
@[simp] lemma perm23_11 : permMatrix swap23 1 1 = (0 : ℂ) := by
  rfl
@[simp] lemma perm23_12 : permMatrix swap23 1 2 = (1 : ℂ) := by
  rfl
@[simp] lemma perm23_21 : permMatrix swap23 2 1 = (1 : ℂ) := by
  rfl
@[simp] lemma perm23_22 : permMatrix swap23 2 2 = (0 : ℂ) := by
  rfl
/-- All remaining entries are 0. -/
@[simp] lemma perm23_01 : permMatrix swap23 0 1 = (0 : ℂ) := by
  rfl
@[simp] lemma perm23_02 : permMatrix swap23 0 2 = (0 : ℂ) := by
  rfl
@[simp] lemma perm23_10 : permMatrix swap23 1 0 = (0 : ℂ) := by
  rfl
@[simp] lemma perm23_20 : permMatrix swap23 2 0 = (0 : ℂ) := by
  rfl
theorem permMatrix_swap23_sq : permMatrix swap23 * permMatrix swap23 = (1 : M3C) := by
  rw [← Matrix.permMatrix_mul]
  simp [swap23]

/-! ## Weyl group action via conjugation by permutation matrices -/

def weylAct (σ : Equiv.Perm (Fin 3)) (A : M3C) : M3C :=
  permMatrix σ * A * permMatrix σ

theorem weylAct_swap12_commutator (A B : M3C) :
    weylAct swap12 A * weylAct swap12 B - weylAct swap12 B * weylAct swap12 A =
    weylAct swap12 (A * B - B * A) := by
  dsimp [weylAct]
  rw [conjAct_commutator (permMatrix swap12) (permMatrix swap12) permMatrix_swap12_sq A B]

theorem weylAct_swap23_commutator (A B : M3C) :
    weylAct swap23 A * weylAct swap23 B - weylAct swap23 B * weylAct swap23 A =
    weylAct swap23 (A * B - B * A) := by
  dsimp [weylAct]
  rw [conjAct_commutator (permMatrix swap23) (permMatrix swap23) permMatrix_swap23_sq A B]

theorem weylAct_smul (σ : Equiv.Perm (Fin 3)) (c : ℂ) (A : M3C) :
    weylAct σ (c • A) = c • weylAct σ A := by
  simp [weylAct]

/-- The Weyl action transports any commutator identity `[A,B] = c•C`.
This is the key structural theorem: the Lie algebra structure is
preserved under the S₃ Weyl group action. -/
theorem weylAct_transport (σ : Equiv.Perm (Fin 3)) (A B C : M3C) (c : ℂ)
    (h_comm : A * B - B * A = c • C)
    (h_weyl_sq : permMatrix σ * permMatrix σ = 1) :
    weylAct σ A * weylAct σ B - weylAct σ B * weylAct σ A = c • weylAct σ C := by
  calc
    weylAct σ A * weylAct σ B - weylAct σ B * weylAct σ A
        = weylAct σ (A * B - B * A) := by
      dsimp [weylAct]
      rw [conjAct_commutator (permMatrix σ) (permMatrix σ) h_weyl_sq A B]
    _ = weylAct σ (c • C) := by rw [h_comm]
    _ = c • weylAct σ C := by rw [weylAct_smul]

theorem weylAct_swap12_transport (A B C : M3C) (c : ℂ) (h : A * B - B * A = c • C) :
    weylAct swap12 A * weylAct swap12 B - weylAct swap12 B * weylAct swap12 A =
    c • weylAct swap12 C :=
  weylAct_transport swap12 A B C c h permMatrix_swap12_sq

theorem weylAct_swap23_transport (A B C : M3C) (c : ℂ) (h : A * B - B * A = c • C) :
    weylAct swap23 A * weylAct swap23 B - weylAct swap23 B * weylAct swap23 A =
    c • weylAct swap23 C :=
  weylAct_transport swap23 A B C c h permMatrix_swap23_sq

/-! ## Transport to the color Lie action on 4-component spinors -/

/-- Weyl-transported commutators descend to `colorLieAction4`.
Since `colorLieAction4` is a genuine Lie algebra representation,
any Weyl-conjugate of a proved GellMann commutator holds in the
representation. -/
theorem weyl_transport_to_colorAction (σ : Equiv.Perm (Fin 3)) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C) (h_sq : permMatrix σ * permMatrix σ = 1)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) :
    colorLieAction4 (weylAct σ A) (colorLieAction4 (weylAct σ B) ψ) -
      colorLieAction4 (weylAct σ B) (colorLieAction4 (weylAct σ A) ψ) =
    c • colorLieAction4 (weylAct σ C) ψ := by
  rw [← colorLieAction4_commutator (weylAct σ A) (weylAct σ B) ψ]
  have hw := weylAct_transport σ A B C c h h_sq
  rw [hw]
  ext i <;> simp [colorLieAction4, Matrix.smul_apply, smul_smul, Finset.smul_sum]

/-- Concrete: swap12-transported `[λ₁,λ₂]=2i·λ₃` in the color action. -/
theorem swap12_transport_gl1_gl2_colorAction
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) :
    colorLieAction4 (weylAct swap12 gl1) (colorLieAction4 (weylAct swap12 gl2) ψ) -
      colorLieAction4 (weylAct swap12 gl2) (colorLieAction4 (weylAct swap12 gl1) ψ) =
    (2 * Complex.I) • colorLieAction4 (weylAct swap12 gl3) ψ :=
  weyl_transport_to_colorAction swap12 gl1 gl2 gl3 (2 * Complex.I)
    gl1_comm_gl2 permMatrix_swap12_sq ψ

/-! ## Deliberate boundary

The explicit action on all Gell-Mann generators, transitivity on the three
positive-root pairs, and generation of all sixteen concrete commutators are
not asserted here.  They remain owner-level closure debt.
-/

/-! ## Synthesis -/

theorem weyl_su3_color_symmetry_synthesis
    (A B C : M3C) (c : ℂ) (h : A * B - B * A = c • C) :
    weylAct swap12 A * weylAct swap12 B - weylAct swap12 B * weylAct swap12 A =
      c • weylAct swap12 C ∧
    weylAct swap23 A * weylAct swap23 B - weylAct swap23 B * weylAct swap23 A =
      c • weylAct swap23 C ∧
    permMatrix swap12 * permMatrix swap12 = (1 : M3C) ∧
    permMatrix swap23 * permMatrix swap23 = (1 : M3C) := by
  refine ⟨weylAct_swap12_transport A B C c h,
    weylAct_swap23_transport A B C c h, ?_, ?_⟩
  · exact permMatrix_swap12_sq
  · exact permMatrix_swap23_sq

end WeylSU3ColorSymmetry

end noncomputable section
