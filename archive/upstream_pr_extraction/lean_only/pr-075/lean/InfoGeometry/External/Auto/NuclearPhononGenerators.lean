import Mathlib.Tactic

/-!
Finite algebraic owners for the reusable parts of the former phonon fixture.

No physical generator count, string-labelled mode, or complex-number CCR
literal is promoted here.  The remaining statements are generic arithmetic
and bilinear-operator lemmas.
-/

namespace NuclearPhononGenerators

abbrev Q := ℚ

def symmetricPairCount (n : ℕ) : ℕ := n * (n + 1) / 2

def antisymmetricPairCount (n : ℕ) : ℕ := n * (n - 1) / 2

def uDimension (n : ℕ) : ℕ := n * n

def suDimension (n : ℕ) : ℕ := n * n - 1

def soDimension (n : ℕ) : ℕ := n * (n - 1) / 2

def spRealDimensionFromHalfRank (n : ℕ) : ℕ := n * (2 * n + 1)

def u6Dimension : ℕ := uDimension 6

def sp6RDimension : ℕ := spRealDimensionFromHalfRank 3

theorem u6_dimension_eq_36 : u6Dimension = 36 := by
  norm_num [u6Dimension, uDimension]

theorem sp6R_dimension_eq_21 : sp6RDimension = 21 := by
  norm_num [sp6RDimension, spRealDimensionFromHalfRank]

abbrev PhononRaisingOperator (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  (V → V → ℝ) × (V → V → ℝ) × (V → V → ℝ)

namespace PhononRaisingOperator

abbrev Qform {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) : V → V → ℝ := op.1

abbrev Kform {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) : V → V → ℝ := op.2.1

abbrev Tform {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) : V → V → ℝ := op.2.2

end PhononRaisingOperator

noncomputable def raisingPhonon {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) (u v : V) : ℂ :=
  ⟨(op.Qform u v - op.Kform u v) / 2, op.Tform u v / 2⟩

theorem raising_phonon_non_vacuous {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : PhononRaisingOperator V) (u v : V) :
    op.Tform u v ≠ 0 → raisingPhonon op u v ≠ 0 := by
  intro hT hzero
  have h_im : (raisingPhonon op u v).im = 0 := by
    rw [hzero]
    rfl
  dsimp [raisingPhonon] at h_im
  have hmul := congrArg (fun x : ℝ => x * 2) h_im
  norm_num at hmul
  apply hT
  simpa using hmul

def poincareC1 (m : Q) : Q := -m * m

def springStiffnessFromC1 (C1 : Q) : Q := -C1

theorem casimir_spring_stiffness (m : Q) :
    springStiffnessFromC1 (poincareC1 m) = m * m := by
  rw [springStiffnessFromC1, poincareC1]
  ring

end NuclearPhononGenerators
