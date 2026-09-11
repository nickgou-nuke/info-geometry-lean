import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real Majorana matrix carrier

This recovered file keeps the explicit `4 × 4` real matrices and separates the
algebraic identities they are intended to satisfy from proved theorems.  The
former unproved chiral/Cuntz/topological claims are now statement shapes.
-/

namespace InfoGeometry.MajoranaTensorBridge

open Matrix

/-- Four-by-four real matrices. -/
abbrev MajoranaMatrix : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- `γ⁰` in a real Majorana-style representation. -/
def gamma0_maj : MajoranaMatrix :=
  !![ 1,  0,  0,  0;
      0,  1,  0,  0;
      0,  0, -1,  0;
      0,  0,  0, -1]

/-- `γ¹` in a real Majorana-style representation. -/
def gamma1_maj : MajoranaMatrix :=
  !![ 0,  0,  1,  0;
      0,  0,  0,  1;
      1,  0,  0,  0;
      0,  1,  0,  0]

/-- `γ²` in a real Majorana-style representation. -/
def gamma2_maj : MajoranaMatrix :=
  !![ 0,  0,  0,  1;
      0,  0,  1,  0;
      0, -1,  0,  0;
     -1,  0,  0,  0]

/-- `γ³` in a real Majorana-style representation. -/
def gamma3_maj : MajoranaMatrix :=
  !![ 0,  0,  1,  0;
      0,  0,  0, -1;
     -1,  0,  0,  0;
      0,  1,  0,  0]

/-- Signature-square obligations for the displayed matrices. -/
def majoranaSignatureSquaresStatement : Prop :=
  gamma0_maj * gamma0_maj = 1 ∧
  gamma1_maj * gamma1_maj = 1 ∧
  gamma2_maj * gamma2_maj = -1 ∧
  gamma3_maj * gamma3_maj = -1

/-- The mixed commutator `Σᵘᵛ = [γᵘ, γᵛ]`. -/
noncomputable def realLorentzGenerator (gamma_u gamma_v : MajoranaMatrix) : MajoranaMatrix :=
  gamma_u * gamma_v - gamma_v * gamma_u

/-- A spacetime vector embedded into the matrix span of the four generators. -/
noncomputable def majoranaSpacetimeVector (t x y z : ℝ) : MajoranaMatrix :=
  t • gamma0_maj + x • gamma1_maj + y • gamma2_maj + z • gamma3_maj

/-- Pure associativity fact for conjugation by an inverse matrix. -/
theorem majorana_lorentz_sandwich (S V S_inv : MajoranaMatrix)
    (_h_inv : S * S_inv = 1) (h_inv2 : S_inv * S = 1) :
    (S * V * S_inv) * (S * V * S_inv) = S * (V * V) * S_inv := by
  calc
    (S * V * S_inv) * (S * V * S_inv)
        = S * V * (S_inv * S) * V * S_inv := by simp only [Matrix.mul_assoc]
    _ = S * V * 1 * V * S_inv := by rw [h_inv2]
    _ = S * V * V * S_inv := by simp only [Matrix.mul_one]
    _ = S * (V * V) * S_inv := by simp only [Matrix.mul_assoc]

/-- Candidate chiral volume element. -/
noncomputable def gamma5_maj : MajoranaMatrix :=
  gamma0_maj * gamma1_maj * gamma2_maj * gamma3_maj

/-- Statement shape for the grading identity. -/
def gamma5_maj_sq_statement : Prop := gamma5_maj * gamma5_maj = 1

/-- Candidate chiral projectors. -/
noncomputable def chiralProjectorL : MajoranaMatrix := (1 / 2 : ℝ) • (1 - gamma5_maj)
noncomputable def chiralProjectorR : MajoranaMatrix := (1 / 2 : ℝ) • (1 + gamma5_maj)

/-- Chiral supertrace expression. -/
noncomputable def chiralSupertrace (A : MajoranaMatrix) : ℝ := Matrix.trace (gamma5_maj * A)

/-- Statement shape for the basic chiral trace identities. -/
def chiralTraceStatement : Prop :=
  chiralSupertrace 1 = 0 ∧
  Matrix.trace chiralProjectorL = 2 ∧
  Matrix.trace chiralProjectorR = 2

/-- Candidate nilpotent generator. -/
noncomputable def cuntzGeneratorPlus : MajoranaMatrix := (1 / 2 : ℝ) • (gamma0_maj + gamma2_maj)

/-- Candidate parity-conjugate nilpotent generator. -/
noncomputable def cuntzGeneratorMinus : MajoranaMatrix := (1 / 2 : ℝ) • (gamma0_maj - gamma2_maj)

/-- Statement shape for the nilpotent/anticommutator identities. -/
def cuntzGeneratorStatement : Prop :=
  cuntzGeneratorPlus * cuntzGeneratorPlus = 0 ∧
  cuntzGeneratorMinus * cuntzGeneratorMinus = 0 ∧
  cuntzGeneratorPlus * cuntzGeneratorMinus + cuntzGeneratorMinus * cuntzGeneratorPlus = 1

end InfoGeometry.MajoranaTensorBridge
