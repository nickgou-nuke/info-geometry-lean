import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.SylvesterIwasawaKAN

namespace InfoGeometry.Canonical.SylvesterGrading

open InfoGeometry.Canonical.SylvesterIwasawaKAN

variable {R : Type*} [CommRing R]

/-! ### 1. Abstract Braided Commutators -/

/-- An abelian bicharacter β : Γ → Γ → Rˣ governing the categorical braiding. -/
structure GradingBicharacter (Γ : Type*) [AddCommMonoid Γ] (R : Type*) [CommRing R] where
  β : Γ → Γ → Rˣ
  map_add_left : ∀ g₁ g₂ h : Γ, β (g₁ + g₂) h = β g₁ h * β g₂ h
  map_add_right : ∀ g h₁ h₂ : Γ, β g (h₁ + h₂) = β g h₁ * β g h₂

instance {Γ} [AddCommMonoid Γ] :
    CoeFun (GradingBicharacter Γ R) (fun _ => Γ → Γ → R) where
  coe B g h := (B.β g h : R)

/-- The Braided Commutator [a, b]_β = a * b - β(|a|, |b|) • (b * a). -/
def braidedCommutator {Γ A : Type*} [AddCommMonoid Γ] [Ring A] [Algebra R A]
    (B : GradingBicharacter Γ R) (ga gb : Γ) (a b : A) : A :=
  a * b - (B.β ga gb : R) • (b * a)

theorem braidedCommutator_eq_zero_iff {Γ A : Type*} [AddCommMonoid Γ] [Ring A] [Algebra R A]
    (B : GradingBicharacter Γ R) (ga gb : Γ) (a b : A) :
    braidedCommutator B ga gb a b = 0 ↔ a * b = (B.β ga gb : R) • (b * a) := by
  dsimp [braidedCommutator]
  exact sub_eq_zero

/-! ### 2. Sylvester Matrix Grading Realization -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix M has Sylvester grade (a, b) if it is proportional to X^a Z^b -/
def IsSylvesterGrade (X Z : Matrix n n R) (a b : ℕ) (M : Matrix n n R) : Prop :=
  ∃ c : R, M = c • (X ^ a * Z ^ b)

/-- The exact multiplication of two displacement basis elements -/
lemma displacement_mul (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z)
    (a1 b1 a2 b2 : ℕ) :
    (X ^ a1 * Z ^ b1) * (X ^ a2 * Z ^ b2) = (ω ^ (a2 * b1)) • (X ^ (a1 + a2) * Z ^ (b1 + b2)) := by
  calc
    (X ^ a1 * Z ^ b1) * (X ^ a2 * Z ^ b2) = X ^ a1 * (Z ^ b1 * X ^ a2) * Z ^ b2 := by
      simp only [Matrix.mul_assoc]
    _ = X ^ a1 * ((ω ^ (a2 * b1)) • (X ^ a2 * Z ^ b1)) * Z ^ b2 := by
      rw [sylvester_pow_XZ ω X Z h a2 b1]
    _ = (ω ^ (a2 * b1)) • (X ^ a1 * (X ^ a2 * Z ^ b1) * Z ^ b2) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = (ω ^ (a2 * b1)) • ((X ^ a1 * X ^ a2) * (Z ^ b1 * Z ^ b2)) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (ω ^ (a2 * b1)) • (X ^ (a1 + a2) * Z ^ (b1 + b2)) := by
      rw [← pow_add, ← pow_add]

theorem sylvester_grade_mul (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z)
    (a1 b1 a2 b2 : ℕ) (M1 M2 : Matrix n n R)
    (h1 : IsSylvesterGrade X Z a1 b1 M1)
    (h2 : IsSylvesterGrade X Z a2 b2 M2) :
    IsSylvesterGrade X Z (a1 + a2) (b1 + b2) (M1 * M2) := by
  rcases h1 with ⟨c1, hc1⟩
  rcases h2 with ⟨c2, hc2⟩
  use c1 * c2 * ω ^ (a2 * b1)
  calc
    M1 * M2 = (c1 • (X ^ a1 * Z ^ b1)) * (c2 • (X ^ a2 * Z ^ b2)) := by rw [hc1, hc2]
    _ = (c1 * c2) • (X ^ a1 * Z ^ b1 * (X ^ a2 * Z ^ b2)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm c2 c1]
    _ = (c1 * c2) • ((ω ^ (a2 * b1)) • (X ^ (a1 + a2) * Z ^ (b1 + b2))) := by
      rw [displacement_mul ω X Z h a1 b1 a2 b2]
    _ = (c1 * c2 * ω ^ (a2 * b1)) • (X ^ (a1 + a2) * Z ^ (b1 + b2)) := by
      rw [smul_smul]

/-- The Heisenberg-Artin Braiding Deformation:
    Elements of grade (a1, b1) and (a2, b2) q-commute via the symplectic phase factor. -/
theorem sylvester_braiding (ω : R) (X Z : Matrix n n R) (h : IsSylvesterPair ω X Z)
    (a1 b1 a2 b2 : ℕ) (M1 M2 : Matrix n n R) (c1 c2 : R)
    (h1 : M1 = c1 • (X ^ a1 * Z ^ b1))
    (h2 : M2 = c2 • (X ^ a2 * Z ^ b2)) :
    (ω ^ (a1 * b2)) • (M1 * M2) = (ω ^ (a2 * b1)) • (M2 * M1) := by
  calc
    (ω ^ (a1 * b2)) • (M1 * M2) = (ω ^ (a1 * b2)) • ((c1 • (X ^ a1 * Z ^ b1)) * (c2 • (X ^ a2 * Z ^ b2))) := by rw [h1, h2]
    _ = (ω ^ (a1 * b2)) • ((c1 * c2) • ((X ^ a1 * Z ^ b1) * (X ^ a2 * Z ^ b2))) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm c2 c1]
    _ = (ω ^ (a1 * b2)) • ((c1 * c2) • ((ω ^ (a2 * b1)) • (X ^ (a1 + a2) * Z ^ (b1 + b2)))) := by
      rw [displacement_mul ω X Z h a1 b1 a2 b2]
    _ = (ω ^ (a2 * b1)) • ((c2 * c1) • ((ω ^ (a1 * b2)) • (X ^ (a2 + a1) * Z ^ (b2 + b1)))) := by
      rw [add_comm a1 a2, add_comm b1 b2]
      simp only [smul_smul]
      congr 1
      ring
    _ = (ω ^ (a2 * b1)) • ((c2 * c1) • ((X ^ a2 * Z ^ b2) * (X ^ a1 * Z ^ b1))) := by
      rw [displacement_mul ω X Z h a2 b2 a1 b1]
    _ = (ω ^ (a2 * b1)) • ((c2 • (X ^ a2 * Z ^ b2)) * (c1 • (X ^ a1 * Z ^ b1))) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm c1 c2]
    _ = (ω ^ (a2 * b1)) • (M2 * M1) := by rw [← h1, ← h2]


/-! ### 3. Yang-Baxter Topological Integrability and Phase Space -/

/-- The Yang-Baxter hexagon equation holds identically for abelian bicharacters. -/
theorem artin_braid_phase_identity {Γ : Type*} [AddCommMonoid Γ] (B : GradingBicharacter Γ R) (gu gv gw : Γ) :
    (B.β gu gv : R) * (B.β gu gw : R) * (B.β gv gw : R) =
    (B.β gv gw : R) * (B.β gu gw : R) * (B.β gu gv : R) := by
  ring

abbrev PhaseSpace := ℤ × ℤ

def phaseSymplecticForm (w₁ w₂ : PhaseSpace) : ℤ :=
  w₁.1 * w₂.2 - w₁.2 * w₂.1

lemma phaseSymplecticForm_swap (w₁ w₂ : PhaseSpace) :
    phaseSymplecticForm w₁ w₂ = - phaseSymplecticForm w₂ w₁ := by
  dsimp [phaseSymplecticForm]
  ring

def degX : PhaseSpace := (1, 0)
def degZ : PhaseSpace := (0, 1)

theorem phaseSymplectic_ZX : phaseSymplecticForm degZ degX = -1 := by rfl
theorem phaseSymplectic_XZ : phaseSymplecticForm degX degZ = 1 := by rfl

theorem heisenberg_quantum_torus {A : Type*} [Ring A] [Algebra R A]
    (B : GradingBicharacter PhaseSpace R) (X Z : A)
    (q : Rˣ)
    (h_phase : (B.β degZ degX : R) = (q : Rˣ))
    (h_comm : braidedCommutator B degZ degX Z X = 0) :
    Z * X = (q : Rˣ) • (X * Z) := by
  rw [braidedCommutator_eq_zero_iff] at h_comm
  rw [h_phase] at h_comm
  exact h_comm

end InfoGeometry.Canonical.SylvesterGrading
