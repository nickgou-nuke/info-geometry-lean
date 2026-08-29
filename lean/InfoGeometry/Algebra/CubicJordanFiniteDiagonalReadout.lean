import InfoGeometry.Algebra.CubicJordanPeirce

/-!
# Finite diagonal Jordan readout for the Albert carrier

This is the honest finite diagonal subcarrier of `AlbertMatrix`.  It supplies
the Jordan laws and spectral/positive readback without pretending that the
full split-octonionic product has already been defined.
-/

namespace InfoGeometry.Algebra.CubicJordanFiniteDiagonalReadout

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

abbrev DiagonalJ3 := Fin 3 → ℝ

def jordanProduct (x y : DiagonalJ3) : DiagonalJ3 := fun i => x i * y i

def conjugate (x : DiagonalJ3) : DiagonalJ3 := x

def normSquared (x : DiagonalJ3) : ℝ := ∑ i, (x i) ^ 2

def unit : DiagonalJ3 := fun _ => 1

def e₁ : DiagonalJ3 := fun i => if i = 0 then 1 else 0
def e₂ : DiagonalJ3 := fun i => if i = 1 then 1 else 0
def e₃ : DiagonalJ3 := fun i => if i = 2 then 1 else 0

def positive (x : DiagonalJ3) : Prop := ∀ i, 0 ≤ x i

def peirceCoordinates (X : AlbertMatrix) : DiagonalJ3 :=
  ![X.α₁, X.α₂, X.α₃]

theorem conjugate_involution (x : DiagonalJ3) : conjugate (conjugate x) = x := rfl

theorem normSquared_nonneg (x : DiagonalJ3) : 0 ≤ normSquared x := by
  dsimp [normSquared]
  positivity

theorem jordanProduct_comm (x y : DiagonalJ3) :
    jordanProduct x y = jordanProduct y x := by
  funext i
  simp [jordanProduct, mul_comm]

theorem jordanProduct_unit (x : DiagonalJ3) :
    jordanProduct unit x = x := by
  funext i
  simp [jordanProduct, unit]

theorem jordan_identity (x y : DiagonalJ3) :
    jordanProduct (jordanProduct x x) (jordanProduct y x) =
      jordanProduct x (jordanProduct (jordanProduct x y) x) := by
  funext i
  simp [jordanProduct]
  ring

theorem scalar_diagonal_jordan_identity (x y : DiagonalJ3) :
    jordanProduct (jordanProduct x x) (jordanProduct y x) =
      jordanProduct x (jordanProduct (jordanProduct x y) x) := by
  exact jordan_identity x y

theorem e₁_idempotent : jordanProduct e₁ e₁ = e₁ := by
  funext i
  fin_cases i <;> simp [e₁, jordanProduct]

theorem e₂_idempotent : jordanProduct e₂ e₂ = e₂ := by
  funext i
  fin_cases i <;> simp [e₂, jordanProduct]

theorem e₃_idempotent : jordanProduct e₃ e₃ = e₃ := by
  funext i
  fin_cases i <;> simp [e₃, jordanProduct]

theorem scalar_diagonal_e₁_idempotent :
    jordanProduct e₁ e₁ = e₁ := e₁_idempotent

theorem scalar_diagonal_e₂_idempotent :
    jordanProduct e₂ e₂ = e₂ := e₂_idempotent

theorem scalar_diagonal_e₃_idempotent :
    jordanProduct e₃ e₃ = e₃ := e₃_idempotent

theorem scalar_diagonal_e₁_e₂_orthogonal :
    jordanProduct e₁ e₂ = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [e₁, e₂, jordanProduct]

theorem scalar_diagonal_e₁_e₃_orthogonal :
    jordanProduct e₁ e₃ = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [e₁, e₃, jordanProduct]

theorem scalar_diagonal_e₂_e₃_orthogonal :
    jordanProduct e₂ e₃ = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [e₂, e₃, jordanProduct]

theorem diagonal_completeness : e₁ + e₂ + e₃ = unit := by
  funext i
  fin_cases i <;> simp [e₁, e₂, e₃, unit]

theorem scalar_diagonal_partition : e₁ + e₂ + e₃ = unit :=
  diagonal_completeness

theorem diagonal_spectral_readout (x : DiagonalJ3) :
    x = x 0 • e₁ + x 1 • e₂ + x 2 • e₃ := by
  funext i
  fin_cases i <;> simp [e₁, e₂, e₃]

theorem peirce_coordinates_recover_diagonal (a₁ a₂ a₃ : ℝ) :
    peirceCoordinates
      { α₁ := a₁, α₂ := a₂, α₃ := a₃,
        z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ } =
      a₁ • e₁ + a₂ • e₂ + a₃ • e₃ := by
  funext i
  fin_cases i <;> simp [peirceCoordinates, e₁, e₂, e₃]

theorem positive_e₁ : positive e₁ := by
  intro i
  fin_cases i <;> simp [e₁]

theorem positive_e₂ : positive e₂ := by
  intro i
  fin_cases i <;> simp [e₂]

theorem positive_e₃ : positive e₃ := by
  intro i
  fin_cases i <;> simp [e₃]

theorem positive_iff_coordinatewise (x : DiagonalJ3) :
    positive x ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h₀, h₁, h₂⟩ i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂

end InfoGeometry.Algebra.CubicJordanFiniteDiagonalReadout
