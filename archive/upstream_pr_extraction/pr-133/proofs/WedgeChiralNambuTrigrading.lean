import Mathlib
import Mathlib.Data.Matrix.Basic

noncomputable section
namespace InfoGeometry.WedgeChiralNambuTrigrading

abbrev TrigradingIndex := Fin 2 × Fin 2 × Fin 2
abbrev M8C := Matrix TrigradingIndex TrigradingIndex ℂ

-- 1. Wedge (Rindler) Involution
def gammaWedge : M8C :=
  Matrix.diagonal (fun i => if i.1 = 0 then (1 : ℂ) else -1)

-- 2. Chiral Involution
def gammaChi : M8C :=
  Matrix.diagonal (fun i => if i.2.1 = 0 then (1 : ℂ) else -1)

-- 3. Nambu (Particle-Hole) Involution
def gammaNambu : M8C :=
  Matrix.diagonal (fun i => if i.2.2 = 0 then (1 : ℂ) else -1)

@[simp] theorem gammaWedge_sq : gammaWedge * gammaWedge = (1 : M8C) := by
  dsimp [gammaWedge]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases h0 : i.1 = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

@[simp] theorem gammaChi_sq : gammaChi * gammaChi = (1 : M8C) := by
  dsimp [gammaChi]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases h0 : i.2.1 = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

@[simp] theorem gammaNambu_sq : gammaNambu * gammaNambu = (1 : M8C) := by
  dsimp [gammaNambu]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    by_cases h0 : i.2.2 = 0 <;> simp [Matrix.diagonal, h0]
  · simp [Matrix.diagonal, h]

-- Commutation relations
@[simp] theorem gammaWedge_gammaChi_commute :
    gammaWedge * gammaChi = gammaChi * gammaWedge := by
  dsimp [gammaWedge, gammaChi]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal, mul_comm]

@[simp] theorem gammaWedge_gammaNambu_commute :
    gammaWedge * gammaNambu = gammaNambu * gammaWedge := by
  dsimp [gammaWedge, gammaNambu]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal, mul_comm]

@[simp] theorem gammaChi_gammaNambu_commute :
    gammaChi * gammaNambu = gammaNambu * gammaChi := by
  dsimp [gammaChi, gammaNambu]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal, mul_comm]

-- Z2 Parity definitions via Adjoint action
def WedgeParity (A : M8C) (ε : Fin 2) : Prop :=
  gammaWedge * A * gammaWedge = (if ε = 0 then A else -A)

def ChiralParity (A : M8C) (ε : Fin 2) : Prop :=
  gammaChi * A * gammaChi = (if ε = 0 then A else -A)

def NambuParity (A : M8C) (ε : Fin 2) : Prop :=
  gammaNambu * A * gammaNambu = (if ε = 0 then A else -A)

def Tridegree (A : M8C) (ε_W ε_Chi ε_N : Fin 2) : Prop :=
  WedgeParity A ε_W ∧ ChiralParity A ε_Chi ∧ NambuParity A ε_N

-- Grand Canonical Rindler-Chiral Weights
-- The thermodynamic partition structure separates the modular flow (beta_U) and chiral chemical potential
def grandCanonicalWeight (beta_U mu mu_chi : ℂ) : M8C :=
  Matrix.diagonal (fun i => 
    let sign_W := if i.1 = 0 then (1 : ℂ) else -1
    let sign_Chi := if i.2.1 = 0 then (1 : ℂ) else -1
    let sign_N := if i.2.2 = 0 then (1 : ℂ) else -1
    -- H_R is reversed in the left wedge (sign_W)
    Complex.exp (-beta_U * (sign_W * sign_N * 1 - mu - sign_Chi * mu_chi)))

end InfoGeometry.WedgeChiralNambuTrigrading
end noncomputable section
