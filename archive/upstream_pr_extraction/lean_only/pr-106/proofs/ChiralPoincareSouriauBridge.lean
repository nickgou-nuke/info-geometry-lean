import Mathlib

/-!
# Chiral supercharges, Poincaré momentum, and Souriau beta vector

This file is the finite Pauli-soldering bridge:

* a Minkowski four-vector `P = (E,px,py,pz)` is encoded as the Hermitian
  spinor matrix `P_{α dotα}=P_μ σ^μ_{α dotα}`;
* the chiral SUSY relation is recorded as
  `{Q_α,Q̄_dotα}=2 P_{α dotα}`;
* the inverse Pauli traces recover `E,px,py,pz`;
* `det(P_μ σ^μ)=E²-px²-py²-pz²`, the mass Casimir;
* a Souriau inverse-temperature vector `β^μ=u^μ/T` is the dual covector paired
  with momentum.

The supercharge anticommutator is represented by concrete matrix data satisfying
the displayed equation; the file proves the Pauli/Poincaré/Souriau algebraic
identities that follow from it.
-/

noncomputable section

namespace ChiralPoincareSouriauBridge

open Matrix
open scoped BigOperators

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli σ₁. -/
def σ1 : M2C := !![0, 1; 1, 0]

/-- Pauli σ₂. -/
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]

/-- Pauli σ₃. -/
def σ3 : M2C := !![1, 0; 0, -1]

/-- A complexified momentum four-vector. -/
structure FourMomentum where
  E : ℂ
  px : ℂ
  py : ℂ
  pz : ℂ

/-- Minkowski quadratic/Casimir with mostly-minus convention. -/
def minkowskiSq (P : FourMomentum) : ℂ :=
  P.E ^ 2 - P.px ^ 2 - P.py ^ 2 - P.pz ^ 2

/-- Pauli soldering: `P_{α dotα}=P_μ σ^μ_{α dotα}`. -/
def pauliMomentum (P : FourMomentum) : M2C :=
  !![P.E + P.pz, P.px - Complex.I * P.py;
     P.px + Complex.I * P.py, P.E - P.pz]

/-- Explicit determinant of the Pauli-soldered momentum matrix: the mass Casimir. -/
theorem det_pauliMomentum (P : FourMomentum) :
    (pauliMomentum P).det = minkowskiSq P := by
  cases P with
  | mk E px py pz =>
    simp [pauliMomentum, minkowskiSq]
    ring_nf
    simp [Complex.I_mul_I]
    ring

/-- Chiral super-Poincaré relation: the odd anticommutator matrix is `2P`. -/
structure ChiralSUSYMomentum where
  P : FourMomentum
  antiQQbar : M2C
  susy_anticomm : antiQQbar = (2 : ℂ) • pauliMomentum P

/-- Momentum spinor matrix from the supercharge anticommutator. -/
def momentumSpinorFromSupercharges (S : ChiralSUSYMomentum) : M2C :=
  (1 / 2 : ℂ) • S.antiQQbar

/-- The supercharge square/anticommutator recovers the Pauli-soldered momentum. -/
theorem momentum_from_supercharges (S : ChiralSUSYMomentum) :
    momentumSpinorFromSupercharges S = pauliMomentum S.P := by
  rw [momentumSpinorFromSupercharges, S.susy_anticomm]
  ext i j
  simp [Matrix.smul_apply]

/-- Energy recovered by inverse Pauli trace. -/
def recoverE (A : M2C) : ℂ := (1 / 2 : ℂ) * Matrix.trace A

/-- x-momentum recovered by inverse Pauli trace. -/
def recoverPx (A : M2C) : ℂ := (1 / 2 : ℂ) * Matrix.trace (A * σ1)

/-- y-momentum recovered by inverse Pauli trace. -/
def recoverPy (A : M2C) : ℂ := (1 / 2 : ℂ) * Matrix.trace (A * σ2)

/-- z-momentum recovered by inverse Pauli trace. -/
def recoverPz (A : M2C) : ℂ := (1 / 2 : ℂ) * Matrix.trace (A * σ3)

@[simp] theorem recoverE_pauliMomentum (P : FourMomentum) :
    recoverE (pauliMomentum P) = P.E := by
  cases P with
  | mk E px py pz =>
    simp [recoverE, pauliMomentum, Matrix.trace, Fin.sum_univ_two]
    ring

@[simp] theorem recoverPx_pauliMomentum (P : FourMomentum) :
    recoverPx (pauliMomentum P) = P.px := by
  cases P with
  | mk E px py pz =>
    simp [recoverPx, pauliMomentum, σ1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[simp] theorem recoverPy_pauliMomentum (P : FourMomentum) :
    recoverPy (pauliMomentum P) = P.py := by
  cases P with
  | mk E px py pz =>
    simp [recoverPy, pauliMomentum, σ2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
    ring_nf
    simp [Complex.I_mul_I]

@[simp] theorem recoverPz_pauliMomentum (P : FourMomentum) :
    recoverPz (pauliMomentum P) = P.pz := by
  cases P with
  | mk E px py pz =>
    simp [recoverPz, pauliMomentum, σ3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The inverse Pauli transform recovers all four components from `{Q,Q̄}/2`. -/
theorem supercharge_pauli_inverse (S : ChiralSUSYMomentum) :
    recoverE (momentumSpinorFromSupercharges S) = S.P.E ∧
    recoverPx (momentumSpinorFromSupercharges S) = S.P.px ∧
    recoverPy (momentumSpinorFromSupercharges S) = S.P.py ∧
    recoverPz (momentumSpinorFromSupercharges S) = S.P.pz := by
  rw [momentum_from_supercharges S]
  simp

/-! ## Twistor/null factorization -/

/-- Rank-one spinor-helicity/twistor momentum `λ_α \tilde λ_{dotα}`. -/
def spinorOuter (lam mu : Fin 2 → ℂ) : M2C := fun i j => lam i * mu j

/-- A factorized twistor momentum is null: its determinant vanishes. -/
theorem det_spinorOuter_zero (lam mu : Fin 2 → ℂ) :
    (spinorOuter lam mu).det = 0 := by
  simp [spinorOuter, Matrix.det_fin_two]
  ring

/-! ## Souriau beta vector -/

/-- Complexified Souriau inverse-temperature four-vector. -/
structure BetaVector where
  b0 : ℂ
  bx : ℂ
  bY : ℂ
  bz : ℂ

/-- Mostly-minus pairing `β·P`. -/
def betaPair (β : BetaVector) (P : FourMomentum) : ℂ :=
  β.b0 * P.E - β.bx * P.px - β.bY * P.py - β.bz * P.pz

/-- The beta vector is soldered by the same Pauli map. -/
def pauliBeta (β : BetaVector) : M2C :=
  pauliMomentum ⟨β.b0, β.bx, β.bY, β.bz⟩

/-- `det(β_μ σ^μ)=β²`, the thermal/Souriau norm. -/
theorem det_pauliBeta (β : BetaVector) :
    (pauliBeta β).det = β.b0 ^ 2 - β.bx ^ 2 - β.bY ^ 2 - β.bz ^ 2 := by
  simpa [pauliBeta, minkowskiSq] using
    det_pauliMomentum ⟨β.b0, β.bx, β.bY, β.bz⟩

/-- If `β^μ = γ/T (1,vx,vy,vz)` and `γ²(1-v²)=1`, then `β²=1/T²`. -/
theorem souriau_beta_norm
    (T γ vx vy vz : ℂ)
    (hγ : γ ^ 2 * (1 - vx ^ 2 - vy ^ 2 - vz ^ 2) = 1) :
    let β : BetaVector :=
      ⟨γ / T, γ * vx / T, γ * vy / T, γ * vz / T⟩
    β.b0 ^ 2 - β.bx ^ 2 - β.bY ^ 2 - β.bz ^ 2 = (T ^ 2)⁻¹ := by
  dsimp
  calc
    (γ / T) ^ 2 - (γ * vx / T) ^ 2 - (γ * vy / T) ^ 2 - (γ * vz / T) ^ 2
        = (γ ^ 2 * (1 - vx ^ 2 - vy ^ 2 - vz ^ 2)) / T ^ 2 := by ring
    _ = (T ^ 2)⁻¹ := by rw [hγ]; ring

/-- Compact synthesis theorem for the bridge. -/
theorem chiral_poincare_souriau_bridge_synthesis (S : ChiralSUSYMomentum) :
    momentumSpinorFromSupercharges S = pauliMomentum S.P ∧
    (pauliMomentum S.P).det = minkowskiSq S.P ∧
    recoverE (momentumSpinorFromSupercharges S) = S.P.E ∧
    recoverPx (momentumSpinorFromSupercharges S) = S.P.px ∧
    recoverPy (momentumSpinorFromSupercharges S) = S.P.py ∧
    recoverPz (momentumSpinorFromSupercharges S) = S.P.pz := by
  exact ⟨momentum_from_supercharges S, det_pauliMomentum S.P,
    (supercharge_pauli_inverse S).1,
    (supercharge_pauli_inverse S).2.1,
    (supercharge_pauli_inverse S).2.2.1,
    (supercharge_pauli_inverse S).2.2.2⟩

#check det_pauliMomentum
#check momentum_from_supercharges
#check det_spinorOuter_zero
#check souriau_beta_norm
#check chiral_poincare_souriau_bridge_synthesis

end ChiralPoincareSouriauBridge
