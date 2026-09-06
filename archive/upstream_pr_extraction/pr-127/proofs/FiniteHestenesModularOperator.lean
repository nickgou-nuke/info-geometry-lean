import proofs.FiniteHestenesTomitaBridge

/-! # Finite modular operator on the Hestenes standard form

This owner packages an invertible self-adjoint matrix `ρ` together with its
explicit inverse.  On the Hilbert--Schmidt carrier it defines

`Δρ(X) = ρ X ρ⁻¹`

and proves the finite Tomita relation `J₀ Δρ J₀ = Δρ⁻¹`.  The construction is
then transported through the genuine real algebra equivalence
`Cl⁺(1,3) ≃ₐ[ℝ] M₂(ℂ)`.

No positivity, logarithm, unbounded functional calculus, or analytic
Tomita--Takesaki theorem is asserted here.
-/

noncomputable section
namespace FiniteHestenesModularOperator

open HestenesCl14
open HestenesEvenPauliEquiv
open FiniteHestenesTomitaBridge

/-- Algebraic finite-dimensional faithful-density datum.  Positivity is kept
outside this owner; the fields record exactly what the modular identities use. -/
structure ModularDatum where
  rho : HS2
  rhoInv : HS2
  rho_mul_rhoInv : rho * rhoInv = 1
  rhoInv_mul_rho : rhoInv * rho = 1
  rho_selfAdjoint : matrixTomita rho = rho
  rhoInv_selfAdjoint : matrixTomita rhoInv = rhoInv

namespace ModularDatum

def delta (d : ModularDatum) (X : HS2) : HS2 :=
  d.rho * X * d.rhoInv

def deltaInv (d : ModularDatum) (X : HS2) : HS2 :=
  d.rhoInv * X * d.rho

@[simp] theorem delta_zero (d : ModularDatum) : d.delta 0 = 0 := by
  simp [delta]

@[simp] theorem delta_add (d : ModularDatum) (X Y : HS2) :
    d.delta (X + Y) = d.delta X + d.delta Y := by
  simp [delta, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem deltaInv_delta (d : ModularDatum) (X : HS2) :
    d.deltaInv (d.delta X) = X := by
  simp only [delta, deltaInv]
  calc
    d.rhoInv * (d.rho * X * d.rhoInv) * d.rho =
        (d.rhoInv * d.rho) * X * (d.rhoInv * d.rho) := by
          simp only [Matrix.mul_assoc]
    _ = X := by rw [d.rhoInv_mul_rho]; simp

@[simp] theorem delta_deltaInv (d : ModularDatum) (X : HS2) :
    d.delta (d.deltaInv X) = X := by
  simp only [delta, deltaInv]
  calc
    d.rho * (d.rhoInv * X * d.rho) * d.rhoInv =
        (d.rho * d.rhoInv) * X * (d.rho * d.rhoInv) := by
          simp only [Matrix.mul_assoc]
    _ = X := by rw [d.rho_mul_rhoInv]; simp

/-- Finite algebraic form of `J₀ Δρ J₀ = Δρ⁻¹`. -/
theorem tomita_delta_tomita (d : ModularDatum) (X : HS2) :
    matrixTomita (d.delta (matrixTomita X)) = d.deltaInv X := by
  simp [delta, deltaInv, matrixTomita_antimultiplicative,
    d.rho_selfAdjoint, d.rhoInv_selfAdjoint, Matrix.mul_assoc]

def cliffordDelta (d : ModularDatum) (x : ClPlus14) : ClPlus14 :=
  clPlusPauliAlgEquiv.symm (d.delta (clPlusPauliAlgEquiv x))

def cliffordDeltaInv (d : ModularDatum) (x : ClPlus14) : ClPlus14 :=
  clPlusPauliAlgEquiv.symm (d.deltaInv (clPlusPauliAlgEquiv x))

@[simp] theorem map_cliffordDelta (d : ModularDatum) (x : ClPlus14) :
    clPlusPauliAlgEquiv (d.cliffordDelta x) =
      d.delta (clPlusPauliAlgEquiv x) := by
  simp [cliffordDelta]

@[simp] theorem map_cliffordDeltaInv (d : ModularDatum) (x : ClPlus14) :
    clPlusPauliAlgEquiv (d.cliffordDeltaInv x) =
      d.deltaInv (clPlusPauliAlgEquiv x) := by
  simp [cliffordDeltaInv]

@[simp] theorem cliffordDeltaInv_delta (d : ModularDatum) (x : ClPlus14) :
    d.cliffordDeltaInv (d.cliffordDelta x) = x := by
  apply clPlusPauliAlgEquiv.injective
  simp

@[simp] theorem cliffordDelta_deltaInv (d : ModularDatum) (x : ClPlus14) :
    d.cliffordDelta (d.cliffordDeltaInv x) = x := by
  apply clPlusPauliAlgEquiv.injective
  simp

/-- Native Clifford pullback of `J₀ Δρ J₀ = Δρ⁻¹`. -/
theorem cliffordTomita_delta_tomita (d : ModularDatum) (x : ClPlus14) :
    cliffordTomita (d.cliffordDelta (cliffordTomita x)) =
      d.cliffordDeltaInv x := by
  apply clPlusPauliAlgEquiv.injective
  simp [tomita_delta_tomita]

theorem finite_modular_packet (d : ModularDatum) :
    (∀ X : HS2, d.deltaInv (d.delta X) = X) ∧
      (∀ X : HS2, d.delta (d.deltaInv X) = X) ∧
      (∀ X : HS2,
        matrixTomita (d.delta (matrixTomita X)) = d.deltaInv X) ∧
      (∀ x : ClPlus14,
        cliffordTomita (d.cliffordDelta (cliffordTomita x)) =
          d.cliffordDeltaInv x) := by
  exact ⟨d.deltaInv_delta, d.delta_deltaInv, d.tomita_delta_tomita,
    d.cliffordTomita_delta_tomita⟩

end ModularDatum
end FiniteHestenesModularOperator
end noncomputable section
