import proofs.TwoSheetKreinAdjoint

/-!
# Finite Krein/Tomita data on the six-state matrix algebra

This is the finite algebraic standard-form lane: the Hilbert--Schmidt carrier
is the matrix algebra itself and Tomita conjugation is conjugate-transpose.
No analytic unbounded Tomita--Takesaki theorem is claimed here.
-/

noncomputable section
namespace FiniteKreinTomitaSixState

open TwoSheetThreeColorWeyl
open TwoSheetKreinAdjoint

abbrev HilbertSchmidtSix := M6C

def tomita (A : HilbertSchmidtSix) : HilbertSchmidtSix := Matrix.conjTranspose A

def modularOperator (A : HilbertSchmidtSix) : HilbertSchmidtSix := A

@[simp] theorem tomita_involutive (A : HilbertSchmidtSix) :
    tomita (tomita A) = A := by
  simp [tomita]

theorem tomita_antimultiplicative (A B : HilbertSchmidtSix) :
    tomita (A * B) = tomita B * tomita A := by
  simp [tomita, Matrix.conjTranspose_mul]

@[simp] theorem modularOperator_identity (A : HilbertSchmidtSix) :
    modularOperator A = A := rfl

structure FiniteTomitaData (𝒜 : Type) where
  S : 𝒜 → 𝒜
  J : 𝒜 → 𝒜
  Delta : 𝒜 → 𝒜
  factorization : ∀ x, S x = J (Delta x)
  J_involutive : ∀ x, J (J x) = x

def finiteTomitaData :
    FiniteTomitaData HilbertSchmidtSix := by
  classical
  exact {
    S := tomita
    J := tomita
    Delta := modularOperator
    factorization := by intro A; rfl
    J_involutive := tomita_involutive
  }

theorem finiteTomitaData_J_involutive (A : HilbertSchmidtSix) :
    finiteTomitaData.J (finiteTomitaData.J A) = A :=
  finiteTomitaData.J_involutive A

end FiniteKreinTomitaSixState
end noncomputable section
