import Mathlib
import InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform

/-!
# Dynamical Zeta Functions and the Milnor-Thurston Identity

Formalizes the fundamental definitions and structural identities for dynamical
zeta functions, based on "Fonctions zêta dynamiques" by Viviane Baladi.
-/

noncomputable section

namespace DynamicalZetaFunction

open Complex

/-- 
The finite-dimensional matrix determinant identity (Exercise 0):
det(I - zL) = exp(-sum_{n=1}^\infty (z^n / n) Tr(L^n))
This serves as the core algebraic identity motivating the definition of dynamical
zeta functions.
-/
def matrix_zeta_identity_prop {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 / (max 1 ‖Matrix.trace L‖) → 
    ((1 : Matrix (Fin n) (Fin n) ℂ) - z • L).det = 
    Complex.exp (- ∑' (k : ℕ), (z ^ (k + 1) / (k + 1 : ℂ)) * (L ^ (k + 1)).trace)

/--
The weighted Milnor-Thurston identity (Theorem 4).
For a transfer operator M and kneading operator D(z), the sharp determinant
factorizes via the trace of the Fredholm determinant of the kneading operator.
Det#(1 - z M) = 1 / Det_*(1 + D(z))
-/
def weighted_milnor_thurston_identity_prop
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (M : B →L[ℂ] B)
    (D : ℂ → B →L[ℂ] B)
    (Det_sharp : (B →L[ℂ] B) → ℂ)
    (Det_star : (B →L[ℂ] B) → ℂ) : Prop :=
  ∀ z : ℂ, Det_sharp (1 - z • M) = 1 / Det_star (1 + D z)

/--
The higher-dimensional Milnor-Thurston-Kitaev-Baillif formula (Theorem 1 in Chapter 3).
For a dynamical system on an n-dimensional manifold, the sharp determinant
factorizes into an alternating product of determinants over the k-forms.
-/
def higher_dim_milnor_thurston_prop
    (n : ℕ)
    (M : ℕ → Type)
    (D_k : ℕ → ℂ → ℂ)
    (Det_sharp : ℂ → ℂ)
    (Det_star : ℂ → ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Det_sharp z = ∏ k : Fin n, (Det_star z (D_k k.val z)) ^ ((-1 : ℂ)^(k.val + 1))

end DynamicalZetaFunction
