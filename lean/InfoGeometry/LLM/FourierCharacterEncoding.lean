import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.LLM

/-! # Fourier/character positional kernels

For an additive position space, a Fourier mode is represented by a monoid
homomorphism into the multiplicative group of nonzero complex numbers.  This
file keeps the character layer separate from any choice of finite sampling
set or normalization of a DFT.
-/

structure FourierCharacter (G : Type*) [AddMonoid G] where
  toFun : G → ℂˣ
  map_zero' : toFun 0 = 1
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y

instance {G : Type*} [AddMonoid G] : CoeFun (FourierCharacter G) (fun _ => G → ℂˣ) :=
  ⟨FourierCharacter.toFun⟩

def fourierCharacterKernel {G : Type*} [AddMonoid G]
    (χ : FourierCharacter G) (t s : G) : ℂ :=
  (χ (t + s) : ℂ)

theorem fourierCharacterKernel_eq_relative {G : Type*} [AddGroup G]
    (χ : FourierCharacter G) (t s : G) :
    fourierCharacterKernel χ t (-s) = χ (t - s) := by
  simp [fourierCharacterKernel, sub_eq_add_neg]

theorem fourierCharacterKernel_add_left {G : Type*} [AddCommGroup G]
    (χ : FourierCharacter G) (a t s : G) :
    fourierCharacterKernel χ (a + t) (- (a + s)) =
      fourierCharacterKernel χ t (-s) := by
  simp only [fourierCharacterKernel]
  have h : a + t + -(a + s) = t + -s := by abel
  rw [h]

theorem fourierCharacterKernel_additive_law {G : Type*} [AddGroup G]
    (χ : FourierCharacter G) (t s u : G) :
    fourierCharacterKernel χ (t + s) (-u) =
      (χ t : ℂ) * fourierCharacterKernel χ s (-u) := by
  simp only [fourierCharacterKernel]
  convert congrArg (fun z : ℂˣ => (z : ℂ))
    (χ.map_add' t (s + -u)) using 1 <;> rw [add_assoc]

theorem fourierCharacterKernel_zero {G : Type*} [AddGroup G]
    (χ : FourierCharacter G) (t : G) :
    fourierCharacterKernel χ t (-t) = 1 := by
  simpa [fourierCharacterKernel] using congrArg (fun z : ℂˣ => (z : ℂ)) χ.map_zero'

end InfoGeometry.LLM
