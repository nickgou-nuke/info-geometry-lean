import Mathlib.Algebra.Lie.Basic
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.OperatorAlgebra.SplitOctonionDerivationWitness
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Split-octonion derivation-space packet

Defines the elementary derivation-space bracket and connects the canonical
split-octonion derivation owner to its native fourteen-dimensional and
standard-derivation spanning theorems.
-/

noncomputable section

namespace InfoGeometry.Lie.G2FromSplitOctonions

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationWitness

def DerivSpace : Type := SplitOct → SplitOct

def bracket (D₁ D₂ : DerivSpace) : DerivSpace := fun X => subZ (D₁ (D₂ X)) (D₂ (D₁ X))

def IsDeriv (D : DerivSpace) : Prop :=
  (∀ X Y, D (addZ X Y) = addZ (D X) (D Y)) ∧
    (∀ X, D (negZ X) = negZ (D X)) ∧
      ∀ X Y, D (mulZ X Y) = addZ (mulZ (D X) Y) (mulZ X (D Y))

theorem rot01_preserves_add (X Y : SplitOct) :
    rot01Derivation (addZ X Y) =
      addZ (rot01Derivation X) (rot01Derivation Y) := by
  cases X
  cases Y
  unfold rot01Derivation addZ
  congr <;> ring

theorem rot01_preserves_neg (X : SplitOct) :
    rot01Derivation (negZ X) = negZ (rot01Derivation X) := by
  cases X
  unfold rot01Derivation negZ
  rfl

theorem bracket_closed {D₁ D₂ : DerivSpace} (hD1 : IsDeriv D₁) (hD2 : IsDeriv D₂) :
    IsDeriv (bracket D₁ D₂) := by
  rcases hD1 with ⟨hD1_add, hD1_neg, hD1_mul⟩
  rcases hD2 with ⟨hD2_add, hD2_neg, hD2_mul⟩
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    unfold bracket
    rw [hD2_add X Y, hD1_add (D₂ X) (D₂ Y),
      hD1_add X Y, hD2_add (D₁ X) (D₁ Y)]
    ext <;> simp [addZ, subZ] <;> ring
  · intro X
    unfold bracket
    rw [hD2_neg X, hD1_neg (D₂ X), hD1_neg X, hD2_neg (D₁ X)]
    ext <;> simp [negZ, subZ] <;> ring
  · intro X Y
    unfold bracket
    rw [hD2_mul X Y, hD1_add (mulZ (D₂ X) Y) (mulZ X (D₂ Y)),
      hD1_mul (D₂ X) Y, hD1_mul X (D₂ Y),
      hD1_mul X Y, hD2_add (mulZ (D₁ X) Y) (mulZ X (D₁ Y)),
      hD2_mul (D₁ X) Y, hD2_mul X (D₁ Y)]
    ext <;> simp [addZ, subZ, mulZ] <;> ring

-- Concrete derivation
theorem D01_deriv : IsDeriv rot01Derivation :=
  ⟨rot01_preserves_add, rot01_preserves_neg, rot01_is_derivation⟩

end InfoGeometry.Lie.G2FromSplitOctonions

noncomputable section
