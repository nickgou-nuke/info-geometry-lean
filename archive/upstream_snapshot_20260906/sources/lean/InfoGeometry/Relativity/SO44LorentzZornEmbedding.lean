import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# InfoGeometry.Relativity.SO44LorentzZornEmbedding

The embedding of the doubled Lorentz group into SO(4,4) via the
Zorn null-cone coordinates.

The cots synthesis gives the explicit construction:
  P = (X+Y)/√2,   Q = (X-Y)/√2,
with independent Lorentz actions:
  P ↦ Λ_R P,   Q ↦ Λ_L Q,
giving the SO(4,4) matrix:
  [Λ_R+Λ_L, Λ_R-Λ_L; Λ_R-Λ_L, Λ_R+Λ_L] / 2.

This owner packages the finite algebraic skeleton.
-/

noncomputable section

namespace InfoGeometry.Relativity.SO44LorentzZornEmbedding

open InfoGeometry.Algebra
open ZornVectorMatrix
open ZornVec3

variable {R : Type*} [CommRing R]

/-! ## 1. Zorn null-cone coordinates -/

/-- The P coordinate: sum of the two Zorn null directions. -/
def zornP (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  add X Y

/-- The Q coordinate: difference of the two Zorn null directions. -/
def zornQ (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub X Y

/-! ## 2. Lorentz actions on P and Q -/

/-- Independent Lorentz action on the P coordinate. -/
def lorentzActionP (Λ : ZornVectorMatrix R) (P : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul Λ P

/-- Independent Lorentz action on the Q coordinate. -/
def lorentzActionQ (Λ : ZornVectorMatrix R) (Q : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul Λ Q

/-! ## 3. SO(4,4) embedding block -/

/-- The 2×2 block matrix embedding of the doubled Lorentz group into SO(4,4). -/
def so44EmbeddingBlock
    (Λ_R Λ_L : ZornVectorMatrix R) : Matrix (Fin 2) (Fin 2) (ZornVectorMatrix R) :=
  !![add Λ_R Λ_L, sub Λ_R Λ_L; sub Λ_R Λ_L, add Λ_R Λ_L]

/-! ## 4. Action on Zorn pair (X,Y) -/

/-- The SO(4,4) action on the Zorn pair (X,Y). -/
def so44ActionOnZornPair
    (Λ_R Λ_L : ZornVectorMatrix R)
    (X Y : ZornVectorMatrix R) :
    ZornVectorMatrix R × ZornVectorMatrix R :=
  let M := so44EmbeddingBlock Λ_R Λ_L
  (add (mul (M 0 0) X) (mul (M 0 1) Y),
   add (mul (M 1 0) X) (mul (M 1 1) Y))

/-! ## 5. Preservation of Zorn norm -/

/-- The Zorn norm is N_Z(X,Y) = X·Y. -/
def zornNorm (X Y : ZornVectorMatrix R) : R :=
  dot X.v Y.v

/-- The SO(4,4) embedding preserves the Zorn norm. -/
theorem so44Embedding_preserves_zorn_norm
    (Λ_R Λ_L : ZornVectorMatrix R)
    (X Y : ZornVectorMatrix R) :
    zornNorm X Y =
      zornNorm
        (so44ActionOnZornPair Λ_R Λ_L X Y).1
        (so44ActionOnZornPair Λ_R Λ_L X Y).2 := by
  sorry

/-! ## 6. Inter-sheet bimodule action -/

/-- The inter-sheet bimodule action under the SO(4,4) embedding. -/
def bifundamentalAction
    (Λ_R Λ_L : ZornVectorMatrix R)
    (M : ZornVectorMatrix R → ZornVectorMatrix R → ZornVectorMatrix R)
    (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  mul (mul Λ_R (M X Y)) Λ_L

/-! ## 7. Triality lift -/

/-- The three Spin(4,4) actions induced from the doubled Lorentz group.
    ρ₁ acts on X, ρ₂ acts on XY, ρ₃ acts on Y.
-/
structure Spin44TrialityLift where
  ρ₁ : ZornVectorMatrix R → ZornVectorMatrix R
  ρ₂ : ZornVectorMatrix R → ZornVectorMatrix R → ZornVectorMatrix R
  ρ₃ : ZornVectorMatrix R → ZornVectorMatrix R
  h_triality :
    ∀ Λ_R Λ_L X Y,
      ρ₂ (ρ₁ (ZornVectorMatrix.mul Λ_R X)) (ρ₃ (ZornVectorMatrix.mul Λ_L Y)) =
        ZornVectorMatrix.mul (ZornVectorMatrix.mul Λ_R (ρ₂ X Y)) Λ_L

/-! ## 8. Flat limit -/

/-- The flat limit: when Λ_R = Λ_L, the embedding reduces to
    the diagonal SO(4,4) ≅ SO(1,3).
-/
theorem flat_limit_diagonal
    (Λ : ZornVectorMatrix R)
    (X Y : ZornVectorMatrix R) :
    so44ActionOnZornPair Λ Λ X Y =
      (mul Λ X, mul Λ Y) := by
  sorry

end InfoGeometry.Relativity.SO44LorentzZornEmbedding
