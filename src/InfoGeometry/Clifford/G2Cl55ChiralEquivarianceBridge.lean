import InfoGeometry.Clifford.Clifford55ChiralHyperbolicStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge

/-!
# Chiral equivariance interface for the native `Cl(5,5)` spinor carrier

This owner isolates the representation-theoretic transport theorem needed by
future `G₂` actions.  It does not claim that a particular `G₂` action has
already been identified with a `SpinorMatrix 5`; instead it proves that any
matrix action commuting with the ordered chirality preserves both chiral
projectors.  Concrete actions can consume this interface once their carrier
map and chirality-commutation theorem are available.
-/

noncomputable section

namespace InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.SpinorRep

theorem commutes_chiralPlusProjector_of_commutes_chirality
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A) :
    A * chiralPlusProjector = chiralPlusProjector * A := by
  rw [chiralPlusProjector, Algebra.mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, hA]
  simp only [mul_one, one_mul]

theorem commutes_chiralMinusProjector_of_commutes_chirality
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A) :
    A * chiralMinusProjector = chiralMinusProjector * A := by
  rw [chiralMinusProjector, Algebra.mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, hA]
  simp only [mul_one, one_mul]

theorem preserves_chiralProjectors_of_commutes_chirality
    (A : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A) :
    A * chiralPlusProjector = chiralPlusProjector * A ∧
      A * chiralMinusProjector = chiralMinusProjector * A := by
  exact ⟨commutes_chiralPlusProjector_of_commutes_chirality A hA,
    commutes_chiralMinusProjector_of_commutes_chirality A hA⟩

theorem spinBivector_preserves_chiralProjectors
    (X : SpinBivector55)
    (hX : spinBivectorMatrixLieHom X * chirality55 =
      chirality55 * spinBivectorMatrixLieHom X) :
    spinBivectorMatrixLieHom X * chiralPlusProjector =
        chiralPlusProjector * spinBivectorMatrixLieHom X ∧
      spinBivectorMatrixLieHom X * chiralMinusProjector =
        chiralMinusProjector * spinBivectorMatrixLieHom X := by
  exact preserves_chiralProjectors_of_commutes_chirality
    (spinBivectorMatrixLieHom X) hX

end InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge
