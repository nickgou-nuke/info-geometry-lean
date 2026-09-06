import InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge

/-!
# Conditional chiral/Hodge equivariance on the `Cl(5,5)` spinor carrier

This module records the exact transport needed by a future concrete
exceptional action.  The Hodge operator is an explicit parameter: no
unproved identification with a `G₂` action is introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.G2Cl55ChiralHodgeEquivarianceBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.G2Cl55ChiralEquivarianceBridge
open InfoGeometry.Clifford.SpinorRep

def chiralDiracPlus (H : SpinorMatrix 5) : SpinorMatrix 5 :=
  chiralPlusProjector * H

def chiralDiracMinus (H : SpinorMatrix 5) : SpinorMatrix 5 :=
  chiralMinusProjector * H

theorem commutes_chiralDiracPlus
    (A H : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A)
    (hH : A * H = H * A) :
    A * chiralDiracPlus H = chiralDiracPlus H * A := by
  have hP := commutes_chiralPlusProjector_of_commutes_chirality A hA
  dsimp [chiralDiracPlus]
  calc
    A * (chiralPlusProjector * H) = (A * chiralPlusProjector) * H := by
      rw [mul_assoc]
    _ = (chiralPlusProjector * A) * H := by rw [hP]
    _ = chiralPlusProjector * (A * H) := by rw [mul_assoc]
    _ = chiralPlusProjector * (H * A) := by rw [hH]
    _ = (chiralPlusProjector * H) * A := by rw [mul_assoc]

theorem commutes_chiralDiracMinus
    (A H : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A)
    (hH : A * H = H * A) :
    A * chiralDiracMinus H = chiralDiracMinus H * A := by
  have hP := commutes_chiralMinusProjector_of_commutes_chirality A hA
  dsimp [chiralDiracMinus]
  calc
    A * (chiralMinusProjector * H) = (A * chiralMinusProjector) * H := by
      rw [mul_assoc]
    _ = (chiralMinusProjector * A) * H := by rw [hP]
    _ = chiralMinusProjector * (A * H) := by rw [mul_assoc]
    _ = chiralMinusProjector * (H * A) := by rw [hH]
    _ = (chiralMinusProjector * H) * A := by rw [mul_assoc]

theorem commutes_chiralDirac_pair
    (A H : SpinorMatrix 5)
    (hA : A * chirality55 = chirality55 * A)
    (hH : A * H = H * A) :
    A * chiralDiracPlus H = chiralDiracPlus H * A ∧
      A * chiralDiracMinus H = chiralDiracMinus H * A := by
  exact ⟨commutes_chiralDiracPlus A H hA hH,
    commutes_chiralDiracMinus A H hA hH⟩

end InfoGeometry.Clifford.G2Cl55ChiralHodgeEquivarianceBridge
