import InfoGeometry.Clifford.SplitQuaternion
import InfoGeometry.Clifford.UniversalCoverLog
import InfoGeometry.Projective.KleinFiniteLogFormCarrier
import Mathlib.Tactic

/-!
# Möbius root directions and logarithmic winding

This owner keeps two finite structures distinct:

* `rootPlus` and `rootMinus` are the two null/root directions in the single
  split-quaternion carrier.  They are not separate geometric sheets.
* `logCoordinate` is the additive coordinate on the existing universal-cover
  carrier `ℂ × ℤ`; its integer component records deck winding.

Only explicit algebraic identities are claimed here.  No global de Rham
classification or identification with a physical spacetime is introduced.
-/

namespace InfoGeometry.Projective.MobiusWindingRootBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.UniversalCoverLog

/-! ## The split null/root frame -/

/-- The split-quaternion element represented by the upper triangular root. -/
def rootPlus : SplitQuaternion := ⟨0, 1, 1, 0⟩

/-- The split-quaternion element represented by the lower triangular root. -/
def rootMinus : SplitQuaternion := ⟨0, 1, -1, 0⟩

/-- The diagonal Cartan direction in the same split-quaternion carrier. -/
def cartan : SplitQuaternion := ⟨0, 0, 0, 1⟩

/-- Coordinate subtraction on the explicit split-quaternion carrier. -/
def sqSub (q r : SplitQuaternion) : SplitQuaternion :=
  ⟨q.w - r.w, q.x - r.x, q.y - r.y, q.z - r.z⟩

/-- Scalar multiplication on the explicit split-quaternion coordinate carrier. -/
def sqScale (c : ℝ) (q : SplitQuaternion) : SplitQuaternion :=
  ⟨c * q.w, c * q.x, c * q.y, c * q.z⟩

theorem rootPlus_sq : rootPlus * rootPlus = 0 := by
  change sqMul rootPlus rootPlus = sqZero
  ext <;> simp [rootPlus, sqMul, sqZero]

theorem rootMinus_sq : rootMinus * rootMinus = 0 := by
  change sqMul rootMinus rootMinus = sqZero
  ext <;> simp [rootMinus, sqMul, sqZero]

theorem rootPlus_norm : norm rootPlus = 0 := by
  change (0 : ℝ) * 0 + 1 * 1 - 1 * 1 - 0 * 0 = 0
  norm_num

theorem rootMinus_norm : norm rootMinus = 0 := by
  change (0 : ℝ) * 0 + 1 * 1 - (-1) * (-1) - 0 * 0 = 0
  norm_num

theorem rootPlus_toMatrix : toMatrix rootPlus = !![(0 : ℝ), 2; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, rootPlus]

theorem rootMinus_toMatrix : toMatrix rootMinus = !![(0 : ℝ), 0; -2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, rootMinus]

theorem rootPlus_matrix_sq : toMatrix rootPlus * toMatrix rootPlus = 0 := by
  rw [rootPlus_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_matrix_sq : toMatrix rootMinus * toMatrix rootMinus = 0 := by
  rw [rootMinus_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rootPlus_matrix_det : (toMatrix rootPlus).det = 0 := by
  calc
    (toMatrix rootPlus).det = det_2x2 (toMatrix rootPlus) := by
      symm
      exact det_2x2_eq_matrix_det _
    _ = norm rootPlus := by symm; exact norm_eq_det rootPlus
    _ = 0 := rootPlus_norm

theorem rootMinus_matrix_det : (toMatrix rootMinus).det = 0 := by
  calc
    (toMatrix rootMinus).det = det_2x2 (toMatrix rootMinus) := by
      symm
      exact det_2x2_eq_matrix_det _
    _ = norm rootMinus := by symm; exact norm_eq_det rootMinus
    _ = 0 := rootMinus_norm

theorem cartan_rootPlus_commutator :
    sqSub (cartan * rootPlus) (rootPlus * cartan) =
      ⟨0, 2, 2, 0⟩ := by
  change sqSub (sqMul cartan rootPlus) (sqMul rootPlus cartan) = _
  ext <;> simp [sqSub, cartan, rootPlus, sqMul] <;> ring_nf

theorem cartan_rootMinus_commutator :
    sqSub (cartan * rootMinus) (rootMinus * cartan) =
      ⟨0, -2, 2, 0⟩ := by
  change sqSub (sqMul cartan rootMinus) (sqMul rootMinus cartan) = _
  ext <;> simp [sqSub, cartan, rootMinus, sqMul] <;> ring_nf

theorem cartan_rootPlus_weight :
    sqSub (cartan * rootPlus) (rootPlus * cartan) = sqScale 2 rootPlus := by
  rw [cartan_rootPlus_commutator]
  ext <;> simp [sqScale, rootPlus]

theorem cartan_rootMinus_weight :
    sqSub (cartan * rootMinus) (rootMinus * cartan) = sqScale (-2) rootMinus := by
  rw [cartan_rootMinus_commutator]
  ext <;> simp [sqScale, rootMinus]

/-! ## The finite Cartan flow and exchange inversion -/

/-- The diagonal Cartan matrix in the real `2 × 2` representation. -/
def cartanMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![(1 : ℝ), 0; 0, -1]

/-- The split exchange matrix exchanging the two Witt/root coordinates. -/
def rootExchange : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 1, 0]

/-- The finite real Cartan flow `diag(exp κ, exp (-κ))`. -/
noncomputable def cartanFlow (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp κ, 0; 0, Real.exp (-κ)]

theorem rootExchange_sq : rootExchange * rootExchange = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootExchange_conjugates_cartan :
    rootExchange * cartanMatrix * rootExchange = -cartanMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExchange, cartanMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem cartanFlow_neg (κ : ℝ) :
    cartanFlow (-κ) = !![Real.exp (-κ), 0; 0, Real.exp κ] := by
  simp [cartanFlow, neg_neg]

theorem rootExchange_conjugates_cartanFlow (κ : ℝ) :
    rootExchange * cartanFlow κ * rootExchange = cartanFlow (-κ) := by
  rw [cartanFlow_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExchange, cartanFlow, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootExchange_conjugates_rootPlus :
    rootExchange * toMatrix rootPlus * rootExchange = -toMatrix rootMinus := by
  rw [rootPlus_toMatrix, rootMinus_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExchange, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootExchange_conjugates_rootMinus :
    rootExchange * toMatrix rootMinus * rootExchange = -toMatrix rootPlus := by
  rw [rootPlus_toMatrix, rootMinus_toMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExchange, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The logarithmic coordinate and deck winding -/

/-- A logarithmic coordinate is a point of the existing universal cover. -/
abbrev LogCoordinate : Type := UniversalCover

/-- The additive logarithmic coordinate on the universal cover. -/
noncomputable def logCoordinate (p : LogCoordinate) : ℂ := uLog p

theorem logCoordinate_deck_up (z : ℂ) (n : ℤ) :
    logCoordinate (deckUp (z, n)) =
      logCoordinate (z, n) + 2 * Real.pi * Complex.I := by
  exact uLog_deck_up z n

theorem logCoordinate_deck_down (z : ℂ) (n : ℤ) :
    logCoordinate (deckDown (z, n)) =
      logCoordinate (z, n) - 2 * Real.pi * Complex.I := by
  exact uLog_deck_down z n

theorem deckUp_deckDown (z : ℂ) (n : ℤ) :
    deckUp (deckDown (z, n)) = (z, n) := by
  simp [deckUp, deckDown]

theorem deckDown_deckUp (z : ℂ) (n : ℤ) :
    deckDown (deckUp (z, n)) = (z, n) := by
  simp [deckUp, deckDown]

theorem logCoordinate_sheet_add (z : ℂ) (n k : ℤ) :
    logCoordinate (z, n + k) =
      logCoordinate (z, n) +
        (2 * Real.pi * Complex.I : ℂ) * (k : ℂ) := by
  exact uLog_sheet_add z n k

theorem logCoordinate_deck_additive (z : ℂ) (n k l : ℤ) :
    logCoordinate (z, n + k + l) =
      logCoordinate (z, n) +
        (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) + (l : ℂ)) := by
  rw [logCoordinate_sheet_add z (n + k) l]
  rw [logCoordinate_sheet_add z n k]
  ring

end InfoGeometry.Projective.MobiusWindingRootBridge
