import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Perjes conventions on the existing Penrose carrier

The paper uses `omega = -i X pi`; the existing incidence owner uses `+i`.
The Witt pairing and diagonal `(2,2)` pairing are related by an explicit
complex-linear equivalence with factor two, not by identifying coordinates.
-/

noncomputable section
namespace InfoGeometry.Twistor.PerjesConventions

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.PenroseTwistor
open scoped BigOperators Matrix

/-- Change only the upper spinor sign. -/
def incidenceSign : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (-Z.1, Z.2)
  invFun Z := (-Z.1, Z.2)
  left_inv Z := by simp
  right_inv Z := by simp
  map_add' Z W := by ext <;> simp [add_comm]
  map_smul' c Z := by ext <;> simp

/-- Equation (3.7), with the sign used in KFKI-1980-76. -/
def paperIncidence (X : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 :=
  incidenceSign.toLinearMap.comp (incidenceLinearMap X)

@[simp] theorem paperIncidence_apply (X : ComplexSpacetime) (pi : Spinor2) :
    paperIncidence X pi = (-Complex.I • X.mulVec pi, pi) := by
  ext <;> simp [paperIncidence, incidenceSign, incidenceLinearMap, omegaLinearMap]

@[simp] theorem incidenceSign_involutive (Z : Twistor4) :
    incidenceSign (incidenceSign Z) = Z := by ext <;> simp [incidenceSign]

/-- Hermitian form in the incidence (Witt) frame, conjugate-linear on the left. -/
def wittPair (Z W : Twistor4) : ℂ :=
  (∑ a : Fin 2, star (Z.1 a) * W.2 a) +
    ∑ a : Fin 2, star (Z.2 a) * W.1 a

/-- The dual-valued conjugation in the incidence frame. -/
def wittDual (Z : Twistor4) : Module.Dual ℂ Twistor4 where
  toFun W := wittPair Z W
  map_add' W V := by simp [wittPair, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c W := by simp [wittPair, Fin.sum_univ_two, smul_eq_mul]; ring

@[simp] theorem wittPair_conj (Z W : Twistor4) :
    star (wittPair Z W) = wittPair W Z := by
  simp [wittPair, Fin.sum_univ_two, mul_comm]
  ring

@[simp] theorem wittPair_smul (c : ℂ) (Z W : Twistor4) :
    wittPair (c • Z) (c • W) = (star c * c) * wittPair Z W := by
  simp [wittPair, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- The sign adapter reverses the Witt pairing; it preserves its null cone. -/
theorem wittPair_incidenceSign (Z W : Twistor4) :
    wittPair (incidenceSign Z) (incidenceSign W) = -wittPair Z W := by
  simp [wittPair, incidenceSign, Fin.sum_univ_two]
  ring

/-- Unnormalized Witt-to-diagonal change of basis. Its norm multiplier is two. -/
def wittToDiagonal : Twistor4 ≃ₗ[ℂ] TwistorCarrier where
  toFun Z := ![Z.1 0 + Z.2 0, Z.1 1 + Z.2 1,
                Z.1 0 - Z.2 0, Z.1 1 - Z.2 1]
  invFun z := ((fun a => if a = 0 then (z 0 + z 2) / 2 else (z 1 + z 3) / 2),
               (fun a => if a = 0 then (z 0 - z 2) / 2 else (z 1 - z 3) / 2))
  left_inv Z := by ext a <;> fin_cases a <;> simp
  right_inv z := by ext a; fin_cases a <;> simp <;> ring
  map_add' Z W := by ext a; fin_cases a <;> simp <;> ring
  map_smul' c Z := by ext a; fin_cases a <;> simp [smul_eq_mul] <;> ring

/-- Exact transport of the Hermitian form, including the normalization. -/
theorem diagonal_pairing (Z W : Twistor4) :
    twistorHermitian (wittToDiagonal Z) (wittToDiagonal W) = 2 * wittPair Z W := by
  simp [twistorHermitian_apply, wittToDiagonal, wittPair,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

/-- Classical helicity in equation (6.6), not a projectively invariant number. -/
def paperHelicity (Z : Twistor4) : ℝ := (wittPair Z Z).re / 2

theorem diagonal_helicity (Z : Twistor4) :
    helicity (wittToDiagonal Z) = 4 * paperHelicity Z := by
  rw [helicity, diagonal_pairing]
  simp [paperHelicity]
  ring

/-- Real spacetime incidence gives an isotropic plane in the correct Witt frame. -/
theorem paperIncidence_witt_isotropic (X : ComplexSpacetime) (hX : Xᴴ = X)
    (pi rho : Spinor2) :
    wittPair (paperIncidence X pi) (paperIncidence X rho) = 0 := by
  have hs (a b : Fin 2) : star (X b a) = X a b := congrFun (congrFun hX a) b
  simp [paperIncidence_apply, wittPair, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hs]
  ring

open InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-- The scalar `1/sqrt(2)` in equation (2.1). -/
def paperScale : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma paperScale_sq : 2 * paperScale ^ 2 = 1 := by
  have h : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by exact_mod_cast h
  dsimp [paperScale]
  rw [inv_pow, hc]
  norm_num

/-- The paper's axis ordering, sign and normalization relative to the Pauli owner. -/
def paperSpacetime (t x y z : ℝ) : ComplexSpacetime :=
  paperScale • pauliMomentum ⟨t, y, -z, x⟩

theorem paperSpacetime_determinant (t x y z : ℝ) :
    2 * (paperSpacetime t x y z).det =
      ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  simp only [paperSpacetime, Matrix.det_smul, Fintype.card_fin,
    det_pauliMomentum, minkowskiSq]
  rw [← mul_assoc, paperScale_sq, one_mul]
  push_cast
  ring

end InfoGeometry.Twistor.PerjesConventions
