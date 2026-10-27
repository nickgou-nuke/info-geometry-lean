import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-!
# Explicit convention adapters for Perjes (1980)

The paper uses `omega = -i X pi`; the existing incidence owner uses `+i`.
The unnormalised Witt-to-diagonal change of basis below multiplies the
Hermitian form by two. It is not an isometry with the factor suppressed.
No topology, particle interpretation or field equation is assumed here.
-/

noncomputable section
namespace InfoGeometry.Twistor.PerjesConventions

open Matrix
open scoped BigOperators
open PenroseIncidence PenroseTwistor

/-- Change only the sign of the upper spinor block. -/
def incidenceSignChange : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (-Z.1, Z.2)
  invFun Z := (-Z.1, Z.2)
  left_inv Z := by simp
  right_inv Z := by simp
  map_add' Z W := by simp [add_comm]
  map_smul' c Z := by simp

/-- Equation (3.7), with the paper's minus sign. -/
def perjesIncidence (X : ComplexSpacetime) (π : Spinor2) : Twistor4 :=
  (-Complex.I • omegaLinearMap X π, π)

theorem signChange_incidence (X : ComplexSpacetime) (π : Spinor2) :
    incidenceSignChange (incidenceLinearMap X π) = perjesIncidence X π := by
  simp [incidenceSignChange, incidenceLinearMap, perjesIncidence]

/-- The Hermitian form in the incidence (off-diagonal) spin frame. -/
def incidenceHermitian (Z W : Twistor4) : ℂ :=
  ∑ i : Fin 2, (star (Z.1 i) * W.2 i + star (Z.2 i) * W.1 i)

theorem incidenceHermitian_conj (Z W : Twistor4) :
    star (incidenceHermitian Z W) = incidenceHermitian W Z := by
  simp [incidenceHermitian, Fin.sum_univ_two]
  ring

/-- An explicit carrier equivalence, not an implicit identification of bases. -/
def incidenceToDiagonal : Twistor4 ≃ₗ[ℂ] TwistorCarrier where
  toFun Z := ![Z.1 0 + Z.2 0, Z.1 1 + Z.2 1,
    Z.1 0 - Z.2 0, Z.1 1 - Z.2 1]
  invFun z := (fun i => if i = 0 then (z 0 + z 2) / 2 else (z 1 + z 3) / 2,
    fun i => if i = 0 then (z 0 - z 2) / 2 else (z 1 - z 3) / 2)
  left_inv Z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  right_inv z := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' Z W := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c Z := by
    funext i
    fin_cases i <;> simp [mul_add, mul_sub]

/-- The exact factor relating the existing diagonal form and the incidence form. -/
theorem diagonalHermitian_eq_twice (Z W : Twistor4) :
    twistorHermitian (incidenceToDiagonal Z) (incidenceToDiagonal W) =
      2 * incidenceHermitian Z W := by
  simp [twistorHermitian_apply, incidenceToDiagonal, incidenceHermitian,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring

/-- Perjes equation (6.6) uses half the incidence-frame self-pairing. -/
def physicalHelicity (Z : Twistor4) : ℝ :=
  (incidenceHermitian Z Z).re / 2

theorem existing_helicity_adapter (Z : Twistor4) :
    helicity (incidenceToDiagonal Z) = 4 * physicalHelicity Z := by
  rw [helicity, diagonalHermitian_eq_twice]
  simp [physicalHelicity]
  ring

theorem incidenceHermitian_smul (c : ℂ) (Z W : Twistor4) :
    incidenceHermitian (c • Z) (c • W) =
      (star c * c) * incidenceHermitian Z W := by
  simp [incidenceHermitian, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem physicalHelicity_phase (c : ℂ) (hc : star c * c = 1) (Z : Twistor4) :
    physicalHelicity (c • Z) = physicalHelicity Z := by
  unfold physicalHelicity
  rw [incidenceHermitian_smul, hc, one_mul]

/-- Incidence isotropy measures the skew-Hermitian part of the actual matrix. -/
theorem incidenceHermitian_incidence (X : ComplexSpacetime) (π ρ : Spinor2) :
    incidenceHermitian (incidenceLinearMap X π) (incidenceLinearMap X ρ) =
      Complex.I * (∑ i : Fin 2, star (π i) * ((X - Xᴴ).mulVec ρ) i) := by
  simp [incidenceHermitian, incidenceLinearMap, omegaLinearMap,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem hermitian_incidence_isotropic (X : ComplexSpacetime) (hX : Xᴴ = X)
    (π ρ : Spinor2) :
    incidenceHermitian (incidenceLinearMap X π) (incidenceLinearMap X ρ) = 0 := by
  rw [incidenceHermitian_incidence, hX]
  simp

open InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-- Equation (2.1): its spatial ordering and its `1/sqrt(2)` are explicit. -/
def perjesSolder (t x y z : ℝ) : ComplexSpacetime :=
  ((Real.sqrt 2 : ℂ)⁻¹) • pauliMomentum ⟨t, y, -z, x⟩

theorem perjesSolder_determinant (t x y z : ℝ) :
    2 * (perjesSolder t x y z).det =
      ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [perjesSolder, Matrix.det_smul, Fintype.card_fin, inv_pow,
    hs, det_pauliMomentum, minkowskiSq]
  push_cast
  ring

end InfoGeometry.Twistor.PerjesConventions
