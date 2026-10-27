import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.PenroseTwistor
import Mathlib

/-!
# Perjes' incidence and Hermitian conventions

The source is KFKI-1980-76, equations (3.7), (5.5) and (6.6).
The existing owner uses +i X pi, whereas Perjes uses -i X pi.
The incidence pairing is off-diagonal; the existing Penrose pairing is diagonal.
These are connected by actual linear equivalences, with their normalization kept.
-/
noncomputable section
namespace InfoGeometry.Twistor.PerjesConventions
open PenroseIncidence PenroseTwistor
open scoped BigOperators

/-- Pair coordinates and the already-owned complex four-space. -/
def coordinateEquiv : Twistor4 ≃ₗ[ℂ] TwistorCarrier where
  toFun Z := ![Z.1 0, Z.1 1, Z.2 0, Z.2 1]
  invFun z := (![z 0, z 1], ![z 2, z 3])
  left_inv Z := by ext i <;> fin_cases i <;> rfl
  right_inv z := by funext i; fin_cases i <;> rfl
  map_add' Z W := by funext i; fin_cases i <;> rfl
  map_smul' c Z := by funext i; fin_cases i <;> rfl

/-- Change the upper spinor's sign, without altering the established incidence owner. -/
def incidenceSign : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (-Z.1, Z.2)
  invFun Z := (-Z.1, Z.2)
  left_inv Z := by simp
  right_inv Z := by simp
  map_add' Z W := by simp
  map_smul' c Z := by simp

def incidence (X : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 :=
  incidenceSign.toLinearMap.comp (incidenceLinearMap X)

@[simp] theorem incidence_apply (X : ComplexSpacetime) (π : Spinor2) :
    incidence X π = ((-Complex.I) • X.mulVec π, π) := by
  simp [incidence, incidenceSign, incidenceLinearMap_apply, omegaLinearMap_apply]

theorem incidence_injective (X : ComplexSpacetime) : Function.Injective (incidence X) :=
  incidenceSign.injective.comp (incidenceLinearMap_injective X)

/-- Off-diagonal Hermitian form in the incidence frame. -/
def pairing (Z W : Twistor4) : ℂ :=
  star (Z.1 0) * W.2 0 + star (Z.1 1) * W.2 1 +
  star (Z.2 0) * W.1 0 + star (Z.2 1) * W.1 1

theorem pairing_swap (Z W : Twistor4) : pairing W Z = star (pairing Z W) := by
  simp [pairing, star_add, star_mul]
  ring

theorem pairing_smul (c : ℂ) (Z W : Twistor4) :
    pairing (c • Z) (c • W) = (c * star c) * pairing Z W := by
  simp [pairing, smul_eq_mul, star_mul]
  ring

/-- An unnormalized diagonal frame: its Hermitian form is twice the incidence form. -/
def diagonalFrame : Twistor4 ≃ₗ[ℂ] TwistorCarrier where
  toFun Z := ![Z.1 0 + Z.2 0, Z.1 1 + Z.2 1,
    Z.1 0 - Z.2 0, Z.1 1 - Z.2 1]
  invFun z := (![(z 0 + z 2)/2, (z 1 + z 3)/2],
    ![(z 0 - z 2)/2, (z 1 - z 3)/2])
  left_inv Z := by ext i <;> fin_cases i <;> simp <;> ring
  right_inv z := by funext i; fin_cases i <;> simp <;> ring
  map_add' Z W := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c Z := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem diagonalFrame_pairing (Z W : Twistor4) :
    twistorHermitian (diagonalFrame Z) (diagonalFrame W) = 2 * pairing Z W := by
  simp [twistorHermitian_apply, diagonalFrame, pairing, Fin.sum_univ_four,
    star_add, star_sub, star_mul]
  ring

/-- Perjes' s, not the owner's differently normalized diagonal readout. -/
def physicalHelicity (Z : Twistor4) : ℝ := (pairing Z Z).re / 2

theorem helicity_adapter (Z : Twistor4) :
    PenroseTwistor.helicity (diagonalFrame Z) = 4 * physicalHelicity Z := by
  unfold PenroseTwistor.helicity
  rw [diagonalFrame_pairing]
  simp [physicalHelicity, Complex.mul_re]
  ring

theorem helicity_phase_invariant (c : ℂ) (hc : c * star c = 1) (Z : Twistor4) :
    physicalHelicity (c • Z) = physicalHelicity Z := by
  simp only [physicalHelicity, pairing_smul, hc, one_mul]

/-- The factor i and the ordered Hermitian difference are both explicit. -/
theorem incidence_pairing (X Y : ComplexSpacetime) (π ρ : Spinor2) :
    pairing (incidence X π) (incidence Y ρ) =
      Complex.I * (∑ i, star (π i) * ((X.conjTranspose - Y).mulVec ρ) i) := by
  simp [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, smul_eq_mul, star_add, star_mul]
  ring

theorem hermitian_incidence_isotropic (X : ComplexSpacetime)
    (hX : X.conjTranspose = X) (π ρ : Spinor2) :
    pairing (incidence X π) (incidence X ρ) = 0 := by
  rw [incidence_pairing, hX, sub_self]
  simp

end InfoGeometry.Twistor.PerjesConventions
