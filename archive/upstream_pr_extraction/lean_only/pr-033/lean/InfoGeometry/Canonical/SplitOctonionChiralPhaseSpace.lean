import Mathlib
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Canonical.SplitOctonionCircularChiralClosure

/-!
# Split-octonion chiral symplectic phase space

This owner formalizes the native six-dimensional Peirce polarization over the
real Zorn carrier.  It proves the alternating form, its nondegeneracy, the
upper/lower Zorn embeddings, and the Lagrangian sheet identities.  It does not
assert a twistor, Hilbert-space, or modular-flow identification.
-/

namespace InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

abbrev Vec := Fin 3 → ℝ
abbrev Carrier := ZornMatrix ℝ
abbrev Phase := Vec × Vec

@[simp] theorem vec_expand (q : Vec) :
    ![q 0, q 1, q 2] = q := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem vec_zero :
    (![0, 0, 0] : Vec) = 0 := by
  funext i
  fin_cases i <;> rfl

def chiralPairing (q p : Vec) : ℝ := Vec3.dot q p

@[simp] theorem chiralPairing_formula (q p : Vec) :
    chiralPairing q p = q 0 * p 0 + q 1 * p 1 + q 2 * p 2 := rfl

theorem chiralPairing_comm (q p : Vec) :
    chiralPairing q p = chiralPairing p q := by
  simp [chiralPairing, Vec3.dot]
  ring

def omega (X Y : Phase) : ℝ :=
  chiralPairing X.1 Y.2 - chiralPairing Y.1 X.2

@[simp] theorem omega_self (X : Phase) : omega X X = 0 := by
  simp [omega]

theorem omega_skew (X Y : Phase) : omega X Y = -omega Y X := by
  unfold omega
  rw [neg_sub]

theorem omega_add_left (X Y Z : Phase) :
    omega (X + Y) Z = omega X Z + omega Y Z := by
  rcases X with ⟨qx, px⟩
  rcases Y with ⟨qy, py⟩
  rcases Z with ⟨qz, pz⟩
  simp [omega, chiralPairing, Vec3.dot]
  ring

theorem omega_add_right (X Y Z : Phase) :
    omega X (Y + Z) = omega X Y + omega X Z := by
  rw [omega_skew X (Y + Z), omega_add_left Y Z X]
  rw [omega_skew Y X, omega_skew Z X]
  ring

theorem omega_smul_left (a : ℝ) (X Y : Phase) :
    omega (a • X) Y = a * omega X Y := by
  rcases X with ⟨qx, px⟩
  rcases Y with ⟨qy, py⟩
  simp [omega, chiralPairing, Vec3.dot]
  ring

theorem omega_smul_right (a : ℝ) (X Y : Phase) :
    omega X (a • Y) = a * omega X Y := by
  rw [omega_skew X (a • Y), omega_smul_left a Y X, omega_skew Y X]
  ring

def upperZorn (q : Vec) : Carrier where
  a := 0
  v := q
  w := 0
  b := 0

def lowerZorn (p : Vec) : Carrier where
  a := 0
  v := 0
  w := p
  b := 0

@[simp] theorem upperZorn_injective : Function.Injective upperZorn := by
  intro q r h
  exact congrArg ZornMatrix.v h

@[simp] theorem lowerZorn_injective : Function.Injective lowerZorn := by
  intro p r h
  exact congrArg ZornMatrix.w h

theorem upperZorn_basis (i : Fin 3) :
    upperZorn (Vec3.basis i) = (U i : Carrier) := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext j
    fin_cases j <;> rfl
  · rfl

theorem lowerZorn_basis (i : Fin 3) :
    lowerZorn (Vec3.basis i) = (V i : Carrier) := by
  apply ZornMatrix.ext
  · rfl
  · funext j
    fin_cases j <;> rfl
  · rfl
  · rfl

@[simp] theorem E11_mul_upperZorn (q : Vec) :
    (E11 : Carrier) * upperZorn q = upperZorn q := by
  apply ZornMatrix.ext
  · simp [upperZorn, E11, ZornMatrix.mul, Vec3.dot]
  · funext j
    fin_cases j <;> simp [upperZorn, E11, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · funext j
    fin_cases j <;> simp [upperZorn, E11, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · simp [upperZorn, E11, ZornMatrix.mul, Vec3.dot]

@[simp] theorem upperZorn_mul_E11 (q : Vec) :
    upperZorn q * (E11 : Carrier) = 0 := by
  apply ZornMatrix.ext
  · simp [upperZorn, E11, ZornMatrix.mul, Vec3.dot, ZornMatrix.zero]
  · funext j
    fin_cases j <;> simp [upperZorn, E11, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero]
  · funext j
    fin_cases j <;> simp [upperZorn, E11, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero]
  · simp [upperZorn, E11, ZornMatrix.mul, Vec3.dot, ZornMatrix.zero]

@[simp] theorem E22_mul_lowerZorn (p : Vec) :
    (E22 : Carrier) * lowerZorn p = lowerZorn p := by
  apply ZornMatrix.ext
  · simp [lowerZorn, E22, ZornMatrix.mul, Vec3.dot]
  · funext j
    fin_cases j <;> simp [lowerZorn, E22, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · funext j
    fin_cases j <;> simp [lowerZorn, E22, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross]
  · simp [lowerZorn, E22, ZornMatrix.mul, Vec3.dot]

@[simp] theorem lowerZorn_mul_E22 (p : Vec) :
    lowerZorn p * (E22 : Carrier) = 0 := by
  apply ZornMatrix.ext
  · simp [lowerZorn, E22, ZornMatrix.mul, Vec3.dot, ZornMatrix.zero]
  · funext j
    fin_cases j <;> simp [lowerZorn, E22, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero]
  · funext j
    fin_cases j <;> simp [lowerZorn, E22, ZornMatrix.mul,
        Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.zero]
  · simp [lowerZorn, E22, ZornMatrix.mul, Vec3.dot, ZornMatrix.zero]

theorem upperZorn_mul_lowerZorn (q p : Vec) :
    upperZorn q * lowerZorn p = chiralPairing q p • (E11 : Carrier) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, chiralPairing, E11, ZornMatrix.mul,
      Vec3.dot, Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.smul] <;>
    ring

theorem lowerZorn_mul_upperZorn (p q : Vec) :
    lowerZorn p * upperZorn q = chiralPairing q p • (E22 : Carrier) := by
  apply ZornMatrix.ext <;>
    simp [upperZorn, lowerZorn, chiralPairing, E22, ZornMatrix.mul,
      Vec3.dot, Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, ZornMatrix.smul] <;>
    ring

theorem omega_eq_zorn_mixed_readout (X Y : Phase) :
    omega X Y =
      (upperZorn X.1 * lowerZorn Y.2).a -
      (upperZorn Y.1 * lowerZorn X.2).a := by
  rw [upperZorn_mul_lowerZorn, upperZorn_mul_lowerZorn]
  simp [omega, chiralPairing, ZornMatrix.smul, E11]

def plusPhase (q : Vec) : Phase := (q, 0)
def minusPhase (p : Vec) : Phase := (0, p)

@[simp] theorem omega_plus_plus (q r : Vec) :
    omega (plusPhase q) (plusPhase r) = 0 := by
  simp [omega, plusPhase]

@[simp] theorem omega_minus_minus (p s : Vec) :
    omega (minusPhase p) (minusPhase s) = 0 := by
  simp [omega, minusPhase]

@[simp] theorem omega_plus_minus (q p : Vec) :
    omega (plusPhase q) (minusPhase p) = chiralPairing q p := by
  simp [omega, plusPhase, minusPhase]

@[simp] theorem omega_minus_plus (p q : Vec) :
    omega (minusPhase p) (plusPhase q) = -chiralPairing q p := by
  simp [omega, plusPhase, minusPhase]

theorem omega_nondegenerate_left
    (X : Phase) (hX : ∀ Y : Phase, omega X Y = 0) : X = 0 := by
  rcases X with ⟨q, p⟩
  apply Prod.ext
  · funext i
    fin_cases i
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX ((0 : Vec), Vec3.basis 0)
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX ((0 : Vec), Vec3.basis 1)
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX ((0 : Vec), Vec3.basis 2)
  · funext i
    fin_cases i
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX (Vec3.basis 0, (0 : Vec))
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX (Vec3.basis 1, (0 : Vec))
    · simpa [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
        Vec3.basis] using hX (Vec3.basis 2, (0 : Vec))

theorem omega_nondegenerate_right
    (Y : Phase) (hY : ∀ X : Phase, omega X Y = 0) : Y = 0 := by
  apply omega_nondegenerate_left Y
  intro X
  rw [omega_skew]
  simp [hY X]

theorem omega_nondegenerate :
    ∀ X : Phase, (∀ Y : Phase, omega X Y = 0) → X = 0 :=
  omega_nondegenerate_left

/-! ## Split polarization operator and metric -/

/-- The para-complex grading of the two chiral sheets. -/
def paraJ (X : Phase) : Phase := (X.1, -X.2)

@[simp] theorem paraJ_sq (X : Phase) : paraJ (paraJ X) = X := by
  rcases X with ⟨q, p⟩
  simp [paraJ]

theorem omega_paraJ_paraJ (X Y : Phase) :
    omega (paraJ X) (paraJ Y) = -omega X Y := by
  rcases X with ⟨q, p⟩
  rcases Y with ⟨r, s⟩
  simp [paraJ, omega, chiralPairing, Vec3.dot]
  ring

/-- The symmetric split metric induced by `omega` and `paraJ`. -/
def paraMetric (X Y : Phase) : ℝ := omega X (paraJ Y)

theorem paraMetric_symm (X Y : Phase) :
    paraMetric X Y = paraMetric Y X := by
  rcases X with ⟨q, p⟩
  rcases Y with ⟨r, s⟩
  simp [paraMetric, paraJ, omega, chiralPairing, Vec3.dot]
  ring

theorem paraMetric_nondegenerate_left
    (X : Phase) (hX : ∀ Y : Phase, paraMetric X Y = 0) :
    X = 0 := by
  apply omega_nondegenerate_left X
  intro Z
  have h := hX (paraJ Z)
  simpa [paraMetric, paraJ] using h

/-! ## Circular basis readback -/

theorem sigmaPlus_eq_upperZorn_basis (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaPlus i =
      upperZorn (Vec3.basis i) := by
  symm
  exact upperZorn_basis i

theorem sigmaMinus_eq_lowerZorn_basis (i : Fin 3) :
    InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaMinus i =
      lowerZorn (Vec3.basis i) := by
  symm
  exact lowerZorn_basis i

theorem omega_circular_basis (i j : Fin 3) :
    omega (plusPhase (Vec3.basis i)) (minusPhase (Vec3.basis j)) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
      Vec3.basis]

theorem circular_mixed_product_realizes_phase_pairing (i j : Fin 3) :
    (InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaPlus i *
        InfoGeometry.Canonical.SplitOctonionCircularChiralClosure.sigmaMinus j).a =
      omega (plusPhase (Vec3.basis i)) (minusPhase (Vec3.basis j)) := by
  rw [sigmaPlus_eq_upperZorn_basis, sigmaMinus_eq_lowerZorn_basis]
  rw [upperZorn_mul_lowerZorn]
  simp [omega, plusPhase, minusPhase, chiralPairing, Vec3.dot,
    Vec3.basis, ZornMatrix.smul, E11]

end
end InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
