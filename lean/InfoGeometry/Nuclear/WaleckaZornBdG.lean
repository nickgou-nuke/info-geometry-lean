import InfoGeometry.Nuclear.SplitOctonionNambuGorkovBridge
import InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge
import InfoGeometry.Algebra.ZornLeftCAR

namespace InfoGeometry.Nuclear.WaleckaZornBdG

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Nuclear.NambuGorkov
open InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

noncomputable section

def effectiveMass (bareMass scalarCoupling scalarField : ℝ) : ℝ :=
  bareMass - scalarCoupling * scalarField

def meanFieldState (bareMass scalarCoupling scalarField : ℝ) (pairing : Vec3 ℝ) :
    NambuGorkovCarrier ℝ :=
  ⟨effectiveMass bareMass scalarCoupling scalarField, pairing⟩

theorem effectiveMass_lt (bareMass scalarCoupling scalarField : ℝ)
    (coupling_pos : 0 < scalarCoupling) (field_pos : 0 < scalarField) :
    effectiveMass bareMass scalarCoupling scalarField < bareMass := by
  unfold effectiveMass
  linarith [mul_pos coupling_pos field_pos]

theorem effectiveMass_pos_iff (bareMass scalarCoupling scalarField : ℝ) :
    0 < effectiveMass bareMass scalarCoupling scalarField ↔
      scalarCoupling * scalarField < bareMass := sub_pos

def nativeHamiltonian (state : NambuGorkovCarrier ℝ) : ZornVectorMatrix ℝ :=
  oldToVector (toZorn state)

def regularHamiltonian (state : NambuGorkovCarrier ℝ) :
    Module.End ℝ (ZornVectorMatrix ℝ) :=
  leftMultiplication (nativeHamiltonian state)

theorem nativeHamiltonian_square (state : NambuGorkovCarrier ℝ) :
    ZornVectorMatrix.mul (nativeHamiltonian state) (nativeHamiltonian state) =
      (bogoliubovEnergy state) ^ 2 • ZornVectorMatrix.one := by
  have dispersion : (bogoliubovEnergy state) ^ 2 =
      state.xi ^ 2 + Vec3.dot state.delta state.delta := by
    rw [bogoliubovEnergy_sq, nambu_gorkov_zornNorm, neg_neg]
  have trace_zero : ZornVectorMatrix.trace (nativeHamiltonian state) = 0 := by
    simp [nativeHamiltonian, oldToVector, toZorn, ZornVectorMatrix.trace]
  have scalar_norm : ZornVectorMatrix.scalar
      (ZornVectorMatrix.norm (nativeHamiltonian state)) =
        -((bogoliubovEnergy state) ^ 2 • ZornVectorMatrix.one) := by
    rw [dispersion]
    ext coordinate <;>
      simp [nativeHamiltonian, oldToVector, toZorn, ZornVectorMatrix.norm,
        ZornVectorMatrix.scalar, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.one, ZornVec3.dot, Vec3.dot, Fin.sum_univ_three] <;> ring
  have characteristic := ZornVectorMatrix.characteristic_equation (nativeHamiltonian state)
  change ZornVectorMatrix.mul (nativeHamiltonian state) (nativeHamiltonian state) -
      ZornVectorMatrix.trace (nativeHamiltonian state) • nativeHamiltonian state +
        ZornVectorMatrix.scalar (ZornVectorMatrix.norm (nativeHamiltonian state)) = 0
    at characteristic
  rw [trace_zero, zero_smul, sub_zero, scalar_norm] at characteristic
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using characteristic)

theorem regularHamiltonian_square (state : NambuGorkovCarrier ℝ) :
    regularHamiltonian state * regularHamiltonian state =
      (bogoliubovEnergy state) ^ 2 •
        (1 : Module.End ℝ (ZornVectorMatrix ℝ)) := by
  unfold regularHamiltonian
  rw [leftMultiplication_square, nativeHamiltonian_square, map_smul,
    leftMultiplication_one]

theorem meanField_massless_square
    (bareMass scalarCoupling scalarField : ℝ) (pairing : Vec3 ℝ)
    (massless : bareMass = scalarCoupling * scalarField) :
    regularHamiltonian (meanFieldState bareMass scalarCoupling scalarField pairing) *
        regularHamiltonian (meanFieldState bareMass scalarCoupling scalarField pairing) =
      Vec3.dot pairing pairing • (1 : Module.End ℝ (ZornVectorMatrix ℝ)) := by
  rw [regularHamiltonian_square, bogoliubovEnergy_sq, nambu_gorkov_zornNorm]
  simp [meanFieldState, effectiveMass, massless]

def pairingMassRatio (state : NambuGorkovCarrier ℝ) : ℝ :=
  Vec3.dot state.delta state.delta / state.xi ^ 2

theorem meanField_pairingMassRatio_increases
    (bareMass scalarCoupling scalarField : ℝ) (pairing : Vec3 ℝ)
    (coupling_pos : 0 < scalarCoupling) (field_pos : 0 < scalarField)
    (effective_pos : 0 < effectiveMass bareMass scalarCoupling scalarField)
    (pairing_pos : 0 < Vec3.dot pairing pairing) :
    pairingMassRatio ⟨bareMass, pairing⟩ <
      pairingMassRatio (meanFieldState bareMass scalarCoupling scalarField pairing) := by
  have mass_lt := effectiveMass_lt bareMass scalarCoupling scalarField coupling_pos field_pos
  have bare_pos : 0 < bareMass := lt_trans effective_pos mass_lt
  have squares_lt : (effectiveMass bareMass scalarCoupling scalarField) ^ 2 < bareMass ^ 2 := by
    nlinarith
  unfold pairingMassRatio meanFieldState
  dsimp only
  apply (div_lt_div_iff₀ (sq_pos_of_pos bare_pos) (sq_pos_of_pos effective_pos)).mpr
  exact mul_lt_mul_of_pos_left squares_lt pairing_pos

end

end InfoGeometry.Nuclear.WaleckaZornBdG
