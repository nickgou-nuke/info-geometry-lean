import InfoGeometry.Canonical.ThreeColorOperatorSuperBracketClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# Chiral Zorn quadratic and bivector channels

The primitive carrier is the non-associative operator-valued Zorn product.
This owner does not install a Lie algebra structure on that carrier.  It only
packages the two additive readouts of the already-proved products:

* the mixed anticommutator is the diagonal (quadratic) channel;
* the mixed commutator is the diagonal chirality/difference channel;
* same-chirality commutators are the cross/bivector channel.

For noncommutative coefficients the cross product is not assumed antisymmetric;
the displayed difference is therefore the strongest unconditional statement.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

def operatorNeg (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨-X.n_plus, -X.n_minus, fun i => -X.sigma_plus i, fun i => -X.sigma_minus i⟩

def operatorSubChannel (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorAdd X (operatorNeg Y)

def operatorAnticommutator (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorAdd (operatorZornMul X Y) (operatorZornMul Y X)

def operatorCommutator (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorSubChannel (operatorZornMul X Y) (operatorZornMul Y X)

def operatorSymmetricDot (U V : OperatorVector A) (half : A) : A :=
  half * (operatorDot U V + operatorDot V U)

def operatorAntisymmetricDot (U V : OperatorVector A) (half : A) : A :=
  half * (operatorDot U V - operatorDot V U)

theorem operatorSymmetricDot_add_antisymmetricDot
    (U V : OperatorVector A) (half : A) (h_half : half + half = 1) :
    operatorSymmetricDot U V half + operatorAntisymmetricDot U V half =
      operatorDot U V := by
  dsimp [operatorSymmetricDot, operatorAntisymmetricDot]
  calc
    half * (operatorDot U V + operatorDot V U) +
        half * (operatorDot U V - operatorDot V U) =
        half * operatorDot U V + half * operatorDot U V := by
          noncomm_ring
    _ = (half + half) * operatorDot U V := by
          rw [add_mul]
    _ = operatorDot U V := by rw [h_half, one_mul]

theorem operatorSymmetricDot_sub_antisymmetricDot
    (U V : OperatorVector A) (half : A) (h_half : half + half = 1) :
    operatorSymmetricDot U V half - operatorAntisymmetricDot U V half =
      operatorDot V U := by
  dsimp [operatorSymmetricDot, operatorAntisymmetricDot]
  calc
    half * (operatorDot U V + operatorDot V U) -
        half * (operatorDot U V - operatorDot V U) =
        half * operatorDot V U + half * operatorDot V U := by
          noncomm_ring
    _ = (half + half) * operatorDot V U := by
          rw [add_mul]
    _ = operatorDot V U := by rw [h_half, one_mul]

theorem mixed_chiral_anticommutator_channel
    (U V : OperatorVector A) :
    operatorAnticommutator (sigmaPlus U) (sigmaMinus V) =
      operatorAdd (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  rw [operatorAnticommutator, sigmaPlus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaPlus]

theorem mixed_chiral_commutator_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaPlus U) (sigmaMinus V) =
      operatorSubChannel (nPlus (operatorDot U V)) (nMinus (operatorDot V U)) := by
  rw [operatorCommutator, sigmaPlus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaPlus]

theorem mixed_chiral_anticommutator_sa_duality
    (U V : OperatorVector A) (half : A)
    (h_half : half + half = 1) :
    operatorAnticommutator (sigmaPlus U) (sigmaMinus V) =
      operatorAdd
        (nPlus (operatorSymmetricDot U V half +
          operatorAntisymmetricDot U V half))
        (nMinus (operatorSymmetricDot U V half -
          operatorAntisymmetricDot U V half)) := by
  rw [mixed_chiral_anticommutator_channel]
  apply operatorZornMatrix_ext
  · simp only [operatorAdd, nPlus, nMinus, operatorSymmetricDot,
      operatorAntisymmetricDot, add_zero, zero_add]
    calc
      operatorDot U V = (half + half) * operatorDot U V := by
        rw [h_half, one_mul]
      _ = half * operatorDot U V + half * operatorDot U V := by
        rw [add_mul]
      _ = half * (operatorDot U V + operatorDot V U) +
          half * (operatorDot U V - operatorDot V U) := by
        noncomm_ring
  · simp only [operatorAdd, nPlus, nMinus, operatorSymmetricDot,
      operatorAntisymmetricDot, add_zero, zero_add]
    calc
      operatorDot V U = (half + half) * operatorDot V U := by
        rw [h_half, one_mul]
      _ = half * operatorDot V U + half * operatorDot V U := by
        rw [add_mul]
      _ = half * (operatorDot U V + operatorDot V U) -
          half * (operatorDot U V - operatorDot V U) := by
        noncomm_ring
  · simp [operatorAdd, nPlus, nMinus, operatorSymmetricDot,
      operatorAntisymmetricDot]
  · simp [operatorAdd, nPlus, nMinus, operatorSymmetricDot,
      operatorAntisymmetricDot]

theorem mixed_chiral_commutator_sa_duality
    (U V : OperatorVector A) (half : A)
    (h_half : half + half = 1) :
    operatorCommutator (sigmaPlus U) (sigmaMinus V) =
      operatorSubChannel
        (nPlus (operatorSymmetricDot U V half +
          operatorAntisymmetricDot U V half))
        (nMinus (operatorSymmetricDot U V half -
          operatorAntisymmetricDot U V half)) := by
  rw [mixed_chiral_commutator_channel,
    operatorSymmetricDot_add_antisymmetricDot U V half h_half,
    operatorSymmetricDot_sub_antisymmetricDot U V half h_half]

theorem same_chiral_plus_commutator_cross_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorCross U V - operatorCross V U) := by
  rw [operatorCommutator, sigmaPlus_mul_sigmaPlus,
    sigmaPlus_mul_sigmaPlus]
  apply operatorZornMatrix_ext
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaMinus]
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaMinus]
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaMinus]
  · funext i
    simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaMinus, sub_eq_add_neg]

theorem same_chiral_plus_commutator_hodge_bivector_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (operatorHodgeDual2 (operatorBivectorChannel U V)) := by
  rw [same_chiral_plus_commutator_cross_channel,
    operatorHodgeDual2_bivectorChannel_eq_cross_difference]

theorem same_chiral_plus_commutator_leviCivita_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaPlus U) (sigmaPlus V) =
      sigmaMinus (leviCivitaOperatorCross U V -
        leviCivitaOperatorCross V U) := by
  rw [same_chiral_plus_commutator_cross_channel]
  congr 1
  funext i
  rw [leviCivitaOperatorCross_eq_operatorCross,
    leviCivitaOperatorCross_eq_operatorCross]

theorem same_chiral_minus_commutator_cross_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-(operatorCross U V - operatorCross V U)) := by
  rw [operatorCommutator, sigmaMinus_mul_sigmaMinus,
    sigmaMinus_mul_sigmaMinus]
  apply operatorZornMatrix_ext
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaPlus]
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaPlus]
  · funext i
    simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaPlus,
      sub_eq_add_neg, add_comm]
  · simp [operatorSubChannel, operatorAdd, operatorNeg, sigmaPlus]

theorem same_chiral_minus_commutator_hodge_bivector_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-(operatorHodgeDual2 (operatorBivectorChannel U V))) := by
  rw [same_chiral_minus_commutator_cross_channel,
    operatorHodgeDual2_bivectorChannel_eq_cross_difference]

theorem same_chiral_minus_commutator_leviCivita_channel
    (U V : OperatorVector A) :
    operatorCommutator (sigmaMinus U) (sigmaMinus V) =
      sigmaPlus (-(leviCivitaOperatorCross U V -
        leviCivitaOperatorCross V U)) := by
  rw [same_chiral_minus_commutator_cross_channel]
  congr 1
  funext i
  rw [leviCivitaOperatorCross_eq_operatorCross,
    leviCivitaOperatorCross_eq_operatorCross]

section CommutativeCoefficients

variable {C : Type*} [CommRing C]

/-- The Zorn dot pairing is symmetric when its coefficients commute. -/
theorem operatorDot_swap_eq_of_commutative
    (U V : OperatorVector C) :
    operatorDot V U = operatorDot U V := by
  simp [operatorDot, InfoGeometry.Physics.NCG.NCZornElement.zornDot]
  ring

/-- The diagonal difference channel is the common dot pairing multiplied by
the two-sheet chirality sign. -/
theorem mixed_chiral_commutator_is_chirality_channel_commutative
    (U V : OperatorVector C) :
    operatorCommutator (sigmaPlus U) (sigmaMinus V) =
      operatorSubChannel (nPlus (operatorDot U V))
        (nMinus (operatorDot U V)) := by
  rw [mixed_chiral_commutator_channel,
    operatorDot_swap_eq_of_commutative]

/-- With commuting coefficients, the cross channel is genuinely
antisymmetric, so the ordinary same-sheet commutator is the doubled
cross/bivector output. -/
theorem operatorCross_swap_eq_neg_of_commutative
    (U V : OperatorVector C) :
    operatorCross V U = -(operatorCross U V) := by
  funext i
  fin_cases i <;>
    simp [operatorCross, InfoGeometry.Physics.NCG.NCZornElement.zornCross,
      sub_eq_add_neg] <;> ring

theorem same_chiral_plus_commutator_cross_channel_commutative
    (U V : OperatorVector C) :
    operatorCommutator (sigmaPlus U) (sigmaPlus V) =
      operatorAdd (sigmaMinus (operatorCross U V))
        (sigmaMinus (operatorCross U V)) := by
  rw [same_chiral_plus_commutator_cross_channel,
    operatorCross_swap_eq_neg_of_commutative]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaMinus, sub_eq_add_neg]
  · simp [operatorAdd, sigmaMinus, sub_eq_add_neg]
  · simp [operatorAdd, sigmaMinus, sub_eq_add_neg]
  · funext i
    simp [operatorAdd, sigmaMinus, sub_eq_add_neg]

theorem same_chiral_minus_commutator_cross_channel_commutative
    (U V : OperatorVector C) :
    operatorCommutator (sigmaMinus U) (sigmaMinus V) =
      operatorAdd (sigmaPlus (-(operatorCross U V)))
        (sigmaPlus (-(operatorCross U V))) := by
  rw [same_chiral_minus_commutator_cross_channel,
    operatorCross_swap_eq_neg_of_commutative]
  apply operatorZornMatrix_ext
  · simp [operatorAdd, sigmaPlus, sub_eq_add_neg]
  · simp [operatorAdd, sigmaPlus, sub_eq_add_neg]
  · funext i
    simp [operatorAdd, sigmaPlus, sub_eq_add_neg]
  · simp [operatorAdd, sigmaPlus, sub_eq_add_neg]

end CommutativeCoefficients

end InfoGeometry.Canonical
