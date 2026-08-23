import InfoGeometry.OperatorAlgebra.SplitOctonionPeirceSymplectic

/-!
# The linear symplectic Lie algebra of the Peirce phase carrier

This owner records the honest intermediate target for a future derivation
representation theorem.  It does not identify split-octonion derivations with
phase endomorphisms; it only proves the native Lie closure of the endomorphisms
which infinitesimally preserve the real Peirce pairing.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceSymplectic

abbrev PhaseEnd := RealCarrier →ₗ[ℝ] RealCarrier

def PreservesRealPairing (T : PhaseEnd) : Prop :=
  ∀ X Y : RealCarrier,
    realPairing (T X) Y + realPairing X (T Y) = 0

theorem realPairing_add_left (X Y Z : RealCarrier) :
    realPairing (X + Y) Z = realPairing X Z + realPairing Y Z := by
  change (∑ i, ((X.1 i + Y.1 i) * Z.2 i - Z.1 i * (X.2 i + Y.2 i))) =
    (∑ i, (X.1 i * Z.2 i - Z.1 i * X.2 i)) +
      ∑ i, (Y.1 i * Z.2 i - Z.1 i * Y.2 i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realPairing_add_right (X Y Z : RealCarrier) :
    realPairing X (Y + Z) = realPairing X Y + realPairing X Z := by
  change (∑ i, (X.1 i * (Y.2 i + Z.2 i) - (Y.1 i + Z.1 i) * X.2 i)) =
    (∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i)) +
      ∑ i, (X.1 i * Z.2 i - Z.1 i * X.2 i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realPairing_neg_left (X Y : RealCarrier) :
    realPairing (-X) Y = -realPairing X Y := by
  change (∑ i, ((-X.1 i) * Y.2 i - Y.1 i * (-X.2 i))) =
    -(∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realPairing_neg_right (X Y : RealCarrier) :
    realPairing X (-Y) = -realPairing X Y := by
  change (∑ i, (X.1 i * (-Y.2 i) - (-Y.1 i) * X.2 i)) =
    -(∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realPairing_smul_left (a : ℝ) (X Y : RealCarrier) :
    realPairing (a • X) Y = a * realPairing X Y := by
  change (∑ i, ((a * X.1 i) * Y.2 i - Y.1 i * (a * X.2 i))) =
    a * (∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realPairing_smul_right (a : ℝ) (X Y : RealCarrier) :
    realPairing X (a • Y) = a * realPairing X Y := by
  change (∑ i, (X.1 i * (a * Y.2 i) - (a * Y.1 i) * X.2 i)) =
    a * (∑ i, (X.1 i * Y.2 i - Y.1 i * X.2 i))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem preservesRealPairing_zero :
    PreservesRealPairing 0 := by
  intro X Y
  change realPairing 0 Y + realPairing X 0 = 0
  simp [realPairing]

theorem preservesRealPairing_add
    {S T : PhaseEnd}
    (hS : PreservesRealPairing S)
    (hT : PreservesRealPairing T) :
    PreservesRealPairing (S + T) := by
  intro X Y
  rw [LinearMap.add_apply, realPairing_add_left]
  rw [LinearMap.add_apply, realPairing_add_right]
  linarith [hS X Y, hT X Y]

theorem preservesRealPairing_neg
    {T : PhaseEnd}
    (hT : PreservesRealPairing T) :
    PreservesRealPairing (-T) := by
  intro X Y
  rw [LinearMap.neg_apply, realPairing_neg_left]
  rw [LinearMap.neg_apply, realPairing_neg_right]
  rw [← add_neg (realPairing (T X) Y) (realPairing X (T Y))]
  rw [hT X Y, neg_zero]

theorem preservesRealPairing_smul
    (a : ℝ) {T : PhaseEnd}
    (hT : PreservesRealPairing T) :
    PreservesRealPairing (a • T) := by
  intro X Y
  rw [LinearMap.smul_apply, realPairing_smul_left]
  rw [LinearMap.smul_apply, realPairing_smul_right]
  rw [← mul_add, hT X Y, mul_zero]

def commutator (S T : PhaseEnd) : PhaseEnd :=
  S.comp T - T.comp S

@[simp] theorem commutator_apply (S T : PhaseEnd) (X : RealCarrier) :
    commutator S T X = S (T X) - T (S X) := by
  rfl

theorem preservesRealPairing_commutator
    {S T : PhaseEnd}
    (hS : PreservesRealPairing S)
    (hT : PreservesRealPairing T) :
    PreservesRealPairing (commutator S T) := by
  intro X Y
  simp only [commutator_apply]
  rw [sub_eq_add_neg, realPairing_add_left, realPairing_neg_left]
  rw [sub_eq_add_neg, realPairing_add_right, realPairing_neg_right]
  have hST := hS (T X) Y
  have hTS := hT (S X) Y
  have hSY := hS X (T Y)
  have hTY := hT X (S Y)
  linarith

end InfoGeometry.OperatorAlgebra.SplitOctonions.PeirceSymplectic
