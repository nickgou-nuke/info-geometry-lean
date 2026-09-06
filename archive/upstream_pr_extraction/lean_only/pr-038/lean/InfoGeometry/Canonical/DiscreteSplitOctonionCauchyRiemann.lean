import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism
import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication

namespace InfoGeometry.Canonical

/-!
# Unit-lattice split-octonionic difference operators

This is the finite-algebraic entry point suggested by the discrete
octonionic-analysis paper.  The lattice is indexed by the already named
eight basis directions.  We formalize forward/backward differences and the
corresponding left split-octonionic Cauchy--Riemann readouts.  No fundamental
solution, boundary formula, or analytic completion is asserted here.
-/

abbrev SplitOctonionLattice := IntegralSplitBasis → ℤ

abbrev SplitOctonionField :=
  SplitOctonionLattice → StandardRationalSplitOctonion

def latticeShiftPlus (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    SplitOctonionLattice :=
  fun i => if i = j then m i + 1 else m i

def latticeShiftMinus (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    SplitOctonionLattice :=
  fun i => if i = j then m i - 1 else m i

def forwardDifference (f : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    StandardRationalSplitOctonion :=
  f (latticeShiftPlus j m) - f m

def backwardDifference (f : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    StandardRationalSplitOctonion :=
  f m - f (latticeShiftMinus j m)

theorem forwardDifference_add (f g : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    forwardDifference (f + g) j m =
      forwardDifference f j m + forwardDifference g j m := by
  dsimp [forwardDifference]
  abel

theorem backwardDifference_add (f g : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    backwardDifference (f + g) j m =
      backwardDifference f j m + backwardDifference g j m := by
  dsimp [backwardDifference]
  abel

theorem forwardDifference_smul (a : ℚ) (f : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    forwardDifference (a • f) j m =
      a • forwardDifference f j m := by
  dsimp [forwardDifference]
  simp only [smul_sub]

theorem backwardDifference_smul (a : ℚ) (f : SplitOctonionField)
    (j : IntegralSplitBasis) (m : SplitOctonionLattice) :
    backwardDifference (a • f) j m =
      a • backwardDifference f j m := by
  dsimp [backwardDifference]
  simp only [smul_sub]

theorem splitOctonionMulQ_zero_right (x : StandardRationalSplitOctonion) :
    splitOctonionMulQ x 0 = 0 := by
  unfold splitOctonionMulQ
  dsimp [splitQuaternionMulQ, splitQuaternionAddQ, splitQuaternionConjQ,
    splitOctonionOfQuaternionPairQ, splitQuaternionOfQ, splitQuaternionLPartQ]
  funext b
  fin_cases b <;> simp [splitOctonionOfQuaternionPairQ]

theorem splitOctonionMulQ_zero_left (x : StandardRationalSplitOctonion) :
    splitOctonionMulQ 0 x = 0 := by
  unfold splitOctonionMulQ
  dsimp [splitQuaternionMulQ, splitQuaternionAddQ, splitQuaternionConjQ,
    splitOctonionOfQuaternionPairQ, splitQuaternionOfQ, splitQuaternionLPartQ]
  funext b
  fin_cases b <;> simp [splitOctonionOfQuaternionPairQ]

def discreteSplitCauchyRiemannPlus (f : SplitOctonionField)
    (m : SplitOctonionLattice) : StandardRationalSplitOctonion :=
  ∑ j : IntegralSplitBasis,
    splitOctonionMulQ (rationalBasis j) (forwardDifference f j m)

def discreteSplitCauchyRiemannMinus (f : SplitOctonionField)
    (m : SplitOctonionLattice) : StandardRationalSplitOctonion :=
  ∑ j : IntegralSplitBasis,
    splitOctonionMulQ (rationalBasis j) (backwardDifference f j m)

theorem discreteSplitCauchyRiemannPlus_zero :
    discreteSplitCauchyRiemannPlus
        (0 : SplitOctonionField) = 0 := by
  funext m
  classical
  simp [discreteSplitCauchyRiemannPlus, forwardDifference,
    splitOctonionMulQ_zero_right]

theorem discreteSplitCauchyRiemannMinus_zero :
    discreteSplitCauchyRiemannMinus
        (0 : SplitOctonionField) = 0 := by
  funext m
  classical
  simp [discreteSplitCauchyRiemannMinus, backwardDifference,
    splitOctonionMulQ_zero_right]

/-- Constant fields have zero forward difference in every lattice direction. -/
theorem forwardDifference_const
    (c : StandardRationalSplitOctonion) (j : IntegralSplitBasis)
    (m : SplitOctonionLattice) :
    forwardDifference (fun _ : SplitOctonionLattice => c) j m = 0 := by
  simp [forwardDifference]

/-- Constant fields have zero backward difference in every lattice direction. -/
theorem backwardDifference_const
    (c : StandardRationalSplitOctonion) (j : IntegralSplitBasis)
    (m : SplitOctonionLattice) :
    backwardDifference (fun _ : SplitOctonionLattice => c) j m = 0 := by
  simp [backwardDifference]

/-- Constant fields have vanishing plus CR readout. -/
theorem discreteSplitCauchyRiemannPlus_const
    (c : StandardRationalSplitOctonion) (m : SplitOctonionLattice) :
    discreteSplitCauchyRiemannPlus (fun _ : SplitOctonionLattice => c) m = 0 := by
  have hzero : ∀ j : IntegralSplitBasis,
      splitOctonionMulQ (rationalBasis j) (0 : StandardRationalSplitOctonion) = 0 := by
    intro j
    exact splitOctonionMulQ_zero_right _
  simp [discreteSplitCauchyRiemannPlus, forwardDifference, hzero]

/-- Constant fields have vanishing minus CR readout. -/
theorem discreteSplitCauchyRiemannMinus_const
    (c : StandardRationalSplitOctonion) (m : SplitOctonionLattice) :
    discreteSplitCauchyRiemannMinus (fun _ : SplitOctonionLattice => c) m = 0 := by
  have hzero : ∀ j : IntegralSplitBasis,
      splitOctonionMulQ (rationalBasis j) (0 : StandardRationalSplitOctonion) = 0 := by
    intro j
    exact splitOctonionMulQ_zero_right _
  simp [discreteSplitCauchyRiemannMinus, backwardDifference, hzero]

/-- A split-octonionic field is discrete-monogenic when both CR readouts vanish. -/
def discreteSplitMonogenic (f : SplitOctonionField) : Prop :=
  ∀ m, discreteSplitCauchyRiemannPlus f m = 0 ∧
    discreteSplitCauchyRiemannMinus f m = 0

/-- Constant fields are discrete monogenic for both split CR readouts. -/
theorem discreteSplitMonogenic_const
    (c : StandardRationalSplitOctonion) :
    discreteSplitMonogenic (fun _ : SplitOctonionLattice => c) := by
  intro m
  constructor
  · exact discreteSplitCauchyRiemannPlus_const c m
  · exact discreteSplitCauchyRiemannMinus_const c m

end InfoGeometry.Canonical
