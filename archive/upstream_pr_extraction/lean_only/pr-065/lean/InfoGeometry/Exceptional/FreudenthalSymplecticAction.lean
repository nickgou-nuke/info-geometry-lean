import InfoGeometry.Exceptional.FreudenthalSymplecticMixedBracket

/-!
# Symplectic action on the Freudenthal mixed bracket

This is the proven grade-zero action law for the current symplectic mixed
bracket.  It is deliberately stated for the existing symplectic operator
carrier, not for an unconstructed exceptional `𝔢₇` carrier.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem symplectic_commutator_rankTwo
    (T : Module.End ℝ (FreudenthalCharge J))
    (hT : IsSymplecticOperator D T)
    (X Y : FreudenthalCharge J) :
    ⁅T, symplecticRankTwo D X Y⁆ =
      symplecticRankTwo D (T X) Y +
        symplecticRankTwo D X (T Y) := by
  apply LinearMap.ext
  intro Z
  change T (symplecticRankTwo D X Y Z) -
      symplecticRankTwo D X Y (T Z) = _
  simp only [Ring.lie_def, Module.End.mul_apply,
    symplecticRankTwo_apply, LinearMap.add_apply,
    map_add, map_smul,
    symplecticForm_add_left, symplecticForm_add_right,
    symplecticForm_smul_left, symplecticForm_smul_right]
  have hYZ := hT Y Z
  have hXZ := hT X Z
  have hYZ' :
      FreudenthalCharge.symplecticForm D Y (T Z) =
        -FreudenthalCharge.symplecticForm D (T Y) Z := by
    linarith
  have hXZ' :
      FreudenthalCharge.symplecticForm D X (T Z) =
        -FreudenthalCharge.symplecticForm D (T X) Z := by
    linarith
  rw [hYZ', hXZ']
  module

theorem symplectic_commutator_rankTwo_mem
    (T : Module.End ℝ (FreudenthalCharge J))
    (hT : IsSymplecticOperator D T)
    (X Y : FreudenthalCharge J) :
    ⁅T, symplecticRankTwo D X Y⁆ ∈
      symplecticOperatorLieSubalgebra D := by
  exact (symplecticOperatorLieSubalgebra D).lie_mem hT
    (symplecticRankTwo_isSymplectic D X Y)

theorem symplectic_rankTwo_commutator_rankTwo
    (X Y U V : FreudenthalCharge J) :
    ⁅symplecticRankTwo D X Y, symplecticRankTwo D U V⁆ =
      symplecticRankTwo D (symplecticRankTwo D X Y U) V +
        symplecticRankTwo D U (symplecticRankTwo D X Y V) := by
  exact symplectic_commutator_rankTwo D
    (symplecticRankTwo D X Y)
    (symplecticRankTwo_isSymplectic D X Y) U V

/-! The same commutator law exposed on the existing mixed-bracket subtype.
This remains a rank-two symplectic statement; it is not an identification
with an exceptional `𝔢₇` carrier. -/

theorem mixedSymplecticBracket_commutator
    (X Y U V : FreudenthalCharge J) :
    ⁅(mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)),
        (mixedSymplecticBracket D U V : Module.End ℝ (FreudenthalCharge J))⁆ =
      (mixedSymplecticBracket D (symplecticRankTwo D X Y U) V :
        Module.End ℝ (FreudenthalCharge J)) +
        (mixedSymplecticBracket D U (symplecticRankTwo D X Y V) :
          Module.End ℝ (FreudenthalCharge J)) := by
  exact symplectic_rankTwo_commutator_rankTwo D X Y U V

/-- The zero-grade symplectic action differentiates the mixed bracket. -/
theorem zeroGrade_action_mixedSymplecticBracket
    (T : symplecticOperatorLieSubalgebra D)
    (X Y : FreudenthalCharge J) :
    ⁅T, mixedSymplecticBracket D X Y⁆ =
      mixedSymplecticBracket D ((T : Module.End ℝ (FreudenthalCharge J)) X) Y +
        mixedSymplecticBracket D X
          ((T : Module.End ℝ (FreudenthalCharge J)) Y) := by
  apply Subtype.ext
  exact symplectic_commutator_rankTwo D T T.property X Y

/-- Jacobi for the currently realized mixed symplectic zero-grade
operators.  This is the genuine Lie-theoretic closure available on the
current carrier; it does not identify that carrier with `𝔢₇`. -/
theorem mixedSymplecticBracket_jacobi
    (X Y U V P Q : FreudenthalCharge J) :
    ⁅(mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)),
        ⁅(mixedSymplecticBracket D U V : Module.End ℝ (FreudenthalCharge J)),
          (mixedSymplecticBracket D P Q : Module.End ℝ (FreudenthalCharge J))⁆⁆ +
      ⁅(mixedSymplecticBracket D U V : Module.End ℝ (FreudenthalCharge J)),
        ⁅(mixedSymplecticBracket D P Q : Module.End ℝ (FreudenthalCharge J)),
          (mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J))⁆⁆ +
      ⁅(mixedSymplecticBracket D P Q : Module.End ℝ (FreudenthalCharge J)),
        ⁅(mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)),
          (mixedSymplecticBracket D U V : Module.End ℝ (FreudenthalCharge J))⁆⁆ = 0 := by
  simpa using (lie_jacobi
    (x := (mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)))
    (y := (mixedSymplecticBracket D U V : Module.End ℝ (FreudenthalCharge J)))
    (z := (mixedSymplecticBracket D P Q : Module.End ℝ (FreudenthalCharge J))))

end InfoGeometry.Exceptional.Freudenthal
