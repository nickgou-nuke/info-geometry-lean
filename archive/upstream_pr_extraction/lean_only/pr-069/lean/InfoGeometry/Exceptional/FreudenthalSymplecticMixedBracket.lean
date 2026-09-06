import InfoGeometry.Exceptional.FreudenthalChargeLinear

/-!
# The proven symplectic mixed bracket on Freudenthal charges

The current repository proves a canonical rank-two symplectic operator from
two Freudenthal charges.  This owner exposes that operation as a genuine
mixed bracket into the existing symplectic Lie subalgebra.  It deliberately
does not identify that subalgebra with `𝔢₇`.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev SymplecticZero := symplecticOperatorLieSubalgebra D

def mixedSymplecticBracket
    (X Y : FreudenthalCharge J) : SymplecticZero D :=
  ⟨symplecticRankTwo D X Y, symplecticRankTwo_isSymplectic D X Y⟩

@[simp] theorem mixedSymplecticBracket_val
    (X Y : FreudenthalCharge J) :
    (mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)) =
      symplecticRankTwo D X Y := rfl

theorem mixedSymplecticBracket_swap
    (X Y : FreudenthalCharge J) :
    mixedSymplecticBracket D X Y = mixedSymplecticBracket D Y X := by
  apply Subtype.ext
  exact symplecticRankTwo_swap D X Y

theorem mixedSymplecticBracket_isSymplectic
    (X Y : FreudenthalCharge J) :
    IsSymplecticOperator D
      (mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J)) :=
  (mixedSymplecticBracket D X Y).property

/-- The mixed rank-two bracket is closed under the existing zero-grade Lie
subalgebra.  This is the subtype-level closure needed by later graded
 constructions; it does not identify the carrier with `𝔢₇`. -/
theorem mixedSymplecticBracket_lie_mem
    (T : SymplecticZero D) (X Y : FreudenthalCharge J) :
    IsSymplecticOperator D
      ⁅(T : Module.End ℝ (FreudenthalCharge J)),
        (mixedSymplecticBracket D X Y : Module.End ℝ (FreudenthalCharge J))⁆ := by
  exact (symplecticOperatorLieSubalgebra D).lie_mem T.property
    (mixedSymplecticBracket D X Y).property

end InfoGeometry.Exceptional.Freudenthal
