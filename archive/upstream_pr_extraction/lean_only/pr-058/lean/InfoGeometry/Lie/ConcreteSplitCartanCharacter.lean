import InfoGeometry.Lie.ConcreteSplitCartan

/-!
# The rank-one split-Cartan character

The concrete split-Cartan parameter group is the additive logarithmic
coordinate used by the exponential flow.  This file packages the standard
parabolic character `t ↦ exp (ν t)` as a genuine homomorphism into `ℂˣ`.
It is independent of a choice of representation of the ambient group and
makes no parabolic-induction or irreducibility claim.
-/

noncomputable section

namespace InfoGeometry.Lie.ConcreteSplitCartan

/-- The complex character of the logarithmic split-Cartan parameter. -/
def splitCartanACharacter (ν : ℂ) : Multiplicative ℝ →* ℂˣ where
  toFun t := Units.mk0
    (Complex.exp (ν * ((Multiplicative.toAdd t : ℝ) : ℂ)))
    (Complex.exp_ne_zero _)
  map_one' := by
    ext
    simp
  map_mul' t u := by
    ext
    change Complex.exp (ν * (((Multiplicative.toAdd t : ℝ) +
      (Multiplicative.toAdd u : ℝ) : ℝ) : ℂ)) =
      Complex.exp (ν * ((Multiplicative.toAdd t : ℝ) : ℂ)) *
        Complex.exp (ν * ((Multiplicative.toAdd u : ℝ) : ℂ))
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem splitCartanACharacter_apply
    (ν : ℂ) (t : Multiplicative ℝ) :
    (splitCartanACharacter ν t : ℂ) =
      Complex.exp (ν * ((Multiplicative.toAdd t : ℝ) : ℂ)) := by
  rfl

theorem splitCartanACharacter_additive_readout
    (ν : ℂ) (t u : ℝ) :
    (splitCartanACharacter ν (Multiplicative.ofAdd (t + u)) : ℂ) =
      (splitCartanACharacter ν (Multiplicative.ofAdd t) : ℂ) *
        (splitCartanACharacter ν (Multiplicative.ofAdd u) : ℂ) := by
  exact congrArg Units.val
    ((splitCartanACharacter ν).map_mul
      (Multiplicative.ofAdd t) (Multiplicative.ofAdd u))

theorem splitCartanACharacter_ne_zero
    (ν : ℂ) (t : Multiplicative ℝ) :
    (splitCartanACharacter ν t : ℂ) ≠ 0 := by
  exact Complex.exp_ne_zero _

end InfoGeometry.Lie.ConcreteSplitCartan
