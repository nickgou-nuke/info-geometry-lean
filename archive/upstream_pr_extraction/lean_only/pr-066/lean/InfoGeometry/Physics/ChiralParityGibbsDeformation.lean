import InfoGeometry.Physics.SupergradedCuntzBdG

namespace InfoGeometry.Physics

open SupergradedCuntzBdG

noncomputable section

/-!
# Scalar chiral-parity Gibbs deformation

This owner records the scalar part of the proposed identification.  The
quantity `chi` is an abstract parity coordinate and the Gibbs/q weight is
`exp (β * μ * chi)`.  It is not silently identified with the native
split-octonion element `nPlus - nMinus`; exponentiating that nonassociative
carrier requires a separate construction.
-/

/-- The scalar Gibbs weight attached to a parity coordinate. -/
def chiralParityGibbsWeight (β μ chi : ℝ) : ℂ :=
  qRapidity (β * μ * chi)

@[simp] theorem chiralParityGibbsWeight_ne_zero
    (β μ chi : ℝ) :
    chiralParityGibbsWeight β μ chi ≠ 0 := by
  exact qRapidity_ne_zero _

/-- Chemical-potential shifts add at the rapidity level. -/
theorem chiralParityRapidity_mu_shift
    (β μ chi δμ : ℝ) :
    β * (μ + δμ) * chi = β * μ * chi + β * δμ * chi := by
  ring

/-- The Gibbs weight is multiplicative under a chemical-potential shift. -/
theorem chiralParityGibbsWeight_mu_shift
    (β μ chi δμ : ℝ) :
    chiralParityGibbsWeight β (μ + δμ) chi =
      chiralParityGibbsWeight β μ chi *
        chiralParityGibbsWeight β δμ chi := by
  rw [chiralParityGibbsWeight, chiralParityGibbsWeight,
    chiralParityGibbsWeight, chiralParityRapidity_mu_shift,
    qRapidity, qRapidity, qRapidity, Real.exp_add]
  norm_num

/-! ## q-deformed Jordan/Lie split -/

theorem chiralParity_qAffine_lie_super_split
    {A : Type*} [Semiring A] [Algebra ℂ A]
    (β μ chi : ℝ) (p q : Z2Parity) (x y : A) :
    qAffineSuperBracket (β * μ * chi) p q x y =
      (1 - chiralParityGibbsWeight β μ chi : ℂ) • lieBracket x y +
        chiralParityGibbsWeight β μ chi • superBracket p q x y := by
  simpa [qAffineSuperBracket, chiralParityGibbsWeight] using
    (affineSuperBracket_lie_super_split
      (qRapidity (β * μ * chi)) p q x y)

theorem chiralParity_qAffine_odd_odd_jordan_lie_split
    {A : Type*} [Semiring A] [Algebra ℂ A]
    (β μ chi : ℝ) (x y : A) :
    qAffineSuperBracket (β * μ * chi)
        Z2Parity.odd Z2Parity.odd x y =
      (1 - chiralParityGibbsWeight β μ chi : ℂ) • lieBracket x y +
        chiralParityGibbsWeight β μ chi • jordanProduct x y := by
  simpa [qAffineSuperBracket, chiralParityGibbsWeight] using
    (affineSuperBracket_odd_odd_jordan_lie_split
      (qRapidity (β * μ * chi)) x y)

end

end InfoGeometry.Physics
