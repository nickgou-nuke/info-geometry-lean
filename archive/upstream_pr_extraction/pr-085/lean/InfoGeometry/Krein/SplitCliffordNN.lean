import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ClNNSpecialization
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Krein.SplitCliffordNN

Krein-lane bridge to the recursive split `Cl(n,n)` owner surface from
`InfoGeometry.Clifford.ClNN`.

This file is intentionally narrow:

- expose the split `Cl(n,n)` carrier/quadratic/algebra surfaces under the
  `InfoGeometry.Krein` lane,
- expose the rank-one `(1,1)` specialization map used by downstream Krein
  consumers,
- keep the Clifford CAR structure and rank-one quadratic reduction available as
  direct bridge lemmas.

Authority note:

- ontology ownership remains in `InfoGeometry.Clifford.ClNN` and
  `InfoGeometry.Clifford.ClNNSpecialization`,
- this file is a Krein-facing transport/bridge layer.
-/

namespace InfoGeometry.Krein.SplitCliffordNN

open InfoGeometry.Clifford

/-- Split `Cl(n,n)` carrier, surfaced in the Krein lane. -/
abbrev Carrier (n : ℕ) := ClNN.Carrier n

/-- Split `Cl(n,n)` quadratic form, surfaced in the Krein lane. -/
noncomputable abbrev Quad (n : ℕ) : QuadraticForm ℝ (Carrier n) := ClNN.Quad n

/-- Split `Cl(n,n)` Clifford algebra, surfaced in the Krein lane. -/
abbrev Alg (n : ℕ) := ClNN.Alg n

/-- Rank-one specialization equivalence `Carrier 1 ≃ₗ (ℝ × ℝ)`. -/
@[rep_depth krein]
noncomputable abbrev rankOneCarrierEquiv : Carrier 1 ≃ₗ[ℝ] (ℝ × ℝ) :=
  ClNNSpecialization.rankOneEquiv

/-- Krein-lane CAR identity for the two normalized rank-head null modes. -/
@[rep_depth krein, simp] theorem gamma_head_null_car
    (n : ℕ) :
    ClNN.gammaHeadNullMinus n * ClNN.gammaHeadNullPlus n
      + ClNN.gammaHeadNullPlus n * ClNN.gammaHeadNullMinus n = (1 : Alg (n + 1)) := by
  exact ClNN.gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n

/-- Rank-one quadratic reduction from the split recursive carrier to `splitQ11`. -/
@[rep_depth krein, simp] theorem quad_rankOne_symm
    (x : ℝ × ℝ) :
    Quad 1 (rankOneCarrierEquiv.symm x) = InfoGeometry.Clifford.splitQ11 x := by
  simpa [Quad, rankOneCarrierEquiv] using ClNNSpecialization.quad_rankOneEquiv_symm x

/-- Rank-one isotropy of the normalized `u_-` split-null seed in the Krein lane. -/
@[rep_depth krein, simp] theorem quad_rankOne_headNullMinus :
    Quad 1 (ClNN.headNullMinus 0) = 0 := by
  simpa [Quad] using ClNNSpecialization.quad_rankOne_headNullMinus

/-- Rank-one isotropy of the normalized `u_+` split-null seed in the Krein lane. -/
@[rep_depth krein, simp] theorem quad_rankOne_headNullPlus :
    Quad 1 (ClNN.headNullPlus 0) = 0 := by
  simpa [Quad] using ClNNSpecialization.quad_rankOne_headNullPlus

end InfoGeometry.Krein.SplitCliffordNN
