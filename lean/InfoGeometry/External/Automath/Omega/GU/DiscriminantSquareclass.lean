import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.GU.DiscriminantWedge2Square
import InfoGeometry.External.Automath.Omega.GU.JoukowskyGodelLeadingCoeffRigidity
import InfoGeometry.External.Automath.Omega.GU.JoukowskyGodelPullbackFactorization

namespace Omega.GU

open scoped BigOperators

variable {K : Type*} [Field K]

/-- The degree-2 transported root `w = r z + r⁻¹ z⁻¹`. -/
noncomputable def quadraticTransportRoot (r z : K) : K :=
  r * z + r⁻¹ * z⁻¹

/-- Degree-2 discriminant written as leading coefficient squared times the squared root gap. -/
def quadraticPolynomialDiscriminant (a z₁ z₂ : K) : K :=
  a ^ 2 * (z₁ - z₂) ^ 2

/-- Equality in the square-class quotient, encoded by an explicit square factor. -/
def sameSquareclass (a b : K) : Prop :=
  ∃ u : K, a = b * u ^ 2

/-- The degree-2 Joukowsky--Godel transport package specialized to roots `z₁,z₂`. -/
noncomputable def quadraticJoukowskyGodelTransportData
    (a_n a_0 r z₁ z₂ : K) (hVieta : a_n * (z₁ * z₂) = a_0) :
    JoukowskyGodelTransportData K where
  n := 2
  a_n := a_n
  a_0 := a_0
  r := r
  roots := ![z₁, z₂]
  hVieta := by
    simpa using hVieta

/-- The explicit square factor relating the discriminants of `P` and the transported quadratic
`Q_r`. -/
noncomputable def quadraticTransportSquareWitness (a_0 r z₁ z₂ : K) : K :=
  a_0 * (r - r⁻¹ * (z₁ * z₂)⁻¹)

/-- Expanding the transported roots gives the expected root-gap factorization. -/
theorem quadraticTransportRoot_sub
    (r z₁ z₂ : K) (hr : r ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    quadraticTransportRoot r z₁ - quadraticTransportRoot r z₂ =
      (z₁ - z₂) * (r - r⁻¹ * (z₁ * z₂)⁻¹) := by
  unfold quadraticTransportRoot
  field_simp [hr, hz₁, hz₂]
  ring

/-- Degree-2 squareclass conservation for the Joukowsky--Godel transport: the transported
discriminant differs from the original discriminant by an explicit square.
    thm:group-jg-discriminant-squareclass -/
theorem paper_group_jg_discriminant_squareclass
    (a_n a_0 r z₁ z₂ : K)
    (hr : r ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hVieta : a_n * (z₁ * z₂) = a_0) :
    let D := quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta
    let ΔQ :=
      quadraticPolynomialDiscriminant
        D.transportLeadingCoeff
        (quadraticTransportRoot r z₁)
        (quadraticTransportRoot r z₂)
    let ΔP := quadraticPolynomialDiscriminant a_n z₁ z₂
    ΔQ = ΔP * (quadraticTransportSquareWitness a_0 r z₁ z₂) ^ 2 ∧
      sameSquareclass ΔQ ΔP := by
  dsimp
  have hlead :
      (quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta).transportLeadingCoeff =
        a_n * a_0 := by
    simpa [quadraticJoukowskyGodelTransportData] using
      paper_group_jg_lc_rigidity
        (quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta)
  have hw :
      quadraticTransportRoot r z₁ - quadraticTransportRoot r z₂ =
        (z₁ - z₂) * (r - r⁻¹ * (z₁ * z₂)⁻¹) :=
    quadraticTransportRoot_sub r z₁ z₂ hr hz₁ hz₂
  have hfactor :
      quadraticPolynomialDiscriminant
          (quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta).transportLeadingCoeff
          (quadraticTransportRoot r z₁)
          (quadraticTransportRoot r z₂) =
        quadraticPolynomialDiscriminant a_n z₁ z₂ *
          (quadraticTransportSquareWitness a_0 r z₁ z₂) ^ 2 := by
    rw [hlead]
    simp [quadraticPolynomialDiscriminant, quadraticTransportSquareWitness, hw]
    ring
  refine ⟨hfactor, ?_⟩
  exact ⟨quadraticTransportSquareWitness a_0 r z₁ z₂, hfactor⟩

end Omega.GU
