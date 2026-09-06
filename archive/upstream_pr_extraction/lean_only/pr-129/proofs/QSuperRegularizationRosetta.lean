import proofs.QSuperCuntzRegularization
import proofs.RegularizationCayleyPipeline

/-!
# q-super regularization Rosetta layer

This module is an index/bridge layer for the four regularization mechanisms
that are already proved in the finite q-super-Cuntz layer.

It does not prove the analytic q→1 colimit or full representation theory.
These remain open analytic properties. The proved
part here is the finite Rosetta dictionary:

* Minkowski signature is the superparity/Krein operator.
* Lorentz-weighted bilinear readout is the finite supertrace.
* Spectral squashing is bounded by `tanh`.
* The Cayley boundary is unitary, hence lives on the CUE/q-circle side.
-/

noncomputable section

namespace QSuperRegularizationRosetta

open Matrix

abbrev M2C := QSuperCuntzRegularization.M2C

/-- The four regularization roles unified by the q-super-Cuntz layer. -/
inductive RegularizationRole where
  | minkowskiSignature
  | lorentzBilinear
  | spectralSquashing
  | cueCircle
  deriving DecidableEq, Repr, Inhabited

open RegularizationRole

/-- An entry in the regularization dictionary.

`finiteContract` is the part backed by compiled finite Lean facts. -/
structure RegularizationProjection where
  role : RegularizationRole
  phenomenologicalName : String
  qSuperOrigin : String
  mathematicalRole : String
  finiteContract : Prop

/-- The four-entry Rosetta dictionary as projections out of the q-super root. -/
def projection : RegularizationRole → RegularizationProjection
  | minkowskiSignature =>
      { role := minkowskiSignature
        phenomenologicalName := "Minkowski signature eta"
        qSuperOrigin := "superparity (-1)^F = PB - PF"
        mathematicalRole := "endogenous signed metric from the two Cuntz sectors"
        finiteContract :=
          QSuperCuntzRegularization.superParityOperator = SpectralSquashCayleyDKT.eta ∧
          QSuperCuntzRegularization.superParityOperator * QSuperCuntzRegularization.superParityOperator = 1 ∧
          star QSuperCuntzRegularization.superParityOperator = QSuperCuntzRegularization.superParityOperator }
  | lorentzBilinear =>
      { role := lorentzBilinear
        phenomenologicalName := "Lorentz bilinear supertrace"
        qSuperOrigin := "STr(X) = Tr((-1)^F X)"
        mathematicalRole := "metric-weighted finite expectation functional"
        finiteContract := ∀ X : M2C, QSuperCuntzRegularization.supertrace X = X 0 0 - X 1 1 }
  | spectralSquashing =>
      { role := spectralSquashing
        phenomenologicalName := "spectral tanh squashing"
        qSuperOrigin := "q-integer / root-of-unity truncation shadow"
        mathematicalRole := "bounded coordinate for the regularized spectrum"
        finiteContract := ∀ lam : ℝ, -1 < SpectralSquashCayleyDKT.squashCoord lam ∧ SpectralSquashCayleyDKT.squashCoord lam < 1 }
  | cueCircle =>
      { role := cueCircle
        phenomenologicalName := "CUE / q-circle boundary"
        qSuperOrigin := "unitary Cayley coordinate"
        mathematicalRole := "unit-circle coordinate for bounded C*-colimit stages"
        finiteContract :=
          ∀ lam : ℝ,
            SpectralSquashCayleyDKT.cayleyStage lam * star (SpectralSquashCayleyDKT.cayleyStage lam) = 1 ∧
            SpectralSquashCayleyDKT.cayleyStage lam * SpectralSquashCayleyDKT.dktAdjoint (SpectralSquashCayleyDKT.cayleyStage lam) = 1 }

/-- The complete regularization dictionary rooted at `O_q(1|1)`. -/
structure RosettaStone where
  rootAlgebra : String
  finiteLayer : String
  colimitLayer : String
  continuousLayer : String
  minkowskiSignature : RegularizationProjection
  lorentzBilinear : RegularizationProjection
  spectralSquashing : RegularizationProjection
  qCircleCue : RegularizationProjection

/-- Concrete Rosetta record for a chosen q-parameter. -/
def rosetta (_q : ℂ) : RosettaStone where
  rootAlgebra := "O_q(1|1)"
  finiteLayer := "root-of-unity finite q-super-Cuntz stage"
  colimitLayer := "q -> 1 C*-colimit / Cayley bounded flow"
  continuousLayer := "inverse-Cayley macroscopic spacetime boundary"
  minkowskiSignature := projection minkowskiSignature
  lorentzBilinear := projection lorentzBilinear
  spectralSquashing := projection spectralSquashing
  qCircleCue := projection cueCircle

/-- The finite part of the Rosetta dictionary is exactly the already-compiled
q-super-Cuntz regularization synthesis. -/
theorem q_super_rosetta_finite_contracts :
    (projection minkowskiSignature).finiteContract ∧
    (projection lorentzBilinear).finiteContract ∧
    (projection spectralSquashing).finiteContract ∧
    (projection cueCircle).finiteContract := by
  constructor
  · constructor
    · exact QSuperCuntzRegularization.superParity_eq_eta
    · constructor
      · exact QSuperCuntzRegularization.superParity_sq
      · exact QSuperCuntzRegularization.superParity_selfadjoint
  · constructor
    · intro X
      exact QSuperCuntzRegularization.supertrace_apply X
    · constructor
      · intro mu
        exact SpectralSquashCayleyDKT.squashCoord_bounded mu
      · intro mu
        constructor
        · exact SpectralSquashCayleyDKT.cayleyStage_unitary mu
        · exact QSuperCuntzRegularization.cayley_superparity_unitary mu

/-- A named capstone for the q-super regularization Rosetta layer. -/
theorem q_super_regularization_rosetta_synthesis (q : ℂ) :
    (rosetta q).rootAlgebra = "O_q(1|1)" ∧
    (rosetta q).minkowskiSignature.finiteContract ∧
    (rosetta q).lorentzBilinear.finiteContract ∧
    (rosetta q).spectralSquashing.finiteContract ∧
    (rosetta q).qCircleCue.finiteContract := by
  constructor
  · rfl
  · constructor
    · exact q_super_rosetta_finite_contracts.left
    · constructor
      · exact q_super_rosetta_finite_contracts.right.left
      · constructor
        · exact q_super_rosetta_finite_contracts.right.right.left
        · exact q_super_rosetta_finite_contracts.right.right.right

end QSuperRegularizationRosetta

end noncomputable section
