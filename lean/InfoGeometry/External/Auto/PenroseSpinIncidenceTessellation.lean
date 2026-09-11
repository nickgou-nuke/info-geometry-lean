import InfoGeometry.External.Auto.QuadraticConfiguration3
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.NonIsoConf3QuadricD4PointCount

/-!
# Three-edge spin-incidence bookkeeping

This module connects the live three-edge configuration type to six formal
alpha/beta generators in the D=4 quadric candidate.  Its finite surface includes
incidence maps, degree formulas, Arnold normalization, and the recorded point count.
-/

noncomputable section

namespace PenroseSpinIncidenceTessellation

open QuadraticConfiguration3
open NonIsoConf3QuadricD4Model
open NonIsoConf3QuadricD4PointCount

/-- Two generator labels on each of the three incidence edges. -/
abbrev SpinTileGenerator := Edge3 × Bool

/-- Map a three-point edge to its degree-one formal generator. -/
def edgeToAlpha : Edge3 → QuadricGen
  | Edge3.e12 => QuadricGen.alpha12
  | Edge3.e23 => QuadricGen.alpha23
  | Edge3.e13 => QuadricGen.alpha13

/-- Map a three-point edge to its degree-three formal generator. -/
def edgeToBeta : Edge3 → QuadricGen
  | Edge3.e12 => QuadricGen.beta12
  | Edge3.e23 => QuadricGen.beta23
  | Edge3.e13 => QuadricGen.beta13

@[simp] theorem edgeToAlpha_degree (e : Edge3) : genDegree (edgeToAlpha e) = 1 := by
  cases e <;> rfl

@[simp] theorem edgeToBeta_degree (e : Edge3) : genDegree (edgeToBeta e) = 3 := by
  cases e <;> rfl

/-- Three edges with two labels each give six finite generators. -/
theorem incidence_edge_generator_card :
    Fintype.card SpinTileGenerator = 6 := by
  decide

/-- The imported formal alpha normalization is the three-edge cycle relation. -/
theorem incidence_alpha_cycle_relation :
    NonIsoConf3QuadricD4Model.vadd
      (NonIsoConf3QuadricD4Model.vsub
        (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a12a23)
        (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a12a13))
      (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a23a13) = 0 :=
  NonIsoConf3QuadricD4Model.alpha_arnold_relation

/-- Consolidated finite incidence and arithmetic statement. -/
theorem penrose_spin_incidence_tessellation_synthesis :
    Fintype.card SpinTileGenerator = 6 ∧
    (∀ e : Edge3, genDegree (edgeToAlpha e) = 1) ∧
    (∀ e : Edge3, genDegree (edgeToBeta e) = 3) ∧
    NonIsoConf3QuadricD4Model.vadd
      (NonIsoConf3QuadricD4Model.vsub
        (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a12a23)
        (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a12a13))
      (NonIsoConf3QuadricD4Model.reduceAlphaProduct AlphaProduct.a23a13) = 0 ∧
    countPolynomial 3 = 1296 :=
  ⟨incidence_edge_generator_card,
    edgeToAlpha_degree,
    edgeToBeta_degree,
    incidence_alpha_cycle_relation,
    countPolynomial_at_three⟩

end PenroseSpinIncidenceTessellation

end noncomputable section
