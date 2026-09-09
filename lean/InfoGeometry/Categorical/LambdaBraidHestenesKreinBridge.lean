import InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
import InfoGeometry.Canonical.FilteredHestenesAnalyticFamily
import InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
import InfoGeometry.Krein.DoubledSpace

/-!
# Compiled lambda--braid--Hestenes--Krein bridge

This file is an integration contract, not a new analytic or topological axiom.
It collects the already proved DAG, categorical braid, and Hestenes--Krein
stage laws into one typed packet.  The three carriers remain distinct: a
lambda causal net is not silently identified with a braid group or a Hilbert
carrier.  Any physical identification must be supplied by a separate owner.
-/

noncomputable section

namespace InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge

open CategoryTheory
open InfoGeometry.Canonical
open InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.FilteredHestenesAnalyticFamily
open InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
open InfoGeometry.Krein

universe u

/-- A compiled theory packet containing the independently typed lanes of the
repository and their already established compatibility witnesses. -/
structure CompiledTheoryBridge where
  term : LambdaTerm
  net : CausalNet
  net_has_causal_past : net.HasCausalPast
  braidDiagram : BraidGroupDiagram.{u}
  braidData : ArtinNaturalData braidDiagram
  hestenesCone : HestenesKreinCone
  analyticFamily : AnalyticFamily hestenesCone

namespace CompiledTheoryBridge

variable (P : CompiledTheoryBridge.{u})

/-- The lambda lane is a finite ranked DAG. -/
theorem lambda_lane_dag :
    (lambdaToCausalNet P.term).IsDAG :=
  lambda_causal_net_preserves_dag P.term

/-- The negative-grammar lane is forced by the presence of a causal past. -/
theorem negative_grammar_lane :
    causalNetToPolarity P.net = Polarity.negative :=
  negative_grammar_async_polarity P.net P.net_has_causal_past

/-- The braid lane descends both natural endomorphisms to the categorical
colimit and preserves the finite-stage Artin equation. -/
theorem braid_lane :
    (∀ n : ℕ,
      stageInjection P.braidDiagram n ≫
          descendedEndomorphism P.braidDiagram P.braidData.braid1 =
        P.braidData.braid1.app n ≫ stageInjection P.braidDiagram n) ∧
    (∀ n : ℕ,
      stageInjection P.braidDiagram n ≫
          descendedEndomorphism P.braidDiagram P.braidData.braid2 =
        P.braidData.braid2.app n ≫ stageInjection P.braidDiagram n) ∧
    (descendedEndomorphism P.braidDiagram P.braidData.braid1 ≫
        descendedEndomorphism P.braidDiagram P.braidData.braid2 ≫
        descendedEndomorphism P.braidDiagram P.braidData.braid1 =
      descendedEndomorphism P.braidDiagram P.braidData.braid2 ≫
        descendedEndomorphism P.braidDiagram P.braidData.braid1 ≫
        descendedEndomorphism P.braidDiagram P.braidData.braid2) :=
  braid_group_colimit_artin_packet P.braidDiagram P.braidData

/-- The Hestenes--Krein lane is stage-independent for every finite
transition. -/
theorem hestenes_lane :
    ∀ n m : ℕ, ∀ x : DoubledSpace (P.hestenesCone.Base n),
      P.analyticFamily.colimitReadout (n + m)
          (FilteredPhaseCone.bondIterate
            P.hestenesCone.toFilteredPhaseCone n m x) =
        P.analyticFamily.colimitReadout n x :=
  fun n m x =>
    P.analyticFamily.colimitReadout_bondIterate n m x

/-- The derivative lane is stage-independent for every finite transition. -/
theorem hestenes_derivative_lane :
    ∀ n m : ℕ, ∀ x : DoubledSpace (P.hestenesCone.Base n),
      ((P.hestenesCone.ι (n + m)).comp
        ((P.analyticFamily.analytic (n + m)
          (FilteredPhaseCone.bondIterate
            P.hestenesCone.toFilteredPhaseCone n m x)).deriv)).comp
        (FilteredPhaseCone.bondIterate
          P.hestenesCone.toFilteredPhaseCone n m) =
      (P.hestenesCone.ι n).comp
        ((P.analyticFamily.analytic n x).deriv) :=
  fun n m x =>
    P.analyticFamily.colimitReadout_deriv_bondIterate n m x

/-- Master theorem: all three compiled lanes satisfy their native closure
laws simultaneously.  This is the strongest honest cross-lane statement
available without asserting an unproved map from lambda terms to braid groups
or from braid groups to Hestenes carriers. -/
theorem compiled_closure :
    (lambdaToCausalNet P.term).IsDAG ∧
    causalNetToPolarity P.net = Polarity.negative ∧
    (∀ n : ℕ,
      stageInjection P.braidDiagram n ≫
          descendedEndomorphism P.braidDiagram P.braidData.braid1 =
        P.braidData.braid1.app n ≫ stageInjection P.braidDiagram n) ∧
    (∀ n m : ℕ, ∀ x : DoubledSpace (P.hestenesCone.Base n),
      P.analyticFamily.colimitReadout (n + m)
          (FilteredPhaseCone.bondIterate
            P.hestenesCone.toFilteredPhaseCone n m x) =
        P.analyticFamily.colimitReadout n x) := by
  refine ⟨P.lambda_lane_dag, P.negative_grammar_lane, ?_, ?_⟩
  · exact (P.braid_lane).1
  · exact P.hestenes_lane

end CompiledTheoryBridge

end InfoGeometry.Categorical.LambdaBraidHestenesKreinBridge
