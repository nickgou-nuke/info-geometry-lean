import Mathlib
import proofs.QuadraticConfiguration3
import proofs.NonIsoConf3OrlikSolomon
import proofs.NonIsoConf3QuadricD4Model
import proofs.NonIsoConf3QuadricD4PointCount

/-!
# Three-point non-isotropic quadric configuration: finite de Rham/cooperad colimit form

This module assembles the finite 3-point package into an inductive finite
colimit shape built from finite-stage data:

1. corrected D=4 cooperad signature,
2. Orlik--Solomon finite form,
3. D=4 rank data, and
4. point-count values.
-/

noncomputable section

namespace NonIsoConf3ThreePointDeRhamCooperad


/-- Finite arity-three cooperad signature in ambient degree `D = 4`. -/
def fourD_cooperad_signature : Prop :=
  (∀ e : QuadraticConfiguration3.Edge3,
      QuadraticConfiguration3.genDegree 4 ⟨e, QuadraticConfiguration3.GenKind.alpha⟩ = 1) ∧
    (∀ e : QuadraticConfiguration3.Edge3,
      QuadraticConfiguration3.genDegree 4 ⟨e, QuadraticConfiguration3.GenKind.beta⟩ = 3) ∧
      (∀ b : QuadraticConfiguration3.BlockDecomp3,
        ∃ e : QuadraticConfiguration3.Edge3,
          QuadraticConfiguration3.cooperadEdge b e = QuadraticConfiguration3.TargetFactor.internal) ∧
        (∀ b : QuadraticConfiguration3.BlockDecomp3,
          ∀ e : QuadraticConfiguration3.Edge3,
            QuadraticConfiguration3.cooperadEdge b e = QuadraticConfiguration3.TargetFactor.outer ∨
              QuadraticConfiguration3.cooperadEdge b e = QuadraticConfiguration3.TargetFactor.internal)

/-- Orlik--Solomon finite-form proposition. -/
def OrlikOSData : Prop :=
  NonIsoConf3OrlikSolomon.vadd
      (NonIsoConf3OrlikSolomon.vsub
        (NonIsoConf3OrlikSolomon.reduceProduct NonIsoConf3OrlikSolomon.PairProduct.A12A23)
        (NonIsoConf3OrlikSolomon.reduceProduct NonIsoConf3OrlikSolomon.PairProduct.A12A13))
      (NonIsoConf3OrlikSolomon.reduceProduct NonIsoConf3OrlikSolomon.PairProduct.A23A13) = 0 ∧
    NonIsoConf3OrlikSolomon.slotRank NonIsoConf3OrlikSolomon.CohomologySlot.degree0 = 1 ∧
      NonIsoConf3OrlikSolomon.slotRank NonIsoConf3OrlikSolomon.CohomologySlot.degreeGenerator = 3 ∧
        NonIsoConf3OrlikSolomon.slotRank NonIsoConf3OrlikSolomon.CohomologySlot.degreeQuadratic = 2 ∧
          NonIsoConf3OrlikSolomon.delta12 NonIsoConf3OrlikSolomon.PairGen.A12 =
            { macroPart := none, micro := some NonIsoConf3OrlikSolomon.PairGen.A12 } ∧
          NonIsoConf3OrlikSolomon.delta12 NonIsoConf3OrlikSolomon.PairGen.A13 =
            { macroPart := some NonIsoConf3OrlikSolomon.PairGen.A13, micro := none }

/-- D=4 rank proposition for the corrected model. -/
def D4RankData : Prop :=
  NonIsoConf3QuadricD4Model.genDegree NonIsoConf3QuadricD4Model.QuadricGen.alpha12 = 1 ∧
    NonIsoConf3QuadricD4Model.genDegree NonIsoConf3QuadricD4Model.QuadricGen.beta12 = 3 ∧
      NonIsoConf3QuadricD4Model.vadd
        (NonIsoConf3QuadricD4Model.vsub
          (NonIsoConf3QuadricD4Model.reduceAlphaProduct NonIsoConf3QuadricD4Model.AlphaProduct.a12a23)
          (NonIsoConf3QuadricD4Model.reduceAlphaProduct NonIsoConf3QuadricD4Model.AlphaProduct.a12a13))
        (NonIsoConf3QuadricD4Model.reduceAlphaProduct NonIsoConf3QuadricD4Model.AlphaProduct.a23a13) = 0 ∧
        NonIsoConf3QuadricD4Model.candidateRank 0 = 1 ∧
          NonIsoConf3QuadricD4Model.candidateRank 1 = 3 ∧
            NonIsoConf3QuadricD4Model.candidateRank 2 = 2 ∧
              NonIsoConf3QuadricD4Model.candidateRank 12 = 0

/-- D=4 finite point-count value proposition. -/
def PointCountValues : Prop :=
  NonIsoConf3QuadricD4PointCount.countPolynomial 3 = 1296 ∧
    NonIsoConf3QuadricD4PointCount.countPolynomial 5 = 175200 ∧
      NonIsoConf3QuadricD4PointCount.countPolynomial 7 = 3400992 ∧
        NonIsoConf3QuadricD4PointCount.countPolynomial 11 = 156961200

/-- Finite D=4 cooperad signature. -/
theorem fourD_cooperad_signature_proof :
    fourD_cooperad_signature := by
  refine ⟨?hα, ?hβ, ?hint, ?hover⟩
  · intro e
    simp [QuadraticConfiguration3.genDegree]
  · intro e
    simp [QuadraticConfiguration3.genDegree]
  · intro b
    exact QuadraticConfiguration3.cooperad_has_internal_edge b
  · intro b e
    exact QuadraticConfiguration3.cooperad_edge_outer_or_internal b e

/-- Four finite colimit stages for the 3-point package. -/
inductive ThreePointStage where
  | cooperad
  | orlikSolomon
  | d4Candidate
  | pointCount
  deriving DecidableEq, Fintype, Repr

/-- Data available at each finite stage.  The final stage contains all previous
requirements, so this is an inductive colimit as cumulative finite evidence. -/
def ThreePointStage.data : ThreePointStage → Prop
  | ThreePointStage.cooperad => fourD_cooperad_signature
  | ThreePointStage.orlikSolomon => fourD_cooperad_signature ∧ OrlikOSData
  | ThreePointStage.d4Candidate => fourD_cooperad_signature ∧ OrlikOSData ∧ D4RankData
  | ThreePointStage.pointCount =>
      fourD_cooperad_signature ∧ OrlikOSData ∧ D4RankData ∧ PointCountValues

/-- The final finite stage is the finite 3-point colimit target. -/
def three_point_non_iso_colimit_target : Prop :=
  ThreePointStage.data ThreePointStage.pointCount

/-- Inductive colimit theorem assembling finite data in cumulative stages. -/
theorem three_point_non_iso_D4_inductive_colimit :
    three_point_non_iso_colimit_target := by
  exact ⟨fourD_cooperad_signature_proof,
    by
      simpa [OrlikOSData] using
        NonIsoConf3OrlikSolomon.non_iso_conf3_os_cooperad_synthesis,
    by
      simpa [D4RankData] using
        NonIsoConf3QuadricD4Model.corrected_d4_candidate_synthesis,
    by
      exact ⟨NonIsoConf3QuadricD4PointCount.countPolynomial_at_three,
        NonIsoConf3QuadricD4PointCount.countPolynomial_at_five,
        NonIsoConf3QuadricD4PointCount.countPolynomial_at_seven,
        NonIsoConf3QuadricD4PointCount.countPolynomial_at_eleven⟩⟩


end NonIsoConf3ThreePointDeRhamCooperad

end noncomputable section
