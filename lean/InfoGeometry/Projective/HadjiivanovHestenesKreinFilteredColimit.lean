/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
import InfoGeometry.Topology.ArtinBraidRep
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Hadjiivanov--Hestenes--Krein filtered descent

This owner uses the repository's canonical doubled filtered cone directly.
-/

noncomputable section

namespace InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit

open FilteredColimit
open FilteredColimit.InductiveCocone
open InfoGeometry.Topology.ArtinBraid
open InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
open InfoGeometry.Krein

variable {I : Type*} [Preorder I]
variable {Stage : I → Type}
variable [∀ i, AddCommGroup (Stage i)]
variable [∀ i, Module ℂ (Stage i)]

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

variable (C : HestenesKreinCone)

theorem bond_phase_linear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.bond n) (clockPhaseStructure (C.Base (n + 1))) :=
  C.bond_hestenes n

theorem inclusion_phase_linear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.ι n) (clockPhaseStructure C.LimitBase) :=
  C.ι_hestenes n

theorem inclusion_bond_iterate (n m : ℕ)
    (x : DoubledSpace (C.Base n)) :
    C.ι (n + m) (FilteredPhaseCone.bondIterate
      C.toFilteredPhaseCone n m x) = C.ι n x := by
  exact FilteredPhaseCone.ι_bondIterate_apply C.toFilteredPhaseCone n m x

theorem bond_iterate_phase_linear (n m : ℕ) :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m)
      (clockPhaseStructure (C.Base (n + m))) := by
  exact FilteredPhaseCone.bondIterate_phaseLinear C.toFilteredPhaseCone n m


structure CategoricalHadjiivanovData
    (sys : DirectInductiveSystem ℂ I Stage)
    (Ainf : Type) [NormedAddCommGroup Ainf] [NormedSpace ℂ Ainf]
    (cocone : InductiveCocone ℂ sys Ainf)
    [InnerProductSpace ℝ Ainf] [CompleteSpace Ainf] where
  stageMonodromy : ∀ i, Stage i →ₗ[ℂ] Stage i
  ambientMonodromy : Ainf →L[ℂ] Ainf
  stageDescent :
    ∀ i, ambientMonodromy.toLinearMap.comp (cocone.psi i) =
      (cocone.psi i).comp (stageMonodromy i)
  braidGenerators : ArtinBraidRepData ℂ Ainf
  braidLaw : IsArtinBraidRep braidGenerators
  monodromy_braid_commutes :
    ∀ i, ambientMonodromy.toLinearMap.comp (braidGenerators.sigma i) =
      (braidGenerators.sigma i).comp ambientMonodromy.toLinearMap

namespace CategoricalHadjiivanovData

variable {sys : DirectInductiveSystem ℂ I Stage}
variable {Ainf : Type} [NormedAddCommGroup Ainf] [NormedSpace ℂ Ainf]
variable {cocone : InductiveCocone ℂ sys Ainf}
variable [InnerProductSpace ℝ Ainf] [CompleteSpace Ainf]
variable (D : CategoricalHadjiivanovData sys Ainf cocone)

def doubledMonodromy : DoubledSpace Ainf →L[ℝ] DoubledSpace Ainf :=
  doubledContinuousLinearMap (D.ambientMonodromy.restrictScalars ℝ)

theorem doubledMonodromy_isHestenes :
    IsHestenesHolomorphicDifferential
      (E := Ainf) (F := Ainf) D.doubledMonodromy :=
  doubledContinuousLinearMap_isHestenes
    (D.ambientMonodromy.restrictScalars ℝ)

theorem doubledMonodromy_clockAxis (x : DoubledSpace Ainf) :
    D.doubledMonodromy (clockAxis (E := Ainf) x) =
      clockAxis (E := Ainf) (D.doubledMonodromy x) := by
  exact congrArg (fun L : DoubledSpace Ainf →L[ℝ] DoubledSpace Ainf => L x)
    (doubledMonodromy_isHestenes D)

theorem ambientMonodromy_stage_independent {i j : I} (hij : i ≤ j) (x : Stage i) :
    D.ambientMonodromy (cocone.psi j (sys.f hij x)) =
      cocone.psi i (D.stageMonodromy i x) := by
  rw [cocone.cocone_eval_comm hij x]
  exact LinearMap.congr_fun (D.stageDescent i) x

theorem stageMonodromy_after_transition {i j : I} (hij : i ≤ j) (x : Stage i) :
    cocone.psi j (sys.f hij (D.stageMonodromy i x)) =
      D.ambientMonodromy (cocone.psi j (sys.f hij x)) := by
  rw [cocone.cocone_eval_comm hij (D.stageMonodromy i x),
    cocone.cocone_eval_comm hij x]
  exact (LinearMap.congr_fun (D.stageDescent i) x).symm


theorem categorical_hk_braid_descent {i j : I} (hij : i ≤ j) (x : Stage i) :
    cocone.psi j (sys.f hij x) = cocone.psi i x ∧
    D.doubledMonodromy (clockAxis (E := Ainf)
      (to_doubled (cocone.psi i x) (cocone.psi i x))) =
      clockAxis (E := Ainf)
        (D.doubledMonodromy (to_doubled (cocone.psi i x) (cocone.psi i x))) ∧
    AdjacentBraidLaw D.braidGenerators ∧ FarBraidLaw D.braidGenerators := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cocone.cocone_eval_comm hij x
  · exact D.doubledMonodromy_clockAxis _
  · exact artin_adjacent_readout D.braidGenerators D.braidLaw
  · exact artin_far_readout D.braidGenerators D.braidLaw

theorem braid_monodromy_commutation (i : ℕ) (x : Ainf) :
    D.ambientMonodromy (D.braidGenerators.sigma i x) =
      D.braidGenerators.sigma i (D.ambientMonodromy x) := by
  exact LinearMap.congr_fun (D.monodromy_braid_commutes i) x

end CategoricalHadjiivanovData

end InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit
