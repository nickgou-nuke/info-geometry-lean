import InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
import InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
import InfoGeometry.Topology.ArtinBraidRep

/-!
# Categorical Hadjiivanov--Hestenes--Krein braid descent

This file is the categorical completion of the finite Hadjiivanov logarithmic
connection lane. The filtered system is represented by the native
FilteredColimit.InductiveCocone, not by a merely sequential cone.

The theorem is intentionally conditional at the analytic boundary: a
continuous complex-linear ambient monodromy is supplied explicitly. Its
restriction to scalars and canonical doubling give the Hestenes--Krein
differential; no unproved analytic continuation or holonomy theorem is hidden
in the definitions.
-/

noncomputable section

namespace InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit

open FilteredColimit
open FilteredColimit.InductiveCocone
open InfoGeometry.Topology.ArtinBraid
open InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit
open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity

universe u

variable {I : Type*} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, AddCommGroup (Stage i)]
variable [∀ i, Module ℂ (Stage i)]

/-- Categorical filtered Hadjiivanov data with a single ambient monodromy. -/
structure CategoricalHadjiivanovData
    (sys : DirectInductiveSystem ℂ I Stage)
    (Ainf : Type u) [AddCommGroup Ainf] [Module ℂ Ainf]
    (cocone : InductiveCocone ℂ sys Ainf)
    [NormedAddCommGroup Ainf] [NormedSpace ℂ Ainf] where
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
variable {Ainf : Type u} [AddCommGroup Ainf] [Module ℂ Ainf]
variable {cocone : InductiveCocone ℂ sys Ainf}
variable [NormedAddCommGroup Ainf] [NormedSpace ℂ Ainf]
variable (D : CategoricalHadjiivanovData sys Ainf cocone)

/-- The ambient monodromy is Hestenes--Krein analytic after restriction of
scalars and canonical doubling. -/
def doubledMonodromy :
    DoubledSpace Ainf →L[ℝ] DoubledSpace Ainf :=
  doubledContinuousLinearMap (D.ambientMonodromy.restrictScalars ℝ)

theorem doubledMonodromy_isHestenes :
    IsHestenesHolomorphicDifferential
      (E := Ainf) (F := Ainf) D.doubledMonodromy :=
  doubledContinuousLinearMap_isHestenes
    (D.ambientMonodromy.restrictScalars ℝ)

/-- The doubled ambient monodromy has the native Hestenes clock-axis law. -/
theorem doubledMonodromy_clockAxis
    (x : DoubledSpace Ainf) :
    D.doubledMonodromy (clockAxis (E := Ainf) x) =
      clockAxis (E := Ainf) (D.doubledMonodromy x) := by
  exact congrArg
    (fun L : DoubledSpace Ainf →L[ℝ] DoubledSpace Ainf => L x)
    (doubledMonodromy_isHestenes D)

/-- A stage representative has the same ambient monodromy readout after any
single filtered transition. -/
theorem ambientMonodromy_stage_independent
    {i j : I} (hij : i ≤ j) (x : Stage i) :
    D.ambientMonodromy
        (cocone.psi j (sys.f hij x)) =
      cocone.psi i (D.stageMonodromy i x) := by
  rw [cocone.colimit_functional_trace_comm
    D.ambientMonodromy.toLinearMap hij x]
  exact LinearMap.congr_fun (D.stageDescent i) x

/-- The stage monodromy intertwines through every filtered transition. -/
theorem stageMonodromy_after_transition
    {i j : I} (hij : i ≤ j) (x : Stage i) :
    cocone.psi j (sys.f hij (D.stageMonodromy i x)) =
      D.ambientMonodromy
        (cocone.psi j (sys.f hij x)) := by
  rw [D.ambientMonodromy_stage_independent hij x]
  rw [cocone.colimit_functional_trace_comm
    D.ambientMonodromy.toLinearMap hij (D.stageMonodromy i x)]
  exact LinearMap.congr_fun (D.stageDescent i) (D.stageMonodromy i x)

/-- The categorical cocone, Hestenes analyticity, and Artin braid laws form one
descent packet. -/
theorem categorical_hk_braid_descent
    {i j : I} (hij : i ≤ j) (x : Stage i) :
    cocone.psi j (sys.f hij x) = cocone.psi i x ∧
    D.doubledMonodromy (clockAxis (E := Ainf)
      (to_doubled (cocone.psi i x) (cocone.psi i x))) =
      clockAxis (E := Ainf)
        (D.doubledMonodromy
          (to_doubled (cocone.psi i x) (cocone.psi i x))) ∧
    AdjacentBraidLaw D.braidGenerators ∧
    FarBraidLaw D.braidGenerators := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cocone.cocone_eval_comm hij x
  · exact D.doubledMonodromy_clockAxis _
  · exact artin_adjacent_readout D.braidGenerators D.braidLaw
  · exact artin_far_readout D.braidGenerators D.braidLaw

/-- The braid representation preserves the Hestenes monodromy law on every
finite stage whenever the explicit ambient commutation witnesses hold. -/
theorem braid_monodromy_commutation
    (i : ℕ) (x : Ainf) :
    D.ambientMonodromy (D.braidGenerators.sigma i x) =
      D.braidGenerators.sigma i (D.ambientMonodromy x) := by
  exact LinearMap.congr_fun (D.monodromy_braid_commutes i) x

end CategoricalHadjiivanovData

end InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit
