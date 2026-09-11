import InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topological adapter for the finite `Cl(1,1)` compatible local state net

The algebraic owner supplies the diagonal-block restriction and its normalized
trace compatibility.  This owner exposes those same maps as continuous
`TopCat` morphisms.  It does not construct a completed UHF algebra or a global
KMS state.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological

open CategoryTheory
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet

def stageRestrictTopCatHom (n : ℕ) :
    TopCat.of (MatStage (n + 1)) ⟶ TopCat.of (MatStage n) :=
  TopCat.ofHom
    { toFun := stageRestrict n
      continuous_toFun :=
        (stageRestrict n).continuous_of_finiteDimensional }

@[simp] theorem stageRestrictTopCatHom_apply
    (n : ℕ) (X : MatStage (n + 1)) :
    stageRestrictTopCatHom n X = stageRestrict n X :=
  rfl

theorem stageRestrictTopCatHom_stageEmbed
    (n : ℕ) (A : MatStage n) :
    stageRestrictTopCatHom n (stageEmbed n A) = A := by
  change stageRestrict n (stageEmbed n A) = A
  exact stageRestrict_stageEmbed n A

theorem normalizedTraceTopCatHom_restrict
    (n : ℕ) (X : MatStage (n + 1)) :
    normalizedTraceLinear n (stageRestrictTopCatHom n X) =
      normalizedTraceLinear (n + 1) X := by
  change normalizedTrace n (stageRestrict n X) =
    normalizedTrace (n + 1) X
  exact normalizedTrace_stageRestrict n X


end InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological
