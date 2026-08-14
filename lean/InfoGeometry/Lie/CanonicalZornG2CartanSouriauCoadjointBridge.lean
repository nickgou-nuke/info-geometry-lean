import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Canonical.SouriauCoadjointCovariance
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section

open SouriauCoadjoint
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {State : Type*} [Fintype State] [Nonempty State] (D : CartanSouriauDatum State)

def souriauChargeMeanFunctional (beta : Fin 2 → ℝ) : LieDual (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap 
    { toFun := fun v => ∑ i : Fin 2, souriauChargeMean D beta i * v i,
      map_add' := by intro x y; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        change (∑ i : Fin 2, souriauChargeMean D beta i * (c * x i)) = c * ∑ i : Fin 2, souriauChargeMean D beta i * x i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }

/-- The abstract Souriau thermodynamic action instance for the finite Cartan model.
We parameterize over a generic group action and cocycle, as the concrete
adjoint action must be provided by the global symmetry layer. -/
def finiteCartanSouriauAction (G : Type*)
    (action : LieGroupAction G (Fin 2 → ℝ))
    (cocycle : G → LieDual (Fin 2 → ℝ)) : 
    SouriauThermodynamicAction G (Fin 2 → ℝ) where
  action := action
  cocycle := cocycle
  Psi := fun beta => souriauMassieu D beta
  heatVector := fun beta => souriauChargeMeanFunctional D beta
