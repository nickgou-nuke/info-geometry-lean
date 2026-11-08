import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

theorem souriauChargeMeanFunctional_apply
    (beta : Fin 2 → ℝ) (v : Fin 2 → ℝ) :
    souriauChargeMeanFunctional D beta v =
      ∑ i : Fin 2, souriauChargeMean D beta i * v i := by
  rfl

theorem souriauChargeMeanFunctional_apply_pi_single
    (beta : Fin 2 → ℝ) (i : Fin 2) :
    souriauChargeMeanFunctional D beta (Pi.single i 1) =
      souriauChargeMean D beta i := by
  rw [souriauChargeMeanFunctional_apply]
  fin_cases i <;> simp [Pi.single]

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

/-!
## Finite affine entropy consumer

The preceding generic theorem owns the affine cancellation between the
Massieu defect and the transported heat vector.  This theorem instantiates
that result for the finite Cartan Gibbs datum; no Lie-group or manifold
structure is inferred here.
-/

theorem finiteCartanSouriauEntropy_affine_invariant
    (G : Type*)
    (action : LieGroupAction G (Fin 2 → ℝ))
    (cocycle : G → LieDual (Fin 2 → ℝ))
    (g : G)
    (h_Psi_cov : ∀ (g : G) (β : Fin 2 → ℝ),
      souriauMassieu D (action.Ad g β) =
        souriauMassieu D β - cocycle g (action.Ad g β))
    (h_heat_cov : ∀ (g : G) (β : Fin 2 → ℝ),
      souriauChargeMeanFunctional D (action.Ad g β) =
        coadjoint (action.Ad g) (souriauChargeMeanFunctional D β) + cocycle g)
    (h_zero_cocycle : cocycle g = 0)
    (β : Fin 2 → ℝ) :
    souriauEntropy (finiteCartanSouriauAction D G action cocycle)
        (action.Ad g β) =
      souriauEntropy (finiteCartanSouriauAction D G action cocycle) β := by
  exact SouriauCoadjoint.souriau_entropy_linear_invariance
    (finiteCartanSouriauAction D G action cocycle) g h_Psi_cov h_heat_cov
    h_zero_cocycle β
