import InfoGeometry.Canonical.SouriauCoadjointCovariance
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCoadjointBridge

/-!
# Souriau thermodynamic states on coadjoint orbits

This file packages the existing Souriau covariance theorem as an explicit
orbit statement. The zero-cocycle case is the genuine coadjoint orbit; the
nonzero-cocycle case remains affine coadjoint covariance in the imported owner.
-/

namespace InfoGeometry.Canonical.SouriauThermodynamicCoadjointOrbitBridge

open SouriauCoadjoint
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

variable {G V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def coadjointOrbit (act : LieGroupAction G V) (μ : LieDual V) : Set (LieDual V) :=
  {ν | ∃ g : G, ν = coadjoint (act.Ad g) μ}

theorem heatVector_mem_coadjointOrbit_of_zeroCocycle
    (sys : SouriauThermodynamicAction G V)
    (g : G)
    (h_heat_cov : ∀ (g : G) (β : V),
      sys.heatVector (sys.action.Ad g β) =
        coadjoint (sys.action.Ad g) (sys.heatVector β) + sys.cocycle g)
    (h_zero_cocycle : sys.cocycle g = 0) (β : V) :
    sys.heatVector (sys.action.Ad g β) ∈
      coadjointOrbit sys.action (sys.heatVector β) := by
  refine ⟨g, ?_⟩
  exact SouriauCoadjoint.heatVector_linear_covariance
    sys g h_heat_cov h_zero_cocycle β

theorem thermodynamicState_entropy_invariant_of_zeroCocycle
    (sys : SouriauThermodynamicAction G V)
    (g : G)
    (h_Psi_cov : ∀ (g : G) (β : V),
      sys.Psi (sys.action.Ad g β) =
        sys.Psi β - sys.cocycle g (sys.action.Ad g β))
    (h_heat_cov : ∀ (g : G) (β : V),
      sys.heatVector (sys.action.Ad g β) =
        coadjoint (sys.action.Ad g) (sys.heatVector β) + sys.cocycle g)
    (h_zero_cocycle : sys.cocycle g = 0) (β : V) :
    souriauEntropy sys (sys.action.Ad g β) = souriauEntropy sys β :=
  SouriauCoadjoint.souriau_entropy_linear_invariance
    sys g h_Psi_cov h_heat_cov h_zero_cocycle β

theorem finiteCartan_chargeMean_mem_coadjointOrbit_of_zeroCocycle
    {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State)
    (G : Type*)
    (action : LieGroupAction G (Fin 2 → ℝ))
    (cocycle : G → LieDual (Fin 2 → ℝ))
    (g : G)
    (h_heat_cov : ∀ (g : G) (β : Fin 2 → ℝ),
      souriauChargeMeanFunctional D (action.Ad g β) =
        coadjoint (action.Ad g) (souriauChargeMeanFunctional D β) + cocycle g)
    (h_zero_cocycle : cocycle g = 0) (β : Fin 2 → ℝ) :
    souriauChargeMeanFunctional D (action.Ad g β) ∈
      coadjointOrbit action (souriauChargeMeanFunctional D β) := by
  exact heatVector_mem_coadjointOrbit_of_zeroCocycle
    (finiteCartanSouriauAction D G action cocycle) g h_heat_cov h_zero_cocycle β

end InfoGeometry.Canonical.SouriauThermodynamicCoadjointOrbitBridge
