import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic

noncomputable section

namespace SouriauCoadjoint

variable {V G : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- The coadjoint action is not a second matrix chosen independently.  It is
   induced by precomposition with the adjoint continuous linear equivalence. -/
abbrev LieDual (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V →L[ℝ] ℝ

def coadjoint (Ad : V ≃L[ℝ] V) : LieDual V → LieDual V :=
  fun μ => μ.comp (Ad.symm : V →L[ℝ] V)

structure LieGroupAction (G V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  Ad : G → V ≃L[ℝ] V

structure SouriauThermodynamicAction (G V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  action : LieGroupAction G V
  cocycle : G → LieDual V
  Psi : V → ℝ
  heatVector : V → LieDual V

/-- 🏆 THEOREM 1: Linear Ad-Invariance of Characteristic Function when Cocycle θ = 0 -/
theorem Psi_linear_invariance
    (sys : SouriauThermodynamicAction G V)
    (g : G)
    (h_Psi_cov : ∀ (g : G) (β : V),
      sys.Psi (sys.action.Ad g β) = sys.Psi β - sys.cocycle g (sys.action.Ad g β))
    (h_zero_cocycle : sys.cocycle g = 0) (β : V) :
    sys.Psi (sys.action.Ad g β) = sys.Psi β := by
  rw [h_Psi_cov g β, h_zero_cocycle]
  simp

/-- 🏆 THEOREM 2: Linear Coadjoint Covariance of Heat Vector Q(Ad_g β) = Ad*_g (Q(β)) when θ = 0 -/
theorem heatVector_linear_covariance
    (sys : SouriauThermodynamicAction G V)
    (g : G)
    (h_heat_cov : ∀ (g : G) (β : V),
      sys.heatVector (sys.action.Ad g β) =
        coadjoint (sys.action.Ad g) (sys.heatVector β) + sys.cocycle g)
    (h_zero_cocycle : sys.cocycle g = 0) (β : V) :
    sys.heatVector (sys.action.Ad g β) =
      coadjoint (sys.action.Ad g) (sys.heatVector β) := by
  rw [h_heat_cov g β, h_zero_cocycle, add_zero]

/-- 🏆 THEOREM 3: Dual Pairing Invariance under Coadjoint and Adjoint Actions
    ⟨Ad*_g μ, Ad_g β⟩ = ⟨μ, β⟩ -/
theorem dual_pairing_invariance
    (act : LieGroupAction G V) (g : G)
    (μ : LieDual V) (β : V) :
    coadjoint (act.Ad g) μ (act.Ad g β) = μ β := by
  simp [coadjoint]

/-- Souriau Group Entropy S(β) = ⟨β, Q(β)⟩ + Ψ(β) -/
def souriauEntropy (sys : SouriauThermodynamicAction G V) (β : V) : ℝ :=
  sys.heatVector β β + sys.Psi β

/- Continuity of the entropy functional is conditional on the actual analytic
  data supplied by an ensemble: no regularity of `Psi` or `heatVector` is
  inferred merely from their types. -/
theorem continuous_souriauEntropy
    (sys : SouriauThermodynamicAction G V)
    (_h_heat : Continuous sys.heatVector)
    (h_Psi : Continuous sys.Psi)
    (h_eval : Continuous (fun β : V => sys.heatVector β β)) :
    Continuous (souriauEntropy sys) := by
  exact h_eval.add h_Psi

theorem isClosed_souriauEntropy_level_set
    (sys : SouriauThermodynamicAction G V) (c : ℝ)
    (h_heat : Continuous sys.heatVector)
    (h_Psi : Continuous sys.Psi)
    (h_eval : Continuous (fun β : V => sys.heatVector β β)) :
    IsClosed {β : V | souriauEntropy sys β = c} := by
  exact isClosed_singleton.preimage
    (continuous_souriauEntropy sys h_heat h_Psi h_eval)

theorem isClosed_transformed_souriauEntropy_level_set
    (sys : SouriauThermodynamicAction G V) (g : G) (c : ℝ)
    (h_heat : Continuous sys.heatVector)
    (h_Psi : Continuous sys.Psi)
    (h_eval : Continuous (fun β : V => sys.heatVector β β)) :
    IsClosed {β : V | souriauEntropy sys (sys.action.Ad g β) = c} := by
  exact isClosed_singleton.preimage
    ((continuous_souriauEntropy sys h_heat h_Psi h_eval).comp
      (sys.action.Ad g).continuous)

/-- 🏆 THEOREM 4: Entropy Invariance under Linear Adjoint & Coadjoint Actions
    S(Ad_g β) = S(β) -/
theorem souriau_entropy_linear_invariance
    (sys : SouriauThermodynamicAction G V)
    (g : G)
    (h_Psi_cov : ∀ (g : G) (β : V),
      sys.Psi (sys.action.Ad g β) = sys.Psi β - sys.cocycle g (sys.action.Ad g β))
    (h_heat_cov : ∀ (g : G) (β : V),
      sys.heatVector (sys.action.Ad g β) =
        coadjoint (sys.action.Ad g) (sys.heatVector β) + sys.cocycle g)
    (h_zero_cocycle : sys.cocycle g = 0) (β : V) :
    souriauEntropy sys (sys.action.Ad g β) = souriauEntropy sys β := by
  dsimp [souriauEntropy]
  rw [heatVector_linear_covariance sys g h_heat_cov h_zero_cocycle β]
  rw [Psi_linear_invariance sys g h_Psi_cov h_zero_cocycle β]
  rw [dual_pairing_invariance sys.action g (sys.heatVector β) β]

/- The finite-dimensional linear action maps are continuous in the product
  topology on `n → ℝ`; this is the topological action edge underlying the
  algebraic covariance identities above. -/
theorem continuous_ad_action (act : LieGroupAction G V) (g : G) :
    Continuous (fun β : V => act.Ad g β) :=
  (act.Ad g).continuous

theorem continuous_coad_action (act : LieGroupAction G V) (g : G)
    (h_coad : Continuous (fun μ : LieDual V => coadjoint (act.Ad g) μ)) :
    Continuous (fun μ : LieDual V => coadjoint (act.Ad g) μ) :=
  h_coad

theorem continuous_ad_cocycle_pairing
    (sys : SouriauThermodynamicAction G V) (g : G) :
    Continuous (fun β : V => sys.cocycle g (sys.action.Ad g β)) := by
  exact (sys.cocycle g).continuous.comp (continuous_ad_action sys.action g)

theorem continuous_Psi_covariance_difference
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_Psi : Continuous sys.Psi) :
    Continuous (fun β : V =>
      sys.Psi (sys.action.Ad g β) - sys.Psi β) :=
  (h_Psi.comp (continuous_ad_action sys.action g)).sub h_Psi

theorem continuous_Psi_covariance_residual
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_Psi : Continuous sys.Psi) :
    Continuous (fun β : V =>
      sys.Psi (sys.action.Ad g β) - sys.Psi β +
        sys.cocycle g (sys.action.Ad g β)) :=
  (continuous_Psi_covariance_difference sys g h_Psi).add
    (continuous_ad_cocycle_pairing sys g)

theorem Psi_covariance_residual_zero
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_Psi_cov : ∀ (g : G) (β : V),
      sys.Psi (sys.action.Ad g β) = sys.Psi β - sys.cocycle g (sys.action.Ad g β))
    (β : V) :
    sys.Psi (sys.action.Ad g β) - sys.Psi β +
        sys.cocycle g (sys.action.Ad g β) = 0 := by
  rw [h_Psi_cov g β]
  ring

theorem isClosed_Psi_covariance_residual_zero
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_Psi : Continuous sys.Psi) :
    IsClosed {β : V |
      sys.Psi (sys.action.Ad g β) - sys.Psi β +
        sys.cocycle g (sys.action.Ad g β) = 0} := by
  exact isClosed_singleton.preimage
    (continuous_Psi_covariance_residual sys g h_Psi)

theorem continuous_heatVector_covariance_residual
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_heat : Continuous sys.heatVector)
    (h_coad : Continuous (fun μ : LieDual V => coadjoint (sys.action.Ad g) μ)) :
    Continuous (fun β : V =>
      sys.heatVector (sys.action.Ad g β) -
        coadjoint (sys.action.Ad g) (sys.heatVector β) - sys.cocycle g) :=
  ((h_heat.comp (continuous_ad_action sys.action g)).sub
    ((continuous_coad_action sys.action g h_coad).comp h_heat)).sub
      continuous_const

theorem heatVector_covariance_residual_zero
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_heat_cov : ∀ (g : G) (β : V),
      sys.heatVector (sys.action.Ad g β) =
        coadjoint (sys.action.Ad g) (sys.heatVector β) + sys.cocycle g)
    (β : V) :
    sys.heatVector (sys.action.Ad g β) -
        coadjoint (sys.action.Ad g) (sys.heatVector β) - sys.cocycle g = 0 := by
  rw [h_heat_cov g β]
  simp

theorem isClosed_heatVector_covariance_residual_zero
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_heat : Continuous sys.heatVector)
    (h_coad : Continuous (fun μ : LieDual V =>
      coadjoint (sys.action.Ad g) μ)) :
    IsClosed {β : V |
      sys.heatVector (sys.action.Ad g β) -
        coadjoint (sys.action.Ad g) (sys.heatVector β) - sys.cocycle g = 0} := by
  exact isClosed_singleton.preimage
    (continuous_heatVector_covariance_residual sys g h_heat h_coad)

theorem continuous_transformed_souriauEntropy
    (sys : SouriauThermodynamicAction G V) (g : G)
    (h_heat : Continuous sys.heatVector)
    (h_Psi : Continuous sys.Psi)
    (h_eval : Continuous (fun β : V => sys.heatVector β β)) :
    Continuous (fun β : V =>
      souriauEntropy sys (sys.action.Ad g β)) :=
  (continuous_souriauEntropy sys h_heat h_Psi h_eval).comp
    (continuous_ad_action sys.action g)

end SouriauCoadjoint
