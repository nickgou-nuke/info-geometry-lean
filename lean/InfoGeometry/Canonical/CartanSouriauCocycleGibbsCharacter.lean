import InfoGeometry.Algebra.CartanSouriauAffineCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open SouriauCoadjoint
open InfoGeometry.Algebra

namespace InfoGeometry.Canonical

variable {G V State : Type*}
variable [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [LinearGroupAction G V]
variable (Θ : AffineCoadjointCocycle G V)

/-- The Souriau cocycle transforms into a multiplicative Gibbs-character cocycle. -/
def cocycleGibbsMultiplier (g : G) (β : V) : ℝ :=
  Real.exp (-(Θ g β))

/-- The fundamental multiplicative law for the twisted character. -/
theorem cocycleGibbsMultiplier_mul (g h : G) (β : V) :
    cocycleGibbsMultiplier Θ (g * h) β =
      cocycleGibbsMultiplier Θ g β * cocycleGibbsMultiplier Θ h ((Ad V g).symm β) := by
  unfold cocycleGibbsMultiplier
  rw [coadjointCocycle_mul G V Θ g h]
  have h_eval : (Θ g + coadjoint (Ad V g) (Θ h)) β =
      Θ g β + coadjoint (Ad V g) (Θ h) β := rfl
  rw [h_eval]
  have h_coad : coadjoint (Ad V g) (Θ h) β = Θ h ((Ad V g).symm β) := rfl
  rw [h_coad]
  rw [neg_add, Real.exp_add]

variable [Fintype State] [Nonempty State] [MulAction G State]
variable (J : AffineMomentMap G V Θ State)

/-- Unnormalized twisted Gibbs character (statistical weight). -/
def twistedGibbsCharacter
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (β : V) (m : State) : ℝ :=
  Real.exp (-(AffineMomentMap.momentMap G V Θ J m β))

/-- The exact hierarchy: additive coadjoint cocycle -> multiplicative thermodynamic cocycle. -/
theorem twistedGibbsCharacter_equivariant (g : G) (β : V) (m : State) :
    twistedGibbsCharacter Θ J β (g • m) =
      cocycleGibbsMultiplier Θ g β * twistedGibbsCharacter Θ J ((Ad V g).symm β) m := by
  unfold twistedGibbsCharacter cocycleGibbsMultiplier
  rw [AffineMomentMap.momentMap_affine_equivariant G V Θ J g m]
  unfold affineCoadjointAction
  have h_eval :
      (coadjoint (Ad V g) (AffineMomentMap.momentMap G V Θ J m) + Θ g) β =
      coadjoint (Ad V g) (AffineMomentMap.momentMap G V Θ J m) β + Θ g β := rfl
  rw [h_eval]
  have h_coad :
      coadjoint (Ad V g) (AffineMomentMap.momentMap G V Θ J m) β =
      AffineMomentMap.momentMap G V Θ J m ((Ad V g).symm β) := rfl
  rw [h_coad]
  rw [neg_add, Real.exp_add, mul_comm]

def twistedGibbsPartition
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (β : V) : ℝ :=
  ∑ m : State, twistedGibbsCharacter Θ J β m

theorem twistedGibbsPartition_pos (β : V) : 0 < twistedGibbsPartition Θ J β := by
  unfold twistedGibbsPartition
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

theorem twistedGibbsPartition_transformation (g : G) (β : V) :
    twistedGibbsPartition Θ J β =
      cocycleGibbsMultiplier Θ g β * twistedGibbsPartition Θ J ((Ad V g).symm β) := by
  unfold twistedGibbsPartition
  have h_sum : (∑ m : State, twistedGibbsCharacter Θ J β m) =
      ∑ m : State, twistedGibbsCharacter Θ J β (g • m) := by
    exact (Equiv.sum_comp (MulAction.toPerm g) _).symm
  rw [h_sum]
  simp_rw [twistedGibbsCharacter_equivariant Θ J g β]
  rw [Finset.mul_sum]

def twistedMassieu
    (Θ : AffineCoadjointCocycle G V) (J : AffineMomentMap G V Θ State)
    (β : V) : ℝ :=
  Real.log (twistedGibbsPartition Θ J β)

/-- The Massieu potential naturally linearizes the multiplicative cocycle. -/
theorem twistedMassieu_additive_cocycle (g : G) (β : V) :
    twistedMassieu Θ J β = twistedMassieu Θ J ((Ad V g).symm β) - Θ g β := by
  unfold twistedMassieu
  rw [twistedGibbsPartition_transformation Θ J g β]
  have h_pos1 : 0 < cocycleGibbsMultiplier Θ g β := Real.exp_pos _
  have h_pos2 : 0 < twistedGibbsPartition Θ J ((Ad V g).symm β) := twistedGibbsPartition_pos Θ J _
  rw [Real.log_mul (ne_of_gt h_pos1) (ne_of_gt h_pos2)]
  unfold cocycleGibbsMultiplier
  rw [Real.log_exp]
  ring

end InfoGeometry.Canonical
