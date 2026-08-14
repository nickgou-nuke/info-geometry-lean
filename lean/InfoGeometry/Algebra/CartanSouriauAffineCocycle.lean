import InfoGeometry.Canonical.SouriauCoadjointCovariance
import Mathlib.Algebra.Group.Equiv.Basic

noncomputable section
open SouriauCoadjoint

namespace InfoGeometry.Algebra

variable (G V : Type*) [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A linear group action of G on V by continuous linear equivalences. -/
class LinearGroupAction where
  action : G →* (V ≃L[ℝ] V)

variable [LinearGroupAction G V]

def Ad (V : Type*) {G} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearGroupAction G V] (g : G) : V ≃L[ℝ] V :=
  LinearGroupAction.action g

/-- An affine coadjoint cocycle (Souriau cocycle) for the group action. -/
structure AffineCoadjointCocycle where
  toFun : G → LieDual V
  cocycle_mul' : ∀ g h : G, toFun (g * h) = toFun g + coadjoint (Ad V g) (toFun h)

instance : CoeFun (AffineCoadjointCocycle G V) (fun _ => G → LieDual V) :=
  ⟨AffineCoadjointCocycle.toFun⟩

variable (Θ : AffineCoadjointCocycle G V)

theorem coadjointCocycle_mul (g h : G) :
    Θ (g * h) = Θ g + coadjoint (Ad V g) (Θ h) :=
  Θ.cocycle_mul' g h

theorem coadjointCocycle_one : Θ (1 : G) = 0 := by
  have h := coadjointCocycle_mul G V Θ 1 1
  rw [mul_one] at h
  have h_ad_one : Ad V (1 : G) = 1 := MonoidHom.map_one (LinearGroupAction.action (G := G) (V := V))
  have h_coad_one : coadjoint (Ad V (1 : G)) (Θ 1) = Θ 1 := by
    rw [h_ad_one]
    rfl
  rw [h_coad_one] at h
  have h2 : Θ 1 + Θ 1 = Θ 1 + 0 := by
    calc Θ 1 + Θ 1 = Θ 1 := h.symm
      _ = Θ 1 + 0 := (add_zero _).symm
  exact add_left_cancel h2

/-- The affine coadjoint action of G on the dual space. -/
def affineCoadjointAction (g : G) (μ : LieDual V) : LieDual V :=
  coadjoint (Ad V g) μ + Θ g

theorem affineCoadjointAction_one (μ : LieDual V) :
    affineCoadjointAction G V Θ 1 μ = μ := by
  unfold affineCoadjointAction
  rw [coadjointCocycle_one G V Θ]
  have h_ad_one : Ad V (1 : G) = 1 := MonoidHom.map_one (LinearGroupAction.action (G := G) (V := V))
  have h_coad_one : coadjoint (Ad V (1 : G)) μ = μ := by
    rw [h_ad_one]
    rfl
  rw [h_coad_one, add_zero]

theorem affineCoadjointAction_mul (g h : G) (μ : LieDual V) :
    affineCoadjointAction G V Θ (g * h) μ =
      affineCoadjointAction G V Θ g (affineCoadjointAction G V Θ h μ) := by
  unfold affineCoadjointAction
  rw [coadjointCocycle_mul G V Θ g h]
  have h_ad_mul : Ad V (g * h) = Ad V g * Ad V h :=
    MonoidHom.map_mul (LinearGroupAction.action (G := G) (V := V)) g h
  have h_coad_mul : coadjoint (Ad V (g * h)) μ =
      coadjoint (Ad V g) (coadjoint (Ad V h) μ) := by
    rw [h_ad_mul]
    rfl
  rw [h_coad_mul]
  have h_lin : coadjoint (Ad V g) (coadjoint (Ad V h) μ + Θ h) =
      coadjoint (Ad V g) (coadjoint (Ad V h) μ) +
      coadjoint (Ad V g) (Θ h) := by
    rfl
  rw [h_lin]
  abel

/-- An affine equivariant moment map. -/
structure AffineMomentMap (State : Type*) [MulAction G State] where
  momentMap : State → LieDual V
  momentMap_affine_equivariant : ∀ (g : G) (m : State),
    momentMap (g • m) = affineCoadjointAction G V Θ g (momentMap m)

end InfoGeometry.Algebra
