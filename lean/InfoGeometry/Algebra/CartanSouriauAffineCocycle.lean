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

def coadjointEquiv (g : G) : LieDual V ≃+ LieDual V where
  toFun := coadjoint (Ad V g)
  invFun := coadjoint (Ad V g⁻¹)
  map_add' := by
    intro μ ν
    unfold coadjoint
    ext x
    simp
  left_inv := by
    intro μ
    have h_ad : Ad V (g⁻¹ * g) = Ad V g⁻¹ * Ad V g :=
      MonoidHom.map_mul (LinearGroupAction.action (G := G) (V := V)) g⁻¹ g
    have h_coad : coadjoint (Ad V g⁻¹ * Ad V g) μ = coadjoint (Ad V g⁻¹) (coadjoint (Ad V g) μ) := rfl
    have inv_g : g⁻¹ * g = 1 := inv_mul_cancel g
    rw [← h_coad, ← h_ad, inv_g]
    have h_ad_one : Ad V (1 : G) = 1 := MonoidHom.map_one (LinearGroupAction.action (G := G) (V := V))
    rw [h_ad_one]
    rfl
  right_inv := by
    intro μ
    have h_ad : Ad V (g * g⁻¹) = Ad V g * Ad V g⁻¹ :=
      MonoidHom.map_mul (LinearGroupAction.action (G := G) (V := V)) g g⁻¹
    have h_coad : coadjoint (Ad V g * Ad V g⁻¹) μ = coadjoint (Ad V g) (coadjoint (Ad V g⁻¹) μ) := rfl
    have mul_inv : g * g⁻¹ = 1 := mul_inv_cancel g
    rw [← h_coad, ← h_ad, mul_inv]
    have h_ad_one : Ad V (1 : G) = 1 := MonoidHom.map_one (LinearGroupAction.action (G := G) (V := V))
    rw [h_ad_one]
    rfl

def affineCoadjointEquiv (g : G) : LieDual V ≃ LieDual V where
  toFun := affineCoadjointAction G V Θ g
  invFun := affineCoadjointAction G V Θ g⁻¹
  left_inv := by
    intro μ
    rw [← affineCoadjointAction_mul G V Θ, inv_mul_cancel, affineCoadjointAction_one]
  right_inv := by
    intro μ
    rw [← affineCoadjointAction_mul G V Θ, mul_inv_cancel, affineCoadjointAction_one]

theorem affineCoadjointAction_sub (g : G) (μ ν : LieDual V) :
    affineCoadjointAction G V Θ g μ - affineCoadjointAction G V Θ g ν =
      coadjoint (Ad V g) (μ - ν) := by
  unfold affineCoadjointAction
  have h_add : ∀ A B C : LieDual V, (A + C) - (B + C) = A - B := by intro A B C; abel
  rw [h_add]
  unfold coadjoint
  ext x
  simp

theorem AffineMomentMap.momentMap_eq_affineCoadjointAction
    {State : Type*} [MulAction G State] (A : AffineMomentMap G V Θ State) (g : G) (x : State) :
    A.momentMap (g • x) = affineCoadjointAction G V Θ g (A.momentMap x) :=
  A.momentMap_affine_equivariant g x

end InfoGeometry.Algebra
