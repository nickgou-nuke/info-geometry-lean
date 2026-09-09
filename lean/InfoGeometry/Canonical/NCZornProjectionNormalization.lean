import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra

/-!
# Component normal forms for the operator-valued NC-Zorn carrier

This owner exposes only definitional component reductions.  It deliberately
installs no ring, alternative, or nonassociative-ring structure on the carrier.
The lemmas are intended to normalize projections before coefficient algebra
identities are discharged by `noncomm_ring`.
-/

namespace InfoGeometry.Canonical.NCZornProjectionNormalization

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

@[simp] theorem add_sigma_plus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X + Y).sigma_plus i = X.sigma_plus i + Y.sigma_plus i := by
  rfl

@[simp] theorem add_sigma_minus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X + Y).sigma_minus i = X.sigma_minus i + Y.sigma_minus i := by
  rfl

@[simp] theorem neg_sigma_plus_apply (X : NCZornElement A) (i : Fin 3) :
    (-X).sigma_plus i = -X.sigma_plus i := by
  rfl

@[simp] theorem neg_sigma_minus_apply (X : NCZornElement A) (i : Fin 3) :
    (-X).sigma_minus i = -X.sigma_minus i := by
  rfl

@[simp] theorem sub_sigma_plus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X - Y).sigma_plus i = X.sigma_plus i - Y.sigma_plus i := by
  change X.sigma_plus i + -Y.sigma_plus i = _
  simp only [sub_eq_add_neg]

@[simp] theorem sub_sigma_minus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X - Y).sigma_minus i = X.sigma_minus i - Y.sigma_minus i := by
  change X.sigma_minus i + -Y.sigma_minus i = _
  simp only [sub_eq_add_neg]

@[simp] theorem add_add_sub_sigma_plus_apply
    (X Y Z W : NCZornElement A) (i : Fin 3) :
    ((X + Y) + Z - W).sigma_plus i =
      X.sigma_plus i + Y.sigma_plus i + Z.sigma_plus i - W.sigma_plus i := by
  simp only [sub_sigma_plus_apply, add_sigma_plus_apply]

@[simp] theorem add_add_sub_sigma_minus_apply
    (X Y Z W : NCZornElement A) (i : Fin 3) :
    ((X + Y) + Z - W).sigma_minus i =
      X.sigma_minus i + Y.sigma_minus i + Z.sigma_minus i - W.sigma_minus i := by
  simp only [sub_sigma_minus_apply, add_sigma_minus_apply]

@[simp] theorem mul_sigma_plus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X * Y).sigma_plus i =
      X.n_plus * Y.sigma_plus i + X.sigma_plus i * Y.n_minus -
        NCZornElement.zornCross X.sigma_minus Y.sigma_minus i := by
  rfl

@[simp] theorem mul_sigma_minus_apply (X Y : NCZornElement A) (i : Fin 3) :
    (X * Y).sigma_minus i =
      X.n_minus * Y.sigma_minus i + X.sigma_minus i * Y.n_plus +
        NCZornElement.zornCross X.sigma_plus Y.sigma_plus i := by
  rfl

@[simp] theorem mul_n_plus (X Y : NCZornElement A) :
    (X * Y).n_plus = X.n_plus * Y.n_plus +
      NCZornElement.zornDot X.sigma_plus Y.sigma_minus := by
  rfl

@[simp] theorem mul_n_minus (X Y : NCZornElement A) :
    (X * Y).n_minus = X.n_minus * Y.n_minus +
      NCZornElement.zornDot X.sigma_minus Y.sigma_plus := by
  rfl

end InfoGeometry.Canonical.NCZornProjectionNormalization
