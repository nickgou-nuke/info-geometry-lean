import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.Noncommutative

variable {A : Type*} [Ring A]

def adK (K X : A) : A := K * X - X * K

@[simp] theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

theorem adK_add (K X Y : A) :
    adK K (X + Y) = adK K X + adK K Y := by
  dsimp [adK]
  simp only [mul_add, add_mul]
  abel

theorem adK_mul (K X Y : A) :
    adK K (X * Y) = adK K X * Y + X * adK K Y := by
  dsimp [adK]
  simp only [mul_assoc, sub_mul, mul_sub]
  abel

@[simp] theorem adK_one (K : A) : adK K 1 = 0 := by simp [adK]

def IsDerivation (D : A →ₗ[ℤ] A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

structure NCDerivation (A : Type*) [Ring A] where
  toLinearMap : A →ₗ[ℤ] A
  leibniz' : IsDerivation toLinearMap

instance : CoeFun (NCDerivation A) (fun _ => A → A) where
  coe D := D.toLinearMap

theorem NCDerivation.leibniz (D : NCDerivation A) (x y : A) :
    D (x * y) = D x * y + x * D y := D.leibniz' x y

theorem derivation_one (D : A →ₗ[ℤ] A) (hD : IsDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  have h' : D 1 = D 1 + D 1 := by simpa only [mul_one, one_mul] using h
  have h'' : D 1 + 0 = D 1 + D 1 := by simpa using h'
  exact (add_left_cancel h'').symm

@[simp] theorem NCDerivation.map_one (D : NCDerivation A) : D 1 = 0 :=
  derivation_one D.toLinearMap D.leibniz'

@[ext] theorem NCDerivation.ext {D E : NCDerivation A}
    (h : ∀ X, D X = E X) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      have hDE : D = E := by
        ext X
        exact h X
      cases hDE
      rfl

def adKLinear (K : A) : A →ₗ[ℤ] A where
  toFun X := adK K X
  map_add' X Y := adK_add K X Y
  map_smul' n X := by
    change K * (n • X) - (n • X) * K = n • (K * X - X * K)
    have hL : K * (n • X) = n • (K * X) :=
      (AddMonoidHom.mulLeft K).map_zsmul X n
    have hR : (n • X) * K = n • (X * K) :=
      (AddMonoidHom.mulRight K).map_zsmul X n
    rw [hL, hR, smul_sub]

def innerNCDerivation (K : A) : NCDerivation A where
  toLinearMap := adKLinear K
  leibniz' := adK_mul K

def ncDerivationCommutator (D E : NCDerivation A) : NCDerivation A where
  toLinearMap :=
    { toFun := fun X => D (E X) - E (D X)
      map_add' := by
        intro X Y
        simp only [map_add]
        abel
      map_smul' := by
        intro n X
        simp only [map_smul, RingHom.id_apply]
        simp [smul_sub] }
  leibniz' := by
    intro X Y
    change D (E (X * Y)) - E (D (X * Y)) =
      (D (E X) - E (D X)) * Y + X * (D (E Y) - E (D Y))
    rw [E.leibniz, D.leibniz, D.toLinearMap.map_add,
      E.toLinearMap.map_add, D.leibniz, D.leibniz,
      E.leibniz, E.leibniz]
    simp only [sub_mul, mul_sub]
    abel

theorem ncDerivationCommutator_apply (D E : NCDerivation A) (X : A) :
    ncDerivationCommutator D E X = D (E X) - E (D X) := rfl

theorem ncDerivationCommutator_skew (D E : NCDerivation A) (X : A) :
    ncDerivationCommutator D E X = -ncDerivationCommutator E D X := by
  simp only [ncDerivationCommutator_apply]
  abel

@[simp] theorem ncDerivationCommutator_self (D : NCDerivation A) (X : A) :
    ncDerivationCommutator D D X = 0 := by
  simp only [ncDerivationCommutator_apply]
  abel

theorem ncDerivationCommutator_jacobi
    (D E F : NCDerivation A) (X : A) :
    ncDerivationCommutator D (ncDerivationCommutator E F) X +
        ncDerivationCommutator E (ncDerivationCommutator F D) X +
        ncDerivationCommutator F (ncDerivationCommutator D E) X = 0 := by
  simp only [ncDerivationCommutator_apply, map_sub]
  abel

theorem ncDerivationCommutator_inner_apply
    (D : NCDerivation A) (K X : A) :
    ncDerivationCommutator D (innerNCDerivation K) X =
      innerNCDerivation (D K) X := by
  change D (adK K X) - adK K (D X) = adK (D K) X
  dsimp [adK]
  rw [D.toLinearMap.map_sub, D.leibniz, D.leibniz]
  abel

theorem ncDerivationCommutator_inner
    (D : NCDerivation A) (K : A) :
    ncDerivationCommutator D (innerNCDerivation K) =
      innerNCDerivation (D K) := by
  apply NCDerivation.ext
  intro X
  exact ncDerivationCommutator_inner_apply D K X

theorem innerNCDerivation_bracket (K₁ K₂ : A) :
    ncDerivationCommutator (innerNCDerivation K₁) (innerNCDerivation K₂) =
      innerNCDerivation (adK K₁ K₂) := by
  apply NCDerivation.ext
  intro X
  exact ncDerivationCommutator_inner_apply (innerNCDerivation K₁) K₂ X

/- The bundled inner derivation has zero action exactly on central elements. -/
instance : Zero (NCDerivation A) where
  zero :=
    { toLinearMap := 0
      leibniz' := by
        intro X Y
        simp }

theorem innerNCDerivation_eq_zero_iff (K : A) :
    innerNCDerivation K = 0 ↔ ∀ X : A, K * X = X * K := by
  constructor
  · intro h X
    have hX : innerNCDerivation K X = (0 : NCDerivation A) X :=
      congrArg (fun E : NCDerivation A => E X) h
    change K * X - X * K = 0 at hX
    exact sub_eq_zero.mp hX
  · intro h
    apply NCDerivation.ext
    intro X
    change K * X - X * K = 0
    rw [h X]
    simp

theorem innerNCDerivation_commutes_iff (K₁ K₂ : A) :
    ncDerivationCommutator (innerNCDerivation K₁) (innerNCDerivation K₂) = 0 ↔
      ∀ X : A, adK K₁ K₂ * X = X * adK K₁ K₂ := by
  rw [innerNCDerivation_bracket, innerNCDerivation_eq_zero_iff]

def dlog (D : A →ₗ[ℤ] A) (u : Aˣ) : A :=
  (↑(u⁻¹) : A) * D (u : A)

theorem dlog_eq_zero_of_fixed (D : A →ₗ[ℤ] A) (u : Aˣ)
    (h : D (u : A) = 0) : dlog D u = 0 := by simp [dlog, h]

@[simp] theorem dlog_one (D : A →ₗ[ℤ] A) (hD : IsDerivation D) :
    dlog D 1 = 0 := by simp [dlog, derivation_one D hD]

theorem dlog_mul (D : A →ₗ[ℤ] A) (hD : IsDerivation D) (u v : Aˣ) :
    dlog D (u * v) =
      (↑(v⁻¹) : A) * dlog D u * (v : A) + dlog D v := by
  unfold dlog
  have hprod : D ((u : A) * (v : A)) =
      D (u : A) * (v : A) + (u : A) * D (v : A) := hD _ _
  change (↑((u * v)⁻¹) : A) * D ((u : A) * (v : A)) = _
  rw [hprod, mul_inv_rev]
  change ((↑(v⁻¹) : A) * (↑(u⁻¹) : A)) *
      (D (u : A) * (v : A) + (u : A) * D (v : A)) = _
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  simp only [mul_add, mul_assoc]
  have hterm : (↑(v⁻¹) : A) * ((↑(u⁻¹) : A) *
      ((u : A) * D (v : A))) = (↑(v⁻¹) : A) * D (v : A) := by
    calc
      _ = (↑(v⁻¹) : A) * (((↑(u⁻¹) : A) * (u : A)) * D (v : A)) := by
        rw [mul_assoc]
      _ = _ := by rw [hu, one_mul]
  rw [hterm]

/- The three-factor form records the noncommutative cocycle coherence: the
   contribution from the first factor is transported through both later
   factors, in their order. -/
theorem dlog_mul_three (D : A →ₗ[ℤ] A) (hD : IsDerivation D)
    (u v w : Aˣ) :
    dlog D (u * v * w) =
      (↑(w⁻¹) : A) * (↑(v⁻¹) : A) * dlog D u * (v : A) * (w : A) +
        (↑(w⁻¹) : A) * dlog D v * (w : A) + dlog D w := by
  rw [dlog_mul D hD (u * v) w, dlog_mul D hD u v]
  simp only [mul_assoc, add_mul, mul_add]

theorem dlog_mul_of_central_right (D : A →ₗ[ℤ] A)
    (hD : IsDerivation D) (u v : Aˣ)
    (hv : ∀ x : A, (v : A) * x = x * (v : A)) :
    dlog D (u * v) = dlog D u + dlog D v := by
  rw [dlog_mul D hD u v]
  have hconj : (↑(v⁻¹) : A) * dlog D u * (v : A) = dlog D u := by
    calc
      (↑(v⁻¹) : A) * dlog D u * (v : A)
          = (↑(v⁻¹) : A) * (dlog D u * (v : A)) := by
            exact mul_assoc _ _ _
      _ = (↑(v⁻¹) : A) * ((v : A) * dlog D u) := by rw [hv]
      _ = ((↑(v⁻¹) : A) * (v : A)) * dlog D u := by rw [mul_assoc]
      _ = 1 * dlog D u := by
        have hvunit : (↑(v⁻¹) : A) * (v : A) = 1 := v.inv_val
        rw [hvunit]
      _ = dlog D u := by rw [one_mul]
  rw [hconj]

theorem dlog_mul_of_commute_right (D : A →ₗ[ℤ] A)
    (hD : IsDerivation D) (u v : Aˣ)
    (hcomm : Commute (dlog D u) (v : A)) :
    dlog D (u * v) = dlog D u + dlog D v := by
  rw [dlog_mul D hD u v]
  have hconj : (↑(v⁻¹) : A) * dlog D u * (v : A) = dlog D u := by
    calc
      (↑(v⁻¹) : A) * dlog D u * (v : A) =
          (↑(v⁻¹) : A) * (dlog D u * (v : A)) := by
        rw [mul_assoc]
      _ = (↑(v⁻¹) : A) * ((v : A) * dlog D u) := by
        rw [hcomm.eq]
      _ = ((↑(v⁻¹) : A) * (v : A)) * dlog D u := by
        rw [mul_assoc]
      _ = dlog D u := by simp
  rw [hconj]

theorem dlog_inv (D : A →ₗ[ℤ] A) (hD : IsDerivation D) (u : Aˣ) :
    dlog D (u⁻¹) = -((u : A) * dlog D u * (↑(u⁻¹) : A)) := by
  unfold dlog
  have hone : D (1 : A) = 0 := derivation_one D hD
  have hprod : D ((u : A) * (↑(u⁻¹) : A)) =
      D (u : A) * (↑(u⁻¹) : A) + (u : A) * D (↑(u⁻¹) : A) := hD _ _
  have hunit : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  rw [hunit, hone] at hprod
  have hinv : (u : A) * D (↑(u⁻¹) : A) =
      -(D (u : A) * (↑(u⁻¹) : A)) := eq_neg_of_add_eq_zero_right hprod.symm
  calc
    (↑((u⁻¹)⁻¹) : A) * D (↑(u⁻¹) : A) =
        (u : A) * D (↑(u⁻¹) : A) := by simp
    _ = _ := hinv
    _ = -((u : A) * ((↑(u⁻¹) : A) * D (u : A)) *
        (↑(u⁻¹) : A)) := by
      have hrewrite : (u : A) * ((↑(u⁻¹) : A) * D (u : A)) *
          (↑(u⁻¹) : A) = D (u : A) * (↑(u⁻¹) : A) := by
        rw [← mul_assoc, hunit, one_mul]
      exact congrArg Neg.neg hrewrite.symm

def NCDerivation.dlog (D : NCDerivation A) (u : Aˣ) : A :=
  InfoGeometry.Modular.Noncommutative.dlog D.toLinearMap u

theorem NCDerivation.dlog_mul (D : NCDerivation A) (u v : Aˣ) :
    D.dlog (u * v) = (↑(v⁻¹) : A) * D.dlog u * (v : A) + D.dlog v :=
  InfoGeometry.Modular.Noncommutative.dlog_mul D.toLinearMap D.leibniz' u v

theorem NCDerivation.dlog_inv (D : NCDerivation A) (u : Aˣ) :
    D.dlog (u⁻¹) = -((u : A) * D.dlog u * (↑(u⁻¹) : A)) :=
  InfoGeometry.Modular.Noncommutative.dlog_inv D.toLinearMap D.leibniz' u

/- The logarithmic derivative of an inner derivation is a unit conjugate
   difference. -/
theorem innerNCDerivation_dlog (K : A) (u : Aˣ) :
    (innerNCDerivation K).dlog u =
      (↑(u⁻¹) : A) * K * (u : A) - K := by
  unfold NCDerivation.dlog dlog
  change (↑(u⁻¹) : A) * (K * (u : A) - (u : A) * K) =
    (↑(u⁻¹) : A) * K * (u : A) - K
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  calc
    (↑(u⁻¹) : A) * (K * (u : A) - (u : A) * K) =
        (↑(u⁻¹) : A) * K * (u : A) -
          (↑(u⁻¹) : A) * ((u : A) * K) := by
      rw [mul_sub, mul_assoc]
    _ = (↑(u⁻¹) : A) * K * (u : A) - K := by
      rw [← mul_assoc (a := (↑(u⁻¹) : A)) (b := (u : A)), hu, one_mul]

theorem innerNCDerivation_dlog_eq_zero_iff (K : A) (u : Aˣ) :
    (innerNCDerivation K).dlog u = 0 ↔ Commute K (u : A) := by
  constructor
  · intro h
    have h' : (↑(u⁻¹) : A) * K * (u : A) = K := by
      exact sub_eq_zero.mp (by simpa [innerNCDerivation_dlog K u] using h)
    have h'' := congrArg (fun z : A => (u : A) * z) h'
    simp only [mul_assoc] at h''
    have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
    rw [← mul_assoc (a := (u : A)) (b := (↑(u⁻¹) : A)), hu,
      one_mul] at h''
    change K * (u : A) = (u : A) * K
    exact h''
  · intro h
    rw [innerNCDerivation_dlog K u]
    have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
    rw [mul_assoc, h.eq, ← mul_assoc, hu, one_mul, sub_self]

/- Algebraic modular conjugation by a unit. -/
def innerConjugation (u : Aˣ) (X : A) : A :=
  (u : A) * X * (↑(u⁻¹) : A)

/-- The logarithmic derivative of an inner derivation is the displacement
    between a generator and its inverse-unit conjugate.  This is the
    noncommutative form of the modular cocycle increment. -/
theorem innerNCDerivation_dlog_eq_innerConjugation_inverse_sub
    (K : A) (u : Aˣ) :
    (innerNCDerivation K).dlog u = innerConjugation (u⁻¹) K - K := by
  simpa [innerConjugation] using innerNCDerivation_dlog K u

theorem innerNCDerivation_dlog_eq_zero_iff_conjugation_fixed
    (K : A) (u : Aˣ) :
    (innerNCDerivation K).dlog u = 0 ↔
      innerConjugation (u⁻¹) K = K := by
  rw [innerNCDerivation_dlog_eq_innerConjugation_inverse_sub]
  exact sub_eq_zero

theorem innerConjugation_one (u : Aˣ) : innerConjugation u (1 : A) = 1 := by
  simp [innerConjugation]

theorem innerConjugation_mul (u : Aˣ) (X Y : A) :
    innerConjugation u (X * Y) =
      innerConjugation u X * innerConjugation u Y := by
  unfold innerConjugation
  simp only [mul_assoc]
  rw [← mul_assoc (a := (↑(u⁻¹) : A)) (b := (u : A))]
  have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  rw [hu, one_mul]

theorem innerConjugation_add (u : Aˣ) (X Y : A) :
    innerConjugation u (X + Y) =
      innerConjugation u X + innerConjugation u Y := by
  simp only [innerConjugation, add_mul, mul_add]

theorem innerConjugation_sub (u : Aˣ) (X Y : A) :
    innerConjugation u (X - Y) =
      innerConjugation u X - innerConjugation u Y := by
  simp only [innerConjugation, mul_sub, sub_mul]

theorem innerConjugation_adK (u : Aˣ) (K X : A) :
    innerConjugation u (adK K X) =
      adK (innerConjugation u K) (innerConjugation u X) := by
  change innerConjugation u (K * X - X * K) =
    innerConjugation u K * innerConjugation u X -
      innerConjugation u X * innerConjugation u K
  rw [innerConjugation_sub,
    ← innerConjugation_mul u K X,
    ← innerConjugation_mul u X K]

theorem innerConjugation_commutator (u : Aˣ) (X Y : A) :
    innerConjugation u (X * Y - Y * X) =
      innerConjugation u X * innerConjugation u Y -
        innerConjugation u Y * innerConjugation u X := by
  rw [innerConjugation_sub,
    ← innerConjugation_mul u X Y,
    ← innerConjugation_mul u Y X]

theorem innerConjugation_eq_of_central (u : Aˣ) (K : A)
    (hK : ∀ X : A, K * X = X * K) :
    innerConjugation u K = K := by
  unfold innerConjugation
  rw [← hK (u : A), mul_assoc]
  have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
  rw [hu, mul_one]

theorem innerConjugation_comp (u v : Aˣ) (X : A) :
    innerConjugation u (innerConjugation v X) =
      innerConjugation (u * v) X := by
  unfold innerConjugation
  simp only [Units.val_mul, mul_inv_rev, mul_assoc]

theorem innerConjugation_inverse (u : Aˣ) (X : A) :
    innerConjugation (u⁻¹) (innerConjugation u X) = X := by
  calc
    innerConjugation (u⁻¹) (innerConjugation u X) =
        innerConjugation (u⁻¹ * u) X :=
      innerConjugation_comp (u⁻¹) u X
    _ = innerConjugation 1 X := by rw [inv_mul_cancel]
    _ = X := by simp [innerConjugation]

/-- Unit conjugation, bundled as the native ring automorphism of `A`. -/
def innerConjugationRingEquiv (u : Aˣ) : A ≃+* A :=
  RingEquiv.ofBijective
    ({ toFun := innerConjugation u
       map_one' := innerConjugation_one u
       map_mul' := innerConjugation_mul u
       map_zero' := by simp [innerConjugation]
       map_add' := innerConjugation_add u } : A →+* A)
    (by
      constructor
      · intro X Y h
        have h' := congrArg (innerConjugation (u⁻¹)) h
        simpa [innerConjugation_inverse] using h'
      · intro X
        refine ⟨innerConjugation (u⁻¹) X, ?_⟩
        simpa using innerConjugation_inverse (u⁻¹) X)

@[simp] theorem innerConjugationRingEquiv_apply (u : Aˣ) (X : A) :
    innerConjugationRingEquiv u X = innerConjugation u X := by
  simp [innerConjugationRingEquiv]

theorem innerNCDerivation_dlog_eq_ringEquiv_sub (K : A) (u : Aˣ) :
    (innerNCDerivation K).dlog u =
      innerConjugationRingEquiv (u⁻¹) K - K := by
  simp only [innerConjugationRingEquiv_apply]
  exact innerNCDerivation_dlog_eq_innerConjugation_inverse_sub K u

theorem innerConjugationRingEquiv_commutator (u : Aˣ) (X Y : A) :
    innerConjugationRingEquiv u (X * Y - Y * X) =
      innerConjugationRingEquiv u X * innerConjugationRingEquiv u Y -
        innerConjugationRingEquiv u Y * innerConjugationRingEquiv u X := by
  simp only [innerConjugationRingEquiv_apply]
  exact innerConjugation_commutator u X Y

theorem innerConjugationRingEquiv_mul_apply (u v : Aˣ) (X : A) :
    innerConjugationRingEquiv (u * v) X =
      innerConjugationRingEquiv u (innerConjugationRingEquiv v X) := by
  simp only [innerConjugationRingEquiv_apply]
  exact (innerConjugation_comp u v X).symm

theorem innerConjugationRingEquiv_inv_apply (u : Aˣ) (X : A) :
    innerConjugationRingEquiv (u⁻¹) (innerConjugationRingEquiv u X) = X := by
  simp only [innerConjugationRingEquiv_apply]
  exact innerConjugation_inverse u X

theorem innerConjugationRingEquiv_map_adK (u : Aˣ) (K X : A) :
    innerConjugationRingEquiv u (adK K X) =
      adK (innerConjugationRingEquiv u K)
        (innerConjugationRingEquiv u X) := by
  simp only [innerConjugationRingEquiv_apply]
  exact innerConjugation_adK u K X

theorem innerConjugationRingEquiv_fixed_iff (u : Aˣ) (K : A) :
    innerConjugationRingEquiv u K = K ↔ Commute K (u : A) := by
  constructor
  · intro h
    have h' := congrArg (fun z : A => z * (u : A)) h
    change ((u : A) * K * (↑(u⁻¹) : A)) * (u : A) = K * (u : A) at h'
    have hu : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
    rw [mul_assoc, hu, mul_one] at h'
    change K * (u : A) = (u : A) * K
    exact h'.symm
  · intro h
    simp only [innerConjugationRingEquiv_apply]
    unfold innerConjugation
    have hu : (u : A) * (↑(u⁻¹) : A) = 1 := u.val_inv
    rw [← h.eq, mul_assoc, hu, mul_one]

theorem innerConjugationRingEquiv_fixed_iff_dlog_eq_zero
    (u : Aˣ) (K : A) :
    innerConjugationRingEquiv u K = K ↔
      (innerNCDerivation K).dlog u = 0 := by
  rw [innerConjugationRingEquiv_fixed_iff,
    innerNCDerivation_dlog_eq_zero_iff]

theorem innerConjugation_central_iff (u : Aˣ) (K : A) :
    (∀ X : A, innerConjugation u K * X = X * innerConjugation u K) ↔
      ∀ X : A, K * X = X * K := by
  constructor
  · intro hK X
    have hz : innerConjugation u (adK K X) = 0 := by
      rw [innerConjugation_adK]
      exact sub_eq_zero.mpr (hK (innerConjugation u X))
    have hz' := congrArg (innerConjugation (u⁻¹)) hz
    have hz0 : innerConjugation (u⁻¹) (0 : A) = 0 := by
      simp [innerConjugation]
    rw [innerConjugation_inverse, hz0] at hz'
    exact sub_eq_zero.mp hz'
  · intro hK X
    rw [innerConjugation_eq_of_central u K hK]
    exact hK X

theorem innerConjugationRingEquiv_central_iff (u : Aˣ) (K : A) :
    (∀ X : A, innerConjugationRingEquiv u K * X =
      X * innerConjugationRingEquiv u K) ↔
      ∀ X : A, K * X = X * K := by
  simp only [innerConjugationRingEquiv_apply]
  exact innerConjugation_central_iff u K

end InfoGeometry.Modular.Noncommutative

end noncomputable section
