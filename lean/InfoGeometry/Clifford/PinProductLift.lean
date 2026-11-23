/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.NoncommRing

/-!
# Pin generator lift across an orthogonal Clifford product

For a negative unit vector `e` in a second orthogonal summand, the operator
`ι(v,0) * ι(0,e)` has the same Clifford square as `v`. This is the
algebraic product assignment that appears in equation (1.10) of Freed,
*Index Theory on Pin Manifolds*. The formalized subgroup is Mathlib's native
unitary `pinGroup`; this file does not identify it with Freed's geometric Pin
groups or assert the paper's group embedding without further hypotheses.

The lift is shown to lie in the even Clifford subalgebra and to preserve the
quadratic value. It also induces a monoid hom from Mathlib's native Pin
submonoid to the target Spin submonoid. Injectivity of that homomorphism and
the induced map on orthogonal groups are not established here.
-/

namespace InfoGeometry.Clifford.PinProductLift

open CliffordAlgebra

variable {R M₁ M₂ : Type*}
variable [CommRing R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]

/-- The product lift of a vector by a fixed vector in an orthogonal summand. -/
def liftVector (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (v : M₁) : CliffordAlgebra (Q₁.prod Q₂) :=
  ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (0, e)

/-- The vector lift is an element of the even Clifford subalgebra.  Thus the
generator-level construction lands in the carrier used for Spin elements,
not merely in the ambient Clifford algebra. -/
def liftVectorEven (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (v : M₁) : CliffordAlgebra.even (Q₁.prod Q₂) :=
  ⟨liftVector Q₁ Q₂ e v, by
    change liftVector Q₁ Q₂ e v ∈ CliffordAlgebra.evenOdd (Q₁.prod Q₂) 0
    exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q₁.prod Q₂) (v, 0) (0, e)⟩

/-- For fixed auxiliary vector `e`, the Pin-to-even-Clifford generator lift
is linear in the vector being lifted. This gives the construction an actual
module-map interface rather than only pointwise square identities. -/
def liftVectorEvenLinear (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) : M₁ →ₗ[R] CliffordAlgebra.even (Q₁.prod Q₂) where
  toFun := liftVectorEven Q₁ Q₂ e
  map_add' v w := by
    apply Subtype.ext
    change ι (Q₁.prod Q₂) (v + w, 0) * ι (Q₁.prod Q₂) (0, e) =
      ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (0, e) +
        ι (Q₁.prod Q₂) (w, 0) * ι (Q₁.prod Q₂) (0, e)
    rw [show (v + w, (0 : M₂)) = (v, 0) + (w, 0) by ext <;> simp,
      map_add, add_mul]
  map_smul' c v := by
    apply Subtype.ext
    change ι (Q₁.prod Q₂) (c • v, 0) * ι (Q₁.prod Q₂) (0, e) =
      c • (ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (0, e))
    rw [show (c • v, (0 : M₂)) = c • (v, 0) by ext <;> simp,
      map_smul, smul_mul_assoc]

/-- If `e` has square `-1`, multiplying a vector from the first orthogonal
summand by `e` preserves its Clifford square. The proof is in the associative
Clifford algebra and uses the noncommuting order of the two orthogonal
generators. -/
theorem liftVector_sq
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v : M₁) :
    liftVector Q₁ Q₂ e v * liftVector Q₁ Q₂ e v =
      algebraMap R (CliffordAlgebra (Q₁.prod Q₂)) (Q₁ v) := by
  let x : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (v, 0)
  let y : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (0, e)
  have hxy : x * y = -y * x := by
    dsimp [x, y]
    simpa [x, y] using (ι_mul_ι_comm_of_isOrtho
      (Q := Q₁.prod Q₂) (QuadraticMap.IsOrtho.inl_inr v e))
  have hx : x * x = algebraMap R _ (Q₁ v) := by
    dsimp [x]
    rw [ι_sq_scalar]
    simp [QuadraticMap.prod_apply]
  have hy : y * y = algebraMap R _ (-1 : R) := by
    dsimp [y]
    rw [ι_sq_scalar]
    simp [QuadraticMap.prod_apply, he]
  have hyx : y * x = -(x * y) := by
    calc
      y * x = -(- (y * x)) := by simp
      _ = -(x * y) := by rw [hxy]; simp
  calc
    (x * y) * (x * y) = -(x * x) * (y * y) := by
      calc
        (x * y) * (x * y) = x * (y * x) * y := by noncomm_ring
        _ = x * (-(x * y)) * y := by rw [hyx]
        _ = -(x * x) * (y * y) := by noncomm_ring
    _ = algebraMap R _ (Q₁ v) := by
      rw [hx, hy]
      simp

/-- The lift preserves ordered products of two generators. The auxiliary
negative unit cancels after the two orthogonal sign swaps, so the induced
Clifford homomorphism preserves the bivector operators of the first factor. -/
theorem liftVector_mul_liftVector
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v w : M₁) :
    liftVector Q₁ Q₂ e v * liftVector Q₁ Q₂ e w =
      ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (w, 0) := by
  let x : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (v, 0)
  let z : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (w, 0)
  let y : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (0, e)
  have hyz : y * z = -z * y := by
    dsimp [y, z]
    simpa [neg_mul] using (ι_mul_ι_comm_of_isOrtho
      (Q := Q₁.prod Q₂)
      (QuadraticMap.IsOrtho.inr_inl (Q₁ := Q₁) (Q₂ := Q₂) w e))
  have hy : y * y = -1 := by
    dsimp [y]
    rw [ι_sq_scalar]
    simp [QuadraticMap.prod_apply, he]
  change (x * y) * (z * y) = x * z
  calc
    (x * y) * (z * y) = x * (y * z) * y := by noncomm_ring
    _ = x * (-(z * y)) * y := by rw [hyz]; simp [neg_mul]
    _ = -(x * z) * (y * y) := by noncomm_ring
    _ = -(x * z) * (-1) := by rw [hy]
    _ = x * z := by noncomm_ring

/-- The even lift acts on vectors in the first orthogonal summand by the same
Clifford sandwich as the original negative-square vector. This is the
generator-level intertwining of the Pin reflection action with the Spin
action after adjoining the orthogonal negative line. -/
theorem liftVector_conj_ι
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v w : M₁) :
    liftVector Q₁ Q₂ e v * ι (Q₁.prod Q₂) (w, 0) *
        star (liftVector Q₁ Q₂ e v) =
      ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (w, 0) *
        ι (Q₁.prod Q₂) (v, 0) := by
  let x : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (v, 0)
  let y : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (0, e)
  let z : CliffordAlgebra (Q₁.prod Q₂) := ι (Q₁.prod Q₂) (w, 0)
  have hyz : y * z = -z * y := by
    dsimp [y, z]
    simpa [neg_mul] using (ι_mul_ι_comm_of_isOrtho
      (Q := Q₁.prod Q₂)
      (QuadraticMap.IsOrtho.inr_inl (Q₁ := Q₁) (Q₂ := Q₂) w e))
  have hy : y * y = -1 := by
    dsimp [y]
    rw [ι_sq_scalar]
    simp [QuadraticMap.prod_apply, he]
  have hstar : star (x * y) = y * x := by
    dsimp [x, y]
    rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
    simp
  change (x * y) * z * star (x * y) = x * z * x
  rw [hstar]
  calc
    (x * y) * z * (y * x) = x * (y * z * y) * x := by noncomm_ring
    _ = x * z * x := by
      have hyzy : y * z * y = z := by
        calc
          y * z * y = -(z * y) * y := by rw [hyz]; noncomm_ring
          _ = -z * (y * y) := by noncomm_ring
          _ = z := by rw [hy]; noncomm_ring
      rw [hyzy]

/-- The product lift obeys the Pin twisted-adjoint sign formula on vectors in
the first orthogonal summand. When `Q₁ v = -1`, Clifford conjugation `star`
is the inverse of the source vector, so the right side is precisely the
standard Pin action; the left side is ordinary conjugation by the even lift. -/
theorem liftVector_intertwines_pin_action
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v w : M₁) :
    liftVector Q₁ Q₂ e v * ι (Q₁.prod Q₂) (w, 0) *
        star (liftVector Q₁ Q₂ e v) =
      -(ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (w, 0) *
        star (ι (Q₁.prod Q₂) (v, 0))) := by
  rw [liftVector_conj_ι Q₁ Q₂ e he v w]
  rw [CliffordAlgebra.star_ι]
  noncomm_ring

/-- The lifted linear map satisfies the defining quadratic relation inside
the even subalgebra itself. -/
theorem liftVectorEvenLinear_sq
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v : M₁) :
    liftVectorEvenLinear Q₁ Q₂ e v * liftVectorEvenLinear Q₁ Q₂ e v =
      algebraMap R (CliffordAlgebra.even (Q₁.prod Q₂)) (Q₁ v) := by
  apply Subtype.ext
  change (liftVectorEven Q₁ Q₂ e v : CliffordAlgebra (Q₁.prod Q₂)) *
    (liftVectorEven Q₁ Q₂ e v : CliffordAlgebra (Q₁.prod Q₂)) = _
  change liftVector Q₁ Q₂ e v * liftVector Q₁ Q₂ e v = _
  exact liftVector_sq Q₁ Q₂ e he v

/-- The generator lift extends, by the Clifford algebra universal property,
to an algebra homomorphism from the first Clifford algebra into the even
subalgebra of the orthogonal product Clifford algebra. -/
noncomputable def liftCliffordEven
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) :
    CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra.even (Q₁.prod Q₂) :=
  CliffordAlgebra.lift Q₁
    ⟨liftVectorEvenLinear Q₁ Q₂ e,
      fun v => by
        change liftVectorEven Q₁ Q₂ e v * liftVectorEven Q₁ Q₂ e v = _
        exact liftVectorEvenLinear_sq Q₁ Q₂ e he v⟩

/-- On Clifford generators, the extended algebra homomorphism is the
even-subalgebra vector lift used to define it. -/
@[simp] theorem liftCliffordEven_ι
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v : M₁) :
    liftCliffordEven Q₁ Q₂ e he (ι Q₁ v) = liftVectorEven Q₁ Q₂ e v := by
  rw [liftCliffordEven, CliffordAlgebra.lift_ι_apply]
  rfl

/-- The same lift, viewed as an algebra homomorphism into the ambient product
Clifford algebra. -/
noncomputable def liftCliffordAmbient
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) :
    CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  (CliffordAlgebra.even (Q₁.prod Q₂)).val.comp
    (liftCliffordEven Q₁ Q₂ e he)

/-- On generators, the ambient homomorphism is exactly multiplication by the
fixed negative unit in the orthogonal summand. -/
@[simp] theorem liftCliffordAmbient_ι
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v : M₁) :
    liftCliffordAmbient Q₁ Q₂ e he (ι Q₁ v) = liftVector Q₁ Q₂ e v := by
  simp [liftCliffordAmbient, liftVectorEven, liftVector, liftCliffordEven_ι]

/-- The ambient algebra homomorphism preserves Clifford conjugation.
This is the structural compatibility needed before its restriction can be
shown to preserve Mathlib's unitary Pin condition.  The generator case uses
the noncommuting orthogonal factors in their prescribed order. -/
theorem liftCliffordAmbient_map_star
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1)
    (x : CliffordAlgebra Q₁) :
    liftCliffordAmbient Q₁ Q₂ e he (star x) =
      star (liftCliffordAmbient Q₁ Q₂ e he x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [liftCliffordAmbient]
  | ι v =>
      rw [CliffordAlgebra.star_ι, map_neg, liftCliffordAmbient_ι]
      change -liftVector Q₁ Q₂ e v = star (liftVector Q₁ Q₂ e v)
      dsimp [liftVector]
      rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
      have hxy :
          ι (Q₁.prod Q₂) (v, 0) * ι (Q₁.prod Q₂) (0, e) =
            -(ι (Q₁.prod Q₂) (0, e) * ι (Q₁.prod Q₂) (v, 0)) := by
        simpa using (ι_mul_ι_comm_of_isOrtho
          (Q := Q₁.prod Q₂) (QuadraticMap.IsOrtho.inl_inr v e))
      simp [hxy]
  | mul x y hx hy =>
      simp only [star_mul, map_mul, hx, hy]
  | add x y hx hy =>
      simp only [star_add, map_add, hx, hy]

/-- The lift sends unitary Clifford elements to unitary elements. This proves
the norm-preservation half of Pin-group preservation; the Lipschitz-group
condition is separate and is not asserted by this theorem. -/
theorem liftCliffordAmbient_mem_unitary
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1)
    {x : CliffordAlgebra Q₁} (hx : x ∈ unitary (CliffordAlgebra Q₁)) :
    liftCliffordAmbient Q₁ Q₂ e he x ∈
      unitary (CliffordAlgebra (Q₁.prod Q₂)) := by
  rw [Unitary.mem_iff]
  constructor
  · calc
      star (liftCliffordAmbient Q₁ Q₂ e he x) * liftCliffordAmbient Q₁ Q₂ e he x =
          liftCliffordAmbient Q₁ Q₂ e he (star x) * liftCliffordAmbient Q₁ Q₂ e he x := by
            rw [← liftCliffordAmbient_map_star]
      _ = liftCliffordAmbient Q₁ Q₂ e he (star x * x) := by rw [map_mul]
      _ = 1 := by rw [hx.1, map_one]
  · calc
      liftCliffordAmbient Q₁ Q₂ e he x * star (liftCliffordAmbient Q₁ Q₂ e he x) =
          liftCliffordAmbient Q₁ Q₂ e he x * liftCliffordAmbient Q₁ Q₂ e he (star x) := by
            rw [← liftCliffordAmbient_map_star]
      _ = liftCliffordAmbient Q₁ Q₂ e he (x * star x) := by rw [map_mul]
      _ = 1 := by rw [hx.2, map_one]

/-- A unit vector generator in the source Lipschitz subgroup maps to a product
of two target vector generators. The auxiliary negative unit makes both
factors invertible whenever their product is the image of an invertible
source generator. -/
theorem liftCliffordAmbient_map_lipschitz_generator
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1)
    {u : (CliffordAlgebra Q₁)ˣ} {v : M₁}
    (hu : (u : CliffordAlgebra Q₁) = ι Q₁ v) :
    Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom u ∈
      lipschitzGroup (Q₁.prod Q₂) := by
  let target := CliffordAlgebra (Q₁.prod Q₂)
  let x : target := ι (Q₁.prod Q₂) (v, 0)
  let y : target := ι (Q₁.prod Q₂) (0, e)
  have hxy : IsUnit (x * y) := by
    have hmap : IsUnit (liftCliffordAmbient Q₁ Q₂ e he (u : CliffordAlgebra Q₁)) :=
      Units.isUnit (Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom u)
    rw [hu, liftCliffordAmbient_ι, liftVector] at hmap
    simpa [x, y] using hmap
  have hyQ : IsUnit ((Q₁.prod Q₂) (0, e)) := by
    simp [QuadraticMap.prod_apply, he]
  have hy : IsUnit y := by
    dsimp [y]
    exact CliffordAlgebra.isUnit_ι_of_isUnit (Q₁.prod Q₂) hyQ
  have hx : IsUnit x := by
    have hunit : IsUnit ((hy.unit⁻¹ : targetˣ) : target) := Units.isUnit _
    have h := hxy.mul hunit
    simpa [x, y, mul_assoc, hy.unit_spec] using h
  let ux : targetˣ := hx.unit
  let uy : targetˣ := hy.unit
  have hux : ux ∈ lipschitzGroup (Q₁.prod Q₂) := by
    unfold lipschitzGroup
    apply Subgroup.subset_closure
    exact ⟨(v, 0), by simp [ux, x]⟩
  have huy : uy ∈ lipschitzGroup (Q₁.prod Q₂) := by
    unfold lipschitzGroup
    apply Subgroup.subset_closure
    exact ⟨(0, e), by simp [uy, y]⟩
  have hmap : Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom u = ux * uy := by
    apply Units.ext
    simp [ux, uy, x, y, hu, liftCliffordAmbient_ι, liftVector]
  rw [hmap]
  exact Subgroup.mul_mem _ hux huy

set_option maxHeartbeats 5000000 in
/-- The ambient Clifford algebra map preserves the entire Lipschitz subgroup,
not only its vector generators. This uses Mathlib's actual closure-generated
definition and the generator theorem above. -/
theorem liftCliffordAmbient_map_lipschitz
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1)
    {u : (CliffordAlgebra Q₁)ˣ} (hu : u ∈ lipschitzGroup Q₁) :
    Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom u ∈
      lipschitzGroup (Q₁.prod Q₂) := by
  unfold lipschitzGroup at hu ⊢
  induction hu using Subgroup.closure_induction'' with
  | mem u hu =>
      rcases hu with ⟨v, hv⟩
      exact liftCliffordAmbient_map_lipschitz_generator Q₁ Q₂ e he hv.symm
  | inv_mem u hu =>
      rcases hu with ⟨v, hv⟩
      have hgen :
          Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom u ∈
            Subgroup.closure
              ((↑) ⁻¹' Set.range (ι (Q₁.prod Q₂)) :
                Set (CliffordAlgebra (Q₁.prod Q₂))ˣ) := by
        exact liftCliffordAmbient_map_lipschitz_generator Q₁ Q₂ e he hv.symm
      simpa only [map_inv] using Subgroup.inv_mem _ hgen
  | one =>
      simpa only [map_one] using Subgroup.one_mem _
  | mul u v _ _ hu hv =>
      simpa only [map_mul] using Subgroup.mul_mem _ hu hv

/-- A vector of Clifford square `-1` is a member of Mathlib's native Pin
submonoid. The proof checks both its Lipschitz-generator and unitary clauses. -/
theorem cliffordVector_mem_pinGroup_of_sq_eq_neg_one
    {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (v : M) (hv : Q v = -1) :
    ι Q v ∈ pinGroup Q := by
  let u : (CliffordAlgebra Q)ˣ :=
    (CliffordAlgebra.isUnit_ι_of_isUnit Q (by rw [hv]; exact ⟨-1, by simp⟩)).unit
  have hu : (u : CliffordAlgebra Q) = ι Q v := by
    exact (CliffordAlgebra.isUnit_ι_of_isUnit Q
      (by rw [hv]; exact ⟨-1, by simp⟩)).unit_spec
  rw [← hu, pinGroup.mem_iff]
  constructor
  · refine (Submonoid.mem_map).2 ⟨u, ?_, rfl⟩
    change u ∈ lipschitzGroup Q
    unfold lipschitzGroup
    apply Subgroup.subset_closure
    exact ⟨v, hu⟩
  · rw [Unitary.mem_iff]
    constructor
    · rw [hu, CliffordAlgebra.star_ι, neg_mul, CliffordAlgebra.ι_sq_scalar]
      simp [hv]
    · rw [hu, CliffordAlgebra.star_ι, mul_neg, CliffordAlgebra.ι_sq_scalar]
      simp [hv]

/-- The product lift takes native Pin elements into the target Spin submonoid.
The three required components are checked separately: Lipschitz closure,
Clifford-star unitarity, and even parity of the algebra-hom image. -/
private theorem liftCliffordAmbient_pin_mem_spin
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (g : pinGroup Q₁) :
    liftCliffordAmbient Q₁ Q₂ e he (g : CliffordAlgebra Q₁) ∈
      spinGroup (Q₁.prod Q₂) := by
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · refine (Submonoid.mem_map).2 ⟨
        Units.map (liftCliffordAmbient Q₁ Q₂ e he).toMonoidHom
          (pinGroup.toUnits g), ?_, ?_⟩
      · exact liftCliffordAmbient_map_lipschitz Q₁ Q₂ e he
          (u := pinGroup.toUnits g)
          (pinGroup.units_mem_lipschitzGroup g.prop)
      · simp [pinGroup.toUnits]
    · rw [Unitary.mem_iff]
      constructor
      · have h := congrArg (liftCliffordAmbient Q₁ Q₂ e he)
          (pinGroup.mem_unitary g.prop).1
        simpa only [map_mul, liftCliffordAmbient_map_star, map_one] using h
      · have h := congrArg (liftCliffordAmbient Q₁ Q₂ e he)
          (pinGroup.mem_unitary g.prop).2
        simpa only [map_mul, liftCliffordAmbient_map_star, map_one] using h
  · change liftCliffordAmbient Q₁ Q₂ e he (g : CliffordAlgebra Q₁) ∈
      CliffordAlgebra.evenOdd (Q₁.prod Q₂) 0
    exact (liftCliffordEven Q₁ Q₂ e he (g : CliffordAlgebra Q₁)).property

/-- The negative-auxiliary-vector lift induces a monoid hom from Mathlib's Pin
submonoid for `Q₁` to the Spin submonoid for `Q₁.prod Q₂`. The statement uses
Mathlib's native unitary Pin convention; it does not assert injectivity. -/
noncomputable def pinToSpinProduct
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) :
    pinGroup Q₁ →* spinGroup (Q₁.prod Q₂) where
  toFun g :=
    ⟨liftCliffordAmbient Q₁ Q₂ e he (g : CliffordAlgebra Q₁),
      liftCliffordAmbient_pin_mem_spin Q₁ Q₂ e he g⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp

/-- On a negative-square vector generator, the Pin-to-Spin hom is exactly the
ordered product with the fixed orthogonal negative vector. -/
theorem pinToSpinProduct_vector
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (e : M₂) (he : Q₂ e = -1) (v : M₁) (hv : Q₁ v = -1) :
    (pinToSpinProduct Q₁ Q₂ e he
      ⟨ι Q₁ v, cliffordVector_mem_pinGroup_of_sq_eq_neg_one Q₁ v hv⟩ :
        CliffordAlgebra (Q₁.prod Q₂)) = liftVector Q₁ Q₂ e v := by
  simp [pinToSpinProduct, liftCliffordAmbient_ι, liftVector]

end InfoGeometry.Clifford.PinProductLift
