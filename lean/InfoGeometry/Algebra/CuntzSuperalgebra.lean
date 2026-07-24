import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Superalgebra: Z_2 parity grading Π(S_i) = -S_i

Defines the parity automorphism Π on CuntzAlg n satisfying:
- Π(S_i) = -S_i, Π(Sdag_i) = -Sdag_i
- Π² = id (involution of order 2)
- Π(xy) = Π(x)Π(y), Π(1) = 1 (algebra automorphism)
- Π commutes with the formal dagger on the quotient generators

The even subalgebra (Π(x)=x) contains projectors and the Hamiltonian.
The odd subspace (Π(x)=-x) contains generators.

Proof: define Π on the free tensor algebra by negating each generator.
Since every Cuntz relation involves pairs of generators, the signs
cancel ((-1)² = +1), so Π descends to the quotient.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzSuperalgebra

/-! ## Parity on the free tensor algebra -/

noncomputable def parityOnTensor (n : ℕ) : CuntzTensor n →ₐ[ℂ] CuntzTensor n :=
  TensorAlgebra.lift ℂ (-(TensorAlgebra.ι ℂ : CuntzFree n →ₗ[ℂ] CuntzTensor n))

@[simp] theorem parityOnTensor_S (n : ℕ) (i : Fin n) :
    parityOnTensor n (S n i) = -(S n i) := by
  dsimp [parityOnTensor, S, gen]
  simp

@[simp] theorem parityOnTensor_Sdag (n : ℕ) (i : Fin n) :
    parityOnTensor n (Sdag n i) = -(Sdag n i) := by
  dsimp [parityOnTensor, Sdag, gen]
  simp

/-! ## Descent through the Cuntz relation -/

theorem parityOnTensor_respects_Cuntz (n : ℕ) {x y : CuntzTensor n}
    (h : CuntzRel n x y) :
    CuntzRel n (parityOnTensor n x) (parityOnTensor n y) := by
  rcases h with (⟨i, j⟩ | _)
  · -- orth: Sdag_i S_j ~ δ_{ij}
    -- Π(Sdag_i S_j) = (-Sdag_i)(-S_j) = Sdag_i S_j ~ δ_{ij}
    simpa [map_mul, parityOnTensor_S, parityOnTensor_Sdag] using CuntzRel.orth i j
  · -- ranges_sum_one: Σ S_i Sdag_i ~ 1
    -- Π(Σ S_i Sdag_i) = Σ (-S_i)(-Sdag_i) = Σ S_i Sdag_i ~ 1
    simpa [map_mul, map_sum, parityOnTensor_S, parityOnTensor_Sdag]
      using CuntzRel.ranges_sum_one (n := n)

theorem parityOnTensor_respects_CuntzMk (n : ℕ) :
    ∀ ⦃x y : CuntzTensor n⦄,
      CuntzRel n x y →
        (cuntzMk n) (parityOnTensor n x) = (cuntzMk n) (parityOnTensor n y) := by
  intro x y h
  exact RingQuot.mkAlgHom_rel ℂ (parityOnTensor_respects_Cuntz n h)

/-! ## Parity on the Cuntz quotient -/

noncomputable def parity (n : ℕ) : CuntzAlg n →ₐ[ℂ] CuntzAlg n :=
  (RingQuot.liftAlgHom ℂ) ⟨
    (cuntzMk n).comp (parityOnTensor n),
    parityOnTensor_respects_CuntzMk n
  ⟩

@[simp] theorem parity_mk (n : ℕ) (x : CuntzTensor n) :
    parity n (cuntzMk n x) = cuntzMk n (parityOnTensor n x) := by
  change
    ((RingQuot.liftAlgHom ℂ)
      ⟨(cuntzMk n).comp (parityOnTensor n), parityOnTensor_respects_CuntzMk n⟩)
        ((RingQuot.mkAlgHom ℂ (CuntzRel n)) x) =
      (cuntzMk n) (parityOnTensor n x)
  exact RingQuot.liftAlgHom_mkAlgHom_apply ℂ
    ((cuntzMk n).comp (parityOnTensor n))
    (parityOnTensor_respects_CuntzMk n)
    x

@[simp] theorem parity_S (n : ℕ) (i : Fin n) : parity n (cuntzS n i) = -(cuntzS n i) := by
  rw [cuntzS, parity_mk, parityOnTensor_S]
  simp [cuntzMk]

@[simp] theorem parity_Sdag (n : ℕ) (i : Fin n) : parity n (cuntzSdag n i) = -(cuntzSdag n i) := by
  rw [cuntzSdag, parity_mk, parityOnTensor_Sdag]
  simp [cuntzMk]

@[simp] theorem parityOnTensor_sq (n : ℕ) (x : CuntzTensor n) :
    parityOnTensor n (parityOnTensor n x) = x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      simp [parityOnTensor]
  | ι v =>
      simp [parityOnTensor]
  | mul x y hx hy =>
      simp [map_mul, hx, hy]
  | add x y hx hy =>
      simp [map_add, hx, hy]

/-- Π² = id. Two negations cancel. -/
@[simp] theorem parity_sq (n : ℕ) (x : CuntzAlg n) : parity n (parity n x) = x := by
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  change parity n (parity n (cuntzMk n y)) = cuntzMk n y
  rw [parity_mk, parity_mk, parityOnTensor_sq]

/-- The parity involution as a genuine algebra automorphism. -/
noncomputable def parityEquiv (n : ℕ) : CuntzAlg n ≃ₐ[ℂ] CuntzAlg n where
  toFun := parity n
  invFun := parity n
  left_inv := parity_sq n
  right_inv := parity_sq n
  map_mul' := map_mul (parity n)
  map_add' := map_add (parity n)
  commutes' := (parity n).commutes

@[simp] theorem parityEquiv_apply (n : ℕ) (x : CuntzAlg n) :
    parityEquiv n x = parity n x :=
  rfl

theorem parity_star_cuntzS (n : ℕ) (i : Fin n) :
    parity n (star (cuntzS n i)) = star (parity n (cuntzS n i)) := by
  rw [star_cuntzS, parity_Sdag, parity_S]
  simp [star_cuntzS]

theorem parity_star_cuntzSdag (n : ℕ) (i : Fin n) :
    parity n (star (cuntzSdag n i)) = star (parity n (cuntzSdag n i)) := by
  rw [star_cuntzSdag, parity_S, parity_Sdag]
  simp [star_cuntzSdag]

/-! ## Binary-labelled Cuntz gradings -/

/-- Sign attached to a binary generator label. -/
def labelSign {n : ℕ} (δ : Fin n → Bool) (i : Fin n) : ℂ :=
  if δ i then -1 else 1

@[simp] theorem labelSign_sq {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
    labelSign δ i * labelSign δ i = 1 := by
  by_cases h : δ i <;> simp [labelSign, h]

@[simp] theorem labelSign_ne_zero {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
    labelSign δ i ≠ 0 := by
  by_cases h : δ i <;> simp [labelSign, h]

/-- Linear generator map induced by a binary Cuntz label. -/
noncomputable def labeledParityFree {n : ℕ} (δ : Fin n → Bool) :
    CuntzFree n →ₗ[ℂ] CuntzFree n where
  toFun v :=
    Finsupp.onFinset v.support
      (fun g => labelSign δ g.1 * v g)
      (by
        intro g hg
        have hv : v g ≠ 0 := by
          intro hzero
          exact hg (by simp [hzero])
        exact Finsupp.mem_support_iff.mpr hv)
  map_add' v w := by
    ext g
    simp [mul_add]
  map_smul' c v := by
    ext g
    simp [mul_left_comm]

@[simp] theorem labeledParityFree_single {n : ℕ} (δ : Fin n → Bool)
    (i : Fin n) (b : Bool) :
    labeledParityFree δ (Finsupp.single (i, b) (1 : ℂ)) =
      Finsupp.single (i, b) (labelSign δ i) := by
  ext g
  by_cases h : g = (i, b)
  · subst g
    simp [labeledParityFree]
  · simp [labeledParityFree, Finsupp.single_eq_of_ne h]

/-- Tensor-algebra automorphism candidate induced by a binary Cuntz label. -/
noncomputable def labeledParityOnTensor {n : ℕ} (δ : Fin n → Bool) :
    CuntzTensor n →ₐ[ℂ] CuntzTensor n :=
  TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp (labeledParityFree δ))

@[simp] theorem labeledParityOnTensor_S {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
  labeledParityOnTensor δ (S n i) = labelSign δ i • S n i := by
  dsimp [labeledParityOnTensor, S, gen]
  rw [TensorAlgebra.lift_ι_apply]
  change (TensorAlgebra.ι ℂ)
      (labeledParityFree δ (Finsupp.single (i, false) (1 : ℂ))) =
    labelSign δ i • (TensorAlgebra.ι ℂ) (Finsupp.single (i, false) (1 : ℂ))
  rw [labeledParityFree_single]
  calc
    (TensorAlgebra.ι ℂ) (Finsupp.single (i, false) (labelSign δ i))
        = (TensorAlgebra.ι ℂ)
            (labelSign δ i • Finsupp.single (i, false) (1 : ℂ)) := by
          congr 1
          simp [Finsupp.smul_single]
    _ = labelSign δ i •
          (TensorAlgebra.ι ℂ) (Finsupp.single (i, false) (1 : ℂ)) := by
          rw [LinearMap.map_smul]

@[simp] theorem labeledParityOnTensor_Sdag {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
  labeledParityOnTensor δ (Sdag n i) = labelSign δ i • Sdag n i := by
  dsimp [labeledParityOnTensor, Sdag, gen]
  rw [TensorAlgebra.lift_ι_apply]
  change (TensorAlgebra.ι ℂ)
      (labeledParityFree δ (Finsupp.single (i, true) (1 : ℂ))) =
    labelSign δ i • (TensorAlgebra.ι ℂ) (Finsupp.single (i, true) (1 : ℂ))
  rw [labeledParityFree_single]
  calc
    (TensorAlgebra.ι ℂ) (Finsupp.single (i, true) (labelSign δ i))
        = (TensorAlgebra.ι ℂ)
            (labelSign δ i • Finsupp.single (i, true) (1 : ℂ)) := by
          congr 1
          simp [Finsupp.smul_single]
    _ = labelSign δ i •
          (TensorAlgebra.ι ℂ) (Finsupp.single (i, true) (1 : ℂ)) := by
          rw [LinearMap.map_smul]

theorem labeledParityOnTensor_respects_CuntzMk {n : ℕ} (δ : Fin n → Bool) :
    ∀ ⦃x y : CuntzTensor n⦄,
      CuntzRel n x y →
        (cuntzMk n) (labeledParityOnTensor δ x) =
          (cuntzMk n) (labeledParityOnTensor δ y) := by
  intro x y h
  rcases h with (⟨i, j⟩ | _)
  ·
    by_cases hij : i = j
    · subst j
      calc
        (cuntzMk n) (labeledParityOnTensor δ (Sdag n i * S n i))
            = (labelSign δ i • cuntzSdag n i) *
                (labelSign δ i • cuntzS n i) := by
              simp [map_mul, cuntzS, cuntzSdag]
        _ = labelSign δ i • labelSign δ i •
              (cuntzSdag n i * cuntzS n i) := by
              rw [smul_mul_assoc, mul_smul_comm]
        _ = 1 := by
              rw [smul_smul, labelSign_sq, one_smul, cuntz_isometry]
        _ = (cuntzMk n) (labeledParityOnTensor δ (if i = i then 1 else 0)) := by
              simp [labeledParityOnTensor]
    · calc
        (cuntzMk n) (labeledParityOnTensor δ (Sdag n i * S n j))
            = (labelSign δ i • cuntzSdag n i) *
                (labelSign δ j • cuntzS n j) := by
              simp [map_mul, cuntzS, cuntzSdag]
        _ = labelSign δ i • labelSign δ j •
              (cuntzSdag n i * cuntzS n j) := by
              rw [smul_mul_assoc, mul_smul_comm]
        _ = 0 := by
              rw [cuntz_distinct_orthogonal n hij, smul_zero, smul_zero]
        _ = (cuntzMk n) (labeledParityOnTensor δ (if i = j then 1 else 0)) := by
              simp [hij, labeledParityOnTensor]
  ·
    calc
      (cuntzMk n) (labeledParityOnTensor δ (∑ i : Fin n, S n i * Sdag n i))
          = ∑ i : Fin n,
              labelSign δ i • labelSign δ i •
                (cuntzS n i * cuntzSdag n i) := by
              simp [map_sum, map_mul, cuntzS, cuntzSdag]
      _ = ∑ i : Fin n, cuntzS n i * cuntzSdag n i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [smul_smul, labelSign_sq, one_smul]
      _ = 1 := cuntz_ranges_sum_one n
      _ = (cuntzMk n) (labeledParityOnTensor δ 1) := by simp [labeledParityOnTensor]

/-- Quotient grading automorphism induced by a binary label on the finite Cuntz generators. -/
noncomputable def labeledParity {n : ℕ} (δ : Fin n → Bool) : CuntzAlg n →ₐ[ℂ] CuntzAlg n :=
  (RingQuot.liftAlgHom ℂ) ⟨
    (cuntzMk n).comp (labeledParityOnTensor δ),
    labeledParityOnTensor_respects_CuntzMk δ
  ⟩

@[simp] theorem labeledParity_mk {n : ℕ} (δ : Fin n → Bool) (x : CuntzTensor n) :
    labeledParity δ (cuntzMk n x) = cuntzMk n (labeledParityOnTensor δ x) := by
  change
    ((RingQuot.liftAlgHom ℂ)
      ⟨(cuntzMk n).comp (labeledParityOnTensor δ),
        labeledParityOnTensor_respects_CuntzMk δ⟩)
        ((RingQuot.mkAlgHom ℂ (CuntzRel n)) x) =
      (cuntzMk n) (labeledParityOnTensor δ x)
  exact RingQuot.liftAlgHom_mkAlgHom_apply ℂ
    ((cuntzMk n).comp (labeledParityOnTensor δ))
    (labeledParityOnTensor_respects_CuntzMk δ)
    x

@[simp] theorem labeledParity_S {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
    labeledParity δ (cuntzS n i) = labelSign δ i • cuntzS n i := by
  rw [cuntzS, labeledParity_mk, labeledParityOnTensor_S]
  simp [cuntzMk]

@[simp] theorem labeledParity_Sdag {n : ℕ} (δ : Fin n → Bool) (i : Fin n) :
    labeledParity δ (cuntzSdag n i) = labelSign δ i • cuntzSdag n i := by
  rw [cuntzSdag, labeledParity_mk, labeledParityOnTensor_Sdag]
  simp [cuntzMk]

@[simp] theorem labeledParityFree_sq {n : ℕ} (δ : Fin n → Bool) (v : CuntzFree n) :
  labeledParityFree δ (labeledParityFree δ v) = v := by
  ext g
  simp [labeledParityFree, ← mul_assoc]

@[simp] theorem labeledParityOnTensor_sq {n : ℕ} (δ : Fin n → Bool) (x : CuntzTensor n) :
    labeledParityOnTensor δ (labeledParityOnTensor δ x) = x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r =>
      simp [labeledParityOnTensor]
  | ι v =>
      simp [labeledParityOnTensor]
  | mul x y hx hy =>
      simp [map_mul, hx, hy]
  | add x y hx hy =>
      simp [map_add, hx, hy]

@[simp] theorem labeledParity_sq {n : ℕ} (δ : Fin n → Bool) (x : CuntzAlg n) :
    labeledParity δ (labeledParity δ x) = x := by
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x with ⟨y, rfl⟩
  change labeledParity δ (labeledParity δ (cuntzMk n y)) = cuntzMk n y
  rw [labeledParity_mk, labeledParity_mk, labeledParityOnTensor_sq]

/-- Binary-labelled Cuntz grading as an algebra involution. -/
noncomputable def labeledParityEquiv {n : ℕ} (δ : Fin n → Bool) :
    CuntzAlg n ≃ₐ[ℂ] CuntzAlg n where
  toFun := labeledParity δ
  invFun := labeledParity δ
  left_inv := labeledParity_sq δ
  right_inv := labeledParity_sq δ
  map_mul' := map_mul (labeledParity δ)
  map_add' := map_add (labeledParity δ)
  commutes' := (labeledParity δ).commutes

end InfoGeometry.Algebra.CuntzSuperalgebra
