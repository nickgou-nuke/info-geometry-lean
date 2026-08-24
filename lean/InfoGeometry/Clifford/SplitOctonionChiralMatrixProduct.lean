import InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Transported chiral Cayley product

The outer `2 × 2` quaternion-entry matrices are only a linear carrier.  The
operation below is the transported split-Cayley product; it is deliberately
not ordinary matrix multiplication.  For pure imaginary quaternion entries,
the scalar channels use anticommutators and the chiral channels use
commutators.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout

noncomputable section

private def half : ChiralEntry := (1 / 2 : ℝ) • entryOne

def chiralStar (X Y : ChiralMatrix) : ChiralMatrix :=
  !![ X 0 0 * Y 0 0 + half * (X 0 1 * Y 1 0 + Y 1 0 * X 0 1),
      X 0 0 * Y 0 1 + Y 1 1 * X 0 1 + half * (X 1 0 * Y 1 0 - Y 1 0 * X 1 0);
      Y 0 0 * X 1 0 + X 1 1 * Y 1 0 + half * (X 0 1 * Y 0 1 - Y 0 1 * X 0 1),
      X 1 1 * Y 1 1 + half * (X 1 0 * Y 0 1 + Y 0 1 * X 1 0) ]

def chiralZornProductCoordinates
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ℝ) :
    Fin 8 → ℝ
  | 0 => a₀ * c₀ - (a₁ * d₁ + a₂ * d₂ + a₃ * d₃)
  | 1 => a₀ * c₁ + d₀ * a₁ + (b₂ * d₃ - b₃ * d₂)
  | 2 => a₀ * c₂ + d₀ * a₂ + (b₃ * d₁ - b₁ * d₃)
  | 3 => a₀ * c₃ + d₀ * a₃ + (b₁ * d₂ - b₂ * d₁)
  | 4 => b₀ * d₀ - (b₁ * c₁ + b₂ * c₂ + b₃ * c₃)
  | 5 => c₀ * b₁ + b₀ * d₁ + (a₂ * c₃ - a₃ * c₂)
  | 6 => c₀ * b₂ + b₀ * d₂ + (a₃ * c₁ - a₁ * c₃)
  | 7 => c₀ * b₃ + b₀ * d₃ + (a₁ * c₂ - a₂ * c₁)

set_option maxHeartbeats 4000000 in
theorem chiralStar_coordinates_eq
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ℝ) :
    chiralStar (chiralCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
        (chiralCoordinates c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃) =
      chiralCoordinates
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 0)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 1)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 2)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 3)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 4)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 5)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 6)
        (chiralZornProductCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
          c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ 7) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, chiralCoordinates,
      chiralZornProductCoordinates, half, uPlus, uMinus, uOne, uTwo, uThree,
      vOne, vTwo, vThree, rhoPlus, rhoMinus, entryOne, entryZero,
      entryI, entryJ, entryK] <;>
    apply Quaternion.ext <;>
      simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul] <;>
        ring

def chiralCayleyConjCoordinates (c : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![c 4, -(c 1), -(c 2), -(c 3), c 0, -(c 5), -(c 6), -(c 7)]

@[simp] theorem chiralCayleyConjCoordinates_apply (c : Fin 8 → ℝ) :
    chiralCayleyConjCoordinates c =
      ![c 4, -(c 1), -(c 2), -(c 3), c 0, -(c 5), -(c 6), -(c 7)] := rfl

theorem chiralStar_coordinate_conj_eq_scalar
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) :
    chiralStar (chiralCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃)
        (chiralCoordinates b₀ (-a₁) (-a₂) (-a₃) a₀ (-b₁) (-b₂) (-b₃)) =
      chiralCoordinates
        (a₀ * b₀ + a₁ * b₁ + a₂ * b₂ + a₃ * b₃)
        0 0 0
        (a₀ * b₀ + a₁ * b₁ + a₂ * b₂ + a₃ * b₃)
        0 0 0 := by
  rw [chiralStar_coordinates_eq]
  simp [chiralZornProductCoordinates]
  ring

theorem chiralStar_coordinate_conj_eq_scalar_right
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ℝ) :
    chiralStar (chiralCoordinates b₀ (-a₁) (-a₂) (-a₃) a₀ (-b₁) (-b₂) (-b₃))
        (chiralCoordinates a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃) =
      chiralCoordinates
        (a₀ * b₀ + a₁ * b₁ + a₂ * b₂ + a₃ * b₃)
        0 0 0
        (a₀ * b₀ + a₁ * b₁ + a₂ * b₂ + a₃ * b₃)
        0 0 0 := by
  rw [chiralStar_coordinates_eq]
  simp [chiralZornProductCoordinates]
  ring

noncomputable def chiralQuadratic : QuadraticForm ℝ (Fin 8 → ℝ) :=
  QuadraticMap.ofPolar
    (fun c => c 0 * c 4 + c 1 * c 5 + c 2 * c 6 + c 3 * c 7)
    (by
      intro a c
      dsimp
      ring)
    (by
      intro c d e
      dsimp [QuadraticMap.polar]
      ring)
    (by
      intro a c d
      dsimp [QuadraticMap.polar]
      ring)

@[simp] theorem chiralQuadratic_apply (c : Fin 8 → ℝ) :
    chiralQuadratic c = c 0 * c 4 + c 1 * c 5 + c 2 * c 6 + c 3 * c 7 := by
  rfl

def chiralCoordinateProduct (x y : Fin 8 → ℝ) : Fin 8 → ℝ :=
  chiralZornProductCoordinates
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)

/-! The coordinate product is the restriction of `chiralStar` to the
eight-dimensional Cayley carrier. -/

theorem chiralStar_coordinates_linear_eq
    (x y : Fin 8 → ℝ) :
    chiralStar (chiralCoordinatesLinear x) (chiralCoordinatesLinear y) =
      chiralCoordinatesLinear (chiralCoordinateProduct x y) := by
  simpa [chiralCoordinatesLinear, chiralCoordinates, chiralCoordinateProduct,
    chiralZornProductCoordinates] using
    chiralStar_coordinates_eq
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)

theorem chiralStar_carrier_eq
    (x y : chiralCayleyCarrier) :
    chiralStar x.1 y.1 =
      chiralCoordinatesLinear
        (chiralCoordinateProduct (chiralCoordinatesEquiv.symm x)
          (chiralCoordinatesEquiv.symm y)) := by
  rw [← chiralCoordinatesEquiv_symm_apply x,
    ← chiralCoordinatesEquiv_symm_apply y]
  exact chiralStar_coordinates_linear_eq _ _

theorem chiralCoordinateProduct_add_right (x y z : Fin 8 → ℝ) :
    chiralCoordinateProduct x (y + z) =
      chiralCoordinateProduct x y + chiralCoordinateProduct x z := by
  funext i
  fin_cases i <;>
    simp [chiralCoordinateProduct, chiralZornProductCoordinates,
      add_mul, mul_add, sub_mul, mul_sub] <;> ring

theorem chiralCoordinateProduct_smul_right (a : ℝ) (x y : Fin 8 → ℝ) :
    chiralCoordinateProduct x (a • y) =
      a • chiralCoordinateProduct x y := by
  funext i
  fin_cases i <;>
    simp [chiralCoordinateProduct, chiralZornProductCoordinates,
      smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub] <;> ring

theorem chiralCoordinateProduct_add_left (x y z : Fin 8 → ℝ) :
    chiralCoordinateProduct (x + y) z =
      chiralCoordinateProduct x z + chiralCoordinateProduct y z := by
  funext i
  fin_cases i <;>
    simp [chiralCoordinateProduct, chiralZornProductCoordinates,
      add_mul, mul_add, sub_mul, mul_sub] <;> ring

theorem chiralCoordinateProduct_smul_left (a : ℝ) (x y : Fin 8 → ℝ) :
    chiralCoordinateProduct (a • x) y =
      a • chiralCoordinateProduct x y := by
  funext i
  fin_cases i <;>
    simp [chiralCoordinateProduct, chiralZornProductCoordinates,
      smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub] <;> ring

def chiralCoordinateConj : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := chiralCayleyConjCoordinates
  map_add' x y := by
    funext i
    fin_cases i <;> simp [chiralCayleyConjCoordinates] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [chiralCayleyConjCoordinates]

@[simp] theorem chiralCoordinateConj_involutive (x : Fin 8 → ℝ) :
    chiralCoordinateConj (chiralCoordinateConj x) = x := by
  funext i
  fin_cases i <;> simp [chiralCoordinateConj, chiralCayleyConjCoordinates]

theorem chiralCoordinateConj_preserves_quadratic (c : Fin 8 → ℝ) :
    chiralQuadratic (chiralCoordinateConj c) = chiralQuadratic c := by
  simp [chiralQuadratic_apply, chiralCoordinateConj,
    chiralCayleyConjCoordinates]
  ring

theorem chiralCoordinateConj_preserves_polar
    (x y : Fin 8 → ℝ) :
    QuadraticMap.polar (⇑chiralQuadratic)
        (chiralCoordinateConj x) (chiralCoordinateConj y) =
      QuadraticMap.polar (⇑chiralQuadratic) x y := by
  change chiralQuadratic (chiralCoordinateConj x + chiralCoordinateConj y) -
      chiralQuadratic (chiralCoordinateConj x) -
        chiralQuadratic (chiralCoordinateConj y) =
    chiralQuadratic (x + y) - chiralQuadratic x - chiralQuadratic y
  rw [← chiralCoordinateConj.map_add, chiralCoordinateConj_preserves_quadratic,
    chiralCoordinateConj_preserves_quadratic,
    chiralCoordinateConj_preserves_quadratic]

theorem chiralCoordinateConj_product (x y : Fin 8 → ℝ) :
    chiralCoordinateConj (chiralCoordinateProduct x y) =
      chiralCoordinateProduct (chiralCoordinateConj y)
        (chiralCoordinateConj x) := by
  funext i
  fin_cases i <;>
    simp [chiralCoordinateConj, chiralCoordinateProduct,
      chiralCayleyConjCoordinates, chiralZornProductCoordinates] <;>
    ring

def chiralCoordinateLeft (x : Fin 8 → ℝ) :
    (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := chiralCoordinateProduct x
  map_add' y z := by
    exact chiralCoordinateProduct_add_right x y z
  map_smul' a y := by
    exact chiralCoordinateProduct_smul_right a x y

def chiralCoordinateRight (x : Fin 8 → ℝ) :
    (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := fun y => chiralCoordinateProduct y x
  map_add' y z := by
    exact chiralCoordinateProduct_add_left y z x
  map_smul' a y := by
    exact chiralCoordinateProduct_smul_left a y x

theorem chiralCoordinateConj_left_right (x y : Fin 8 → ℝ) :
    chiralCoordinateConj (chiralCoordinateLeft x
      (chiralCoordinateConj y)) =
      chiralCoordinateRight (chiralCoordinateConj x) y := by
  simpa only [chiralCoordinateLeft, chiralCoordinateRight,
    chiralCoordinateConj_involutive] using
    chiralCoordinateConj_product x (chiralCoordinateConj y)

def chiralCoordinateGamma :
    (Fin 8 → ℝ) →ₗ[ℝ]
      ((Fin 8 → ℝ) × (Fin 8 → ℝ) →ₗ[ℝ]
        ((Fin 8 → ℝ) × (Fin 8 → ℝ))) where
  toFun x := {
    toFun p :=
      (chiralCoordinateLeft x p.2,
        chiralCoordinateLeft (chiralCoordinateConj x) p.1)
    map_add' p q := by
      apply Prod.ext
      · change chiralCoordinateLeft x (p.2 + q.2) =
          chiralCoordinateLeft x p.2 + chiralCoordinateLeft x q.2
        simp only [map_add]
      · change chiralCoordinateLeft (chiralCoordinateConj x) (p.1 + q.1) =
          chiralCoordinateLeft (chiralCoordinateConj x) p.1 +
            chiralCoordinateLeft (chiralCoordinateConj x) q.1
        rw [map_add]
    map_smul' a p := by
      apply Prod.ext
      · change chiralCoordinateLeft x (a • p.2) =
          a • chiralCoordinateLeft x p.2
        simp only [map_smul]
      · change chiralCoordinateLeft (chiralCoordinateConj x) (a • p.1) =
          a • chiralCoordinateLeft (chiralCoordinateConj x) p.1
        rw [map_smul]
  }
  map_add' x y := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · change chiralCoordinateLeft (x + y) p.2 =
        chiralCoordinateLeft x p.2 + chiralCoordinateLeft y p.2
      simpa [chiralCoordinateLeft] using
        chiralCoordinateProduct_add_left x y p.2
    · change chiralCoordinateLeft (chiralCoordinateConj (x + y)) p.1 =
        chiralCoordinateLeft (chiralCoordinateConj x) p.1 +
          chiralCoordinateLeft (chiralCoordinateConj y) p.1
      rw [show chiralCoordinateConj (x + y) =
        chiralCoordinateConj x + chiralCoordinateConj y from
          chiralCoordinateConj.map_add x y]
      simpa [chiralCoordinateLeft] using
        chiralCoordinateProduct_add_left
          (chiralCoordinateConj x) (chiralCoordinateConj y) p.1
  map_smul' a x := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · change chiralCoordinateLeft (a • x) p.2 =
        a • chiralCoordinateLeft x p.2
      simpa [chiralCoordinateLeft] using
        chiralCoordinateProduct_smul_left a x p.2
    · change chiralCoordinateLeft (chiralCoordinateConj (a • x)) p.1 =
        a • chiralCoordinateLeft (chiralCoordinateConj x) p.1
      rw [show chiralCoordinateConj (a • x) =
        a • chiralCoordinateConj x from
          chiralCoordinateConj.map_smul a x]
      simpa [chiralCoordinateLeft] using
        chiralCoordinateProduct_smul_left a
          (chiralCoordinateConj x) p.1

theorem chiralCoordinateGamma_square (x : Fin 8 → ℝ) :
    chiralCoordinateGamma x ∘ₗ chiralCoordinateGamma x =
      chiralQuadratic x • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [chiralCoordinateGamma, chiralCoordinateLeft,
        chiralCoordinateProduct, chiralCoordinateConj,
        chiralCayleyConjCoordinates, chiralZornProductCoordinates,
        chiralQuadratic] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [chiralCoordinateGamma, chiralCoordinateLeft,
        chiralCoordinateProduct, chiralCoordinateConj,
        chiralCayleyConjCoordinates, chiralZornProductCoordinates,
        chiralQuadratic] <;>
      ring

noncomputable def chiralCliffordRepresentation :
    CliffordAlgebra chiralQuadratic →ₐ[ℝ]
      Module.End ℝ ((Fin 8 → ℝ) × (Fin 8 → ℝ)) :=
  CliffordAlgebra.lift chiralQuadratic
    ⟨chiralCoordinateGamma, chiralCoordinateGamma_square⟩

abbrev ChiralCayley := chiralCayleyCarrier

noncomputable def chiralCayleyConj : ChiralCayley →ₗ[ℝ] ChiralCayley :=
  chiralCoordinatesEquiv.toLinearMap.comp
    (chiralCoordinateConj.comp chiralCoordinatesEquiv.symm.toLinearMap)

@[simp] theorem chiralCayleyConj_involutive (x : ChiralCayley) :
    chiralCayleyConj (chiralCayleyConj x) = x := by
  apply chiralCoordinatesEquiv.symm.injective
  simpa [chiralCayleyConj] using
    chiralCoordinateConj_involutive (chiralCoordinatesEquiv.symm x)

noncomputable def chiralCayleyQuadratic :
    QuadraticForm ℝ ChiralCayley :=
  QuadraticMap.comp chiralQuadratic (chiralCoordinatesEquiv.symm).toLinearMap

@[simp] theorem chiralCayleyQuadratic_apply
    (x : ChiralCayley) :
    chiralCayleyQuadratic x = chiralQuadratic (chiralCoordinatesEquiv.symm x) := by
  rfl

theorem chiralCayleyConj_preserves_quadratic (x : ChiralCayley) :
    chiralCayleyQuadratic (chiralCayleyConj x) =
      chiralCayleyQuadratic x := by
  simp only [chiralCayleyQuadratic_apply]
  simpa [chiralCayleyConj] using
    chiralCoordinateConj_preserves_quadratic
      (chiralCoordinatesEquiv.symm x)

noncomputable def chiralCayleyConjIsometry :
    chiralCayleyQuadratic.IsometryEquiv chiralCayleyQuadratic where
  toLinearEquiv :=
    { toFun := chiralCayleyConj
      invFun := chiralCayleyConj
      left_inv := chiralCayleyConj_involutive
      right_inv := chiralCayleyConj_involutive
      map_add' := chiralCayleyConj.map_add
      map_smul' := chiralCayleyConj.map_smul }
  map_app' := chiralCayleyConj_preserves_quadratic

noncomputable def chiralCayleyPairEquiv :
    ((Fin 8 → ℝ) × (Fin 8 → ℝ)) ≃ₗ[ℝ]
      (ChiralCayley × ChiralCayley) :=
  LinearEquiv.prodCongr chiralCoordinatesEquiv chiralCoordinatesEquiv

/-! The associative chained-left-action algebra is formed after restricting
to the Cayley carrier.  Its generators are transported coordinate left
actions; `Algebra.adjoin` supplies only associative operator composition. -/

noncomputable def chiralCayleyLeftAction (x : ChiralCayley) :
    ChiralCayley →ₗ[ℝ] ChiralCayley :=
  chiralCoordinatesEquiv.toLinearMap.comp
    ((chiralCoordinateLeft (chiralCoordinatesEquiv.symm x)).comp
      chiralCoordinatesEquiv.symm.toLinearMap)

@[simp] theorem chiralCayleyLeftAction_apply
    (x y : ChiralCayley) :
    chiralCayleyLeftAction x y =
      chiralCoordinatesEquiv
        (chiralCoordinateProduct (chiralCoordinatesEquiv.symm x)
          (chiralCoordinatesEquiv.symm y)) := by
  rfl

noncomputable def chiralCayleyRightAction (x : ChiralCayley) :
    ChiralCayley →ₗ[ℝ] ChiralCayley :=
  chiralCoordinatesEquiv.toLinearMap.comp
    ((chiralCoordinateRight (chiralCoordinatesEquiv.symm x)).comp
      chiralCoordinatesEquiv.symm.toLinearMap)

@[simp] theorem chiralCayleyRightAction_apply
    (x y : ChiralCayley) :
    chiralCayleyRightAction x y =
      chiralCoordinatesEquiv
        (chiralCoordinateProduct (chiralCoordinatesEquiv.symm y)
          (chiralCoordinatesEquiv.symm x)) := by
  rfl

def chiralCayleyConjugateAction
    (T : Module.End ℝ ChiralCayley) : Module.End ℝ ChiralCayley :=
  chiralCayleyConj.comp (T.comp chiralCayleyConj)

@[simp] theorem chiralCayleyConjugateAction_involutive
    (T : Module.End ℝ ChiralCayley) :
    chiralCayleyConjugateAction
        (chiralCayleyConjugateAction T) = T := by
  apply LinearMap.ext
  intro x
  simp [chiralCayleyConjugateAction, LinearMap.comp_apply]

theorem chiralCayleyConjugateAction_comp
    (S T : Module.End ℝ ChiralCayley) :
    chiralCayleyConjugateAction (S.comp T) =
      (chiralCayleyConjugateAction S).comp
        (chiralCayleyConjugateAction T) := by
  apply LinearMap.ext
  intro x
  simp [chiralCayleyConjugateAction, LinearMap.comp_apply]

theorem chiralCayleyConjugateAction_add
    (C D : Module.End ℝ ChiralCayley) :
    chiralCayleyConjugateAction (C + D) =
      chiralCayleyConjugateAction C + chiralCayleyConjugateAction D := by
  apply LinearMap.ext
  intro x
  simp [chiralCayleyConjugateAction, LinearMap.comp_apply]

theorem chiralCayleyConjugateAction_algebraMap (r : ℝ) :
    chiralCayleyConjugateAction
        (algebraMap ℝ (Module.End ℝ ChiralCayley) r) =
      algebraMap ℝ (Module.End ℝ ChiralCayley) r := by
  apply LinearMap.ext
  intro x
  simp [chiralCayleyConjugateAction, LinearMap.comp_apply,
    Algebra.smul_def]

noncomputable def chiralCayleyConjugateActionRingEquiv :
    Module.End ℝ ChiralCayley ≃+* Module.End ℝ ChiralCayley where
  toFun := chiralCayleyConjugateAction
  invFun := chiralCayleyConjugateAction
  left_inv T := chiralCayleyConjugateAction_involutive T
  right_inv T := chiralCayleyConjugateAction_involutive T
  map_mul' S T := by
    change chiralCayleyConjugateAction (S.comp T) =
      chiralCayleyConjugateAction S * chiralCayleyConjugateAction T
    rw [chiralCayleyConjugateAction_comp]
    rfl
  map_add' S T := chiralCayleyConjugateAction_add S T

noncomputable def chiralCayleyConjugateActionAlgHom :
    Module.End ℝ ChiralCayley →ₐ[ℝ] Module.End ℝ ChiralCayley :=
  { toRingHom := chiralCayleyConjugateActionRingEquiv.toRingHom
    commutes' := fun r => chiralCayleyConjugateAction_algebraMap r }

theorem chiralCayleyConj_left_right (x y : ChiralCayley) :
    chiralCayleyConj
        (chiralCayleyLeftAction x (chiralCayleyConj y)) =
      chiralCayleyRightAction (chiralCayleyConj x) y := by
  apply chiralCoordinatesEquiv.symm.injective
  simpa [chiralCayleyConj, chiralCayleyLeftAction,
    chiralCayleyRightAction] using
    chiralCoordinateConj_left_right
      (chiralCoordinatesEquiv.symm x) (chiralCoordinatesEquiv.symm y)

theorem chiralCayleyConjugateAction_left
    (x : ChiralCayley) :
    chiralCayleyConjugateAction (chiralCayleyLeftAction x) =
      chiralCayleyRightAction (chiralCayleyConj x) := by
  apply LinearMap.ext
  intro y
  exact chiralCayleyConj_left_right x y

theorem chiralCayleyConjugateAction_right
    (x : ChiralCayley) :
    chiralCayleyConjugateAction (chiralCayleyRightAction x) =
      chiralCayleyLeftAction (chiralCayleyConj x) := by
  have h := congrArg chiralCayleyConjugateAction
    (chiralCayleyConjugateAction_left (chiralCayleyConj x))
  symm
  simpa [chiralCayleyConjugateAction_involutive] using h

noncomputable def chiralCayleyChainedRightActionAlgebra :
    Subalgebra ℝ (Module.End ℝ ChiralCayley) :=
  Algebra.adjoin ℝ (Set.range chiralCayleyRightAction)

theorem chiralCayleyConjugateAction_left_mem_rightAlgebra
    (x : ChiralCayley) :
    chiralCayleyConjugateAction (chiralCayleyLeftAction x) ∈
      chiralCayleyChainedRightActionAlgebra := by
  rw [chiralCayleyConjugateAction_left]
  exact Algebra.subset_adjoin ⟨chiralCayleyConj x, rfl⟩

noncomputable def chiralCayleyChainedLeftActionAlgebra :
    Subalgebra ℝ (Module.End ℝ ChiralCayley) :=
  Algebra.adjoin ℝ (Set.range chiralCayleyLeftAction)

theorem chiralCayleyLeftAction_mem_chainedAlgebra (x : ChiralCayley) :
    chiralCayleyLeftAction x ∈ chiralCayleyChainedLeftActionAlgebra := by
  exact Algebra.subset_adjoin ⟨x, rfl⟩

theorem chiralCayleyConjugateAction_left_mem_rightAlgebra_of_mem
    {T : Module.End ℝ ChiralCayley}
    (hT : T ∈ chiralCayleyChainedLeftActionAlgebra) :
    chiralCayleyConjugateAction T ∈
      chiralCayleyChainedRightActionAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun C _ => chiralCayleyConjugateAction C ∈
      chiralCayleyChainedRightActionAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro x hx
    rcases hx with ⟨x, rfl⟩
    exact chiralCayleyConjugateAction_left_mem_rightAlgebra x
  · intro r
    rw [chiralCayleyConjugateAction_algebraMap]
    exact chiralCayleyChainedRightActionAlgebra.algebraMap_mem r
  · intro C D hC hD hC' hD'
    rw [chiralCayleyConjugateAction_add]
    exact chiralCayleyChainedRightActionAlgebra.add_mem hC' hD'
  · intro C D hC hD hC' hD'
    rw [show C * D = C.comp D by rfl,
      chiralCayleyConjugateAction_comp]
    exact chiralCayleyChainedRightActionAlgebra.mul_mem hC' hD'

theorem chiralCayleyChainedRightActionAlgebra_eq_map_left :
    chiralCayleyChainedRightActionAlgebra =
      chiralCayleyChainedLeftActionAlgebra.map
        chiralCayleyConjugateActionAlgHom := by
  apply le_antisymm
  · change Algebra.adjoin ℝ (Set.range chiralCayleyRightAction) ≤ _
    refine Algebra.adjoin_le ?_
    intro T hT
    rcases hT with ⟨x, rfl⟩
    refine Subalgebra.mem_map.mpr ⟨chiralCayleyLeftAction (chiralCayleyConj x),
      chiralCayleyLeftAction_mem_chainedAlgebra _, ?_⟩
    have hgen : chiralCayleyConjugateActionAlgHom
          (chiralCayleyLeftAction (chiralCayleyConj x)) =
        chiralCayleyRightAction x := by
      change chiralCayleyConjugateAction
          (chiralCayleyLeftAction (chiralCayleyConj x)) =
        chiralCayleyRightAction x
      rw [chiralCayleyConjugateAction_left]
      simp
    exact hgen
  · rw [Subalgebra.map_le]
    intro T hT
    exact chiralCayleyConjugateAction_left_mem_rightAlgebra_of_mem hT

theorem chiralCayleyConjugateAction_right_mem_leftAlgebra_of_mem
    {T : Module.End ℝ ChiralCayley}
    (hT : T ∈ chiralCayleyChainedRightActionAlgebra) :
    chiralCayleyConjugateAction T ∈
      chiralCayleyChainedLeftActionAlgebra := by
  refine Algebra.adjoin_induction
    (p := fun C _ => chiralCayleyConjugateAction C ∈
      chiralCayleyChainedLeftActionAlgebra)
    ?_ ?_ ?_ ?_ hT
  · intro x hx
    rcases hx with ⟨x, rfl⟩
    rw [chiralCayleyConjugateAction_right]
    exact chiralCayleyLeftAction_mem_chainedAlgebra (chiralCayleyConj x)
  · intro r
    rw [chiralCayleyConjugateAction_algebraMap]
    exact chiralCayleyChainedLeftActionAlgebra.algebraMap_mem r
  · intro C D hC hD hC' hD'
    rw [chiralCayleyConjugateAction_add]
    exact chiralCayleyChainedLeftActionAlgebra.add_mem hC' hD'
  · intro C D hC hD hC' hD'
    rw [show C * D = C.comp D by rfl,
      chiralCayleyConjugateAction_comp]
    exact chiralCayleyChainedLeftActionAlgebra.mul_mem hC' hD'

theorem chiralCayleyConjugateAction_mem_right_iff
    (T : Module.End ℝ ChiralCayley) :
    chiralCayleyConjugateAction T ∈
        chiralCayleyChainedRightActionAlgebra ↔
      T ∈ chiralCayleyChainedLeftActionAlgebra := by
  constructor
  · intro hT
    have h := chiralCayleyConjugateAction_right_mem_leftAlgebra_of_mem hT
    simpa [chiralCayleyConjugateAction_involutive] using h
  · exact chiralCayleyConjugateAction_left_mem_rightAlgebra_of_mem

/-- The ambient Cayley-conjugation transport restricts to an algebra
equivalence between the two chained action subalgebras. -/
noncomputable def chiralCayleyChainedActionAlgEquiv :
    chiralCayleyChainedLeftActionAlgebra ≃ₐ[ℝ]
      chiralCayleyChainedRightActionAlgebra where
  toFun T :=
    ⟨chiralCayleyConjugateAction T.1,
      chiralCayleyConjugateAction_left_mem_rightAlgebra_of_mem T.2⟩
  invFun T :=
    ⟨chiralCayleyConjugateAction T.1,
      chiralCayleyConjugateAction_right_mem_leftAlgebra_of_mem T.2⟩
  left_inv T := by
    apply Subtype.ext
    exact chiralCayleyConjugateAction_involutive T.1
  right_inv T := by
    apply Subtype.ext
    exact chiralCayleyConjugateAction_involutive T.1
  map_mul' S T := by
    apply Subtype.ext
    exact chiralCayleyConjugateAction_comp S.1 T.1
  map_add' S T := by
    apply Subtype.ext
    exact chiralCayleyConjugateAction_add S.1 T.1
  commutes' r := by
    apply Subtype.ext
    exact chiralCayleyConjugateAction_algebraMap r

def chiralCayleyGamma (x : ChiralCayley) :
    (ChiralCayley × ChiralCayley) →ₗ[ℝ]
      (ChiralCayley × ChiralCayley) where
  toFun p :=
    chiralCayleyPairEquiv
      (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
        (chiralCayleyPairEquiv.symm p))
  map_add' p q := by
    simp [chiralCayleyPairEquiv]
  map_smul' a p := by
    simp [chiralCayleyPairEquiv]

def chiralCayleyGammaLinear :
    ChiralCayley →ₗ[ℝ]
      ((ChiralCayley × ChiralCayley) →ₗ[ℝ]
        (ChiralCayley × ChiralCayley)) where
  toFun := chiralCayleyGamma
  map_add' x y := by
    apply LinearMap.ext
    intro p
    simp only [chiralCayleyGamma, LinearMap.add_apply]
    change chiralCayleyPairEquiv
        (chiralCoordinateGamma (chiralCoordinatesEquiv.symm (x + y))
          (chiralCayleyPairEquiv.symm p)) =
      chiralCayleyPairEquiv
          (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
            (chiralCayleyPairEquiv.symm p)) +
        chiralCayleyPairEquiv
          (chiralCoordinateGamma (chiralCoordinatesEquiv.symm y)
            (chiralCayleyPairEquiv.symm p))
    rw [← chiralCayleyPairEquiv.map_add]
    apply congrArg chiralCayleyPairEquiv
    rw [show chiralCoordinatesEquiv.symm (x + y) =
      chiralCoordinatesEquiv.symm x + chiralCoordinatesEquiv.symm y from
        chiralCoordinatesEquiv.symm.map_add x y]
    exact congrArg (fun L => L (chiralCayleyPairEquiv.symm p))
      (chiralCoordinateGamma.map_add _ _)
  map_smul' a x := by
    apply LinearMap.ext
    intro p
    simpa [chiralCayleyGamma, chiralCayleyPairEquiv] using
      congrArg (fun L => L (chiralCayleyPairEquiv.symm p))
        (chiralCoordinateGamma.map_smul
          (chiralCoordinatesEquiv.symm x)
          (chiralCayleyPairEquiv.symm p))

theorem chiralCayleyGamma_square (x : ChiralCayley) :
    chiralCayleyGamma x ∘ₗ chiralCayleyGamma x =
      chiralCayleyQuadratic x • LinearMap.id := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  dsimp [chiralCayleyGamma]
  rw [chiralCayleyPairEquiv.symm_apply_apply]
  change chiralCayleyPairEquiv
      (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
        (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
          (chiralCayleyPairEquiv.symm p))) =
    chiralCayleyQuadratic x • p
  rw [chiralCayleyQuadratic_apply]
  conv_rhs =>
    rw [← chiralCayleyPairEquiv.apply_symm_apply p]
  rw [← chiralCayleyPairEquiv.map_smul]
  exact congrArg chiralCayleyPairEquiv
    (congrArg (fun L => L (chiralCayleyPairEquiv.symm p))
      (chiralCoordinateGamma_square (chiralCoordinatesEquiv.symm x)))

noncomputable def chiralCayleyCliffordRepresentation :
    CliffordAlgebra chiralCayleyQuadratic →ₐ[ℝ]
      Module.End ℝ (ChiralCayley × ChiralCayley) :=
  CliffordAlgebra.lift chiralCayleyQuadratic
    ⟨chiralCayleyGammaLinear, chiralCayleyGamma_square⟩

@[simp] theorem chiralCayleyCliffordRepresentation_ι_apply
    (x : ChiralCayley) :
    chiralCayleyCliffordRepresentation
        (CliffordAlgebra.ι chiralCayleyQuadratic x) =
      chiralCayleyGamma x := by
  exact CliffordAlgebra.lift_ι_apply chiralCayleyGammaLinear
    chiralCayleyGamma_square x

def chiralCayleyChirality :
    (ChiralCayley × ChiralCayley) →ₗ[ℝ]
    (ChiralCayley × ChiralCayley) where
  toFun p := (p.1, -p.2)
  map_add' p q := by
    apply Prod.ext
    · simp
    · simp
      abel_nf
  map_smul' a p := by
    apply Prod.ext <;> simp

@[simp] theorem chiralCayleyChirality_apply
    (u v : ChiralCayley) :
    chiralCayleyChirality (u, v) = (u, -v) := rfl

theorem chiralCayleyChirality_square :
    chiralCayleyChirality ∘ₗ chiralCayleyChirality =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  simp [chiralCayleyChirality]

theorem chiralCayleyChirality_anticommutes
    (x : ChiralCayley) :
    chiralCayleyChirality ∘ₗ chiralCayleyGamma x =
      -(chiralCayleyGamma x ∘ₗ chiralCayleyChirality) := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext
  · change chiralCoordinatesEquiv
        (chiralCoordinateProduct (chiralCoordinatesEquiv.symm x)
          (chiralCoordinatesEquiv.symm v)) =
      -chiralCoordinatesEquiv
        (chiralCoordinateProduct (chiralCoordinatesEquiv.symm x)
          (chiralCoordinatesEquiv.symm (-v)))
    rw [← map_neg]
    congr 1
    funext i
    fin_cases i <;>
      simp [chiralCoordinateProduct, chiralZornProductCoordinates] <;>
      ring
  · simp [chiralCayleyChirality, chiralCayleyGamma,
      chiralCayleyPairEquiv, LinearEquiv.prodCongr,
      chiralCoordinateGamma, chiralCoordinateLeft, chiralCoordinateConj]
    rfl

/-- Left multiplication by a chiral element, viewed as an operator on the
carrier.  It is a function rather than an asserted associative matrix
representation; the associator records the obstruction to composing these
operators as ordinary multiplication operators. -/
def leftChiralStar (X : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Y => chiralStar X Y

def rightChiralStar (Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun X => chiralStar X Y

def chiralAssociator (X Y Z : ChiralMatrix) : ChiralMatrix :=
  chiralStar (chiralStar X Y) Z - chiralStar X (chiralStar Y Z)

def leftProductDefect (X Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftChiralStar (chiralStar X Y) Z - leftChiralStar X (leftChiralStar Y Z)

def leftRightCommutatorDefect (X Y : ChiralMatrix) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftChiralStar X (rightChiralStar Y Z) -
    rightChiralStar Y (leftChiralStar X Z)

/-- The two four-component chiral operator frames.  They are frames of the
carrier; neither is asserted to be a subalgebra. -/
def sheetPlus : Fin 4 → ChiralMatrix :=
  ![uPlus, uOne, uTwo, uThree]

def sheetMinus : Fin 4 → ChiralMatrix :=
  ![uMinus, vOne, vTwo, vThree]

def leftSheetAction (a : Fin 4) : ChiralMatrix → ChiralMatrix :=
  leftChiralStar (sheetPlus a)

def rightSheetAction (b : Fin 4) : ChiralMatrix → ChiralMatrix :=
  rightChiralStar (sheetMinus b)

def sheetCommutantDefect (a b : Fin 4) : ChiralMatrix → ChiralMatrix :=
  fun Z => leftSheetAction a (rightSheetAction b Z) -
    rightSheetAction b (leftSheetAction a Z)

theorem leftChiralStar_apply (X Y : ChiralMatrix) :
    leftChiralStar X Y = chiralStar X Y := rfl

set_option maxHeartbeats 800000 in
theorem leftChiralStar_add_right (X Y Z : ChiralMatrix) :
    leftChiralStar X (Y + Z) = leftChiralStar X Y + leftChiralStar X Z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftChiralStar, chiralStar, half, add_mul, mul_add, sub_mul, mul_sub] <;>
      abel

theorem leftChiralStar_smul_right (a : ℝ) (X Y : ChiralMatrix) :
    leftChiralStar X (a • Y) = a • leftChiralStar X Y := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftChiralStar, chiralStar, half, smul_eq_mul, mul_add, add_mul, sub_mul, mul_sub,
      smul_add, smul_sub, smul_smul] <;>
      module

theorem chiralStar_add_right (X Y Z : ChiralMatrix) :
    chiralStar X (Y + Z) = chiralStar X Y + chiralStar X Z := by
  simpa [leftChiralStar] using leftChiralStar_add_right X Y Z

theorem chiralStar_smul_right (a : ℝ) (X Y : ChiralMatrix) :
    chiralStar X (a • Y) = a • chiralStar X Y := by
  simpa [leftChiralStar] using leftChiralStar_smul_right a X Y

def leftChiralStarLinear (X : ChiralMatrix) :
    ChiralMatrix →ₗ[ℝ] ChiralMatrix where
  toFun := leftChiralStar X
  map_add' := leftChiralStar_add_right X
  map_smul' a Y := leftChiralStar_smul_right a X Y

@[simp] theorem leftChiralStarLinear_apply (X Y : ChiralMatrix) :
    leftChiralStarLinear X Y = leftChiralStar X Y := by
  change leftChiralStar X Y = leftChiralStar X Y
  rfl

/-! The product defect is also an ordinary endomorphism in the acted-on
variable.  This records the obstruction inside the associative operator
algebra without asserting that the chiral product is associative. -/
def leftProductDefectLinear (X Y : ChiralMatrix) :
    ChiralMatrix →ₗ[ℝ] ChiralMatrix :=
  leftChiralStarLinear (chiralStar X Y) -
    leftChiralStarLinear X ∘ₗ leftChiralStarLinear Y

@[simp] theorem leftProductDefectLinear_apply
    (X Y Z : ChiralMatrix) :
    leftProductDefectLinear X Y Z = leftProductDefect X Y Z := by
  rfl

set_option maxHeartbeats 800000 in
theorem leftChiralStar_add_left (X Y Z : ChiralMatrix) :
    leftChiralStar (X + Y) Z = leftChiralStar X Z + leftChiralStar Y Z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftChiralStar, chiralStar, half, add_mul, mul_add, sub_mul, mul_sub] <;>
      abel

theorem leftChiralStar_smul_left (a : ℝ) (X Y : ChiralMatrix) :
    leftChiralStar (a • X) Y = a • leftChiralStar X Y := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftChiralStar, chiralStar, half, smul_eq_mul, mul_add, add_mul, sub_mul, mul_sub,
      smul_add, smul_sub, smul_smul] <;>
      module

theorem chiralStar_add_left (X Y Z : ChiralMatrix) :
    chiralStar (X + Y) Z = chiralStar X Z + chiralStar Y Z := by
  simpa [leftChiralStar] using leftChiralStar_add_left X Y Z

theorem chiralStar_smul_left (a : ℝ) (X Y : ChiralMatrix) :
    chiralStar (a • X) Y = a • chiralStar X Y := by
  simpa [leftChiralStar] using leftChiralStar_smul_left a X Y

def rightChiralStarLinear (Y : ChiralMatrix) :
    ChiralMatrix →ₗ[ℝ] ChiralMatrix where
  toFun := rightChiralStar Y
  map_add' := by
    intro X Z
    simpa [rightChiralStar] using leftChiralStar_add_left X Z Y
  map_smul' a X := by
    simpa [rightChiralStar] using leftChiralStar_smul_left a X Y

@[simp] theorem rightChiralStarLinear_apply (X Y : ChiralMatrix) :
    rightChiralStarLinear Y X = rightChiralStar Y X := by
  change rightChiralStar Y X = rightChiralStar Y X
  rfl

/-! ## Doubled chiral operator -/

def conjChiral (X : ChiralMatrix) : ChiralMatrix := star X

@[simp] theorem conjChiral_involutive (X : ChiralMatrix) :
    conjChiral (conjChiral X) = X := by
  simp [conjChiral]

def chiralGamma (X : ChiralMatrix) :
    (ChiralMatrix × ChiralMatrix) →ₗ[ℝ]
      (ChiralMatrix × ChiralMatrix) where
  toFun p :=
    (leftChiralStar X p.2, leftChiralStar (conjChiral X) p.1)
  map_add' p q := by
    apply Prod.ext
    · simp [leftChiralStar_add_right, QuaternionAlgebra.re_star,
        QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
        QuaternionAlgebra.imK_star]
    · simp [leftChiralStar_add_right, QuaternionAlgebra.re_star,
        QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
        QuaternionAlgebra.imK_star]
  map_smul' a p := by
    apply Prod.ext
    · simp [leftChiralStar_smul_right]
    · simp [leftChiralStar_smul_right]

@[simp] theorem chiralGamma_apply (X : ChiralMatrix)
    (u v : ChiralMatrix) :
    chiralGamma X (u, v) =
      (leftChiralStar X v, leftChiralStar (conjChiral X) u) :=
  rfl

theorem chiralGamma_add (X Y : ChiralMatrix) :
    chiralGamma (X + Y) = chiralGamma X + chiralGamma Y := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext
  · exact leftChiralStar_add_left X Y v
  · simpa [chiralGamma, conjChiral] using leftChiralStar_add_left (star X) (star Y) u

theorem chiralGamma_smul (r : ℝ) (X : ChiralMatrix) :
    chiralGamma (r • X) = r • chiralGamma X := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  apply Prod.ext
  · exact leftChiralStar_smul_left r X v
  · change leftChiralStar (star (r • X)) u = r • leftChiralStar (star X) u
    have hstar : star (r • X) = r • star X := by
      apply Matrix.ext
      intro i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    rw [hstar]
    exact leftChiralStar_smul_left r (star X) u

def chiralGammaLinear :
    ChiralMatrix →ₗ[ℝ]
      ((ChiralMatrix × ChiralMatrix) →ₗ[ℝ] (ChiralMatrix × ChiralMatrix)) where
  toFun := chiralGamma
  map_add' := chiralGamma_add
  map_smul' r X := chiralGamma_smul r X

@[simp] theorem chiralGammaLinear_apply (X : ChiralMatrix) :
    chiralGammaLinear X = chiralGamma X := rfl

theorem chiralGamma_square_apply
    (X : ChiralMatrix) (u v : ChiralMatrix) :
    (chiralGamma X ∘ₗ chiralGamma X) (u, v) =
      (leftChiralStar X
          (leftChiralStar (conjChiral X) u),
        leftChiralStar (conjChiral X)
          (leftChiralStar X v)) := by
  rfl

theorem chiralGamma_square
    (X : ChiralMatrix) (n : ℝ)
    (hleft : ∀ u : ChiralMatrix,
      leftChiralStar X
          (leftChiralStar (conjChiral X) u) = n • u)
    (hright : ∀ u : ChiralMatrix,
      leftChiralStar (conjChiral X)
          (leftChiralStar X u) = n • u) :
    chiralGamma X ∘ₗ chiralGamma X =
      n • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  rw [chiralGamma_square_apply, hleft u, hright v]
  simp [LinearMap.id_apply]

theorem no_chiralNorm_left_conjChiral :
    ¬ ∃ n : ℝ, ∀ u : ChiralMatrix,
      leftChiralStar (uPlus)
          (leftChiralStar (conjChiral uPlus) u) = n • u := by
  rintro ⟨n, h⟩
  have hp := congrArg (fun M : ChiralMatrix => M 0 0) (h uPlus)
  have hm := congrArg (fun M : ChiralMatrix => M 1 1) (h uMinus)
  simp [leftChiralStar, conjChiral, chiralStar, uPlus, uMinus,
    rhoPlus, rhoMinus, entryZero, entryOne] at hp hm
  have hp_re := congrArg (fun q : ChiralEntry => q.re) hp
  have hm_re := congrArg (fun q : ChiralEntry => q.re) hm
  simp at hp_re hm_re
  linarith

theorem rightChiralStar_apply (X Y : ChiralMatrix) :
    rightChiralStar Y X = chiralStar X Y := rfl

theorem leftRightStar_defect (X Y Z : ChiralMatrix) :
    leftChiralStar X (rightChiralStar Y Z) -
        rightChiralStar Y (leftChiralStar X Z) =
      chiralStar X (chiralStar Z Y) - chiralStar (chiralStar X Z) Y := rfl

theorem leftRightCommutatorDefect_eq_neg_chiralAssociator
    (X Y Z : ChiralMatrix) :
    leftRightCommutatorDefect X Y Z = -chiralAssociator X Z Y := by
  simp [leftRightCommutatorDefect, rightChiralStar, leftChiralStar,
    chiralAssociator, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/- The defect is a genuine linear operator in the acted-on variable. -/
def leftRightCommutatorDefectLinear (X Y : ChiralMatrix) :
    ChiralMatrix →ₗ[ℝ] ChiralMatrix :=
  leftChiralStarLinear X ∘ₗ rightChiralStarLinear Y -
    rightChiralStarLinear Y ∘ₗ leftChiralStarLinear X

@[simp] theorem leftRightCommutatorDefectLinear_apply
    (X Y Z : ChiralMatrix) :
    leftRightCommutatorDefectLinear X Y Z = leftRightCommutatorDefect X Y Z := by
  rfl

theorem leftRightCommutatorDefectLinear_eq_neg_associator
    (X Y Z : ChiralMatrix) :
    leftRightCommutatorDefectLinear X Y Z = -chiralAssociator X Z Y := by
  rw [leftRightCommutatorDefectLinear_apply,
    leftRightCommutatorDefect_eq_neg_chiralAssociator]

theorem leftProductDefect_apply (X Y Z : ChiralMatrix) :
    leftProductDefect X Y Z = chiralAssociator X Y Z := rfl

theorem leftProductDefectLinear_eq_associator
    (X Y Z : ChiralMatrix) :
    leftProductDefectLinear X Y Z = chiralAssociator X Y Z := by
  rw [leftProductDefectLinear_apply, leftProductDefect_apply]

theorem leftRightCommutatorDefect_apply (X Y Z : ChiralMatrix) :
    leftRightCommutatorDefect X Y Z =
      chiralStar X (chiralStar Z Y) - chiralStar (chiralStar X Z) Y := rfl

theorem sheetCommutantDefect_apply (a b : Fin 4) (Z : ChiralMatrix) :
    sheetCommutantDefect a b Z =
      chiralStar (sheetPlus a) (chiralStar Z (sheetMinus b)) -
        chiralStar (chiralStar (sheetPlus a) Z) (sheetMinus b) := rfl

@[simp] theorem chiralStar_zero_left (X : ChiralMatrix) :
    chiralStar 0 X = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half]

@[simp] theorem chiralStar_zero_right (X : ChiralMatrix) :
    chiralStar X 0 = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half]

theorem chiralStar_uOne_uTwo : chiralStar uOne uTwo = vThree := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, uTwo, vThree, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uTwo_uThree : chiralStar uTwo uThree = vOne := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uTwo, uThree, vOne, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uThree_uOne : chiralStar uThree uOne = vTwo := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uThree, uOne, vTwo, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uTwo_uOne : chiralStar uTwo uOne = -vThree := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uTwo, uOne, vThree, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uThree_uTwo : chiralStar uThree uTwo = -vOne := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uThree, uTwo, vOne, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uOne_uThree : chiralStar uOne uThree = -vTwo := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, uThree, vTwo, entryZero, entryI, entryJ,
      entryK] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, entryOne]

theorem chiralStar_uOne_uTwo_commutator :
    chiralStar uOne uTwo - chiralStar uTwo uOne = 2 • vThree := by
  rw [chiralStar_uOne_uTwo, chiralStar_uTwo_uOne]
  module

theorem chiralStar_uTwo_uThree_commutator :
    chiralStar uTwo uThree - chiralStar uThree uTwo = 2 • vOne := by
  rw [chiralStar_uTwo_uThree, chiralStar_uThree_uTwo]
  module

theorem chiralStar_uThree_uOne_commutator :
    chiralStar uThree uOne - chiralStar uOne uThree = 2 • vTwo := by
  rw [chiralStar_uThree_uOne, chiralStar_uOne_uThree]
  module

theorem chiralStar_uOne_uTwo_anticommutator :
    chiralStar uOne uTwo + chiralStar uTwo uOne = 0 := by
  rw [chiralStar_uOne_uTwo, chiralStar_uTwo_uOne]
  module

theorem chiralStar_uTwo_uThree_anticommutator :
    chiralStar uTwo uThree + chiralStar uThree uTwo = 0 := by
  rw [chiralStar_uTwo_uThree, chiralStar_uThree_uTwo]
  module

theorem chiralStar_uThree_uOne_anticommutator :
    chiralStar uThree uOne + chiralStar uOne uThree = 0 := by
  rw [chiralStar_uThree_uOne, chiralStar_uOne_uThree]
  module

theorem chiralStar_uOne_vOne : chiralStar uOne vOne = -rhoPlus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoPlus, entryZero, entryOne, entryI] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]

theorem chiralStar_vOne_uOne : chiralStar vOne uOne = -rhoMinus := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralStar, half, uOne, vOne, rhoMinus, entryZero, entryOne, entryI] <;>
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul]

theorem chiralStar_uOne_vOne_anticommutator :
    chiralStar uOne vOne + chiralStar vOne uOne = -chiralOne := by
  rw [chiralStar_uOne_vOne, chiralStar_vOne_uOne]
  simp [chiralOne, uPlus, uMinus]
  module

theorem chiralStar_uOne_vOne_commutator :
    chiralStar uOne vOne - chiralStar vOne uOne = -ell := by
  rw [chiralStar_uOne_vOne, chiralStar_vOne_uOne]
  change -rhoPlus - -rhoMinus = -(rhoPlus - rhoMinus)
  simp only [sub_neg_eq_add, sub_eq_add_neg]
  module

theorem chiralStar_associator_uOne_uTwo_uThree :
    chiralStar (chiralStar uOne uTwo) uThree ≠
      chiralStar uOne (chiralStar uTwo uThree) := by
  intro h
  have h00 := congrArg (fun M : ChiralMatrix => M 0 0) h
  have h00' := congrArg (fun q : ChiralEntry => q.re) h00
  norm_num [chiralStar_uOne_uTwo, chiralStar_uOne_vOne, rhoMinus, rhoPlus,
    chiralStar, half, uOne, uTwo, uThree, vThree, entryZero, entryOne,
    entryI, entryJ, entryK] at h00'

theorem chiralAssociator_uOne_uTwo_uThree_ne_zero :
    chiralAssociator uOne uTwo uThree ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : ChiralMatrix => M 0 0) h
  have h00' := congrArg (fun q : ChiralEntry => q.re) h00
  norm_num [chiralAssociator, chiralStar_uOne_uTwo, chiralStar_uOne_vOne,
    rhoMinus, rhoPlus, chiralStar, half, uOne, uTwo, uThree, vThree,
    entryZero, entryOne, entryI, entryJ, entryK] at h00'

end
end InfoGeometry.Clifford.SplitOctonionChiralMatrixReadout
