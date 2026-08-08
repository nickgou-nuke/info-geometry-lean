import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Physics.YangBaxterZornBridge
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Functor.OfSequence

noncomputable section

namespace InfoGeometry.Categorical.ZornUHFColimit

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open scoped MonoidalCategory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.YangBaxterZornBridge

abbrev FinZorn := Fin 8 → ℂ
abbrev ZornStage (n : ℕ) := BitWord n → FinZorn

/-- Zorn multiplication transported to the standard eight-dimensional complex module. -/
def finZornMul (x y : FinZorn) : FinZorn :=
  zornToFin8 (zornMul (fin8ToZorn x) (fin8ToZorn y))

@[simp] theorem finZornMul_zero_left (x : FinZorn) : finZornMul 0 x = 0 := by
  simp [finZornMul, fin8ToZorn, zornMul, zornToFin8, dot3, cross3]

@[simp] theorem finZornMul_zero_right (x : FinZorn) : finZornMul x 0 = 0 := by
  simp [finZornMul, fin8ToZorn, zornMul, zornToFin8, dot3, cross3]

theorem fin8ToZorn_add (x y : FinZorn) :
    fin8ToZorn (x + y) = zornAdd (fin8ToZorn x) (fin8ToZorn y) := by
  apply zorn_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem fin8ToZorn_smul (c : ℂ) (x : FinZorn) :
    fin8ToZorn (c • x) = zornSmul c (fin8ToZorn x) := by
  apply zorn_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem finZornMul_add_left (x y z : FinZorn) :
    finZornMul (x + y) z = finZornMul x z + finZornMul y z := by
  unfold finZornMul
  rw [fin8ToZorn_add]
  rw [add_zornMul, zornToFin8_add]

theorem finZornMul_add_right (x y z : FinZorn) :
    finZornMul x (y + z) = finZornMul x y + finZornMul x z := by
  unfold finZornMul
  rw [fin8ToZorn_add]
  rw [zornMul_add, zornToFin8_add]

theorem finZornMul_smul_left (c : ℂ) (x y : FinZorn) :
    finZornMul (c • x) y = c • finZornMul x y := by
  unfold finZornMul
  rw [fin8ToZorn_smul]
  rw [smul_zornMul, zornToFin8_smul]

theorem finZornMul_smul_right (c : ℂ) (x y : FinZorn) :
    finZornMul x (c • y) = c • finZornMul x y := by
  unfold finZornMul
  rw [fin8ToZorn_smul]
  rw [zornMul_smul, zornToFin8_smul]

/-- Restriction along a finite-prefix inclusion. -/
def prefixLE {n m : ℕ} (h : n ≤ m) (w : BitWord m) : BitWord n :=
  fun i => w ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩

@[simp] theorem prefixLE_refl (n : ℕ) (w : BitWord n) : prefixLE (le_refl n) w = w := rfl

@[simp] theorem prefixLE_trans {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (w : BitWord k) :
    prefixLE h (prefixLE g w) = prefixLE (h.trans g) w := rfl

/-- The complex-linear bonding map for every `n ≤ m`. -/
def stageBondLinear {n m : ℕ} (h : n ≤ m) : ZornStage n →ₗ[ℂ] ZornStage m where
  toFun f w := f (prefixLE h w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem stageBondLinear_apply {n m : ℕ} (h : n ≤ m) (f : ZornStage n)
    (w : BitWord m) : stageBondLinear h f w = f (prefixLE h w) := rfl

/-- The filtered `ModuleCat ℂ` diagram of finite Zorn-valued diagonal stages. -/
def zornStageFunctor : ℕ ⥤ ModuleCat ℂ where
  obj n := ModuleCat.of ℂ (ZornStage n)
  map f := ModuleCat.ofHom (stageBondLinear (leOfHom f))
  map_id n := by ext f w; rfl
  map_comp f g := by ext x w; rfl

@[simp] theorem zornStageFunctor_map_apply {n m : ℕ} (f : n ⟶ m) (x : ZornStage n)
    (w : BitWord m) :
    zornStageFunctor.map f x w = x (prefixLE (leOfHom f) w) := rfl

/-- Pointwise Zorn multiplication as a bilinear morphism at finite stage `n`. -/
def stageMul (n : ℕ) : zornStageFunctor.obj n ⊗ zornStageFunctor.obj n ⟶
    zornStageFunctor.obj n :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun x y w => finZornMul (x w) (y w))
    (fun x y z => by funext w; exact finZornMul_add_left (x w) (y w) (z w))
    (fun c x y => by funext w; exact finZornMul_smul_left c (x w) (y w))
    (fun x y z => by funext w; exact finZornMul_add_right (x w) (y w) (z w))
    (fun c x y => by funext w; exact finZornMul_smul_right c (x w) (y w))

@[simp] theorem stageMul_tmul (n : ℕ) (x y : ZornStage n) (w : BitWord n) :
    stageMul n (x ⊗ₜ[ℂ] y) w = finZornMul (x w) (y w) := rfl

/-- Every bonding map is a homomorphism for the pointwise nonassociative product. -/
theorem stageMul_naturality {n m : ℕ} (f : n ⟶ m) :
    (zornStageFunctor.map f ⊗ₘ zornStageFunctor.map f) ≫ stageMul m =
      stageMul n ≫ zornStageFunctor.map f := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  funext w
  rfl

/-- The genuine Mathlib categorical colimit of the finite diagonal modules. -/
abbrev ZornColimit := colimit zornStageFunctor

@[simp] theorem colimit_ι_map_apply {n m : ℕ} (f : n ⟶ m) (x : ZornStage n) :
    colimit.ι zornStageFunctor m (zornStageFunctor.map f x) =
      colimit.ι zornStageFunctor n x := by
  simpa using congr_fun
    (congrArg (fun q : zornStageFunctor.obj n ⟶ ZornColimit =>
      (q : zornStageFunctor.obj n → ZornColimit)) (colimit.w zornStageFunctor f)) x

/-- Multiply representatives from two stages after transporting them to their common stage. -/
def pairMul (n m : ℕ) :
    zornStageFunctor.obj n ⊗ zornStageFunctor.obj m ⟶ ZornColimit :=
  let N := max n m
  (zornStageFunctor.map (homOfLE (le_max_left n m)) ⊗ₘ
      zornStageFunctor.map (homOfLE (le_max_right n m))) ≫
    stageMul N ≫ colimit.ι zornStageFunctor N

@[simp] theorem pairMul_tmul (n m : ℕ) (x : ZornStage n) (y : ZornStage m) :
    pairMul n m (x ⊗ₜ[ℂ] y) =
      colimit.ι zornStageFunctor (max n m)
        (fun w => finZornMul
          (x (prefixLE (le_max_left n m) w))
          (y (prefixLE (le_max_right n m) w))) := rfl

theorem pairMul_naturality_right (n : ℕ) {m k : ℕ} (f : m ⟶ k) :
    (𝟙 (zornStageFunctor.obj n) ⊗ₘ zornStageFunctor.map f) ≫ pairMul n k =
      pairMul n m := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change pairMul n k (x ⊗ₜ[ℂ] zornStageFunctor.map f y) = pairMul n m (x ⊗ₜ[ℂ] y)
  rw [pairMul_tmul, pairMul_tmul]
  let hNM : max n m ≤ max n k :=
    max_le (le_max_left n k) ((leOfHom f).trans (le_max_right n k))
  rw [← colimit_ι_map_apply (homOfLE hNM)]
  congr 1

theorem pairMul_naturality_left {n k : ℕ} (f : n ⟶ k) (m : ℕ) :
    (zornStageFunctor.map f ⊗ₘ 𝟙 (zornStageFunctor.obj m)) ≫ pairMul k m =
      pairMul n m := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change pairMul k m (zornStageFunctor.map f x ⊗ₜ[ℂ] y) = pairMul n m (x ⊗ₜ[ℂ] y)
  rw [pairMul_tmul, pairMul_tmul]
  let hNM : max n m ≤ max k m :=
    max_le ((leOfHom f).trans (le_max_left k m)) (le_max_right k m)
  rw [← colimit_ι_map_apply (homOfLE hNM)]
  congr 1

/-- For fixed left stage `n`, the common-stage products form a cocone in the right variable. -/
def rightMulCocone (n : ℕ) :
    Cocone (zornStageFunctor ⋙ MonoidalCategory.tensorLeft (zornStageFunctor.obj n)) where
  pt := ZornColimit
  ι :=
    { app := pairMul n
      naturality := fun _ _ f => pairMul_naturality_right n f }

/-- Tensoring by a fixed stage preserves the filtered colimit. -/
def rightTensorColimit (n : ℕ) :
    IsColimit ((MonoidalCategory.tensorLeft (zornStageFunctor.obj n)).mapCocone
      (colimit.cocone zornStageFunctor)) :=
  isColimitOfPreserves (MonoidalCategory.tensorLeft (zornStageFunctor.obj n))
    (colimit.isColimit zornStageFunctor)

/-- First universal descent: multiplication by a finite-stage element on the left. -/
def rightDesc (n : ℕ) : zornStageFunctor.obj n ⊗ ZornColimit ⟶ ZornColimit :=
  (rightTensorColimit n).desc (rightMulCocone n)

@[reassoc (attr := simp)] theorem rightDesc_fac (n m : ℕ) :
    (𝟙 (zornStageFunctor.obj n) ⊗ₘ colimit.ι zornStageFunctor m) ≫ rightDesc n =
      pairMul n m := by
  exact (rightTensorColimit n).fac (rightMulCocone n) m

theorem rightDesc_naturality {n k : ℕ} (f : n ⟶ k) :
    (zornStageFunctor.map f ⊗ₘ 𝟙 ZornColimit) ≫ rightDesc k = rightDesc n := by
  apply (rightTensorColimit n).hom_ext
  intro m
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have hk := LinearMap.congr_fun
    (congrArg (fun q : zornStageFunctor.obj k ⊗ zornStageFunctor.obj m ⟶ ZornColimit =>
      q.hom) (rightDesc_fac k m))
    (zornStageFunctor.map f x ⊗ₜ[ℂ] y)
  have hn := LinearMap.congr_fun
    (congrArg (fun q : zornStageFunctor.obj n ⊗ zornStageFunctor.obj m ⟶ ZornColimit =>
      q.hom) (rightDesc_fac n m))
    (x ⊗ₜ[ℂ] y)
  have hpair := LinearMap.congr_fun
    (congrArg (fun q : zornStageFunctor.obj n ⊗ zornStageFunctor.obj m ⟶ ZornColimit =>
      q.hom) (pairMul_naturality_left f m))
    (x ⊗ₜ[ℂ] y)
  simpa using hk.trans (hpair.trans hn.symm)

/-- The once-descended products form a cocone in the left stage variable. -/
def leftMulCocone :
    Cocone (zornStageFunctor ⋙ MonoidalCategory.tensorRight ZornColimit) where
  pt := ZornColimit
  ι :=
    { app := rightDesc
      naturality := fun _ _ f => rightDesc_naturality f }

/-- Right tensoring preserves this colimit by transport across the braided symmetry. -/
instance preservesColimit_zornStageFunctor_tensorRight :
    PreservesColimit zornStageFunctor
      (MonoidalCategory.tensorRight ZornColimit) :=
  preservesColimit_of_natIso zornStageFunctor
    (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight ZornColimit)

/-- Tensoring the filtered colimit on the right also preserves its universal property. -/
def leftTensorColimit :
    IsColimit ((MonoidalCategory.tensorRight ZornColimit).mapCocone
      (colimit.cocone zornStageFunctor)) :=
  isColimitOfPreserves (MonoidalCategory.tensorRight ZornColimit)
    (colimit.isColimit zornStageFunctor)

/-- Multiplication on the categorical colimit, descended through the tensor universal property. -/
def colimitMul : ZornColimit ⊗ ZornColimit ⟶ ZornColimit :=
  leftTensorColimit.desc leftMulCocone

@[reassoc (attr := simp)] theorem colimitMul_fac_left (n : ℕ) :
    (colimit.ι zornStageFunctor n ⊗ₘ 𝟙 ZornColimit) ≫ colimitMul = rightDesc n := by
  exact leftTensorColimit.fac leftMulCocone n

/-- Finite-stage readback for multiplication descended to the categorical colimit. -/
theorem colimitMul_ι_tmul_ι (n m : ℕ) (x : ZornStage n) (y : ZornStage m) :
    colimitMul
        (colimit.ι zornStageFunctor n x ⊗ₜ[ℂ] colimit.ι zornStageFunctor m y) =
      pairMul n m (x ⊗ₜ[ℂ] y) := by
  calc
    colimitMul
        (colimit.ι zornStageFunctor n x ⊗ₜ[ℂ] colimit.ι zornStageFunctor m y) =
        rightDesc n (x ⊗ₜ[ℂ] colimit.ι zornStageFunctor m y) := by
      simpa using LinearMap.congr_fun
        (congrArg (fun q : zornStageFunctor.obj n ⊗ ZornColimit ⟶ ZornColimit =>
          q.hom)
          (colimitMul_fac_left n)) (x ⊗ₜ[ℂ] colimit.ι zornStageFunctor m y)
    _ = pairMul n m (x ⊗ₜ[ℂ] y) := by
      simpa using LinearMap.congr_fun
        (congrArg (fun q : zornStageFunctor.obj n ⊗ zornStageFunctor.obj m ⟶ ZornColimit =>
          q.hom)
          (rightDesc_fac n m)) (x ⊗ₜ[ℂ] y)

/-- The elementwise product induced by the descended tensor morphism. -/
def colimitProduct (x y : ZornColimit) : ZornColimit := colimitMul (x ⊗ₜ[ℂ] y)

theorem colimitProduct_add_left (x y z : ZornColimit) :
    colimitProduct (x + y) z = colimitProduct x z + colimitProduct y z := by
  unfold colimitProduct
  rw [TensorProduct.add_tmul]
  exact colimitMul.hom.map_add (x ⊗ₜ[ℂ] z) (y ⊗ₜ[ℂ] z)

theorem colimitProduct_add_right (x y z : ZornColimit) :
    colimitProduct x (y + z) = colimitProduct x y + colimitProduct x z := by
  unfold colimitProduct
  rw [TensorProduct.tmul_add]
  exact colimitMul.hom.map_add (x ⊗ₜ[ℂ] y) (x ⊗ₜ[ℂ] z)

theorem colimitProduct_smul_left (c : ℂ) (x y : ZornColimit) :
    colimitProduct (c • x) y = c • colimitProduct x y := by
  unfold colimitProduct
  rw [← TensorProduct.smul_tmul']
  change colimitMul.hom (c • (x ⊗ₜ[ℂ] y)) = c • colimitMul.hom (x ⊗ₜ[ℂ] y)
  exact colimitMul.hom.map_smul c (x ⊗ₜ[ℂ] y)

theorem colimitProduct_smul_right (c : ℂ) (x y : ZornColimit) :
    colimitProduct x (c • y) = c • colimitProduct x y := by
  simp [colimitProduct, TensorProduct.tmul_smul]

instance : Mul ZornColimit := ⟨colimitProduct⟩

instance : NonUnitalNonAssocRing ZornColimit where
  zero_mul x := by simp [HMul.hMul, Mul.mul, colimitProduct]
  mul_zero x := by simp [HMul.hMul, Mul.mul, colimitProduct]
  left_distrib := colimitProduct_add_right
  right_distrib := colimitProduct_add_left

instance : IsScalarTower ℂ ZornColimit ZornColimit where
  smul_assoc := colimitProduct_smul_left

instance : SMulCommClass ℂ ZornColimit ZornColimit where
  smul_comm c x y := by
    rw [smul_eq_mul, smul_eq_mul]
    change c • colimitProduct x y = colimitProduct x (c • y)
    exact (colimitProduct_smul_right c x y).symm

/-- Native multiplication readback for representatives inserted from arbitrary finite stages. -/
theorem colimit_mul_ι_ι (n m : ℕ) (x : ZornStage n) (y : ZornStage m) :
    colimit.ι zornStageFunctor n x * colimit.ι zornStageFunctor m y =
      pairMul n m (x ⊗ₜ[ℂ] y) := by
  change colimitProduct
    (colimit.ι zornStageFunctor n x) (colimit.ι zornStageFunctor m y) = _
  exact colimitMul_ι_tmul_ι n m x y

/-- At one finite stage, native colimit multiplication is exactly the injected pointwise product. -/
theorem colimit_mul_ι_same_stage (n : ℕ) (x y : ZornStage n) :
    colimit.ι zornStageFunctor n x * colimit.ι zornStageFunctor n y =
      colimit.ι zornStageFunctor n (fun w => finZornMul (x w) (y w)) := by
  rw [colimit_mul_ι_ι, pairMul_tmul]
  rw [← colimit_ι_map_apply (homOfLE (le_max_left n n))]
  congr 1

/-- The finite eight-coordinate image of the concrete nonzero Zorn nilpotent. -/
def finZornNilpotent : FinZorn := zornToFin8 zornNilpotent

@[simp] theorem finZornNilpotent_sq_zero :
    finZornMul finZornNilpotent finZornNilpotent = 0 := by
  unfold finZornMul finZornNilpotent
  simp only [fin8ToZorn_zornToFin8]
  rw [zornNilpotent_sq_zero]
  funext i
  fin_cases i <;> rfl

/-- The same concrete nilpotent, viewed as a constant observable at finite stage `n`. -/
def nilpotentStage (n : ℕ) : ZornStage n := fun _ => finZornNilpotent

@[simp] theorem nilpotentStage_bond {n m : ℕ} (f : n ⟶ m) :
    zornStageFunctor.map f (nilpotentStage n) = nilpotentStage m := rfl

@[simp] theorem nilpotentStage_sq_zero (n : ℕ) :
    (fun w => finZornMul (nilpotentStage n w) (nilpotentStage n w)) = 0 := by
  funext w
  exact finZornNilpotent_sq_zero

/-- The nilpotent seed transported through the canonical colimit injection. -/
def colimitNilpotent : ZornColimit :=
  colimit.ι zornStageFunctor 0 (nilpotentStage 0)

/-- Every finite constant representative defines the same colimit seed. -/
theorem colimitNilpotent_eq_stage (n : ℕ) :
    colimitNilpotent = colimit.ι zornStageFunctor n (nilpotentStage n) := by
  rw [← nilpotentStage_bond (homOfLE (Nat.zero_le n)), colimit_ι_map_apply]
  rfl

/-- The transported Zorn seed is genuinely square-zero in the categorical colimit algebra. -/
theorem colimitNilpotent_sq_zero : colimitNilpotent * colimitNilpotent = 0 := by
  change colimitProduct colimitNilpotent colimitNilpotent = 0
  unfold colimitProduct colimitNilpotent
  rw [colimitMul_ι_tmul_ι, pairMul_tmul]
  have hzero :
      (fun w : BitWord (max 0 0) =>
        finZornMul
          (nilpotentStage 0 (prefixLE (le_max_left 0 0) w))
          (nilpotentStage 0 (prefixLE (le_max_right 0 0) w))) = 0 := by
    funext w
    exact finZornNilpotent_sq_zero
  rw [hzero]
  change (colimit.ι zornStageFunctor 0).hom 0 = 0
  exact (colimit.ι zornStageFunctor 0).hom.map_zero

end InfoGeometry.Categorical.ZornUHFColimit
