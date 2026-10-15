import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Topology.DelaunayFlipMatrixEmbeddings

/-!
# InfoGeometry.Sandbox.FibonacciGrothendieckSemiringEquiv

Bijectivity and additive/multiplicative equivalence for `FibonacciK0 ≃+ FibonacciRingModel`,
induced fusion-ring operations on `FibonacciK0`, compatibility with `tensorTauK0`,
and local 2×2 block insertion evaluation identities for `embedBlock₂`.
-/

set_option autoImplicit false

namespace InfoGeometry.Algebra.FibonacciGrothendieckRing

/-! ## 1. Bijectivity & Additive Isomorphism `FibonacciK0 ≃+ FibonacciRingModel` -/

/-- Evaluation of `k0ToModel` on a quotient representative. -/
theorem k0ToModel_mk (x : FibFusionMonoid × FibFusionMonoid) :
    k0ToModel (Quotient.mk (grothendieckSetoid FibFusionMonoid) x) =
      rawToModel x.1 - rawToModel x.2 :=
  rfl

/-- `k0ToModel` is injective. -/
theorem k0ToModel_injective : Function.Injective k0ToModel := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂
    (s₁ := grothendieckSetoid FibFusionMonoid)
    (s₂ := grothendieckSetoid FibFusionMonoid) a b ?_
  intro x y h
  have h1 : (x.1.1 : Int) - (x.2.1 : Int) = (y.1.1 : Int) - (y.2.1 : Int) := by
    exact congrArg Prod.fst h
  have h2 : (x.1.2 : Int) - (x.2.2 : Int) = (y.1.2 : Int) - (y.2.2 : Int) := by
    exact congrArg Prod.snd h
  apply Quotient.sound
  use (0, 0)
  apply Prod.ext
  · change x.1.1 + y.2.1 + 0 = x.2.1 + y.1.1 + 0
    omega
  · change x.1.2 + y.2.2 + 0 = x.2.2 + y.1.2 + 0
    omega

/-- `k0ToModel` is surjective. -/
theorem k0ToModel_surjective : Function.Surjective k0ToModel := by
  intro p
  rcases p with ⟨a, b⟩
  use Quotient.mk (grothendieckSetoid FibFusionMonoid)
    ((a.toNat, b.toNat), ((-a).toNat, (-b).toNat))
  rw [k0ToModel_mk]
  apply Prod.ext
  · change (a.toNat : Int) - ((-a).toNat : Int) = a
    omega
  · change (b.toNat : Int) - ((-b).toNat : Int) = b
    omega

/-- Additive isomorphism between `FibonacciK0` and `FibonacciRingModel`. -/
noncomputable def fibonacciK0AddEquiv : FibonacciK0 ≃+ FibonacciRingModel :=
  AddEquiv.ofBijective k0ToModel ⟨k0ToModel_injective, k0ToModel_surjective⟩

@[simp]
theorem fibonacciK0AddEquiv_apply (x : FibonacciK0) :
    fibonacciK0AddEquiv x = k0ToModel x :=
  rfl

@[simp]
theorem k0ToModel_fibonacciK0AddEquiv_symm (y : FibonacciRingModel) :
    k0ToModel (fibonacciK0AddEquiv.symm y) = y :=
  fibonacciK0AddEquiv.apply_symm_apply y

@[simp]
theorem fibonacciK0AddEquiv_symm_k0ToModel (x : FibonacciK0) :
    fibonacciK0AddEquiv.symm (k0ToModel x) = x :=
  fibonacciK0AddEquiv.symm_apply_apply x

/-! ## 2. Induced Multiplication & Ring Identities on `FibonacciK0` -/

/-- Multiplication on `FibonacciK0` induced via `fibonacciK0AddEquiv`. -/
noncomputable def k0Mul (x y : FibonacciK0) : FibonacciK0 :=
  fibonacciK0AddEquiv.symm (FibonacciRingModel.mul (fibonacciK0AddEquiv x) (fibonacciK0AddEquiv y))

@[simp]
theorem k0ToModel_k0Mul (x y : FibonacciK0) :
    k0ToModel (k0Mul x y) = FibonacciRingModel.mul (k0ToModel x) (k0ToModel y) := by
  dsimp [k0Mul]
  exact fibonacciK0AddEquiv.apply_symm_apply
    (FibonacciRingModel.mul (fibonacciK0AddEquiv x) (fibonacciK0AddEquiv y))

/-- The Fibonacci fusion rule directly in `FibonacciK0`: `τ * τ = τ + 1`. -/
theorem k0Mul_tau_tau : k0Mul fibTauK0 fibTauK0 = fibTauK0 + fibOneK0 := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, k0ToModel_tau, k0ToModel_one, FibonacciRingModel.tau_mul_tau]

theorem k0Mul_comm (x y : FibonacciK0) : k0Mul x y = k0Mul y x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_k0Mul, FibonacciRingModel.mul_comm]

theorem k0Mul_assoc (x y z : FibonacciK0) : k0Mul (k0Mul x y) z = k0Mul x (k0Mul y z) := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_k0Mul, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.mul_assoc]

@[simp]
theorem one_k0Mul (x : FibonacciK0) : k0Mul fibOneK0 x = x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_one, FibonacciRingModel.one_mul]

@[simp]
theorem k0Mul_one (x : FibonacciK0) : k0Mul x fibOneK0 = x := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, k0ToModel_one, FibonacciRingModel.mul_one]

theorem k0Mul_left_distrib (x y z : FibonacciK0) :
    k0Mul x (y + z) = k0Mul x y + k0Mul x z := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, map_add, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.left_distrib]

theorem k0Mul_right_distrib (x y z : FibonacciK0) :
    k0Mul (x + y) z = k0Mul x z + k0Mul y z := by
  apply k0ToModel_injective
  rw [k0ToModel_k0Mul, map_add, map_add, k0ToModel_k0Mul, k0ToModel_k0Mul,
    FibonacciRingModel.right_distrib]

/-- Compatibility of `tensorTauK0` with `k0ToModel`. -/
theorem k0ToModel_tensorTauK0 (x : FibonacciK0) :
    k0ToModel (tensorTauK0 x) = FibonacciRingModel.mul (k0ToModel x) FibonacciRingModel.tau := by
  rcases grothendieck_eq_sub x with ⟨a, b, rfl⟩
  simp only [map_sub, tensorTauK0_grothendieckMap, k0ToModel_grothendieckMap, rawToModel_tensorTau]
  ext <;> simp [FibonacciRingModel.mul, FibonacciRingModel.tau]; ring

/-- Tensoring by `τ` in `FibonacciK0` coincides with multiplying by `fibTauK0`. -/
theorem tensorTauK0_eq_k0Mul_tau (x : FibonacciK0) :
    tensorTauK0 x = k0Mul x fibTauK0 := by
  apply k0ToModel_injective
  rw [k0ToModel_tensorTauK0, k0ToModel_k0Mul, k0ToModel_tau]

end InfoGeometry.Algebra.FibonacciGrothendieckRing

namespace InfoGeometry.Topology.Delaunay

open Matrix

/-! ## 3. 2×2 Block Insertion Identities for `embedBlock₂` -/

@[simp]
theorem embedBlock₂_apply_aa (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ) (a b : Fin d) :
    embedBlock₂ d block a b a a = block 0 0 := by
  simp [embedBlock₂]

@[simp]
theorem embedBlock₂_apply_ab (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b a b = block 0 1 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

@[simp]
theorem embedBlock₂_apply_ba (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b b a = block 1 0 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

@[simp]
theorem embedBlock₂_apply_bb (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b b b = block 1 1 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

theorem embedBlock₂_apply_other (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b i j : Fin d) (hia : i ≠ a) (hib : i ≠ b) :
    embedBlock₂ d block a b i j = if i = j then 1 else 0 := by
  simp [embedBlock₂, hia, hib]

/-- Inserting the 2×2 identity matrix at distinct indices `a ≠ b` yields the `d × d` identity matrix. -/
theorem embedBlock₂_one (d : ℕ) (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d 1 a b = 1 := by
  ext i j
  dsimp [embedBlock₂]
  split_ifs <;> simp_all [Matrix.one_apply] <;> tauto

end InfoGeometry.Topology.Delaunay
