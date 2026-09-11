import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.NonAssocDerivation

noncomputable section

namespace InfoGeometry.Algebra.NonAssocDerivationKernel

open InfoGeometry.Algebra

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]
variable [One A]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- A Leibniz endomorphism annihilates the supplied multiplicative unit. -/
theorem map_one_eq_zero_of_isLeibniz
    (D : Module.End R A)
    (hD : NonAssocDerivation.IsLeibniz R A D)
    (unit_mul : ∀ a : A, (1 : A) * a = a)
    (mul_unit : ∀ a : A, a * (1 : A) = a) :
    D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by
    simpa [unit_mul, mul_unit] using hD 1 1
  have h' : D 1 + 0 = D 1 + D 1 := by
    simpa using h
  exact (add_left_cancel h').symm

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem map_smul_one_eq_zero_of_isLeibniz
    (D : Module.End R A)
    (hD : NonAssocDerivation.IsLeibniz R A D)
    (unit_mul : ∀ a : A, (1 : A) * a = a)
    (mul_unit : ∀ a : A, a * (1 : A) = a)
    (c : R) :
    D (c • (1 : A)) = 0 := by
  rw [map_smul]
  rw [map_one_eq_zero_of_isLeibniz D hD unit_mul mul_unit]
  simp

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem scalar_one_mem_ker_of_isLeibniz
    (D : Module.End R A)
    (hD : NonAssocDerivation.IsLeibniz R A D)
    (unit_mul : ∀ a : A, (1 : A) * a = a)
    (mul_unit : ∀ a : A, a * (1 : A) = a)
    (c : R) :
    c • (1 : A) ∈ LinearMap.ker D := by
  exact map_smul_one_eq_zero_of_isLeibniz D hD unit_mul mul_unit c

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem scalar_line_le_ker_of_isLeibniz
    (D : Module.End R A)
    (hD : NonAssocDerivation.IsLeibniz R A D)
    (unit_mul : ∀ a : A, (1 : A) * a = a)
    (mul_unit : ∀ a : A, a * (1 : A) = a) :
    Submodule.span R ({(1 : A)} : Set A) ≤ LinearMap.ker D := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  simpa using scalar_one_mem_ker_of_isLeibniz D hD unit_mul mul_unit 1

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem apply_eq_iff_sub_mem_ker
    (D : Module.End R A) (u₁ u₂ : A) :
    D u₁ = D u₂ ↔ u₁ - u₂ ∈ LinearMap.ker D := by
  constructor
  · intro h
    change D (u₁ - u₂) = 0
    rw [map_sub, h, sub_self]
  · intro h
    have hzero : D (u₁ - u₂) = 0 := h
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem apply_add_eq_of_mem_ker
    (D : Module.End R A) {u k : A}
    (hk : k ∈ LinearMap.ker D) :
    D (u + k) = D u := by
  rw [map_add]
  simpa using hk

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem sub_mem_ker_of_apply_eq
    (D : Module.End R A) {u₁ u₂ : A}
    (h : D u₁ = D u₂) :
    u₁ - u₂ ∈ LinearMap.ker D :=
  (apply_eq_iff_sub_mem_ker D u₁ u₂).mp h

abbrev SolutionFiber (D : Module.End R A) (v : A) :=
  {u : A // D u = v}

def solutionFiberEquivKer
    (D : Module.End R A) (v u₀ : A)
    (hu₀ : D u₀ = v) :
    SolutionFiber D v ≃ LinearMap.ker D where
  toFun u := ⟨u.1 - u₀, sub_mem_ker_of_apply_eq D (u.2.trans hu₀.symm)⟩
  invFun k := ⟨u₀ + k.1, by
    rw [map_add, hu₀]
    rw [show D k.1 = 0 from k.2, add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

@[simp]
theorem solutionFiberEquivKer_apply_val
    (D : Module.End R A) (v u₀ : A)
    (hu₀ : D u₀ = v) (u : SolutionFiber D v) :
    (solutionFiberEquivKer D v u₀ hu₀ u).1 = u.1 - u₀ :=
  rfl

@[simp]
theorem solutionFiberEquivKer_symm_apply_val
    (D : Module.End R A) (v u₀ : A)
    (hu₀ : D u₀ = v) (k : LinearMap.ker D) :
    ((solutionFiberEquivKer D v u₀ hu₀).symm k).1 = u₀ + k.1 :=
  rfl

theorem solution_eq_base_add_kernel
    (D : Module.End R A) (v u₀ : A)
    (hu₀ : D u₀ = v) (u : SolutionFiber D v) :
    u.1 = u₀ + (solutionFiberEquivKer D v u₀ hu₀ u).1 := by
  change u.1 = u₀ + (u.1 - u₀)
  abel

theorem base_add_kernel_mem_solutionFiber
    (D : Module.End R A) (v u₀ : A)
    (hu₀ : D u₀ = v) (k : LinearMap.ker D) :
    D (u₀ + k.1) = v := by
  rw [map_add, hu₀, k.2, add_zero]

/-! ### Generalized kernels of iterated endomorphisms

These are purely linear-algebraic carriers.  They do not identify a
generalized kernel with a physical sector or with a braid representation.
-/

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
abbrev iteratedKernel
    (D : Module.End R A) (n : ℕ) : Submodule R A :=
  LinearMap.ker (D ^ n)

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem mem_iteratedKernel_iff
    (D : Module.End R A) (n : ℕ) (x : A) :
    x ∈ iteratedKernel D n ↔ (D ^ n) x = 0 :=
  Iff.rfl

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
@[simp] theorem iteratedKernel_one
    (D : Module.End R A) :
    iteratedKernel D 1 = LinearMap.ker D := by
  ext x
  simp [iteratedKernel]

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem iteratedKernel_mono
    (D : Module.End R A) {m n : ℕ} (hmn : m ≤ n) :
    iteratedKernel D m ≤ iteratedKernel D n := by
  intro x hx
  change (D ^ n) x = 0
  rw [show n = (n - m) + m by omega, pow_add]
  change (D ^ (n - m)) ((D ^ m) x) = 0
  rw [hx, map_zero]

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem ker_le_iteratedKernel_succ
    (D : Module.End R A) (n : ℕ) :
    LinearMap.ker D ≤ iteratedKernel D (n + 1) := by
  change iteratedKernel D 1 ≤ iteratedKernel D (n + 1)
  simpa [iteratedKernel] using
    iteratedKernel_mono D (show 1 ≤ n + 1 by omega)

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem map_mem_iteratedKernel_succ
    (D : Module.End R A) (n : ℕ) {x : A}
    (hx : x ∈ iteratedKernel D (n + 1)) :
    D x ∈ iteratedKernel D n := by
  change (D ^ n) (D x) = 0
  change (D ^ n * D) x = 0
  rw [← pow_succ]
  exact hx

omit [IsScalarTower R A A] [SMulCommClass R A A] [One A] in
theorem iteratedKernel_succ_eq_comap
    (D : Module.End R A) (n : ℕ) :
    iteratedKernel D (n + 1) =
      (iteratedKernel D n).comap D := by
  ext x
  change (D ^ (n + 1)) x = 0 ↔ D x ∈ iteratedKernel D n
  rw [pow_succ]
  rfl

instance solutionFiberAddAction
    (D : Module.End R A) (v : A) :
    AddAction (LinearMap.ker D) (SolutionFiber D v) where
  vadd k u :=
    ⟨k.1 + u.1, by
      rw [map_add, k.2, zero_add, u.2]⟩
  zero_vadd u := by
    apply Subtype.ext
    change (0 : LinearMap.ker D).1 + u.1 = u.1
    simp
  add_vadd k₁ k₂ u := by
    apply Subtype.ext
    change (k₁.1 + k₂.1) + u.1 = k₁.1 + (k₂.1 + u.1)
    abel

instance solutionFiberVSub
    (D : Module.End R A) (v : A) :
    VSub (LinearMap.ker D) (SolutionFiber D v) where
  vsub u₁ u₂ :=
    ⟨u₁.1 - u₂.1,
      sub_mem_ker_of_apply_eq D (u₁.2.trans u₂.2.symm)⟩

instance solutionFiberAddTorsor
    (D : Module.End R A) (v : A)
    [Nonempty (SolutionFiber D v)] :
    AddTorsor (LinearMap.ker D) (SolutionFiber D v) :=
  AddTorsor.mk
    (fun u₁ u₂ => by
      apply Subtype.ext
      change (u₁.1 - u₂.1) + u₂.1 = u₁.1
      abel)
    (fun k u => by
      apply Subtype.ext
      change (k.1 + u.1) - u.1 = k.1
      abel)

end InfoGeometry.Algebra.NonAssocDerivationKernel
