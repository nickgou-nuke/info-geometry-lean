import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped Matrix

namespace InfoGeometry.Algebra

/-!
# The integral chiral Clifford order

The four standard integral matrices generate an order in `M₂(ℤ)`, not the
whole matrix ring.  Its membership condition is the pair of parity relations
on the diagonal and off-diagonal entries.  This file formalizes that order as
a genuine Mathlib `Subring`.
-/

abbrev Mat₂Z := Matrix (Fin 2) (Fin 2) ℤ

def IsChiralOrderMatrix (A : Mat₂Z) : Prop :=
  Int.ModEq 2 (A 0 0) (A 1 1) ∧
    Int.ModEq 2 (A 0 1) (A 1 0)

def IntegralChiralCliffordOrder : Subring Mat₂Z where
  carrier := {A | IsChiralOrderMatrix A}
  zero_mem' := by
    constructor <;> simp
  one_mem' := by
    constructor <;> simp
  add_mem' := by
    intro A B hA hB
    rcases hA with ⟨hA₀, hA₁⟩
    rcases hB with ⟨hB₀, hB₁⟩
    constructor
    · simpa [IsChiralOrderMatrix] using hA₀.add hB₀
    · simpa [IsChiralOrderMatrix] using hA₁.add hB₁
  neg_mem' := by
    intro A hA
    rcases hA with ⟨hA₀, hA₁⟩
    constructor
    · simpa [IsChiralOrderMatrix] using hA₀.neg
    · simpa [IsChiralOrderMatrix] using hA₁.neg
  mul_mem' := by
    intro A B hA hB
    rcases hA with ⟨hA₀, hA₁⟩
    rcases hB with ⟨hB₀, hB₁⟩
    constructor
    · change Int.ModEq 2 ((A * B) 0 0) ((A * B) 1 1)
      simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm,
        add_left_comm, add_assoc] using
        (hA₀.mul hB₀).add (hA₁.mul hB₁.symm)
    · change Int.ModEq 2 ((A * B) 0 1) ((A * B) 1 0)
      simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm,
        add_left_comm, add_assoc] using
        (hA₀.mul hB₁).add (hA₁.mul hB₀.symm)

theorem mem_integralChiralCliffordOrder (A : Mat₂Z) :
    A ∈ IntegralChiralCliffordOrder ↔ IsChiralOrderMatrix A :=
  Iff.rfl

def chiralIdentity : Mat₂Z := !![(1 : ℤ), 0; 0, 1]

def chiralHyperbolic : Mat₂Z := !![(1 : ℤ), 0; 0, -1]

def chiralCompact : Mat₂Z := !![(0 : ℤ), -1; 1, 0]

def chiralMixing : Mat₂Z := !![(0 : ℤ), 1; 1, 0]

theorem chiral_generators_mem_order :
    chiralIdentity ∈ IntegralChiralCliffordOrder ∧
    chiralHyperbolic ∈ IntegralChiralCliffordOrder ∧
    chiralCompact ∈ IntegralChiralCliffordOrder ∧
    chiralMixing ∈ IntegralChiralCliffordOrder := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    change IsChiralOrderMatrix _ <;>
    constructor <;> decide

def chiralCombination (x y z w : ℤ) : Mat₂Z :=
  x • chiralIdentity + y • chiralHyperbolic +
    z • chiralCompact + w • chiralMixing

theorem chiralCombination_entries (x y z w : ℤ) :
    chiralCombination x y z w = !![x + y, -z + w; z + w, x - y] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCombination, chiralIdentity, chiralHyperbolic,
      chiralCompact, chiralMixing, Matrix.add_apply] <;>
    ring

theorem chiralCombination_mem_order (x y z w : ℤ) :
    chiralCombination x y z w ∈ IntegralChiralCliffordOrder := by
  have hI := IntegralChiralCliffordOrder.zsmul_mem
    (chiral_generators_mem_order.1) x
  have hL := IntegralChiralCliffordOrder.zsmul_mem
    (chiral_generators_mem_order.2.1) y
  have hJ := IntegralChiralCliffordOrder.zsmul_mem
    (chiral_generators_mem_order.2.2.1) z
  have hX := IntegralChiralCliffordOrder.zsmul_mem
    (chiral_generators_mem_order.2.2.2) w
  simpa [chiralCombination, add_assoc] using
    IntegralChiralCliffordOrder.add_mem
      (IntegralChiralCliffordOrder.add_mem
        (IntegralChiralCliffordOrder.add_mem hI hL) hJ) hX

def chiralDet₂ (A : Mat₂Z) : ℤ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

theorem chiralCombination_det (x y z w : ℤ) :
    chiralDet₂ (chiralCombination x y z w) =
      x ^ 2 - y ^ 2 + z ^ 2 - w ^ 2 := by
  rw [chiralCombination_entries]
  simp [chiralDet₂]
  ring

theorem chiral_order_is_not_full_matrix_ring :
    ∃ A : Mat₂Z, A ∉ IntegralChiralCliffordOrder := by
  refine ⟨!![(1 : ℤ), 0; 0, 0], ?_⟩
  intro h
  have hdiag : Int.ModEq 2 (1 : ℤ) 0 := h.1
  norm_num [Int.ModEq] at hdiag

end InfoGeometry.Algebra
