import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Finite spinor-array identities and incidence

This file formalizes finite-index algebra over `ℂ`: the alternating `Fin 2`
spinor form, its contraction against symmetric arrays, a curvature-shaped
array, and the homogeneity/product rule of a separately defined incidence
map. These calculations are useful algebraic ingredients, but this file does
not construct twistor space, sheaf cohomology, a Penrose transform, spacetime
derivatives, or a source-free Maxwell solution. In particular, symmetry of
the supplied gradient array is explicit input to the contraction identity,
not a consequence of a field equation or of cohomology.

Historical claims being replaced:
1. 2-spinor index space `Fin 2` and the symplectic Levi-Civita metric `epsilon`.
2. Antisymmetry of the spinor metric: `ε_{ji} = - ε_{ij}`.
3. Contraction theorem: `∑_{i, j} ε^{ij} T_{ij} = 0` for any symmetric 2-tensor.
4. The former comments overclaimed an analytic twistor cohomology interpretation; the array data below has no such structure:
   - Field spinor `ϕ_{A'B'}(x)` with symmetry `ϕ_{A'B'} = ϕ_{B'A'}`.
   - Spacetime gradient `∇_{A A'} ϕ_{B' C'}` totally symmetric in primed indices.
5. The Zero-Rest-Mass field equation:
   `∑_{A', B'} ε^{A'B'} ∇_{AA'} ϕ_{B'C'} = 0`.
6. The self-dual Maxwell curvature tensor `F_{AA' BB'} = ε_{AB} ϕ_{A'B'}`:
   - Spacetime 2-form antisymmetry: `F_{BB' AA'} = - F_{AA' BB'}`.
   - Vanishing of the anti-self-dual curvature: `∑_{A', B'} ε^{A'B'} F_{AA' BB'} = 0`.
   - Source-free Maxwell field equations.
7. Penrose incidence relation `ω^A = i * x^{AA'} π_{A'}` and projective homogeneity.
8. Master synthesis structure and certificate.

The finite-array identities below are proved in Mathlib; they should not be
read as a formalization of the analytic Penrose transform.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorPenroseTransform

/-! ### 1. The Spinor Metric Epsilon -/

/-- Levi-Civita symplectic metric tensor on 2-spinor space. -/
def epsilon : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 0 then -1
  else 0

lemma eps_00 : epsilon 0 0 = 0 := by rfl
lemma eps_01 : epsilon 0 1 = 1 := by rfl
lemma eps_10 : epsilon 1 0 = -1 := by rfl
lemma eps_11 : epsilon 1 1 = 0 := by rfl

/-- **Theorem (Antisymmetry of the Spinor Metric)**:
    `ε_{ji} = - ε_{ij}`. -/
theorem epsilon_antisymm (i j : Fin 2) : epsilon j i = - epsilon i j := by
  fin_cases i <;> fin_cases j
  · change epsilon 0 0 = - epsilon 0 0; rw [eps_00, neg_zero]
  · change epsilon 1 0 = - epsilon 0 1; rw [eps_10, eps_01]
  · change epsilon 0 1 = - epsilon 1 0; rw [eps_01, eps_10, neg_neg]
  · change epsilon 1 1 = - epsilon 1 1; rw [eps_11, neg_zero]

/-- **Theorem (Symmetric Contraction Annihilation)**:
    The contraction of the antisymmetric epsilon metric with any symmetric
    spinor tensor vanishes identically: `∑_{i, j} ε_{ij} T_{ij} = 0`. -/
theorem contract_epsilon_symm (T : Fin 2 → Fin 2 → ℂ) (hT : ∀ i j, T i j = T j i) :
    (∑ i : Fin 2, ∑ j : Fin 2, epsilon i j * T i j) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  rw [eps_00, eps_01, eps_10, eps_11]
  have h_symm : T 1 0 = T 0 1 := hT 1 0
  calc 0 * T 0 0 + 1 * T 0 1 + (-1 * T 1 0 + 0 * T 1 1)
    _ = T 0 1 - T 1 0 := by ring
    _ = T 0 1 - T 0 1 := by rw [h_symm]
    _ = 0             := by ring

/-! ### 2. Finite array data with explicit symmetries -/

/-- The two finite arrays used by the algebraic readouts. Symmetry assumptions
are theorem hypotheses, not fields of this data structure. -/
structure TwistorMaxwellArrayData where
  /-- A two-index array used as curvature-shaped data. -/
  field : (Fin 2 → Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ)
  /-- A four-index array, with no derivative structure imposed. -/
  grad : (Fin 2 → Fin 2 → ℂ) → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ

namespace TwistorMaxwellArrayData

variable (P : TwistorMaxwellArrayData)

/-! ### 3. Antisymmetric contraction of the supplied symmetric array -/

/-- Contracting the explicitly symmetric `grad` array with `epsilon` gives
zero. This finite identity does not assert or derive a zero-rest-mass PDE. -/
theorem symmetric_gradient_contraction_zero
    (x : Fin 2 → Fin 2 → ℂ) (A C' : Fin 2)
    (hGradSymm : ∀ A' B', P.grad x A A' B' C' = P.grad x A B' A' C') :
    (∑ A' : Fin 2, ∑ B' : Fin 2, epsilon A' B' * P.grad x A A' B' C') = 0 := by
  let T : Fin 2 → Fin 2 → ℂ := fun A' B' => P.grad x A A' B' C'
  have hT : ∀ i j, T i j = T j i := hGradSymm
  exact contract_epsilon_symm T hT

/-! ### 4. Curvature-shaped array and its algebraic symmetries -/

/-- An antisymmetric-pair array built from `epsilon` and the symmetric `field`.
This definition alone does not supply Maxwell's differential equations. -/
def curvatureArray (x : Fin 2 → Fin 2 → ℂ) :
    Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun A A' B B' => epsilon A B * P.field x A' B'

/-- The curvature-shaped array is antisymmetric under exchange of its two
index pairs. This finite-array fact is not a Maxwell field construction. -/
theorem curvature_array_pair_antisymmetric
    (x : Fin 2 → Fin 2 → ℂ) (A A' B B' : Fin 2)
    (hFieldSymm : ∀ i j, P.field x i j = P.field x j i) :
    P.curvatureArray x B B' A A' = - P.curvatureArray x A A' B B' := by
  dsimp [curvatureArray]
  rw [epsilon_antisymm B A]
  rw [hFieldSymm B' A']
  ring

/-- The primed-index epsilon contraction of this array vanishes by symmetry of
`field`. This identity does not identify a Hodge-dual component or prove a
Maxwell field equation. -/
theorem curvature_array_epsilon_contraction_zero
    (x : Fin 2 → Fin 2 → ℂ) (A B : Fin 2)
    (hFieldSymm : ∀ i j, P.field x i j = P.field x j i) :
    (∑ A' : Fin 2, ∑ B' : Fin 2, epsilon A' B' * P.curvatureArray x A A' B B') = 0 := by
  rw [Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  dsimp [curvatureArray]
  rw [eps_00, eps_01, eps_10, eps_11]
  have h_symm : P.field x 1 0 = P.field x 0 1 := hFieldSymm 1 0
  calc 0 * (epsilon A B * P.field x 0 0) + 1 * (epsilon A B * P.field x 0 1) +
       (-1 * (epsilon A B * P.field x 1 0) + 0 * (epsilon A B * P.field x 1 1))
    _ = epsilon A B * (P.field x 0 1 - P.field x 1 0) := by ring
    _ = epsilon A B * (P.field x 0 1 - P.field x 0 1) := by rw [h_symm]
    _ = 0                                            := by ring

/-- The same symmetric-array contraction with renamed free indices. This is
not a source-free Maxwell divergence theorem. -/
theorem symmetric_array_contraction_readout
    (x : Fin 2 → Fin 2 → ℂ) (C C' : Fin 2)
    (hGradSymm : ∀ A' B', P.grad x C A' B' C' = P.grad x C B' A' C') :
    (∑ A' : Fin 2, ∑ B' : Fin 2, epsilon A' B' * P.grad x C A' B' C') = 0 :=
  P.symmetric_gradient_contraction_zero x C C' hGradSymm

end TwistorMaxwellArrayData

/-! ### 5. Finite complex incidence formula -/

/-- The standard-form complex bilinear incidence expression. This definition
does not itself construct projective twistor space or null geodesics. -/
def twistorIncidence (x : Fin 2 → Fin 2 → ℂ) (pi : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun A => Complex.I * (∑ A' : Fin 2, x A A' * pi A')

/-- **Theorem (Projective Homogeneity of Incidence)**:
    Scaling the spinor `π_{A'}` by `c` scales the incidence spinor `ω^A` by `c`. -/
theorem incidence_homogeneous (x : Fin 2 → Fin 2 → ℂ) (pi : Fin 2 → ℂ) (c : ℂ) :
    twistorIncidence x (c • pi) = c • twistorIncidence x pi := by
  ext A
  dsimp [twistorIncidence]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/-! ### 5a. Conditional transport of chirality through incidence

The file's incidence map is defined over `ℂ`, rather than over a superspace
algebra.  The following theorem records exactly the algebraic input needed to
transport an annihilation equation through that map: a real-linear derivation
must kill the coordinate, the spinor, and the scalar `I`.  It does not identify
such a derivation with a supersymmetry covariant derivative.
-/

/-- If a real-linear derivation kills the spacetime coordinates, the reference
spinor, and `I`, then it kills the corresponding Penrose incidence component.
This is the product-and-sum part of a chiral incidence argument. -/
theorem incidence_derivation_eq_zero
    (D : ℂ →ₗ[ℝ] ℂ)
    (hD_mul : ∀ z w, D (z * w) = D z * w + z * D w)
    (hDI : D Complex.I = 0)
    (x : Fin 2 → Fin 2 → ℂ) (pi : Fin 2 → ℂ) (A : Fin 2)
    (hx : ∀ A' : Fin 2, D (x A A') = 0)
    (hpi : ∀ A' : Fin 2, D (pi A') = 0) :
    D (twistorIncidence x pi A) = 0 := by
  dsimp [twistorIncidence]
  have hsum : D (∑ A' : Fin 2, x A A' * pi A') = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro A' _
    rw [hD_mul, hx A', hpi A']
    simp
  rw [hD_mul, hDI, hsum]
  simp

/-! ### 6. Master Certified Synthesis -/

end InfoGeometry.Twistor.TwistorPenroseTransform
