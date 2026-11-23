/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Contraction

import InfoGeometry.Canonical.KahlerAtiyahCartanForms

/-!
# Kähler--Atiyah bivectors and the spin Lie action

This module is the next theorem edge after the Cartan-form Clifford
representation on the exterior algebra.

For a symmetric metric `g`, write `c(v)` for the Kähler--Atiyah action
`ε(v) + ι(g(v,-))`.  The normalized Clifford bivector

`Σ(v,u) = (1/4) [c(v), c(u)]`

acts on generators by the orthogonal Lie algebra formula

`[Σ(v,u), c(w)] = g(u,w)c(v) - g(v,w)c(u)`.

Thus the degree-two Clifford commutators on literal exterior forms realize
the infinitesimal spin/orthogonal action, without introducing a matrix gamma
representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.KahlerAtiyahSpinConnection

open InfoGeometry.Canonical.KahlerAtiyahCartanForms

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Commutator in the endomorphism algebra of exterior forms. -/
def endCommutator
    (A B : FormEnd V) :
    FormEnd V :=
  A * B - B * A

private theorem commutator_jacobi {R : Type*} [Ring R] (A B C : R) :
    (A * B - B * A) * C - C * (A * B - B * A) =
      (A * (B * C - C * B) - (B * C - C * B) * A) -
        (B * (A * C - C * A) - (A * C - C * A) * B) := by
  noncomm_ring

@[simp] theorem endCommutator_self
    (A : FormEnd V) :
    endCommutator A A = 0 := by
  simp [endCommutator]

theorem endCommutator_skew
    (A B : FormEnd V) :
    endCommutator A B = -endCommutator B A := by
  dsimp [endCommutator]
  abel

theorem endCommutator_smul_left (r : ℝ) (A B : FormEnd V) :
    endCommutator (r • A) B = r • endCommutator A B := by
  ext α
  simp [endCommutator, Module.End.mul_apply, smul_sub]

theorem endCommutator_smul_right (r : ℝ) (A B : FormEnd V) :
    endCommutator A (r • B) = r • endCommutator A B := by
  calc
    endCommutator A (r • B) = -endCommutator (r • B) A :=
      endCommutator_skew A (r • B)
    _ = -(r • endCommutator B A) := by rw [endCommutator_smul_left]
    _ = r • endCommutator A B := by
      rw [endCommutator_skew B A]
      simp

theorem endCommutator_add_left (A₁ A₂ B : FormEnd V) :
    endCommutator (A₁ + A₂) B =
      endCommutator A₁ B + endCommutator A₂ B := by
  dsimp [endCommutator]
  noncomm_ring

/-- Normalized Clifford bivector generator
`Σ(v,u) = 1/4 [c(v),c(u)]`. -/
def spinBivector
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    FormEnd V :=
  (1 / 4 : ℝ) •
    endCommutator
      (cartanCliffordAction g v)
      (cartanCliffordAction g u)

theorem spinBivector_skew
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    spinBivector g v u = -spinBivector g u v := by
  unfold spinBivector
  rw [endCommutator_skew (cartanCliffordAction g v) (cartanCliffordAction g u),
    smul_neg]

theorem spinBivector_add_left
    (g : LinearMap.BilinForm ℝ V) (v₁ v₂ u : V) :
    spinBivector g (v₁ + v₂) u =
      spinBivector g v₁ u + spinBivector g v₂ u := by
  unfold spinBivector
  rw [show cartanCliffordAction g (v₁ + v₂) =
      cartanCliffordAction g v₁ + cartanCliffordAction g v₂ by
        exact map_add (cartanCliffordActionMap g) v₁ v₂]
  rw [endCommutator_add_left]
  rw [smul_add]

theorem spinBivector_smul_left
    (g : LinearMap.BilinForm ℝ V) (r : ℝ) (v u : V) :
    spinBivector g (r • v) u = r • spinBivector g v u := by
  unfold spinBivector
  rw [show cartanCliffordAction g (r • v) =
      r • cartanCliffordAction g v by
        exact map_smul (cartanCliffordActionMap g) r v]
  rw [endCommutator_smul_left]
  module

theorem spinBivector_add_right
    (g : LinearMap.BilinForm ℝ V) (v u₁ u₂ : V) :
    spinBivector g v (u₁ + u₂) =
      spinBivector g v u₁ + spinBivector g v u₂ := by
  calc
    spinBivector g v (u₁ + u₂) =
        -(spinBivector g (u₁ + u₂) v) := by rw [spinBivector_skew]
    _ = -(spinBivector g u₁ v + spinBivector g u₂ v) := by
      rw [spinBivector_add_left]
    _ = spinBivector g v u₁ + spinBivector g v u₂ := by
      rw [spinBivector_skew g v u₁, spinBivector_skew g v u₂]
      module

theorem spinBivector_smul_right
    (g : LinearMap.BilinForm ℝ V) (r : ℝ) (v u : V) :
    spinBivector g v (r • u) = r • spinBivector g v u := by
  calc
    spinBivector g v (r • u) =
        -(spinBivector g (r • u) v) := by rw [spinBivector_skew]
    _ = -(r • spinBivector g u v) := by rw [spinBivector_smul_left]
    _ = r • spinBivector g v u := by rw [spinBivector_skew]; module

@[simp] theorem spinBivector_self
    (g : LinearMap.BilinForm ℝ V)
    (v : V) :
    spinBivector g v v = 0 := by
  simp [spinBivector]

/--
Unnormalized commutator identity behind the spin action.

For three Clifford generators `A = c(v)`, `B = c(u)`, `C = c(w)`,
the double commutator satisfies

`[[A,B],C] = 4 g(u,w) A - 4 g(v,w) B`.
-/
theorem clifford_double_commutator
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (endCommutator
          (cartanCliffordAction g v)
          (cartanCliffordAction g u))
        (cartanCliffordAction g w) =
      (4 * g u w) • cartanCliffordAction g v -
        (4 * g v w) • cartanCliffordAction g u := by
  let A : FormEnd V := cartanCliffordAction g v
  let B : FormEnd V := cartanCliffordAction g u
  let C : FormEnd V := cartanCliffordAction g w

  have hBC :
      B * C + C * B =
        (2 * g u w) • (1 : FormEnd V) := by
    dsimp [B, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg u w

  have hAC :
      A * C + C * A =
        (2 * g v w) • (1 : FormEnd V) := by
    dsimp [A, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg v w

  have hrearrange :
      endCommutator (endCommutator A B) C =
        A * (B * C + C * B) -
          (A * C + C * A) * B -
          B * (A * C + C * A) +
          (B * C + C * B) * A := by
    dsimp [endCommutator]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
    abel

  rw [hrearrange, hBC, hAC]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

/-! ### Contracted Clifford double commutator

This is the positive-definite orthonormal-frame specialization of the algebraic
identity used in Shirokov's Theorem 5.2.  It is stated on Mathlib's
Kähler--Atiyah action on exterior forms, with no matrix representation. -/

/-- In an orthonormal frame, summing the double commutator over the frame
produces the factor `4 (dim V - 1)` on each Clifford generator. -/
theorem orthonormal_frame_double_commutator_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (j : ι) :
    (∑ i : ι,
      endCommutator (cartanCliffordAction g (b i))
        (endCommutator (cartanCliffordAction g (b i))
          (cartanCliffordAction g (b j))) : FormEnd V) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ)) •
        cartanCliffordAction g (b j) := by
  have hterm (i : ι) :
      endCommutator (cartanCliffordAction g (b i))
        (endCommutator (cartanCliffordAction g (b i))
          (cartanCliffordAction g (b j))) =
        (if i = j then (0 : FormEnd V)
          else (4 : ℝ) • cartanCliffordAction g (b j)) := by
    have hbase := clifford_double_commutator g hg (b i) (b j) (b i)
    have hreverse := endCommutator_skew
      (cartanCliffordAction g (b i))
      (endCommutator (cartanCliffordAction g (b i))
        (cartanCliffordAction g (b j)))
    rw [horth j i, horth i i] at hbase
    by_cases hij : i = j
    · subst j
      simp [endCommutator]
    · rw [hreverse, hbase]
      have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun i => endCommutator (cartanCliffordAction g (b i))
      (endCommutator (cartanCliffordAction g (b i))
        (cartanCliffordAction g (b j)))) (Finset.mem_univ j)]
  have herase :
      (∑ i ∈ (Finset.univ : Finset ι).erase j,
        endCommutator (cartanCliffordAction g (b i))
          (endCommutator (cartanCliffordAction g (b i))
            (cartanCliffordAction g (b j)))) =
        (Fintype.card ι - 1 : ℕ) •
          ((4 : ℝ) • cartanCliffordAction g (b j)) := by
    calc
      (∑ i ∈ (Finset.univ : Finset ι).erase j,
          endCommutator (cartanCliffordAction g (b i))
            (endCommutator (cartanCliffordAction g (b i))
              (cartanCliffordAction g (b j)))) =
          ∑ i ∈ (Finset.univ : Finset ι).erase j,
            (4 : ℝ) • cartanCliffordAction g (b j) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hij : i ≠ j := (Finset.mem_erase.mp hi).1
              rw [hterm, if_neg hij]
      _ = (Fintype.card ι - 1 : ℕ) •
          ((4 : ℝ) • cartanCliffordAction g (b j)) := by
            simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
  rw [herase, hterm j]
  simp only [if_true, add_zero]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [mul_comm]

/-- Scaling the Clifford field by `σ` scales its contracted cubic current by
`σ^3`, as in Shirokov's Theorem 5.2. -/
theorem scaled_orthonormal_frame_double_commutator_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (horth : ∀ i j, g (b i) (b j) = if i = j then 1 else 0)
    (j : ι) (σ : ℝ) :
    (∑ i : ι,
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) : FormEnd V) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
        cartanCliffordAction g (b j) := by
  have hscale (i : ι) :
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (σ • cartanCliffordAction g (b i))
          (σ • cartanCliffordAction g (b j))) =
        σ ^ 3 • endCommutator (cartanCliffordAction g (b i))
          (endCommutator (cartanCliffordAction g (b i))
            (cartanCliffordAction g (b j))) := by
    let A := cartanCliffordAction g (b i)
    let B := cartanCliffordAction g (b j)
    have hin : endCommutator (σ • A) (σ • B) = σ ^ 2 • endCommutator A B := by
      rw [endCommutator_smul_left, endCommutator_smul_right]
      module
    change endCommutator (σ • A) (endCommutator (σ • A) (σ • B)) =
      σ ^ 3 • endCommutator A (endCommutator A B)
    rw [hin]
    calc
      endCommutator (σ • A) (σ ^ 2 • endCommutator A B) =
          σ ^ 2 • endCommutator (σ • A) (endCommutator A B) :=
        endCommutator_smul_right _ _ _
      _ = σ ^ 2 • (σ • endCommutator A (endCommutator A B)) := by
        rw [endCommutator_smul_left]
      _ = σ ^ 3 • endCommutator A (endCommutator A B) := by module
  calc
    (∑ i : ι,
        endCommutator (σ • cartanCliffordAction g (b i))
          (endCommutator (σ • cartanCliffordAction g (b i))
            (σ • cartanCliffordAction g (b j))) : FormEnd V) =
        σ ^ 3 • ∑ i : ι,
          endCommutator (cartanCliffordAction g (b i))
            (endCommutator (cartanCliffordAction g (b i))
              (cartanCliffordAction g (b j))) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            exact hscale i
    _ = ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          cartanCliffordAction g (b j) := by
            rw [orthonormal_frame_double_commutator_sum b g hg horth]
            module

/-! The paper's contracted index in a pseudo-Euclidean frame carries the
metric sign. Raising both contracted and output indices removes dependence on
the signature in the cubic current coefficient. -/

/-- Contracted Clifford double commutator in a pseudo-orthonormal frame.
The function `ε` records the diagonal signature, with `ε i = ±1`; the raised
frame vectors are `ε i • b i`. -/
theorem pseudoOrthonormal_frame_contracted_double_commutator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (j : ι) :
    (∑ i : ι,
      endCommutator (cartanCliffordAction g (b i))
        (endCommutator (ε i • cartanCliffordAction g (b i))
          (ε j • cartanCliffordAction g (b j))) : FormEnd V) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ)) •
        (ε j • cartanCliffordAction g (b j)) := by
  have hterm (i : ι) :
      endCommutator (cartanCliffordAction g (b i))
        (endCommutator (ε i • cartanCliffordAction g (b i))
          (ε j • cartanCliffordAction g (b j))) =
        (if i = j then (0 : FormEnd V)
          else (4 : ℝ) • (ε j • cartanCliffordAction g (b j))) := by
    let ci := cartanCliffordAction g (b i)
    let cj := cartanCliffordAction g (b j)
    have hbase := clifford_double_commutator g hg (b i) (b j) (b i)
    have hreverse := endCommutator_skew ci (endCommutator ci cj)
    rw [horth j i, horth i i] at hbase
    by_cases hij : i = j
    · subst j
      simp [endCommutator]
    · rw [if_neg hij]
      have hbase' : endCommutator (endCommutator ci cj) ci =
          -((4 * ε i) • cj) := by
        have hji : j ≠ i := fun h => hij h.symm
        simpa [ci, cj, hij, hji] using hbase
      have hinner : endCommutator (ε i • ci) (ε j • cj) =
          (ε i * ε j) • endCommutator ci cj := by
        rw [endCommutator_smul_left, endCommutator_smul_right]
        module
      have hscalar : (ε i * ε j) * (4 * ε i) = 4 * ε j := by
        calc
          (ε i * ε j) * (4 * ε i) = 4 * ε j * (ε i * ε i) := by ring
          _ = 4 * ε j := by rw [hε i, mul_one]
      rw [hinner]
      calc
        endCommutator ci ((ε i * ε j) • endCommutator ci cj) =
            (ε i * ε j) • endCommutator ci (endCommutator ci cj) :=
          endCommutator_smul_right _ _ _
        _ = (ε i * ε j) • (-endCommutator (endCommutator ci cj) ci) := by
          rw [hreverse]
        _ = (4 : ℝ) • (ε j • cj) := by
          rw [hbase']
          simp only [smul_neg, neg_neg, smul_smul]
          rw [hscalar]
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun i => endCommutator (cartanCliffordAction g (b i))
      (endCommutator (ε i • cartanCliffordAction g (b i))
        (ε j • cartanCliffordAction g (b j)))) (Finset.mem_univ j)]
  have herase :
      (∑ i ∈ (Finset.univ : Finset ι).erase j,
        endCommutator (cartanCliffordAction g (b i))
          (endCommutator (ε i • cartanCliffordAction g (b i))
            (ε j • cartanCliffordAction g (b j)))) =
        (Fintype.card ι - 1 : ℕ) •
          ((4 : ℝ) • (ε j • cartanCliffordAction g (b j))) := by
    calc
      (∑ i ∈ (Finset.univ : Finset ι).erase j,
          endCommutator (cartanCliffordAction g (b i))
            (endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j)))) =
          ∑ i ∈ (Finset.univ : Finset ι).erase j,
            (4 : ℝ) • (ε j • cartanCliffordAction g (b j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hij : i ≠ j := (Finset.mem_erase.mp hi).1
              rw [hterm, if_neg hij]
      _ = (Fintype.card ι - 1 : ℕ) •
            ((4 : ℝ) • (ε j • cartanCliffordAction g (b j))) := by
              simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
  rw [herase, hterm j]
  simp only [if_true, add_zero]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  rw [mul_comm]

/-- Cubic scaling of the diagonal pseudo-Euclidean Clifford contraction. -/
theorem scaled_pseudoOrthonormal_frame_contracted_double_commutator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (j : ι) (σ : ℝ) :
    (∑ i : ι,
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (ε i • (σ • cartanCliffordAction g (b i)))
          (ε j • (σ • cartanCliffordAction g (b j)))) : FormEnd V) =
      ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
        (ε j • cartanCliffordAction g (b j)) := by
  have hscale (i : ι) :
      endCommutator (σ • cartanCliffordAction g (b i))
        (endCommutator (ε i • (σ • cartanCliffordAction g (b i)))
          (ε j • (σ • cartanCliffordAction g (b j)))) =
      σ ^ 3 • endCommutator (cartanCliffordAction g (b i))
        (endCommutator (ε i • cartanCliffordAction g (b i))
          (ε j • cartanCliffordAction g (b j))) := by
    have hleft : ε i • (σ • cartanCliffordAction g (b i)) =
        σ • (ε i • cartanCliffordAction g (b i)) := by
      calc
        ε i • (σ • cartanCliffordAction g (b i)) =
            (ε i * σ) • cartanCliffordAction g (b i) := smul_smul _ _ _
        _ = (σ * ε i) • cartanCliffordAction g (b i) := by rw [mul_comm]
        _ = σ • (ε i • cartanCliffordAction g (b i)) := (smul_smul _ _ _).symm
    have hright : ε j • (σ • cartanCliffordAction g (b j)) =
        σ • (ε j • cartanCliffordAction g (b j)) := by
      calc
        ε j • (σ • cartanCliffordAction g (b j)) =
            (ε j * σ) • cartanCliffordAction g (b j) := smul_smul _ _ _
        _ = (σ * ε j) • cartanCliffordAction g (b j) := by rw [mul_comm]
        _ = σ • (ε j • cartanCliffordAction g (b j)) := (smul_smul _ _ _).symm
    rw [hleft, hright]
    have hinner :
        endCommutator (σ • (ε i • cartanCliffordAction g (b i)))
          (σ • (ε j • cartanCliffordAction g (b j))) =
        σ ^ 2 • endCommutator (ε i • cartanCliffordAction g (b i))
          (ε j • cartanCliffordAction g (b j)) := by
      calc
        _ = σ • endCommutator (ε i • cartanCliffordAction g (b i))
              (σ • (ε j • cartanCliffordAction g (b j))) :=
            endCommutator_smul_left _ _ _
        _ = σ • (σ • endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j))) := by
            rw [endCommutator_smul_right]
        _ = σ ^ 2 • endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j)) := by
            rw [smul_smul, pow_two]
    calc
      endCommutator (σ • cartanCliffordAction g (b i))
          (endCommutator (σ • (ε i • cartanCliffordAction g (b i)))
            (σ • (ε j • cartanCliffordAction g (b j)))) =
        σ • endCommutator (cartanCliffordAction g (b i))
          (endCommutator (σ • (ε i • cartanCliffordAction g (b i)))
            (σ • (ε j • cartanCliffordAction g (b j)))) :=
          endCommutator_smul_left _ _ _
      _ = σ • (σ ^ 2 • endCommutator (cartanCliffordAction g (b i))
            (endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j)))) := by
          rw [hinner, endCommutator_smul_right]
      _ = σ ^ 3 • endCommutator (cartanCliffordAction g (b i))
            (endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j))) := by
          module
  calc
    (∑ i : ι,
        endCommutator (σ • cartanCliffordAction g (b i))
          (endCommutator (ε i • (σ • cartanCliffordAction g (b i)))
            (ε j • (σ • cartanCliffordAction g (b j)))) : FormEnd V) =
        σ ^ 3 • ∑ i : ι,
          endCommutator (cartanCliffordAction g (b i))
            (endCommutator (ε i • cartanCliffordAction g (b i))
              (ε j • cartanCliffordAction g (b j))) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            exact hscale i
    _ = ((4 * (Fintype.card ι - 1 : ℕ) : ℝ) * σ ^ 3) •
          (ε j • cartanCliffordAction g (b j)) := by
            rw [pseudoOrthonormal_frame_contracted_double_commutator b g hg ε hε horth j]
            module

/--
The normalized Clifford bivector acts on Cartan generators by the defining
orthogonal Lie algebra representation:

`[Σ(v,u),c(w)] = g(u,w)c(v) - g(v,w)c(u)`.
-/
theorem spinBivector_comm_cartanCliffordAction
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (spinBivector g v u)
        (cartanCliffordAction g w) =
      (g u w) • cartanCliffordAction g v -
        (g v w) • cartanCliffordAction g u := by
  unfold spinBivector
  rw [endCommutator_smul_left]
  rw [clifford_double_commutator g hg v u w]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

/--
Coframe specialization.  If `g(θ_a,θ_b)=η_ab`, the spin bivectors act on
the Cartan coframe generators by

`[Σ_ab,c(θ_c)] = η_bc c(θ_a) - η_ac c(θ_b)`.
-/
theorem coframe_spinBivector_action
    {ι : Type*}
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (θ : ι → V)
    (η : ι → ι → ℝ)
    (hθ : ∀ a b, g (θ a) (θ b) = η a b)
    (a b c : ι) :
    endCommutator
        (spinBivector g (θ a) (θ b))
        (cartanCliffordAction g (θ c)) =
      (η b c) • cartanCliffordAction g (θ a) -
        (η a c) • cartanCliffordAction g (θ b) := by
  rw [spinBivector_comm_cartanCliffordAction g hg]
  rw [hθ, hθ]

/-! ### Metric-skew endomorphisms as Clifford bivector actions

The elementary bivectors above generate the orthogonal Lie algebra when the
metric is nondegenerate. The formula below is written using an explicit basis
and its metric-dual basis. The resulting operator is proved independent of
that basis; the theorem remains pointwise on one real Clifford module and does
not itself construct bundle transition functions or a global spinor bundle.
No complex scalar structure or orthonormal-frame assumption is introduced.
-/

/-- The endomorphism whose values on a frame are its coordinate derivatives. -/
noncomputable def frameDerivativeMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (dh : ι → V) : V →ₗ[ℝ] V :=
  b.constr ℝ dh

@[simp] theorem frameDerivativeMap_apply_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (dh : ι → V) (i : ι) :
    frameDerivativeMap b dh (b i) = dh i := by
  simp [frameDerivativeMap]

/-- Differentiating the pseudo-orthonormal frame relations gives a
metric-skew frame-derivative endomorphism. The hypothesis is the exact
first-order compatibility identity on frame vectors. -/
theorem frameDerivativeMap_metricSkew
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (dh : ι → V)
    (hcompat : ∀ i j, g (dh i) (b j) + g (b i) (dh j) = 0) :
    ∀ x y, g (frameDerivativeMap b dh x) y +
      g x (frameDerivativeMap b dh y) = 0 := by
  intro x y
  let cx : ι → ℝ := fun i => b.repr x i
  let cy : ι → ℝ := fun i => b.repr y i
  have hx : (∑ i : ι, cx i • b i) = x := by
    simpa [cx] using b.sum_repr x
  have hy : (∑ i : ι, cy i • b i) = y := by
    simpa [cy] using b.sum_repr y
  have hA (z : V) : frameDerivativeMap b dh z =
      ∑ i : ι, b.repr z i • dh i := by
    simp [frameDerivativeMap, Module.Basis.constr_apply_fintype]
  have hPairLeft (i : ι) : g (dh i) y =
      ∑ j : ι, cy j * g (dh i) (b j) := by
    calc
      g (dh i) y = g (dh i) (∑ j : ι, cy j • b j) := by
        exact congrArg (g (dh i)) hy.symm
      _ = ∑ j : ι, cy j * g (dh i) (b j) := by
        simp [LinearMap.BilinForm.smul_right, map_sum, smul_eq_mul]
  have hPairRight (j : ι) : g x (dh j) =
      ∑ i : ι, cx i * g (b i) (dh j) := by
    calc
      g x (dh j) = g (∑ i : ι, cx i • b i) (dh j) := by
        exact congrArg (fun z => g z (dh j)) hx.symm
      _ = ∑ i : ι, cx i * g (b i) (dh j) := by
        simp [LinearMap.BilinForm.smul_left, map_sum, smul_eq_mul]
  have hFirst : g (frameDerivativeMap b dh x) y =
      ∑ i : ι, ∑ j : ι, cx i * cy j * g (dh i) (b j) := by
    calc
      g (frameDerivativeMap b dh x) y =
          ∑ i : ι, cx i * g (dh i) y := by
            rw [hA x]
            simp [cx, LinearMap.BilinForm.smul_left, smul_eq_mul,
              LinearMap.BilinForm.sum_left]
      _ = ∑ i : ι, cx i * (∑ j : ι, cy j * g (dh i) (b j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hPairLeft i]
      _ = ∑ i : ι, ∑ j : ι, cx i * cy j * g (dh i) (b j) := by
            simp [Finset.mul_sum, mul_assoc]
  have hSecond : g x (frameDerivativeMap b dh y) =
      ∑ i : ι, ∑ j : ι, cx i * cy j * g (b i) (dh j) := by
    calc
      g x (frameDerivativeMap b dh y) =
          ∑ j : ι, cy j * g x (dh j) := by
            rw [hA y]
            simp [cy, LinearMap.BilinForm.smul_right, smul_eq_mul,
              LinearMap.BilinForm.sum_right]
      _ = ∑ j : ι, cy j * (∑ i : ι, cx i * g (b i) (dh j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hPairRight j]
      _ = ∑ i : ι, ∑ j : ι, cx i * cy j * g (b i) (dh j) := by
            rw [Finset.sum_comm]
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hFirst, hSecond]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← mul_add, hcompat, mul_zero]

/-- A Clifford bivector representative for a metric-skew endomorphism, written
using the supplied basis and its metric-dual basis. -/
noncomputable def metricSkewSpinLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A : V →ₗ[ℝ] V) : FormEnd V :=
  (1 / 2 : ℝ) • ∑ i, spinBivector g (A (b i)) ((g.dualBasis hg b) i)

/-- The bivector spin lift is the quarter-sum of Clifford products whenever
the metric trace of the endomorphism vanishes. This is the algebraic form of
the frame formula `C = (1/4) Σ_i (A b_i) b^i`; the trace condition is explicit
so the scalar part is not silently discarded. -/
theorem metricSkewSpinLift_eq_quarter_frame_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : V →ₗ[ℝ] V)
    (htrace : ∑ i : ι, g (A (b i)) ((g.dualBasis hg b) i) = 0) :
    metricSkewSpinLift b g hg A =
      (1 / 4 : ℝ) • ∑ i : ι,
        cartanCliffordAction g (A (b i)) *
          cartanCliffordAction g ((g.dualBasis hg b) i) := by
  have hcomm (i : ι) :
      endCommutator (cartanCliffordAction g (A (b i)))
          (cartanCliffordAction g ((g.dualBasis hg b) i)) =
        (2 : ℝ) •
            (cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i)) -
          (2 * g (A (b i)) ((g.dualBasis hg b) i)) • (1 : FormEnd V) := by
    have hanti := cartanCliffordAction_anticommutator_of_symmetric
      g hgsymm (A (b i)) ((g.dualBasis hg b) i)
    have hsecond :
        cartanCliffordAction g ((g.dualBasis hg b) i) *
            cartanCliffordAction g (A (b i)) =
          (2 * g (A (b i)) ((g.dualBasis hg b) i)) • (1 : FormEnd V) -
            cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) := by
      calc
        _ = cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) +
            cartanCliffordAction g ((g.dualBasis hg b) i) *
              cartanCliffordAction g (A (b i)) -
            cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) := by noncomm_ring
        _ = (2 * g (A (b i)) ((g.dualBasis hg b) i)) • (1 : FormEnd V) -
            cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) := by rw [hanti]
    rw [endCommutator]
    rw [hsecond]
    module
  unfold metricSkewSpinLift spinBivector
  rw [Finset.smul_sum]
  have hsum :
      (∑ i : ι,
        endCommutator (cartanCliffordAction g (A (b i)))
          (cartanCliffordAction g ((g.dualBasis hg b) i))) =
        (2 : ℝ) • ∑ i : ι,
            cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) := by
    calc
      _ = ∑ i : ι,
          ((2 : ℝ) • (cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i)) -
            (2 * g (A (b i)) ((g.dualBasis hg b) i)) • (1 : FormEnd V)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hcomm i
      _ = (2 : ℝ) • ∑ i : ι,
            cartanCliffordAction g (A (b i)) *
              cartanCliffordAction g ((g.dualBasis hg b) i) := by
              rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
              have hscalar :
                  ∑ i : ι, (2 * g (A (b i)) ((g.dualBasis hg b) i)) = 0 := by
                calc
                  _ = 2 * ∑ i : ι,
                      g (A (b i)) ((g.dualBasis hg b) i) := by rw [Finset.mul_sum]
                  _ = 0 := by rw [htrace]; simp
              rw [show (∑ i : ι,
                  (2 * g (A (b i)) ((g.dualBasis hg b) i)) •
                    (1 : FormEnd V)) =
                  (∑ i : ι, 2 * g (A (b i)) ((g.dualBasis hg b) i)) •
                    (1 : FormEnd V) by rw [← Finset.sum_smul]]
              rw [hscalar, zero_smul, sub_zero]
  have hscale :
      (∑ i : ι,
        (1 / 2 : ℝ) • ((1 / 4 : ℝ) •
          endCommutator (cartanCliffordAction g (A (b i)))
            (cartanCliffordAction g ((g.dualBasis hg b) i)))) =
        (1 / 8 : ℝ) • ∑ i : ι,
          endCommutator (cartanCliffordAction g (A (b i)))
            (cartanCliffordAction g ((g.dualBasis hg b) i)) := by
    calc
      _ = ∑ i : ι, ((1 / 2 : ℝ) * (1 / 4 : ℝ)) •
          endCommutator (cartanCliffordAction g (A (b i)))
            (cartanCliffordAction g ((g.dualBasis hg b) i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [smul_smul]
      _ = (1 / 8 : ℝ) • ∑ i : ι,
          endCommutator (cartanCliffordAction g (A (b i)))
            (cartanCliffordAction g ((g.dualBasis hg b) i)) := by
              rw [Finset.smul_sum]
              norm_num
  rw [hscale, hsum]
  module

/-- A metric-skew endomorphism has zero metric trace when the supplied
metric-dual frame is diagonal in the original frame. -/
theorem metricSkew_trace_zero_of_diagonal_dual_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (hdual : ∃ ε : ι → ℝ,
      ∀ i, (g.dualBasis hg b) i = ε i • b i)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0) :
    ∑ i : ι, g (A (b i)) ((g.dualBasis hg b) i) = 0 := by
  have hdiag (i : ι) : g (A (b i)) (b i) = 0 := by
    have h := hA (b i) (b i)
    rw [hgsymm (b i) (A (b i))] at h
    exact (add_self_eq_zero.mp h)
  obtain ⟨ε, hdual⟩ := hdual
  have hterm (i : ι) : g (A (b i)) ((g.dualBasis hg b) i) = 0 := by
    rw [hdual i, map_smul]
    simp only [smul_eq_mul, hdiag, mul_zero]
  simp [hterm]

/-- In a pseudo-orthonormal frame, the metric-dual basis is the signed frame. -/
theorem metricDualBasis_eq_signed_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0) :
    ∀ i, (g.dualBasis hg b) i = ε i • b i := by
  let _ := b.finiteDimensional_of_finite
  intro i
  apply (g.toDual hg).injective
  ext x
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.BilinForm.toDual_def]
  apply Finset.sum_congr rfl
  intro j hj
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.BilinForm.toDual_def]
  rw [horth]
  by_cases hji : j = i
  · subst j
    simp [hε]
  · have hij : i ≠ j := fun h => hji h.symm
    simp [hji, hij]

/-- The frame-product formula follows for metric-skew maps when the
metric-dual frame is a diagonal rescaling of the chosen basis. -/
theorem metricSkewSpinLift_eq_quarter_frame_product_of_pseudoOrthonormal_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0) :
    metricSkewSpinLift b g hg A =
      (1 / 4 : ℝ) • ∑ i : ι,
        cartanCliffordAction g (A (b i)) *
          cartanCliffordAction g ((g.dualBasis hg b) i) := by
  apply metricSkewSpinLift_eq_quarter_frame_product b g hg hgsymm A
  have hdual : ∀ i, (g.dualBasis hg b) i = ε i • b i :=
    metricDualBasis_eq_signed_frame b g hg ε hε horth
  exact metricSkew_trace_zero_of_diagonal_dual_frame b g hg hgsymm ⟨ε, hdual⟩ A hA

/-- Spin connection obtained by lifting a directional derivative of the
chosen frame. The first index of `d` is the derivative direction and the
second is the frame index. -/
noncomputable def spinConnectionFromFrameDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (d : ι → ι → V) (μ : ι) : FormEnd V :=
  metricSkewSpinLift b g hg (frameDerivativeMap b (d μ))

/-- Shirokov's frame formula `C_μ = (1/4) Σ_ν (∂_μ h_ν) h^ν` for a
pseudo-orthonormal frame. The derivative of the frame-pairing identity is
the explicit metric-compatibility premise. -/
theorem spinConnectionFromFrameDerivative_eq_quarter_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, g (b i) (b j) = if i = j then ε i else 0)
    (d : ι → ι → V)
    (hcompat : ∀ μ i j,
      g (d μ i) (b j) + g (b i) (d μ j) = 0)
    (μ : ι) :
    spinConnectionFromFrameDerivative b g hg d μ =
      (1 / 4 : ℝ) • ∑ i : ι,
        cartanCliffordAction g (d μ i) *
          cartanCliffordAction g ((g.dualBasis hg b) i) := by
  unfold spinConnectionFromFrameDerivative
  simpa only [frameDerivativeMap_apply_basis] using
    metricSkewSpinLift_eq_quarter_frame_product_of_pseudoOrthonormal_frame
    b g hg hgsymm ε hε horth (frameDerivativeMap b (d μ))
    (frameDerivativeMap_metricSkew b g (d μ) (hcompat μ))

private def metricSkewSpinTensorMap
    (g : LinearMap.BilinForm ℝ V) (A : V →ₗ[ℝ] V) :
    TensorProduct ℝ V V →ₗ[ℝ] FormEnd V :=
  TensorProduct.lift (LinearMap.mk₂ ℝ
    (fun v u => spinBivector g (A v) u)
    (by
      intro v₁ v₂ u
      rw [map_add A, spinBivector_add_left])
    (by
      intro r v u
      rw [map_smul A, spinBivector_smul_left])
    (by
      intro v u₁ u₂
      exact spinBivector_add_right g (A v) u₁ u₂)
    (by
      intro r v u
      exact spinBivector_smul_right g r (A v) u))

private theorem dualTensorBasis_sum_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V) :
    (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) =
      ∑ j, c.dualBasis j ⊗ₜ[ℝ] c j := by
  have hb : dualTensorHom ℝ V V
      (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) = LinearMap.id := by
    rw [map_sum]
    ext x
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply, Module.Basis.dualBasis_apply]
    exact b.sum_repr x
  have hc : dualTensorHom ℝ V V
      (∑ j, c.dualBasis j ⊗ₜ[ℝ] c j) = LinearMap.id := by
    rw [map_sum]
    ext x
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply, Module.Basis.dualBasis_apply]
    exact c.sum_repr x
  apply (dualTensorHomEquivOfBasis b).injective
  change dualTensorHom ℝ V V (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) =
    dualTensorHom ℝ V V (∑ j, c.dualBasis j ⊗ₜ[ℝ] c j)
  exact hb.trans hc.symm

/-- The tensor made from a basis and its metric-dual basis is independent of
the chosen finite basis. -/
theorem metricDualTensor_basis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate) :
    (∑ i, b i ⊗ₜ[ℝ] (g.dualBasis hg b) i) =
      ∑ j, c j ⊗ₜ[ℝ] (g.dualBasis hg c) j := by
  have hcanonical := dualTensorBasis_sum_eq b c
  have htransport := congrArg
    (fun z => (g.toDual hg).symm.rTensor V z) hcanonical
  have hcomm := congrArg (TensorProduct.comm ℝ V V) htransport
  simpa [LinearEquiv.rTensor_tmul, LinearMap.BilinForm.dualBasis,
    Module.Basis.map_apply, TensorProduct.comm_tmul] using hcomm

/-- The metric-skew bivector operator itself is independent of the chosen
finite basis. The proof factors the basis sum through the basis-independent
metric-dual tensor, so this is operator equality and not only equality of its
action on Clifford generators. -/
theorem metricSkewSpinLift_basis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (A : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg A = metricSkewSpinLift c g hg A := by
  unfold metricSkewSpinLift
  have h := congrArg (metricSkewSpinTensorMap g A)
    (metricDualTensor_basis_independent b c g hg)
  have hsum :
      (∑ i, spinBivector g (A (b i)) ((g.dualBasis hg b) i)) =
        ∑ j, spinBivector g (A (c j)) ((g.dualBasis hg c) j) := by
    simpa [metricSkewSpinTensorMap, LinearMap.mk₂] using h
  exact congrArg (fun z : FormEnd V => (1 / 2 : ℝ) • z) hsum

/-- Additivity of the chosen-basis bivector representative in the
metric-skew endomorphism. This is the connection one-form linearity needed
when the covariant derivative of a field is assembled by addition. -/
theorem metricSkewSpinLift_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A₁ A₂ : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg (A₁ + A₂) =
      metricSkewSpinLift b g hg A₁ + metricSkewSpinLift b g hg A₂ := by
  unfold metricSkewSpinLift
  simp only [LinearMap.add_apply, spinBivector_add_left]
  rw [Finset.sum_add_distrib, smul_add]

/-- Scalar linearity of the chosen-basis bivector representative. -/
theorem metricSkewSpinLift_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (r : ℝ) (A : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg (r • A) =
      r • metricSkewSpinLift b g hg A := by
  unfold metricSkewSpinLift
  simp only [LinearMap.smul_apply, spinBivector_smul_left]
  rw [← Finset.smul_sum]
  rw [smul_smul, smul_smul, mul_comm (1 / 2 : ℝ) r]

private theorem endCommutator_sum_left
    {ι : Type*} [Fintype ι]
    (F : ι → FormEnd V) (B : FormEnd V) :
    endCommutator (∑ i, F i) B = ∑ i, endCommutator (F i) B := by
  simp only [endCommutator, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- A metric-skew endomorphism is realized on Clifford generators by the
commutator with the bivector representative constructed from the supplied
metric-dual basis. This proves the pointwise algebraic action identity needed
for a Kosmann lift; the basis-independent operator theorem above removes the
choice of basis, but this file does not construct bundle transition maps. -/
theorem metricSkewSpinLift_comm_cartanCliffordAction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate)
    (hgsymm : ∀ x y, g x y = g y x)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (w : V) :
    endCommutator
        (metricSkewSpinLift b g hg A)
        (cartanCliffordAction g w) =
      cartanCliffordAction g (A w) := by
  let bStar := g.dualBasis hg b
  have hpair (i : ι) : g (bStar i) w = b.repr w i := by
    rw [← b.sum_repr w]
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp
    · intro j hj hji
      rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp [hji]
    · simp
  have hfirst :
      ∑ i, g (bStar i) w • cartanCliffordAction g (A (b i)) =
        cartanCliffordAction g (A w) := by
    simp_rw [hpair]
    let L := (cartanCliffordActionMap g).comp A
    change ∑ i, b.repr w i •
        L (b i) = L w
    simp_rw [← map_smul L]
    rw [← map_sum L (fun i => b.repr w i • b i) Finset.univ]
    rw [b.sum_repr w]
  have hskew (i : ι) : g (A (b i)) w = -g (b i) (A w) :=
    eq_neg_of_add_eq_zero_left (hA (b i) w)
  have hdualReconstruct :
      ∑ i, g (b i) (A w) • bStar i = A w := by
    calc
      ∑ i, g (b i) (A w) • bStar i =
          ∑ i, bStar.repr (A w) i • bStar i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [LinearMap.BilinForm.dualBasis_repr_apply, hgsymm]
      _ = A w := bStar.sum_repr (A w)
  have hsecond :
      ∑ i, g (A (b i)) w • cartanCliffordAction g (bStar i) =
        -cartanCliffordAction g (A w) := by
    calc
      ∑ i, g (A (b i)) w • cartanCliffordAction g (bStar i) =
          -∑ i, g (b i) (A w) • cartanCliffordAction g (bStar i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hskew]
            module
      _ = -cartanCliffordAction g (A w) := by
            have hmap := congrArg (cartanCliffordActionMap g) hdualReconstruct
            simp only [map_sum, map_smul] at hmap
            exact congrArg Neg.neg hmap
  unfold metricSkewSpinLift
  rw [endCommutator_smul_left, endCommutator_sum_left]
  simp_rw [spinBivector_comm_cartanCliffordAction g hgsymm]
  rw [show (1 / 2 : ℝ) •
      (∑ i, (g (bStar i) w • cartanCliffordAction g (A (b i)) -
        g (A (b i)) w • cartanCliffordAction g (bStar i))) =
      (1 / 2 : ℝ) • (cartanCliffordAction g (A w) -
        -cartanCliffordAction g (A w)) by rw [Finset.sum_sub_distrib, hfirst, hsecond]]
  module

/-- The commutator of metric-skew endomorphisms is metric-skew. This is the
pointwise Lie-algebra closure needed to transport curvature through the spin
lift; no definiteness assumption on the symmetric form is used. -/
theorem metricSkewEnd_comm_metricSkew
    (g : LinearMap.BilinForm ℝ V)
    (A B : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (hB : ∀ x y, g (B x) y + g x (B y) = 0)
    (x y : V) :
    g ((A.comp B - B.comp A) x) y +
        g x ((A.comp B - B.comp A) y) = 0 := by
  have hAB : g (A (B x)) y = g x (B (A y)) := by
    have h₁ := hA (B x) y
    have h₂ := hB x (A y)
    linarith
  have hBA : g (B (A x)) y = g x (A (B y)) := by
    have h₁ := hB (A x) y
    have h₂ := hA x (B y)
    linarith
  change g (A (B x) - B (A x)) y +
    g x (A (B y) - B (A y)) = 0
  simp only [LinearMap.sub_apply, map_sub]
  rw [hAB, hBA]
  abel

/-- The spin lift represents the Lie bracket on Clifford generators: the
commutator of two lifted metric-skew endomorphisms acts on every Clifford
generator exactly as the commutator of the original endomorphisms. This is
the pointwise Lie-algebra compatibility that a curved Kosmann construction
would need; no curved bundle or curvature tensor is defined here. -/
theorem metricSkewSpinLift_commutator_action
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate)
    (hgsymm : ∀ x y, g x y = g y x)
    (A B : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (hB : ∀ x y, g (B x) y + g x (B y) = 0)
    (w : V) :
    endCommutator
        (endCommutator (metricSkewSpinLift b g hg A)
          (metricSkewSpinLift b g hg B))
        (cartanCliffordAction g w) =
      cartanCliffordAction g ((A.comp B - B.comp A) w) := by
  calc
    endCommutator
        (endCommutator (metricSkewSpinLift b g hg A)
          (metricSkewSpinLift b g hg B))
        (cartanCliffordAction g w) =
      endCommutator (metricSkewSpinLift b g hg A)
          (endCommutator (metricSkewSpinLift b g hg B)
            (cartanCliffordAction g w)) -
        endCommutator (metricSkewSpinLift b g hg B)
          (endCommutator (metricSkewSpinLift b g hg A)
            (cartanCliffordAction g w)) := by
          simpa only [endCommutator] using
            (commutator_jacobi
              (metricSkewSpinLift b g hg A)
              (metricSkewSpinLift b g hg B)
              (cartanCliffordAction g w))
    _ = cartanCliffordAction g (A (B w)) -
          cartanCliffordAction g (B (A w)) := by
          rw [metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm B hB w,
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm A hA w,
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm A hA (B w),
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm B hB (A w)]
    _ = cartanCliffordAction g ((A.comp B - B.comp A) w) := by
          change cartanCliffordActionMap g (A (B w)) -
            cartanCliffordActionMap g (B (A w)) = _
          rw [← map_sub]
          simp only [LinearMap.sub_apply, LinearMap.comp_apply]
          simp only [cartanCliffordActionMap_apply]

/-! ### Spin connection one-forms on a fixed real Clifford module

Given a linear family of metric-skew endomorphisms, the preceding basis
representative assembles into a linear one-form with values in the real
Kähler--Atiyah operator algebra. This is the algebraic, fixed-fiber
connection-lifting step; it does not supply a tangent/spinor bundle, local
trivializations, or a curved covariant derivative.
-/

/-- The spin-operator-valued one-form induced by a linear family of
endomorphisms of `V`. -/
def metricSkewSpinConnection
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A : U →ₗ[ℝ] V →ₗ[ℝ] V) :
    U →ₗ[ℝ] FormEnd V where
  toFun x := metricSkewSpinLift b g hg (A x)
  map_add' x y := by
    rw [map_add A x y]
    exact metricSkewSpinLift_add b g hg (A x) (A y)
  map_smul' r x := by
    rw [map_smul A r x]
    exact metricSkewSpinLift_smul b g hg r (A x)

/-- The spin-operator-valued connection one-form is independent of the basis
used to write its metric-dual contraction. The equality is in the linear-map
space of one-forms, not merely pointwise after acting on Clifford generators. -/
theorem metricSkewSpinConnection_basis_independent
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V) :
    metricSkewSpinConnection b g hg A =
      metricSkewSpinConnection c g hg A := by
  apply LinearMap.ext
  intro x
  exact metricSkewSpinLift_basis_independent b c g hg (A x)

/-- The induced spin connection one-form acts on Clifford generators by the
original metric-skew endomorphism-valued one-form. -/
theorem metricSkewSpinConnection_comm_cartanCliffordAction
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (x : U) (w : V) :
    endCommutator
        (metricSkewSpinConnection b g hg A x)
        (cartanCliffordAction g w) =
      cartanCliffordAction g (A x w) := by
  exact metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
    (A x) (hA x) w

/-- The curvature action of the induced real spin connection agrees on
Clifford generators with the curvature action of the underlying
metric-skew endomorphism connection.  The bracket term is kept explicit, so
this statement applies to a Lie-algebra connection once its base bracket is
instantiated; it does not assert the existence of a curved spinor bundle. -/
theorem metricSkewSpinConnection_curvature_action
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (bracket : U → U → U) (x y : U) (w : V) :
    endCommutator
        (endCommutator (metricSkewSpinConnection b g hg A x)
          (metricSkewSpinConnection b g hg A y))
        (cartanCliffordAction g w) -
      endCommutator (metricSkewSpinConnection b g hg A (bracket x y))
        (cartanCliffordAction g w) =
      cartanCliffordAction g
        (A x (A y w) - A y (A x w) - A (bracket x y) w) := by
  change endCommutator
      (endCommutator (metricSkewSpinLift b g hg (A x))
        (metricSkewSpinLift b g hg (A y)))
      (cartanCliffordAction g w) -
    endCommutator (metricSkewSpinLift b g hg (A (bracket x y)))
      (cartanCliffordAction g w) = _
  rw [metricSkewSpinLift_commutator_action b g hg hgsymm
      (A x) (A y) (hA x) (hA y) w,
    metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
      (A (bracket x y)) (hA (bracket x y)) w]
  change cartanCliffordActionMap g
        (A x (A y w) - A y (A x w)) -
      cartanCliffordActionMap g (A (bracket x y) w) = _
  rw [← map_sub]
  simp only [cartanCliffordActionMap_apply]

/-- If the metric-skew connection on the vector module is a representation of
the supplied Lie bracket, its induced real spin connection has zero curvature
defect on every Clifford generator. This is the representation-compatibility
condition needed before transporting such a connection through a colimit. -/
theorem metricSkewSpinConnection_curvature_vanishes_on_generators
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (bracket : U → U → U) (x y : U)
    (hcurv : ∀ w : V,
      A x (A y w) - A y (A x w) = A (bracket x y) w) :
    endCommutator
        (endCommutator (metricSkewSpinConnection b g hg A x)
          (metricSkewSpinConnection b g hg A y))
        (cartanCliffordAction g w) -
      endCommutator (metricSkewSpinConnection b g hg A (bracket x y))
        (cartanCliffordAction g w) = 0 := by
  rw [metricSkewSpinConnection_curvature_action b g hg hgsymm A hA
    bracket x y w]
  have h : A x (A y w) - A y (A x w) - A (bracket x y) w = 0 := by
    rw [hcurv w]
    simp
  rw [h]
  exact map_zero (cartanCliffordActionMap g)

end InfoGeometry.Canonical.KahlerAtiyahSpinConnection
