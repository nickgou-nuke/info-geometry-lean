/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LatticeGauge.FinitePlaquette
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.PEquiv

/-!
# Operator-valued monomial braiding

The shift convention is row `i`, column `σ i`. Both vertex and edge labels are
units in an arbitrary coefficient ring, with no centrality assumption. The
braiding factor is the existing lattice-gauge plaquette holonomy on the explicit
loop/shift lattice below. Native invertible matrices realize its braid relation and
group commutator. All statements are algebraic and finite-indexed; no continuum
limit or discrete-to-infinitesimal correspondence is asserted.
-/

namespace InfoGeometry.Weyl.OperatorBraiding

open Matrix
open InfoGeometry.LatticeGauge

section GroupHolonomy

variable {ι G : Type*} [Group G]

/-- At every vertex there is a loop and an oriented edge to `σ i`. -/
def loopShiftLattice (σ : Equiv.Perm ι) : PlaquetteLattice ι (Bool × ι) ι where
  source := Prod.snd
  target := fun e => if e.1 then σ e.2 else e.2
  bottom := fun i => (false, i)
  right := fun i => (true, i)
  top := fun i => (false, σ i)
  left := fun i => (true, i)
  bottom_right := fun _ => rfl
  right_top := fun _ => rfl
  top_left := fun _ => rfl
  left_bottom := fun _ => rfl

/-- The loop labels are `V`; the shift-edge labels are `U`. -/
def loopShiftLinks (U V : ι → G) : Bool × ι → G
  | (false, i) => V i
  | (true, i) => U i

/-- Operator-valued braiding holonomy, realized by the existing plaquette owner. -/
def braidingHolonomy (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) : G :=
  plaquetteHolonomy (loopShiftLattice σ) (loopShiftLinks U V) i

@[simp] theorem braidingHolonomy_apply (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) :
    braidingHolonomy σ U V i = V i * U i * (V (σ i))⁻¹ * (U i)⁻¹ := rfl

/-- Cancellation preserves the order of all four noncommuting factors. -/
theorem braidingHolonomy_mul (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) :
    braidingHolonomy σ U V i * U i * V (σ i) = V i * U i := by
  simp [mul_assoc]

/-- Flatness means that the vertex labels intertwine along the weighted edge. -/
theorem braidingHolonomy_eq_one_iff (σ : Equiv.Perm ι) (U V : ι → G) (i : ι) :
    braidingHolonomy σ U V i = 1 ↔ V i * U i = U i * V (σ i) := by
  rw [braidingHolonomy_apply, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

/-- Gauge action on an edge with source `i` and target `σ i`. -/
def edgeGauge (σ : Equiv.Perm ι) (g U : ι → G) : ι → G :=
  fun i => g i * U i * (g (σ i))⁻¹

/-- Gauge action on a loop at a vertex. -/
def vertexGauge (g V : ι → G) : ι → G :=
  fun i => g i * V i * (g i)⁻¹

theorem gaugeTransform_loopShiftLinks (σ : Equiv.Perm ι) (g U V : ι → G) :
    gaugeTransform (loopShiftLattice σ) g (loopShiftLinks U V) =
      loopShiftLinks (edgeGauge σ g U) (vertexGauge g V) := by
  funext e
  rcases e with ⟨b, i⟩
  cases b <;> rfl

/-- Homogeneous covariance is inherited from the existing plaquette theorem. -/
theorem braidingHolonomy_gauge (σ : Equiv.Perm ι) (g U V : ι → G) (i : ι) :
    braidingHolonomy σ (edgeGauge σ g U) (vertexGauge g V) i =
      g i * braidingHolonomy σ U V i * (g i)⁻¹ := by
  unfold braidingHolonomy
  rw [← gaugeTransform_loopShiftLinks]
  exact plaquetteHolonomy_gauge_covariant (loopShiftLattice σ) g (loopShiftLinks U V) i

end GroupHolonomy

section Matrices

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]

/-- A diagonal matrix whose diagonal entries are arbitrary coefficient units. -/
def clock (V : ι → Aˣ) : Matrix ι ι A :=
  diagonal fun i => (V i : A)

/-- The native permutation matrix, with row `i` supported at column `σ i`. -/
def permutationUnit (σ : Equiv.Perm ι) : (Matrix ι ι A)ˣ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    simp
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    simp

/-- The diagonal matrix is a genuine unit, without a determinant or commutative base. -/
def clockUnit (V : ι → Aˣ) : (Matrix ι ι A)ˣ where
  val := clock V
  inv := clock fun i => (V i)⁻¹
  val_inv := by
    simp [clock, diagonal_mul_diagonal]
  inv_val := by
    simp [clock, diagonal_mul_diagonal]

/-- Weighted monomial shift, retaining each edge label on the left of the permutation. -/
def shift (σ : Equiv.Perm ι) (U : ι → Aˣ) : Matrix ι ι A :=
  clock U * σ.toPEquiv.toMatrix

/-- A weighted shift is a product of two explicitly constructed invertible matrices. -/
def shiftUnit (σ : Equiv.Perm ι) (U : ι → Aˣ) : (Matrix ι ι A)ˣ :=
  clockUnit U * permutationUnit σ

@[simp] theorem clockUnit_val (V : ι → Aˣ) :
    (clockUnit V : Matrix ι ι A) = clock V := rfl

@[simp] theorem shiftUnit_val (σ : Equiv.Perm ι) (U : ι → Aˣ) :
    (shiftUnit σ U : Matrix ι ι A) = shift σ U := rfl

/-- The diagonal realization does not identify distinct operator-unit labels. -/
theorem clockUnit_injective : Function.Injective (clockUnit (ι := ι) (A := A)) := by
  intro V W h
  funext i
  apply Units.ext
  have hi := congrArg (fun u : (Matrix ι ι A)ˣ => (u : Matrix ι ι A) i i) h
  simpa [clock] using hi

@[simp] theorem clockUnit_eq_one_iff (V : ι → Aˣ) :
    clockUnit V = 1 ↔ ∀ i, V i = 1 := by
  have h_one : clockUnit (fun _ : ι => (1 : Aˣ)) = 1 := by
    apply Units.ext
    simp [clock]
  rw [← h_one, clockUnit_injective.eq_iff]
  exact funext_iff

@[simp] theorem shift_apply (σ : Equiv.Perm ι) (U : ι → Aˣ) (i j : ι) :
    shift σ U i j = if j = σ i then (U i : A) else 0 := by
  simp [shift, clock, diagonal_mul, PEquiv.toMatrix_apply, eq_comm]

/-- The exact noncentral operator braid. The phase is a diagonal operator matrix. -/
theorem clock_shift_braid (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    clock V * shift σ U = clock (braidingHolonomy σ U V) * shift σ U * clock V := by
  ext i j
  simp only [clock, diagonal_mul, mul_diagonal]
  by_cases h : j = σ i
  · subst j
    simp only [shift_apply]
    exact (congrArg (fun u : Aˣ => (u : A)) (braidingHolonomy_mul σ U V i)).symm
  · simp [shift_apply, h]

/-- The same braid in the unit group of the matrix ring. -/
theorem clockUnit_shiftUnit_braid (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    clockUnit V * shiftUnit σ U =
      clockUnit (braidingHolonomy σ U V) * shiftUnit σ U * clockUnit V := by
  apply Units.ext
  exact clock_shift_braid σ U V

/-- The group commutator is exactly the plaquette holonomy matrix. -/
theorem clockUnit_shiftUnit_commutator (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    clockUnit V * shiftUnit σ U * (clockUnit V)⁻¹ * (shiftUnit σ U)⁻¹ =
      clockUnit (braidingHolonomy σ U V) := by
  rw [clockUnit_shiftUnit_braid]
  group

/-- Commutativity is equivalent to flatness; no flatness assumption enters the braid. -/
theorem clockUnit_shiftUnit_commute_iff (σ : Equiv.Perm ι) (U V : ι → Aˣ) :
    Commute (clockUnit V) (shiftUnit σ U) ↔
      ∀ i, braidingHolonomy σ U V i = 1 := by
  rw [commute_iff_eq]
  constructor
  · intro h
    apply (clockUnit_eq_one_iff _).mp
    rw [← clockUnit_shiftUnit_commutator, h]
    group
  · intro h
    have braid := clockUnit_shiftUnit_braid σ U V
    rw [(clockUnit_eq_one_iff _).mpr h, one_mul] at braid
    exact braid

/-- A vertex gauge acts by conjugation on the diagonal vertex matrix. -/
theorem clock_vertexGauge (g V : ι → Aˣ) :
    clock (vertexGauge g V) = clock g * clock V * clock (fun i => (g i)⁻¹) := by
  simp [clock, vertexGauge, diagonal_mul_diagonal, mul_assoc]

/-- The edge gauge action is matrix conjugation, including the target-vertex factor. -/
theorem shift_edgeGauge (σ : Equiv.Perm ι) (g U : ι → Aˣ) :
    shift σ (edgeGauge σ g U) =
      clock g * shift σ U * clock (fun i => (g i)⁻¹) := by
  ext i j
  simp only [clock, diagonal_mul, mul_diagonal]
  by_cases h : j = σ i
  · subst j
    simp [shift_apply, edgeGauge]
  · simp [shift_apply, h]

/-- Plaquette covariance in the same native matrix carrier as the braid. -/
theorem clock_braidingHolonomy_gauge (σ : Equiv.Perm ι) (g U V : ι → Aˣ) :
    clock (braidingHolonomy σ (edgeGauge σ g U) (vertexGauge g V)) =
      clock g * clock (braidingHolonomy σ U V) * clock (fun i => (g i)⁻¹) := by
  rw [← clock_vertexGauge]
  congr 1
  funext i
  exact braidingHolonomy_gauge σ g U V i

end Matrices

end InfoGeometry.Weyl.OperatorBraiding
