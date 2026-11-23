/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Noncommutative gauge curvature and braided holonomy

Finite algebraic results over associative rings. These statements do not
assert analytic gauge theory, topology, or a classification of braid groups.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeGaugeAndBraidedHolonomy

section Jet

variable {B : Type*} [Ring B]

def expJet2 (X : B) : B := 2 + 2 * X + X * X

theorem expJet2_commutator (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
        2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
        (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

theorem expJet2_commutator_of_sq_eq_zero {X Y : B}
    (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [expJet2_commutator, hX, hY]
  noncomm_ring

end Jet

section Derivations

variable {B : Type*} [Ring B]

def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ x y, d (x * y) = d x * y + x * d y

theorem IsRingDeriv.map_one {d : B →+ B} (hd : IsRingDeriv d) : d 1 = 0 := by
  have h : d 1 = d 1 + d 1 := by simpa only [mul_one, one_mul] using hd 1 1
  calc
    d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self _

theorem IsRingDeriv.map_units_inv {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -((↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B)) := by
  have h := hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h
  have hi : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  have h' : (u : B) * d (↑u⁻¹ : B) = -(d (u : B) * (↑u⁻¹ : B)) :=
    eq_neg_of_add_eq_zero_right h.symm
  calc
    d (↑u⁻¹ : B) = 1 * d (↑u⁻¹ : B) := by rw [one_mul]
    _ = ((↑u⁻¹ : B) * (u : B)) * d (↑u⁻¹ : B) := by rw [hi]
    _ = (↑u⁻¹ : B) * ((u : B) * d (↑u⁻¹ : B)) := by noncomm_ring
    _ = (↑u⁻¹ : B) * (-(d (u : B) * (↑u⁻¹ : B))) := by rw [h']
    _ = -((↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B)) := by noncomm_ring

def liftMatrixDeriv {S : Type*} [Ring S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : S →+ S) : Matrix ι ι S →+ Matrix ι ι S where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by
    ext i j
    exact map_add d (M i j) (N i j)

theorem IsRingDeriv.liftMatrix {S : Type*} [Ring S] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d : S →+ S} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (ι := ι) d) := by
  intro M N
  ext i k
  change d (∑ j, M i j * N j k) =
    (∑ j, d (M i j) * N j k) + ∑ j, M i j * d (N j k)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hd (M i j) (N j k)

end Derivations

section GaugeCurvature

variable {B : Type*} [Ring B]

def covDeriv (d : B →+ B) (A ψ : B) : B := d ψ + A * ψ

def curvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def gaugeConn (d : B →+ B) (u : Bˣ) (A : B) : B :=
  (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)

theorem covariant_curvature_multiplication
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hcomm : ∀ x, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : B) :
    covDeriv d₁ A₁ (covDeriv d₂ A₂ ψ) -
      covDeriv d₂ A₂ (covDeriv d₁ A₁ ψ) = curvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covDeriv, curvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, hcomm ψ]
  noncomm_ring

theorem covariant_gauge_intertwining {d : B →+ B} (hd : IsRingDeriv d)
    (u : Bˣ) (A ψ : B) :
    covDeriv d (gaugeConn d u A) ((u : B) * ψ) = (u : B) * covDeriv d A ψ := by
  dsimp [covDeriv, gaugeConn]
  rw [hd (u : B) ψ]
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  calc
    d (u : B) * ψ + (u : B) * d ψ +
        ((u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)) * ((u : B) * ψ)
      = d (u : B) * ψ + (u : B) * d ψ +
          (u : B) * A * ((↑u⁻¹ : B) * (u : B)) * ψ -
            d (u : B) * ((↑u⁻¹ : B) * (u : B)) * ψ := by noncomm_ring
    _ = d (u : B) * ψ + (u : B) * d ψ +
          (u : B) * A * 1 * ψ - d (u : B) * 1 * ψ := by rw [hu]
    _ = (u : B) * (d ψ + A * ψ) := by noncomm_ring

theorem curvature_gauge_covariance
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hcomm : ∀ x, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) (A₁ A₂ : B) :
    curvature d₁ d₂ (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) =
      (u : B) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by
  have hleft := covariant_curvature_multiplication hd₁ hd₂ hcomm
    (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) ((u : B) * 1)
  rw [covariant_gauge_intertwining hd₂ u A₂ 1,
    covariant_gauge_intertwining hd₁ u A₁ (covDeriv d₂ A₂ 1),
    covariant_gauge_intertwining hd₁ u A₁ 1,
    covariant_gauge_intertwining hd₂ u A₂ (covDeriv d₁ A₁ 1)] at hleft
  have hright := covariant_curvature_multiplication hd₁ hd₂ hcomm A₁ A₂ 1
  have hmul : curvature d₁ d₂ (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) * (u : B) =
      (u : B) * curvature d₁ d₂ A₁ A₂ := by
    calc
      _ = curvature d₁ d₂ (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) * ((u : B) * 1) := by rw [mul_one]
      _ = (u : B) * covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) -
          (u : B) * covDeriv d₂ A₂ (covDeriv d₁ A₁ 1) := hleft.symm
      _ = (u : B) * (covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) -
          covDeriv d₂ A₂ (covDeriv d₁ A₁ 1)) := by noncomm_ring
      _ = (u : B) * (curvature d₁ d₂ A₁ A₂ * 1) := by rw [hright]
      _ = (u : B) * curvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc
    _ = curvature d₁ d₂ (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) *
          ((u : B) * (↑u⁻¹ : B)) := by rw [Units.mul_inv, mul_one]
    _ = (curvature d₁ d₂ (gaugeConn d₁ u A₁) (gaugeConn d₂ u A₂) * (u : B)) *
          (↑u⁻¹ : B) := by noncomm_ring
    _ = (u : B) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by rw [hmul]

theorem maurer_cartan_flatness
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (hcomm : ∀ x, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) :
    curvature d₁ d₂ (-d₁ (u : B) * (↑u⁻¹ : B))
      (-d₂ (u : B) * (↑u⁻¹ : B)) = 0 := by
  have h₁ : -d₁ (u : B) * (↑u⁻¹ : B) = gaugeConn d₁ u 0 := by
    dsimp [gaugeConn]; noncomm_ring
  have h₂ : -d₂ (u : B) * (↑u⁻¹ : B) = gaugeConn d₂ u 0 := by
    dsimp [gaugeConn]; noncomm_ring
  rw [h₁, h₂, curvature_gauge_covariance hd₁ hd₂ hcomm u 0 0]
  dsimp [curvature]
  rw [Ring.lie_def, map_zero, map_zero]
  noncomm_ring

def adjointCovDeriv (d : B →+ B) (A X : B) : B := d X + ⁅A, X⁆

/-- The differential Second Bianchi identity for three commuting Leibniz derivations.
The carrier remains the given associative ring; the commutator terms are essential. -/
theorem differential_second_bianchi
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjointCovDeriv d₁ A₁ (curvature d₂ d₃ A₂ A₃) +
      adjointCovDeriv d₂ A₂ (curvature d₃ d₁ A₃ A₁) +
      adjointCovDeriv d₃ A₃ (curvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjointCovDeriv, curvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
    h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

end GaugeCurvature

section WilsonCocycle

variable {G : Type*} [Group G]

def conjugateBy (x q : G) : G := x * q * x⁻¹

def wilsonCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjugateBy X (wilsonCocycle X Q n)

theorem braided_pow_law {X Z Q : G} (h : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = wilsonCocycle X Q n * X ^ n * Z := by
  induction n with
  | zero => simp [wilsonCocycle]
  | succ n ih =>
      calc
        Z * X ^ (n + 1) = (Z * X) * X ^ n := by rw [pow_succ']; group
        _ = (Q * X * Z) * X ^ n := by rw [h]
        _ = Q * X * (Z * X ^ n) := by group
        _ = Q * X * (wilsonCocycle X Q n * X ^ n * Z) := by rw [ih]
        _ = (Q * (X * wilsonCocycle X Q n * X⁻¹)) * X ^ (n + 1) * Z := by
          rw [pow_succ']
          group
        _ = wilsonCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [wilsonCocycle, conjugateBy]

theorem wilsonCocycle_add (X Q : G) (m n : ℕ) :
    wilsonCocycle X Q (m + n) =
      wilsonCocycle X Q m * conjugateBy (X ^ m) (wilsonCocycle X Q n) := by
  induction m with
  | zero => simp [wilsonCocycle, conjugateBy]
  | succ m ih =>
      have hmn : m + 1 + n = (m + n) + 1 := by omega
      rw [hmn, wilsonCocycle, ih, wilsonCocycle]
      have hmul (a b : G) : conjugateBy X (a * b) =
          conjugateBy X a * conjugateBy X b := by
        dsimp [conjugateBy]
        group
      rw [hmul]
      have hcomp : conjugateBy X (conjugateBy (X ^ m) (wilsonCocycle X Q n)) =
          conjugateBy (X ^ (m + 1)) (wilsonCocycle X Q n) := by
        dsimp [conjugateBy]
        rw [pow_succ']
        group
      rw [hcomp]
      rw [mul_assoc]

theorem wilsonCocycle_eq_one_of_pow_eq_one {X Z Q : G}
    (h : Z * X = Q * X * Z) {N : ℕ} (hX : X ^ N = 1) :
    wilsonCocycle X Q N = 1 := by
  have hn := braided_pow_law h N
  rw [hX, mul_one, mul_one] at hn
  calc
    wilsonCocycle X Q N = (wilsonCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← hn]
    _ = 1 := mul_inv_cancel Z

end WilsonCocycle

section BlockHolonomy

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev BlockMat := Matrix (Fin 2) (Fin 2) Mat2Z

def W0 : Mat2Z := ![![0, 1], ![1, 0]]
def W1 : Mat2Z := ![![1, 0], ![0, -1]]
def G : Mat2Z := ![![1, -1], ![0, 1]]
def Ginv : Mat2Z := ![![1, 1], ![0, 1]]
def Xblock : BlockMat := ![![0, G], ![Ginv, 0]]
def Zblock : BlockMat := ![![W0, 0], ![0, W1]]
def Qblock : BlockMat := (Zblock * Xblock) * (Zblock * Xblock)
def Q0 : Mat2Z := ![![0, -1], ![1, 2]]

theorem Xblock_sq : Xblock * Xblock = 1 := by decide
theorem Zblock_sq : Zblock * Zblock = 1 := by decide
theorem block_braiding : Zblock * Xblock = Qblock * Xblock * Zblock := by decide
theorem Qblock_noncomm_X : Qblock * Xblock ≠ Xblock * Qblock := by decide
theorem Qblock_noncomm_Z : Qblock * Zblock ≠ Zblock * Qblock := by decide
theorem Qblock_sq_ne_one : Qblock * Qblock ≠ 1 := by decide
theorem Qblock_wilson_closure : Qblock * (Xblock * Qblock * Xblock) = 1 := by decide

end BlockHolonomy

section MajoranaBraid

theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E F : B}
    (hE : E * E = -1) (hEF : E * F + F * E = 0) :
    (1 + E) * (1 + F) * (1 + E) = 2 * (E + F) := by
  calc
    (1 + E) * (1 + F) * (1 + E) =
        2 * (E + F) + (E * E + 1) * (1 - F) + (1 + E) * (E * F + F * E) := by
          noncomm_ring
    _ = 2 * (E + F) := by rw [hE, hEF]; noncomm_ring

theorem clifford_majorana_braid {B : Type*} [Ring B] {E F : B}
    (hE : E * E = -1) (hF : F * F = -1)
    (hEF : E * F + F * E = 0) :
    (1 + E) * (1 + F) * (1 + E) = (1 + F) * (1 + E) * (1 + F) := by
  have hFE : F * E + E * F = 0 := by rw [add_comm, hEF]
  rw [clifford_bivector_triple_product hE hEF,
    clifford_bivector_triple_product hF hFE]
  rw [add_comm E F]

def E12 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]]
def E23 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 0, -1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, -1, 0, 0]]
def R12 : Matrix (Fin 4) (Fin 4) ℤ := 1 + E12
def R23 : Matrix (Fin 4) (Fin 4) ℤ := 1 + E23

theorem E12_sq : E12 * E12 = -1 := by decide
theorem E23_sq : E23 * E23 = -1 := by decide
theorem E12_E23_anticomm : E12 * E23 + E23 * E12 = 0 := by decide

theorem mat4_braid_and_noncommuting :
    R12 * R23 * R12 = R23 * R12 * R23 ∧ R12 * R23 ≠ R23 * R12 := by
  refine ⟨clifford_majorana_braid E12_sq E23_sq E12_E23_anticomm, ?_⟩
  decide

end MajoranaBraid

section QuaternionBivectors

variable {R : Type*} [Ring R]

def commutator (x y : R) : R := x * y - y * x

theorem quaternion_bivector_relations {e f : R}
    (he : e * e = -1) (hf : f * f = -1) (hanti : e * f + f * e = 0) :
    (e * f) * (e * f) = -1 ∧
    commutator e f = 2 * (e * f) ∧
    commutator f (e * f) = 2 * e ∧
    commutator (e * f) e = 2 * f := by
  have hfe : f * e = -(e * f) := eq_neg_of_add_eq_zero_right hanti
  constructor
  · calc
      (e * f) * (e * f) = e * (f * e) * f := by noncomm_ring
      _ = e * (-(e * f)) * f := by rw [hfe]
      _ = -1 := by
        calc
          e * (-(e * f)) * f = -(e * (e * f) * f) := by noncomm_ring
          _ = -((e * e) * (f * f)) := by noncomm_ring
          _ = -1 := by rw [he, hf]; norm_num
  constructor
  · dsimp [commutator]
    rw [hfe, sub_neg_eq_add, two_mul]
  constructor
  · dsimp [commutator]
    calc
      f * (e * f) - (e * f) * f = (f * e) * f - e * (f * f) := by noncomm_ring
      _ = (-(e * f)) * f - e * (-1) := by rw [hfe, hf]
      _ = -(e * (f * f)) + e := by noncomm_ring
      _ = e + e := by rw [hf]; simp
      _ = 2 * e := by rw [two_mul]
  · dsimp [commutator]
    calc
      (e * f) * e - e * (e * f) = e * (f * e) - (e * e) * f := by noncomm_ring
      _ = e * (-(e * f)) - (-1) * f := by rw [hfe, he]
      _ = -((e * e) * f) + f := by noncomm_ring
      _ = f + f := by rw [he]; simp
      _ = 2 * f := by rw [two_mul]

theorem cayley_rotor_noncommute {R : Type*} [Ring R] {e f : R}
    (hanti : e * f + f * e = 0) :
    commutator (1 + e) (1 + f) = 2 * (e * f) := by
  dsimp [commutator]
  calc
    (1 + e) * (1 + f) - (1 + f) * (1 + e) = e * f - f * e := by noncomm_ring
    _ = 2 * (e * f) := by
      have hfe : f * e = -(e * f) := eq_neg_of_add_eq_zero_right hanti
      rw [hfe, sub_neg_eq_add, two_mul]

end QuaternionBivectors

end InfoGeometry.OperatorAlgebra.NoncommutativeGaugeAndBraidedHolonomy
