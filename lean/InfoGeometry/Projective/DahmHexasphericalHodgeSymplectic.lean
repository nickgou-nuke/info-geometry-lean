/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadric

/-!
# Dahm (bfIS-2026-02) over an operator ring: Lie spheres, Hodge split, `J`-symmetric pair

Every statement here is over an arbitrary, in general **noncommutative**, ring of
operators `A`.  No commutativity of coordinates is assumed; where the commutative
formula would identify `ab` with `ba`, the operator statement keeps both orders.

* **Lie hexaspherical coordinates (Sec. II.D, Eq. 14–15).**  For operator-valued
  centre `(ξ, η, ζ)` and oriented radius `R`, the homogeneous coordinates
  `hexa2 = (1 + s, 1 - s, 2ξ, 2η, 2ζ, 2R)`, `s = ξ² + η² + ζ² - R²`, lie on the
  `(4,2)` Lie quadric (`lieForm_hexa2`).  The difference of two spheres has
  `lieForm = 4 · ((ξ-ξ')² + (η-η')² + (ζ-ζ')² - (R-R')²)` and the symmetrised polar
  form is its negative (`lieForm_hexa2_sub`, `liePolarSym_hexa2`): oriented contact
  as an operator identity.
* **Hodge split (Sec. I.A, II.H, V.B).**  On the owner `Plucker6 A` carrier the
  Hodge star is an involution, `⟨P, ⋆P⟩ = kleinQ P + kleinQ (⋆P)`, and
  `|P + ⋆P|² - |P - ⋆P|² = 4 (kleinQ P + kleinQ (⋆P))`.  For a central complex
  structure `I` (`I² = -1`), Minkowski's combined square is
  `Σ (m_k + I e_k)² = Σ (m_k² - e_k²) + I (kleinQ P + kleinQ (⋆P))`.
* **Symmetric pair for a complex structure (Sec. II.E, III).**  In any ring with an
  involutive anti-automorphism `star` (a `*`-ring, e.g. an operator algebra), for
  `J` with `star J = -J`, `J² = -1`, `θ M = J (star M) J` is an involutive Lie
  automorphism; its `±1` eigenspaces are `{M | star M J + J M = 0}` (symplectic)
  and `{M | star M J = J M}`, with the Cartan bracket relations.  Dahm's
  `Q₀₂ = 1 ⊗ q₂` is instantiated on `4 × 4` matrices over an arbitrary `*`-ring.

## Scope

Not proved: dimension counts (`10 = 4 + 6`, `15 = 5 + 10`), the real-form
identifications, or any physical reading.
-/

namespace InfoGeometry.Projective.DahmHexasphericalHodgeSymplectic

open Matrix
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.KleinQuadric.Plucker6 (kleinQ)

/-! ### Lie hexaspherical coordinates over an operator ring -/

section Hexaspherical

variable {A : Type*} [Ring A]

/-- Hexaspherical coordinates `(y₀, …, y₅)` with operator entries. -/
structure Hexa6 (A : Type*) where
  y0 : A
  y1 : A
  y2 : A
  y3 : A
  y4 : A
  y5 : A

/-- The `(4,2)` Lie quadric form `-y₀² + y₁² + y₂² + y₃² + y₄² - y₅²`. -/
def lieForm (y : Hexa6 A) : A :=
  -(y.y0 * y.y0) + y.y1 * y.y1 + y.y2 * y.y2 + y.y3 * y.y3 + y.y4 * y.y4 - y.y5 * y.y5

/-- Coordinatewise difference. -/
def Hexa6.sub (y z : Hexa6 A) : Hexa6 A :=
  ⟨y.y0 - z.y0, y.y1 - z.y1, y.y2 - z.y2, y.y3 - z.y3, y.y4 - z.y4, y.y5 - z.y5⟩

/-- Coordinatewise sum. -/
def Hexa6.add (y z : Hexa6 A) : Hexa6 A :=
  ⟨y.y0 + z.y0, y.y1 + z.y1, y.y2 + z.y2, y.y3 + z.y3, y.y4 + z.y4, y.y5 + z.y5⟩

/-- Symmetrised polar form `lieForm (y + z) - lieForm y - lieForm z`
(the operator replacement of `2 B(y,z)`; it uses both orders `y z` and `z y`). -/
def liePolarSym (y z : Hexa6 A) : A := lieForm (y.add z) - lieForm y - lieForm z

/-- The sphere parameter `s = ξ² + η² + ζ² - R²`. -/
def sphereS (ξ η ζ R : A) : A := ξ * ξ + η * η + ζ * ζ - R * R

/-- Homogeneous (doubled) hexaspherical coordinates of an oriented sphere
(Dahm Eq. 14 scaled by `2`, which avoids inverting `2` in the operator ring). -/
def hexa2 (ξ η ζ R : A) : Hexa6 A :=
  ⟨1 + sphereS ξ η ζ R, 1 - sphereS ξ η ζ R, 2 * ξ, 2 * η, 2 * ζ, 2 * R⟩

/-- Dahm Eq. 15: every operator-valued oriented sphere lies on the Lie quadric. -/
theorem lieForm_hexa2 (ξ η ζ R : A) : lieForm (hexa2 ξ η ζ R) = 0 := by
  simp only [lieForm, hexa2, sphereS]
  noncomm_ring

/-- The difference of two spheres measures oriented contact. -/
theorem lieForm_hexa2_sub (ξ η ζ R ξ' η' ζ' R' : A) :
    lieForm ((hexa2 ξ η ζ R).sub (hexa2 ξ' η' ζ' R')) =
      4 * ((ξ - ξ') * (ξ - ξ') + (η - η') * (η - η') + (ζ - ζ') * (ζ - ζ') -
        (R - R') * (R - R')) := by
  simp only [lieForm, hexa2, sphereS, Hexa6.sub]
  noncomm_ring

/-- In any ring, `lieForm (y - z) = lieForm y + lieForm z - liePolarSym y z`. -/
theorem lieForm_sub_eq (y z : Hexa6 A) :
    lieForm (y.sub z) = lieForm y + lieForm z - liePolarSym y z := by
  simp only [lieForm, liePolarSym, Hexa6.sub, Hexa6.add]
  noncomm_ring

/-- **Oriented contact (operator form):** the symmetrised polar form of two spheres is
`-4 ((ξ-ξ')² + (η-η')² + (ζ-ζ')² - (R-R')²)`. -/
theorem liePolarSym_hexa2 (ξ η ζ R ξ' η' ζ' R' : A) :
    liePolarSym (hexa2 ξ η ζ R) (hexa2 ξ' η' ζ' R') =
      -(4 * ((ξ - ξ') * (ξ - ξ') + (η - η') * (η - η') + (ζ - ζ') * (ζ - ζ') -
        (R - R') * (R - R'))) := by
  have h := lieForm_sub_eq (hexa2 ξ η ζ R) (hexa2 ξ' η' ζ' R')
  rw [lieForm_hexa2_sub, lieForm_hexa2, lieForm_hexa2, zero_add, zero_sub] at h
  rw [h, neg_neg]

end Hexaspherical

/-! ### Hodge split of `Λ²` with operator coordinates -/

section Hodge

variable {A : Type*} [Ring A]

/-- Hodge star on `Λ²` in owner order `(p01,p02,p03,p12,p13,p23)`. -/
def hodge (P : Plucker6 A) : Plucker6 A where
  p01 := P.p23
  p02 := -P.p13
  p03 := P.p12
  p12 := P.p03
  p13 := -P.p02
  p23 := P.p01

/-- Coordinate pairing `⟨P, Q⟩ = Σ P_ij Q_ij` (left factor first). -/
def euclid (P Q : Plucker6 A) : A :=
  P.p01 * Q.p01 + P.p02 * Q.p02 + P.p03 * Q.p03 +
    P.p12 * Q.p12 + P.p13 * Q.p13 + P.p23 * Q.p23

theorem hodge_hodge (P : Plucker6 A) : hodge (hodge P) = P := by
  cases P; simp [hodge]

/-- `⟨P, ⋆P⟩ = kleinQ P + kleinQ (⋆P)`: the operator Klein form appears in both orders. -/
theorem euclid_hodge (P : Plucker6 A) :
    euclid P (hodge P) = kleinQ P + kleinQ (hodge P) := by
  simp only [euclid, hodge, kleinQ]; noncomm_ring

/-- Self-dual part `P + ⋆P`. -/
def selfDual (P : Plucker6 A) : Plucker6 A := Plucker6.add P (hodge P)

/-- Anti-self-dual part `P - ⋆P`. -/
def antiSelfDual (P : Plucker6 A) : Plucker6 A where
  p01 := P.p01 - P.p23
  p02 := P.p02 + P.p13
  p03 := P.p03 - P.p12
  p12 := P.p12 - P.p03
  p13 := P.p13 + P.p02
  p23 := P.p23 - P.p01

theorem hodge_selfDual (P : Plucker6 A) : hodge (selfDual P) = selfDual P := by
  cases P
  simp only [selfDual, hodge, Plucker6.add, Plucker6.mk.injEq]
  constructorm* _ ∧ _ <;> abel

theorem hodge_antiSelfDual (P : Plucker6 A) :
    hodge (antiSelfDual P) = Plucker6.scale (-1) (antiSelfDual P) := by
  cases P
  simp only [antiSelfDual, hodge, Plucker6.scale, Plucker6.mk.injEq]
  constructorm* _ ∧ _ <;> noncomm_ring

/-- Self-dual minus anti-self-dual norm is `4 (kleinQ P + kleinQ (⋆P))`. -/
theorem selfDual_sub_antiSelfDual (P : Plucker6 A) :
    euclid (selfDual P) (selfDual P) - euclid (antiSelfDual P) (antiSelfDual P) =
      4 * (kleinQ P + kleinQ (hodge P)) := by
  simp only [euclid, selfDual, antiSelfDual, hodge, Plucker6.add, kleinQ]; noncomm_ring

/-- **Minkowski's combined square** for a central complex structure `I`, `I² = -1`, with
`m = (p23, -p13, p12)`, `e = (p01, p02, p03)`. -/
theorem minkowski_combined_square (I : A) (hI : ∀ c : A, I * c = c * I) (hII : I * I = -1)
    (P : Plucker6 A) :
    (P.p23 + I * P.p01) * (P.p23 + I * P.p01) + (-P.p13 + I * P.p02) * (-P.p13 + I * P.p02) +
        (P.p12 + I * P.p03) * (P.p12 + I * P.p03) =
      (P.p23 * P.p23 + P.p13 * P.p13 + P.p12 * P.p12 -
          (P.p01 * P.p01 + P.p02 * P.p02 + P.p03 * P.p03)) +
        I * (kleinQ P + kleinQ (hodge P)) := by
  have sq : ∀ m e : A, (m + I * e) * (m + I * e) = m * m - e * e + I * (m * e + e * m) := by
    intro m e
    have h1 : m * (I * e) = I * (m * e) := by rw [← mul_assoc, ← hI m, mul_assoc]
    have h2 : I * e * (I * e) = -(e * e) := by
      calc I * e * (I * e) = I * (e * I) * e := by noncomm_ring
        _ = I * (I * e) * e := by rw [← hI e]
        _ = (I * I) * (e * e) := by noncomm_ring
        _ = -(e * e) := by rw [hII]; noncomm_ring
    calc (m + I * e) * (m + I * e) = m * m + m * (I * e) + I * e * m + I * e * (I * e) := by
          noncomm_ring
      _ = m * m + I * (m * e) + I * e * m + -(e * e) := by rw [h1, h2]
      _ = m * m - e * e + I * (m * e + e * m) := by noncomm_ring
  rw [sq, sq, sq]
  simp only [kleinQ, hodge]
  noncomm_ring

end Hodge

/-! ### The symmetric pair of a complex structure in a `*`-ring -/

section SymmetricPair

variable {A : Type*} [Ring A] [StarRing A]

/-- `theta J M = J (star M) J`. -/
def theta (J M : A) : A := J * star M * J

variable {J : A}

theorem theta_theta (hS : star J = -J) (hJ : J * J = -1) (M : A) : theta J (theta J M) = M := by
  have h : theta J (theta J M) = (J * J) * M * (J * J) := by
    simp only [theta, star_mul, star_star, hS, Matrix.neg_mul, mul_neg, neg_mul, neg_neg,
      mul_assoc]
  rw [h, hJ]; simp

theorem theta_add (M N : A) : theta J (M + N) = theta J M + theta J N := by
  simp [theta, mul_add, add_mul]

theorem theta_neg (M : A) : theta J (-M) = -theta J M := by
  simp [theta]

/-- `theta` is a Lie automorphism: `θ[M,N] = [θM, θN]`. -/
theorem theta_lie (hJ : J * J = -1) (M N : A) :
    theta J (M * N - N * M) = theta J M * theta J N - theta J N * theta J M := by
  have key : ∀ X Y : A, J * X * J * (J * Y * J) = -(J * X * Y * J) := by
    intro X Y
    calc J * X * J * (J * Y * J) = J * X * (J * J) * Y * J := by simp only [mul_assoc]
      _ = -(J * X * Y * J) := by rw [hJ]; noncomm_ring
  simp only [theta, star_sub, star_mul, key]
  noncomm_ring

/-- `M` is symplectic for `J`: `star M * J + J * M = 0`. -/
def IsSymp (J M : A) : Prop := star M * J + J * M = 0

/-- `M` lies in the `-1` eigenspace: `star M * J = J * M`. -/
def IsAntiSymp (J M : A) : Prop := star M * J = J * M

theorem isSymp_iff (hJ : J * J = -1) (M : A) : IsSymp J M ↔ theta J M = M := by
  unfold IsSymp theta
  constructor
  · intro h
    have h' : star M * J = -(J * M) := eq_neg_of_add_eq_zero_left h
    rw [mul_assoc, h', mul_neg, ← mul_assoc, hJ]; simp
  · intro h
    calc star M * J + J * M = star M * J + J * (J * star M * J) := by rw [h]
      _ = star M * J + (J * J) * star M * J := by simp only [mul_assoc]
      _ = 0 := by rw [hJ]; simp

theorem isAntiSymp_iff (hJ : J * J = -1) (M : A) : IsAntiSymp J M ↔ theta J M = -M := by
  unfold IsAntiSymp theta
  constructor
  · intro h
    rw [mul_assoc, h, ← mul_assoc, hJ]; simp
  · intro h
    have : J * (J * star M * J) = J * -M := by rw [h]
    rw [← mul_assoc, ← mul_assoc, hJ, mul_neg] at this
    simpa using this

/-- Cartan splitting `(M + θM) + (M - θM) = 2 M` into the `±1` eigenspaces. -/
theorem theta_split (hS : star J = -J) (hJ : J * J = -1) (M : A) :
    theta J (M + theta J M) = M + theta J M ∧
      theta J (M - theta J M) = -(M - theta J M) ∧
      (M + theta J M) + (M - theta J M) = 2 * M := by
  refine ⟨?_, ?_, ?_⟩
  · rw [theta_add, theta_theta hS hJ, add_comm]
  · rw [sub_eq_add_neg, theta_add, theta_neg, theta_theta hS hJ]; abel
  · noncomm_ring

/-- Bracket relations `[𝔨,𝔨] ⊆ 𝔨`, `[𝔨,𝔭] ⊆ 𝔭`, `[𝔭,𝔭] ⊆ 𝔨`. -/
theorem theta_brackets (hJ : J * J = -1) {X Y : A} :
    (theta J X = X → theta J Y = Y → theta J (X * Y - Y * X) = X * Y - Y * X) ∧
    (theta J X = X → theta J Y = -Y → theta J (X * Y - Y * X) = -(X * Y - Y * X)) ∧
    (theta J X = -X → theta J Y = -Y → theta J (X * Y - Y * X) = X * Y - Y * X) := by
  refine ⟨fun hX hY => ?_, fun hX hY => ?_, fun hX hY => ?_⟩ <;>
    rw [theta_lie hJ, hX, hY] <;> noncomm_ring

end SymmetricPair

/-! ### Dahm's `Q₀₂ = 1 ⊗ q₂` on `4 × 4` matrices over an operator `*`-ring -/

/-- Integer pattern of `Q₀₂ = 1₂ ⊗ q₂`, `q₂ = !![0,-1;1,0]`. -/
def dahmJ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- Integer pattern of `1₂ ⊗ σ_z`. -/
def dahmK : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- Integer witness: `Q₀₂` and `1 ⊗ σ_z` do not commute. -/
theorem dahmJ_dahmK_ne : dahmJ * dahmK ≠ dahmK * dahmJ := by decide

section OperatorMatrices

variable {B : Type*} [Ring B] [StarRing B]

/-- `Q₀₂` with entries in the operator ring `B`. -/
def opJ {B : Type*} [Ring B] : Matrix (Fin 4) (Fin 4) B := dahmJ.map (Int.cast)

/-- `1 ⊗ σ_z` with entries in the operator ring `B`. -/
def opK {B : Type*} [Ring B] : Matrix (Fin 4) (Fin 4) B := dahmK.map (Int.cast)

theorem opJ_star : star ((opJ : Matrix (Fin 4) (Fin 4) B)) = -(opJ : Matrix (Fin 4) (Fin 4) B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opJ, dahmJ, Matrix.star_apply]

theorem opJ_sq : (opJ : Matrix (Fin 4) (Fin 4) B) * (opJ : Matrix (Fin 4) (Fin 4) B) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opJ, dahmJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem opJ_opK_anticomm : (opJ : Matrix (Fin 4) (Fin 4) B) * (opK : Matrix (Fin 4) (Fin 4) B) = -((opK : Matrix (Fin 4) (Fin 4) B) * (opJ : Matrix (Fin 4) (Fin 4) B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [opJ, opK, dahmJ, dahmK, Matrix.mul_apply, Fin.sum_univ_four]

/-- Non-commutativity witness on the operator carrier (needs only `2 ≠ 0` in `B`). -/
theorem opJ_opK_ne (h2 : (2 : B) ≠ 0) : (opJ : Matrix (Fin 4) (Fin 4) B) * (opK : Matrix (Fin 4) (Fin 4) B) ≠ (opK : Matrix (Fin 4) (Fin 4) B) * (opJ : Matrix (Fin 4) (Fin 4) B) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [opJ, opK, dahmJ, dahmK, Matrix.mul_apply, Fin.sum_univ_four] at h01
  apply h2
  have : (1 : B) + 1 = 0 := by rw [eq_neg_iff_add_eq_zero] at h01; simpa using h01
  rw [← one_add_one_eq_two]; exact this

/-- Noncommutativity witness on the operator carrier (any characteristic-zero `*`-ring). -/
theorem opJ_opK_ne_charZero {C : Type*} [Ring C] [StarRing C] [CharZero C] :
    (opJ : Matrix (Fin 4) (Fin 4) C) * opK ≠ opK * opJ :=
  opJ_opK_ne two_ne_zero

/-- The symmetric-pair splitting for Dahm's `Q₀₂` on operator-valued `4 × 4` matrices. -/
theorem opJ_theta_split (M : Matrix (Fin 4) (Fin 4) B) :
    theta ((opJ : Matrix (Fin 4) (Fin 4) B)) (M + theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M) = M + theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M ∧
      theta ((opJ : Matrix (Fin 4) (Fin 4) B)) (M - theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M) = -(M - theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M) ∧
      (M + theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M) + (M - theta ((opJ : Matrix (Fin 4) (Fin 4) B)) M) = 2 * M :=
  theta_split opJ_star opJ_sq M

end OperatorMatrices

end InfoGeometry.Projective.DahmHexasphericalHodgeSymplectic
