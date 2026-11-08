/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornMatrix

set_option maxHeartbeats 2000000

/-!
# Circular/Peirce readback for the native split-octonion carrier

This file is a small dictionary layer over `InfoGeometry.Algebra.ZornMatrix`.
The symbols `uPlus`, `uMinus`, `sigmaPlus`, and `sigmaMinus` are native Zorn
elements; no associative multiplication is added to the octonion carrier.
The local two-generator packets record the matrix-unit relations available in
each colour fibre, while the global associator property remains explicit.
-/

namespace InfoGeometry.Canonical.SplitOctonionCircularChiralClosure

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

abbrev Carrier := ZornMatrix ℝ

abbrev uPlus : Carrier := E11
abbrev uMinus : Carrier := E22

abbrev sigmaPlus (i : Fin 3) : Carrier := U i
abbrev sigmaMinus (i : Fin 3) : Carrier := V i

def chirality : Carrier := uPlus - uMinus

def commutator (X Y : Carrier) : Carrier := X * Y - Y * X

def anticommutator (X Y : Carrier) : Carrier := X * Y + Y * X

/-- A general upper Zorn vector.  This is a Zorn element, not an element of an
associative Peirce algebra. -/
def upperVector (x : Vec3 ℝ) : Carrier :=
  { a := 0, v := x, w := 0, b := 0 }

/-- A general lower Zorn vector. -/
def lowerVector (x : Vec3 ℝ) : Carrier :=
  { a := 0, v := 0, w := x, b := 0 }

/-- The product of two upper Zorn vectors is their cross product in the lower
slot.  In particular, the upper sector is not a zero-product subalgebra. -/
theorem upperVector_mul_upperVector (x y : Vec3 ℝ) :
    upperVector x * upperVector y = lowerVector (Vec3.cross x y) := by
  apply ZornMatrix.ext <;>
    simp [upperVector, lowerVector, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

/-- The lower same-chirality product has the opposite cross-product sign. -/
theorem lowerVector_mul_lowerVector (x y : Vec3 ℝ) :
    lowerVector x * lowerVector y = upperVector (-Vec3.cross x y) := by
  apply ZornMatrix.ext <;>
    simp [upperVector, lowerVector, ZornMatrix.mul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul]

/-- The opposite-chirality products land on their respective diagonal
idempotents, weighted by the Euclidean dot product. -/
theorem upperVector_mul_lowerVector (x y : Vec3 ℝ) :
    upperVector x * lowerVector y = (Vec3.dot x y) • uPlus := by
  apply ZornMatrix.ext <;>
    simp [upperVector, lowerVector, uPlus, ZornMatrix.mul, ZornMatrix.smul,
      E11, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;> ring

theorem lowerVector_mul_upperVector (x y : Vec3 ℝ) :
    lowerVector y * upperVector x = (Vec3.dot y x) • uMinus := by
  apply ZornMatrix.ext <;>
    simp [upperVector, lowerVector, uMinus, ZornMatrix.mul, ZornMatrix.smul,
      E22, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;> ring

/-- Same-chirality anticommutators vanish over the commutative real base,
although the ordered products need not vanish. -/
theorem upperVector_anticommutator (x y : Vec3 ℝ) :
    anticommutator (upperVector x) (upperVector y) = 0 := by
  rw [anticommutator, upperVector_mul_upperVector,
    upperVector_mul_upperVector]
  have hcross : Vec3.cross y x = -Vec3.cross x y := by
    funext i
    fin_cases i <;> simp [Vec3.cross] <;> ring
  rw [hcross]
  apply ZornMatrix.ext <;>
    simp [lowerVector, ZornMatrix.add, ZornMatrix.zero, Vec3.add, Vec3.smul,
      Vec3.cross] <;> ring

/-- Lower same-chirality anticommutators vanish as well. -/
theorem lowerVector_anticommutator (x y : Vec3 ℝ) :
    anticommutator (lowerVector x) (lowerVector y) = 0 := by
  rw [anticommutator, lowerVector_mul_lowerVector,
    lowerVector_mul_lowerVector]
  have hcross : Vec3.cross y x = -Vec3.cross x y := by
    funext i
    fin_cases i <;> simp [Vec3.cross] <;> ring
  rw [hcross]
  apply ZornMatrix.ext <;>
    simp [upperVector, ZornMatrix.add, ZornMatrix.zero, Vec3.add,
      Vec3.smul, Vec3.cross] <;> ring

/-- The split-octonion cubic pairing on three upper vectors.  The two diagonal
coefficients agree over `ℝ`, so the result is the scalar triple product times
the unit. -/
theorem upperVector_cubic_pairing (x y z : Vec3 ℝ) :
    anticommutator (upperVector x * upperVector y) (upperVector z) =
      (Vec3.dot (Vec3.cross x y) z) • (I : Carrier) := by
  apply ZornMatrix.ext <;>
    simp [anticommutator, upperVector, I, ZornMatrix.mul,
      ZornMatrix.add, ZornMatrix.smul, Vec3.dot, Vec3.cross,
      Vec3.add, Vec3.sub, Vec3.smul] <;> ring

/-- Concrete witness that the proposed global affine multiplication law for
`I + upperVector` fails on the split-octonion Zorn carrier. -/
theorem upperVector_unipotent_product_defect :
    ((I : Carrier) + upperVector (Vec3.basis 0)) *
        ((I : Carrier) + upperVector (Vec3.basis 1)) -
      ((I : Carrier) + upperVector (Vec3.basis 0 + Vec3.basis 1)) ≠ 0 := by
  have hdef :
      ((I : Carrier) + upperVector (Vec3.basis 0)) *
          ((I : Carrier) + upperVector (Vec3.basis 1)) -
        ((I : Carrier) + upperVector (Vec3.basis 0 + Vec3.basis 1)) =
        lowerVector (Vec3.basis 2) := by
    apply ZornMatrix.ext
    · simp [upperVector, lowerVector, I, ZornMatrix.add, ZornMatrix.sub,
        ZornMatrix.mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
    · funext k
      fin_cases k <;>
        simp [upperVector, lowerVector, I, ZornMatrix.add, ZornMatrix.sub,
          ZornMatrix.mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
          Vec3.sub, Vec3.smul]
    · funext k
      fin_cases k <;>
        simp [upperVector, lowerVector, I, ZornMatrix.add, ZornMatrix.sub,
          ZornMatrix.mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
          Vec3.sub, Vec3.smul]
    · simp [upperVector, lowerVector, I, ZornMatrix.add, ZornMatrix.sub,
        ZornMatrix.mul, Vec3.basis, Vec3.dot, Vec3.cross, Vec3.add,
        Vec3.sub, Vec3.smul]
  rw [hdef]
  intro h
  have hcoord : (lowerVector (Vec3.basis 2)).w 2 = 1 := by
    simp [lowerVector, Vec3.basis]
  rw [h] at hcoord
  simp [ZornMatrix.zero] at hcoord

/- The laws are exposed below as direct theorems.  They are not packaged as
proof-only packet data: the native Zorn-matrix lemmas are the owners. -/
/-
structure CircularChiralPacket where
  unit_decomposition : uPlus + uMinus = I
  orthogonal_plus_minus : uPlus * uMinus = 0
  orthogonal_minus_plus : uMinus * uPlus = 0
  plus_idempotent : uPlus * uPlus = uPlus
  minus_idempotent : uMinus * uMinus = uMinus
  plus_left : ∀ i, uPlus * sigmaPlus i = sigmaPlus i
  plus_right : ∀ i, sigmaPlus i * uMinus = sigmaPlus i
  minus_left : ∀ i, uMinus * sigmaMinus i = sigmaMinus i
  minus_right : ∀ i, sigmaMinus i * uPlus = sigmaMinus i
  mixed_plus_minus : ∀ i j,
    sigmaPlus i * sigmaMinus j = if i = j then uPlus else 0
  mixed_minus_plus : ∀ i j,
    sigmaMinus i * sigmaPlus j = if i = j then uMinus else 0
  upper_anticommutator : ∀ i j,
    anticommutator (sigmaPlus i) (sigmaPlus j) = 0
  lower_anticommutator : ∀ i j,
    anticommutator (sigmaMinus i) (sigmaMinus j) = 0
  mixed_anticommutator : ∀ i j,
    anticommutator (sigmaPlus i) (sigmaMinus j) = if i = j then I else 0

noncomputable def circularChiralPacket : CircularChiralPacket where
  unit_decomposition := E11_add_E22
  orthogonal_plus_minus := E11_mul_E22
  orthogonal_minus_plus := E22_mul_E11
  plus_idempotent := E11_mul_E11
  minus_idempotent := E22_mul_E22
  plus_left := E11_mul_U
  plus_right := U_mul_E22
  minus_left := E22_mul_V
  minus_right := V_mul_E11
  mixed_plus_minus := U_mul_V
  mixed_minus_plus := V_mul_U
  upper_anticommutator := by
    intro i j
    exact U_anticommute i j
  lower_anticommutator := by
    intro i j
    exact V_anticommute i j
  mixed_anticommutator := by
    intro i j
    exact U_V_anticommutator i j
-/

@[simp] theorem uPlus_add_uMinus : uPlus + uMinus = (I : Carrier) :=
  by
    apply ZornMatrix.ext
    · rw [add_a]
      norm_num [uPlus, uMinus, I, E11, E22]
    · rw [add_v]
      ext j
      dsimp [uPlus, uMinus, I, E11, E22, Vec3.add]
      fin_cases j <;>
        simp
    · rw [add_w]
      ext j
      dsimp [uPlus, uMinus, I, E11, E22, Vec3.add]
      fin_cases j <;>
        simp
    · rw [add_b]
      norm_num [uPlus, uMinus, I, E11, E22]

@[simp] theorem uPlus_mul_uMinus : uPlus * uMinus = (0 : Carrier) :=
  by simpa [uPlus, uMinus] using (E11_mul_E22 (R := ℝ))

@[simp] theorem uMinus_mul_uPlus : uMinus * uPlus = (0 : Carrier) :=
  by simpa [uPlus, uMinus] using (E22_mul_E11 (R := ℝ))

@[simp] theorem sigmaPlus_mul_sigmaMinus (i j : Fin 3) :
    sigmaPlus i * sigmaMinus j = if i = j then uPlus else 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp [sigmaPlus, sigmaMinus, uPlus, U, V, E11, zero, ZornMatrix.mul,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis] <;> ring

@[simp] theorem sigmaMinus_mul_sigmaPlus (i j : Fin 3) :
    sigmaMinus i * sigmaPlus j = if i = j then uMinus else 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp [sigmaPlus, sigmaMinus, uMinus, U, V, E22, zero, ZornMatrix.mul,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis] <;> ring

theorem sigmaPlus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaPlus i) (sigmaPlus j) = 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp [anticommutator, sigmaPlus, U, zero, ZornMatrix.mul,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis] <;>
      ext <;> simp [ZornMatrix.add, Vec3.add, Vec3.smul] <;> ring

theorem sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaMinus i) (sigmaMinus j) = 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp [anticommutator, sigmaMinus, V, zero, ZornMatrix.mul,
        Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul, Vec3.basis] <;>
      ext <;> simp [ZornMatrix.add, Vec3.add, Vec3.smul] <;> ring

theorem sigmaPlus_sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaPlus i) (sigmaMinus j) = if i = j then I else 0 :=
  by
    fin_cases i <;> fin_cases j <;>
      simp [anticommutator, sigmaPlus, sigmaMinus, U, V, I, E11, E22, zero,
        ZornMatrix.mul, Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul,
        Vec3.basis] <;> ext <;>
      simp [ZornMatrix.add, Vec3.add, Vec3.smul] <;> ring

/-
structure LocalM2Packet (i : Fin 3) where
  plus_sq : sigmaPlus i * sigmaPlus i = 0
  minus_sq : sigmaMinus i * sigmaMinus i = 0
  plus_minus : sigmaPlus i * sigmaMinus i = uPlus
  minus_plus : sigmaMinus i * sigmaPlus i = uMinus
  car : anticommutator (sigmaPlus i) (sigmaMinus i) = I

def localM2Packet (i : Fin 3) : LocalM2Packet i where
  plus_sq := U_mul_self_zero i
  minus_sq := V_mul_self_zero i
  plus_minus := U_mul_V_self i
  minus_plus := V_mul_U_self i
  car := by simpa using U_V_anticommutator i i
-/

theorem localM2Laws (i : Fin 3) :
    sigmaPlus i * sigmaPlus i = 0 ∧
    sigmaMinus i * sigmaMinus i = 0 ∧
    sigmaPlus i * sigmaMinus i = uPlus ∧
    sigmaMinus i * sigmaPlus i = uMinus ∧
    anticommutator (sigmaPlus i) (sigmaMinus i) = (I : Carrier) := by
  exact ⟨U_mul_self_zero i, V_mul_self_zero i,
    by simpa using sigmaPlus_mul_sigmaMinus i i,
    by simpa using sigmaMinus_mul_sigmaPlus i i,
    by simpa [anticommutator] using sigmaPlus_sigmaMinus_anticommutator i i⟩

theorem commutator_sigmaPlus_sigmaMinus (i j : Fin 3) :
    commutator (sigmaPlus i) (sigmaMinus j) =
      if i = j then chirality else 0 := by
  unfold commutator
  rw [sigmaPlus_mul_sigmaMinus i j, sigmaMinus_mul_sigmaPlus j i]
  by_cases h : i = j
  · subst j
    simp [chirality, E11, E22, sub, zero]
  · have h' : ¬j = i := by
      intro hji
      exact h hji.symm
    simp only [h, h']
    apply ZornMatrix.ext
    · simp [ZornMatrix.sub, zero]
    · funext k
      fin_cases k <;> simp [ZornMatrix.sub, zero, Vec3.sub]
    · funext k
      fin_cases k <;> simp [ZornMatrix.sub, zero, Vec3.sub]
    · simp [ZornMatrix.sub, zero]

theorem nonassociative_circular_property :
    ((sigmaPlus 0 * sigmaPlus 1) * sigmaPlus 2) ≠
      sigmaPlus 0 * (sigmaPlus 1 * sigmaPlus 2) := by
  exact ZornMatrix.nonassociative_witness (R := ℝ)

end InfoGeometry.Canonical.SplitOctonionCircularChiralClosure
