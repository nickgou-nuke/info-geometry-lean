import Mathlib
import InfoGeometry.Algebra.ZornMatrix

/-!
# Circular/Peirce readback for the native split-octonion carrier

This file is a small dictionary layer over `InfoGeometry.Algebra.ZornMatrix`.
The symbols `uPlus`, `uMinus`, `sigmaPlus`, and `sigmaMinus` are native Zorn
elements; no associative multiplication is added to the octonion carrier.
The local two-generator packets record the matrix-unit relations available in
each colour fibre, while the global associator witness remains explicit.
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

@[simp] theorem uPlus_add_uMinus : uPlus + uMinus = (I : Carrier) :=
  circularChiralPacket.unit_decomposition

@[simp] theorem uPlus_mul_uMinus : uPlus * uMinus = (0 : Carrier) :=
  circularChiralPacket.orthogonal_plus_minus

@[simp] theorem uMinus_mul_uPlus : uMinus * uPlus = (0 : Carrier) :=
  circularChiralPacket.orthogonal_minus_plus

@[simp] theorem sigmaPlus_mul_sigmaMinus (i j : Fin 3) :
    sigmaPlus i * sigmaMinus j = if i = j then uPlus else 0 :=
  circularChiralPacket.mixed_plus_minus i j

@[simp] theorem sigmaMinus_mul_sigmaPlus (i j : Fin 3) :
    sigmaMinus i * sigmaPlus j = if i = j then uMinus else 0 :=
  circularChiralPacket.mixed_minus_plus i j

theorem sigmaPlus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaPlus i) (sigmaPlus j) = 0 :=
  circularChiralPacket.upper_anticommutator i j

theorem sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaMinus i) (sigmaMinus j) = 0 :=
  circularChiralPacket.lower_anticommutator i j

theorem sigmaPlus_sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaPlus i) (sigmaMinus j) = if i = j then I else 0 :=
  circularChiralPacket.mixed_anticommutator i j

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

theorem commutator_sigmaPlus_sigmaMinus (i j : Fin 3) :
    commutator (sigmaPlus i) (sigmaMinus j) =
      if i = j then chirality else 0 := by
  unfold commutator
  rw [U_mul_V, V_mul_U]
  by_cases h : i = j
  · subst j
    simp [chirality, E11, E22, sub, zero]
  · have h' : ¬j = i := by
      intro hji
      exact h hji.symm
    simp only [h, h']
    apply ZornMatrix.ext
    · simp [sub_a, zero]
    · funext k
      fin_cases k <;> simp [sub_v, zero, Vec3.sub]
    · funext k
      fin_cases k <;> simp [sub_w, zero, Vec3.sub]
    · simp [sub_b, zero]

theorem nonassociative_circular_witness :
    ((sigmaPlus 0 * sigmaPlus 1) * sigmaPlus 2) ≠
      sigmaPlus 0 * (sigmaPlus 1 * sigmaPlus 2) := by
  exact ZornMatrix.nonassociative_witness (R := ℝ)

end InfoGeometry.Canonical.SplitOctonionCircularChiralClosure
