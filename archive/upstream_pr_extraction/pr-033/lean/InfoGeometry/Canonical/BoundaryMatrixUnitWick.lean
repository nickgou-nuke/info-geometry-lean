import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.NoncommRing

/-!
# Boundary matrix-unit Wick owner theorem

This file is argument-based.  It introduces no vacuum-contraction field and
imports no bundled bosonization layer.  Raw modes, CAR laws, and
normal-ordering corrections are explicit theorem parameters and definitions.

The canonical source of those CAR laws is the exterior-Fock construction in
`CanonicalNormalOrdering`: creation is exterior multiplication, annihilation is
`CliffordAlgebra.contractLeft`, and the vacuum contraction is computed from the
augmentation `epsilon_0`.  The downstream constructor
`BosonizationConstructiveCurrent.exteriorFockRawCAR` packages those proved CAR
laws and instantiates the Wick theorem for the actual exterior-Fock modes.
-/

namespace InfoGeometry.Canonical.BoundaryMatrixUnitWick

/-- Ordinary associative commutator in a noncommutative ring. -/
def comm {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Integer Fock polarization indicator: occupied negative modes. -/
def occ (a : Int) : Int :=
  if a < 0 then 1 else 0

/-- Raw matrix unit before normal ordering: `ψ⁺_a ψ⁻_{-b}`. -/
def rawMatrixUnit {A : Type*} [Ring A]
    (psiPlus psiMinus : Int → A) (a b : Int) : A :=
  psiPlus a * psiMinus (-b)

/-- Normal-ordered matrix unit `:ψ⁺_a ψ⁻_{-b}:`. -/
def matrixUnit {A : Type*} [Ring A]
    (psiPlus psiMinus : Int → A) (a b : Int) : A :=
  rawMatrixUnit psiPlus psiMinus a b -
    (if a = b then occ a • (1 : A) else 0)

/-- Compatibility spelling for `rawMatrixUnit`. -/
def rawUnit {A : Type*} [Ring A]
    (psiPlus psiMinus : Int → A) (a b : Int) : A :=
  rawMatrixUnit psiPlus psiMinus a b

/-- Compatibility spelling for the normal-ordered `matrixUnit`. -/
def normalUnit {A : Type*} [Ring A]
    (psiPlus psiMinus : Int → A) (a b : Int) : A :=
  matrixUnit psiPlus psiMinus a b

section ExplicitCAR

variable {A : Type*} [Ring A]
variable (psiPlus psiMinus : Int → A)

private lemma psiMinus_psiPlus_reorder
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (b c : Int) :
    psiMinus (-b) * psiPlus c =
      -(psiPlus c * psiMinus (-b)) + if b = c then 1 else 0 := by
  exact eq_neg_add_of_add_eq (by simpa [add_comm] using car_minus_plus b c)

private lemma psiPlus_reorder
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (a c : Int) :
    psiPlus a * psiPlus c = -(psiPlus c * psiPlus a) := by
  exact eq_neg_of_add_eq_zero_left (car_plus_plus a c)

private lemma psiMinus_reorder
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (b d : Int) :
    psiMinus (-b) * psiMinus (-d) =
      -(psiMinus (-d) * psiMinus (-b)) := by
  exact eq_neg_of_add_eq_zero_left (car_minus_minus b d)

private lemma first_raw_bilinear_expand
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (a b c d : Int) :
    psiPlus a * psiMinus (-b) * (psiPlus c * psiMinus (-d)) =
      -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) +
        (if b = c then psiPlus a * psiMinus (-d) else 0) := by
  calc
    psiPlus a * psiMinus (-b) * (psiPlus c * psiMinus (-d))
        = psiPlus a * (psiMinus (-b) * psiPlus c) * psiMinus (-d) := by
          noncomm_ring
    _ =
        psiPlus a *
            (-(psiPlus c * psiMinus (-b)) + if b = c then 1 else 0) *
          psiMinus (-d) := by
            rw [psiMinus_psiPlus_reorder psiPlus psiMinus car_minus_plus b c]
    _ =
        -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) +
          (if b = c then psiPlus a * psiMinus (-d) else 0) := by
            by_cases h : b = c <;> simp [h] <;> noncomm_ring

private def quarticPart (a b c d : Int) : A :=
  -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) +
    psiPlus c * psiPlus a * psiMinus (-d) * psiMinus (-b)

private lemma quarticPart_cancel
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    quarticPart psiPlus psiMinus a b c d = 0 := by
  unfold quarticPart
  noncomm_ring [psiPlus_reorder psiPlus car_plus_plus a c,
    psiMinus_reorder psiMinus car_minus_minus b d]

/-- Raw CAR bilinears obey the ordinary matrix-unit commutator. -/
theorem raw_matrixUnit_commutator_from_rawCAR
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    comm (rawMatrixUnit psiPlus psiMinus a b) (rawMatrixUnit psiPlus psiMinus c d) =
      (if b = c then rawMatrixUnit psiPlus psiMinus a d else 0) -
        (if a = d then rawMatrixUnit psiPlus psiMinus c b else 0) := by
  dsimp [comm, rawMatrixUnit]
  rw [first_raw_bilinear_expand psiPlus psiMinus car_minus_plus a b c d,
    first_raw_bilinear_expand psiPlus psiMinus car_minus_plus c d a b]
  by_cases hbc : b = c
  · by_cases had : a = d
    · have hda : d = a := had.symm
      rw [if_pos hbc, if_pos had, if_pos hda]
      calc
        -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) +
              psiPlus a * psiMinus (-d) -
            (-(psiPlus c * psiPlus a * psiMinus (-d) * psiMinus (-b)) +
              psiPlus c * psiMinus (-b))
            =
              quarticPart psiPlus psiMinus a b c d +
                (psiPlus a * psiMinus (-d) - psiPlus c * psiMinus (-b)) := by
                unfold quarticPart
                noncomm_ring
        _ = psiPlus a * psiMinus (-d) - psiPlus c * psiMinus (-b) := by
                rw [quarticPart_cancel psiPlus psiMinus car_plus_plus car_minus_minus a b c d]
                abel
    · have hda : ¬ d = a := by exact fun h => had h.symm
      rw [if_pos hbc, if_neg had, if_neg hda]
      calc
        -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) +
              psiPlus a * psiMinus (-d) -
            (-(psiPlus c * psiPlus a * psiMinus (-d) * psiMinus (-b)) + 0)
            =
              quarticPart psiPlus psiMinus a b c d + psiPlus a * psiMinus (-d) := by
                unfold quarticPart
                noncomm_ring
        _ = psiPlus a * psiMinus (-d) - 0 := by
                rw [quarticPart_cancel psiPlus psiMinus car_plus_plus car_minus_minus a b c d]
                simp
  · by_cases had : a = d
    · have hda : d = a := had.symm
      rw [if_neg hbc, if_pos had, if_pos hda]
      calc
        -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) + 0 -
            (-(psiPlus c * psiPlus a * psiMinus (-d) * psiMinus (-b)) +
              psiPlus c * psiMinus (-b))
            =
              quarticPart psiPlus psiMinus a b c d - psiPlus c * psiMinus (-b) := by
                unfold quarticPart
                noncomm_ring
        _ = 0 - psiPlus c * psiMinus (-b) := by
                rw [quarticPart_cancel psiPlus psiMinus car_plus_plus car_minus_minus a b c d]
    · have hda : ¬ d = a := by exact fun h => had h.symm
      rw [if_neg hbc, if_neg had, if_neg hda]
      calc
        -(psiPlus a * psiPlus c * psiMinus (-b) * psiMinus (-d)) + 0 -
            (-(psiPlus c * psiPlus a * psiMinus (-d) * psiMinus (-b)) + 0)
            =
              quarticPart psiPlus psiMinus a b c d := by
                unfold quarticPart
                noncomm_ring
        _ = 0 - 0 := by
                rw [quarticPart_cancel psiPlus psiMinus car_plus_plus car_minus_minus a b c d]
                simp

/-- Compatibility spelling for the raw Wick matrix-unit commutator. -/
theorem rawUnit_commutator
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    comm (rawUnit psiPlus psiMinus a b) (rawUnit psiPlus psiMinus c d) =
      (if b = c then rawUnit psiPlus psiMinus a d else 0) -
        (if a = d then rawUnit psiPlus psiMinus c b else 0) := by
  simpa [rawUnit] using
    raw_matrixUnit_commutator_from_rawCAR psiPlus psiMinus
      car_minus_plus car_plus_plus car_minus_minus a b c d

private lemma comm_sub_zsmul_one_sub_zsmul_one (X Y : A) (m n : Int) :
    comm (X - m • (1 : A)) (Y - n • (1 : A)) = comm X Y := by
  unfold comm
  simp only [zsmul_one]
  noncomm_ring [Int.cast_comm m X, Int.cast_comm m Y, Int.cast_comm n X,
    Int.cast_comm n Y, Int.cast_comm m (n : A)]

private lemma comm_sub_zsmul_one_left (X Y : A) (m : Int) :
    comm (X - m • (1 : A)) Y = comm X Y := by
  simpa using comm_sub_zsmul_one_sub_zsmul_one (A := A) X Y m 0

private lemma comm_sub_zsmul_one_right (X Y : A) (n : Int) :
    comm X (Y - n • (1 : A)) = comm X Y := by
  simpa using comm_sub_zsmul_one_sub_zsmul_one (A := A) X Y 0 n

private lemma matrixUnit_comm_eq_raw_comm (a b c d : Int) :
    comm (matrixUnit psiPlus psiMinus a b) (matrixUnit psiPlus psiMinus c d) =
      comm (rawMatrixUnit psiPlus psiMinus a b) (rawMatrixUnit psiPlus psiMinus c d) := by
  unfold matrixUnit
  by_cases hab : a = b <;> by_cases hcd : c = d
  · simpa [hab, hcd] using
      comm_sub_zsmul_one_sub_zsmul_one (A := A)
        (rawMatrixUnit psiPlus psiMinus a b) (rawMatrixUnit psiPlus psiMinus c d)
        (occ a) (occ c)
  · simpa [hab, hcd] using
      comm_sub_zsmul_one_left (A := A)
        (rawMatrixUnit psiPlus psiMinus a b) (rawMatrixUnit psiPlus psiMinus c d)
        (occ a)
  · simpa [hab, hcd] using
      comm_sub_zsmul_one_right (A := A)
        (rawMatrixUnit psiPlus psiMinus a b) (rawMatrixUnit psiPlus psiMinus c d)
        (occ c)
  · simp [hab, hcd]

/--
Owner theorem for the `H²` boundary layer: normal-ordered CAR matrix units
produce the Wick/Schwinger central correction.
-/
theorem normalOrdered_matrixUnit_commutator_from_rawCAR
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    comm (matrixUnit psiPlus psiMinus a b) (matrixUnit psiPlus psiMinus c d) =
      (if b = c then matrixUnit psiPlus psiMinus a d else 0) -
        (if a = d then matrixUnit psiPlus psiMinus c b else 0) +
        (if b = c ∧ a = d then (occ a - occ c) • (1 : A) else 0) := by
  rw [matrixUnit_comm_eq_raw_comm]
  rw [raw_matrixUnit_commutator_from_rawCAR psiPlus psiMinus
    car_minus_plus car_plus_plus car_minus_minus a b c d]
  unfold matrixUnit rawMatrixUnit
  by_cases hbc : b = c
  · subst c
    by_cases had : a = d
    · subst d
      simp [occ]
      abel
    · simp [had]
  · by_cases had : a = d
    · subst d
      have hcb : ¬ c = b := fun h => hbc h.symm
      simp [hbc, hcb]
    · simp [hbc, had]

/-- Compatibility spelling for the normal-ordered Wick/Schwinger commutator. -/
theorem normalUnit_commutator
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    comm (normalUnit psiPlus psiMinus a b) (normalUnit psiPlus psiMinus c d) =
      (if b = c then normalUnit psiPlus psiMinus a d else 0) -
        (if a = d then normalUnit psiPlus psiMinus c b else 0) +
        (if b = c ∧ a = d then (occ a - occ c) • (1 : A) else 0) := by
  simpa [normalUnit] using
    normalOrdered_matrixUnit_commutator_from_rawCAR psiPlus psiMinus
      car_minus_plus car_plus_plus car_minus_minus a b c d

end ExplicitCAR

end InfoGeometry.Canonical.BoundaryMatrixUnitWick
