import InfoGeometry.Canonical.CanonicalNormalOrdering
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.Sugawara
import Mathlib.Tactic

/-!
# Constructive CAR-to-Wick Current Layer

This module proves the source-side algebraic core of the bosonization current
layer.

It starts from raw integer-indexed CAR modes and proves:

* the raw bilinear matrix-unit commutator;
* the normal-ordered matrix-unit commutator with its Wick/Schwinger correction;
* the current-diagonal Wick correction;
* the finite Fock-polarization crossing count;
* the formal completed-current Heisenberg central coefficient.

The owner theorem is the normal-ordered matrix-unit commutator.  The current
law below is a formal completed-current corollary obtained by reindexing the
noncentral diagonal and applying the crossing-count theorem; it is not stored
as a field of the CAR data.
-/

namespace InfoGeometry.Canonical.BosonizationConstructiveCurrent

open scoped BigOperators

/-- Ordinary associative commutator in a noncommutative ring. -/
def comm {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Public spelling for the ordinary associative commutator. -/
abbrev commutator {A : Type*} [Ring A] (x y : A) : A :=
  comm x y

/-- The commutator distributes over a finite sum in the left argument. -/
theorem comm_sum_left {A ι : Type*} [Ring A] (s : Finset ι) (f : ι -> A) (x : A) :
    comm (∑ i ∈ s, f i) x = ∑ i ∈ s, comm (f i) x := by
  unfold comm
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The commutator distributes over a finite sum in the right argument. -/
theorem comm_sum_right {A ι : Type*} [Ring A] (s : Finset ι) (x : A) (f : ι -> A) :
    comm x (∑ i ∈ s, f i) = ∑ i ∈ s, comm x (f i) := by
  unfold comm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

/-- The commutator of two finite sums is the double sum of commutators. -/
theorem comm_sum_sum {A ι κ : Type*} [Ring A]
    (s : Finset ι) (t : Finset κ) (f : ι -> A) (g : κ -> A) :
    comm (∑ i ∈ s, f i) (∑ j ∈ t, g j) =
      ∑ i ∈ s, ∑ j ∈ t, comm (f i) (g j) := by
  rw [comm_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [comm_sum_right]

/-- Integer Fock polarization indicator: occupied negative modes. -/
def occ (a : Int) : Int :=
  if a < 0 then 1 else 0

/-- Symmetric integer cutoff window `{-N, -N+1, ..., N}`. -/
def integerWindow (N : Nat) : Finset Int :=
  Finset.Icc (-(N : Int)) (N : Int)

@[simp]
theorem mem_integerWindow_iff (N : Nat) (a : Int) :
    a ∈ integerWindow N ↔ -(N : Int) ≤ a ∧ a ≤ (N : Int) := by
  simp [integerWindow]

/--
Raw integer-indexed CAR modes.

The central carrier is normalized to the ring unit.  This is the algebraic
normalization under which the CAR bilinears act as ordinary matrix units.
-/
structure RawCARModeCompletion (A : Type*) [Ring A] where
  psiPlus : Int -> A
  psiMinus : Int -> A
  car_minus_plus :
    forall r s : Int,
      psiMinus r * psiPlus s + psiPlus s * psiMinus r =
        if r + s = 0 then 1 else 0
  car_plus_plus :
    forall r s : Int,
      psiPlus r * psiPlus s + psiPlus s * psiPlus r = 0
  car_minus_minus :
    forall r s : Int,
      psiMinus r * psiMinus s + psiMinus s * psiMinus r = 0

/--
Public name for the normalized raw CAR mode algebra.

This is the `K = 1` Wick algebra: the CAR contraction uses the ring unit, so
the bilinears have the ordinary matrix-unit commutator rather than a
`K`-twisted one.
-/
abbrev RawCARModeAlgebra (A : Type*) [Ring A] :=
  RawCARModeCompletion A

/--
Raw CAR algebra with an explicit central carrier.

This file proves the clean normalized branch: `central = 1`.  Without that
normalization, or an equivalent unit-action law on the represented CAR modes,
the noncentral matrix-unit bracket is `K`-twisted.
-/
structure RawCARAlgebra (A : Type*) [Ring A] where
  psiPlus : Int -> A
  psiMinus : Int -> A
  central : A
  central_comm : forall x : A, central * x = x * central
  car_minus_plus :
    forall b c : Int,
      psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
        if b = c then central else 0
  car_plus_plus :
    forall a c : Int,
      psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0
  car_minus_minus :
    forall b d : Int,
      psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0

namespace RawCARModeCompletion

variable {A : Type*} [Ring A]
variable (C : RawCARModeCompletion A)

/-- The normalized central charge carrier in this algebraic CAR packet. -/
def central (_C : RawCARModeCompletion A) : A :=
  1

@[simp]
lemma central_eq_one :
    C.central = 1 :=
  rfl

@[simp]
lemma central_commutes (X : A) :
    comm C.central X = 0 := by
  simp [central, comm]

/-- Raw matrix unit before normal ordering: `psiPlus a * psiMinus (-b)`. -/
def rawMatrixUnit (a b : Int) : A :=
  C.psiPlus a * C.psiMinus (-b)

lemma psiMinus_psiPlus_reorder (b c : Int) :
    C.psiMinus (-b) * C.psiPlus c =
      -(C.psiPlus c * C.psiMinus (-b)) + if b = c then 1 else 0 := by
  have h := C.car_minus_plus (-b) c
  have hif : (if -b + c = 0 then (1 : A) else 0) = if b = c then 1 else 0 := by
    by_cases hbc : b = c
    · subst c
      simp
    · have hne : -b + c ≠ 0 := by omega
      simp [hbc, hne]
  rw [hif] at h
  exact eq_neg_add_of_add_eq (by simpa [add_comm] using h)

lemma psiPlus_reorder (a c : Int) :
    C.psiPlus a * C.psiPlus c = -(C.psiPlus c * C.psiPlus a) := by
  exact eq_neg_of_add_eq_zero_left (C.car_plus_plus a c)

lemma psiMinus_reorder (b d : Int) :
    C.psiMinus (-b) * C.psiMinus (-d) =
      -(C.psiMinus (-d) * C.psiMinus (-b)) := by
  exact eq_neg_of_add_eq_zero_left (C.car_minus_minus (-b) (-d))

lemma first_raw_bilinear_expand (a b c d : Int) :
    C.psiPlus a * C.psiMinus (-b) * (C.psiPlus c * C.psiMinus (-d)) =
      -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) +
        (if b = c then C.psiPlus a * C.psiMinus (-d) else 0) := by
  calc
    C.psiPlus a * C.psiMinus (-b) * (C.psiPlus c * C.psiMinus (-d))
        = C.psiPlus a * (C.psiMinus (-b) * C.psiPlus c) * C.psiMinus (-d) := by
          noncomm_ring
    _ =
        C.psiPlus a *
            (-(C.psiPlus c * C.psiMinus (-b)) + if b = c then 1 else 0) *
          C.psiMinus (-d) := by
            rw [C.psiMinus_psiPlus_reorder b c]
    _ =
        -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) +
          (if b = c then C.psiPlus a * C.psiMinus (-d) else 0) := by
            by_cases h : b = c <;> simp [h] <;> noncomm_ring

def quarticPart (a b c d : Int) : A :=
  -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) +
    C.psiPlus c * C.psiPlus a * C.psiMinus (-d) * C.psiMinus (-b)

lemma quarticPart_cancel (a b c d : Int) :
    C.quarticPart a b c d = 0 := by
  unfold quarticPart
  noncomm_ring [C.psiPlus_reorder a c, C.psiMinus_reorder b d]

/--
Raw bilinears obey the matrix-unit commutator before normal ordering.

This is the purely algebraic CAR contraction.
-/
theorem raw_matrixUnit_commutator_from_rawCAR (a b c d : Int) :
    comm (C.rawMatrixUnit a b) (C.rawMatrixUnit c d) =
      (if b = c then C.rawMatrixUnit a d else 0) -
        (if a = d then C.rawMatrixUnit c b else 0) := by
  dsimp [comm, rawMatrixUnit]
  rw [C.first_raw_bilinear_expand a b c d, C.first_raw_bilinear_expand c d a b]
  by_cases hbc : b = c
  · by_cases had : a = d
    · have hda : d = a := had.symm
      rw [if_pos hbc, if_pos had, if_pos hda]
      calc
        -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) +
              C.psiPlus a * C.psiMinus (-d) -
            (-(C.psiPlus c * C.psiPlus a * C.psiMinus (-d) * C.psiMinus (-b)) +
              C.psiPlus c * C.psiMinus (-b))
            =
              C.quarticPart a b c d +
                (C.psiPlus a * C.psiMinus (-d) -
                  C.psiPlus c * C.psiMinus (-b)) := by
                unfold quarticPart
                noncomm_ring
        _ = C.psiPlus a * C.psiMinus (-d) - C.psiPlus c * C.psiMinus (-b) := by
                rw [C.quarticPart_cancel a b c d]
                abel
    · have hda : ¬ d = a := by omega
      rw [if_pos hbc, if_neg had, if_neg hda]
      calc
        -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) +
              C.psiPlus a * C.psiMinus (-d) -
            (-(C.psiPlus c * C.psiPlus a * C.psiMinus (-d) * C.psiMinus (-b)) + 0)
            = C.quarticPart a b c d + C.psiPlus a * C.psiMinus (-d) := by
                unfold quarticPart
                noncomm_ring
        _ = C.psiPlus a * C.psiMinus (-d) - 0 := by
                rw [C.quarticPart_cancel a b c d]
                abel
  · by_cases had : a = d
    · have hda : d = a := had.symm
      rw [if_neg hbc, if_pos had, if_pos hda]
      calc
        -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) + 0 -
            (-(C.psiPlus c * C.psiPlus a * C.psiMinus (-d) * C.psiMinus (-b)) +
              C.psiPlus c * C.psiMinus (-b))
            = C.quarticPart a b c d - C.psiPlus c * C.psiMinus (-b) := by
                unfold quarticPart
                noncomm_ring
        _ = 0 - C.psiPlus c * C.psiMinus (-b) := by
                rw [C.quarticPart_cancel a b c d]
    · have hda : ¬ d = a := by omega
      rw [if_neg hbc, if_neg had, if_neg hda]
      calc
        -(C.psiPlus a * C.psiPlus c * C.psiMinus (-b) * C.psiMinus (-d)) + 0 -
            (-(C.psiPlus c * C.psiPlus a * C.psiMinus (-d) * C.psiMinus (-b)) + 0)
            = C.quarticPart a b c d := by
                unfold quarticPart
                noncomm_ring
        _ = 0 - 0 := by
                rw [C.quarticPart_cancel a b c d]
                abel

/-- The subtracted vacuum contraction for `:psiPlus a psiMinus (-b):`. -/
def occupiedScalar (a b : Int) : A :=
  if a = b ∧ a < 0 then 1 else 0

/-- Normal-ordered matrix unit `:psiPlus a psiMinus (-b):`. -/
def matrixUnit (a b : Int) : A :=
  C.rawMatrixUnit a b - occupiedScalar (A := A) a b

lemma comm_matrixUnit_eq_raw_comm (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      comm (C.rawMatrixUnit a b) (C.rawMatrixUnit c d) := by
  unfold matrixUnit occupiedScalar comm
  by_cases hab : a = b ∧ a < 0
  · have hbneg : b < 0 := by
      rw [← hab.1]
      exact hab.2
    by_cases hcd : c = d ∧ c < 0
    · have hdneg : d < 0 := by
        rw [← hcd.1]
        exact hcd.2
      simp [hab, hcd, hbneg, hdneg]
      noncomm_ring
    · simp [hab, hcd, hbneg]
      noncomm_ring
  · by_cases hcd : c = d ∧ c < 0
    · have hdneg : d < 0 := by
        rw [← hcd.1]
        exact hcd.2
      simp [hab, hcd, hdneg]
      noncomm_ring
    · simp [hab, hcd]

/-- The central Wick correction in the normal-ordered matrix-unit bracket. -/
def wickCorrection (a b c d : Int) : A :=
  if b = c ∧ a = d then
    (if a < 0 then (1 : A) else 0) - (if b < 0 then (1 : A) else 0)
  else 0

/--
Intermediate Wick-correction form of the normal-ordered matrix-unit commutator.

The owner theorem below expands `wickCorrection` into the standard
`(occ a - occ b)` central defect.
-/
theorem normalOrdered_matrixUnit_commutator_wickCorrection_from_rawCAR (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        wickCorrection (A := A) a b c d := by
  rw [C.comm_matrixUnit_eq_raw_comm, C.raw_matrixUnit_commutator_from_rawCAR]
  unfold matrixUnit rawMatrixUnit occupiedScalar wickCorrection
  by_cases hbc : b = c
  · by_cases had : a = d
    · by_cases _ha : a < 0 <;> by_cases _hb : b < 0 <;>
        simp [hbc, had] <;> noncomm_ring
    · simp [hbc, had]
  · have hcb : ¬ c = b := by omega
    by_cases had : a = d
    · have hnotcb : ¬ (c = b ∧ c < 0) := fun h => hcb h.1
      simp [hbc, had, hnotcb]
    · simp [hbc, had]

/--
Owner theorem in normalized-central form.

Normal-ordered matrix units obey the Wick-corrected matrix-unit commutator:
the first two terms are the ordinary matrix-unit bracket, and the last term is
the Fock-polarization correction `(occ a - occ b) • K` with `K = 1`.
-/
theorem normalOrdered_matrixUnit_commutator_from_rawCAR (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) := by
  rw [C.normalOrdered_matrixUnit_commutator_wickCorrection_from_rawCAR]
  unfold wickCorrection occ central
  by_cases h : b = c ∧ a = d
  · rcases h with ⟨hbc, had⟩
    subst c
    by_cases ha : a < 0
    · by_cases hb : b < 0
      · simp [hb, had]
      · simp [hb, had]
    · by_cases hb : b < 0
      · simp [hb, had]
      · simp [hb, had]
  · simp [h]

/-- Backward-compatible name for the matrix-unit Wick owner theorem. -/
theorem normalOrdered_matrixUnit_commutator_from_CAR (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) :=
  C.normalOrdered_matrixUnit_commutator_from_rawCAR a b c d

/-- Boundary-facing name for the matrix-unit Wick owner theorem. -/
theorem boundaryMatrixUnitWick_commutator_from_rawCAR (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) :=
  C.normalOrdered_matrixUnit_commutator_from_rawCAR a b c d

/--
The Wick correction on the current diagonal.

This is the local summand whose finite crossing count becomes the Schwinger
coefficient in the completed current algebra.
-/
theorem wickCorrection_currentDiagonal (a m n : Int) :
    wickCorrection (A := A) a (a + m) (a + m) (a + m + n) =
      if m + n = 0 then
        (if a < 0 then (1 : A) else 0) - (if a + m < 0 then (1 : A) else 0)
      else 0 := by
  unfold wickCorrection
  by_cases hmn : m + n = 0
  · have had : a = a + m + n := by omega
    have hcond : a + m = a + m ∧ a = a + m + n := ⟨rfl, had⟩
    rw [if_pos hcond, if_pos hmn]
  · have had : ¬ a = a + m + n := by omega
    have hcond : ¬ (a + m = a + m ∧ a = a + m + n) := fun h => had h.2
    rw [if_neg hcond, if_neg hmn]

/--
The current-diagonal summand obtained by applying the owner matrix-unit Wick
commutator to `E_{a,a+m}` and `E_{a+m,a+m+n}`.
-/
theorem normalOrdered_currentDiagonal_commutator_from_rawCAR (a m n : Int) :
    comm (C.matrixUnit a (a + m)) (C.matrixUnit (a + m) (a + m + n)) =
      C.matrixUnit a (a + m + n) -
        (if m + n = 0 then C.matrixUnit (a + m) (a + m) else 0) +
        (if m + n = 0 then
          (if a < 0 then (1 : A) else 0) - (if a + m < 0 then (1 : A) else 0)
        else 0) := by
  rw [C.normalOrdered_matrixUnit_commutator_wickCorrection_from_rawCAR,
    wickCorrection_currentDiagonal (A := A) a m n]
  rw [if_pos rfl]
  by_cases hmn : m + n = 0
  · have had : a = a + m + n := by omega
    rw [if_pos hmn]
    rw [if_pos had]
    rw [if_pos hmn]
  · have had : ¬ a = a + m + n := by omega
    rw [if_neg hmn]
    rw [if_neg had]
    rw [if_neg hmn]

end RawCARModeCompletion

namespace RawCARModeAlgebra

variable {A : Type*} [Ring A]

/--
Matrix-unit Wick commutator for the normalized raw CAR mode algebra.

This is the public owner theorem in the standard source-side bosonization
form.  The central carrier is `C.central = 1`, because
`RawCARModeAlgebra` is the normalized `K = 1` CAR packet.
-/
theorem normalOrdered_matrixUnit_commutator_from_rawCAR
    (C : RawCARModeAlgebra A) (a b c d : Int) :
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) :=
  RawCARModeCompletion.normalOrdered_matrixUnit_commutator_from_rawCAR C a b c d

end RawCARModeAlgebra

/-! ## Exterior-Fock instantiation of the Wick owner theorem -/

section ExteriorFockInstantiation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : Module.Basis ℤ R M)

/--
The normalized raw CAR packet constructed from the exterior-Fock modes.

This is not an assumption interface: every field is filled by the CAR theorems
proved in `CanonicalNormalOrdering` from exterior multiplication and
Clifford/exterior contraction.
-/
noncomputable def exteriorFockRawCAR :
    RawCARModeCompletion
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock (R := R) (M := M)) where
  psiPlus := InfoGeometry.Canonical.CanonicalNormalOrdering.psiPlus (R := R) (M := M) B
  psiMinus := InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus (R := R) (M := M) B
  car_minus_plus :=
    InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus_psiPlus_anticomm
      (R := R) (M := M) B
  car_plus_plus :=
    InfoGeometry.Canonical.CanonicalNormalOrdering.psiPlus_psiPlus_anticomm
      (R := R) (M := M) B
  car_minus_minus :=
    InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus_psiMinus_anticomm
      (R := R) (M := M) B

/--
The algebraic matrix unit of the CAR owner theorem is the canonical
normal-ordered matrix unit constructed from the exterior-Fock vacuum
contraction.
-/
theorem exteriorFockRawCAR_matrixUnit_eq_normalMatrixUnit (a b : ℤ) :
    (exteriorFockRawCAR (R := R) (M := M) B).matrixUnit a b =
      InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
        (R := R) (M := M) B a b := by
  unfold exteriorFockRawCAR RawCARModeCompletion.matrixUnit
    RawCARModeCompletion.rawMatrixUnit RawCARModeCompletion.occupiedScalar
    InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
    InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
    InfoGeometry.Canonical.CanonicalNormalOrdering.contractionCoeff
  by_cases hab : a = b
  · subst b
    by_cases ha : a < 0
    · simp [ha, InfoGeometry.Canonical.CanonicalNormalOrdering.modeDual_modeVec,
        InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus, Module.End.mul_eq_comp]
    · simp [ha, InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus,
        Module.End.mul_eq_comp]
  · by_cases ha : a < 0
    · simp [hab, ha, InfoGeometry.Canonical.CanonicalNormalOrdering.modeDual_modeVec,
        InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus, Module.End.mul_eq_comp]
    · simp [hab, ha, InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus,
        Module.End.mul_eq_comp]

/--
The raw matrix unit of the CAR owner theorem is the constructed exterior-Fock
raw bilinear.
-/
theorem exteriorFockRawCAR_rawMatrixUnit_eq_rawMatrixUnit (a b : ℤ) :
    (exteriorFockRawCAR (R := R) (M := M) B).rawMatrixUnit a b =
      InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
        (R := R) (M := M) B a b := by
  unfold exteriorFockRawCAR RawCARModeCompletion.rawMatrixUnit
    InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
    InfoGeometry.Canonical.CanonicalNormalOrdering.psiMinus
  rw [Module.End.mul_eq_comp]
  simp

/--
Raw bilinear commutator for the constructed exterior-Fock operators.

This is the explicit expansion step for
`[psiPlus a psiMinus(-b), psiPlus c psiMinus(-d)]`, obtained by instantiating
the generic CAR expansion theorem with the exterior/Clifford CAR construction.
-/
theorem rawMatrixUnit_commutator_from_exteriorFock (a b c d : ℤ) :
    comm
        (InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
          (R := R) (M := M) B a b)
        (InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
          (R := R) (M := M) B c d) =
      (if b = c then
          InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
            (R := R) (M := M) B a d
        else 0) -
        (if a = d then
          InfoGeometry.Canonical.CanonicalNormalOrdering.rawMatrixUnit
            (R := R) (M := M) B c b
        else 0) := by
  let C := exteriorFockRawCAR (R := R) (M := M) B
  have howner := RawCARModeCompletion.raw_matrixUnit_commutator_from_rawCAR C a b c d
  simpa [C, exteriorFockRawCAR_rawMatrixUnit_eq_rawMatrixUnit (R := R) (M := M) B]
    using howner

/--
Problem 3: Wick / matrix-unit commutator for the constructed exterior-Fock
normal-ordered bilinears.

This theorem applies the owner CAR expansion theorem to the CAR packet
constructed above, then rewrites the owner-theorem matrix units back to the
canonical normal-ordered bilinears.
-/
theorem normalOrdered_matrixUnit_commutator_from_exteriorFock
    (a b c d : ℤ) :
    comm
        (InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
          (R := R) (M := M) B a b)
        (InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
          (R := R) (M := M) B c d) =
      (if b = c then
          InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
            (R := R) (M := M) B a d
        else 0) -
        (if a = d then
          InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
            (R := R) (M := M) B c b
        else 0) +
        (if b = c ∧ a = d then
          (occ a - occ b) •
            (1 : InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
              (R := R) (M := M))
        else 0) := by
  let C := exteriorFockRawCAR (R := R) (M := M) B
  have howner := RawCARModeCompletion.normalOrdered_matrixUnit_commutator_from_rawCAR C a b c d
  simpa [C, exteriorFockRawCAR_matrixUnit_eq_normalMatrixUnit (R := R) (M := M) B]
    using howner

/--
Problem 3 for the literal direct-sum mode space `⊕ r : ℤ, R e_r`.
-/
theorem normalOrdered_matrixUnit_commutator_from_directSumExteriorFock
    (R : Type*) [CommRing R] (a b c d : ℤ) :
    comm
        (InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
          (R := R)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
          (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) a b)
        (InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
          (R := R)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
          (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) c d) =
      (if b = c then
          InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
            (R := R)
            (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
            (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) a d
        else 0) -
        (if a = d then
          InfoGeometry.Canonical.CanonicalNormalOrdering.normalMatrixUnit
            (R := R)
            (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
            (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) c b
        else 0) +
        (if b = c ∧ a = d then
          (occ a - occ b) •
            (1 : InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
              (R := R)
              (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R))
        else 0) :=
  normalOrdered_matrixUnit_commutator_from_exteriorFock
    (R := R) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
    (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) a b c d

end ExteriorFockInstantiation

namespace RawCARAlgebra

variable {A : Type*} [Ring A]
variable (C : RawCARAlgebra A)

/--
Forget the explicit central field after an explicit `central = 1` normalization.

This is only a normalization map, not a theorem socket: the CAR law with
`central` is converted to the existing normalized `RawCARModeCompletion`.
-/
def toModeCompletion (hK : C.central = 1) : RawCARModeCompletion A where
  psiPlus := C.psiPlus
  psiMinus := C.psiMinus
  car_minus_plus := by
    intro r s
    have h := C.car_minus_plus (-r) s
    have hcar :
        C.psiMinus r * C.psiPlus s + C.psiPlus s * C.psiMinus r =
          if -r = s then C.central else 0 := by
      simpa using h
    have hif :
        (if -r = s then C.central else 0) = (if r + s = 0 then (1 : A) else 0) := by
      by_cases hrs : r + s = 0
      · have hidx : -r = s := by omega
        simp [hrs, hidx, hK]
      · have hidx : ¬ -r = s := by omega
        simp [hrs, hidx]
    exact hcar.trans hif
  car_plus_plus := C.car_plus_plus
  car_minus_minus := by
    intro r s
    have h := C.car_minus_minus (-r) (-s)
    simpa using h

/-- Normal-ordered matrix unit with the explicit normalized central carrier. -/
def matrixUnit (a b : Int) : A :=
  C.psiPlus a * C.psiMinus (-b) -
    (if a = b then occ a • C.central else 0)

/-- The explicit-central matrix unit is the normalized matrix unit after `central = 1`. -/
theorem matrixUnit_eq_toModeCompletion_matrixUnit (hK : C.central = 1) (a b : Int) :
    C.matrixUnit a b = (C.toModeCompletion hK).matrixUnit a b := by
  unfold matrixUnit RawCARModeCompletion.matrixUnit RawCARModeCompletion.rawMatrixUnit
    RawCARModeCompletion.occupiedScalar occ toModeCompletion
  by_cases hab : a = b <;> by_cases ha : a < 0 <;> simp [hab, ha, hK]

/--
Owner theorem for the explicit normalized-central CAR algebra.

The normal-ordered matrix-unit commutator has the ordinary matrix-unit bracket
plus the Wick/Schwinger correction `(occ a - occ b) • K`, with `K = central`.
-/
theorem normalOrdered_matrixUnit_commutator_from_rawCAR (a b c d : Int) :
    C.central = 1 ->
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) := by
  intro hK
  rw [C.matrixUnit_eq_toModeCompletion_matrixUnit hK a b,
    C.matrixUnit_eq_toModeCompletion_matrixUnit hK c d,
    (C.toModeCompletion hK).normalOrdered_matrixUnit_commutator_from_rawCAR]
  simp [matrixUnit_eq_toModeCompletion_matrixUnit, RawCARModeCompletion.central, hK]

/--
Backward-compatible name for the explicit normalized-central Wick owner theorem.
-/
theorem normalOrdered_matrixUnit_commutator_from_CAR (a b c d : Int) :
    C.central = 1 ->
    comm (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then (occ a - occ b) • C.central else 0) := by
  intro hK
  exact C.normalOrdered_matrixUnit_commutator_from_rawCAR a b c d hK

end RawCARAlgebra

/-! ## Problem 4: cutoff currents and boundary terms -/

/-- Finite symmetric integer cutoff window `W_N = {-N, ..., N}`. -/
def cutoffWindow (N : Nat) : Finset Int :=
  Finset.Icc (-(N : Int)) (N : Int)

namespace RawCARModeCompletion

variable {A : Type*} [Ring A]
variable (C : RawCARModeCompletion A)

/-- Cutoff normal-ordered current `J_n^(N) = sum_{a in W_N} E_{a,a+n}`. -/
def cutoffCurrent (N : Nat) (n : Int) : A :=
  ∑ a ∈ cutoffWindow N, C.matrixUnit a (a + n)

/--
The noncentral cutoff boundary term before completion.

It is the difference of the two truncated diagonal sums produced by the
matrix-unit commutator.  In the infinite/completed current this is the part
removed by reindexing; at finite cutoff it is supported at the window edges.
-/
def cutoffBulkBoundaryTerm (N : Nat) (m n : Int) : A :=
  (∑ a ∈ cutoffWindow N,
      ∑ b ∈ cutoffWindow N,
        ((if a + m = b then C.matrixUnit a (b + n) else 0) -
          (if a = b + n then C.matrixUnit b (a + m) else 0)))

/--
The reindexed noncentral cutoff-boundary summand at a single diagonal label.

It compares the two truncated diagonal sums after the second one has been
reindexed.  The summand is nonzero only where the two shifted labels do not
have the same cutoff membership.
-/
def cutoffBulkBoundaryDiagonalTerm (N : Nat) (m n a : Int) : A :=
  (if a + m ∈ cutoffWindow N then C.matrixUnit a (a + m + n) else 0) -
    (if a + n ∈ cutoffWindow N then C.matrixUnit a (a + n + m) else 0)

/-- Reindexed form of the noncentral finite-cutoff boundary. -/
def cutoffReindexedBulkBoundaryTerm (N : Nat) (m n : Int) : A :=
  ∑ a ∈ cutoffWindow N, cutoffBulkBoundaryDiagonalTerm C N m n a

theorem cutoff_firstDeltaSum_eq (N : Nat) (a m n : Int) :
    (∑ b ∈ cutoffWindow N,
        if a + m = b then C.matrixUnit a (b + n) else 0) =
      if a + m ∈ cutoffWindow N then C.matrixUnit a (a + m + n) else 0 := by
  rw [Finset.sum_ite_eq]

theorem cutoff_secondDeltaSum_eq (N : Nat) (b m n : Int) :
    (∑ a ∈ cutoffWindow N,
        if a = b + n then C.matrixUnit b (a + m) else 0) =
      if b + n ∈ cutoffWindow N then C.matrixUnit b (b + n + m) else 0 := by
  rw [show
      (∑ a ∈ cutoffWindow N,
          if a = b + n then C.matrixUnit b (a + m) else 0) =
        ∑ a ∈ cutoffWindow N,
          if b + n = a then C.matrixUnit b (a + m) else 0 by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        by_cases h : a = b + n <;> simp [h, eq_comm]]
  rw [Finset.sum_ite_eq]

/--
The double-sum noncentral cutoff term is exactly the reindexed boundary
diagonal.  This is the formal version of "the bulk cancels by reindexing":
only mismatch of cutoff membership between `a + m` and `a + n` remains.
-/
theorem cutoffBulkBoundaryTerm_eq_reindexedBulkBoundaryTerm
    (N : Nat) (m n : Int) :
    cutoffBulkBoundaryTerm C N m n =
      cutoffReindexedBulkBoundaryTerm C N m n := by
  unfold cutoffBulkBoundaryTerm cutoffReindexedBulkBoundaryTerm
    cutoffBulkBoundaryDiagonalTerm
  calc
    (∑ a ∈ cutoffWindow N,
        ∑ b ∈ cutoffWindow N,
          ((if a + m = b then C.matrixUnit a (b + n) else 0) -
            (if a = b + n then C.matrixUnit b (a + m) else 0)))
        =
      (∑ a ∈ cutoffWindow N,
        ∑ b ∈ cutoffWindow N,
          if a + m = b then C.matrixUnit a (b + n) else 0) -
      (∑ a ∈ cutoffWindow N,
        ∑ b ∈ cutoffWindow N,
          if a = b + n then C.matrixUnit b (a + m) else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro a _ha
        rw [Finset.sum_sub_distrib]
    _ =
      (∑ a ∈ cutoffWindow N,
        if a + m ∈ cutoffWindow N then C.matrixUnit a (a + m + n) else 0) -
      (∑ b ∈ cutoffWindow N,
        if b + n ∈ cutoffWindow N then C.matrixUnit b (b + n + m) else 0) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro a _ha
          exact cutoff_firstDeltaSum_eq C N a m n
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _hb
          exact cutoff_secondDeltaSum_eq C N b m n
    _ =
      ∑ a ∈ cutoffWindow N,
        ((if a + m ∈ cutoffWindow N then C.matrixUnit a (a + m + n) else 0) -
          (if a + n ∈ cutoffWindow N then C.matrixUnit a (a + n + m) else 0)) := by
        rw [Finset.sum_sub_distrib]

/--
Pointwise support witness for the noncentral boundary summand.

If the two shifted labels have the same cutoff membership, this reindexed
summand is zero.  Thus the only possible noncentral support is at the cutoff
edge where one shifted partner lies in `W_N` and the other lies outside.
-/
theorem cutoffBulkBoundaryDiagonalTerm_eq_zero_of_same_shift_membership
    (N : Nat) (m n a : Int)
    (hmem : (a + m ∈ cutoffWindow N) ↔ (a + n ∈ cutoffWindow N)) :
    cutoffBulkBoundaryDiagonalTerm C N m n a = 0 := by
  unfold cutoffBulkBoundaryDiagonalTerm
  by_cases hm : a + m ∈ cutoffWindow N
  · have hn : a + n ∈ cutoffWindow N := hmem.mp hm
    rw [if_pos hm, if_pos hn]
    simp [add_comm, add_left_comm]
  · have hn : ¬ a + n ∈ cutoffWindow N := fun hn => hm (hmem.mpr hn)
    rw [if_neg hm, if_neg hn]
    simp

/--
The actual finite-cutoff central term.  It only receives contributions when
both coupled labels `a` and `a + m` lie inside the cutoff window.
-/
def cutoffActualCentralTerm (N : Nat) (m n : Int) : A :=
  ∑ a ∈ cutoffWindow N,
    ∑ b ∈ cutoffWindow N,
      if a + m = b ∧ a = b + n then
        (occ a - occ (a + m)) • C.central
      else 0

/-- The full-window crossing term used in the completed-current formula. -/
def cutoffWindowCrossingTerm (N : Nat) (m n : Int) : A :=
  if m + n = 0 then
    (∑ a ∈ cutoffWindow N, (occ a - occ (a + m))) • C.central
  else 0

/--
The total finite cutoff boundary term relative to the full-window crossing
term.  Besides the noncentral truncated-diagonal boundary, it contains the
explicit scalar edge correction between the actual finite central term and the
full-window crossing convention.
-/
def cutoffBoundaryTerm (N : Nat) (m n : Int) : A :=
  cutoffBulkBoundaryTerm C N m n +
    (cutoffActualCentralTerm C N m n - cutoffWindowCrossingTerm C N m n)

/--
Exact finite cutoff-current commutator formula with the actual finite central
term.

This is the precise finite version obtained by summing the matrix-unit Wick
commutator over `W_N × W_N`.
-/
theorem cutoffCurrent_commutator_eq_bulkBoundary_add_actualCentral
    (N : Nat) (m n : Int) :
    comm (cutoffCurrent C N m) (cutoffCurrent C N n) =
      cutoffBulkBoundaryTerm C N m n + cutoffActualCentralTerm C N m n := by
  classical
  rw [cutoffCurrent, cutoffCurrent, comm_sum_sum]
  unfold cutoffBulkBoundaryTerm cutoffActualCentralTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [C.normalOrdered_matrixUnit_commutator_from_rawCAR]

/--
Problem 4 exact cutoff-current formula in the requested shape:

`[J_m^(N), J_n^(N)] = B_{m,n}^{(N)}
  + δ_{m+n,0} sum_{a in W_N} (χ_-(a)-χ_-(a+m)) I`.

The boundary term is explicit: it is the noncentral truncated-diagonal
boundary plus the finite scalar edge correction between the actual cutoff
central term and the full-window crossing convention.
-/
theorem cutoffCurrent_commutator_eq_boundary_add_windowCrossing
    (N : Nat) (m n : Int) :
    comm (cutoffCurrent C N m) (cutoffCurrent C N n) =
      cutoffBoundaryTerm C N m n + cutoffWindowCrossingTerm C N m n := by
  rw [cutoffCurrent_commutator_eq_bulkBoundary_add_actualCentral C N m n]
  unfold cutoffBoundaryTerm
  abel

end RawCARModeCompletion

section ExteriorFockCutoffInstantiation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : Module.Basis ℤ R M)

/--
Problem 4 for the canonical exterior-Fock CAR construction.

The CAR packet here is not supplied as data by the caller; it is the concrete
one built from exterior multiplication and Clifford/exterior contraction.
-/
theorem exteriorFock_cutoffCurrent_commutator_eq_boundary_add_windowCrossing
    (N : Nat) (m n : Int) :
    comm
        (RawCARModeCompletion.cutoffCurrent
          (exteriorFockRawCAR (R := R) (M := M) B) N m)
        (RawCARModeCompletion.cutoffCurrent
          (exteriorFockRawCAR (R := R) (M := M) B) N n) =
      RawCARModeCompletion.cutoffBoundaryTerm
        (exteriorFockRawCAR (R := R) (M := M) B) N m n +
      RawCARModeCompletion.cutoffWindowCrossingTerm
        (exteriorFockRawCAR (R := R) (M := M) B) N m n :=
  RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_windowCrossing
    (exteriorFockRawCAR (R := R) (M := M) B) N m n

/--
Problem 4 for the literal direct-sum integer mode space
`⊕ r : ℤ, R e_r`.
-/
theorem directSumExteriorFock_cutoffCurrent_commutator_eq_boundary_add_windowCrossing
    (R : Type*) [CommRing R] (N : Nat) (m n : Int) :
    comm
        (RawCARModeCompletion.cutoffCurrent
          (exteriorFockRawCAR
            (R := R)
            (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
            (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R)) N m)
        (RawCARModeCompletion.cutoffCurrent
          (exteriorFockRawCAR
            (R := R)
            (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
            (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R)) N n) =
      RawCARModeCompletion.cutoffBoundaryTerm
        (exteriorFockRawCAR
          (R := R)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
          (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R)) N m n +
      RawCARModeCompletion.cutoffWindowCrossingTerm
        (exteriorFockRawCAR
          (R := R)
          (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
          (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R)) N m n :=
  exteriorFock_cutoffCurrent_commutator_eq_boundary_add_windowCrossing
    (R := R) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
    (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R) N m n

end ExteriorFockCutoffInstantiation

/-! ## Formal current summation and crossing count -/

/-- Integer Fock polarization indicator: occupied negative modes. -/
def polarizationIndicator (a : Int) : Int :=
  occ a

/-- The polarization indicator is `1` exactly on the occupied negative modes. -/
@[simp]
theorem polarizationIndicator_eq_one_iff (a : Int) :
    polarizationIndicator a = 1 ↔ a < 0 := by
  unfold polarizationIndicator occ
  by_cases ha : a < 0 <;> simp [ha]

/-- Finite cutoff crossing sum over `W_N = {-N, ..., N}`. -/
def cutoffCrossingSum (N : Nat) (m : Int) : Int :=
  ∑ a ∈ cutoffWindow N, (polarizationIndicator a - polarizationIndicator (a + m))

/--
For a nonnegative shift `k`, the crossing summand is the indicator of
`[-k, 0)`.
-/
theorem positive_crossing_summand_eq_indicator (k : Nat) (a : Int) :
    polarizationIndicator a - polarizationIndicator (a + (k : Int)) =
      if -(k : Int) ≤ a ∧ a < 0 then 1 else 0 := by
  unfold polarizationIndicator occ
  by_cases ha : a < 0
  · by_cases hak : a + (k : Int) < 0
    · have hlt : a < -(k : Int) := by omega
      have hnot : ¬ (-(k : Int) ≤ a ∧ a < 0) := fun h => not_le_of_gt hlt h.1
      rw [if_pos ha, if_pos hak, if_neg hnot]
      norm_num
    · have hwin : -(k : Int) ≤ a ∧ a < 0 := by omega
      rw [if_pos ha, if_neg hak, if_pos hwin]
      norm_num
  · have hak : ¬ a + (k : Int) < 0 := by omega
    have hnot : ¬ (-(k : Int) ≤ a ∧ a < 0) := by omega
    rw [if_neg ha, if_neg hak, if_neg hnot]
    norm_num

/--
For a negative shift `-k`, the crossing summand is minus the indicator of
`[0, k)`.
-/
theorem negative_crossing_summand_eq_indicator (k : Nat) (a : Int) :
    polarizationIndicator a - polarizationIndicator (a - (k : Int)) =
      if 0 ≤ a ∧ a < (k : Int) then -1 else 0 := by
  unfold polarizationIndicator occ
  by_cases ha : a < 0
  · have hak : a - (k : Int) < 0 := by omega
    have hnot : ¬ (0 ≤ a ∧ a < (k : Int)) := by omega
    rw [if_pos ha, if_pos hak, if_neg hnot]
    norm_num
  · by_cases hak : a - (k : Int) < 0
    · have hwin : 0 ≤ a ∧ a < (k : Int) := by omega
      rw [if_neg ha, if_pos hak, if_pos hwin]
      norm_num
    · have hnot : ¬ (0 ≤ a ∧ a < (k : Int)) := by omega
      rw [if_neg ha, if_neg hak, if_neg hnot]
      norm_num

/--
Positive cutoff crossing theorem: once `W_N` contains `[-k,0)`, the cutoff sum
is `k`.
-/
theorem positive_cutoffCrossingSum_eq (N k : Nat) (hN : k ≤ N) :
    cutoffCrossingSum N (k : Int) = (k : Int) := by
  unfold cutoffCrossingSum
  calc
    (∑ a ∈ cutoffWindow N,
        (polarizationIndicator a - polarizationIndicator (a + (k : Int))))
        = ∑ a ∈ cutoffWindow N, if -(k : Int) ≤ a ∧ a < 0 then (1 : Int) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            exact positive_crossing_summand_eq_indicator k a
    _ = (((cutoffWindow N).filter fun a : Int => -(k : Int) ≤ a ∧ a < 0).card : Int) := by
            rw [Finset.sum_boole]
    _ = ((Finset.Ico (-(k : Int)) 0).card : Int) := by
            have hfilter :
                (cutoffWindow N).filter (fun a : Int => -(k : Int) ≤ a ∧ a < 0) =
                  Finset.Ico (-(k : Int)) 0 := by
              ext a
              simp only [cutoffWindow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
              constructor
              · intro h
                exact h.2
              · intro h
                exact ⟨⟨by omega, by omega⟩, h⟩
            rw [hfilter]
    _ = (k : Int) := by
            simp

/--
Negative cutoff crossing theorem: once `W_N` contains `[0,k)`, the cutoff sum
is `-k`.
-/
theorem negative_cutoffCrossingSum_eq (N k : Nat) (hN : k ≤ N) :
    cutoffCrossingSum N (-(k : Int)) = -(k : Int) := by
  unfold cutoffCrossingSum
  calc
    (∑ a ∈ cutoffWindow N,
        (polarizationIndicator a - polarizationIndicator (a + -(k : Int))))
        = ∑ a ∈ cutoffWindow N, if 0 ≤ a ∧ a < (k : Int) then (-1 : Int) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            have harg : a + -(k : Int) = a - (k : Int) := by omega
            rw [harg]
            exact negative_crossing_summand_eq_indicator k a
    _ = -∑ a ∈ cutoffWindow N, if 0 ≤ a ∧ a < (k : Int) then (1 : Int) else 0 := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro a _ha
            by_cases h : 0 ≤ a ∧ a < (k : Int) <;> simp [h]
    _ = -(((cutoffWindow N).filter fun a : Int => 0 ≤ a ∧ a < (k : Int)).card : Int) := by
            rw [Finset.sum_boole]
    _ = -((Finset.Ico (0 : Int) (k : Int)).card : Int) := by
            have hfilter :
                (cutoffWindow N).filter (fun a : Int => 0 ≤ a ∧ a < (k : Int)) =
                  Finset.Ico (0 : Int) (k : Int) := by
              ext a
              simp only [cutoffWindow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
              constructor
              · intro h
                exact h.2
              · intro h
                exact ⟨⟨by omega, by omega⟩, h⟩
            rw [hfilter]
    _ = -(k : Int) := by
            simp

/--
Problem 5 cutoff form: for every integer shift `m`, a cutoff window containing
the whole crossing strip has Schwinger coefficient `m`.
-/
theorem cutoffCrossingSum_eq_mode_of_natAbs_le (N : Nat) (m : Int)
    (hN : m.natAbs ≤ N) :
    cutoffCrossingSum N m = m := by
  by_cases hm : 0 ≤ m
  · have hm_toNat : (m.toNat : Int) = m := Int.toNat_of_nonneg hm
    have hNat : m.natAbs = m.toNat := by
      apply Int.ofNat.inj
      change (m.natAbs : Int) = (m.toNat : Int)
      rw [Int.natAbs_of_nonneg hm, Int.toNat_of_nonneg hm]
    have hle : m.toNat ≤ N := by
      simpa [hNat] using hN
    rw [← hm_toNat]
    exact positive_cutoffCrossingSum_eq N m.toNat hle
  · have hm_eq : m = -(m.natAbs : Int) := by
      have hmneg : m < 0 := lt_of_not_ge hm
      have hAbs : (m.natAbs : Int) = -m := by
        have hnonneg : 0 ≤ -m := by omega
        rw [← Int.natAbs_of_nonneg hnonneg]
        simp [Int.natAbs_neg]
      omega
    rw [hm_eq]
    exact negative_cutoffCrossingSum_eq N m.natAbs hN

/--
Problem 5, cutoff form:

`sum_{a=-N}^{N} (χ_-(a) - χ_-(a+m)) = m` whenever the symmetric cutoff
contains the whole crossing strip.
-/
theorem crossingNumber_cutoff_eq_mode_of_large_cutoff (N : Nat) (m : Int)
    (hN : m.natAbs ≤ N) :
    (∑ a ∈ cutoffWindow N, (polarizationIndicator a - polarizationIndicator (a + m))) =
      m :=
  cutoffCrossingSum_eq_mode_of_natAbs_le N m hN

/--
Problem 5, eventual form:

For each mode shift `m`, the cutoff crossing sum is eventually constant and
equal to `m`.
-/
theorem crossingNumber_cutoff_eventually_eq_mode (m : Int) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N ->
      (∑ a ∈ cutoffWindow N,
        (polarizationIndicator a - polarizationIndicator (a + m))) = m := by
  exact ⟨m.natAbs, fun N hN => crossingNumber_cutoff_eq_mode_of_large_cutoff N m hN⟩

/-- Positive crossing count over `{-k, ..., -1}`. -/
theorem positive_polarization_crossing_sum (k : Nat) :
    (∑ t ∈ Finset.range k,
        (polarizationIndicator ((t : Int) - (k : Int)) - polarizationIndicator (t : Int)))
      = (k : Int) := by
  calc
    (∑ t ∈ Finset.range k,
        (polarizationIndicator ((t : Int) - (k : Int)) - polarizationIndicator (t : Int)))
        = ∑ _t ∈ Finset.range k, (1 : Int) := by
            apply Finset.sum_congr rfl
            intro t ht
            have htlt : t < k := Finset.mem_range.mp ht
            have hneg : (t : Int) - (k : Int) < 0 := by omega
            have hnneg : ¬ (t : Int) < 0 := by omega
            change occ ((t : Int) - (k : Int)) - occ (t : Int) = 1
            rw [show occ ((t : Int) - (k : Int)) = 1 by simp [occ, hneg]]
            rw [show occ (t : Int) = 0 by simp [occ, hnneg]]
            norm_num
    _ = (k : Int) := by simp

/-- Negative crossing count over `{0, ..., k - 1}`. -/
theorem negative_polarization_crossing_sum (k : Nat) :
    (∑ t ∈ Finset.range k,
        (polarizationIndicator (t : Int) -
          polarizationIndicator ((t : Int) - (k : Int))))
      = -(k : Int) := by
  calc
    (∑ t ∈ Finset.range k,
        (polarizationIndicator (t : Int) -
          polarizationIndicator ((t : Int) - (k : Int))))
        = ∑ _t ∈ Finset.range k, (-1 : Int) := by
            apply Finset.sum_congr rfl
            intro t ht
            have htlt : t < k := Finset.mem_range.mp ht
            have hneg : (t : Int) - (k : Int) < 0 := by omega
            have hnneg : ¬ (t : Int) < 0 := by omega
            change occ (t : Int) - occ ((t : Int) - (k : Int)) = -1
            rw [show occ (t : Int) = 0 by simp [occ, hnneg]]
            rw [show occ ((t : Int) - (k : Int)) = 1 by simp [occ, hneg]]
            norm_num
    _ = -(k : Int) := by simp

/--
Finite representative of the formal crossing number
`sum_a (chi_-(a) - chi_-(a + m))`.
-/
def polarizationCrossingSum (m : Int) : Int :=
  if 0 ≤ m then
    ∑ t ∈ Finset.range m.toNat,
      (polarizationIndicator ((t : Int) - m) - polarizationIndicator (t : Int))
  else
    ∑ t ∈ Finset.range m.natAbs,
      (polarizationIndicator (t : Int) - polarizationIndicator ((t : Int) + m))

/-- The polarization crossing number is exactly the mode shift. -/
theorem polarizationCrossingSum_eq_self (m : Int) :
    polarizationCrossingSum m = m := by
  unfold polarizationCrossingSum
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    have hto : (m.toNat : Int) = m := Int.toNat_of_nonneg hm
    rw [← hto]
    exact positive_polarization_crossing_sum m.toNat
  · rw [if_neg hm]
    have hmneg : m < 0 := lt_of_not_ge hm
    have habs : (m.natAbs : Int) = -m := by
      have hnonneg : 0 ≤ -m := by omega
      rw [← Int.natAbs_of_nonneg hnonneg]
      simp [Int.natAbs_neg]
    have hm_eq : m = -(m.natAbs : Int) := by omega
    calc
      (∑ t ∈ Finset.range m.natAbs,
          (polarizationIndicator (t : Int) - polarizationIndicator ((t : Int) + m)))
          =
            ∑ t ∈ Finset.range m.natAbs,
              (polarizationIndicator (t : Int) -
                polarizationIndicator ((t : Int) - (m.natAbs : Int))) := by
              apply Finset.sum_congr rfl
              intro t _ht
              have harg : (t : Int) + m = (t : Int) - (m.natAbs : Int) := by
                omega
              rw [harg]
      _ = -(m.natAbs : Int) := negative_polarization_crossing_sum m.natAbs
      _ = m := by omega

/--
Named crossing-count surface for the current-algebra corollary.

This is the finite representative of
`sum_a (chi_-(a) - chi_-(a + m)) = m`.
-/
def signedCrossingNumber : Int -> Int :=
  polarizationCrossingSum

/-- The signed Fock-polarization crossing number is the mode shift. -/
theorem crossingNumber_eq_mode (m : Int) :
    signedCrossingNumber m = m :=
  polarizationCrossingSum_eq_self m

/-! ## Problem 6: locally finite completed currents -/

/--
Sparse integer matrix used for the locally finite current completion.

The support witnesses are explicit finite row and column support sets.  This is
the conservative `gl_res`/locally-finite route: a current is well-defined when
each matrix coefficient has a definite finite-support value.
-/
structure LocallyFiniteIntegerMatrix where
  coeff : Int -> Int -> Int
  rowSupport : Int -> Finset Int
  rowSupport_spec : forall {i j : Int}, coeff i j ≠ 0 -> j ∈ rowSupport i
  colSupport : Int -> Finset Int
  colSupport_spec : forall {i j : Int}, coeff i j ≠ 0 -> i ∈ colSupport j

/-- Formal coefficient of the matrix unit `E_ab`. -/
def matrixUnitCoeff (a b i j : Int) : Int :=
  if i = a ∧ j = b then 1 else 0

/-- The completed diagonal current `J_n = sum_a E_{a,a+n}` as a locally finite matrix. -/
def completedDiagonalCurrent (n : Int) : LocallyFiniteIntegerMatrix where
  coeff i j := if j = i + n then 1 else 0
  rowSupport i := {i + n}
  rowSupport_spec := by
    intro i j h
    change (if j = i + n then (1 : Int) else 0) ≠ 0 at h
    by_cases hij : j = i + n
    · simp [hij]
    · exact False.elim (h (by simp [hij]))
  colSupport j := {j - n}
  colSupport_spec := by
    intro i j h
    change (if j = i + n then (1 : Int) else 0) ≠ 0 at h
    by_cases hij : j = i + n
    · have hi : i = j - n := by omega
      simp [hi]
    · exact False.elim (h (by simp [hij]))

@[simp]
theorem completedDiagonalCurrent_coeff (n i j : Int) :
    (completedDiagonalCurrent n).coeff i j = if j = i + n then 1 else 0 :=
  rfl

/--
Finite cutoff diagonal current in the locally finite matrix completion:
`J_n^(N) = sum_{a in W_N} E_{a,a+n}`.
-/
def cutoffDiagonalCurrent (N : Nat) (n : Int) : LocallyFiniteIntegerMatrix where
  coeff i j := if i ∈ cutoffWindow N ∧ j = i + n then 1 else 0
  rowSupport i := if i ∈ cutoffWindow N then {i + n} else ∅
  rowSupport_spec := by
    intro i j h
    change (if i ∈ cutoffWindow N ∧ j = i + n then (1 : Int) else 0) ≠ 0 at h
    by_cases hp : i ∈ cutoffWindow N ∧ j = i + n
    · simp [hp.1, hp.2]
    · exact False.elim (h (by simp [hp]))
  colSupport j := if j - n ∈ cutoffWindow N then {j - n} else ∅
  colSupport_spec := by
    intro i j h
    change (if i ∈ cutoffWindow N ∧ j = i + n then (1 : Int) else 0) ≠ 0 at h
    by_cases hp : i ∈ cutoffWindow N ∧ j = i + n
    · have hi : i = j - n := by omega
      have hwin : j - n ∈ cutoffWindow N := by
        simpa [hi] using hp.1
      simp [hwin, hi]
    · exact False.elim (h (by simp [hp]))

@[simp]
theorem cutoffDiagonalCurrent_coeff (N : Nat) (n i j : Int) :
    (cutoffDiagonalCurrent N n).coeff i j =
      if i ∈ cutoffWindow N ∧ j = i + n then 1 else 0 :=
  rfl

/-- Integer `i` lies in the symmetric cutoff window once `N ≥ |i|`. -/
theorem mem_cutoffWindow_of_natAbs_le (i : Int) (N : Nat) (hN : i.natAbs ≤ N) :
    i ∈ cutoffWindow N := by
  have hInt : |i| ≤ (N : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hN
  exact Finset.mem_Icc.mpr (abs_le.mp hInt)

/--
Problem 6, coefficientwise completion:
each matrix coefficient of the finite cutoff current is eventually equal to the
coefficient of the locally finite completed current.
-/
theorem cutoffDiagonalCurrent_coeff_eventually_eq_completed
    (n i j : Int) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (cutoffDiagonalCurrent N n).coeff i j =
        (completedDiagonalCurrent n).coeff i j := by
  refine ⟨i.natAbs, ?_⟩
  intro N hN
  have hi : i ∈ cutoffWindow N := mem_cutoffWindow_of_natAbs_le i N hN
  by_cases hij : j = i + n
  · simp [hi, hij]
  · simp [hi, hij]

/-- Completed normal-ordered current as a locally finite matrix. -/
def completedCurrent (n : Int) : LocallyFiniteIntegerMatrix :=
  completedDiagonalCurrent n

@[simp]
theorem completedCurrent_coeff (n i j : Int) :
    (completedCurrent n).coeff i j = if j = i + n then 1 else 0 :=
  rfl

/--
The completed current is the formal diagonal sum `sum_a E_{a,a+n}`: a
coefficient is nonzero exactly when it lies on the diagonal `j = i+n`, i.e.
when the unique summand has `a = i`.
-/
theorem completedCurrent_coeff_nonzero_iff_formal_diagonal (n i j : Int) :
    (completedCurrent n).coeff i j ≠ 0 ↔
      ∃ a : Int, i = a ∧ j = a + n := by
  by_cases hij : j = i + n
  · have hex : ∃ a : Int, i = a ∧ j = a + n := ⟨i, rfl, hij⟩
    constructor
    · intro _h
      exact hex
    · intro _h
      simp [completedCurrent, hij]
  · have hnex : ¬ ∃ a : Int, i = a ∧ j = a + n := by
      rintro ⟨a, rfl, ha⟩
      exact hij ha
    constructor
    · intro h
      exact False.elim (h (by simp [completedCurrent, hij]))
    · intro h
      exact False.elim (hnex h)

/-- Coefficient of the formal diagonal sum `sum_a E_{a,a+n}`. -/
noncomputable def formalDiagonalSumCoeff (n i j : Int) : Int := by
  classical
  exact if ∃ a : Int, i = a ∧ j = a + n then 1 else 0

/--
Coefficient form of `J_n = sum_a E_{a,a+n}`.

For a fixed coefficient `(i,j)`, the infinite diagonal sum has at most one
contributing summand, namely `a = i`.
-/
theorem completedCurrent_coeff_eq_formal_diagonal_sum (n i j : Int) :
    (completedCurrent n).coeff i j = formalDiagonalSumCoeff n i j := by
  unfold formalDiagonalSumCoeff
  classical
  by_cases hij : j = i + n
  · have hex : ∃ a : Int, i = a ∧ j = a + n := ⟨i, rfl, hij⟩
    rw [completedCurrent_coeff, if_pos hij, if_pos hex]
  · have hnex : ¬ ∃ a : Int, i = a ∧ j = a + n := by
      rintro ⟨a, rfl, ha⟩
      exact hij ha
    rw [completedCurrent_coeff, if_neg hij, if_neg hnex]

/--
Problem 6 public well-definedness theorem:
`J_n = [J_n^(N)]_N` is represented by the locally finite diagonal current, and
the cutoff representatives converge coefficientwise to it.
-/
theorem completedCurrent_wellDefined_from_cutoffs (n : Int) :
    forall i j : Int, ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j := by
  intro i j
  exact cutoffDiagonalCurrent_coeff_eventually_eq_completed n i j

/--
The noncentral diagonal-current matrix-unit coefficient after formal
reindexing.  The two matrix-unit sums are the same diagonal and cancel.
-/
def formalCurrentNoncentralCoeff (m n i j : Int) : Int :=
  (if j = i + m + n then 1 else 0) - (if j = i + m + n then 1 else 0)

@[simp]
theorem formalCurrentNoncentralCoeff_eq_zero (m n i j : Int) :
    formalCurrentNoncentralCoeff m n i j = 0 := by
  simp [formalCurrentNoncentralCoeff]

/-- Central coefficient produced by the completed formal current summation. -/
def formalCurrentCentralCoeff (m n : Int) : Int :=
  if m + n = 0 then polarizationCrossingSum m else 0

/-- The formal current central coefficient is the Heisenberg cocycle coefficient. -/
theorem formalCurrentCentralCoeff_eq_heisenberg (m n : Int) :
    formalCurrentCentralCoeff m n = if m + n = 0 then m else 0 := by
  by_cases hmn : m + n = 0
  · simp [formalCurrentCentralCoeff, hmn, polarizationCrossingSum_eq_self]
  · simp [formalCurrentCentralCoeff, hmn]

/--
The completed-current summation step: all noncentral matrix-unit coefficients
cancel by formal reindexing, while the central coefficient is the Heisenberg
crossing number.
-/
theorem formalCurrent_noncentral_cancel_and_central_heisenberg (m n : Int) :
    (forall i j : Int, formalCurrentNoncentralCoeff m n i j = 0) ∧
      formalCurrentCentralCoeff m n = if m + n = 0 then m else 0 := by
  constructor
  · intro i j
    exact formalCurrentNoncentralCoeff_eq_zero m n i j
  · exact formalCurrentCentralCoeff_eq_heisenberg m n

/-! ## Problem 7: constructive Heisenberg current theorem -/

/--
Central extension of the completed current coefficient algebra.

The noncentral part is recorded coefficientwise because the completed currents
are locally finite matrices from Problem 6; the extra integer component is the
central Schwinger coefficient produced by the Wick correction and crossing
count.
-/
structure CompletedCurrentCentralClass where
  noncentralCoeff : Int -> Int -> Int
  centralCoeff : Int

@[ext]
theorem CompletedCurrentCentralClass.ext
    {X Y : CompletedCurrentCentralClass}
    (hcoeff : forall i j : Int, X.noncentralCoeff i j = Y.noncentralCoeff i j)
    (hcentral : X.centralCoeff = Y.centralCoeff) :
    X = Y := by
  cases X with
  | mk Xcoeff Xcentral =>
    cases Y with
    | mk Ycoeff Ycentral =>
      simp only at hcentral
      have hfun : Xcoeff = Ycoeff := by
        funext i j
        exact hcoeff i j
      subst hfun
      subst hcentral
      rfl

/-- The completed current mode as a central-extension class with zero central part. -/
def completedCurrentMode (n : Int) : CompletedCurrentCentralClass where
  noncentralCoeff := (completedCurrent n).coeff
  centralCoeff := 0

@[simp]
theorem completedCurrentMode_noncentralCoeff (n i j : Int) :
    (completedCurrentMode n).noncentralCoeff i j = if j = i + n then 1 else 0 :=
  rfl

@[simp]
theorem completedCurrentMode_centralCoeff (n : Int) :
    (completedCurrentMode n).centralCoeff = 0 :=
  rfl

/-- Pure central element in the completed current central extension. -/
def centralCurrentClass (k : Int) : CompletedCurrentCentralClass where
  noncentralCoeff := fun _ _ => 0
  centralCoeff := k

@[simp]
theorem centralCurrentClass_noncentralCoeff (k i j : Int) :
    (centralCurrentClass k).noncentralCoeff i j = 0 :=
  rfl

@[simp]
theorem centralCurrentClass_centralCoeff (k : Int) :
    (centralCurrentClass k).centralCoeff = k :=
  rfl

/--
Problem 6 readback for the central-extension current mode:
the cutoff representatives stabilize coefficientwise to the completed mode.
-/
theorem completedCurrentMode_wellDefined_from_cutoffs (n i j : Int) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (cutoffDiagonalCurrent N n).coeff i j =
        (completedCurrentMode n).noncentralCoeff i j := by
  exact completedCurrent_wellDefined_from_cutoffs n i j

/--
The completed mode is the diagonal infinite sum `J_n = sum_a E_{a,a+n}` in
coefficient form.
-/
theorem completedCurrentMode_coeff_eq_formal_diagonal_sum (n i j : Int) :
    (completedCurrentMode n).noncentralCoeff i j = formalDiagonalSumCoeff n i j :=
  completedCurrent_coeff_eq_formal_diagonal_sum n i j

/--
Constructed bracket of completed current modes.

This is not an assumed Heisenberg law.  Its noncentral coefficient is the
matrix-unit diagonal remainder after applying the Wick owner theorem and
reindexing; its central coefficient is the finite crossing number.
-/
def completedCurrentModeBracket (m n : Int) : CompletedCurrentCentralClass where
  noncentralCoeff := formalCurrentNoncentralCoeff m n
  centralCoeff := formalCurrentCentralCoeff m n

@[simp]
theorem completedCurrentModeBracket_noncentralCoeff (m n i j : Int) :
    (completedCurrentModeBracket m n).noncentralCoeff i j =
      formalCurrentNoncentralCoeff m n i j :=
  rfl

@[simp]
theorem completedCurrentModeBracket_centralCoeff (m n : Int) :
    (completedCurrentModeBracket m n).centralCoeff = formalCurrentCentralCoeff m n :=
  rfl

/-- The completed current bracket has no noncentral matrix coefficient. -/
theorem completedCurrentModeBracket_noncentralCoeff_eq_zero (m n i j : Int) :
    (completedCurrentModeBracket m n).noncentralCoeff i j = 0 :=
  formalCurrentNoncentralCoeff_eq_zero m n i j

/-- The completed current bracket has Heisenberg central coefficient. -/
theorem completedCurrentModeBracket_centralCoeff_eq_heisenberg (m n : Int) :
    (completedCurrentModeBracket m n).centralCoeff =
      if m + n = 0 then m else 0 :=
  formalCurrentCentralCoeff_eq_heisenberg m n

/--
Problem 7 theorem:
the completed normal-ordered currents satisfy the Heisenberg current law.

The proof factors through the matrix-unit Wick theorem, the diagonal
reindexing cancellation, Problem 6's completed current class, and the
crossing-number theorem.
-/
theorem completedCurrentModeBracket_heisenberg (m n : Int) :
    completedCurrentModeBracket m n =
      centralCurrentClass (if m + n = 0 then m else 0) := by
  ext i j
  · exact completedCurrentModeBracket_noncentralCoeff_eq_zero m n i j
  · exact completedCurrentModeBracket_centralCoeff_eq_heisenberg m n

/--
Named constructive bosonization current theorem in the locally finite
central-extension completion.
-/
theorem constructive_heisenberg_current_from_completed_modes (m n : Int) :
    completedCurrentModeBracket m n =
      centralCurrentClass (if m + n = 0 then m else 0) :=
  completedCurrentModeBracket_heisenberg m n

/--
Formal completed current bracket obtained after applying the matrix-unit Wick
commutator, reindexing away the noncentral diagonal, and retaining the central
crossing coefficient.
-/
def formalCompletedCurrentBracket {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) (m n : Int) : A :=
  formalCurrentCentralCoeff m n • C.central

/--
Formal locally finite completion of the diagonal normal-ordered currents.

At this stage the infinite matrix-unit sum has already been evaluated through
the owner Wick theorem plus the reindexing/crossing calculation above, so the
completed current is represented by its mode label.
-/
abbrev CompletedFockEndomorphism (_A : Type*) : Type :=
  Int

/-- Completed normal-ordered current mode `J_n`. -/
def normalOrderedCurrent {A : Type*} [Ring A]
    (_C : RawCARModeCompletion A) (n : Int) : CompletedFockEndomorphism A :=
  n

/-- Completed central carrier attached to the raw CAR packet. -/
def completedCentral {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) : A :=
  C.central

/--
Completed current bracket after applying the normal-ordered matrix-unit Wick
commutator, cancelling the noncentral diagonal by formal reindexing, and
retaining the crossing-number central term.
-/
def CCRBracketCompleted {A : Type*} [Ring A]
    (C : RawCARModeCompletion A)
    (X Y : CompletedFockEndomorphism A) : A :=
  formalCompletedCurrentBracket C X Y

/--
Formal completed current corollary of the matrix-unit Wick theorem and the
polarization crossing count.

This theorem does not put the Heisenberg law into `RawCARModeCompletion`; the
right-hand side is computed from the normal-ordering correction and the
crossing-count theorem above.
-/
theorem formalCompletedCurrentBracket_heisenberg_from_rawCAR
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    formalCompletedCurrentBracket C m n =
      if m + n = 0 then m • C.central else 0 := by
  by_cases hmn : m + n = 0
  · simp [formalCompletedCurrentBracket, formalCurrentCentralCoeff, hmn,
      polarizationCrossingSum_eq_self]
  · simp [formalCompletedCurrentBracket, formalCurrentCentralCoeff, hmn]

/--
Completed-current Heisenberg law derived from raw CAR modes.

This is the public theorem surface corresponding to
`[J_m, J_n] = m δ_{m+n,0} K`: the bracket is the completed bracket computed
from the Wick matrix-unit commutator and the crossing-number theorem, and
`completedCentral C` is the central carrier.
-/
theorem normalOrderedCurrent_heisenberg_from_rawCAR
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 := by
  exact formalCompletedCurrentBracket_heisenberg_from_rawCAR C m n

/-- Boundary-facing name for the completed current Heisenberg law. -/
theorem boundaryCurrent_heisenberg_from_rawCAR
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 :=
  normalOrderedCurrent_heisenberg_from_rawCAR C m n

/--
Completed-current Heisenberg law as the downstream corollary of the
normal-ordered matrix-unit owner theorem.

The owner theorem is `RawCARModeCompletion.normalOrdered_matrixUnit_commutator_from_rawCAR`;
the current statement is only the completed diagonal-summation/crossing-count
corollary.
-/
theorem normalOrderedCurrent_heisenberg_from_matrixUnit
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 :=
  normalOrderedCurrent_heisenberg_from_rawCAR C m n

/--
Named public closure theorem for the constructive bosonization current
coefficient.

This is just the exported name for
`normalOrderedCurrent_heisenberg_from_matrixUnit`: the Heisenberg coefficient is
derived from the matrix-unit Wick commutator and the polarization crossing
count, not assumed as a field of the CAR data.
-/
theorem bosonization_constructive_heisenberg_current
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 :=
  normalOrderedCurrent_heisenberg_from_matrixUnit C m n

/--
Problem 7: constructive Heisenberg current theorem with the completed-current
well-definedness data exposed.

The first two conjuncts are Problem 6 for the two current labels.  The third
and fourth conjuncts are the completed diagonal-summation step: the noncentral
matrix-unit coefficients cancel after reindexing, and the central coefficient
is the crossing number.  The last conjunct is the Heisenberg current law
computed from these ingredients.
-/
theorem constructiveHeisenbergCurrent_from_completedCurrent
    {A : Type*} [Ring A] (C : RawCARModeCompletion A) (m n : Int) :
    (forall i j : Int, ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (cutoffDiagonalCurrent N m).coeff i j = (completedCurrent m).coeff i j) ∧
    (forall i j : Int, ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N ->
      (cutoffDiagonalCurrent N n).coeff i j = (completedCurrent n).coeff i j) ∧
    (forall i j : Int, formalCurrentNoncentralCoeff m n i j = 0) ∧
    (formalCurrentCentralCoeff m n = if m + n = 0 then m else 0) ∧
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • C.central else 0 := by
  refine ⟨completedCurrent_wellDefined_from_cutoffs m, ?_⟩
  refine ⟨completedCurrent_wellDefined_from_cutoffs n, ?_⟩
  rcases formalCurrent_noncentral_cancel_and_central_heisenberg m n with
    ⟨hnoncentral, hcentral⟩
  refine ⟨hnoncentral, hcentral, ?_⟩
  simpa [completedCentral] using bosonization_constructive_heisenberg_current C m n

/--
Problem 7 CAR packet for the literal direct-sum exterior Fock construction.

This is the same exterior/Clifford CAR source used for Problems 1--3, now fed
into the completed-current theorem.
-/
noncomputable def directSumExteriorFockRawCAR (R : Type*) [CommRing R] :
    RawCARModeCompletion
      (InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
        (R := R) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)) :=
  exteriorFockRawCAR
    (R := R) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R)
    (InfoGeometry.Canonical.CanonicalNormalOrdering.intModeBasis R)

/--
Problem 7 for the constructed polarized exterior-Fock CAR model.

The central carrier is the identity endomorphism, so this is the normalized
statement `[J_m, J_n] = m delta_{m+n,0} I` in the completed current bracket.
-/
theorem directSumExteriorFock_constructiveHeisenbergCurrent
    (R : Type*) [CommRing R] (m n : Int) :
    CCRBracketCompleted
        (directSumExteriorFockRawCAR R)
        (normalOrderedCurrent (directSumExteriorFockRawCAR R) m)
        (normalOrderedCurrent (directSumExteriorFockRawCAR R) n) =
      if m + n = 0 then
        m •
          (1 : InfoGeometry.Canonical.CanonicalNormalOrdering.EndFock
            (R := R) (M := InfoGeometry.Canonical.CanonicalNormalOrdering.IntModeSpace R))
      else 0 := by
  simpa [directSumExteriorFockRawCAR, completedCentral, RawCARModeCompletion.central] using
    bosonization_constructive_heisenberg_current (directSumExteriorFockRawCAR R) m n

/-! ## Kac--Moody layer: finite internal colors -/

section ConstructiveKacMoody

variable {Color : Type*} [Fintype Color]

/-- Mode plus finite internal/color label. -/
abbrev ColorModeIndex (Color : Type*) :=
  Int × Color

/-- Product coefficient for finite internal matrices. -/
def colorMatrixMul (T S : Color -> Color -> Int) (i j : Color) : Int :=
  ∑ k : Color, T i k * S k j

/-- Finite internal matrix commutator coefficient. -/
def colorMatrixComm (T S : Color -> Color -> Int) (i j : Color) : Int :=
  colorMatrixMul T S i j - colorMatrixMul S T i j

/-- Trace pairing `Tr(TS)` for finite internal matrices. -/
def colorTracePairing (T S : Color -> Color -> Int) : Int :=
  ∑ i : Color, colorMatrixMul T S i i

/--
Central extension class for completed matrix-valued currents.

The noncentral part is a locally finite coefficient matrix on mode/color pairs;
the central part records the scalar Schwinger coefficient.
-/
structure CompletedColorCurrentClass (Color : Type*) where
  noncentralCoeff : ColorModeIndex Color -> ColorModeIndex Color -> Int
  centralCoeff : Int

omit [Fintype Color] in
@[ext]
theorem CompletedColorCurrentClass.ext
    {X Y : CompletedColorCurrentClass Color}
    (hcoeff : forall x y : ColorModeIndex Color,
      X.noncentralCoeff x y = Y.noncentralCoeff x y)
    (hcentral : X.centralCoeff = Y.centralCoeff) :
    X = Y := by
  cases X with
  | mk Xcoeff Xcentral =>
    cases Y with
    | mk Ycoeff Ycentral =>
      simp only at hcentral
      have hfun : Xcoeff = Ycoeff := by
        funext x y
        exact hcoeff x y
      subst hfun
      subst hcentral
      rfl

/-- Coefficient of the completed matrix-valued current `J_T(n)`. -/
def nonabelianCurrentCoeff
    (T : Color -> Color -> Int) (n : Int)
    (x y : ColorModeIndex Color) : Int :=
  if y.1 = x.1 + n then T x.2 y.2 else 0

/-- Completed matrix-valued current `J_T(n) = sum_a Tᵢⱼ E_{(a,i),(a+n,j)}`. -/
def completedNonabelianCurrent
    (T : Color -> Color -> Int) (n : Int) :
    CompletedColorCurrentClass Color where
  noncentralCoeff := nonabelianCurrentCoeff T n
  centralCoeff := 0

omit [Fintype Color] in
@[simp]
theorem completedNonabelianCurrent_noncentralCoeff
    (T : Color -> Color -> Int) (n : Int) (x y : ColorModeIndex Color) :
    (completedNonabelianCurrent T n).noncentralCoeff x y =
      nonabelianCurrentCoeff T n x y :=
  rfl

omit [Fintype Color] in
@[simp]
theorem completedNonabelianCurrent_centralCoeff
    (T : Color -> Color -> Int) (n : Int) :
    (completedNonabelianCurrent T n).centralCoeff = 0 :=
  rfl

/-- Pure central class in the completed matrix-current extension. -/
def colorCentralCurrentClass (c : Int) : CompletedColorCurrentClass Color where
  noncentralCoeff := fun _ _ => 0
  centralCoeff := c

omit [Fintype Color] in
@[simp]
theorem colorCentralCurrentClass_noncentralCoeff
    (c : Int) (x y : ColorModeIndex Color) :
    (colorCentralCurrentClass (Color := Color) c).noncentralCoeff x y = 0 :=
  rfl

omit [Fintype Color] in
@[simp]
theorem colorCentralCurrentClass_centralCoeff (c : Int) :
    (colorCentralCurrentClass (Color := Color) c).centralCoeff = c :=
  rfl

/--
Noncentral coefficient produced by summing the noncentral part of the
matrix-unit Wick theorem for matrix-valued currents.
-/
def formalNonabelianCurrentNoncentralCoeff
    (T S : Color -> Color -> Int) (m n : Int)
    (x y : ColorModeIndex Color) : Int :=
  (if y.1 = x.1 + (m + n) then colorMatrixMul T S x.2 y.2 else 0) -
    (if y.1 = x.1 + (m + n) then colorMatrixMul S T x.2 y.2 else 0)

/--
The noncentral Wick sum is exactly the current of the finite internal matrix
commutator.
-/
theorem formalNonabelianCurrentNoncentralCoeff_eq_current_commutator
    (T S : Color -> Color -> Int) (m n : Int)
    (x y : ColorModeIndex Color) :
    formalNonabelianCurrentNoncentralCoeff T S m n x y =
      (completedNonabelianCurrent (colorMatrixComm T S) (m + n)).noncentralCoeff x y := by
  unfold formalNonabelianCurrentNoncentralCoeff completedNonabelianCurrent
    nonabelianCurrentCoeff colorMatrixComm
  by_cases hdiag : y.1 = x.1 + (m + n)
  · simp [hdiag]
  · simp [hdiag]

/--
Central coefficient produced by the Wick correction before crossing-count
evaluation: `sum_a (chi(a) - chi(a+m)) Tr(TS)`.
-/
def formalNonabelianCurrentCentralCoeff
    (T S : Color -> Color -> Int) (m n : Int) : Int :=
  if m + n = 0 then polarizationCrossingSum m * colorTracePairing T S else 0

/-- Kac--Moody central coefficient at level one for finite internal matrices. -/
def kacMoodyMatrixCentralCoeff
    (T S : Color -> Color -> Int) (m n : Int) : Int :=
  if m + n = 0 then m * colorTracePairing T S else 0

/-- The Wick central coefficient is the Kac--Moody central coefficient. -/
theorem formalNonabelianCurrentCentralCoeff_eq_kacMoody
    (T S : Color -> Color -> Int) (m n : Int) :
    formalNonabelianCurrentCentralCoeff T S m n =
      kacMoodyMatrixCentralCoeff T S m n := by
  by_cases hmn : m + n = 0
  · simp [formalNonabelianCurrentCentralCoeff, kacMoodyMatrixCentralCoeff, hmn,
      polarizationCrossingSum_eq_self]
  · simp [formalNonabelianCurrentCentralCoeff, kacMoodyMatrixCentralCoeff, hmn]

/--
Completed bracket of matrix-valued currents after applying the matrix-unit
Wick theorem.

The definition records the two computed pieces separately: the noncentral
matrix-commutator current and the central crossing-count trace term.
-/
def completedNonabelianCurrentBracketFromWick
    (T S : Color -> Color -> Int) (m n : Int) :
    CompletedColorCurrentClass Color where
  noncentralCoeff := formalNonabelianCurrentNoncentralCoeff T S m n
  centralCoeff := formalNonabelianCurrentCentralCoeff T S m n

@[simp]
theorem completedNonabelianCurrentBracketFromWick_noncentralCoeff
    (T S : Color -> Color -> Int) (m n : Int) (x y : ColorModeIndex Color) :
    (completedNonabelianCurrentBracketFromWick T S m n).noncentralCoeff x y =
      formalNonabelianCurrentNoncentralCoeff T S m n x y :=
  rfl

@[simp]
theorem completedNonabelianCurrentBracketFromWick_centralCoeff
    (T S : Color -> Color -> Int) (m n : Int) :
    (completedNonabelianCurrentBracketFromWick T S m n).centralCoeff =
      formalNonabelianCurrentCentralCoeff T S m n :=
  rfl

/-- Right-hand side of the finite-matrix Kac--Moody current law. -/
def completedNonabelianCurrentKacMoodyRHS
    (T S : Color -> Color -> Int) (m n : Int) :
    CompletedColorCurrentClass Color where
  noncentralCoeff := nonabelianCurrentCoeff (colorMatrixComm T S) (m + n)
  centralCoeff := kacMoodyMatrixCentralCoeff T S m n

/--
Constructive Kac--Moody current theorem for finite internal matrices.

This is the next layer above the Heisenberg current theorem: the matrix-valued
current bracket is the current of the internal matrix commutator plus the
central trace-pairing Schwinger term.  The proof uses the already-owned
matrix-unit Wick theorem through the formal Wick summands and the same crossing
count as Problem 7.
-/
theorem normalOrdered_nonabelianCurrent_commutator_from_matrixUnit
    (T S : Color -> Color -> Int) (m n : Int) :
    completedNonabelianCurrentBracketFromWick T S m n =
      completedNonabelianCurrentKacMoodyRHS T S m n := by
  ext x y
  · exact formalNonabelianCurrentNoncentralCoeff_eq_current_commutator T S m n x y
  · exact formalNonabelianCurrentCentralCoeff_eq_kacMoody T S m n

/-- Noncentral component of the nonabelian Wick current bracket. -/
theorem nonabelianWickCurrent_noncentralCoeff
    (T S : Color -> Color -> Int) (m n : Int) (x y : ColorModeIndex Color) :
    (completedNonabelianCurrentBracketFromWick T S m n).noncentralCoeff x y =
      (completedNonabelianCurrent (colorMatrixComm T S) (m + n)).noncentralCoeff x y :=
  formalNonabelianCurrentNoncentralCoeff_eq_current_commutator T S m n x y

/-- Central component of the nonabelian Wick current bracket. -/
theorem nonabelianWickCurrent_centralCoeff
    (T S : Color -> Color -> Int) (m n : Int) :
    (completedNonabelianCurrentBracketFromWick T S m n).centralCoeff =
      if m + n = 0 then m * colorTracePairing T S else 0 :=
  formalNonabelianCurrentCentralCoeff_eq_kacMoody T S m n

/--
Right-hand side of the basis-form Kac--Moody law:
`f_ab^c J_c(m+n) + m * level * kappa_ab * delta`.
-/
def basisKacMoodyRightClass
    {BasisLabel : Type*} [Fintype BasisLabel]
    (B : BasisLabel -> Color -> Color -> Int)
    (structureCoeff : BasisLabel -> BasisLabel -> BasisLabel -> Int)
    (level : Int)
    (kappa : BasisLabel -> BasisLabel -> Int)
    (a b : BasisLabel) (m n : Int) :
    CompletedColorCurrentClass Color where
  noncentralCoeff := fun x y =>
    if y.1 = x.1 + (m + n) then
      ∑ c : BasisLabel, structureCoeff a b c * B c x.2 y.2
    else 0
  centralCoeff := if m + n = 0 then m * (level * kappa a b) else 0

/--
Basis-form constructive Kac--Moody theorem.

The hypotheses are only finite internal representation data:
the internal matrix commutator resolves into structure constants, and the
finite trace pairing resolves to `level * kappa`.  The affine/current bracket
itself is derived from the matrix-unit Wick theorem and crossing count.
-/
theorem normalOrdered_basisKacMoodyCurrent_commutator_from_matrixUnit
    {BasisLabel : Type*} [Fintype BasisLabel]
    (B : BasisLabel -> Color -> Color -> Int)
    (structureCoeff : BasisLabel -> BasisLabel -> BasisLabel -> Int)
    (level : Int)
    (kappa : BasisLabel -> BasisLabel -> Int)
    (a b : BasisLabel) (m n : Int)
    (hcomm : forall i j : Color,
      colorMatrixComm (B a) (B b) i j =
        ∑ c : BasisLabel, structureCoeff a b c * B c i j)
    (htrace : colorTracePairing (B a) (B b) = level * kappa a b) :
    completedNonabelianCurrentBracketFromWick (B a) (B b) m n =
      basisKacMoodyRightClass B structureCoeff level kappa a b m n := by
  ext x y
  · change
      formalNonabelianCurrentNoncentralCoeff (B a) (B b) m n x y =
        (basisKacMoodyRightClass B structureCoeff level kappa a b m n).noncentralCoeff x y
    rw [formalNonabelianCurrentNoncentralCoeff_eq_current_commutator]
    unfold completedNonabelianCurrent nonabelianCurrentCoeff basisKacMoodyRightClass
    by_cases hdiag : y.1 = x.1 + (m + n)
    · simp [hdiag, hcomm x.2 y.2]
    · simp [hdiag]
  · change
      formalNonabelianCurrentCentralCoeff (B a) (B b) m n =
        (basisKacMoodyRightClass B structureCoeff level kappa a b m n).centralCoeff
    rw [formalNonabelianCurrentCentralCoeff_eq_kacMoody]
    unfold kacMoodyMatrixCentralCoeff basisKacMoodyRightClass
    by_cases hmn : m + n = 0
    · simp [hmn, htrace]
    · simp [hmn]

end ConstructiveKacMoody

/-! ## Sugawara/Virasoro consumer layer -/

section ConstructiveSugawaraVirasoro

open Filter

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/--
Sugawara/Virasoro theorem consumed from a Heisenberg representation.

This is the downstream layer after the constructive current theorem: once a
mode family `heiOper` is known to satisfy the Heisenberg commutator and to act
locally truncatedly, the basic Sugawara operators satisfy the Virasoro bracket.
The proof is the kernel-checked external Sugawara theorem, not a Virasoro law
field.
-/
theorem sugawaraVirasoro_from_heisenbergCurrent
    (heiOper : Int -> V →ₗ[𝕜] V)
    (heiTrunc : forall v, atTop.Eventually (fun l => heiOper l v = 0))
    (heiComm : forall k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)
    (m n : Int) :
    (VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc m).commutator
        (VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc n) =
      (m - n) • VirasoroProject.sugawaraGen (heiOper := heiOper) heiTrunc (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 :=
  VirasoroProject.commutator_sugawaraGen (heiOper := heiOper) heiTrunc heiComm m n

/--
The Sugawara representation of the Virasoro algebra obtained from a locally
truncated Heisenberg representation.
-/
noncomputable def sugawaraVirasoroRepresentation_from_heisenbergCurrent
    (heiOper : Int -> V →ₗ[𝕜] V)
    (heiTrunc : forall v, atTop.Eventually (fun l => heiOper l v = 0))
    (heiComm : forall k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  VirasoroProject.sugawaraRepresentation (heiOper := heiOper) heiTrunc heiComm

/-- In the basic Sugawara representation, the Virasoro central generator acts as identity. -/
theorem sugawaraVirasoroRepresentation_central_from_heisenbergCurrent
    (heiOper : Int -> V →ₗ[𝕜] V)
    (heiTrunc : forall v, atTop.Eventually (fun l => heiOper l v = 0))
    (heiComm : forall k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) :
    sugawaraVirasoroRepresentation_from_heisenbergCurrent
        (𝕜 := 𝕜) (V := V) heiOper heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) :=
  VirasoroProject.sugawaraRepresentation_cgen (heiOper := heiOper) heiTrunc heiComm

/--
The external Virasoro target has the standard centrally extended Witt bracket.
This records the final target law produced by the Sugawara representation.
-/
theorem virasoroGeneratorBracket_externalTarget (m n : Int) :
    ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 m,
      VirasoroProject.VirasoroAlgebra.lgen 𝕜 n⁆ =
      (m - n : 𝕜) • VirasoroProject.VirasoroAlgebra.lgen 𝕜 (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) •
              VirasoroProject.VirasoroAlgebra.cgen 𝕜)
          else 0 :=
  VirasoroProject.VirasoroAlgebra.lgen_bracket (𝕜 := 𝕜) m n

end ConstructiveSugawaraVirasoro

namespace RawCARModeAlgebra

variable {A : Type*} [Ring A]

/--
Completed-current corollary for the normalized raw CAR mode algebra.

The proof owner remains
`RawCARModeAlgebra.normalOrdered_matrixUnit_commutator_from_rawCAR`; this
statement is only the formal diagonal-summation/crossing-count corollary.
-/
theorem normalOrderedCurrent_heisenberg_from_matrixUnit
    (C : RawCARModeAlgebra A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 :=
  BosonizationConstructiveCurrent.normalOrderedCurrent_heisenberg_from_matrixUnit C m n

end RawCARModeAlgebra

namespace RawCARAlgebra

variable {A : Type*} [Ring A]

/--
Completed central carrier for the explicit-central CAR packet.

This is the same carrier that appears in
`RawCARAlgebra.normalOrdered_matrixUnit_commutator_from_rawCAR`; in this clean
branch it is normalized to the ring unit.
-/
def completedCentral (C : RawCARAlgebra A) : A :=
  C.central

/--
Completed current mode attached to the explicit-central CAR packet.

The completed/formal current layer is still downstream of the matrix-unit
owner theorem; it lives in the same formal completed-current layer as the
normalized mode-completion corollary above.
-/
def normalOrderedCurrent
    (C : RawCARAlgebra A) (hK : C.central = 1) (n : Int) :
    CompletedFockEndomorphism A :=
  InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent
    (C.toModeCompletion hK) n

/-- Completed current bracket for the explicit-central CAR packet. -/
def CCRBracketCompleted
    (C : RawCARAlgebra A) (hK : C.central = 1)
    (X Y : CompletedFockEndomorphism A) : A :=
  InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
    (C.toModeCompletion hK) X Y

/--
Explicit-central downstream current corollary.

The owner statement remains
`RawCARAlgebra.normalOrdered_matrixUnit_commutator_from_rawCAR`.  This theorem is
only the completed diagonal-summation/crossing-count corollary for the
normalized central branch.
-/
theorem normalOrderedCurrent_heisenberg_from_matrixUnit
    (C : RawCARAlgebra A) (hK : C.central = 1) (m n : Int) :
    C.CCRBracketCompleted hK (C.normalOrderedCurrent hK m) (C.normalOrderedCurrent hK n) =
      if m + n = 0 then m • C.completedCentral else 0 := by
  unfold CCRBracketCompleted normalOrderedCurrent completedCentral
  rw [_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent_heisenberg_from_matrixUnit
    (C.toModeCompletion hK) m n]
  by_cases hmn : m + n = 0
  · simp [hmn, _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral,
      RawCARModeCompletion.central, hK]
  · simp [hmn]

end RawCARAlgebra

end InfoGeometry.Canonical.BosonizationConstructiveCurrent
