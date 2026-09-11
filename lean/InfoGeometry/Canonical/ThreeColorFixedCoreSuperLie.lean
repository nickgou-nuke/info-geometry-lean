import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Canonical.ChiralConeOperatorAlgebra

/-!
# Fixed-colour matrix core and its graded bracket

The native three-colour Zorn carrier remains non-associative.  This file
therefore uses the associative matrix realisation `M₂(A)` as the fixed-colour
core.  The diagonal matrix units are even and the two off-diagonal matrix
units are odd.  No Lie or super-Lie instance is installed on the native Zorn
carrier.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.AssociativeSuperBracket
open InfoGeometry.Canonical.SuperAnomaly
open InfoGeometry.Physics

variable {A : Type*} [Ring A] [Algebra ℝ A]

abbrev FixedColourCore (A : Type*) := BdGBlock A

def coreNPlus : FixedColourCore A := !![1, 0; 0, 0]
def coreNMinus : FixedColourCore A := !![0, 0; 0, 1]
def coreSigmaPlus : FixedColourCore A := !![0, 1; 0, 0]
def coreSigmaMinus : FixedColourCore A := !![0, 0; 1, 0]

omit [Algebra ℝ A] in
@[simp] theorem coreSigmaPlus_mul_coreSigmaPlus :
    coreSigmaPlus (A := A) * coreSigmaPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreSigmaPlus, Matrix.mul_apply, Fin.sum_univ_two]

omit [Algebra ℝ A] in
@[simp] theorem coreSigmaMinus_mul_coreSigmaMinus :
    coreSigmaMinus (A := A) * coreSigmaMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreSigmaMinus, Matrix.mul_apply, Fin.sum_univ_two]

omit [Algebra ℝ A] in
@[simp] theorem coreSigmaPlus_mul_coreSigmaMinus :
    coreSigmaPlus (A := A) * coreSigmaMinus = coreNPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreSigmaPlus, coreSigmaMinus, coreNPlus,
      Matrix.mul_apply, Fin.sum_univ_two]

omit [Algebra ℝ A] in
@[simp] theorem coreSigmaMinus_mul_coreSigmaPlus :
    coreSigmaMinus (A := A) * coreSigmaPlus = coreNMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coreSigmaPlus, coreSigmaMinus, coreNMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem associative_superBracket_graded_jacobi
    (p q r : SuperParity) (x y z : FixedColourCore A) :
    paritySign p r • superBracket p (AssociativeSuperBracket.parityAdd q r) x
        (superBracket q r y z) +
      paritySign q p • superBracket q (AssociativeSuperBracket.parityAdd r p) y
        (superBracket r p z x) +
      paritySign r q • superBracket r (AssociativeSuperBracket.parityAdd p q) z
        (superBracket p q x y) = 0 := by
  exact superBracket_graded_jacobi p q r x y z

theorem core_sigmaPlus_odd_odd_bracket_zero :
    superBracket SuperParity.odd SuperParity.odd
        (coreSigmaPlus (A := A)) coreSigmaPlus = 0 := by
  simp [superBracket]

theorem core_sigmaMinus_odd_odd_bracket_zero :
    superBracket SuperParity.odd SuperParity.odd
        (coreSigmaMinus (A := A)) coreSigmaMinus = 0 := by
  simp [superBracket]

theorem core_sigmaPlus_sigmaMinus_odd_odd_bracket :
    superBracket SuperParity.odd SuperParity.odd
        (coreSigmaPlus (A := A)) coreSigmaMinus =
      coreNPlus + coreNMinus := by
  simp [superBracket, paritySign, sub_eq_add_neg]

def similarity (P PInv X : FixedColourCore A) : FixedColourCore A :=
  P * X * PInv

theorem similarity_map_superBracket
    (P PInv X Y : FixedColourCore A)
    (_hLeft : P * PInv = 1) (hRight : PInv * P = 1)
    (p q : SuperParity) :
    similarity P PInv (superBracket p q X Y) =
    superBracket p q (similarity P PInv X) (similarity P PInv Y) := by
  have hmul (U V : FixedColourCore A) :
      similarity P PInv (U * V) =
        similarity P PInv U * similarity P PInv V := by
    unfold similarity
    calc
      (P * (U * V)) * PInv = P * U * (V * PInv) := by
        noncomm_ring
      _ = P * U * ((PInv * P) * (V * PInv)) := by
        rw [hRight, one_mul]
      _ = (P * U * PInv) * (P * V * PInv) := by
        noncomm_ring
  have hsub (U V : FixedColourCore A) :
      similarity P PInv (U - V) =
        similarity P PInv U - similarity P PInv V := by
    unfold similarity
    noncomm_ring
  have hadd (U V : FixedColourCore A) :
      similarity P PInv (U + V) =
        similarity P PInv U + similarity P PInv V := by
    unfold similarity
    noncomm_ring
  cases p <;> cases q
  · simp [superBracket, paritySign]
    rw [hsub, hmul, hmul]
  · simp [superBracket, paritySign]
    rw [hsub, hmul, hmul]
  · simp [superBracket, paritySign]
    rw [hsub, hmul, hmul]
  · simp [superBracket, paritySign]
    rw [hadd, hmul, hmul]

end InfoGeometry.Canonical
