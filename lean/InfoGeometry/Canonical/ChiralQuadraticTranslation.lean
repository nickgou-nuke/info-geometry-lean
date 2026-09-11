import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SupergradedCuntzBdG

/-!
  A theorem-safe algebraic packaging of the chiral-supercharge pattern.

  The data record is deliberately supplied: this file does not assert the
  existence of a SUSY representation or of an analytic translation group.
  It records only the quadratic identities which turn two odd generators into
  an even symmetric and an even relative generator.
-/

namespace InfoGeometry.Canonical.ChiralQuadraticTranslation

variable {A : Type*} [Ring A]

/-- Two chiral charges together with their prescribed quadratic even parts. -/
structure Data where
  Qplus : A
  Qminus : A
  Pplus : A
  Pminus : A
  qplus_sq : Qplus * Qplus = (2 : A) * Pplus
  qminus_sq : Qminus * Qminus = (2 : A) * Pminus
  cross_anticommutator_zero :
    Qplus * Qminus + Qminus * Qplus = 0

namespace Data

variable (d : Data (A := A))

/-- The symmetric (Hamiltonian-like) even combination. -/
def symmetric : A := d.Pplus + d.Pminus

/-- The relative (translation-like) even combination. -/
def relative : A := d.Pplus - d.Pminus

theorem cross_anticommutator_zero' :
    d.Qplus * d.Qminus + d.Qminus * d.Qplus = 0 :=
  d.cross_anticommutator_zero

/-- The symmetric combination is the half-sum of the two charge squares,
    expressed without dividing by `2`. -/
theorem two_mul_symmetric :
    (2 : A) * d.symmetric =
      d.Qplus * d.Qplus + d.Qminus * d.Qminus := by
  rw [d.qplus_sq, d.qminus_sq]
  dsimp [symmetric]
  noncomm_ring

/-- The relative combination is the half-difference of the two charge
    squares, expressed without dividing by `2`. -/
theorem two_mul_relative :
    (2 : A) * d.relative =
      d.Qplus * d.Qplus - d.Qminus * d.Qminus := by
  rw [d.qplus_sq, d.qminus_sq]
  dsimp [relative]
  noncomm_ring

end Data

/-! A nilpotent chiral pair whose mixed products are the two even sectors.
    This is the algebraic shape used by the finite two-channel Cuntz owner. -/
section NilpotentPairs

variable {B : Type*} [Semiring B]

structure NilpotentPairData where
  Qplus : B
  Qminus : B
  Pplus : B
  Pminus : B
  qplus_sq : Qplus * Qplus = 0
  qminus_sq : Qminus * Qminus = 0
  qplus_mul_qminus : Qplus * Qminus = Pplus
  qminus_mul_qplus : Qminus * Qplus = Pminus

namespace NilpotentPairData

variable (d : NilpotentPairData (B := B))

/-- The even symmetric product of a nilpotent chiral pair. -/
def symmetric : B := d.Qplus * d.Qminus + d.Qminus * d.Qplus

theorem symmetric_eq_sector_sum :
    d.symmetric = d.Pplus + d.Pminus := by
  dsimp [symmetric]
  rw [d.qplus_mul_qminus, d.qminus_mul_qplus]

theorem symmetric_eq_one_of_partition (h : d.Pplus + d.Pminus = 1) :
    d.symmetric = 1 := by
  rw [d.symmetric_eq_sector_sum, h]

end NilpotentPairData

end NilpotentPairs

/-! ## Concrete finite Cuntz instance

The following is only an adapter to the already proved finite Cuntz owner; it
does not promote the finite quotient to a continuum or a C*-completion. -/

open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Topology.AlgebraicCuntzQuotient

noncomputable def finiteCuntzPairData :
    NilpotentPairData (B := CuntzAlg ℂ (Fin 2)) where
  Qplus := cuntzSuperchargeR
  Qminus := cuntzSuperchargeL
  Pplus := particleProj
  Pminus := holeProj
  qplus_sq := cuntzSuperchargeR_sq
  qminus_sq := cuntzSuperchargeL_sq
  qplus_mul_qminus := by
    change (S (R := ℂ) 0 * T (R := ℂ) 1) *
      (S (R := ℂ) 1 * T (R := ℂ) 0) = particleProj
    rw [mul_assoc, ← mul_assoc (T (R := ℂ) 1) (S (R := ℂ) 1)
      (T (R := ℂ) 0), T_mul_S]
    simp [particleProj, rangeProj]
  qminus_mul_qplus := by
    change (S (R := ℂ) 1 * T (R := ℂ) 0) *
      (S (R := ℂ) 0 * T (R := ℂ) 1) = holeProj
    rw [mul_assoc, ← mul_assoc (T (R := ℂ) 0) (S (R := ℂ) 0)
      (T (R := ℂ) 1), T_mul_S]
    simp [holeProj, rangeProj]

theorem finiteCuntzPairData_symmetric_eq_one :
    (finiteCuntzPairData).symmetric = 1 := by
  apply NilpotentPairData.symmetric_eq_one_of_partition
  exact particle_hole_partition

end InfoGeometry.Canonical.ChiralQuadraticTranslation
