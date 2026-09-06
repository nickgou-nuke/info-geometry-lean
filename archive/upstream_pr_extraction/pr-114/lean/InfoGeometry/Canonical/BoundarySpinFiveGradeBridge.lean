import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge

/-!
# Boundary spin / five-grade correspondence contract

The repository already proves the three ingredients separately: the null
split-octonion annihilator, the `Cl(5,5)` five-grade routing, and finite braid
relations on Majorana/anyon carriers.  What is *not* proved is a concrete map
identifying these carriers.  This owner records that remaining obligation
without introducing a fabricated representation.

The structure below is data for such a correspondence.  All downstream
lemmas are genuine consequences of the supplied map and its explicitly stated
properties; no existence theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundarySpinFiveGradeBridge

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge

variable {X : Imaginary}

local notation "NullBoundary" => Annihilator X

/-! ## The already closed source and target readouts -/

theorem nullBoundary_finrank_eq_three
    (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0) :
    Module.finrank ℝ NullBoundary = 3 := by
  exact annihilator_finrank_eq_three hX0 hXnull

theorem chiral_plus_grade_one (i : Fin 3) :
    chiralPlus55 i ∈ cl55GradeSubmodule 1 := by
  exact chiralPlus55_mem_grade_one i

theorem chiral_minus_grade_neg_one (i : Fin 3) :
    chiralMinus55 i ∈ cl55GradeSubmodule (-1) := by
  exact chiralMinus55_mem_grade_neg_one i

/-- The already-constructed null-boundary incidence certificate.  This is a
composition of the canonical carrier/projective owner; it does not identify
the boundary fibre with a five-grade Majorana space. -/
theorem null_boundary_incidence_certificate
    {X : Imaginary} (hX0 : X ≠ 0) (hXnull : X ∈ NormLevel 0)
    (Y : Annihilator X) :
    annihilatorBoundaryIncidence
        (X := X) (annihilatorBoundaryMap Y) ∧
      ProjectiveAffineConformalClosure55.Q55 (annihilatorBoundaryMap Y) = 0 := by
  exact ⟨annihilatorBoundaryMap_incidence Y,
    annihilatorBoundaryMap_null hX0 hXnull Y⟩

/-! ## The missing finite correspondence as an explicit contract -/

structure Correspondence (B : Type*) where
  /-- The proposed map from the null annihilator to the five-grade carrier. -/
  phi : NullBoundary → Cl55
  /-- The map is faithful on the selected boundary carrier. -/
  phi_injective : Function.Injective phi
  /-- Source-side chiral grading supplied by the proposed realization. -/
  grade : NullBoundary → ℤ
  /-- Grade readout after soldering into `Cl(5,5)`. -/
  phi_grade : ∀ v, phi v ∈ cl55GradeSubmodule (grade v)
  /-- Candidate spinorial boundary involution. -/
  J : Cl55 → Cl55
  /-- Candidate boundary-zero-mode operator. -/
  Q : Cl55 → Cl55
  /-- The grading involution acts with the declared sign on the image. -/
  J_eigen : ∀ v, J (phi v) = (grade v : ℝ) • phi v
  /-- The boundary operator kills every transported boundary mode. -/
  Q_annihilates : ∀ v, Q (phi v) = 0
  /-- Source braid action. -/
  BZ : B → NullBoundary → NullBoundary
  /-- Target braid action. -/
  BM : B → Cl55 → Cl55
  /-- The missing braid intertwining law. -/
  braid_covariance : ∀ b v, phi (BZ b v) = BM b (phi v)

theorem phi_mem_grade (C : Correspondence (X := X) B) (v : NullBoundary) :
    C.phi v ∈ cl55GradeSubmodule (C.grade v) := by
  exact C.phi_grade v

theorem phi_J_eigen (C : Correspondence (X := X) B) (v : NullBoundary) :
    C.J (C.phi v) = (C.grade v : ℝ) • C.phi v := by
  exact C.J_eigen v

theorem phi_Q_zero (C : Correspondence (X := X) B) (v : NullBoundary) :
    C.Q (C.phi v) = 0 := by
  exact C.Q_annihilates v

theorem phi_braid_covariant (C : Correspondence (X := X) B) (b : B)
    (v : NullBoundary) :
    C.phi (C.BZ b v) = C.BM b (C.phi v) := by
  exact C.braid_covariance b v

theorem phi_injective_on_nullBoundary (C : Correspondence (X := X) B) :
    Function.Injective C.phi := by
  exact C.phi_injective

end InfoGeometry.Canonical.BoundarySpinFiveGradeBridge
