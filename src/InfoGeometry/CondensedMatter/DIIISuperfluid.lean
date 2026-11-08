/-
InfoGeometry/CondensedMatter/DIIISuperfluid.lean

Abstract DIII topological superfluid symmetry datum.

Class DIII has:

  Theta^2 = -1    time reversal / Kramers symmetry
  Xi^2 = +1       particle-hole / Majorana symmetry
  chi^2 = +1      phase-corrected chiral grading
  chi H chi = -H  chiral symmetry of the BdG Hamiltonian

This module records the condensed-matter interpretation of the
operator-algebraic DIII branch.  Concrete 3He-B, lattice BdG, or continuum
Dirac/Majorana models can instantiate the datum later.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.DIIISuperfluid
import InfoGeometry.OperatorAlgebra.ModularChiralMirror
import InfoGeometry.OperatorAlgebra.CPTSymmetryBranch
import InfoGeometry.OperatorAlgebra.JUnitaryTopologicalCharge

noncomputable section

namespace InfoGeometry.CondensedMatter.DIIISuperfluid

/-! ## 1. Condensed-matter DIII BdG datum -/

/--
Abstract DIII superfluid symmetry datum in a real operator algebra.

`Hbdg` is the BdG Hamiltonian.

`Theta` is time reversal, with `Theta² = -1`.

`Xi` is particle-hole / Majorana conjugation, with `Xi² = +1`.

`chi` is the phase-corrected chiral grading, with `chi² = +1`.
-/
structure DIIISuperfluidDatum
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- BdG Hamiltonian. -/
  Hbdg : Op

  /-- Time-reversal operator, encoded in the real doubled algebra. -/
  Theta : Op

  /-- Particle-hole / Majorana operator. -/
  Xi : Op

  /-- Phase-corrected chiral grading. -/
  chi : Op

  /-- DIII time-reversal sign: `Theta² = -1`. -/
  Theta_square :
    Theta * Theta = -1

  /-- DIII particle-hole sign: `Xi² = +1`. -/
  Xi_square :
    Xi * Xi = 1

  /-- Chiral grading law: `chi² = +1`. -/
  chi_square :
    chi * chi = 1

  /--
  Time reversal symmetry.

  Since `Theta² = -1`, one has `Theta⁻¹ = -Theta`; this equation is the
  inverse-free form of `Theta H Theta⁻¹ = H`.
  -/
  time_reversal_symmetry :
    Theta * Hbdg * Theta = -Hbdg

  /--
  Particle-hole symmetry.

  Since `Xi² = 1`, this is the inverse-free form of `Xi H Xi⁻¹ = -H`.
  -/
  particle_hole_symmetry :
    Xi * Hbdg * Xi = -Hbdg

  /--
  Chiral symmetry.

  Since `chi² = 1`, this is equivalent to anticommutation with `Hbdg`.
  -/
  chiral_symmetry :
    chi * Hbdg * chi = -Hbdg

  /--
  Phase-corrected product relation.

  In the real doubled formalism, the chiral grading is supplied as the actual
  product of the two symmetry generators.
  -/
  chiral_is_phase_corrected_product :
    chi = Theta * Xi

namespace DIIISuperfluidDatum

variable
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D : DIIISuperfluidDatum Op)

/--
The chiral grading anticommutes with the BdG Hamiltonian:

`chi H = - H chi`.
-/
theorem chi_anticommutes_H :
    D.chi * D.Hbdg = -(D.Hbdg * D.chi) := by
  calc
    D.chi * D.Hbdg
        = D.chi * D.Hbdg * 1 := by
            rw [mul_one]
    _ = D.chi * D.Hbdg * (D.chi * D.chi) := by
            rw [D.chi_square]
    _ = (D.chi * D.Hbdg * D.chi) * D.chi := by
            noncomm_ring
    _ = (-D.Hbdg) * D.chi := by
            rw [D.chiral_symmetry]
    _ = -(D.Hbdg * D.chi) := by
            rw [neg_mul]

/--
The off-diagonal/chiral BdG relation.

This is the algebraic statement behind the left/right sector splitting of a
chiral Hamiltonian.
-/
def ChiralOffDiagonal : Prop :=
  D.chi * D.Hbdg = -(D.Hbdg * D.chi)

/-- The DIII datum supplies the chiral off-diagonal relation. -/
theorem chiral_offDiagonal :
    D.ChiralOffDiagonal :=
  D.chi_anticommutes_H

/-- The chiral grading is explicitly the product of time reversal and particle-hole symmetry. -/
theorem chi_eq_phase_corrected_product :
    D.chi = D.Theta * D.Xi :=
  D.chiral_is_phase_corrected_product

/--
The phase-corrected chiral product is a genuine involution:
its square is the identity.
-/
theorem phase_corrected_product_sq :
    (D.Theta * D.Xi) * (D.Theta * D.Xi) = 1 := by
  simpa [D.chi_eq_phase_corrected_product] using D.chi_square

/--
The phase-corrected product inherits the chiral symmetry relation.
-/
theorem phase_corrected_product_chiral_symmetry :
    (D.Theta * D.Xi) * D.Hbdg * (D.Theta * D.Xi) = -D.Hbdg := by
  simpa [D.chi_eq_phase_corrected_product] using D.chiral_symmetry

/--
The phase-corrected product anticommutes with the BdG Hamiltonian.
-/
theorem phase_corrected_product_anticommutes_H :
    (D.Theta * D.Xi) * D.Hbdg = -(D.Hbdg * (D.Theta * D.Xi)) := by
  simpa [D.chi_eq_phase_corrected_product] using D.chi_anticommutes_H

end DIIISuperfluidDatum

/-! ## 2. Topological invariant sockets -/

/--
Coarse labels for the standard DIII topological-invariant regimes.

This is deliberately only a label.  Concrete models should provide their own
winding, parity, or interacting classification backend.
-/
inductive DIIITopologicalRegime where
  /-- One-dimensional endpoint/Kramers-Majorana parity regime. -/
  | oneDimensionalZ2
  /-- Two-dimensional helical Majorana edge parity regime. -/
  | twoDimensionalZ2
  /-- Three-dimensional free-fermion integer winding regime. -/
  | threeDimensionalFreeZ
  /-- Three-dimensional interacting reduction, often represented as `Z16`. -/
  | threeDimensionalInteractingZ16
deriving DecidableEq, Repr

/--
A model-specific topological readout attached to a DIII datum.

The invariant value is intentionally abstract: the same symmetry class supports
different classification groups depending on dimension and interaction regime.
-/
def DIIITopologicalReadout
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D : DIIISuperfluidDatum Op) :=
  DIIITopologicalRegime × Σ I : Type*, I

namespace DIIITopologicalReadout

variable
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    {D : DIIISuperfluidDatum Op}

/-- Classification regime carried by a model-specific DIII readout. -/
def regime (R : DIIITopologicalReadout D) : DIIITopologicalRegime :=
  R.1

/-- The model-specific invariant carrier, such as `ℤ`, `ZMod 2`, or `ZMod 16`. -/
def invariantType (R : DIIITopologicalReadout D) : Type* :=
  R.2.1

/-- The chosen invariant value in the carrier selected by the model. -/
def invariant (R : DIIITopologicalReadout D) : R.invariantType :=
  R.2.2

/-- Construct a DIII readout from its regime and invariant value. -/
def mk (regime : DIIITopologicalRegime)
    {I : Type*} (invariant : I) : DIIITopologicalReadout D :=
  (regime, ⟨I, invariant⟩)

@[simp] theorem regime_mk (regime : DIIITopologicalRegime)
    {I : Type*} (invariant : I) :
    (mk (D := D) regime invariant).regime = regime := rfl

@[simp] theorem invariantType_mk (regime : DIIITopologicalRegime)
    {I : Type*} (invariant : I) :
    (mk (D := D) regime invariant).invariantType = I := rfl

@[simp] theorem invariant_mk (regime : DIIITopologicalRegime)
    {I : Type*} (invariant : I) :
    (mk (D := D) regime invariant).invariant = invariant := rfl

end DIIITopologicalReadout

/-! ## 3. Owner target -/

/--
Owner target for a concrete DIII superfluid model.

Concrete instances include continuum 3He-B, lattice BdG models, or
Dirac/Majorana effective surface theories.

This is the actual datum type, not a wrapper existence claim.
-/
abbrev DIIISuperfluidOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] : Type _ :=
  DIIISuperfluidDatum Op

end InfoGeometry.CondensedMatter.DIIISuperfluid
