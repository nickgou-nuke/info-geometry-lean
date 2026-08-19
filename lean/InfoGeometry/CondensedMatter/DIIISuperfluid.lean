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

def DIIISuperfluidLaws
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D : DIIISuperfluidDatum Op) : Prop :=
  D.Theta * D.Theta = -1 ∧
  D.Xi * D.Xi = 1 ∧
  D.chi * D.chi = 1 ∧
  D.Theta * D.Hbdg * D.Theta = -D.Hbdg ∧
  D.Xi * D.Hbdg * D.Xi = -D.Hbdg ∧
  D.chi * D.Hbdg * D.chi = -D.Hbdg ∧
  D.chi = D.Theta * D.Xi

namespace DIIISuperfluidDatum

variable
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (D : DIIISuperfluidDatum Op)
    (hD : DIIISuperfluidLaws D)

/--
The chiral grading anticommutes with the BdG Hamiltonian:

`chi H = - H chi`.
-/
theorem chi_anticommutes_H (hD : DIIISuperfluidLaws D) :
    D.chi * D.Hbdg = -(D.Hbdg * D.chi) := by
  calc
    D.chi * D.Hbdg
        = D.chi * D.Hbdg * 1 := by
            rw [mul_one]
    _ = D.chi * D.Hbdg * (D.chi * D.chi) := by
            rw [hD.2.2.1]
    _ = (D.chi * D.Hbdg * D.chi) * D.chi := by
            noncomm_ring
    _ = (-D.Hbdg) * D.chi := by
            rw [hD.2.2.2.2.2.1]
    _ = -(D.Hbdg * D.chi) := by
            rw [neg_mul]

theorem theta_commutes_H (hD : DIIISuperfluidLaws D) :
    D.Theta * D.Hbdg = D.Hbdg * D.Theta := by
  calc
    D.Theta * D.Hbdg = D.Theta * D.Hbdg * 1 := by rw [mul_one]
    _ = D.Theta * D.Hbdg * (-(D.Theta * D.Theta)) := by
      rw [hD.1]
      simp
    _ = -(D.Theta * D.Hbdg * D.Theta) * D.Theta := by
      noncomm_ring
    _ = -((-D.Hbdg) * D.Theta) := by
      calc
        -(D.Theta * D.Hbdg * D.Theta) * D.Theta =
            -(-D.Hbdg) * D.Theta := by rw [hD.2.2.2.1]
        _ = -((-D.Hbdg) * D.Theta) :=
          neg_mul (-D.Hbdg) D.Theta
    _ = D.Hbdg * D.Theta := by simp

theorem xi_anticommutes_H (hD : DIIISuperfluidLaws D) :
    D.Xi * D.Hbdg = -(D.Hbdg * D.Xi) := by
  calc
    D.Xi * D.Hbdg = D.Xi * D.Hbdg * 1 := by rw [mul_one]
    _ = D.Xi * D.Hbdg * (D.Xi * D.Xi) := by rw [hD.2.1]
    _ = (D.Xi * D.Hbdg * D.Xi) * D.Xi := by noncomm_ring
    _ = (-D.Hbdg) * D.Xi := by rw [hD.2.2.2.2.1]
    _ = -(D.Hbdg * D.Xi) := by rw [neg_mul]

theorem time_reversal_symmetry_iff_theta_commutes_H (hD : DIIISuperfluidLaws D) :
    D.Theta * D.Hbdg * D.Theta = -D.Hbdg ↔
      D.Theta * D.Hbdg = D.Hbdg * D.Theta := by
  constructor
  · intro h
    exact D.theta_commutes_H hD
  · intro h
    calc
      D.Theta * D.Hbdg * D.Theta =
          D.Hbdg * D.Theta * D.Theta := by rw [h]
      _ = D.Hbdg * (-1) := by rw [mul_assoc, hD.1]
      _ = -D.Hbdg := by simp

theorem particle_hole_symmetry_iff_xi_anticommutes_H (hD : DIIISuperfluidLaws D) :
    D.Xi * D.Hbdg * D.Xi = -D.Hbdg ↔
      D.Xi * D.Hbdg = -(D.Hbdg * D.Xi) := by
  constructor
  · intro h
    exact D.xi_anticommutes_H hD
  · intro h
    calc
      D.Xi * D.Hbdg * D.Xi =
          (-(D.Hbdg * D.Xi)) * D.Xi := by rw [h]
      _ = -(D.Hbdg * (D.Xi * D.Xi)) := by noncomm_ring
      _ = -D.Hbdg := by rw [hD.2.1]; simp

/---
The off-diagonal/chiral BdG relation.

This is the algebraic statement behind the left/right sector splitting of a
chiral Hamiltonian.
-/
def ChiralOffDiagonal : Prop :=
  D.chi * D.Hbdg = -(D.Hbdg * D.chi)

/-- The DIII datum supplies the chiral off-diagonal relation. -/
theorem chiral_offDiagonal (hD : DIIISuperfluidLaws D) :
    D.ChiralOffDiagonal :=
  D.chi_anticommutes_H hD

theorem chiral_symmetry_iff_anticommutes_H (hD : DIIISuperfluidLaws D) :
    D.chi * D.Hbdg * D.chi = -D.Hbdg ↔
      D.chi * D.Hbdg = -(D.Hbdg * D.chi) := by
  constructor
  · intro h
    exact D.chi_anticommutes_H hD
  · intro h
    calc
      D.chi * D.Hbdg * D.chi = (-(D.Hbdg * D.chi)) * D.chi := by rw [h]
      _ = -(D.Hbdg * (D.chi * D.chi)) := by noncomm_ring
      _ = -D.Hbdg := by rw [hD.2.2.1]; simp

/-- The chiral grading is explicitly the product of time reversal and particle-hole symmetry. -/
theorem chi_eq_phase_corrected_product (hD : DIIISuperfluidLaws D) :
    D.chi = D.Theta * D.Xi :=
  hD.2.2.2.2.2.2

/--
The phase-corrected chiral product is a genuine involution:
its square is the identity.
-/
theorem phase_corrected_product_sq (hD : DIIISuperfluidLaws D) :
    (D.Theta * D.Xi) * (D.Theta * D.Xi) = 1 := by
  calc
    (D.Theta * D.Xi) * (D.Theta * D.Xi) = D.chi * D.chi := by
      rw [D.chi_eq_phase_corrected_product hD]
    _ = 1 := hD.2.2.1

theorem phase_corrected_product_left_mul_injective (hD : DIIISuperfluidLaws D) :
    Function.Injective (fun x : Op => (D.Theta * D.Xi) * x) := by
  intro x y hxy
  have h := congrArg (fun z : Op => (D.Theta * D.Xi) * z) hxy
  change (D.Theta * D.Xi) * ((D.Theta * D.Xi) * x) =
    (D.Theta * D.Xi) * ((D.Theta * D.Xi) * y) at h
  calc
    x = 1 * x := by rw [one_mul]
    _ = ((D.Theta * D.Xi) * (D.Theta * D.Xi)) * x := by
      rw [D.phase_corrected_product_sq hD]
    _ = (D.Theta * D.Xi) * ((D.Theta * D.Xi) * x) := by
      noncomm_ring
    _ = (D.Theta * D.Xi) * ((D.Theta * D.Xi) * y) := h
    _ = ((D.Theta * D.Xi) * (D.Theta * D.Xi)) * y := by
      noncomm_ring
    _ = 1 * y := by rw [D.phase_corrected_product_sq hD]
    _ = y := by rw [one_mul]

theorem phase_corrected_product_right_mul_injective (hD : DIIISuperfluidLaws D) :
    Function.Injective (fun x : Op => x * (D.Theta * D.Xi)) := by
  intro x y hxy
  have h := congrArg (fun z : Op => z * (D.Theta * D.Xi)) hxy
  change (x * (D.Theta * D.Xi)) * (D.Theta * D.Xi) =
    (y * (D.Theta * D.Xi)) * (D.Theta * D.Xi) at h
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * ((D.Theta * D.Xi) * (D.Theta * D.Xi)) := by
      rw [D.phase_corrected_product_sq hD]
    _ = (x * (D.Theta * D.Xi)) * (D.Theta * D.Xi) := by
      noncomm_ring
    _ = (y * (D.Theta * D.Xi)) * (D.Theta * D.Xi) := h
    _ = y * ((D.Theta * D.Xi) * (D.Theta * D.Xi)) := by
      noncomm_ring
    _ = y * 1 := by rw [D.phase_corrected_product_sq hD]
    _ = y := by rw [mul_one]

/--
The phase-corrected product inherits the chiral symmetry relation.
-/
theorem phase_corrected_product_chiral_symmetry (hD : DIIISuperfluidLaws D) :
    (D.Theta * D.Xi) * D.Hbdg * (D.Theta * D.Xi) = -D.Hbdg := by
  calc
    (D.Theta * D.Xi) * D.Hbdg * (D.Theta * D.Xi) =
        D.chi * D.Hbdg * D.chi := by
      rw [D.chi_eq_phase_corrected_product hD]
    _ = -D.Hbdg := hD.2.2.2.2.2.1

/--
The phase-corrected product anticommutes with the BdG Hamiltonian.
-/
theorem phase_corrected_product_anticommutes_H (hD : DIIISuperfluidLaws D) :
    (D.Theta * D.Xi) * D.Hbdg = -(D.Hbdg * (D.Theta * D.Xi)) := by
  calc
    (D.Theta * D.Xi) * D.Hbdg = D.chi * D.Hbdg := by
      rw [D.chi_eq_phase_corrected_product hD]
    _ = -(D.Hbdg * D.chi) := D.chi_anticommutes_H hD
    _ = -(D.Hbdg * (D.Theta * D.Xi)) := by
      rw [D.chi_eq_phase_corrected_product hD]

theorem time_reversal_commutes_H (hD : DIIISuperfluidLaws D) :
    D.Theta * D.Hbdg = D.Hbdg * D.Theta := by
  calc
    D.Theta * D.Hbdg
        = D.Theta * D.Hbdg * 1 := by rw [mul_one]
    _ = D.Theta * D.Hbdg * (-(D.Theta * D.Theta)) := by
          rw [hD.1]
          simp
    _ = -(D.Theta * D.Hbdg * D.Theta) * D.Theta := by
          noncomm_ring
    _ = -(-D.Hbdg) * D.Theta := by
          rw [hD.2.2.2.1]
    _ = D.Hbdg * D.Theta := by simp

theorem particle_hole_anticommutes_H (hD : DIIISuperfluidLaws D) :
    D.Xi * D.Hbdg = -(D.Hbdg * D.Xi) := by
  calc
    D.Xi * D.Hbdg
        = D.Xi * D.Hbdg * 1 := by rw [mul_one]
    _ = D.Xi * D.Hbdg * (D.Xi * D.Xi) := by
          rw [hD.2.1]
    _ = (D.Xi * D.Hbdg * D.Xi) * D.Xi := by
          noncomm_ring
    _ = (-D.Hbdg) * D.Xi := by
          rw [hD.2.2.2.2.1]
    _ = -(D.Hbdg * D.Xi) := by rw [neg_mul]

end DIIISuperfluidDatum

/-! ## 2. Topological invariants -/

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

end InfoGeometry.CondensedMatter.DIIISuperfluid
