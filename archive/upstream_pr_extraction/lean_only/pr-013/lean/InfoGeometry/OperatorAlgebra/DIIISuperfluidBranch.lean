/-
InfoGeometry/OperatorAlgebra/DIIISuperfluidBranch.lean

DIII superfluid branch.

Class DIII is the BdG/Majorana realization of the chiral-flipping CPT branch:

  T^2 = -1
  C^2 = +1
  chi = T C
  chi^2 = 1
  T H = H T
  C H = - H C
  chi H = - H chi

Here `T` is the time-reversal/Kramers symmetry, `C` is the particle-hole
or CPT/BdG mirror, and `chi` is the induced chiral grading.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ModularChiralMirror

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch

open InfoGeometry.OperatorAlgebra.ModularChiralMirror

/-! ## 1. DIII BdG/Majorana symmetry datum -/

/--
DIII superfluid/BdG symmetry datum in an abstract operator algebra.

This is algebraic and representation-agnostic.  A concrete model can later
instantiate `Op` by finite BdG matrices, bounded real operators on a doubled
Majorana carrier, or a suitable regularized operator algebra.
-/
structure DIIISuperfluidDatum
    (Op : Type*) [Ring Op] where
  /-- BdG/Majorana Hamiltonian. -/
  Hbdg : Op

  /-- Time-reversal symmetry. In class DIII, `T² = -1`. -/
  T : Op

  /-- Particle-hole/BdG conjugation. In class DIII, `C² = +1`. -/
  C : Op

  /-- Chiral grading, usually `chi = T C`. -/
  chi : Op

  /-- Kramers time-reversal sign. -/
  T_square :
    T * T = -(1 : Op)

  /-- BdG particle-hole sign. -/
  C_square :
    C * C = 1

  /-- The chiral grading is the product `T C`. -/
  chi_eq :
    chi = T * C

  /-- The chiral grading is an involution. -/
  chi_square :
    chi * chi = 1

  /-- Time reversal preserves the Hamiltonian. -/
  T_commutes_H :
    T * Hbdg = Hbdg * T

  /-- Particle-hole conjugation anticommutes with the Hamiltonian. -/
  C_anticommutes_H :
    C * Hbdg = -(Hbdg * C)

namespace DIIISuperfluidDatum

variable {Op : Type*} [Ring Op]
variable (D : DIIISuperfluidDatum Op)

/--
The induced chiral symmetry anticommutes with the BdG Hamiltonian:

`chi H = - H chi`.

This is the algebraic reason DIII has a chiral grading.
-/
theorem chi_anticommutes_H :
    D.chi * D.Hbdg = -(D.Hbdg * D.chi) := by
  calc
    D.chi * D.Hbdg
        = (D.T * D.C) * D.Hbdg := by
            rw [D.chi_eq]
    _ = D.T * (D.C * D.Hbdg) := by
            rw [mul_assoc]
    _ = D.T * (-(D.Hbdg * D.C)) := by
            rw [D.C_anticommutes_H]
    _ = -(D.T * (D.Hbdg * D.C)) := by
            rw [mul_neg]
    _ = -((D.T * D.Hbdg) * D.C) := by
            rw [mul_assoc]
    _ = -((D.Hbdg * D.T) * D.C) := by
            rw [D.T_commutes_H]
    _ = -(D.Hbdg * (D.T * D.C)) := by
            rw [mul_assoc]
    _ = -(D.Hbdg * D.chi) := by
            rw [← D.chi_eq]

/-- The chiral grading gives the Hamiltonian sign flip. -/
theorem Hamiltonian_is_chiral_odd :
    D.chi * D.Hbdg = -(D.Hbdg * D.chi) :=
  D.chi_anticommutes_H

end DIIISuperfluidDatum

/-! ## 2. CPT-calibrated DIII branch -/

/--
DIII branch calibrated so that the particle-hole/CPT mirror flips chirality.

The additional relation

`C T = - T C`

implies

`C chi = - chi C`.

Thus the BdG particle-hole mirror is a chiral-flipping modular/CPT mirror.
-/
structure DIIICPTBranchDatum
    (Op : Type*) [Ring Op]
    extends DIIISuperfluidDatum Op where
  /--
  Calibration relation between particle-hole and time-reversal symmetries.

  This is the sign convention that makes `C` anticommute with the induced
  chiral grading.
  -/
  C_T_anticomm :
    C * T = -(T * C)

namespace DIIICPTBranchDatum

variable {Op : Type*} [Ring Op]
variable (D : DIIICPTBranchDatum Op)

/-- The particle-hole/CPT mirror flips chirality: `C chi = - chi C`. -/
theorem C_flips_chirality :
    D.C * D.chi = -(D.chi * D.C) := by
  calc
    D.C * D.chi
        = D.C * (D.T * D.C) := by
            rw [D.chi_eq]
    _ = (D.C * D.T) * D.C := by
            rw [mul_assoc]
    _ = (-(D.T * D.C)) * D.C := by
            rw [D.C_T_anticomm]
    _ = -((D.T * D.C) * D.C) := by
            rw [neg_mul]
    _ = -(D.chi * D.C) := by
            rw [D.chi_eq]

/--
In a real-algebra setting, the DIII CPT branch induces the modular chiral
mirror datum with `J = C` and `chi = chi`.
-/
def toModularChiralMirrorDatum
    [Algebra ℝ Op] :
    ModularChiralMirrorDatum Op where
  J := D.C
  chi := D.chi
  J_square := D.C_square
  chi_square := D.chi_square
  J_flips_chi := D.C_flips_chirality

/-- The left chiral projector of the calibrated DIII branch. -/
def P_left
    [Algebra ℝ Op] : Op :=
  (D.toModularChiralMirrorDatum).P_left

/-- The right chiral projector of the calibrated DIII branch. -/
def P_right
    [Algebra ℝ Op] : Op :=
  (D.toModularChiralMirrorDatum).P_right

/-- Particle-hole/CPT sends the left DIII chiral projector to the right one. -/
theorem C_mul_P_left
    [Algebra ℝ Op] :
    D.C * D.P_left = D.P_right * D.C :=
  (D.toModularChiralMirrorDatum).J_mul_P_left

/-- Particle-hole/CPT sends the right DIII chiral projector to the left one. -/
theorem C_mul_P_right
    [Algebra ℝ Op] :
    D.C * D.P_right = D.P_left * D.C :=
  (D.toModularChiralMirrorDatum).J_mul_P_right

/--
Conjugation by the particle-hole/CPT mirror sends the left projector to the
right projector.
-/
theorem C_conj_P_left
    [Algebra ℝ Op] :
    D.C * D.P_left * D.C = D.P_right :=
  (D.toModularChiralMirrorDatum).J_conj_P_left

/--
Conjugation by the particle-hole/CPT mirror sends the right projector to the
left projector.
-/
theorem C_conj_P_right
    [Algebra ℝ Op] :
    D.C * D.P_right * D.C = D.P_left :=
  (D.toModularChiralMirrorDatum).J_conj_P_right

end DIIICPTBranchDatum

/-! ## 3. Topological data socket -/

/--
A coarse DIII topological phase label.

The classification group depends on spatial dimension and on the analytic
model.  For example, in the noninteracting tenfold-way table, class DIII has
`Z` in three spatial dimensions and `Z2` in one and two dimensions.

This structure records the invariant without asserting a classification theorem.
-/
structure DIIITopologicalInvariant
    (Op : Type*) [Ring Op] where
  /-- Spatial dimension of the bulk model. -/
  spatialDimension : ℕ

  /-- Integer winding invariant, used for the standard 3D DIII case. -/
  winding : ℤ

  /-- Optional mod-two invariant. -/
  modTwo : ZMod 2

  /-- Certificate that this invariant is attached to the chosen DIII model. -/
  invariant_certificate : Prop

/--
A DIII topological superfluid model is a DIII symmetry datum together with a
topological invariant socket.
-/
structure DIIITopologicalSuperfluid
    (Op : Type*) [Ring Op] where
  symmetry : DIIISuperfluidDatum Op
  invariant : DIIITopologicalInvariant Op

end InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch
