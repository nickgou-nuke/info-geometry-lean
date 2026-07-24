import InfoGeometry.Algebra.FiveGradedTKK
import InfoGeometry.Canonical.SL2FiveGradingExample
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Clifford.ConformalLieAlgebra55
import InfoGeometry.Physics.Pin55Formal
import InfoGeometry.Physics.OrbitClassification55

/-!
# InfoGeometry.Canonical.TKKFiveGradePin55AffineCapstone

Conservative capstone for the exact owner surfaces already present in the repo
around:

* TKK / five-graded decomposition;
* the concrete affine `sl₂` ladder `e,f,h`;
* conformal five-grade inversion in the `(5,5)` Clifford lane;
* finite `Pin(5,5)` reflection identities;
* the `J₂(𝕆_s)` orbit trichotomy used for the `O(5,5)` / `Pin(5,5)` story.

This file is intentionally honest. It does **not** claim:

* a full global TKK realization of all `O(5,5)` data;
* a complete topological quotient construction of `Pin(5,5)`;
* a native theorem identifying user-level `e₁,e₂` affine generators with a
  single canonical ambient `O(5,5)` basis.

What it does package is the strongest finite/kernel-checked packet currently
available from existing owner files.

**Relationship to sibling capstones:**

This file covers the **abstract TKK five-grading + affine `sl₂` + Pin(5,5) reflections** story:
- Five-grade weight labels (`-2, -1, 0, +1, +2`)
- Affine `sl₂` ladder commutation relations
- Conformal grade inversion symmetry
- Pin(5,5) discrete reflection generators and their Clifford algebra relations
- Jordan matrix orbit trichotomy (zero / null / generic)

For the **O(5,5) / TKK generator corridor** in `Cl(5,5)` —
the explicit chain from null generators `u₅,v₅,u₄,v₄` through
dilation generators `D₅,D₄,D` to complex structure `J₅,J₄,J` and full adjoint closure —
see the sibling capstone:
`InfoGeometry.Canonical.O55ClosureByCommutators`.

Together, these two files form the complete kernel-checked TKK / Pin(5,5) packet:
- `TKKFiveGradePin55AffineCapstone`: abstract TKK weights, affine ladder, and orbit trichotomy
- `O55ClosureByCommutators`: the Cl(5,5) null-generator closure chain
-/

noncomputable section

namespace InfoGeometry.Canonical.TKKFiveGradePin55AffineCapstone

open InfoGeometry.Algebra.FiveGradedTKK
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.Physics.OrbitClassification55
open InfoGeometry.Clifford.ConformalLieAlgebra55
open Matrix

/--
The finite five-grade label packet already proved in the TKK socket.
-/
theorem weight5_packet :
    Weight5.toInt Weight5.neg_two = -2 ∧
    Weight5.toInt Weight5.neg_one = -1 ∧
    Weight5.toInt Weight5.zero = 0 ∧
    Weight5.toInt Weight5.pos_one = 1 ∧
    Weight5.toInt Weight5.pos_two = 2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Concrete affine `sl₂` ladder already proved in the example file.
-/
theorem affine_sl2_packet :
    InfoGeometry.Canonical.SL2FiveGradingExample.e *
        InfoGeometry.Canonical.SL2FiveGradingExample.f
      - InfoGeometry.Canonical.SL2FiveGradingExample.f *
        InfoGeometry.Canonical.SL2FiveGradingExample.e
      = InfoGeometry.Canonical.SL2FiveGradingExample.h
    ∧ InfoGeometry.Canonical.SL2FiveGradingExample.h *
        InfoGeometry.Canonical.SL2FiveGradingExample.e
      - InfoGeometry.Canonical.SL2FiveGradingExample.e *
        InfoGeometry.Canonical.SL2FiveGradingExample.h
      = (2 : ℝ) • InfoGeometry.Canonical.SL2FiveGradingExample.e
    ∧ InfoGeometry.Canonical.SL2FiveGradingExample.h *
        InfoGeometry.Canonical.SL2FiveGradingExample.f
      - InfoGeometry.Canonical.SL2FiveGradingExample.f *
        InfoGeometry.Canonical.SL2FiveGradingExample.h
      = (-2 : ℝ) • InfoGeometry.Canonical.SL2FiveGradingExample.f := by
  exact ⟨InfoGeometry.Canonical.SL2FiveGradingExample.comm_e_f,
    InfoGeometry.Canonical.SL2FiveGradingExample.comm_h_e,
    InfoGeometry.Canonical.SL2FiveGradingExample.comm_h_f⟩

/--
The canonical conformal five-grade inversion swaps opposite grades and fixes the
center grade.
-/
theorem conformal_grade_swap_packet :
    ConformalGrade.swap ConformalGrade.negTwo = ConformalGrade.posTwo ∧
    ConformalGrade.swap ConformalGrade.negOne = ConformalGrade.posOne ∧
    ConformalGrade.swap ConformalGrade.zero = ConformalGrade.zero ∧
    ConformalGrade.swap ConformalGrade.posOne = ConformalGrade.negOne ∧
    ConformalGrade.swap ConformalGrade.posTwo = ConformalGrade.negTwo := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Finite `Pin(5,5)` reflection packet from the split Clifford owner file.
-/
theorem pin55_reflection_packet :
    q55 ε₀ = 1 ∧
    q55 ε₅ = -1 ∧
    r₀ * r₀ = 1 ∧
    r₅ * r₅ = -1 ∧
    r₀ * r₅ = -(r₅ * r₀) ∧
    (r₀ * r₅) * (r₀ * r₅) = 1 := by
  exact ⟨q55_ε₀, q55_ε₅, r₀_sq, r₅_sq, anticomm, v4_relation⟩

/--
The finite `J₂(𝕆_s)` / `Pin(5,5)` orbit trichotomy packet.
-/
theorem orbit55_packet (X : JordanMatrix10D) :
    JordanMatrix10D.OrbitType X :=
  JordanMatrix10D.orbit_classification X

/--
Unified conservative packet for the TKK / five-grade / `Pin(5,5)` / affine lane.
-/
theorem conservative_tkk_pin55_affine_capstone (X : JordanMatrix10D) :
    (Weight5.toInt Weight5.neg_two = -2
      ∧ Weight5.toInt Weight5.neg_one = -1
      ∧ Weight5.toInt Weight5.zero = 0
      ∧ Weight5.toInt Weight5.pos_one = 1
      ∧ Weight5.toInt Weight5.pos_two = 2)
    ∧ (InfoGeometry.Canonical.SL2FiveGradingExample.e *
          InfoGeometry.Canonical.SL2FiveGradingExample.f
        - InfoGeometry.Canonical.SL2FiveGradingExample.f *
          InfoGeometry.Canonical.SL2FiveGradingExample.e
        = InfoGeometry.Canonical.SL2FiveGradingExample.h
      ∧ InfoGeometry.Canonical.SL2FiveGradingExample.h *
          InfoGeometry.Canonical.SL2FiveGradingExample.e
        - InfoGeometry.Canonical.SL2FiveGradingExample.e *
          InfoGeometry.Canonical.SL2FiveGradingExample.h
        = (2 : ℝ) • InfoGeometry.Canonical.SL2FiveGradingExample.e
      ∧ InfoGeometry.Canonical.SL2FiveGradingExample.h *
          InfoGeometry.Canonical.SL2FiveGradingExample.f
        - InfoGeometry.Canonical.SL2FiveGradingExample.f *
          InfoGeometry.Canonical.SL2FiveGradingExample.h
        = (-2 : ℝ) • InfoGeometry.Canonical.SL2FiveGradingExample.f)
    ∧ (ConformalGrade.swap ConformalGrade.negTwo = ConformalGrade.posTwo
      ∧ ConformalGrade.swap ConformalGrade.negOne = ConformalGrade.posOne
      ∧ ConformalGrade.swap ConformalGrade.zero = ConformalGrade.zero
      ∧ ConformalGrade.swap ConformalGrade.posOne = ConformalGrade.negOne
      ∧ ConformalGrade.swap ConformalGrade.posTwo = ConformalGrade.negTwo)
    ∧ (q55 ε₀ = 1
      ∧ q55 ε₅ = -1
      ∧ r₀ * r₀ = 1
      ∧ r₅ * r₅ = -1
      ∧ r₀ * r₅ = -(r₅ * r₀)
      ∧ (r₀ * r₅) * (r₀ * r₅) = 1)
    ∧ JordanMatrix10D.OrbitType X := by
  exact ⟨weight5_packet, affine_sl2_packet, conformal_grade_swap_packet,
    pin55_reflection_packet, orbit55_packet X⟩

end InfoGeometry.Canonical.TKKFiveGradePin55AffineCapstone
