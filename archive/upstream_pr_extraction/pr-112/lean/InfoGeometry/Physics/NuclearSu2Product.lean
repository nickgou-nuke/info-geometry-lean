import Mathlib.Tactic
import InfoGeometry.External.Auto.WeakIsospinSU2
import InfoGeometry.Physics.ChiralCausalCone

/-!
# Physical degree-zero spin/isospin generators

The existing five-grading is an abstract transition algebra.  This file keeps
the physical degree-zero copies separate: one copy acts in the spin lane and
the other in the isospin lane.  The pair construction records their commuting
cross-action without identifying it with the abstract five-grading.
-/

namespace InfoGeometry.Physics.NuclearSu2Product

open WeakIsospinSU2
open InfoGeometry.Physics.ChiralCausalCone

abbrev ZeroSector := M2C × M2C

noncomputable def pairMul (x y : ZeroSector) : ZeroSector :=
  (x.1 * y.1, x.2 * y.2)

noncomputable def pairComm (x y : ZeroSector) : ZeroSector :=
  pairMul x y - pairMul y x

noncomputable def spinGenerator (x : M2C) : ZeroSector := (x, (0 : M2C))

noncomputable def isospinGenerator (y : M2C) : ZeroSector := ((0 : M2C), y)

theorem spin_isospin_commute (x y : M2C) :
    pairComm (spinGenerator x) (isospinGenerator y) = 0 := by
  ext <;> simp [pairComm, pairMul, spinGenerator, isospinGenerator]

theorem spin_generator_commutator
    (x y : M2C) :
    pairComm (spinGenerator x) (spinGenerator y) =
      spinGenerator (x * y - y * x) := by
  ext <;> simp [pairComm, pairMul, spinGenerator]

theorem isospin_generator_commutator
    (x y : M2C) :
    pairComm (isospinGenerator x) (isospinGenerator y) =
      isospinGenerator (x * y - y * x) := by
  ext <;> simp [pairComm, pairMul, isospinGenerator]

theorem pauli_spin_isospin_cross_commute (i j : Fin 3) :
    pairComm
        (spinGenerator (match i with
          | 0 => I₁
          | 1 => I₂
          | _ => I₃))
        (isospinGenerator (match j with
          | 0 => I₁
          | 1 => I₂
          | _ => I₃)) = 0 := by
  exact spin_isospin_commute _ _

end InfoGeometry.Physics.NuclearSu2Product
