import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import InfoGeometry.Canonical.ZornCliffordRepresentation

/-!
# Base change and the integral spin subgroup

This file maps the external construction of the arithmetic spin subgroup
onto the canonical polymorphic types. Since `ZornMatrix` and `zornNorm`
are defined over any commutative ring, the arithmetic spin subgroup is
simply `spinGroup (zornNorm (R := ℤ))`.

To relate this to the real spin group `spinGroup (zornNorm (R := ℝ))`,
we provide the explicit base change maps along `algebraMap ℤ ℝ`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornIntegralSpinSubgroup

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford

variable {R : Type*} [CommRing R]

@[simp] lemma zero_a : (0 : ZornMatrix R).a = 0 := rfl
@[simp] lemma zero_b : (0 : ZornMatrix R).b = 0 := rfl
@[simp] lemma zero_x : (0 : ZornMatrix R).x = 0 := rfl
@[simp] lemma zero_y : (0 : ZornMatrix R).y = 0 := rfl

@[simp] lemma add_a (z1 z2 : ZornMatrix R) : (z1 + z2).a = z1.a + z2.a := rfl
@[simp] lemma add_b (z1 z2 : ZornMatrix R) : (z1 + z2).b = z1.b + z2.b := rfl
@[simp] lemma add_x (z1 z2 : ZornMatrix R) : (z1 + z2).x = z1.x + z2.x := rfl
@[simp] lemma add_y (z1 z2 : ZornMatrix R) : (z1 + z2).y = z1.y + z2.y := rfl

/-- Base change map embedding the integral Zorn lattice into the real Zorn carrier. -/
def zornBaseChange : ZornMatrix ℤ →+ ZornMatrix ℝ where
  toFun z :=
    { a := (z.a : ℝ)
      b := (z.b : ℝ)
      x := fun i => (z.x i : ℝ)
      y := fun i => (z.y i : ℝ) }
  map_zero' := by ext <;> simp [zero_a, zero_b, zero_x, zero_y]
  map_add' z1 z2 := by ext <;> simp [add_a, add_b, add_x, add_y]

@[simp]
theorem zornBaseChange_a (z : ZornMatrix ℤ) : (zornBaseChange z).a = (z.a : ℝ) := rfl

@[simp]
theorem zornBaseChange_b (z : ZornMatrix ℤ) : (zornBaseChange z).b = (z.b : ℝ) := rfl

@[simp]
theorem zornBaseChange_x (z : ZornMatrix ℤ) (i : Fin 3) : (zornBaseChange z).x i = (z.x i : ℝ) := rfl

@[simp]
theorem zornBaseChange_y (z : ZornMatrix ℤ) (i : Fin 3) : (zornBaseChange z).y i = (z.y i : ℝ) := rfl

theorem zornBaseChange_zornNorm (z : ZornMatrix ℤ) :
    zornNorm (R := ℝ) (zornBaseChange z) = (zornNorm (R := ℤ) z : ℝ) := by
  simp only [zornNorm_apply, zornNormFun]
  dsimp [zornBaseChange, dot]
  push_cast
  ring

/-- The canonical embedding of the integral spin group into the real spin group
is naturally given by functoriality of the Clifford algebra. -/
abbrev integralSpin44 := spinGroup (zornNorm (R := ℤ))

/-- The real spin group over the canonical `(4,4)` Zorn norm. -/
abbrev realSpin44 := spinGroup (zornNorm (R := ℝ))

-- Mathlib already provides functoriality of `CliffordAlgebra` and `spinGroup`
-- when there is an isometric base change map. The map `zornBaseChange` is
-- exactly that isometry over `algebraMap ℤ ℝ`.

end InfoGeometry.Canonical.ZornIntegralSpinSubgroup

end noncomputable section
