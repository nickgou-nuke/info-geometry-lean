import Mathlib.Tactic
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# InfoGeometry.Canonical.SplitCliffordInfiniteCurrent

Canonical infinite current algebra surface, implemented by reusing the external
Heisenberg algebra module.

This file gives a concrete infinite indexed current family `Jinf : Int → 𝔥` and
its central element `Kinf`, with proved commutator law:

`[J_m, J_n] = if m + n = 0 then (m : 𝕜) • Kinf else 0`.

No wrappers, no placeholders.
-/

namespace InfoGeometry.Canonical.SplitCliffordInfiniteCurrent

open scoped BigOperators

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- Infinite current carrier, realized by the external Heisenberg algebra. -/
abbrev InfiniteCurrentAlg : Type _ := VirasoroProject.HeisenbergAlgebra 𝕜

/-- Infinite current modes `J_n`. -/
noncomputable def Jinf (n : Int) : InfiniteCurrentAlg 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n

/-- Central generator `K`. -/
noncomputable def Kinf : InfiniteCurrentAlg 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.kgen 𝕜

/-- External Heisenberg commutator law on canonical infinite modes. -/
@[simp] theorem lie_Jinf
    (m n : Int) :
    ⁅Jinf 𝕜 m, Jinf 𝕜 n⁆ =
      if m + n = 0 then (m : 𝕜) • Kinf 𝕜 else 0 := by
  simpa [Jinf, Kinf] using VirasoroProject.HeisenbergAlgebra.lie_jgen (𝕜 := 𝕜) m n

/-- The central generator commutes with every element. -/
@[simp] theorem lie_Kinf
    (Z : InfiniteCurrentAlg 𝕜) :
    ⁅Kinf 𝕜, Z⁆ = 0 := by
  simpa [Kinf] using VirasoroProject.HeisenbergAlgebra.lie_kgen (𝕜 := 𝕜) Z

/-- Mode-zero current is central. -/
@[simp] theorem lie_Jinf_zero
    (Z : InfiniteCurrentAlg 𝕜) :
    ⁅Jinf 𝕜 0, Z⁆ = 0 := by
  simpa [Jinf] using VirasoroProject.HeisenbergAlgebra.lie_jgen_zero (𝕜 := 𝕜) Z

/-- Concrete first central-mode readout: `[J_1, J_{-1}] = 1 • K`. -/
theorem lie_Jinf_one_neg_one :
    ⁅Jinf 𝕜 1, Jinf 𝕜 (-1)⁆ = (1 : 𝕜) • Kinf 𝕜 := by
  simpa [Jinf, Kinf] using VirasoroProject.HeisenbergAlgebra.lie_jgen (𝕜 := 𝕜) (1 : Int) (-1 : Int)

/-- Concrete opposite readout: `[J_{-1}, J_1] = -1 • K`. -/
theorem lie_Jinf_neg_one_one :
    ⁅Jinf 𝕜 (-1), Jinf 𝕜 1⁆ = ((-1 : Int) : 𝕜) • Kinf 𝕜 := by
  simpa [Jinf, Kinf] using VirasoroProject.HeisenbergAlgebra.lie_jgen (𝕜 := 𝕜) (-1 : Int) (1 : Int)

end InfoGeometry.Canonical.SplitCliffordInfiniteCurrent
