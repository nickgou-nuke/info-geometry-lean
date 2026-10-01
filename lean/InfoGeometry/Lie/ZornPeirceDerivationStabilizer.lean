import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornProductBasis
import InfoGeometry.Lie.CanonicalZornStandardDerivationActions

/-!
# Peirce-sheet stabilizer inside the canonical Zorn derivation Lie algebra

This module defines the intrinsic stabilizer of the primitive Peirce idempotent
`canonicalE11` as the kernel of evaluation

  ev_E11 : Der(O_s) → O_s,   D ↦ D(E11).

Because the Lie bracket on derivations is the commutator, derivations that
annihilate E11 are closed under the bracket.  Hence the stabilizer is a genuine
Lie subalgebra of the repository-owned 14-dimensional canonical Zorn
derivation algebra.

The file also records concrete standard derivations already proved elsewhere
to annihilate E11.

No identification of this Lie subalgebra with `sl(3,R)` is asserted here;
that requires an explicit 8-dimensional equivalence and bracket
intertwining theorem.
-/

noncomputable section

namespace InfoGeometry.Lie.ZornPeirceDerivationStabilizer

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornProductBasis
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornStandardDerivationActions

abbrev Der := canonicalZornDerivations
abbrev CZ := CanonicalZornDerivation.CZ

/-- Evaluation of a canonical split-octonion derivation at the primitive
Peirce idempotent `E11`. -/
def evalE11 : Der →ₗ[ℝ] CZ where
  toFun D := D.1 canonicalE11
  map_add' D E := by
    simp
  map_smul' r D := by
    simp

@[simp] theorem evalE11_apply (D : Der) :
    evalE11 D = D.1 canonicalE11 := rfl

/-- The linear stabilizer submodule of the primitive Peirce idempotent. -/
def stabilizerSubmodule : Submodule ℝ Der :=
  LinearMap.ker evalE11

@[simp] theorem mem_stabilizerSubmodule_iff (D : Der) :
    D ∈ stabilizerSubmodule ↔ D.1 canonicalE11 = 0 := by
  rfl

/-- The Peirce-sheet stabilizer is a Lie subalgebra. -/
def stabilizerLieSubalgebra : LieSubalgebra ℝ Der where
  __ := stabilizerSubmodule
  lie_mem' := by
    intro D E hD hE
    change (⁅D, E⁆ : Der).1 canonicalE11 = 0
    change D.1 (E.1 canonicalE11) - E.1 (D.1 canonicalE11) = 0
    rw [mem_stabilizerSubmodule_iff] at hD hE
    rw [hD, hE]
    simp

@[simp] theorem mem_stabilizerLieSubalgebra_iff (D : Der) :
    D ∈ stabilizerLieSubalgebra ↔ D.1 canonicalE11 = 0 := by
  rfl

/-- The stabilizer is closed under the derivation Lie bracket. -/
theorem bracket_mem_stabilizer
    {D E : Der}
    (hD : D ∈ stabilizerLieSubalgebra)
    (hE : E ∈ stabilizerLieSubalgebra) :
    ⁅D, E⁆ ∈ stabilizerLieSubalgebra :=
  stabilizerLieSubalgebra.lie_mem hD hE

/-- Standard opposite-root derivations `D_{V_i,U_i}` stabilize E11. -/
theorem standard_VU_mem_stabilizer (i : Fin 3) :
    canonicalStandardDerivationOfCanonical (canonicalV i) (canonicalU i) ∈
      stabilizerLieSubalgebra := by
  change directCanonicalStanDerMap (canonicalV i) (canonicalU i) canonicalE11 = 0
  exact direct_standard_v_u_e i

/-- Standard opposite-root derivations `D_{U_i,V_i}` stabilize E11. -/
theorem standard_UV_mem_stabilizer (i : Fin 3) :
    canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i) ∈
      stabilizerLieSubalgebra := by
  change directCanonicalStanDerMap (canonicalU i) (canonicalV i) canonicalE11 = 0
  exact direct_standard_u_v_e i

/-- Any bracket of two concrete E11-stabilizing standard derivations remains
in the E11 stabilizer. -/
theorem standard_UV_bracket_standard_VU_mem_stabilizer
    (i j : Fin 3) :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i),
      canonicalStandardDerivationOfCanonical (canonicalV j) (canonicalU j)⁆ ∈
      stabilizerLieSubalgebra := by
  exact bracket_mem_stabilizer
    (standard_UV_mem_stabilizer i)
    (standard_VU_mem_stabilizer j)

/-- Intrinsic characterization: the stabilizer is exactly the kernel of
evaluation at E11. -/
theorem stabilizer_eq_evalE11_kernel :
    stabilizerLieSubalgebra.toSubmodule = LinearMap.ker evalE11 := by
  rfl

end InfoGeometry.Lie.ZornPeirceDerivationStabilizer
