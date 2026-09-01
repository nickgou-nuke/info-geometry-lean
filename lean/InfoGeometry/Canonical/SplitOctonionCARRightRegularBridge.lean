import Mathlib.Tactic
import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-!
# Native right-regular circular CAR bridge

The literal exterior creation operator raises the established Peirce/exterior
order `0 → 1 → 2 → 3`.  On the split-octonion carrier that endpoint pattern is
carried by right regular multiplication, not by left regular multiplication.

This owner proves the exact operator CAR relations for the right-regular
circular roots.  The proof is intrinsic: right alternativity makes the two
associator corrections in the symmetrized regular product cancel.

No equality with the transported Mathlib exterior operators is asserted here;
that final identification requires the basis-level sign comparison.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable
open InfoGeometry.Physics

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- Native right-regular multiplication operator. -/
def rightRegular (x : CZ) : EndCZ :=
  rightMultiplication x

@[simp] theorem rightRegular_apply (x y : CZ) :
    rightRegular x y = y * x :=
  rfl

private theorem zorn_right_alt (x y : CZ) :
    (y * x) * x = y * (x * x) :=
  InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.zorn_right_alternative x y

/-- In an alternative algebra, the symmetrized composition of right regular
operators is right multiplication by the element anticommutator. -/
theorem rightRegular_anticommutator (a b : CZ) :
    rightRegular a * rightRegular b + rightRegular b * rightRegular a =
      rightRegular (a * b + b * a) := by
  apply LinearMap.ext
  intro y
  change (y * b) * a + (y * a) * b = y * (a * b + b * a)
  rw [mul_add]
  have hskew :=
    InfoGeometry.Algebra.alternative_associator_swap23 zorn_right_alt y b a
  change
    (y * b) * a - y * (b * a) =
      -((y * a) * b - y * (a * b)) at hskew
  abel

/-- A square-zero element gives a square-zero right-regular operator. -/
theorem rightRegular_sq_zero_of_sq_zero
    (x : CZ) (hx : x * x = 0) :
    rightRegular x * rightRegular x = 0 := by
  apply LinearMap.ext
  intro y
  change (y * x) * x = 0
  rw [zorn_right_alt x y, hx]
  simp

@[simp] theorem rightRegular_rootPlus_sq (i : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootPlus i) (rootPlus_sq i)

@[simp] theorem rightRegular_rootMinus_sq (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootMinus i) (rootMinus_sq i)

/-- Full mixed three-mode CAR packet. -/
theorem rightRegular_root_mixed_CAR (i j : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootPlus j) +
        rightRegular (rootPlus j) * rightRegular (rootMinus i) =
      (if i = j then (1 : ℝ) else 0) • (1 : EndCZ) := by
  rw [rightRegular_anticommutator]
  have hanti :
      rootMinus i * rootPlus j + rootPlus j * rootMinus i =
        (if i = j then (1 : ℝ) else 0) • (1 : CZ) := by
    simpa [add_comm] using
      (cartesianZorn_rootPlus_rootMinus_anticommutator_delta j i)
  rw [hanti]
  by_cases hij : i = j
  · subst j
    simp
    apply LinearMap.ext
    intro y
    change y * (1 : CZ) = y
    exact zMul_one y
  · simp [hij, rightRegular]

/-- Positive-positive right-regular anticommutators vanish for all modes. -/
theorem rightRegular_rootPlus_same_CAR (i j : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus j) +
        rightRegular (rootPlus j) * rightRegular (rootPlus i) = 0 := by
  rw [rightRegular_anticommutator]
  have h := cartesianZorn_rootPlus_same_channel_anticommutator i j
  rw [h]
  apply LinearMap.ext
  intro y
  rfl

/-- Negative-negative right-regular anticommutators vanish for all modes. -/
theorem rightRegular_rootMinus_same_CAR (i j : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus j) +
        rightRegular (rootMinus j) * rightRegular (rootMinus i) = 0 := by
  rw [rightRegular_anticommutator]
  have h := cartesianZorn_rootMinus_same_channel_anticommutator i j
  rw [h]
  apply LinearMap.ext
  intro y
  rfl

/-- Per-mode CAR pair for the right-regular circular representation. -/
def rightRegularCARPair (i : Fin 3) : SplitClifford.CARPair EndCZ where
  ann := rightRegular (rootMinus i)
  cre := rightRegular (rootPlus i)
  ann_sq := rightRegular_rootMinus_sq i
  cre_sq := rightRegular_rootPlus_sq i
  anti := by
    simpa using rightRegular_root_mixed_CAR i i

/-! Endpoint laws fixing the exterior-degree orientation. -/

@[simp] theorem rightRegular_rootPlus_uPlus (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i := by
  exact rootPlus_mul_uMinus i |> fun _ => by
    change uPlus * rootPlus i = rootPlus i
    exact uPlus_mul_rootPlus i

@[simp] theorem rightRegular_rootPlus_uMinus (i : Fin 3) :
    rightRegular (rootPlus i) uMinus = 0 := by
  change uMinus * rootPlus i = 0
  exact uMinus_mul_rootPlus i

@[simp] theorem rightRegular_rootMinus_uPlus (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 := by
  change uPlus * rootMinus i = 0
  exact uPlus_mul_rootMinus i

@[simp] theorem rightRegular_rootMinus_uMinus (i : Fin 3) :
    rightRegular (rootMinus i) uMinus = rootMinus i := by
  change uMinus * rootMinus i = rootMinus i
  exact uMinus_mul_rootMinus i

/-- The right-regular positive root has the creation endpoint pattern:
`degree 0 → degree 1`, and annihilates the degree-3 endpoint. -/
theorem rightRegular_creation_endpoint_packet (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i ∧
      rightRegular (rootPlus i) uMinus = 0 :=
  ⟨rightRegular_rootPlus_uPlus i, rightRegular_rootPlus_uMinus i⟩

/-- The right-regular negative root has the annihilation endpoint pattern:
it kills degree 0 and maps the degree-3 endpoint into degree 2. -/
theorem rightRegular_annihilation_endpoint_packet (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 ∧
      rightRegular (rootMinus i) uMinus = rootMinus i :=
  ⟨rightRegular_rootMinus_uPlus i, rightRegular_rootMinus_uMinus i⟩

end InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
