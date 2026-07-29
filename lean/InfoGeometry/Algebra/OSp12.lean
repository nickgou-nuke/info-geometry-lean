import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Algebra.BosonizedOSpCoproduct
import InfoGeometry.Canonical.OperatorCartanSuperbracketClosure
import InfoGeometry.Canonical.FibonacciParafermionAtoms

noncomputable section

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace InfoGeometry.Algebra.OSp12

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The operator carrier used in this file. -/
abbrev Op (V : Type*) [AddCommGroup V] [Module ℝ V] := Module.End ℝ V

/-- Scalar-smul projector onto the vacuum sector `1 - O^2`. -/
def projVac (O : Op V) : Op V :=
  1 - O ^ 2

/-- Scalar-smul projector onto the `+1` sector `(1/2)(O^2 + O)`. -/
def projUp (O : Op V) : Op V :=
  (1 / 2 : ℝ) • (O ^ 2 + O)

/-- Scalar-smul projector onto the `-1` sector `(1/2)(O^2 - O)`. -/
def projDown (O : Op V) : Op V :=
  (1 / 2 : ℝ) • (O ^ 2 - O)

/-- Under `O^3 = O`, the vacuum projector is idempotent. -/
theorem projVac_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projVac O * projVac O = projVac O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy_idempotent O hO3

/-- Under `O^3 = O`, the `+1` projector is idempotent. -/
theorem projUp_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projUp O * projUp O = projUp O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_idempotent O hO3

/-- Under `O^3 = O`, the `-1` projector is idempotent. -/
theorem projDown_idempotent (O : Op V) (hO3 : O ^ 3 = O) :
    projDown O * projDown O = projDown O := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O =
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_idempotent O hO3

theorem projVac_add_projUp_add_projDown (O : Op V) :
    projVac O + projUp O + projDown O = 1 := by
  have hdrazin :
      projUp O + projDown O =
        InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
    calc
      projUp O + projDown O
          = InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O +
              InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O := by
              rfl
      _ = InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_eq_chiral_sum
                (O := O)).symm
  calc
    projVac O + projUp O + projDown O
        = projVac O + (projUp O + projDown O) := by
            abel
    _ = projVac O + InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O := by
            rw [hdrazin]
    _ = 1 := by
            simpa [projVac] using
              (InfoGeometry.Canonical.FibonacciParafermionAtoms.bulk_boundary_completeness
                (O := O))

theorem supportProjector_eq (O : Op V) :
    projUp O + projDown O = O ^ 2 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O +
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O = O ^ 2
  exact (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_eq_chiral_sum
    (O := O)).symm

theorem vacuumComplement_eq (O : Op V) :
    projVac O = 1 - (projUp O + projDown O) := by
  rw [supportProjector_eq]
  rfl

theorem projUp_mul_projDown (O : Op V) (hO3 : O ^ 3 = O) :
    projUp O * projDown O = 0 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_orthogonal_down O hO3

theorem projDown_mul_projUp (O : Op V) (hO3 : O ^ 3 = O) :
    projDown O * projUp O = 0 := by
  change InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O *
      InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O = 0
  exact InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_orthogonal_up O hO3

structure OperatorSurface where
  Γ : Op V
  hΓ : Γ * Γ = 1
  H : Op V
  Ep : Op V
  Em : Op V
  G1 : Op V
  G2 : Op V
  H_even : Γ * H = H * Γ
  Ep_even : Γ * Ep = Ep * Γ
  Em_even : Γ * Em = Em * Γ
  G1_odd : Γ * G1 = -G1 * Γ
  G2_odd : Γ * G2 = -G2 * Γ
  H_Ep : InfoGeometry.Algebra.SupergradedBracket.superBracket false false H Ep = (2 : ℝ) • Ep
  H_Em : InfoGeometry.Algebra.SupergradedBracket.superBracket false false H Em = (-2 : ℝ) • Em
  Ep_Em : InfoGeometry.Algebra.SupergradedBracket.superBracket false false Ep Em = H
  H_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true H G1 = (1 : ℝ) • G1
  H_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true H G2 = (-1 : ℝ) • G2
  Ep_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true Ep G2 = G1
  Em_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket false true Em G1 = G2
  G1_G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G1 G1 = (2 : ℝ) • Ep
  G2_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G2 G2 = (-2 : ℝ) • Em
  G1_G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true G1 G2 = -H

namespace OperatorSurface

def evenProjection (Γ T : Op V) : Op V :=
  (1 / 2 : ℝ) • (T + Γ * T * Γ)

def oddProjection (Γ T : Op V) : Op V :=
  (1 / 2 : ℝ) • (T - Γ * T * Γ)

theorem even_add_odd (Γ T : Op V) :
    evenProjection Γ T + oddProjection Γ T = T := by
  calc
    evenProjection Γ T + oddProjection Γ T
        = (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • T := by
            rw [evenProjection, oddProjection, smul_add, smul_sub]
            simp [sub_eq_add_neg, add_left_comm, add_assoc]
    _ = T := by
          have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
          rw [← add_smul, hhalf, one_smul]

theorem active_support_compression (O : Op V) :
    projUp O + projDown O = O ^ 2 := by
  exact supportProjector_eq O

/-- The first odd self-bracket relation determines its square. -/
theorem G1_sq (S : OperatorSurface (V := V)) :
    S.G1 * S.G1 = S.Ep := by
  have h := congrArg (fun T : Op V => (1 / 2 : ℝ) • T) S.G1_G1
  have h' :
      (1 / 2 : ℝ) • (S.G1 * S.G1) + (1 / 2 : ℝ) • (S.G1 * S.G1) = S.Ep := by
    simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      smul_add, smul_smul] using h
  calc
    S.G1 * S.G1 =
        (1 / 2 : ℝ) • (S.G1 * S.G1) + (1 / 2 : ℝ) • (S.G1 * S.G1) := by
      module
    _ = S.Ep := h'

/-- The second odd self-bracket relation determines its signed square. -/
theorem G2_sq (S : OperatorSurface (V := V)) :
    S.G2 * S.G2 = -S.Em := by
  have h := congrArg (fun T : Op V => (1 / 2 : ℝ) • T) S.G2_G2
  have h' :
      (1 / 2 : ℝ) • (S.G2 * S.G2) + (1 / 2 : ℝ) • (S.G2 * S.G2) = -S.Em := by
    simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      smul_add, smul_smul] using h
  calc
    S.G2 * S.G2 =
        (1 / 2 : ℝ) • (S.G2 * S.G2) + (1 / 2 : ℝ) • (S.G2 * S.G2) := by
      module
    _ = -S.Em := h'

/--
The bosonized coproduct preserves the first odd--odd `osp(1|2)` closure
relation.
-/
theorem bosonized_G1_self_anticommutator (S : OperatorSurface (V := V)) :
    InfoGeometry.Algebra.SupergradedBracket.anticommutator
        (InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd
          (R := ℝ) S.Γ S.G1)
        (InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd
          (R := ℝ) S.Γ S.G1) =
      (2 : ℝ) •
        InfoGeometry.Algebra.BosonizedOSpCoproduct.primitiveEven
          (R := ℝ) S.Ep := by
  exact
    InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd_self_anticommutator
      (R := ℝ) S.Γ S.G1 S.Ep S.hΓ S.G1_odd S.G1_sq

/--
The bosonized coproduct preserves the signed second odd--odd `osp(1|2)`
closure relation.
-/
theorem bosonized_G2_self_anticommutator (S : OperatorSurface (V := V)) :
    InfoGeometry.Algebra.SupergradedBracket.anticommutator
        (InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd
          (R := ℝ) S.Γ S.G2)
        (InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd
          (R := ℝ) S.Γ S.G2) =
      (2 : ℝ) •
        InfoGeometry.Algebra.BosonizedOSpCoproduct.primitiveEven
          (R := ℝ) (-S.Em) := by
  exact
    InfoGeometry.Algebra.BosonizedOSpCoproduct.bosonizedOdd_self_anticommutator
      (R := ℝ) S.Γ S.G2 (-S.Em) S.hΓ S.G2_odd S.G2_sq

/-- Concrete instantiation of the `OperatorSurface` to prove it is not vacuous.
We use the trivial representation where all elements are zero, and `Γ` is `1`. -/
def trivialOperatorSurface (V : Type*) [AddCommGroup V] [Module ℝ V] : OperatorSurface (V := V) where
  Γ := 1
  hΓ := mul_one 1
  H := 0
  Ep := 0
  Em := 0
  G1 := 0
  G2 := 0
  H_even := by simp
  Ep_even := by simp
  Em_even := by simp
  G1_odd := by simp
  G2_odd := by simp
  H_Ep := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  H_Em := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  Ep_Em := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  H_G1 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  H_G2 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  Ep_G2 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  Em_G1 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.commutator]
  G1_G1 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.anticommutator]
  G2_G2 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.anticommutator]
  G1_G2 := by simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
    InfoGeometry.Algebra.SupergradedBracket.anticommutator]

end OperatorSurface

end InfoGeometry.Algebra.OSp12
