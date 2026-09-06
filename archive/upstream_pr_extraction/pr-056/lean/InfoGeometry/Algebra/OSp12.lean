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
open InfoGeometry.Algebra.SupergradedBracket

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
  H : Op V
  Ep : Op V
  Em : Op V
  G1 : Op V
  G2 : Op V

def OperatorSurfaceLaws (S : OperatorSurface (V := V)) : Prop :=
  S.Γ * S.Γ = 1 ∧
  S.Γ * S.H = S.H * S.Γ ∧
  S.Γ * S.Ep = S.Ep * S.Γ ∧
  S.Γ * S.Em = S.Em * S.Γ ∧
  S.Γ * S.G1 = -(S.G1 * S.Γ) ∧
  S.Γ * S.G2 = -(S.G2 * S.Γ) ∧
  superBracket false false S.H S.Ep = (2 : ℝ) • S.Ep ∧
  superBracket false false S.H S.Em = (-2 : ℝ) • S.Em ∧
  superBracket false false S.Ep S.Em = S.H ∧
  superBracket false true S.H S.G1 = (1 : ℝ) • S.G1 ∧
  superBracket false true S.H S.G2 = (-1 : ℝ) • S.G2 ∧
  superBracket false true S.Ep S.G2 = S.G1 ∧
  superBracket false true S.Em S.G1 = S.G2 ∧
  superBracket true true S.G1 S.G1 = (2 : ℝ) • S.Ep ∧
  superBracket true true S.G2 S.G2 = (-2 : ℝ) • S.Em ∧
  superBracket true true S.G1 S.G2 = -S.H

theorem OperatorSurfaceLaws.hΓ {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : S.Γ * S.Γ = 1 := h.1

theorem OperatorSurfaceLaws.G1_odd {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : S.Γ * S.G1 = -(S.G1 * S.Γ) := h.2.2.2.2.1

theorem OperatorSurfaceLaws.H_Ep {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false false S.H S.Ep = (2 : ℝ) • S.Ep := h.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.H_Em {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false false S.H S.Em = (-2 : ℝ) • S.Em := h.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.Ep_Em {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false false S.Ep S.Em = S.H := h.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.H_G1 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false true S.H S.G1 = (1 : ℝ) • S.G1 := h.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.H_G2 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false true S.H S.G2 = (-1 : ℝ) • S.G2 := h.2.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.Ep_G2 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false true S.Ep S.G2 = S.G1 := h.2.2.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.Em_G1 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket false true S.Em S.G1 = S.G2 := h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.G1_G1 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket true true S.G1 S.G1 = (2 : ℝ) • S.Ep := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.G2_G2 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket true true S.G2 S.G2 = (-2 : ℝ) • S.Em := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem OperatorSurfaceLaws.G1_G2 {S : OperatorSurface (V := V)}
    (h : OperatorSurfaceLaws S) : superBracket true true S.G1 S.G2 = -S.H := by
  rcases h with ⟨hΓ, hH, hEp, hEm, hG1, hG2, hHEp, hHEm,
    hEpEm, hHG1, hHG2, hEpG2, hEmG1, hG1G1, hG2G2, hG1G2⟩
  exact hG1G2

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
theorem G1_sq (S : OperatorSurface (V := V))
    (hG1G1 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      S.G1 S.G1 = (2 : ℝ) • S.Ep) :
    S.G1 * S.G1 = S.Ep := by
  have h := congrArg (fun T : Op V => (1 / 2 : ℝ) • T) hG1G1
  have h' :
      (1 / 2 : ℝ) • (S.G1 * S.G1) + (1 / 2 : ℝ) • (S.G1 * S.G1) = S.Ep := by
    simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      InfoGeometry.Algebra.InvariantTransport.anticommutator,
      smul_add, smul_smul] using h
  calc
    S.G1 * S.G1 =
        (1 / 2 : ℝ) • (S.G1 * S.G1) + (1 / 2 : ℝ) • (S.G1 * S.G1) := by
      module
    _ = S.Ep := h'

/-- The second odd self-bracket relation determines its signed square. -/
theorem G2_sq (S : OperatorSurface (V := V))
    (hG2G2 : InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      S.G2 S.G2 = (-2 : ℝ) • S.Em) :
    S.G2 * S.G2 = -S.Em := by
  have h := congrArg (fun T : Op V => (1 / 2 : ℝ) • T) hG2G2
  have h' :
      (1 / 2 : ℝ) • (S.G2 * S.G2) + (1 / 2 : ℝ) • (S.G2 * S.G2) = -S.Em := by
    simpa [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      InfoGeometry.Algebra.InvariantTransport.anticommutator,
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
theorem bosonized_G1_self_anticommutator (S : OperatorSurface (V := V))
    (hΓ : S.Γ * S.Γ = 1)
    (hG1_odd : S.Γ * S.G1 = -(S.G1 * S.Γ))
    (hG1_sq : S.G1 * S.G1 = S.Ep) :
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
      (R := ℝ) S.Γ S.G1 S.Ep hΓ hG1_odd hG1_sq

/--
The bosonized coproduct preserves the signed second odd--odd `osp(1|2)`
closure relation.
-/
theorem bosonized_G2_self_anticommutator (S : OperatorSurface (V := V))
    (hΓ : S.Γ * S.Γ = 1)
    (hG2_odd : S.Γ * S.G2 = -(S.G2 * S.Γ))
    (hG2_sq : S.G2 * S.G2 = -S.Em) :
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
      (R := ℝ) S.Γ S.G2 (-S.Em) hΓ hG2_odd hG2_sq

/-
The old `trivialOperatorSurface` supplied zero operators as a purported
realization.  That was not an OSp(1|2) representation.  Keep the public name
for source compatibility, but make it an explicit constructor: every
operator and every closure proof must now be supplied by a genuine owner.
-/
def trivialOperatorSurface
    (Γ H Ep Em G1 G2 : Op V)
    :
    OperatorSurface (V := V) :=
  { Γ := Γ
    H := H
    Ep := Ep
    Em := Em
    G1 := G1
    G2 := G2 }

end OperatorSurface

end InfoGeometry.Algebra.OSp12
