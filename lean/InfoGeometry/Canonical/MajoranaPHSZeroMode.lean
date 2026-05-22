import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.MajoranaPHSZeroMode

Canonical finite PHS/zero-mode surface over the doubled Tomita-Krein atom.

This module keeps the three notions separate:

* PHS / Majorana reality: `J γ J = γ`;
* boundary zero mode: `CCRBracket H γ = 0`;
* support in a selected corner projector: `P₀ (γ P₀) = γ`.

The finite `Cl(1,1)` swap already exists in
`TomitaKreinNilpotentAtom`; this file only packages the operator-level
predicates and exports the concrete PHS swap as a clean canonical surface.
-/

namespace InfoGeometry.Canonical.MajoranaPHSZeroMode

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1. PHS, zero-mode, and projector predicates -/

/-- Tomita/PHS conjugation on finite doubled-real endomorphisms. -/
@[rep_depth krein]
noncomputable def majoranaConjOp (T : FockEndomorphism E) : FockEndomorphism E :=
  (InfoGeometry.Krein.modular_j (E := E)).comp
    (T.comp (InfoGeometry.Krein.modular_j (E := E)))

/-- PHS / Majorana reality: fixed by Tomita/PHS conjugation. -/
def IsPHSInvariant (T : FockEndomorphism E) : Prop :=
  majoranaConjOp (E := E) T = T

/-- Boundary zero mode: the operator commutes with the chosen boundary generator. -/
def IsBoundaryZeroMode (H T : FockEndomorphism E) : Prop :=
  Commute H T

/-- Self-adjoint and PHS-invariant, using mathlib's symmetry predicate. -/
def IsMajoranaOperator (T : FockEndomorphism E) : Prop :=
  LinearMap.IsSymmetric T.toLinearMap ∧ IsPHSInvariant (E := E) T

/-- A selected zero-mode corner projector: idempotent and PHS-stable. -/
structure ZeroModeProjector (H : FockEndomorphism E) where
  P0 : FockEndomorphism E
  idempotent : P0.comp P0 = P0
  boundary_zero_mode : IsBoundaryZeroMode (E := E) H P0
  phs_stable : IsPHSInvariant (E := E) P0

/-- Support in the selected projector corner. -/
def SupportedInZeroMode
    {H : FockEndomorphism E}
    (Z : ZeroModeProjector (E := E) H)
    (T : FockEndomorphism E) : Prop :=
  Z.P0.comp (T.comp Z.P0) = T

/-- Full zero-mode predicate keeping support, self-adjointness, PHS, and
boundary stationarity separate. -/
def IsMajoranaPHSZeroMode
    (P0 H T : FockEndomorphism E) : Prop :=
  P0.comp (T.comp P0) = T
    ∧ LinearMap.IsSymmetric T.toLinearMap
    ∧ IsPHSInvariant (E := E) T
    ∧ IsBoundaryZeroMode (E := E) H T

/-- Any boundary generator commutes with itself. -/
theorem boundaryGenerator_is_boundary_zero_mode
    (H : FockEndomorphism E) :
    IsBoundaryZeroMode (E := E) H H := by
  exact Commute.refl H

/-- The canonical `K = J ∘ ε` boundary lane is stationary with respect to itself. -/
theorem cptSuperchargeOp_is_boundary_zero_mode :
    IsBoundaryZeroMode (E := E)
      (cptSuperchargeOp (E := E))
      (cptSuperchargeOp (E := E)) := by
  simpa using (boundaryGenerator_is_boundary_zero_mode (E := E) (cptSuperchargeOp (E := E)))

/-! ## 2. Concrete finite PHS swap -/

/-- The concrete split-null creation operator is sent to annihilation by Tomita/PHS. -/
theorem concrete_majorana_creation_swap :
    majoranaConjOp (E := E) (concreteCARCreation (E := E))
      = concreteCARAnnihilation (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [majoranaConjOp, concreteCARCreation, concreteCARAnnihilation,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled]

/-- The concrete split-null annihilation operator is sent to creation by Tomita/PHS. -/
theorem concrete_majorana_annihilation_swap :
    majoranaConjOp (E := E) (concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [majoranaConjOp, concreteCARCreation, concreteCARAnnihilation,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled]

/-- The concrete Majorana swap `u₊ + u₋` is Tomita/PHS invariant. -/
theorem concrete_majorana_swap_is_phs_invariant :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) := by
  unfold IsPHSInvariant
  have hswap :
      majoranaConjOp (E := E) (concreteCARCreation (E := E))
        = concreteCARAnnihilation (E := E) :=
    concrete_majorana_creation_swap (E := E)
  have hswap' :
      majoranaConjOp (E := E) (concreteCARAnnihilation (E := E))
        = concreteCARCreation (E := E) :=
    concrete_majorana_annihilation_swap (E := E)
  calc
    majoranaConjOp (E := E)
        (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
      = majoranaConjOp (E := E) (concreteCARCreation (E := E))
          + majoranaConjOp (E := E) (concreteCARAnnihilation (E := E)) := by
            simp [majoranaConjOp, ContinuousLinearMap.comp_add]
    _ = concreteCARAnnihilation (E := E) + concreteCARCreation (E := E) := by
          rw [hswap, hswap']
    _ = concreteCARCreation (E := E) + concreteCARAnnihilation (E := E) := by
          abel

/-- The concrete Majorana swap is a fixed PHS boundary candidate. -/
theorem concrete_majorana_swap_is_boundary_candidate :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) := by
  exact concrete_majorana_swap_is_phs_invariant (E := E)

end Core

end InfoGeometry.Canonical.MajoranaPHSZeroMode
