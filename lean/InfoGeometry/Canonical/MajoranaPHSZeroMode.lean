import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.BoundaryProjector
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

/-! ## 1. PHS and zero-mode predicates -/

/-- PHS / Majorana reality: fixed by Tomita/PHS conjugation. -/
def IsPHSInvariant (T : FockEndomorphism E) : Prop :=
  tomitaConjOp (E := E) T = T

/-- Boundary zero mode: the operator commutes with the chosen boundary generator. -/
def IsBoundaryZeroMode (H T : FockEndomorphism E) : Prop :=
  CCRBracket (E := E) H T = 0

/-- Krein-self-adjoint and PHS-invariant on the doubled carrier. -/
def IsMajoranaOperator (T : FockEndomorphism E) : Prop :=
  KreinSpace.IsKreinSelfAdjoint (H := DoubledSpace E) T ∧ IsPHSInvariant (E := E) T

/-- Corner support by an idempotent/projector `P₀`, stated directly on operators. -/
def IsSupportedInCorner (P₀ T : FockEndomorphism E) : Prop :=
  P₀.comp (T.comp P₀) = T

/--
Majorana/PHS zero mode in a selected corner.

This is deliberately a plain proposition over a supplied operator projector,
not a wrapper datum: projection laws are imported/proved separately by the
projector owner, e.g. `boundaryProjector_idempotent` or
`spectralPlusProj_idempotent`.
-/
def IsMajoranaPHSZeroMode
    (P₀ H T : FockEndomorphism E) : Prop :=
  IsSupportedInCorner (E := E) P₀ T
    ∧ IsMajoranaOperator (E := E) T
    ∧ IsBoundaryZeroMode (E := E) H T

/-- Any boundary generator commutes with itself. -/
theorem boundaryGenerator_is_boundary_zero_mode
    (H : FockEndomorphism E) :
    IsBoundaryZeroMode (E := E) H H := by
  simp [IsBoundaryZeroMode, CCRBracket]

/-- The canonical `K = J ∘ ε` boundary lane is stationary with respect to itself. -/
theorem cptSuperchargeOp_is_boundary_zero_mode :
    IsBoundaryZeroMode (E := E)
      (cptSuperchargeOp (E := E))
      (cptSuperchargeOp (E := E)) := by
  simpa using (boundaryGenerator_is_boundary_zero_mode (E := E) (cptSuperchargeOp (E := E)))

/--
The canonical boundary projector is supported in its own corner.

This is the exact projection-side statement used by the zero-mode lane:
the boundary projector is idempotent, hence stable under its own corner
compression.
-/
theorem boundaryProjector_supportedInCorner
    (Δ : FockEndomorphism E)
    [(boundarySubspace (E := E) Δ).HasOrthogonalProjection] :
    IsSupportedInCorner (E := E)
      (boundaryProjector (E := E) Δ) (boundaryProjector (E := E) Δ) := by
  have h := boundaryProjector_idempotent (E := E) Δ
  simpa [IsSupportedInCorner, ContinuousLinearMap.comp_assoc, h] using
    (congrArg (fun f : FockEndomorphism E => f.comp (boundaryProjector (E := E) Δ)) h)

/--
Finite Majorana/PHS zero-mode package on the canonical split boundary lane.

This packages the two concrete finite facts that are already owned separately:
PHS invariance of the real Majorana swap and boundary-zero-mode closure of the
Tomita CPT generator.
-/
theorem concreteMajoranaPHSZeroModePackage :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) ∧
    IsBoundaryZeroMode (E := E)
      (cptSuperchargeOp (E := E))
      (cptSuperchargeOp (E := E)) := by
  refine ⟨concrete_majorana_swap_is_phs_invariant (E := E),
    cptSuperchargeOp_is_boundary_zero_mode (E := E)⟩

/-! ## 2. Canonical projector/corner facts -/

/-- The `+` spectral projector is supported in its own canonical corner. -/
theorem spectralPlusProj_supportedInCorner :
    IsSupportedInCorner (E := E)
      (spectralPlusProj (E := E)) (spectralPlusProj (E := E)) := by
  simp [IsSupportedInCorner, spectralPlusProj_idempotent (E := E)]

/-- The `-` spectral projector is supported in its own canonical corner. -/
theorem spectralMinusProj_supportedInCorner :
    IsSupportedInCorner (E := E)
      (spectralMinusProj (E := E)) (spectralMinusProj (E := E)) := by
  simp [IsSupportedInCorner, spectralMinusProj_idempotent (E := E)]

/-! ## 3. Concrete finite PHS swap -/

/-- The concrete split-null creation operator is sent to annihilation by Tomita/PHS. -/
theorem concrete_majorana_creation_swap :
    tomitaConjOp (E := E) (concreteCARCreation (E := E))
      = concreteCARAnnihilation (E := E) := by
  simpa using (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.tomitaConj_creation_eq_annihilation (E := E))

/-- The concrete split-null annihilation operator is sent to creation by Tomita/PHS. -/
theorem concrete_majorana_annihilation_swap :
    tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) := by
  simpa using
    (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.tomitaConj_annihilation_eq_creation (E := E))

/-- The concrete Majorana swap `u₊ + u₋` is Tomita/PHS invariant. -/
theorem concrete_majorana_swap_is_phs_invariant :
    IsPHSInvariant (E := E)
      (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)) := by
  simpa [IsPHSInvariant] using
    (InfoGeometry.Canonical.TomitaKreinNilpotentAtom.concrete_majorana_swap_is_phs_invariant (E := E))

end Core

end InfoGeometry.Canonical.MajoranaPHSZeroMode
